(* HSpec.ml — 高水準抽象特化器
 *
 * spec.rwhile が実装している特化器を直接スタイル（非可逆）で記述する。
 * マクロ操作（SPEC-EXP, SPEC-STEP, MAKE-SEQ 等）を原始命令として持つ。
 *
 * 目的：
 *   spec.rwhile のバグを追跡するために、可逆性アーティファクト（Cd'等）を
 *   排除した高水準で実行し、期待出力と実際の出力を比較する。
 *)

open AbsRwhile

(* ===== 値ユーティリティ ===== *)
let vtrue  = VCons (VNil, VNil)
let vfalse = VNil

let show_val v = PrintRwhile.printTree PrintRwhile.prtValT v

(* ===== 単項インデックス符号化 ===== *)
(* var k は k 個の nil の入れ子: 0=nil, 1=(nil.nil), 2=(nil.(nil.nil)), ... *)
let rec val_to_idx = function
  | VNil           -> 0
  | VCons (VNil, rest) -> 1 + val_to_idx rest
  | v -> failwith ("val_to_idx: unexpected " ^ show_val v)

let rec idx_to_val = function
  | 0 -> VNil
  | n -> VCons (VNil, idx_to_val (n-1))

(* ===== 高水準AST ===== *)

(* 式 (プログラムの式コードのデコード) *)
type hexp =
  | HVar  of int            (* ('var . k) *)
  | HVal  of valT           (* ('val . v) *)
  | HCons of hexp * hexp    (* ('cons . (e1 . e2)) *)
  | HHd   of hexp           (* ('hd . e) *)
  | HTl   of hexp           (* ('tl . e) *)
  | HEq   of hexp * hexp    (* ('eq . (e1 . e2)) *)

(* パターン *)
type hpat =
  | HPVar  of int           (* ('var . k) *)
  | HPVal  of valT          (* ('val . v) *)
  | HPCons of hpat * hpat   (* ('cons . (p1 . p2)) *)

(* コマンド *)
type hcmd =
  | HAss  of int * hexp
  | HRep  of hpat * hpat
  | HSeq  of hcmd * hcmd
  | HCond of hexp * hcmd * hcmd * hexp
  | HLoop of hexp * hcmd * hcmd * hexp
  | HNop

(* ===== デコーダ (valT → hexp / hcmd) ===== *)

(* valT リストを OCaml リストに展開 *)
let rec to_list = function
  | VNil -> []
  | VCons (h, t) -> h :: to_list t
  | v -> failwith ("to_list: not a list: " ^ show_val v)

let rec decode_exp (v : valT) : hexp =
  match v with
  | VCons (VAtom (Atom "'var"), k) -> HVar (val_to_idx k)
  | VCons (VAtom (Atom "'val"), lit) -> HVal lit
  | VCons (VAtom (Atom "'cons"), VCons (e1, e2)) ->
    HCons (decode_exp e1, decode_exp e2)
  | VCons (VAtom (Atom "'hd"), e) -> HHd (decode_exp e)
  | VCons (VAtom (Atom "'tl"), e) -> HTl (decode_exp e)
  | VCons (VAtom (Atom "'eq"), VCons (e1, e2)) ->
    HEq (decode_exp e1, decode_exp e2)
  | _ -> failwith ("decode_exp: unknown: " ^ show_val v)

let rec decode_pat (v : valT) : hpat =
  match v with
  | VCons (VAtom (Atom "'var"), k) -> HPVar (val_to_idx k)
  | VCons (VAtom (Atom "'val"), lit) -> HPVal lit
  | VCons (VAtom (Atom "'cons"), VCons (p1, p2)) ->
    HPCons (decode_pat p1, decode_pat p2)
  | _ -> failwith ("decode_pat: unknown: " ^ show_val v)

let do_nothing =
  HAss (0, HVal VNil)   (* ('ass . (('var . nil) . ('val . nil))) *)

let decode_branch (v : valT) : hcmd =
  decode_cmd_val v
and decode_cmd_val (v : valT) : hcmd =
  match v with
  | VCons (VAtom (Atom "'ass"), VCons (var_code, e_code)) ->
    (match var_code with
     | VCons (VAtom (Atom "'var"), k) ->
       HAss (val_to_idx k, decode_exp e_code)
     | _ -> failwith ("decode_cmd 'ass: bad var: " ^ show_val var_code))
  | VCons (VAtom (Atom "'rep"), VCons (q, r)) ->
    HRep (decode_pat q, decode_pat r)
  | VCons (VAtom (Atom "'seq"), VCons (c1, c2)) ->
    HSeq (decode_cmd_val c1, decode_cmd_val c2)
  | VCons (VAtom (Atom "'cond"), args) ->
    (match to_list args with
     | [e; c1; c2; f; _] ->
       HCond (decode_exp e, decode_cmd_val c1, decode_cmd_val c2, decode_exp f)
     | _ -> failwith ("decode_cmd 'cond: bad args: " ^ show_val args))
  | VCons (VAtom (Atom "'loop"), args) ->
    (match to_list args with
     | [e; do_c; loop_c; f; _] ->
       HLoop (decode_exp e, decode_cmd_val do_c, decode_cmd_val loop_c, decode_exp f)
     | _ -> failwith ("decode_cmd 'loop: bad args: " ^ show_val args))
  | _ -> failwith ("decode_cmd: unknown tag: " ^ show_val v)

let decode_cmd = decode_cmd_val

(* ===== 部分ストア ===== *)

type binding =
  | Static of valT   (* ('S . v) - static: hd = vtrue *)
  | Dynamic          (* ('D . nil) - dynamic: hd = nil *)

type pstore = binding array

let store_size = 100

let init_store () : pstore =
  Array.make store_size Dynamic

let store_get (sigma : pstore) k = sigma.(k)
let store_set (sigma : pstore) k b = sigma.(k) <- b

(* ===== 特化結果 ===== *)

type sresult =
  | SStatic  of valT
  | SDynamic of hexp

let lift = function
  | SStatic v  -> HVal v
  | SDynamic e -> e

(* ===== 可逆更新 (rupdate) ===== *)

let rupdate_val cur newv =
  match cur, newv with
  | VNil, _       -> newv                    (* nil → v: set *)
  | _, _ when cur = newv -> VNil             (* v → v: clear *)
  | _, VNil       -> cur                     (* v → nil: no-op *)
  | _  ->
    failwith (Printf.sprintf "rupdate error: cur=%s new=%s"
                (show_val cur) (show_val newv))

(* ===== 式の特化 (SPEC-EXP) ===== *)

let rec spec_exp (sigma : pstore) (e : hexp) : sresult =
  match e with
  | HVar k ->
    (match store_get sigma k with
     | Static v -> SStatic v
     | Dynamic  -> SDynamic (HVar k))
  | HVal v -> SStatic v
  | HCons (e1, e2) ->
    let r1 = spec_exp sigma e1 and r2 = spec_exp sigma e2 in
    (match r1, r2 with
     | SStatic v1, SStatic v2 -> SStatic (VCons (v1, v2))
     | _ -> SDynamic (HCons (lift r1, lift r2)))
  | HHd e ->
    (match spec_exp sigma e with
     | SStatic (VCons (h, _)) -> SStatic h
     | SStatic v -> failwith ("hd of non-cons: " ^ show_val v)
     | SDynamic e' -> SDynamic (HHd e'))
  | HTl e ->
    (match spec_exp sigma e with
     | SStatic (VCons (_, t)) -> SStatic t
     | SStatic v -> failwith ("tl of non-cons: " ^ show_val v)
     | SDynamic e' -> SDynamic (HTl e'))
  | HEq (e1, e2) ->
    let r1 = spec_exp sigma e1 and r2 = spec_exp sigma e2 in
    (match r1, r2 with
     | SStatic v1, SStatic v2 ->
       SStatic (if v1 = v2 then vtrue else vfalse)
     | _ -> SDynamic (HEq (lift r1, lift r2)))

(* ===== パターン操作 ===== *)

(* パターン中に動的変数があるか確認 *)
let rec pat_all_static (sigma : pstore) = function
  | HPVar k -> (match store_get sigma k with Static _ -> true | Dynamic -> false)
  | HPVal _ -> true
  | HPCons (p1, p2) -> pat_all_static sigma p1 && pat_all_static sigma p2

(* パターンから値を読み出す（変数は Static → Dynamic に遷移） *)
let rec pat_read (sigma : pstore) = function
  | HPVar k ->
    (match store_get sigma k with
     | Static v -> store_set sigma k Dynamic; v
     | Dynamic  -> failwith (Printf.sprintf "pat_read: var %d is dynamic" k))
  | HPVal v -> v
  | HPCons (p1, p2) ->
    let v1 = pat_read sigma p1 in
    let v2 = pat_read sigma p2 in
    VCons (v1, v2)

(* パターンに値を書き込む（変数は Dynamic → Static に遷移） *)
let rec pat_write (sigma : pstore) (p : hpat) (v : valT) =
  match p, v with
  | HPVar k, _ ->
    (match store_get sigma k with
     | Dynamic -> store_set sigma k (Static v)
     | Static cur ->
       failwith (Printf.sprintf "pat_write: var %d already static=%s" k (show_val cur)))
  | HPVal expected, _ ->
    if v <> expected then
      failwith (Printf.sprintf "pat_write: value mismatch %s <> %s"
                  (show_val v) (show_val expected))
  | HPCons (p1, p2), VCons (v1, v2) ->
    pat_write sigma p1 v1; pat_write sigma p2 v2
  | HPCons _, _ ->
    failwith ("pat_write: cons pattern but non-cons value: " ^ show_val v)

(* ===== コマンドの特化 (SPEC-STEP / SPEC-CMD) ===== *)

(* 残留コードをリストで管理（逆順）→ make_seq で折り畳む *)
let depth = ref 0
let log_prefix () = String.make (!depth * 2) ' '

let log_step label =
  Printf.printf "%s[STEP] %s\n%!" (log_prefix ()) label

(* 式コードのシリアライズ *)
let rec show_hexp = function
  | HVar k  -> Printf.sprintf "var[%d]" k
  | HVal v  -> Printf.sprintf "val(%s)" (show_val v)
  | HCons (e1, e2) -> Printf.sprintf "cons(%s,%s)" (show_hexp e1) (show_hexp e2)
  | HHd e   -> Printf.sprintf "hd(%s)" (show_hexp e)
  | HTl e   -> Printf.sprintf "tl(%s)" (show_hexp e)
  | HEq (e1, e2) -> Printf.sprintf "eq(%s,%s)" (show_hexp e1) (show_hexp e2)

let rec show_hpat = function
  | HPVar k -> Printf.sprintf "var[%d]" k
  | HPVal v -> Printf.sprintf "val(%s)" (show_val v)
  | HPCons (p1, p2) -> Printf.sprintf "cons(%s,%s)" (show_hpat p1) (show_hpat p2)

let rec show_hcmd = function
  | HAss (k, e)   -> Printf.sprintf "ass(var[%d], %s)" k (show_hexp e)
  | HRep (q, r)   -> Printf.sprintf "rep(%s, %s)" (show_hpat q) (show_hpat r)
  | HSeq (c1, c2) -> Printf.sprintf "seq(%s; %s)" (show_hcmd c1) (show_hcmd c2)
  | HCond (e, c1, c2, f) ->
    Printf.sprintf "cond(%s ? %s : %s fi %s)"
      (show_hexp e) (show_hcmd c1) (show_hcmd c2) (show_hexp f)
  | HLoop (e, d, l, f) ->
    Printf.sprintf "loop(from %s do %s loop %s until %s)"
      (show_hexp e) (show_hcmd d) (show_hcmd l) (show_hexp f)
  | HNop -> "nop"

let show_store (sigma : pstore) =
  let entries = ref [] in
  for k = store_size - 1 downto 0 do
    match sigma.(k) with
    | Static v -> entries := Printf.sprintf "  var[%d] = S(%s)" k (show_val v) :: !entries
    | Dynamic  -> ()  (* 動的はスキップ *)
  done;
  String.concat "\n" !entries

let show_rcode (rcode : hcmd list) =
  String.concat " ; " (List.rev_map show_hcmd rcode)

(* spec_cmd の返り値: (更新済みストア, 残留コードリスト（逆順）) *)
let rec spec_cmd (sigma : pstore) (rcode : hcmd list) (cmd : hcmd) step_count
    : hcmd list * int =
  match cmd with
  | HNop -> (rcode, step_count)

  | HAss (k, e) ->
    let n = step_count + 1 in
    let r = spec_exp sigma e in
    (match r, store_get sigma k with
     | SStatic v, Static cur ->
       let new_val = rupdate_val cur v in
       store_set sigma k (Static new_val);
       log_step (Printf.sprintf "ass: var[%d] S(%s) ^= S(%s) → S(%s)"
                   k (show_val cur) (show_val v) (show_val new_val));
       (rcode, n)
     | SStatic v, Dynamic ->
       log_step (Printf.sprintf "ass: var[%d] D ^= S(%s) → residual" k (show_val v));
       (HAss (k, HVal v) :: rcode, n)
     | SDynamic e', _ ->
       store_set sigma k Dynamic;
       log_step (Printf.sprintf "ass: var[%d] ^= D(%s) → residual" k (show_hexp e'));
       (HAss (k, e') :: rcode, n))

  | HRep (q, r) ->
    let n = step_count + 1 in
    if pat_all_static sigma r then begin
      let v = pat_read sigma r in
      pat_write sigma q v;
      log_step (Printf.sprintf "rep: static → executed, val=%s" (show_val v));
      (rcode, n)
    end else begin
      log_step (Printf.sprintf "rep: dynamic → residual rep(%s, %s)"
                  (show_hpat q) (show_hpat r));
      (HRep (q, r) :: rcode, n)
    end

  | HSeq (c1, c2) ->
    let (rcode', n') = spec_cmd sigma rcode c1 step_count in
    spec_cmd sigma rcode' c2 n'

  | HCond (e, c_then, c_else, f) ->
    let n = step_count + 1 in
    (match spec_exp sigma e with
     | SStatic v when v <> vfalse ->
       log_step (Printf.sprintf "cond: entry %s = S(true) → take then-branch" (show_hexp e));
       incr depth;
       let (rcode', n') = spec_cmd sigma rcode c_then n in
       decr depth;
       (rcode', n')
     | SStatic _ ->
       log_step (Printf.sprintf "cond: entry %s = S(false) → take else-branch" (show_hexp e));
       incr depth;
       let (rcode', n') = spec_cmd sigma rcode c_else n in
       decr depth;
       (rcode', n')
     | SDynamic e' ->
       log_step (Printf.sprintf "cond: entry %s = Dynamic → residualize" (show_hexp e));
       (HCond (e', c_then, c_else, f) :: rcode, n))

  | HLoop (e, do_c, loop_c, f) ->
    let n = step_count + 1 in
    (match spec_exp sigma e with
     | SDynamic e' ->
       log_step (Printf.sprintf "loop: entry %s = Dynamic → residualize" (show_hexp e));
       (HLoop (e', do_c, loop_c, f) :: rcode, n)
     | SStatic v when v = vfalse ->
       failwith ("loop: entry condition false: " ^ show_hexp e)
     | SStatic _ ->
       log_step (Printf.sprintf "loop: entry %s = S(true) → unroll" (show_hexp e));
       spec_loop sigma rcode do_c loop_c e f n 0)

(* ループ本体の実行（静的アンローリング） *)
and spec_loop sigma rcode do_c loop_c e f step_count iter_count =
  (* 1回目: do_c を実行 *)
  incr depth;
  let (rcode', n') = spec_cmd sigma rcode do_c step_count in
  decr depth;
  (* exit test を確認 *)
  (match spec_exp sigma f with
   | SStatic v when v <> vfalse ->
     log_step (Printf.sprintf "loop iter=%d: exit %s = S(true) → done" iter_count (show_hexp f));
     (rcode', n')
   | SStatic _ ->
     log_step (Printf.sprintf "loop iter=%d: exit %s = S(false) → continue" iter_count (show_hexp f));
     (* entry assertion は false であるはず *)
     (match spec_exp sigma e with
      | SStatic v when v = vfalse -> ()
      | SStatic _ -> failwith (Printf.sprintf "loop iter=%d: re-entry assertion failed" iter_count)
      | SDynamic _ -> ());
     (* loop_c を実行 *)
     incr depth;
     let (rcode'', n'') = spec_cmd sigma rcode' loop_c n' in
     decr depth;
     spec_loop sigma rcode'' do_c loop_c e f n'' (iter_count + 1)
   | SDynamic _ ->
     log_step (Printf.sprintf "loop iter=%d: exit %s = Dynamic → residualize remaining" iter_count (show_hexp f));
     (* 残りのループを残留コードとして出力 *)
     (HLoop (e, do_c, loop_c, f) :: rcode', n'))

(* ===== MAKE-SEQ ===== *)

let make_seq (rcode : hcmd list) : hcmd option =
  (* rcode は逆順。先頭が最後に追加されたコマンド。
     MAKE-SEQ は先頭から取り出して順番に繋ぐ。 *)
  match rcode with
  | [] -> None
  | _  ->
    let cmds = List.rev rcode in  (* 実行順に戻す *)
    Some (List.fold_left (fun acc c ->
      match acc with
      | HNop -> c
      | _    -> HSeq (acc, c)
    ) HNop cmds)

(* ===== 特化器のトップレベル ===== *)

(* 特化: プログラム (read_var, body, write_var) を静的入力 s で特化する *)
let specialize (body : hcmd) (read_idx : int) (static_input : valT) (write_idx : int)
    : hcmd option =
  let sigma = init_store () in
  store_set sigma read_idx (Static static_input);

  Printf.printf "=== HSpec 特化開始 ===\n";
  Printf.printf "read_var = var[%d], static_input = %s\n" read_idx (show_val static_input);
  Printf.printf "write_var = var[%d]\n%!" write_idx;

  let (rcode, total_steps) = spec_cmd sigma [] body 0 in

  Printf.printf "\n=== 特化完了 (%d ステップ) ===\n" total_steps;
  Printf.printf "部分ストア（静的変数）:\n%s\n" (show_store sigma);

  (* write 変数が静的になっているか確認 *)
  (match store_get sigma write_idx with
   | Static v ->
     Printf.printf "write_var[%d] = S(%s) → 残留: ass(var[%d], val(%s))\n"
       write_idx (show_val v) write_idx (show_val v);
     Some (HAss (write_idx, HVal v))
   | Dynamic ->
     Printf.printf "write_var[%d] = Dynamic → RCode から MAKE-SEQ\n" write_idx;
     Printf.printf "RCode (%d コマンド):\n  %s\n" (List.length rcode) (show_rcode rcode);
     make_seq rcode)

(* ===== メインエントリ (TestSuite.ml から呼ぶ用) ===== *)

(* P_data = spec.rwhile の入力形式 (P . S) を直接デコードする *)
let run_hspec (spec_input : valT) =
  (* spec.rwhile の入力: (P . S)
     P = (('var . I) . (Cmd . ('var . J)))
     S = static input *)
  match spec_input with
  | VCons (p_data, s_val) ->
    (match p_data with
     | VCons (VCons (VAtom (Atom "'var"), i_val),
              VCons (cmd_data,
                     VCons (VAtom (Atom "'var"), j_val))) ->
       let read_idx  = val_to_idx i_val in
       let write_idx = val_to_idx j_val in
       Printf.printf "デコード: read_var=var[%d], write_var=var[%d]\n%!"
         read_idx write_idx;
       let body = decode_cmd cmd_data in
       Printf.printf "プログラム本体: %s\n\n%!"
         (String.sub (show_hcmd body) 0
            (min 200 (String.length (show_hcmd body))));
       specialize body read_idx s_val write_idx
     | _ ->
       failwith ("run_hspec: unexpected P format: " ^ show_val p_data))
  | _ ->
    failwith ("run_hspec: expected (P . S), got: " ^ show_val spec_input)
