<?php
// execute.php — R-WHILE Playground backend
// Runs the ri interpreter on user-submitted programs

$dir = dirname(__FILE__);
// `make install` copies ri into this web directory; fall back to a system path.
$RI = is_executable("$dir/ri") ? "$dir/ri" : '/usr/local/bin/ri';
$TIMEOUT = 5; // seconds

$prog = $_POST['prog'] ?? '';
$data = $_POST['data'] ?? '';
$invert = isset($_POST['invert']);
$p2d = isset($_POST['p2d']);
$exp = isset($_POST['exp']);

if (empty(trim($prog))) {
    header('Content-Type: text/plain; charset=UTF-8');
    echo 'Error: No program provided.';
    exit;
}

// Write program and data to temp files
$tmpDir = sys_get_temp_dir();
$progFile = tempnam($tmpDir, 'rwhile_prog_') . '.rwhile';
$dataFile = tempnam($tmpDir, 'rwhile_data_') . '.val';

if (file_put_contents($progFile, $prog) === false ||
    file_put_contents($dataFile, $data) === false) {
    @unlink($progFile);
    @unlink($dataFile);
    @unlink(substr($progFile, 0, -7));
    @unlink(substr($dataFile, 0, -4));
    header('HTTP/1.1 500 Internal Server Error');
    header('Content-Type: text/plain; charset=UTF-8');
    echo 'Error: could not write temporary files.';
    exit;
}

// Build command arguments
$args = [];
if ($invert) $args[] = '-inverse';
if ($p2d) $args[] = '-p2d';
if ($exp) $args[] = '-exp';
$args[] = escapeshellarg($progFile);
if (!empty(trim($data))) {
    $args[] = escapeshellarg($dataFile);
}

// Run with timeout. `timeout` exits 124 (TERM) / 137 (KILL) when it stops the command.
$cmd = '/usr/bin/timeout ' . $TIMEOUT . ' ' . escapeshellarg($RI) . ' ' . implode(' ', $args) . ' 2>&1';
$lines = [];
$code = 0;
exec($cmd, $lines, $code);
$output = implode("\n", $lines);

// Cleanup
@unlink($progFile);
@unlink($dataFile);
// Also clean up the tempnam base file (without .rwhile extension)
@unlink(substr($progFile, 0, -7));
@unlink(substr($dataFile, 0, -4));

if ($code === 124 || $code === 137) {
    $output = "Execution timed out (limit: {$TIMEOUT}s).";
} elseif ($code !== 0 && $output === '') {
    $output = 'Error: execution failed.';
}

header('Content-Type: text/plain; charset=UTF-8');
echo $output;
