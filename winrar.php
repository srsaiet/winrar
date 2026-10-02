<?php
// WinRAR Keygen - PHP Implementation
// Ported from https://github.com/bitcookies/winrar-keygen

// ---- GF(2^15) Tables ----
function gf2p15_init_tables() {
    $order = 0x7fff;
    $log = array_fill(0, 0x8000, 0);
    $exp = array_fill(0, 0x8000, 0);
    $exp[0] = 1;
    for ($i = 1; $i < $order; ++$i) {
        $temp = $exp[$i - 1] * 2;
        if ($temp & 0x8000) {
            $temp ^= 0x8003;
        }
        $exp[$i] = $temp & 0x7fff;
    }
    for ($i = 0; $i < $order; ++$i) {
        $log[$exp[$i]] = $i;
    }
    return [$log, $exp];
}
list($GF2_LOG, $GF2_EXP) = gf2p15_init_tables();

// ---- GF((2^15)^17) operations ----
// Element = array of 17 uint16 values (each < 0x8000)

function gf17_set_zero() {
    return array_fill(0, 17, 0);
}
function gf17_set_one() {
    $v = array_fill(0, 17, 0);
    $v[0] = 1;
    return $v;
}
function gf17_is_zero($a) {
    foreach ($a as $v) { if ($v) return false; }
    return true;
}
function gf17_is_equal($a, $b) {
    for ($i = 0; $i < 17; ++$i) { if ($a[$i] !== $b[$i]) return false; }
    return true;
}
function gf17_add($a, $b) {
    $r = array_fill(0, 17, 0);
    for ($i = 0; $i < 17; ++$i) $r[$i] = $a[$i] ^ $b[$i];
    return $r;
}
function gf17_add_assign(&$a, $b) {
    for ($i = 0; $i < 17; ++$i) $a[$i] ^= $b[$i];
}
function gf17_mul($a, $b) {
    global $GF2_LOG, $GF2_EXP;
    $temp = array_fill(0, 33, 0);
    for ($i = 0; $i < 17; ++$i) {
        if ($a[$i]) {
            $log_a = $GF2_LOG[$a[$i]];
            for ($j = 0; $j < 17; ++$j) {
                if ($b[$j]) {
                    $g = $log_a + $GF2_LOG[$b[$j]];
                    if ($g >= 0x7fff) $g -= 0x7fff;
                    $temp[$i + $j] ^= $GF2_EXP[$g];
                }
            }
        }
    }
    // Modular reduction by y^17 + y^3 + 1
    for ($i = 32; $i > 16; --$i) {
        if ($temp[$i]) {
            $temp[$i - 17] ^= $temp[$i];
            $temp[$i - 14] ^= $temp[$i];
            $temp[$i] = 0;
        }
    }
    return array_slice($temp, 0, 17);
}
function gf17_square($a) {
    global $GF2_LOG, $GF2_EXP;
    $temp = array_fill(0, 33, 0);
    for ($i = 0; $i < 17; ++$i) {
        if ($a[$i]) {
            $g = $GF2_LOG[$a[$i]] * 2;
            if ($g >= 0x7fff) $g -= 0x7fff;
            $temp[$i * 2] = $GF2_EXP[$g];
        }
    }
    for ($i = 32; $i > 16; --$i) {
        if ($temp[$i]) {
            $temp[$i - 17] ^= $temp[$i];
            $temp[$i - 14] ^= $temp[$i];
            $temp[$i] = 0;
        }
    }
    return array_slice($temp, 0, 17);
}
function gf17_inverse($a) {
    global $GF2_LOG, $GF2_EXP;
    if (gf17_is_zero($a)) throw new Exception("Zero doesn't have inverse.");

    $degF = -1;
    $F = array_fill(0, 34, 0);
    for ($i = 0; $i < 17; ++$i) {
        $F[$i] = $a[$i];
        if ($F[$i]) $degF = $i;
    }

    $degG = 17;
    $G = array_fill(0, 34, 0);
    $G[0] = 1; $G[3] = 1; $G[17] = 1;

    $degB = 0;
    $B = array_fill(0, 34, 0);
    $B[0] = 1;

    $degC = 0;
    $C = array_fill(0, 34, 0);

    $addScale = function(&$A, &$degA, $Alpha, $j, $pB, $degB) use ($GF2_LOG, $GF2_EXP) {
        $logAlpha = $GF2_LOG[$Alpha];
        for ($i = 0; $i <= $degB; ++$i) {
            if ($pB[$i]) {
                $g = $logAlpha + $GF2_LOG[$pB[$i]];
                if ($g >= 0x7fff) $g -= 0x7fff;
                $A[$j + $i] ^= $GF2_EXP[$g];
            }
        }
        for ($k = 32; $k >= 0; --$k) {
            if ($A[$k]) { $degA = $k; break; }
        }
        if ($degA < 0) $degA = 0;
    };

    while (true) {
        if ($degF == 0) {
            $result = array_fill(0, 17, 0);
            $inv = $GF2_LOG[$F[0]];
            for ($i = 0; $i <= $degB; ++$i) {
                if ($B[$i]) {
                    $g = $GF2_LOG[$B[$i]] - $inv;
                    if ($g < 0) $g += 0x7fff;
                    $result[$i] = $GF2_EXP[$g];
                }
            }
            return $result;
        }
        if ($degF < $degG) {
            list($F, $G) = [$G, $F]; list($degF, $degG) = [$degG, $degF];
            list($B, $C) = [$C, $B]; list($degB, $degC) = [$degC, $degB];
        }
        $j = $degF - $degG;
        $g = $GF2_LOG[$F[$degF]] - $GF2_LOG[$G[$degG]];
        if ($g < 0) $g += 0x7fff;
        $Alpha = $GF2_EXP[$g];
        $addScale($F, $degF, $Alpha, $j, $G, $degG);
        $addScale($B, $degB, $Alpha, $j, $C, $degC);
    }
}
function gf17_div($a, $b) {
    return gf17_mul($a, gf17_inverse($b));
}
function gf17_from_int($v) {
    $r = array_fill(0, 17, 0);
    $r[0] = $v & 0x7fff;
    return $r;
}
function gf17_load($bytes) {
    $result = array_fill(0, 17, 0);
    $bi = 0; $bits = 0; $val = 0;
    foreach ($bytes as $b) {
        $val = ($val << 8) | $b;
        $bits += 8;
        if ($bits >= 15) {
            $bits -= 15;
            $result[$bi] = ($val >> $bits) & 0x7fff;
            ++$bi;
            if ($bi >= 17) break;
        }
    }
    if ($bi > 0 && $bi <= 17 && $bits > 0) {
        $result[$bi] = ($val << (15 - $bits)) & 0x7fff;
    }
    return $result;
}
function gf17_dump($a) {
    $bytes = [];
    $bits = 0; $val = 0;
    foreach ($a as $v) {
        if ($v & ~0x7fff) throw new Exception("Not in GF");
        $val = ($val << 15) | $v;
        $bits += 15;
        while ($bits >= 8) {
            $bits -= 8;
            $bytes[] = ($val >> $bits) & 0xff;
            $val &= (1 << $bits) - 1;
        }
    }
    if ($bits > 0) $bytes[] = ($val << (8 - $bits)) & 0xff;
    return $bytes;
}
function gf17_dump_cpp($a) {
    // Bit-level pack 17 uint15 values into 32 bytes (matches C++ Dump)
    $bytes = array_fill(0, 32, 0);
    $bi = 0;
    $left_bits = 8;
    for ($i = 0; $i < 17; ++$i) {
        $low8 = $a[$i] & 0xFF;
        $high7 = ($a[$i] >> 8) & 0x7F;
        if ($left_bits == 8) {
            $bytes[$bi] = $low8;
            $bi++;
        } else {
            $bytes[$bi] |= ($low8 << (8 - $left_bits)) & 0xFF;
            $bi++;
            $bytes[$bi] = $low8 >> $left_bits;
        }
        if ($left_bits == 8) {
            $bytes[$bi] = $high7;
            $left_bits = 1;
        } elseif ($left_bits == 7) {
            $bytes[$bi] |= ($high7 << 1) & 0xFF;
            $bi++;
            $left_bits = 8;
        } else {
            $bytes[$bi] |= ($high7 << (8 - $left_bits)) & 0xFF;
            $bi++;
            $bytes[$bi] = $high7 >> $left_bits;
            $left_bits = 8 - (7 - $left_bits);
        }
    }
    return $bytes;
}
function gf17_to_bigint($a) {
    $bytes = gf17_dump_cpp($a);
    // Full value (32 bytes LE = 255-bit BigInt, matches C++ GMP arbitrary precision)
    $val = "0";
    for ($i = 31; $i >= 0; --$i) {
        $val = gmp_add(gmp_mul($val, "256"), (string)$bytes[$i]);
    }
    return $val;
}
function bigint_to_gf17($n) {
    $result = array_fill(0, 17, 0);
    for ($i = 0; $i < 17; ++$i) {
        $result[$i] = (int)gmp_intval(gmp_mod($n, "32768"));
        $n = gmp_div($n, "32768");
    }
    return $result;
}

// ---- Elliptic Curve over GF(2^m) ----
// Curve: y^2 + xy = x^3 + Ax^2 + B
// A = 0, B = element with value 161
class ECPoint {
    public $x, $y;
    public $infinity;
    public function __construct($x = null, $y = null, $inf = false) {
        $this->infinity = $inf;
        if ($inf) { $this->x = gf17_set_zero(); $this->y = gf17_set_zero(); }
        else { $this->x = $x; $this->y = $y; }
    }
}
function ec_double($p) {
    if ($p->infinity) return $p;
    $m = gf17_div($p->y, $p->x);
    $m = gf17_add($m, gf17_from_int(1)); // m = Y/X + 1
    // Actually m = Y/X + X, then NewX = m^2 + m + A
    $m2 = gf17_add(gf17_div($p->y, $p->x), $p->x);
    $newX = gf17_add(gf17_add(gf17_square($m2), $m2), gf17_from_int(0)); // A=0
    $newY = gf17_add(gf17_mul(gf17_add($m2, gf17_from_int(1)), $newX), gf17_square($p->x));
    return new ECPoint($newX, $newY);
}
function ec_add($p, $q) {
    if ($p->infinity) return $q;
    if ($q->infinity) return $p;
    if (gf17_is_equal($p->x, $q->x)) {
        if (gf17_is_equal($p->y, $q->y)) return ec_double($p);
        return new ECPoint(null, null, true);
    }
    $m = gf17_div(gf17_add($p->y, $q->y), gf17_add($p->x, $q->x));
    $newX = gf17_add(gf17_add(gf17_add(gf17_square($m), $m), $p->x), $q->x);
    $newY = gf17_add(gf17_add(gf17_mul(gf17_add($p->x, $newX), $m), $newX), $p->y);
    return new ECPoint($newX, $newY);
}
function ec_mul($p, $k_str) {
    $result = new ECPoint(null, null, true);
    $temp = $p;
    $k = gmp_init($k_str, 16);
    $bits = gmp_strval($k, 2);
    $bitLen = strlen($bits);
    for ($i = 0; $i < $bitLen; ++$i) {
        if ($bits[$bitLen - 1 - $i] === '1') $result = ec_add($result, $temp);
        $temp = ec_double($temp);
    }
    return $result;
}
function ec_point_dump($p) {
    $xbytes = gf17_dump($p->x);
    $y_over_x = gf17_div($p->y, $p->x);
    $zbytes = gf17_dump($y_over_x);
    $prefix = ($zbytes[0] & 1) ? "\x03" : "\x02";
    $xbytes_be = $xbytes;
    // Pad/truncate to 32 bytes (big endian)
    while (count($xbytes_be) < 32) array_unshift($xbytes_be, 0);
    if (count($xbytes_be) > 32) $xbytes_be = array_slice($xbytes_be, -32);
    return $prefix . implode('', array_map('chr', $xbytes_be));
}

// ---- SHA-1 with state access ----
class Sha1State {
    public $state;
    public $count;
    public $buffer;
    public function __construct() {
        $this->state = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0];
        $this->count = 0;
        $this->buffer = '';
    }
    public function update($data) {
        $this->count += strlen($data);
        $this->buffer .= $data;
        while (strlen($this->buffer) >= 64) {
            $block = substr($this->buffer, 0, 64);
            $this->buffer = substr($this->buffer, 64);
            $this->_process($block);
        }
    }
    private function _rol($x, $n) { return (($x << $n) | ($x >> (32 - $n))) & 0xFFFFFFFF; }
    private function _process($block) {
        $w = [];
        for ($i = 0; $i < 16; ++$i) {
            $w[$i] = (ord($block[$i*4]) << 24) | (ord($block[$i*4+1]) << 16) | (ord($block[$i*4+2]) << 8) | ord($block[$i*4+3]);
        }
        for ($i = 16; $i < 80; ++$i) {
            $w[$i] = $this->_rol($w[$i-3] ^ $w[$i-8] ^ $w[$i-14] ^ $w[$i-16], 1);
        }
        $a = $this->state[0]; $b = $this->state[1]; $c = $this->state[2]; $d = $this->state[3]; $e = $this->state[4];
        for ($i = 0; $i < 80; ++$i) {
            if ($i < 20) { $f = ($b & $c) | ((~$b) & $d); $k = 0x5A827999; }
            elseif ($i < 40) { $f = $b ^ $c ^ $d; $k = 0x6ED9EBA1; }
            elseif ($i < 60) { $f = ($b & $c) | ($b & $d) | ($c & $d); $k = 0x8F1BBCDC; }
            else { $f = $b ^ $c ^ $d; $k = 0xCA62C1D6; }
            $temp = ($this->_rol($a, 5) + $f + $e + $k + $w[$i]) & 0xFFFFFFFF;
            $e = $d; $d = $c; $c = $this->_rol($b, 30); $b = $a; $a = $temp;
        }
        $this->state[0] = ($this->state[0] + $a) & 0xFFFFFFFF;
        $this->state[1] = ($this->state[1] + $b) & 0xFFFFFFFF;
        $this->state[2] = ($this->state[2] + $c) & 0xFFFFFFFF;
        $this->state[3] = ($this->state[3] + $d) & 0xFFFFFFFF;
        $this->state[4] = ($this->state[4] + $e) & 0xFFFFFFFF;
    }
    public function digest() {
        $c = clone $this;
        $totalBits = $c->count * 8;
        $c->update("\x80");
        while (strlen($c->buffer) % 64 != 56) $c->update("\x00");
        $lenBytes = '';
        for ($i = 7; $i >= 0; --$i) {
            $lenBytes .= chr(($totalBits >> ($i * 8)) & 0xFF);
        }
        $c->update($lenBytes);
        $result = '';
        for ($i = 0; $i < 5; ++$i) {
            $result .= chr(($c->state[$i] >> 24) & 0xFF);
            $result .= chr(($c->state[$i] >> 16) & 0xFF);
            $result .= chr(($c->state[$i] >> 8) & 0xFF);
            $result .= chr($c->state[$i] & 0xFF);
        }
        return $result;
    }
    public function get_state_be() {
        // Return the 5 state values as big-endian 32-bit values packed in a string
        $result = '';
        for ($i = 0; $i < 5; ++$i) {
            $result .= chr(($this->state[$i] >> 24) & 0xFF);
            $result .= chr(($this->state[$i] >> 16) & 0xFF);
            $result .= chr(($this->state[$i] >> 8) & 0xFF);
            $result .= chr($this->state[$i] & 0xFF);
        }
        return $result;
    }
}

// ---- SHA-1 wrapper for WinRAR keygen ----
function winrar_sha1_state($data) {
    $s = new Sha1State();
    $s->update($data);
    $totalBits = $s->count * 8; // capture original message length BEFORE padding
    $s->update("\x80");
    while (strlen($s->buffer) % 64 != 56) $s->update("\x00");
    $lenBytes = '';
    for ($i = 7; $i >= 0; --$i) $lenBytes .= chr(($totalBits >> ($i * 8)) & 0xFF);
    $s->update($lenBytes);
    return $s->state;
}
function winrar_sha1_state_partial($data) {
    $s = new Sha1State();
    $s->update($data);
    return $s->state;
}

// ---- CRC32 ----
class Crc32 {
    private $table;
    private $crc;
    public function __construct($poly = 0xEDB88320) {
        $this->table = [];
        for ($i = 0; $i < 256; ++$i) {
            $c = $i;
            for ($j = 0; $j < 8; ++$j) {
                $c = ($c & 1) ? (($c >> 1) ^ $poly) : ($c >> 1);
            }
            $this->table[$i] = $c & 0xFFFFFFFF;
        }
        $this->crc = 0xFFFFFFFF;
    }
    public function update($data) {
        for ($i = 0; $i < strlen($data); ++$i) {
            $this->crc = $this->table[($this->crc ^ ord($data[$i])) & 0xFF] ^ ($this->crc >> 8);
            $this->crc &= 0xFFFFFFFF;
        }
    }
    public function evaluate() {
        return $this->crc ^ 0xFFFFFFFF;
    }
}

// ---- WinRAR Keygen ----
// Curve parameters from WinRarConfig.hpp
// A = 0 (zero element)
// B = element with Items[0] = 161
// G = base point
// Order
define('WINRAR_ORDER', '0x1026dd85081b82314691ced9bbec30547840e4bf72d8b5e0d258442bbcd31');
define('WINRAR_PRIVATE_KEY', '0x59fe6abcca90bdb95f0105271fa85fb9f11f467450c1ae9044b7fd61d65e');

$WINRAR_GX = [0x38CC, 0x052F, 0x2510, 0x45AA, 0x1B89, 0x4468, 0x4882, 0x0D67, 0x4FEB, 0x55CE, 0x0025, 0x4CB7, 0x0CC2, 0x59DC, 0x289E, 0x65E3, 0x56FD];
$WINRAR_GY = [0x31A7, 0x65F2, 0x18C4, 0x3412, 0x7388, 0x54C1, 0x539B, 0x4A02, 0x4D07, 0x12D6, 0x7911, 0x3B5E, 0x4F0E, 0x216F, 0x2BF2, 0x1974, 0x20DA];

function winrar_generate_private_key($seed) {
    // Generate private key from seed (or empty for default master key)
    if (strlen($seed) > 0) {
        $state = winrar_sha1_state($seed);
        $generator = [0];
        for ($i = 0; $i < 5; ++$i) {
            $generator[$i + 1] = $state[$i];
        }
    } else {
        $generator = [0, 0xeb3eb781, 0x50265329, 0xdc5ef4a3, 0x6847b9d5, 0xcde43b4c];
    }

    $rawKey = [];
    for ($i = 0; $i < 15; ++$i) {
        $generator[0] = $i + 1;
        $sha1 = new Sha1State();
        // C++: Generator is uint32_t[6] on LE machine → raw bytes are little-endian
        $packet = '';
        foreach ($generator as $g) {
            $packet .= chr($g & 0xFF) . chr(($g >> 8) & 0xFF) . chr(($g >> 16) & 0xFF) . chr(($g >> 24) & 0xFF);
        }
        $sha1->update($packet);
        $totalBits = $sha1->count * 8;
        $sha1->update("\x80");
        while (strlen($sha1->buffer) % 64 != 56) $sha1->update("\x00");
        $lenBytes = '';
        for ($j = 7; $j >= 0; --$j) $lenBytes .= chr(($totalBits >> ($j * 8)) & 0xFF);
        $sha1->update($lenBytes);
        $rawKey[] = $sha1->state[0] & 0xFFFF;  // Low 16 bits (matches C++ static_cast<uint16_t>)
    }

    // Convert rawKey (15 x uint16) to a big integer (little-endian)
    $result = "0";
    for ($i = 14; $i >= 0; --$i) {
        $result = gmp_add(gmp_mul($result, "65536"), (string)$rawKey[$i]);
    }
    return $result;
}

function winrar_generate_public_key_sm2($username) {
    $privKey = winrar_generate_private_key($username);
    $G = new ECPoint($GLOBALS['WINRAR_GX'], $GLOBALS['WINRAR_GY']);
    $pubKey = ec_mul($G, gmp_strval($privKey, 16));
    // X as integer: items[0] + items[1]*2^15 + ... + items[16]*2^240
    $xInt = "0";
    for ($i = 16; $i >= 0; --$i) {
        $xInt = gmp_add(gmp_mul($xInt, "32768"), (string)$pubKey->x[$i]);
    }
    // parity of Y/X
    $yOverX = gf17_div($pubKey->y, $pubKey->x);
    $parity = $yOverX[0] & 1;
    // SM2 compressed: 2*X + parity
    $xInt = gmp_mul($xInt, "2");
    if ($parity) $xInt = gmp_or($xInt, "1");
    $hex = gmp_strval($xInt, 16);
    $hex = str_pad($hex, 64, "0", STR_PAD_LEFT);
    return $hex;
}

function winrar_sign($data) {
    $order = gmp_init(WINRAR_ORDER, 16);
    $privKey = gmp_init(WINRAR_PRIVATE_KEY, 16);
    $G = new ECPoint($GLOBALS['WINRAR_GX'], $GLOBALS['WINRAR_GY']);
    $hashInt = winrar_generate_hash_integer($data);

    while (true) {
        // Generate random
        $random = "0";
        for ($i = 0; $i < 15; ++$i) {
            $random = gmp_add(gmp_mul($random, "65536"), (string)mt_rand(0, 0xFFFF));
        }

        // r = X(Random * G) + hash mod order
        $rG = ec_mul($G, gmp_strval($random, 16));
        $rX = gf17_to_bigint($rG->x);
        $r = gmp_mod(gmp_add($rX, $hashInt), $order);

        if (gmp_cmp($r, "0") == 0 || gmp_cmp(gmp_add($r, $random), $order) == 0) continue;

        // s = Random - PrivateKey * r mod order
        $s = gmp_mod(gmp_sub($random, gmp_mul($privKey, $r)), $order);
        if (gmp_cmp($s, "0") == 0) continue;

        return [$r, $s];
    }
}

function winrar_generate_hash_integer($data) {
    $state = winrar_sha1_state($data);

    // Build 30-byte RawHash matching C++ layout (LE machine):
    //   C++: RawHash[i] = BSWAP32(LE_uint32_from_SHA1_bytes)
    //   => each state word stored as LE bytes (= sha1 digest bytes reversed per-word)
    //   bytes 0..19: SHA-1 state words as LE bytes
    //   bytes 20..23: 0x0ffd8d43 as LE bytes
    //   bytes 24..27: 0xb4e33c7c as LE bytes  
    //   bytes 28..29: 0x53461bd1 first 2 LE bytes
    $rawHash = '';
    for ($i = 0; $i < 5; ++$i) {
        $rawHash .= chr($state[$i] & 0xFF);
        $rawHash .= chr(($state[$i] >> 8) & 0xFF);
        $rawHash .= chr(($state[$i] >> 16) & 0xFF);
        $rawHash .= chr(($state[$i] >> 24) & 0xFF);
    }
    $c0 = 0x0ffd8d43;
    $c1 = 0xb4e33c7c;
    $c2 = 0x53461bd1;
    $rawHash .= chr($c0 & 0xFF) . chr(($c0 >> 8) & 0xFF) . chr(($c0 >> 16) & 0xFF) . chr(($c0 >> 24) & 0xFF);
    $rawHash .= chr($c1 & 0xFF) . chr(($c1 >> 8) & 0xFF) . chr(($c1 >> 16) & 0xFF) . chr(($c1 >> 24) & 0xFF);
    $rawHash .= chr($c2 & 0xFF) . chr(($c2 >> 8) & 0xFF);

    // LE BigInt: BigInteger(false, RawHash, 30, true)
    $result = "0";
    for ($i = 29; $i >= 0; --$i) {
        $result = gmp_add(gmp_mul($result, "256"), (string)ord($rawHash[$i]));
    }
    return $result;
}

// ---- Main key generation ----
function winrar_generate($username, $licenseType) {
    // Step 1: Public key from username
    $temp = winrar_generate_public_key_sm2($username);
    $items = array_fill(0, 4, '');

    // Items[3] = "60" + first 48 chars of temp
    $items[3] = "60" . substr($temp, 0, 48);

    // Items[0] = public key SM2 format from Items[3]
    $items[0] = winrar_generate_public_key_sm2($items[3]);

    // UID = first 16 chars of temp (offset 48) + first 4 chars of Items[0]
    $uid = substr($temp, 48, 16) . substr($items[0], 0, 4);

    // Sign license type
    while (true) {
        list($r, $s) = winrar_sign($licenseType);
        $rHex = gmp_strval($r, 16);
        $sHex = gmp_strval($s, 16);
        $rHex = str_pad($rHex, 60, "0", STR_PAD_LEFT);
        $sHex = str_pad($sHex, 60, "0", STR_PAD_LEFT);
        if (strlen($rHex) === 60 && strlen($sHex) === 60) {
            $items[1] = "60" . $sHex . $rHex;
            break;
        }
    }

    // Sign username + Items[0]
    $signData = $username . $items[0];
    while (true) {
        list($r, $s) = winrar_sign($signData);
        $rHex = gmp_strval($r, 16);
        $sHex = gmp_strval($s, 16);
        $rHex = str_pad($rHex, 60, "0", STR_PAD_LEFT);
        $sHex = str_pad($sHex, 60, "0", STR_PAD_LEFT);
        if (strlen($rHex) === 60 && strlen($sHex) === 60) {
            $items[2] = "60" . $sHex . $rHex;
            break;
        }
    }

    // Calculate checksum
    $crc = new Crc32();
    $crc->update($licenseType);
    $crc->update($username);
    $crc->update($items[0]);
    $crc->update($items[1]);
    $crc->update($items[2]);
    $crc->update($items[3]);
    // C++: Info.Checksum = ~Crc32.Evaluate() = raw CRC accumulator (undoes the final XOR ^ 0xFFFFFFFF)
    $checksum = $crc->evaluate() ^ 0xFFFFFFFF;

    $hexData = sprintf("%u%u%u%u%s%s%s%s%010u",
        strlen($items[0]), strlen($items[1]), strlen($items[2]), strlen($items[3]),
        $items[0], $items[1], $items[2], $items[3], $checksum);

    return [
        'username' => $username,
        'licenseType' => $licenseType,
        'uid' => "UID=" . $uid,
        'items' => $items,
        'checksum' => $checksum,
        'hexData' => $hexData
    ];
}

// ---- CLI / Web handler ----
header('Content-Type: text/html; charset=utf-8');

$username = $_POST['username'] ?? '';
$licenseType = $_POST['license_type'] ?? 'Single PC usage license';
$output = '';

if ($username !== '') {
    try {
        $displayUser = $username;
        $displayLicense = $licenseType;
        $hasNonAscii = function($s) { for ($i = 0; $i < strlen($s); ++$i) if (ord($s[$i]) > 127) return true; return false; };
        if ($hasNonAscii($displayUser) && !str_starts_with($displayUser, 'utf8:'))
            $displayUser = 'utf8:' . $displayUser;
        if ($hasNonAscii($displayLicense) && !str_starts_with($displayLicense, 'utf8:'))
            $displayLicense = 'utf8:' . $displayLicense;
        $reg = winrar_generate($displayUser, $displayLicense);
        $output = "RAR registration data\r\n";
        $output .= $displayUser . "\r\n";
        $output .= $displayLicense . "\r\n";
        $output .= $reg['uid'] . "\r\n";
        $data = $reg['hexData'];
        while (strlen($data) > 0) {
            $output .= substr($data, 0, 54) . "\r\n";
            $data = substr($data, 54);
        }
    } catch (Exception $e) {
        $output = "Error: " . $e->getMessage();
    }
}
?><!DOCTYPE html>
<html lang="es">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>WinRAR Keygen</title>
<style>
* { margin: 0; padding: 0; box-sizing: border-box; }
body { font-family: 'Segoe UI', sans-serif; background: linear-gradient(135deg, #0b1120, #111827); color: #e2e8f0; min-height: 100vh; display: flex; align-items: center; justify-content: center; }
.container { width: 100%; max-width: 560px; padding: 20px; }
.card { background: rgba(30,41,59,0.85); backdrop-filter: blur(12px); border-radius: 20px; padding: 36px 28px; border: 1px solid rgba(51,65,85,0.6); box-shadow: 0 25px 50px -12px rgba(0,0,0,0.6); position: relative; overflow: hidden; }
.card::before { content: ''; position: absolute; top: 0; left: 0; right: 0; height: 2px; background: linear-gradient(90deg, transparent, #f59e0b, #ef4444, transparent); }
.logo { display: flex; align-items: center; justify-content: center; gap: 10px; margin-bottom: 16px; }
.logo-icon { width: 36px; height: 36px; background: linear-gradient(135deg, #f59e0b, #ef4444); border-radius: 8px; display: flex; align-items: center; justify-content: center; font-size: 14px; font-weight: 800; color: white; }
h1 { font-size: 24px; font-weight: 700; text-align: center; color: #f8fafc; }
.subtitle { text-align: center; color: #94a3b8; font-size: 13px; margin-bottom: 24px; }
.form-group { margin-bottom: 16px; }
label { display: block; font-size: 13px; font-weight: 600; color: #cbd5e1; margin-bottom: 6px; }
input[type="text"], select { width: 100%; padding: 10px 14px; border-radius: 10px; border: 1px solid #475569; background: #0f172a; color: #e2e8f0; font-size: 14px; outline: none; transition: border-color 0.2s; }
input[type="text"]:focus, select:focus { border-color: #f59e0b; }
.btn { display: inline-flex; align-items: center; gap: 8px; background: linear-gradient(135deg, #f59e0b, #ef4444); color: white; border: none; padding: 12px 36px; border-radius: 10px; font-size: 14px; font-weight: 600; cursor: pointer; transition: all 0.2s; width: 100%; justify-content: center; }
.btn:hover { box-shadow: 0 6px 20px rgba(245,158,11,0.35); transform: translateY(-1px); }
.result-box { margin-top: 20px; background: #0f172a; border: 1px solid #334155; border-radius: 12px; padding: 16px; overflow: auto; }
.result-box pre { font-family: 'Cascadia Code', 'Consolas', monospace; font-size: 11px; color: #a7f3d0; white-space: pre-wrap; word-break: break-all; line-height: 1.5; }
.hidden { display: none; }
.footer { text-align: center; margin-top: 20px; color: rgba(71,85,105,0.7); font-size: 11px; }
.note { font-size: 11px; color: #64748b; text-align: center; margin-top: 12px; }
</style>
</head>
<body>
<div class="container">
<div class="card">
<div class="logo"><div class="logo-icon">WR</div><h1>WinRAR Keygen</h1></div>
<p class="subtitle">Genera tu licencia <strong>rarreg.key</strong> para WinRAR</p>
<form method="post">
<div class="form-group">
<label for="username">Nombre de usuario</label>
<input type="text" id="username" name="username" value="<?= htmlspecialchars($username) ?>" placeholder="Ej: Tu Nombre" required>
</div>
<div class="form-group">
<label for="license_type">Tipo de licencia</label>
<select id="license_type" name="license_type">
<option value="Single PC usage license" <?= $licenseType === 'Single PC usage license' ? 'selected' : '' ?>>Single PC usage license</option>
<option value="Single PC usage license (business)" <?= $licenseType === 'Single PC usage license (business)' ? 'selected' : '' ?>>Single PC usage license (business)</option>
<option value="Uso Personal" <?= $licenseType === 'Uso Personal' ? 'selected' : '' ?>>Uso Personal</option>
</select>
</div>
<button type="submit" class="btn">
<svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"/><polyline points="7 10 12 15 17 10"/><line x1="12" y1="15" x2="12" y2="3"/></svg>
Generar licencia
</button>
</form>
<?php if ($output !== ''): ?>
<div class="result-box">
<pre id="keyContent"><?= htmlspecialchars($output) ?></pre>
</div>
<button onclick="downloadKey()" class="btn download-btn">
<svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"/><polyline points="7 10 12 15 17 10"/><line x1="12" y1="15" x2="12" y2="3"/></svg>
Descargar rarreg.key
</button>
<p class="note">Tambien puedes copiar el contenido manualmente</p>
<script>
function downloadKey(){var t=document.getElementById('keyContent').textContent,c=new Blob([t],{type:'application/octet-stream'}),u=URL.createObjectURL(c),a=document.createElement('a');a.href=u;a.download='rarreg.key';a.click();URL.revokeObjectURL(u)}
</script>
<?php endif; ?>
</div>
<div class="footer">Basado en <a href="https://github.com/bitcookies/winrar-keygen" style="color:#64748b;">bitcookies/winrar-keygen</a></div>
</div>
</body>
</html>