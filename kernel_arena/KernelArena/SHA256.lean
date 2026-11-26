/-
Pure-Init FIPS 180-4 SHA-256 implementation (zero external dependencies).
-/

namespace KernelArena
namespace SHA256

private def kConsts : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

private def initH : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

@[inline] private def rotr32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

private def padMessage (input : ByteArray) : ByteArray := Id.run do
  let bitLen : Nat := input.size * 8
  let mut out := input.push 0x80
  while out.size % 64 != 56 do
    out := out.push 0
  for i in [0:8] do
    let shiftBits := (7 - i) * 8
    let b := (bitLen >>> shiftBits) % 256
    out := out.push (UInt8.ofNat b)
  return out

private def readWordBE (buf : ByteArray) (offset : Nat) : UInt32 :=
  let b0 := (buf.get! offset).toUInt32
  let b1 := (buf.get! (offset + 1)).toUInt32
  let b2 := (buf.get! (offset + 2)).toUInt32
  let b3 := (buf.get! (offset + 3)).toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

private def wordToHex (w : UInt32) : String := Id.run do
  let mut s := ""
  for i in [0:8] do
    let shift : UInt32 := UInt32.ofNat ((7 - i) * 4)
    let nib := ((w >>> shift) &&& 0xf).toNat
    s := s.push (hexDigit nib)
  return s

def sha256Bytes (input : ByteArray) : String := Id.run do
  let padded := padMessage input
  let numBlocks := padded.size / 64
  let mut h := initH
  for blk in [0:numBlocks] do
    let base := blk * 64
    let mut w : Array UInt32 := Array.replicate 64 0
    for i in [0:16] do
      w := w.set! i (readWordBE padded (base + i * 4))
    for i in [16:64] do
      let w15 := w[i - 15]!
      let w2 := w[i - 2]!
      let s0 := (rotr32 w15 7) ^^^ (rotr32 w15 18) ^^^ (w15 >>> 3)
      let s1 := (rotr32 w2 17) ^^^ (rotr32 w2 19) ^^^ (w2 >>> 10)
      w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)
    let mut a := h[0]!
    let mut b := h[1]!
    let mut c := h[2]!
    let mut d := h[3]!
    let mut e := h[4]!
    let mut f := h[5]!
    let mut g := h[6]!
    let mut hh := h[7]!
    for i in [0:64] do
      let s1 := (rotr32 e 6) ^^^ (rotr32 e 11) ^^^ (rotr32 e 25)
      let ch := (e &&& f) ^^^ ((~~~e) &&& g)
      let temp1 := hh + s1 + ch + kConsts[i]! + w[i]!
      let s0 := (rotr32 a 2) ^^^ (rotr32 a 13) ^^^ (rotr32 a 22)
      let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let temp2 := s0 + maj
      hh := g
      g := f
      f := e
      e := d + temp1
      d := c
      c := b
      b := a
      a := temp1 + temp2
    h := h.set! 0 (h[0]! + a)
    h := h.set! 1 (h[1]! + b)
    h := h.set! 2 (h[2]! + c)
    h := h.set! 3 (h[3]! + d)
    h := h.set! 4 (h[4]! + e)
    h := h.set! 5 (h[5]! + f)
    h := h.set! 6 (h[6]! + g)
    h := h.set! 7 (h[7]! + hh)
  let mut hex := ""
  for i in [0:8] do
    hex := hex ++ wordToHex h[i]!
  return hex

def sha256Hex (s : String) : String :=
  sha256Bytes s.toUTF8

end SHA256
end KernelArena
