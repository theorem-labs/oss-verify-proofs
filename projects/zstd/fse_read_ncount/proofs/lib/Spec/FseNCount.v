(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Inductive res (A : Type) : Type :=
| Ok : A -> res A
| Err : Z -> res A
| Ub : res A
| NoFuel : res A.
Arguments Ok {A} _.
Arguments Err {A} _.
Arguments Ub {A}.
Arguments NoFuel {A}.
Definition bind {A B : Type} (m : res A) (k : A -> res B) : res B :=
match m with
| Ok a => k a
| Err e => Err e
| Ub => Ub
| NoFuel => NoFuel
end.
Notation "'let!' x ':=' m 'in' k" := (bind m (fun x => k))
(at level 200, x pattern, m at level 100, k at level 200, right associativity).
Definition assert (b : bool) : res unit := if b then Ok tt else Ub.
Definition ZSTD_error_GENERIC : Z := 1.
Definition ZSTD_error_corruption_detected : Z := 20.
Definition ZSTD_error_tableLog_tooLarge : Z := 44.
Definition ZSTD_error_maxSymbolValue_tooSmall : Z := 48.
Definition ZSTD_error_dstSize_tooSmall : Z := 70.
Definition FSE_MIN_TABLELOG : Z := 5.
Definition FSE_MAX_TABLELOG : Z := 12.
Definition FSE_TABLELOG_ABSOLUTE_MAX : Z := 15.
Definition FSE_NCOUNTBOUND : Z := 512.
Definition u32 (x : Z) : Z := x mod 2^32.
Definition to_byte (x : Z) : Z := x mod 256.
Definition to_short (x : Z) : Z := (x + 2^15) mod 2^16 - 2^15.
Definition shl32 (x n : Z) : res Z :=
if (0 <=? n) && (n <? 32) then Ok (u32 (x * 2^n)) else Ub.
Definition shr32 (x n : Z) : res Z :=
if (0 <=? n) && (n <? 32) then Ok (x / 2^n) else Ub.
Definition not32 (x : Z) : Z := 2^32 - 1 - x.
Fixpoint ctz_aux (fuel : nat) (x : Z) : Z :=
match fuel with
| O => 0
| S f => if Z.odd x then 0 else 1 + ctz_aux f (Z.div2 x)
end.
Definition ctz32 (x : Z) : res Z :=
if u32 x =? 0 then Ub else Ok (ctz_aux 32 (u32 x)).
Definition highbit32 (x : Z) : res Z :=
if (0 <? x) && (x <? 2^32) then Ok (Z.log2 x) else Ub.
Definition Zlength {A} (l : list A) : Z := Z.of_nat (length l).
Definition Znth (i : Z) (l : list Z) : Z := nth (Z.to_nat i) l 0.
Fixpoint upd_nat (n : nat) (v : Z) (l : list Z) : list Z :=
match l, n with
| [], _ => []
| _ :: t, O => v :: t
| h :: t, S n' => h :: upd_nat n' v t
end.
Definition Zupd (i : Z) (v : Z) (l : list Z) : list Z := upd_nat (Z.to_nat i) v l.
Definition load (l : list Z) (i : Z) : res Z :=
if (0 <=? i) && (i <? Zlength l) then Ok (Znth i l) else Ub.
Definition store (l : list Z) (i v : Z) : res (list Z) :=
if (0 <=? i) && (i <? Zlength l) then Ok (Zupd i v l) else Ub.
Definition readLE32 (buf : list Z) (ip : Z) : res Z :=
if (0 <=? ip) && (ip + 4 <=? Zlength buf) then
Ok (Znth ip buf + 2^8 * Znth (ip+1) buf + 2^16 * Znth (ip+2) buf + 2^24 * Znth (ip+3) buf)
else Ub.
Inductive flow (S : Type) : Type := Cont : S -> flow S | Brk : S -> flow S.
Arguments Cont {S} _.
Arguments Brk {S} _.
Definition write_bound (maxSymbolValue tableLog : Z) : Z :=
let maxHeaderSize := ((maxSymbolValue + 1) * tableLog + 4 + 2) / 8 + 1 + 2 in
if maxSymbolValue =? 0 then FSE_NCOUNTBOUND else maxHeaderSize.
Record wstate := mkW {
w_buf : list Z;
w_out : Z;
w_bitStream : Z;
w_bitCount : Z;
w_symbol : Z;
w_remaining : Z;
w_threshold : Z;
w_nbBits : Z;
w_previousIs0 : bool
}.
Section Writer.
Variable nc : list Z.
Variable alphabetSize : Z.
Variable bufSize : Z.
Variable writeIsSafe : bool.
Definition wflush (dec16 : bool) (s : wstate) : res wstate :=
if negb writeIsSafe && (bufSize - 2 <? w_out s) then Err ZSTD_error_dstSize_tooSmall
else
let! b1 := store (w_buf s) (w_out s) (to_byte (w_bitStream s)) in
let! b2 := store b1 (w_out s + 1) (to_byte (w_bitStream s / 2^8)) in
Ok (mkW b2 (w_out s + 2) (w_bitStream s / 2^16)
(if dec16 then w_bitCount s - 16 else w_bitCount s)
(w_symbol s) (w_remaining s) (w_threshold s) (w_nbBits s) (w_previousIs0 s)).
Definition wflush_if (s : wstate) : res wstate :=
if 16 <? w_bitCount s then wflush true s else Ok s.
Fixpoint skip_zeros (fuel : nat) (symbol : Z) : res Z :=
match fuel with
| O => NoFuel
| S f =>
if symbol <? alphabetSize then
let! c := load nc symbol in
if c =? 0 then skip_zeros f (symbol + 1) else Ok symbol
else Ok symbol
end.
Fixpoint run24 (fuel : nat) (s : wstate) (start : Z) : res (wstate * Z) :=
match fuel with
| O => NoFuel
| S f =>
if start + 24 <=? w_symbol s then
let start' := start + 24 in
let! v := shl32 65535 (w_bitCount s) in
let s1 := mkW (w_buf s) (w_out s) (u32 (w_bitStream s + v)) (w_bitCount s)
(w_symbol s) (w_remaining s) (w_threshold s) (w_nbBits s) (w_previousIs0 s) in
let! s2 := wflush false s1 in
run24 f s2 start'
else Ok (s, start)
end.
Fixpoint run3 (fuel : nat) (s : wstate) (start : Z) : res (wstate * Z) :=
match fuel with
| O => NoFuel
| S f =>
if start + 3 <=? w_symbol s then
let start' := start + 3 in
let! v := shl32 3 (w_bitCount s) in
let s1 := mkW (w_buf s) (w_out s) (u32 (w_bitStream s + v)) (w_bitCount s + 2)
(w_symbol s) (w_remaining s) (w_threshold s) (w_nbBits s) (w_previousIs0 s) in
run3 f s1 start'
else Ok (s, start)
end.
Definition wzero_block (s : wstate) : res (flow wstate) :=
let start := w_symbol s in
let! symbol := skip_zeros (S (Z.to_nat alphabetSize)) (w_symbol s) in
let s0 := mkW (w_buf s) (w_out s) (w_bitStream s) (w_bitCount s)
symbol (w_remaining s) (w_threshold s) (w_nbBits s) (w_previousIs0 s) in
if symbol =? alphabetSize then Ok (Brk s0)
else
let! r1 := run24 (S (Z.to_nat alphabetSize)) s0 start in
let '(s1, start1) := r1 in
let! r2 := run3 (S (Z.to_nat alphabetSize)) s1 start1 in
let '(s2, start2) := r2 in
let! v := shl32 (u32 (symbol - start2)) (w_bitCount s2) in
let s3 := mkW (w_buf s2) (w_out s2) (u32 (w_bitStream s2 + v)) (w_bitCount s2 + 2)
(w_symbol s2) (w_remaining s2) (w_threshold s2) (w_nbBits s2) (w_previousIs0 s2) in
let! s4 := wflush_if s3 in
Ok (Cont s4)
.
Fixpoint shrink (fuel : nat) (remaining threshold nbBits : Z) : res (Z * Z) :=
match fuel with
| O => NoFuel
| S f =>
if remaining <? threshold then shrink f remaining (threshold / 2) (nbBits - 1)
else Ok (threshold, nbBits)
end.
Definition wcount_block (s : wstate) : res wstate :=
let! count := load nc (w_symbol s) in
let symbol := w_symbol s + 1 in
let max := 2 * w_threshold s - 1 - w_remaining s in
let remaining := w_remaining s - (if count <? 0 then - count else count) in
let count1 := count + 1 in
let count2 := if w_threshold s <=? count1 then count1 + max else count1 in
let! v := shl32 (u32 count2) (w_bitCount s) in
let bitStream := u32 (w_bitStream s + v) in
let bitCount := w_bitCount s + w_nbBits s - (if count2 <? max then 1 else 0) in
let previousIs0 := (count2 =? 1) in
if remaining <? 1 then Err ZSTD_error_GENERIC
else
let! tn := shrink 64%nat remaining (w_threshold s) (w_nbBits s) in
let '(threshold, nbBits) := tn in
Ok (mkW (w_buf s) (w_out s) bitStream bitCount symbol remaining threshold nbBits previousIs0).
Definition wbody (s : wstate) : res (flow wstate) :=
let! f := (if w_previousIs0 s then wzero_block s else Ok (Cont s)) in
match f with
| Brk s' => Ok (Brk s')
| Cont s1 =>
let! s2 := wcount_block s1 in
let! s3 := wflush_if s2 in
Ok (Cont s3)
end.
Fixpoint wloop (fuel : nat) (s : wstate) : res wstate :=
match fuel with
| O => NoFuel
| S f =>
if (w_symbol s <? alphabetSize) && (1 <? w_remaining s) then
let! fl := wbody s in
match fl with
| Brk s' => Ok s'
| Cont s' => wloop f s'
end
else Ok s
end.
Definition wfinish (s : wstate) : res (list Z * Z) :=
if negb (w_remaining s =? 1) then Err ZSTD_error_GENERIC
else if negb writeIsSafe && (bufSize - 2 <? w_out s) then Err ZSTD_error_dstSize_tooSmall
else
let! b1 := store (w_buf s) (w_out s) (to_byte (w_bitStream s)) in
let! b2 := store b1 (w_out s + 1) (to_byte (w_bitStream s / 2^8)) in
Ok (b2, w_out s + Z.quot (w_bitCount s + 7) 8).
End Writer.
Definition winit (buf : list Z) (tableLog : Z) : res wstate :=
let! _ := assert ((0 <=? tableLog) && (tableLog <? 31)) in
let tableSize := 2^tableLog in
let! v := shl32 (u32 (tableLog - FSE_MIN_TABLELOG)) 0 in
let bitStream := u32 (0 + v) in
let bitCount := 0 + 4 in
Ok (mkW buf 0 bitStream bitCount 0 (tableSize + 1) tableSize (tableLog + 1) false).
Definition write_ncount_generic (buf : list Z) (nc : list Z)
(maxSymbolValue tableLog : Z) (writeIsSafe : bool) : res (list Z * Z) :=
let bufSize := Zlength buf in
let alphabetSize := maxSymbolValue + 1 in
let! s0 := winit buf tableLog in
let! s1 := wloop nc alphabetSize bufSize writeIsSafe (S (Z.to_nat alphabetSize)) s0 in
wfinish bufSize writeIsSafe s1.
Definition write_ncount (buf : list Z) (nc : list Z) (maxSymbolValue tableLog : Z)
: res (list Z * Z) :=
if FSE_MAX_TABLELOG <? tableLog then Err ZSTD_error_tableLog_tooLarge
else if tableLog <? FSE_MIN_TABLELOG then Err ZSTD_error_GENERIC
else if Zlength buf <? write_bound maxSymbolValue tableLog
then write_ncount_generic buf nc maxSymbolValue tableLog false
else write_ncount_generic buf nc maxSymbolValue tableLog true.
Record rstate := mkR {
r_nc : list Z;
r_ip : Z;
r_bitStream : Z;
r_bitCount : Z;
r_charnum : Z;
r_remaining : Z;
r_threshold : Z;
r_nbBits : Z;
r_previous0 : bool
}.
Definition repeats_of (bitStream : Z) : res Z :=
let! c := ctz32 (Z.lor (not32 bitStream) (2^31)) in Ok (c / 2).
Section Reader.
Variable buf : list Z.
Variable maxSV1 : Z.
Let hbSize : Z := Zlength buf.
Definition reload (s : rstate) : res rstate :=
let ip := r_ip s in
let bc := r_bitCount s in
let '(ip', bc') :=
if (ip <=? hbSize - 7) || (ip + Z.shiftr bc 3 <=? hbSize - 4)
then (ip + Z.shiftr bc 3, Z.land bc 7)
else (hbSize - 4, Z.land (bc - 8 * (hbSize - 4 - ip)) 31) in
let! w := readLE32 buf ip' in
let! bs := shr32 w bc' in
Ok (mkR (r_nc s) ip' bs bc' (r_charnum s) (r_remaining s) (r_threshold s) (r_nbBits s) (r_previous0 s)).
Fixpoint rep_loop (fuel : nat) (s : rstate) (repeats : Z) : res (rstate * Z) :=
match fuel with
| O => NoFuel
| S f =>
if 12 <=? repeats then
let charnum := r_charnum s + 3 * 12 in
let ip := r_ip s in
let bc := r_bitCount s in
let '(ip', bc') :=
if ip <=? hbSize - 7 then (ip + 3, bc)
else (hbSize - 4, Z.land (bc - 8 * (hbSize - 7 - ip)) 31) in
let! w := readLE32 buf ip' in
let! bs := shr32 w bc' in
let! repeats' := repeats_of bs in
rep_loop f (mkR (r_nc s) ip' bs bc' charnum (r_remaining s) (r_threshold s) (r_nbBits s) (r_previous0 s)) repeats'
else Ok (s, repeats)
end.
Definition rzero_block (s : rstate) : res (flow rstate) :=
let! repeats := repeats_of (r_bitStream s) in
let! r := rep_loop (S (Z.to_nat hbSize)) s repeats in
let '(s1, repeats1) := r in
let charnum := r_charnum s1 + 3 * repeats1 in
let! bs := shr32 (r_bitStream s1) (2 * repeats1) in
let bc := r_bitCount s1 + 2 * repeats1 in
let charnum' := charnum + Z.land bs 3 in
let bc' := bc + 2 in
let s2 := mkR (r_nc s1) (r_ip s1) bs bc' charnum' (r_remaining s1) (r_threshold s1) (r_nbBits s1) (r_previous0 s1) in
if maxSV1 <=? charnum' then Ok (Brk s2)
else let! s3 := reload s2 in Ok (Cont s3).
Definition rcount_block (s : rstate) : res (flow rstate) :=
let threshold := r_threshold s in
let max := 2 * threshold - 1 - r_remaining s in
let bs := r_bitStream s in
let '(count0, bc) :=
if Z.land bs (threshold - 1) <? u32 max
then (Z.land bs (threshold - 1), r_bitCount s + (r_nbBits s - 1))
else (let c := Z.land bs (2 * threshold - 1) in
((if threshold <=? c then c - max else c), r_bitCount s + r_nbBits s)) in
let count := count0 - 1 in
let remaining := if 0 <=? count then r_remaining s - count else r_remaining s + count in
let! nc' := store (r_nc s) (r_charnum s) (to_short count) in
let charnum := r_charnum s + 1 in
let previous0 := (count =? 0) in
let! upd := (if remaining <? threshold then
if remaining <=? 1 then Ok None
else let! hb := highbit32 remaining in
let nbBits := hb + 1 in
let! _ := assert ((0 <=? nbBits - 1) && (nbBits - 1 <? 31)) in
Ok (Some (2^(nbBits - 1), nbBits))
else Ok (Some (threshold, r_nbBits s))) in
match upd with
| None =>
Ok (Brk (mkR nc' (r_ip s) bs bc charnum remaining threshold (r_nbBits s) previous0))
| Some (threshold', nbBits') =>
let s1 := mkR nc' (r_ip s) bs bc charnum remaining threshold' nbBits' previous0 in
if maxSV1 <=? charnum then Ok (Brk s1)
else let! s2 := reload s1 in Ok (Cont s2)
end.
Definition rbody (s : rstate) : res (flow rstate) :=
let! f := (if r_previous0 s then rzero_block s else Ok (Cont s)) in
match f with
| Brk s' => Ok (Brk s')
| Cont s1 => rcount_block s1
end.
Fixpoint rloop (fuel : nat) (s : rstate) : res rstate :=
match fuel with
| O => NoFuel
| S f =>
let! fl := rbody s in
match fl with
| Brk s' => Ok s'
| Cont s' => rloop f s'
end
end.
Fixpoint zero_prefix (n : nat) (l : list Z) : list Z :=
match n, l with
| O, _ => l
| S n', [] => []
| S n', _ :: t => 0 :: zero_prefix n' t
end.
Definition read_ncount_body8 (nc0 : list Z) : res (list Z * Z * Z * Z) :=
let! _ := assert (maxSV1 <=? Zlength nc0) in
let nc := zero_prefix (Z.to_nat maxSV1) nc0 in
let! bitStream := readLE32 buf 0 in
let nbBits := Z.land bitStream 15 + FSE_MIN_TABLELOG in
if FSE_TABLELOG_ABSOLUTE_MAX <? nbBits then Err ZSTD_error_tableLog_tooLarge
else
let! bitStream1 := shr32 bitStream 4 in
let bitCount := 4 in
let tableLog := nbBits in
let! _ := assert ((0 <=? nbBits) && (nbBits <? 31)) in
let remaining := 2^nbBits + 1 in
let threshold := 2^nbBits in
let nbBits1 := nbBits + 1 in
let s0 := mkR nc 0 bitStream1 bitCount 0 remaining threshold nbBits1 false in
let! s := rloop (S (Z.to_nat maxSV1)) s0 in
if negb (r_remaining s =? 1) then Err ZSTD_error_corruption_detected
else if maxSV1 <? r_charnum s then Err ZSTD_error_maxSymbolValue_tooSmall
else if 32 <? r_bitCount s then Err ZSTD_error_corruption_detected
else
let maxSV := r_charnum s - 1 in
let ip := r_ip s + Z.shiftr (r_bitCount s + 7) 3 in
Ok (r_nc s, maxSV, tableLog, ip).
End Reader.
Definition read_ncount (nc0 : list Z) (maxSV : Z) (buf : list Z) : res (list Z * Z * Z * Z) :=
let hbSize := Zlength buf in
let maxSV1 := maxSV + 1 in
if hbSize <? 8 then
let buffer := buf ++ repeat 0 (Z.to_nat (8 - hbSize)) in
let! r := read_ncount_body8 buffer maxSV1 nc0 in
let '(nc, msv, tl, countSize) := r in
if hbSize <? countSize then Err ZSTD_error_corruption_detected
else Ok (nc, msv, tl, countSize)
else read_ncount_body8 buf maxSV1 nc0.
Fixpoint harness_fill (fuel : nat) (draws : list Z) (s maxSymbolValue remainingWeight : Z)
(acc : list Z) : option (list Z * Z * list Z) :=
match fuel with
| O => Some (acc, remainingWeight, draws)
| S f =>
if (s <? maxSymbolValue) && (0 <? remainingWeight) then
match draws with
| [] => None
| n :: draws' =>
if (-1 <=? n) && (n <=? remainingWeight) then
let rw := if n <? 0 then remainingWeight - 1 else remainingWeight - n in
harness_fill f draws' (s + 1) maxSymbolValue rw (acc ++ [n])
else None
end
else Some (acc, remainingWeight, draws)
end.
Definition harness_ncount (tableLog maxSymbolValue : Z) (draws : list Z) (lastIsMinus1 : bool)
: option (list Z) :=
let remainingWeight := 2^tableLog - 1 in
match harness_fill 256%nat draws 0 maxSymbolValue remainingWeight [] with
| None => None
| Some (pre, rw, _) =>
let nc0 := pre ++ repeat 0 (256 - length pre) in
let v := rw + 1 in
let v' := if (v =? 1) && lastIsMinus1 then -1 else v in
Some (Zupd maxSymbolValue v' nc0)
end.
Definition weight (c : Z) : Z := if c =? -1 then 1 else c.
Fixpoint wsum (l : list Z) : Z :=
match l with [] => 0 | c :: t => weight c + wsum t end.
Definition valid_ncount (nc : list Z) (maxSymbolValue tableLog : Z) : Prop :=
length nc = 256%nat /\
0 <= maxSymbolValue <= 255 /\
FSE_MIN_TABLELOG <= tableLog <= FSE_MAX_TABLELOG /\
(forall i, 0 <= i <= maxSymbolValue -> -1 <= Znth i nc) /\
Znth maxSymbolValue nc <> 0 /\
(forall i, maxSymbolValue < i -> Znth i nc = 0) /\
wsum (firstn (Z.to_nat (maxSymbolValue + 1)) nc) = 2^tableLog.
