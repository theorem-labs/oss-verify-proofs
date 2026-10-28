(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1cc X1bk X1bj X1cf X1bu.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fc.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ii X1io.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1j8 X1j6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1rl X1nw X1qz X1r0 X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c4.
Local Ltac plia_gen stock ::= plia_size stock.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section PS.
Context {RCEIL : RunCeiling}.

Variables (A G D lo : Z) (bytes : list byte) (sy : sync_st bptr) (j0 j1 j2 j3 : list byte).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
Local Notation ogc := [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3].
Local Notation W := [(bv_unsigned sp - 128, bv_unsigned sp); (A, A + 32); (G, G + 32); (D, D + Z.of_nat (length bytes))].
Local Notation len := (Z.of_nat (length bytes)).
Hypothesis FOK : sync_fields_ok sy.
Hypothesis INV : sync_inv2 sy.
Hypothesis PRE : buf_pre (sy_buf sy) bytes.
Hypothesis LENB : len = sy_storage sy.
Hypothesis HD : 0 <= D. Hypothesis TOPD : D + len < 2^63.
Hypothesis HA : 0 < A. Hypothesis HG : 0 < G.
Hypothesis LO : lo + 128 <= bv_unsigned sp.

Hypothesis SEP_fA : A + 32 <= lo \/ bv_unsigned sp <= A.
Hypothesis SEP_fG : G + 32 <= lo \/ bv_unsigned sp <= G.
Hypothesis SEP_fD : D + len <= lo \/ bv_unsigned sp <= D.
Hypothesis SEP_AG : A + 32 <= G \/ G + 32 <= A.
Hypothesis SEP_AD : A + 32 <= D \/ D + len <= A.
Hypothesis SEP_GD : G + 32 <= D \/ D + len <= G.
#[local] Set Default Proof Using "FOK INV PRE LENB HD TOPD HA HG LO SEP_fA SEP_fG SEP_fD SEP_AG SEP_AD SEP_GD".

Notation POST := (pageseek_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A G D lo bytes ogc m0).

Notation FRAME m loc := (rw_cells rsegs m (bv_unsigned sp + -96) (loc ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).

Local Notation ps_deliver' := (X1j6.ps_deliver A G D lo bytes sy j0 j1 j2 j3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 FOK INV PRE LENB HD TOPD HA HG LO SEP_fA SEP_fG SEP_fD SEP_AG SEP_AD SEP_GD).
Local Notation ps_restore' := (X1j6.ps_restore A G D lo bytes sy j0 j1 j2 j3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 FOK INV PRE LENB HD TOPD HA HG LO SEP_fA SEP_fG SEP_fD SEP_AG SEP_AD SEP_GD).

Lemma ps_tail2 : forall m (j8 j4 : list byte) (hb bb crc c0 c1 c2 c3 : Z) r ogo (sy' : sync_st bptr)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
let ret := sy_returned sy in let fill := sy_fill sy in let buf := sy_buf sy in
let nseg := znth buf (ret + 26) in
let sy1 := mkSync (sy_data sy) buf (sy_storage sy) fill ret (sy_unsynced sy) hb bb in
let chk := Z.lor (Z.lor (Z.shiftl c3 24) (Z.shiftl c2 16)) (Z.lor (Z.shiftl c1 8) c0) in
hb = 27 + nseg -> ret + hb + bb <= fill -> bb = zsum (zslice (ret + 27) nseg buf) ->
c0 = bv_unsigned (nth (Z.to_nat (ret + 22)) bytes (Z_to_bv 8 0)) -> c1 = bv_unsigned (nth (Z.to_nat (ret + 23)) bytes (Z_to_bv 8 0)) ->
c2 = bv_unsigned (nth (Z.to_nat (ret + 24)) bytes (Z_to_bv 8 0)) -> c3 = bv_unsigned (nth (Z.to_nat (ret + 25)) bytes (Z_to_bv 8 0)) ->
ogg_page_checksum (zslice ret hb buf) (zslice (ret + hb) bb buf) = [crc mod 256; (crc / 2^8) mod 256; (crc / 2^16) mod 256; (crc / 2^24) mod 256] ->
rw_cells rsegs m (bv_unsigned sp + -96) [CB 8 j8] ->
rw_cells rsegs m (bv_unsigned sp + -88) [C8 (Z_to_bv 64 (D + ret)); C4 (Z_to_bv 64 hb); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (D + ret + hb)); C4 (Z_to_bv 64 bb); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs m (bv_unsigned sp + -56) [CB 4 j4; C4 (Z_to_bv 64 chk); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
rw_cells rsegs m A (sync_cells D sy1) ->
u8arr rsegs m D (upd_bytes (upd_bytes bytes (Z.to_nat (ret + 22)) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) (Z.to_nat (ret + 22))
[Z_to_bv 8 (crc mod 256); Z_to_bv 8 ((crc / 2^8) mod 256); Z_to_bv 8 ((crc / 2^16) mod 256); Z_to_bv 8 ((crc / 2^24) mod 256)]) ->
rw_cells rsegs m G ogc ->
(if negb (list_eqb (zslice (ret + 22) 4 buf) (ogg_page_checksum (zslice ret hb buf) (zslice (ret + hb) bb buf)))
then sync_fail sy1 ret (fill - ret)
else ((hb + bb, Some (mkPage ret hb bb)), mkSync (sy_data sy) buf (sy_storage sy) fill (ret + (hb + bb)) 0 0 0))
= ((r, ogo), sy') ->
evt rsegs (POST r ogo sy')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (D + sy_returned sy)) (Z_to_bv 64 (sy_fill sy - sy_returned sy)) (Z_to_bv 64 chk)
s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x30694) fc None m (seg_rom rsegs)).
Proof.
intros until x31. intros ret fill buf nseg sy1 chk Hhb Hfit Hbb E0 E1 E2 E3 ECK FR0 PG FR ST MU WM MI SY ARR OG RES.
unfold sy1 in *. clear sy1.
pose proof FOK as sfP_; first [ sf_destruct 6%nat sfP_ as Fs Ff Fr Fu Fh Fbb | sf_fb; destruct sfP_ as (Fs & Ff & Fr & Fu & Fh & Fbb) ]. unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb.
pose proof PRE as [PRE1 PRE2]. pose proof INV as [[I1 [I2 [I3 [I4 Ibok]]]] _]. unfold zlength in I2.
fold ret fill buf in Fr, Ff, I1, I2, PRE1, PRE2, Ibok.
pose proof (znth_bytes_ok buf (ret + 26) Ibok) as Rnseg. fold nseg in Rnseg.
assert (Hbbr : 0 <= bb <= 255 * nseg).
{ pose proof (zsum_bytes_le _ (bytes_ok_zslice (ret + 27) nseg _ Ibok)) as Z1.
rewrite zlength_zslice in Z1 by (unfold zlength; lia). lia. }
pose proof (byte_range (nth (Z.to_nat (ret + 22)) bytes (Z_to_bv 8 0))) as Hc0. rewrite <- E0 in Hc0.
pose proof (byte_range (nth (Z.to_nat (ret + 23)) bytes (Z_to_bv 8 0))) as Hc1. rewrite <- E1 in Hc1.
pose proof (byte_range (nth (Z.to_nat (ret + 24)) bytes (Z_to_bv 8 0))) as Hc2. rewrite <- E2 in Hc2.
pose proof (byte_range (nth (Z.to_nat (ret + 25)) bytes (Z_to_bv 8 0))) as Hc3. rewrite <- E3 in Hc3.
assert (Q0 : 0 <= crc mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (Q1 : 0 <= (crc / 2^8) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (Q2 : 0 <= (crc / 2^16) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (Q3 : 0 <= (crc / 2^24) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
set (q0 := crc mod 256) in *. set (q1 := (crc / 2^8) mod 256) in *. set (q2 := (crc / 2^16) mod 256) in *. set (q3 := (crc / 2^24) mod 256) in *.
clearbody q0 q1 q2 q3.
pose proof (rw_cells_bound _ _ _ _ SY) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB. rewrite !upd_bytes_length in DB by (rewrite ?upd_bytes_length; cbn [length]; lia).
pose proof (rw_cells_bound _ _ _ _ FR0) as FB. cbn [cells_size csize Nat.add app length] in FB.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (bytes_at_read1 rsegs mx D _ (ret + 22) _ (proj1 ARR) ltac:(lia) ltac:(rewrite !upd_bytes_length; cbn [length]; rewrite ?upd_bytes_length; cbn [length]; lia) eq_refl) as R22;
pose proof (bytes_at_read1 rsegs mx D _ (ret + 23) _ (proj1 ARR) ltac:(lia) ltac:(rewrite !upd_bytes_length; cbn [length]; rewrite ?upd_bytes_length; cbn [length]; lia) eq_refl) as R23;
pose proof (bytes_at_read1 rsegs mx D _ (ret + 24) _ (proj1 ARR) ltac:(lia) ltac:(rewrite !upd_bytes_length; cbn [length]; rewrite ?upd_bytes_length; cbn [length]; lia) eq_refl) as R24;
pose proof (bytes_at_read1 rsegs mx D _ (ret + 25) _ (proj1 ARR) ltac:(lia) ltac:(rewrite !upd_bytes_length; cbn [length]; rewrite ?upd_bytes_length; cbn [length]; lia) eq_refl) as R25 end.
rewrite nth_upd_bytes_in in R22, R23, R24, R25 by (cbn [length]; rewrite ?upd_bytes_length; cbn [length]; lia).
replace (Z.to_nat (ret + 22) - Z.to_nat (ret + 22))%nat with 0%nat in R22 by lia.
replace (Z.to_nat (ret + 23) - Z.to_nat (ret + 22))%nat with 1%nat in R23 by lia.
replace (Z.to_nat (ret + 24) - Z.to_nat (ret + 22))%nat with 2%nat in R24 by lia.
replace (Z.to_nat (ret + 25) - Z.to_nat (ret + 22))%nat with 3%nat in R25 by lia.
cbn [nth] in R22, R23, R24, R25.
unfold chk. unfold sync_cells, wz in SY. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes] in SY.

zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.

assert (ECS : zslice (ret + 22) 4 buf = [c0; c1; c2; c3]).
{ rewrite (pre_zslice4 buf bytes (ret + 22) PRE) by lia. subst c0 c1 c2 c3.
replace (ret + 22 + 1) with (ret + 23) by lia. replace (ret + 22 + 2) with (ret + 24) by lia. replace (ret + 22 + 3) with (ret + 25) by lia. reflexivity. }
rewrite ECS, ECK in RES.

zstep. if_cases K.
-
apply bv_eqb_eq in K. apply (proj1 (chk_compare c0 c1 c2 c3 q0 q1 q2 q3 Hc0 Hc1 Hc2 Hc3 Q0 Q1 Q2 Q3)) in K.
rewrite <- K in RES. rewrite (proj2 (list_eqb_eq _ _) eq_refl) in RES. cbn [negb] in RES. injection RES as <- <- <-.
injection K as <- <- <- <-.

match type of ARR with u8arr _ ?mx _ ?l => assert (EL : l = bytes) end.
{ rewrite !upd_bytes_twice by (cbn [length]; rewrite ?upd_bytes_length; cbn [length]; lia).
subst c0 c1 c2 c3. rewrite !Z_to_bv8_unsigned.
transitivity (upd_bytes bytes (Z.to_nat (ret + 22)) (firstn 4 (skipn (Z.to_nat (ret + 22)) bytes))); [| apply upd_bytes_self; lia].
f_equal. rewrite (skipn_nth_cons bytes (Z.to_nat (ret + 22)) (Z_to_bv 8 0)) by lia.
rewrite (skipn_nth_cons bytes (S (Z.to_nat (ret + 22))) (Z_to_bv 8 0)) by lia.
rewrite (skipn_nth_cons bytes (S (S (Z.to_nat (ret + 22)))) (Z_to_bv 8 0)) by lia.
rewrite (skipn_nth_cons bytes (S (S (S (Z.to_nat (ret + 22))))) (Z_to_bv 8 0)) by lia.
cbn [firstn]. repeat f_equal; lia. }
rewrite EL in ARR. clear EL.
eapply (ps_deliver' _ j8 j4 hb bb); try eassumption; try lia.
-
assert (NE : [c0; c1; c2; c3] <> [q0; q1; q2; q3]).
{ intros E. apply (proj2 (chk_compare c0 c1 c2 c3 q0 q1 q2 q3 Hc0 Hc1 Hc2 Hc3 Q0 Q1 Q2 Q3)) in E.
apply (proj2 (bv_eqb_eq _ _)) in E. unfold chkword in E. rewrite E in K. discriminate K. }
destruct (list_eqb [c0; c1; c2; c3] [q0; q1; q2; q3]) eqn:LE; [apply list_eqb_eq in LE; contradiction|]. cbn [negb] in RES.
assert (ogo = None) as ->.
{ unfold sync_fail in RES. destruct (X1qz.find_byte _ _ _); congruence. }
eapply (ps_restore' _ j8 j4 hb bb c0 c1 c2 c3); try eassumption; try lia.
all: try (rewrite !upd_bytes_length by (rewrite ?upd_bytes_length; cbn [length]; lia); reflexivity).
rewrite !upd_bytes_twice by (cbn [length]; rewrite ?upd_bytes_length; cbn [length]; lia).
subst c0 c1 c2 c3. rewrite !Z_to_bv8_unsigned.
transitivity (upd_bytes bytes (Z.to_nat (ret + 22)) (firstn 4 (skipn (Z.to_nat (ret + 22)) bytes))); [| apply upd_bytes_self; lia].
f_equal. rewrite (skipn_nth_cons bytes (Z.to_nat (ret + 22)) (Z_to_bv 8 0)) by lia.
rewrite (skipn_nth_cons bytes (S (Z.to_nat (ret + 22))) (Z_to_bv 8 0)) by lia.
rewrite (skipn_nth_cons bytes (S (S (Z.to_nat (ret + 22)))) (Z_to_bv 8 0)) by lia.
rewrite (skipn_nth_cons bytes (S (S (S (Z.to_nat (ret + 22))))) (Z_to_bv 8 0)) by lia.
cbn [firstn]. repeat f_equal; lia.
Qed.

End PS.
