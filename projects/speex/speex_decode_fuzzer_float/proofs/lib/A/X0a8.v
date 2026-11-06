(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1dh X1ch X1cg X1dk X1cr X1cs X1dg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1sa.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nw X1qz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X05p X09u X0ae X09j X09r X0ab X0a9 X0aa.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1cu.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X110 X106 X10e X10x X10v X10w.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10e OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10w.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cu.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments skipn {A} n l : simpl nomatch.
#[local] Arguments firstn {A} n l : simpl nomatch.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section PS.

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

Notation POST := (pageseek_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A G D lo bytes ogc sy m0).

Notation FRAME m loc := (rw_cells bsegs m (bv_unsigned sp + -96) (loc ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).

Local Notation ps_ret0' := (X10v.ps_ret0 A G D lo bytes sy j0 j1 j2 j3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 FOK INV PRE LENB HD TOPD HA HG LO SEP_fA SEP_fG SEP_fD SEP_AG SEP_AD SEP_GD).
Local Notation ps_sync_fail' := (X10v.ps_sync_fail A G D lo bytes sy j0 j1 j2 j3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 FOK INV PRE LENB HD TOPD HA HG LO SEP_fA SEP_fG SEP_fD SEP_AG SEP_AD SEP_GD).

Local Notation ps_tail2' := (X10w.ps_tail2 A G D lo bytes sy j0 j1 j2 j3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 FOK INV PRE LENB HD TOPD HA HG LO SEP_fA SEP_fG SEP_fD SEP_AG SEP_AD SEP_GD).

Definition hloop_post (x1 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (nseg bb0 : Z) (sy1 : sync_st bptr) (m : mem)
: machine_state -> Prop :=
fun ms' => exists (x14 : word) m',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G)
(Z_to_bv 64 (nseg + 27)) (Z_to_bv 64 nseg)
(Z_to_bv 64 (bb0 + zsum (zslice (sy_returned sy1 + 27) nseg (sy_buf sy))))
(Z_to_bv 64 (D + sy_returned sy1 + 27 + nseg)) x14 x15 x16 x17
(Z_to_bv 64 (D + sy_returned sy1)) (Z_to_bv 64 (sy_fill sy1 - sy_returned sy1)) (Z_to_bv 64 D)
s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xc19d0) fc None m' (seg_rom bsegs)
/\ munch [(A, A + 32)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' A (sync_cells D (mkSync (sy_data sy1) (sy_buf sy1) (sy_storage sy1) (sy_fill sy1) (sy_returned sy1)
(sy_unsynced sy1) (sy_headerbytes sy1)
(bb0 + zsum (zslice (sy_returned sy1 + 27) nseg (sy_buf sy))))).

Lemma ps_hloop : forall (k : nat) (i : Z) m (sy1 : sync_st bptr) (nseg bb0 acc a3v : Z) (x1 x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 : word),
Z.to_nat (nseg - i) = k -> 0 <= i < nseg -> a3v = D + sy_returned sy1 + 27 + i ->
nseg = znth (sy_buf sy) (sy_returned sy1 + 26) -> sy_returned sy1 + 27 + nseg <= sy_fill sy1 ->
sy_fill sy1 <= zlength (sy_buf sy) -> 0 <= bb0 < 2^24 ->
acc = bb0 + zsum (zslice (sy_returned sy1 + 27) i (sy_buf sy)) ->
sync_fields_ok sy1 ->
rw_cells bsegs m A (sync_cells D (mkSync (sy_data sy1) (sy_buf sy1) (sy_storage sy1) (sy_fill sy1) (sy_returned sy1)
(sy_unsynced sy1) (sy_headerbytes sy1) acc)) ->
u8arr bsegs m D bytes -> mem_inv bsegs m ->
evt bsegs (hloop_post x1 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 nseg bb0 sy1 m)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G)
(Z_to_bv 64 (nseg + 27)) (Z_to_bv 64 i) (Z_to_bv 64 acc) (Z_to_bv 64 a3v) x14 x15 x16 x17
(Z_to_bv 64 (D + sy_returned sy1)) (Z_to_bv 64 (sy_fill sy1 - sy_returned sy1)) (Z_to_bv 64 D)
s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xc19b4) fc None m (seg_rom bsegs)).
Proof.
induction k as [|k IH]; intros i m sy1 nseg bb0 acc a3v x1 x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 Hk Hi -> Hnseg Hfit Hfill Hbb0 Hacc FOK1 SY ARR MI; [lia|].
pose proof FOK1 as sfP_; first [ sf_destruct 6%nat sfP_ as Fs Ff Fr Fu Fh Fbb | sf_fb; destruct sfP_ as (Fs & Ff & Fr & Fu & Fh & Fbb) ]. unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb.
pose proof PRE as [PRE1 PRE2]. unfold zlength in Hfill.
set (ret := sy_returned sy1) in *. set (fill := sy_fill sy1) in *.
pose proof (rw_cells_bound _ _ _ _ SY) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof (munch_refl [(A, A + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
unfold sync_cells, wz in SY. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes] in SY.
pose proof INV as [[I1 [I2 [I3 [I4 Ibok]]]] _].
pose proof (znth_bytes_ok (sy_buf sy) (ret + 26) Ibok) as Rnseg. rewrite <- Hnseg in Rnseg.
assert (Hz : forall i', 0 <= i' <= nseg -> 0 <= zsum (zslice (ret + 27) i' (sy_buf sy)) <= 255 * i').
{ intros i' Hi'. pose proof (zsum_bytes_le _ (bytes_ok_zslice (ret + 27) i' _ Ibok)) as Z1.
rewrite zlength_zslice in Z1 by (unfold zlength; lia). exact Z1. }
pose proof (Hz i ltac:(lia)) as Hzi. pose proof (Hz (i + 1) ltac:(lia)) as Hzi1.
pose proof (bytes_at_read1 bsegs m D bytes (ret + 27 + i) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as Rb.
pose proof (byte_range (nth (Z.to_nat (ret + 27 + i)) bytes (Z_to_bv 8 0))) as Hb.
set (b := bv_unsigned (nth (Z.to_nat (ret + 27 + i)) bytes (Z_to_bv 8 0))) in Hb.
assert (Eacc : acc + b = bb0 + zsum (zslice (ret + 27) (i + 1) (sy_buf sy))).
{ rewrite zslice_snoc by (unfold zlength; lia). rewrite zsum_app. cbn [zsum].
rewrite (pre_znth (sy_buf sy) bytes (ret + 27 + i) PRE) by lia. subst b acc. lia. }
ostep. unfold zxb. cbv beta. fold b. ostep. ostep.

match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (bytes_at_read1 bsegs mx D bytes (ret + 26) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as Rn end.
ostep. unfold zxb. cbv beta. fold b.
rewrite <- (pre_znth (sy_buf sy) bytes (ret + 26) PRE) by lia. rewrite <- Hnseg.
ostep. ostep. ostep.
if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
-
rewrite Eacc.
eapply evt_mono.
{ eapply (IH (i + 1)); try eassumption; try lia; [reflexivity|].
unfold sync_cells, wz. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes].
rewrite <- Eacc. exact SY. }
cbv beta. intros ms' P. first [ sf_destruct 7%nat P as x14' m' -> MU' WM' MI' SY' | sf_fb; destruct P as (x14' & m' & -> & MU' & WM' & MI' & SY') ].
exists x14', m'. split; [reflexivity|]. split; [eapply munch_trans; [exact MU| exact MU']|].
split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'| exact SY'].
-
rewrite Eacc. replace (i + 1) with nseg by lia. replace (D + ret + 27 + i + 1) with (D + ret + 27 + nseg) by lia.
finish.
unfold sync_cells, wz. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes].
fold ret. replace nseg with (i + 1) by lia. rewrite <- Eacc. exact SY.
Qed.

Lemma ps_tail : forall m (junk : list byte) (hb bb : Z) (sy1 : sync_st bptr) r ogo (sy' : sync_st bptr)
(x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
let ret := sy_returned sy in let fill := sy_fill sy in let buf := sy_buf sy in
let nseg := znth buf (ret + 26) in
sy_data sy1 = sy_data sy -> sy_buf sy1 = buf -> sy_storage sy1 = sy_storage sy -> sy_fill sy1 = fill ->
sy_returned sy1 = ret -> sy_unsynced sy1 = sy_unsynced sy -> sy_headerbytes sy1 = hb -> sy_bodybytes sy1 = bb ->
hb = 27 + nseg -> ret + hb <= fill -> bb = zsum (zslice (ret + 27) nseg buf) ->
FRAME m [CB 48 junk] -> stk bsegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
rw_cells bsegs m A (sync_cells D sy1) -> u8arr bsegs m D bytes -> rw_cells bsegs m G ogc ->
(if fill - ret <? bb + hb then ((0, None), sy1)
else if negb (list_eqb (zslice (ret + 22) 4 buf) (ogg_page_checksum (zslice ret hb buf) (zslice (ret + hb) bb buf)))
then sync_fail sy1 ret (fill - ret)
else ((hb + bb, Some (mkPage ret hb bb)), mkSync (sy_data sy) buf (sy_storage sy) fill (ret + (hb + bb)) 0 0 0))
= ((r, ogo), sy') ->
evt bsegs (POST r ogo sy')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G)
(Z_to_bv 64 hb) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (D + sy_returned sy)) (Z_to_bv 64 (sy_fill sy - sy_returned sy)) (Z_to_bv 64 D)
s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xc180c) fc None m (seg_rom bsegs)).
Proof.
intros until x31. intros ret fill buf nseg Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Hhb Hfit Hbb FR ST MU WM MI SY ARR OG RES.
destruct sy1 as [d1 b1 st1 f1 r1 u1 h1 bb1]. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes] in *.
subst d1 b1 st1 f1 r1 u1 h1 bb1.
pose proof FOK as sfP_; first [ sf_destruct 6%nat sfP_ as Fs Ff Fr Fu Fh Fbb | sf_fb; destruct sfP_ as (Fs & Ff & Fr & Fu & Fh & Fbb) ]. unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb.
pose proof PRE as [PRE1 PRE2]. pose proof INV as [[I1 [I2 [I3 [I4 Ibok]]]] _]. unfold zlength in I2.
fold ret fill buf in Fr, Ff, I1, I2, PRE1, PRE2, Ibok.
pose proof (znth_bytes_ok buf (ret + 26) Ibok) as Rnseg. fold nseg in Rnseg.
assert (Hbbr : 0 <= bb <= 255 * nseg).
{ pose proof (zsum_bytes_le _ (bytes_ok_zslice (ret + 27) nseg _ Ibok)) as Z1.
rewrite zlength_zslice in Z1 by (unfold zlength; lia). lia. }
pose proof (rw_cells_bound _ _ _ _ SY) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add app length] in FB.
unfold sync_cells, wz in SY. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes] in SY.
ostep. rewrite sx32_lit by (unfold int31; lia). ostep. rewrite swrap32_small by lia.
ostep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
-
destruct (Z.ltb_spec (fill - ret) (bb + hb)); [|exfalso; lia]. injection RES as <- <- <-.
eapply (ps_ret0' _ [CB 48 junk]); try eassumption; [reflexivity|].
unfold sync_fields_ok, int31; cbn; lia.
- destruct (Z.ltb_spec (fill - ret) (bb + hb)); [exfalso; lia|].

pose proof (bytes_at_read1 bsegs m D bytes (ret + 22) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as R22.
pose proof (bytes_at_read1 bsegs m D bytes (ret + 23) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as R23.
pose proof (bytes_at_read1 bsegs m D bytes (ret + 24) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as R24.
pose proof (bytes_at_read1 bsegs m D bytes (ret + 25) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as R25.
pose proof (byte_range (nth (Z.to_nat (ret + 22)) bytes (Z_to_bv 8 0))) as Hc0. set (c0 := bv_unsigned (nth (Z.to_nat (ret + 22)) bytes (Z_to_bv 8 0))) in Hc0.
pose proof (byte_range (nth (Z.to_nat (ret + 23)) bytes (Z_to_bv 8 0))) as Hc1. set (c1 := bv_unsigned (nth (Z.to_nat (ret + 23)) bytes (Z_to_bv 8 0))) in Hc1.
pose proof (byte_range (nth (Z.to_nat (ret + 24)) bytes (Z_to_bv 8 0))) as Hc2. set (c2 := bv_unsigned (nth (Z.to_nat (ret + 24)) bytes (Z_to_bv 8 0))) in Hc2.
pose proof (byte_range (nth (Z.to_nat (ret + 25)) bytes (Z_to_bv 8 0))) as Hc3. set (c3 := bv_unsigned (nth (Z.to_nat (ret + 25)) bytes (Z_to_bv 8 0))) in Hc3.
ostep. ostep. ostep. ostep. unfold zxb. cbv beta. fold c0 c1 c2 c3.
pose proof (u8arr_store_ok bsegs _ _ _ (ret + 22) (wa (D + ret + 22)) ARR ltac:(rewrite ?upd_length; lia) ltac:(f_equal; lia)) as SOK.
ostep. arr_store ARR (ret + 22) (Z_to_bv 8 0).
pose proof (u8arr_store_ok bsegs _ _ _ (ret + 23) (wa (D + ret + 23)) ARR ltac:(rewrite ?upd_length; lia) ltac:(f_equal; lia)) as SOK.
ostep. arr_store ARR (ret + 23) (Z_to_bv 8 0).
pose proof (u8arr_store_ok bsegs _ _ _ (ret + 24) (wa (D + ret + 24)) ARR ltac:(rewrite ?upd_length; lia) ltac:(f_equal; lia)) as SOK.
ostep. arr_store ARR (ret + 24) (Z_to_bv 8 0).
pose proof (u8arr_store_ok bsegs _ _ _ (ret + 25) (wa (D + ret + 25)) ARR ltac:(rewrite ?upd_length; lia) ltac:(f_equal; lia)) as SOK.
ostep. arr_store ARR (ret + 25) (Z_to_bv 8 0).

ostep. ostep. ostep. ostep. ostep. rewrite sx32_lit by (unfold int31; lia). ostep. ostep. rewrite sx32_lit by (unfold int31; lia).
ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep.

chunk_uncons FR as FR0.
match type of FR with rw_cells _ _ ?X (?ca :: ?cb :: ?cc :: ?cd :: ?rest) =>
change (ca :: cb :: cc :: cd :: rest) with ([ca; cb; cc; cd] ++ rest) in FR end.
apply rw_cells_app in FR. destruct FR as [PG FR]. cbn [cells_size csize Nat.add] in FR.
replace (bv_unsigned sp + -96 + 8 + Z.of_nat 32) with (bv_unsigned sp + -56) in FR by lia.
replace (bv_unsigned sp + -96 + 8) with (bv_unsigned sp + -88) in PG by lia.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (PG2 : rw_cells bsegs mx (bv_unsigned sp + -88) (cks_page_cells (D + ret) hb (Z_to_bv 64 0) (D + ret + hb) bb (Z_to_bv 64 0))) end.
{ eapply rw_cells_recell; [exact PG| cbn; repeat split; reflexivity| | reflexivity].
unfold cks_page_cells, wz. cbn [cells_bytes cbytes app]. rewrite (le8_split_u32 hb), (le8_split_u32 bb) by lia.
rewrite <- !app_assoc. reflexivity. }
clear PG. unfold cks_page_cells, wz in PG2.
match type of ARR with u8arr _ _ _ ?b4 => set (bytes4 := b4) in ARR end.
assert (L4 : length bytes4 = length bytes) by (unfold bytes4; rewrite !upd_length; reflexivity).
call_sp (ogg_page_checksum_set_spec D ret hb bb bytes4 (bv_unsigned sp + -88) lo (Z_to_bv 64 0) (Z_to_bv 64 0)).
1:{ exact PG2. } 1:{ exact ARR. } 1:{ exact ST. } 1:{ exact MI. }
1-10: try lia. 1:{ reflexivity. }
rename POST into ARR. rename PC into ST.
assert (E4 : bytes4 = upd_bytes bytes (Z.to_nat (ret + 22)) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]).
{ subst bytes4. apply upd4_upd_bytes; lia. }
clearbody bytes4. subst bytes4.
pose proof (checksum_model buf bytes ret hb bb PRE ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as ECK.
unfold ogg_page_checksum in ARR. unfold ogg_page_checksum at 2 in ECK. cbv zeta in ARR, ECK. cbn [map] in ARR.
match type of ARR with context [Z_to_bv _ (?c mod 256)] => set (crc := c) in ARR, ECK end.
clearbody crc.
eapply (ps_tail2' _ (firstn 8 (firstn 44 junk)) (skipn 8 (skipn 8 (skipn 8 (skipn 16 (firstn 44 junk))))) hb bb crc c0 c1 c2 c3);
try eassumption; try reflexivity; try lia.
Qed.

Lemma ps_hdr : forall m (junk : list byte) r ogo (sy' : sync_st bptr)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
sy_headerbytes sy = 0 ->
FRAME m [CB 48 junk] -> stk bsegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
rw_cells bsegs m A (sync_cells D sy) -> u8arr bsegs m D bytes -> rw_cells bsegs m G ogc ->
ogg_sync_pageseek sy = ((r, ogo), sy') ->
evt bsegs (POST r ogo sy')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (D + sy_returned sy)) (Z_to_bv 64 (sy_fill sy - sy_returned sy)) (Z_to_bv 64 D)
s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xc18cc) fc None m (seg_rom bsegs)).
Proof.
intros until x31. intros Hhb0 FR ST MU WM MI SY ARR OG RES.
pose proof FOK as sfP_; first [ sf_destruct 6%nat sfP_ as Fs Ff Fr Fu Fh Fbb | sf_fb; destruct sfP_ as (Fs & Ff & Fr & Fu & Fh & Fbb) ]. unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb.
pose proof PRE as [PRE1 PRE2]. pose proof INV as [[I1 [I2 [I3 [I4 Ibok]]]] [SH1 SH2]]. unfold zlength in I2.
specialize (SH1 Hhb0).
set (ret := sy_returned sy) in *. set (fill := sy_fill sy) in *. set (buf := sy_buf sy) in *.
pose proof (znth_bytes_ok buf (ret + 26) Ibok) as Rnseg. set (nseg := znth buf (ret + 26)) in *.
pose proof (rw_cells_bound _ _ _ _ SY) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add app length] in FB.
unfold sync_cells, wz in SY.

unfold ogg_sync_pageseek, ogg_sync_check in RES. fold ret fill buf in RES.
destruct (Z.ltb_spec (sy_storage sy) 0); [lia|]. rewrite Hhb0, Z.eqb_refl in RES.

ostep. ostep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
-
destruct (Z.ltb_spec (fill - ret) 27); [exfalso; lia|].
pose proof (bytes_at_read1 bsegs m D bytes ret _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as R0.
pose proof (bytes_at_read1 bsegs m D bytes (ret + 1) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as R1.
pose proof (bytes_at_read1 bsegs m D bytes (ret + 2) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as R2.
pose proof (bytes_at_read1 bsegs m D bytes (ret + 3) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as R3.

ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep.
pose proof (pre_zslice4 buf bytes ret PRE ltac:(lia) ltac:(lia)) as ECS.
ostep. if_cases K2.
+
apply (proj1 (oggs_compare _ _ _ _)) in K2. rewrite <- ECS in K2. rewrite K2 in RES.
rewrite (proj2 (list_eqb_eq _ _) eq_refl) in RES. cbn [negb] in RES. fold nseg in RES.

pose proof (bytes_at_read1 bsegs m D bytes (ret + 26) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as R26.
ostep. unfold zxb. cbv beta. rewrite <- (pre_znth buf bytes (ret + 26) PRE) by lia. fold nseg.
ostep. ostep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
*
destruct (Z.ltb_spec (fill - ret) (nseg + 27)); [|exfalso; lia]. injection RES as <- <- <-.
eapply (ps_ret0' _ [CB 48 junk] sy); try eassumption. reflexivity.
* destruct (Z.ltb_spec (fill - ret) (nseg + 27)); [exfalso; lia|].

ostep. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
--
ostep. ostep.
rewrite K4 in *. rewrite zslice_0 in RES. cbn [zsum] in RES. rewrite Z.add_0_r in RES.
eapply (ps_tail _ junk (0 + 27) (sy_bodybytes sy) (mkSync (sy_data sy) buf (sy_storage sy) fill ret (sy_unsynced sy) (0 + 27) (sy_bodybytes sy)));
fold ret fill buf; fold nseg; rewrite ?K4; try eassumption; try reflexivity; try lia.
--
ostep. ostep. rewrite sx32_lit by (unfold int31; lia). ostep.
call (ps_hloop (Z.to_nat nseg) 0 _ sy nseg (sy_bodybytes sy) (sy_bodybytes sy) (D + ret + 27)).
all: fold ret fill buf; fold nseg; try lia.
1:{ unfold zlength. lia. } 1:{ rewrite zslice_0. cbn. lia. } 1:{ exact FOK. }
1:{ unfold sync_cells, wz. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes]. fold ret fill. exact SY. }
1:{ exact ARR. } 1:{ exact MI. }
rename POST into SY2. unfold sync_cells, wz in SY2. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes] in SY2.
fold ret fill buf in SY2. fold ret fill.

ostep. ostep.
eapply (ps_tail _ junk (nseg + 27) (sy_bodybytes sy + zsum (zslice (ret + 27) nseg buf))
(mkSync (sy_data sy) buf (sy_storage sy) fill ret (sy_unsynced sy) (nseg + 27) (sy_bodybytes sy + zsum (zslice (ret + 27) nseg buf))));
fold ret fill buf; fold nseg; try eassumption; try reflexivity; try lia.
+
assert (NE : zslice ret 4 buf <> OGGS_MAGIC).
{ intros E. rewrite ECS in E. apply (proj2 (oggs_compare _ _ _ _)) in E. rewrite E in K2. discriminate K2. }
destruct (list_eqb (zslice ret 4 buf) OGGS_MAGIC) eqn:LE; [apply list_eqb_eq in LE; contradiction|]. cbn [negb] in RES.
assert (ogo = None) as ->.
{ unfold sync_fail in RES. destruct (X1qz.find_byte _ _ _); congruence. }
eapply (ps_sync_fail' _ [CB 48 junk] sy); try eassumption; try reflexivity; cbn; try lia.
-
destruct (Z.ltb_spec (fill - ret) 27); [|exfalso; lia]. injection RES as <- <- <-.
eapply (ps_ret0' _ [CB 48 junk] sy); try eassumption; try reflexivity.
Qed.

Lemma ps_body : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) r ogo (sy' : sync_st bptr),
stk bsegs m0 lo (bv_unsigned sp) -> mem_inv bsegs m0 ->
rw_cells bsegs m0 A (sync_cells D sy) -> u8arr bsegs m0 D bytes -> rw_cells bsegs m0 G ogc ->
ogg_sync_pageseek sy = ((r, ogo), sy') ->
evt bsegs (POST r ogo sy')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_pageseek) fc None m0 (seg_rom bsegs)).
Proof.
intros until sy'. intros ST MI SY ARR OG RES. unfold A_ogg_sync_pageseek.
pose proof FOK as sfP_; first [ sf_destruct 6%nat sfP_ as Fs Ff Fr Fu Fh Fbb | sf_fb; destruct sfP_ as (Fs & Ff & Fr & Fu & Fh & Fbb) ]. unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb.
pose proof INV as [[I1 [I2 [I3 [I4 Ibok]]]] [SH1 SH2]]. unfold zlength in I2.
pose proof (rw_cells_bound _ _ _ _ SY) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof (rw_cells_bound _ _ _ _ OG) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl W m0) as MU. pose proof (wmono_refl bsegs m0) as WM.
unfold sync_cells, wz in SY.
carve_frame 96%nat ST.

ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep.
ostep. rewrite sx32_lit by (unfold int31; lia).
ostep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia; [exfalso; lia|].

ostep. ostep. ostep. rewrite sx32_lit by (unfold int31; lia). ostep. rewrite sx32_lit by (unfold int31; lia).
ostep. rewrite sx32_lit by (unfold int31; lia). ostep. rewrite swrap32_small by lia. ostep.
ostep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
-
eapply ps_hdr; try eassumption.
-
destruct (SH2 K2) as (Hhb & Hfit & Hbb).
eapply (ps_tail _ _ (sy_headerbytes sy) (sy_bodybytes sy) sy); try eassumption; try reflexivity; try lia.
unfold ogg_sync_pageseek, ogg_sync_check in RES.
destruct (Z.ltb_spec (sy_storage sy) 0); [lia|].
replace (sy_headerbytes sy =? 0) with false in RES by (symmetry; apply Z.eqb_neq; lia).
cbv beta iota zeta in RES. exact RES.
Qed.
End PS.

Lemma ogg_sync_pageseek_spec : forall (A G D lo : Z) (bytes : list byte) (sy : sync_st bptr) (j0 j1 j2 j3 : list byte)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) r ogo (sy' : sync_st bptr),
sync_fields_ok sy -> sync_inv2 sy -> buf_pre (sy_buf sy) bytes -> Z.of_nat (length bytes) = sy_storage sy ->
0 <= D -> D + Z.of_nat (length bytes) < 2^63 -> 0 < A -> 0 < G -> lo + 128 <= bv_unsigned sp ->
(A + 32 <= lo \/ bv_unsigned sp <= A) -> (G + 32 <= lo \/ bv_unsigned sp <= G) -> (D + Z.of_nat (length bytes) <= lo \/ bv_unsigned sp <= D) ->
(A + 32 <= G \/ G + 32 <= A) -> (A + 32 <= D \/ D + Z.of_nat (length bytes) <= A) -> (G + 32 <= D \/ D + Z.of_nat (length bytes) <= G) ->
stk bsegs m lo (bv_unsigned sp) -> mem_inv bsegs m ->
rw_cells bsegs m A (sync_cells D sy) -> u8arr bsegs m D bytes -> rw_cells bsegs m G [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3] ->
ogg_sync_pageseek sy = ((r, ogo), sy') ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 G ->
evt bsegs (pageseek_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A G D lo bytes [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3] sy m r ogo sy')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_pageseek) fc None m (seg_rom bsegs)).
Proof.
intros until sy'. intros FOK INV PRE LENB HD TOPD HA HG LO S1 S2 S3 S4 S5 S6 ST MI SY ARR OG RES -> ->.
eapply (ps_body A G D lo bytes sy j0 j1 j2 j3); eassumption.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments skipn {A} n l : simpl nomatch.
#[local] Arguments firstn {A} n l : simpl nomatch.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section PS.

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

Notation POST := (pageseek_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A G D lo bytes ogc sy m0).

Notation FRAME m loc := (rw_cells asegs m (bv_unsigned sp + -96) (loc ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).

Local Notation ps_ret0' := (X0a9.ps_ret0 A G D lo bytes sy j0 j1 j2 j3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 FOK INV PRE LENB HD TOPD HA HG LO SEP_fA SEP_fG SEP_fD SEP_AG SEP_AD SEP_GD).
Local Notation ps_sync_fail' := (X0a9.ps_sync_fail A G D lo bytes sy j0 j1 j2 j3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 FOK INV PRE LENB HD TOPD HA HG LO SEP_fA SEP_fG SEP_fD SEP_AG SEP_AD SEP_GD).

Local Notation ps_tail2' := (X0aa.ps_tail2 A G D lo bytes sy j0 j1 j2 j3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 FOK INV PRE LENB HD TOPD HA HG LO SEP_fA SEP_fG SEP_fD SEP_AG SEP_AD SEP_GD).

Definition hloop_post (x1 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (nseg bb0 : Z) (sy1 : sync_st bptr) (m : mem)
: machine_state -> Prop :=
fun ms' => exists (x14 : word) m',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G)
(Z_to_bv 64 (nseg + 27)) (Z_to_bv 64 nseg)
(Z_to_bv 64 (bb0 + zsum (zslice (sy_returned sy1 + 27) nseg (sy_buf sy))))
(Z_to_bv 64 (D + sy_returned sy1 + 27 + nseg)) x14 x15 x16 x17
(Z_to_bv 64 (D + sy_returned sy1)) (Z_to_bv 64 (sy_fill sy1 - sy_returned sy1)) (Z_to_bv 64 D)
s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xb92a0) fc None m' (seg_rom asegs)
/\ munch [(A, A + 32)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' A (sync_cells D (mkSync (sy_data sy1) (sy_buf sy1) (sy_storage sy1) (sy_fill sy1) (sy_returned sy1)
(sy_unsynced sy1) (sy_headerbytes sy1)
(bb0 + zsum (zslice (sy_returned sy1 + 27) nseg (sy_buf sy))))).

Lemma ps_hloop : forall (k : nat) (i : Z) m (sy1 : sync_st bptr) (nseg bb0 acc a3v : Z) (x1 x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 : word),
Z.to_nat (nseg - i) = k -> 0 <= i < nseg -> a3v = D + sy_returned sy1 + 27 + i ->
nseg = znth (sy_buf sy) (sy_returned sy1 + 26) -> sy_returned sy1 + 27 + nseg <= sy_fill sy1 ->
sy_fill sy1 <= zlength (sy_buf sy) -> 0 <= bb0 < 2^24 ->
acc = bb0 + zsum (zslice (sy_returned sy1 + 27) i (sy_buf sy)) ->
sync_fields_ok sy1 ->
rw_cells asegs m A (sync_cells D (mkSync (sy_data sy1) (sy_buf sy1) (sy_storage sy1) (sy_fill sy1) (sy_returned sy1)
(sy_unsynced sy1) (sy_headerbytes sy1) acc)) ->
u8arr asegs m D bytes -> mem_inv asegs m ->
evt asegs (hloop_post x1 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 nseg bb0 sy1 m)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G)
(Z_to_bv 64 (nseg + 27)) (Z_to_bv 64 i) (Z_to_bv 64 acc) (Z_to_bv 64 a3v) x14 x15 x16 x17
(Z_to_bv 64 (D + sy_returned sy1)) (Z_to_bv 64 (sy_fill sy1 - sy_returned sy1)) (Z_to_bv 64 D)
s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xb9284) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros i m sy1 nseg bb0 acc a3v x1 x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 Hk Hi -> Hnseg Hfit Hfill Hbb0 Hacc FOK1 SY ARR MI; [lia|].
pose proof FOK1 as sfP_; first [ sf_destruct 6%nat sfP_ as Fs Ff Fr Fu Fh Fbb | sf_fb; destruct sfP_ as (Fs & Ff & Fr & Fu & Fh & Fbb) ]. unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb.
pose proof PRE as [PRE1 PRE2]. unfold zlength in Hfill.
set (ret := sy_returned sy1) in *. set (fill := sy_fill sy1) in *.
pose proof (rw_cells_bound _ _ _ _ SY) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof (munch_refl [(A, A + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold sync_cells, wz in SY. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes] in SY.
pose proof INV as [[I1 [I2 [I3 [I4 Ibok]]]] _].
pose proof (znth_bytes_ok (sy_buf sy) (ret + 26) Ibok) as Rnseg. rewrite <- Hnseg in Rnseg.
assert (Hz : forall i', 0 <= i' <= nseg -> 0 <= zsum (zslice (ret + 27) i' (sy_buf sy)) <= 255 * i').
{ intros i' Hi'. pose proof (zsum_bytes_le _ (bytes_ok_zslice (ret + 27) i' _ Ibok)) as Z1.
rewrite zlength_zslice in Z1 by (unfold zlength; lia). exact Z1. }
pose proof (Hz i ltac:(lia)) as Hzi. pose proof (Hz (i + 1) ltac:(lia)) as Hzi1.
pose proof (bytes_at_read1 asegs m D bytes (ret + 27 + i) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as Rb.
pose proof (byte_range (nth (Z.to_nat (ret + 27 + i)) bytes (Z_to_bv 8 0))) as Hb.
set (b := bv_unsigned (nth (Z.to_nat (ret + 27 + i)) bytes (Z_to_bv 8 0))) in Hb.
assert (Eacc : acc + b = bb0 + zsum (zslice (ret + 27) (i + 1) (sy_buf sy))).
{ rewrite zslice_snoc by (unfold zlength; lia). rewrite zsum_app. cbn [zsum].
rewrite (pre_znth (sy_buf sy) bytes (ret + 27 + i) PRE) by lia. subst b acc. lia. }
ostep. unfold zxb. cbv beta. fold b. ostep. ostep.

match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (bytes_at_read1 asegs mx D bytes (ret + 26) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as Rn end.
ostep. unfold zxb. cbv beta. fold b.
rewrite <- (pre_znth (sy_buf sy) bytes (ret + 26) PRE) by lia. rewrite <- Hnseg.
ostep. ostep. ostep.
if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
-
rewrite Eacc.
eapply evt_mono.
{ eapply (IH (i + 1)); try eassumption; try lia; [reflexivity|].
unfold sync_cells, wz. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes].
rewrite <- Eacc. exact SY. }
cbv beta. intros ms' P. first [ sf_destruct 7%nat P as x14' m' -> MU' WM' MI' SY' | sf_fb; destruct P as (x14' & m' & -> & MU' & WM' & MI' & SY') ].
exists x14', m'. split; [reflexivity|]. split; [eapply munch_trans; [exact MU| exact MU']|].
split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'| exact SY'].
-
rewrite Eacc. replace (i + 1) with nseg by lia. replace (D + ret + 27 + i + 1) with (D + ret + 27 + nseg) by lia.
finish.
unfold sync_cells, wz. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes].
fold ret. replace nseg with (i + 1) by lia. rewrite <- Eacc. exact SY.
Qed.

Lemma ps_tail : forall m (junk : list byte) (hb bb : Z) (sy1 : sync_st bptr) r ogo (sy' : sync_st bptr)
(x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
let ret := sy_returned sy in let fill := sy_fill sy in let buf := sy_buf sy in
let nseg := znth buf (ret + 26) in
sy_data sy1 = sy_data sy -> sy_buf sy1 = buf -> sy_storage sy1 = sy_storage sy -> sy_fill sy1 = fill ->
sy_returned sy1 = ret -> sy_unsynced sy1 = sy_unsynced sy -> sy_headerbytes sy1 = hb -> sy_bodybytes sy1 = bb ->
hb = 27 + nseg -> ret + hb <= fill -> bb = zsum (zslice (ret + 27) nseg buf) ->
FRAME m [CB 48 junk] -> stk asegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
rw_cells asegs m A (sync_cells D sy1) -> u8arr asegs m D bytes -> rw_cells asegs m G ogc ->
(if fill - ret <? bb + hb then ((0, None), sy1)
else if negb (list_eqb (zslice (ret + 22) 4 buf) (ogg_page_checksum (zslice ret hb buf) (zslice (ret + hb) bb buf)))
then sync_fail sy1 ret (fill - ret)
else ((hb + bb, Some (mkPage ret hb bb)), mkSync (sy_data sy) buf (sy_storage sy) fill (ret + (hb + bb)) 0 0 0))
= ((r, ogo), sy') ->
evt asegs (POST r ogo sy')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G)
(Z_to_bv 64 hb) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (D + sy_returned sy)) (Z_to_bv 64 (sy_fill sy - sy_returned sy)) (Z_to_bv 64 D)
s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xb90dc) fc None m (seg_rom asegs)).
Proof.
intros until x31. intros ret fill buf nseg Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Hhb Hfit Hbb FR ST MU WM MI SY ARR OG RES.
destruct sy1 as [d1 b1 st1 f1 r1 u1 h1 bb1]. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes] in *.
subst d1 b1 st1 f1 r1 u1 h1 bb1.
pose proof FOK as sfP_; first [ sf_destruct 6%nat sfP_ as Fs Ff Fr Fu Fh Fbb | sf_fb; destruct sfP_ as (Fs & Ff & Fr & Fu & Fh & Fbb) ]. unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb.
pose proof PRE as [PRE1 PRE2]. pose proof INV as [[I1 [I2 [I3 [I4 Ibok]]]] _]. unfold zlength in I2.
fold ret fill buf in Fr, Ff, I1, I2, PRE1, PRE2, Ibok.
pose proof (znth_bytes_ok buf (ret + 26) Ibok) as Rnseg. fold nseg in Rnseg.
assert (Hbbr : 0 <= bb <= 255 * nseg).
{ pose proof (zsum_bytes_le _ (bytes_ok_zslice (ret + 27) nseg _ Ibok)) as Z1.
rewrite zlength_zslice in Z1 by (unfold zlength; lia). lia. }
pose proof (rw_cells_bound _ _ _ _ SY) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add app length] in FB.
unfold sync_cells, wz in SY. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes] in SY.
ostep. rewrite sx32_lit by (unfold int31; lia). ostep. rewrite swrap32_small by lia.
ostep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
-
destruct (Z.ltb_spec (fill - ret) (bb + hb)); [|exfalso; lia]. injection RES as <- <- <-.
eapply (ps_ret0' _ [CB 48 junk]); try eassumption; [reflexivity|].
unfold sync_fields_ok, int31; cbn; lia.
- destruct (Z.ltb_spec (fill - ret) (bb + hb)); [exfalso; lia|].

pose proof (bytes_at_read1 asegs m D bytes (ret + 22) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as R22.
pose proof (bytes_at_read1 asegs m D bytes (ret + 23) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as R23.
pose proof (bytes_at_read1 asegs m D bytes (ret + 24) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as R24.
pose proof (bytes_at_read1 asegs m D bytes (ret + 25) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as R25.
pose proof (byte_range (nth (Z.to_nat (ret + 22)) bytes (Z_to_bv 8 0))) as Hc0. set (c0 := bv_unsigned (nth (Z.to_nat (ret + 22)) bytes (Z_to_bv 8 0))) in Hc0.
pose proof (byte_range (nth (Z.to_nat (ret + 23)) bytes (Z_to_bv 8 0))) as Hc1. set (c1 := bv_unsigned (nth (Z.to_nat (ret + 23)) bytes (Z_to_bv 8 0))) in Hc1.
pose proof (byte_range (nth (Z.to_nat (ret + 24)) bytes (Z_to_bv 8 0))) as Hc2. set (c2 := bv_unsigned (nth (Z.to_nat (ret + 24)) bytes (Z_to_bv 8 0))) in Hc2.
pose proof (byte_range (nth (Z.to_nat (ret + 25)) bytes (Z_to_bv 8 0))) as Hc3. set (c3 := bv_unsigned (nth (Z.to_nat (ret + 25)) bytes (Z_to_bv 8 0))) in Hc3.
ostep. ostep. ostep. ostep. unfold zxb. cbv beta. fold c0 c1 c2 c3.
pose proof (u8arr_store_ok asegs _ _ _ (ret + 22) (wa (D + ret + 22)) ARR ltac:(rewrite ?upd_length; lia) ltac:(f_equal; lia)) as SOK.
ostep. arr_store ARR (ret + 22) (Z_to_bv 8 0).
pose proof (u8arr_store_ok asegs _ _ _ (ret + 23) (wa (D + ret + 23)) ARR ltac:(rewrite ?upd_length; lia) ltac:(f_equal; lia)) as SOK.
ostep. arr_store ARR (ret + 23) (Z_to_bv 8 0).
pose proof (u8arr_store_ok asegs _ _ _ (ret + 24) (wa (D + ret + 24)) ARR ltac:(rewrite ?upd_length; lia) ltac:(f_equal; lia)) as SOK.
ostep. arr_store ARR (ret + 24) (Z_to_bv 8 0).
pose proof (u8arr_store_ok asegs _ _ _ (ret + 25) (wa (D + ret + 25)) ARR ltac:(rewrite ?upd_length; lia) ltac:(f_equal; lia)) as SOK.
ostep. arr_store ARR (ret + 25) (Z_to_bv 8 0).

ostep. ostep. ostep. ostep. ostep. rewrite sx32_lit by (unfold int31; lia). ostep. ostep. rewrite sx32_lit by (unfold int31; lia).
ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep.

chunk_uncons FR as FR0.
match type of FR with rw_cells _ _ ?X (?ca :: ?cb :: ?cc :: ?cd :: ?rest) =>
change (ca :: cb :: cc :: cd :: rest) with ([ca; cb; cc; cd] ++ rest) in FR end.
apply rw_cells_app in FR. destruct FR as [PG FR]. cbn [cells_size csize Nat.add] in FR.
replace (bv_unsigned sp + -96 + 8 + Z.of_nat 32) with (bv_unsigned sp + -56) in FR by lia.
replace (bv_unsigned sp + -96 + 8) with (bv_unsigned sp + -88) in PG by lia.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (PG2 : rw_cells asegs mx (bv_unsigned sp + -88) (cks_page_cells (D + ret) hb (Z_to_bv 64 0) (D + ret + hb) bb (Z_to_bv 64 0))) end.
{ eapply rw_cells_recell; [exact PG| cbn; repeat split; reflexivity| | reflexivity].
unfold cks_page_cells, wz. cbn [cells_bytes cbytes app]. rewrite (le8_split_u32 hb), (le8_split_u32 bb) by lia.
rewrite <- !app_assoc. reflexivity. }
clear PG. unfold cks_page_cells, wz in PG2.
match type of ARR with u8arr _ _ _ ?b4 => set (bytes4 := b4) in ARR end.
assert (L4 : length bytes4 = length bytes) by (unfold bytes4; rewrite !upd_length; reflexivity).
call_sp (ogg_page_checksum_set_spec D ret hb bb bytes4 (bv_unsigned sp + -88) lo (Z_to_bv 64 0) (Z_to_bv 64 0)).
1:{ exact PG2. } 1:{ exact ARR. } 1:{ exact ST. } 1:{ exact MI. }
1-10: try lia. 1:{ reflexivity. }
rename POST into ARR. rename PC into ST.
assert (E4 : bytes4 = upd_bytes bytes (Z.to_nat (ret + 22)) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]).
{ subst bytes4. apply upd4_upd_bytes; lia. }
clearbody bytes4. subst bytes4.
pose proof (checksum_model buf bytes ret hb bb PRE ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as ECK.
unfold ogg_page_checksum in ARR. unfold ogg_page_checksum at 2 in ECK. cbv zeta in ARR, ECK. cbn [map] in ARR.
match type of ARR with context [Z_to_bv _ (?c mod 256)] => set (crc := c) in ARR, ECK end.
clearbody crc.
eapply (ps_tail2' _ (firstn 8 (firstn 44 junk)) (skipn 8 (skipn 8 (skipn 8 (skipn 16 (firstn 44 junk))))) hb bb crc c0 c1 c2 c3);
try eassumption; try reflexivity; try lia.
Qed.

Lemma ps_hdr : forall m (junk : list byte) r ogo (sy' : sync_st bptr)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
sy_headerbytes sy = 0 ->
FRAME m [CB 48 junk] -> stk asegs m lo (bv_unsigned sp + -96) ->
munch W m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
rw_cells asegs m A (sync_cells D sy) -> u8arr asegs m D bytes -> rw_cells asegs m G ogc ->
ogg_sync_pageseek sy = ((r, ogo), sy') ->
evt asegs (POST r ogo sy')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (D + sy_returned sy)) (Z_to_bv 64 (sy_fill sy - sy_returned sy)) (Z_to_bv 64 D)
s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xb919c) fc None m (seg_rom asegs)).
Proof.
intros until x31. intros Hhb0 FR ST MU WM MI SY ARR OG RES.
pose proof FOK as sfP_; first [ sf_destruct 6%nat sfP_ as Fs Ff Fr Fu Fh Fbb | sf_fb; destruct sfP_ as (Fs & Ff & Fr & Fu & Fh & Fbb) ]. unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb.
pose proof PRE as [PRE1 PRE2]. pose proof INV as [[I1 [I2 [I3 [I4 Ibok]]]] [SH1 SH2]]. unfold zlength in I2.
specialize (SH1 Hhb0).
set (ret := sy_returned sy) in *. set (fill := sy_fill sy) in *. set (buf := sy_buf sy) in *.
pose proof (znth_bytes_ok buf (ret + 26) Ibok) as Rnseg. set (nseg := znth buf (ret + 26)) in *.
pose proof (rw_cells_bound _ _ _ _ SY) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add app length] in FB.
unfold sync_cells, wz in SY.

unfold ogg_sync_pageseek, ogg_sync_check in RES. fold ret fill buf in RES.
destruct (Z.ltb_spec (sy_storage sy) 0); [lia|]. rewrite Hhb0, Z.eqb_refl in RES.

ostep. ostep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
-
destruct (Z.ltb_spec (fill - ret) 27); [exfalso; lia|].
pose proof (bytes_at_read1 asegs m D bytes ret _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as R0.
pose proof (bytes_at_read1 asegs m D bytes (ret + 1) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as R1.
pose proof (bytes_at_read1 asegs m D bytes (ret + 2) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as R2.
pose proof (bytes_at_read1 asegs m D bytes (ret + 3) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as R3.

ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep.
pose proof (pre_zslice4 buf bytes ret PRE ltac:(lia) ltac:(lia)) as ECS.
ostep. if_cases K2.
+
apply (proj1 (oggs_compare _ _ _ _)) in K2. rewrite <- ECS in K2. rewrite K2 in RES.
rewrite (proj2 (list_eqb_eq _ _) eq_refl) in RES. cbn [negb] in RES. fold nseg in RES.

pose proof (bytes_at_read1 asegs m D bytes (ret + 26) _ (proj1 ARR) ltac:(lia) ltac:(lia) eq_refl) as R26.
ostep. unfold zxb. cbv beta. rewrite <- (pre_znth buf bytes (ret + 26) PRE) by lia. fold nseg.
ostep. ostep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
*
destruct (Z.ltb_spec (fill - ret) (nseg + 27)); [|exfalso; lia]. injection RES as <- <- <-.
eapply (ps_ret0' _ [CB 48 junk] sy); try eassumption. reflexivity.
* destruct (Z.ltb_spec (fill - ret) (nseg + 27)); [exfalso; lia|].

ostep. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
--
ostep. ostep.
rewrite K4 in *. rewrite zslice_0 in RES. cbn [zsum] in RES. rewrite Z.add_0_r in RES.
eapply (ps_tail _ junk (0 + 27) (sy_bodybytes sy) (mkSync (sy_data sy) buf (sy_storage sy) fill ret (sy_unsynced sy) (0 + 27) (sy_bodybytes sy)));
fold ret fill buf; fold nseg; rewrite ?K4; try eassumption; try reflexivity; try lia.
--
ostep. ostep. rewrite sx32_lit by (unfold int31; lia). ostep.
call (ps_hloop (Z.to_nat nseg) 0 _ sy nseg (sy_bodybytes sy) (sy_bodybytes sy) (D + ret + 27)).
all: fold ret fill buf; fold nseg; try lia.
1:{ unfold zlength. lia. } 1:{ rewrite zslice_0. cbn. lia. } 1:{ exact FOK. }
1:{ unfold sync_cells, wz. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes]. fold ret fill. exact SY. }
1:{ exact ARR. } 1:{ exact MI. }
rename POST into SY2. unfold sync_cells, wz in SY2. cbn [sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes] in SY2.
fold ret fill buf in SY2. fold ret fill.

ostep. ostep.
eapply (ps_tail _ junk (nseg + 27) (sy_bodybytes sy + zsum (zslice (ret + 27) nseg buf))
(mkSync (sy_data sy) buf (sy_storage sy) fill ret (sy_unsynced sy) (nseg + 27) (sy_bodybytes sy + zsum (zslice (ret + 27) nseg buf))));
fold ret fill buf; fold nseg; try eassumption; try reflexivity; try lia.
+
assert (NE : zslice ret 4 buf <> OGGS_MAGIC).
{ intros E. rewrite ECS in E. apply (proj2 (oggs_compare _ _ _ _)) in E. rewrite E in K2. discriminate K2. }
destruct (list_eqb (zslice ret 4 buf) OGGS_MAGIC) eqn:LE; [apply list_eqb_eq in LE; contradiction|]. cbn [negb] in RES.
assert (ogo = None) as ->.
{ unfold sync_fail in RES. destruct (X1qz.find_byte _ _ _); congruence. }
eapply (ps_sync_fail' _ [CB 48 junk] sy); try eassumption; try reflexivity; cbn; try lia.
-
destruct (Z.ltb_spec (fill - ret) 27); [|exfalso; lia]. injection RES as <- <- <-.
eapply (ps_ret0' _ [CB 48 junk] sy); try eassumption; try reflexivity.
Qed.

Lemma ps_body : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) r ogo (sy' : sync_st bptr),
stk asegs m0 lo (bv_unsigned sp) -> mem_inv asegs m0 ->
rw_cells asegs m0 A (sync_cells D sy) -> u8arr asegs m0 D bytes -> rw_cells asegs m0 G ogc ->
ogg_sync_pageseek sy = ((r, ogo), sy') ->
evt asegs (POST r ogo sy')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_pageseek) fc None m0 (seg_rom asegs)).
Proof.
intros until sy'. intros ST MI SY ARR OG RES. unfold A_ogg_sync_pageseek.
pose proof FOK as sfP_; first [ sf_destruct 6%nat sfP_ as Fs Ff Fr Fu Fh Fbb | sf_fb; destruct sfP_ as (Fs & Ff & Fr & Fu & Fh & Fbb) ]. unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb.
pose proof INV as [[I1 [I2 [I3 [I4 Ibok]]]] [SH1 SH2]]. unfold zlength in I2.
pose proof (rw_cells_bound _ _ _ _ SY) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof (rw_cells_bound _ _ _ _ OG) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl W m0) as MU. pose proof (wmono_refl asegs m0) as WM.
unfold sync_cells, wz in SY.
carve_frame 96%nat ST.

ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep.
ostep. rewrite sx32_lit by (unfold int31; lia).
ostep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia; [exfalso; lia|].

ostep. ostep. ostep. rewrite sx32_lit by (unfold int31; lia). ostep. rewrite sx32_lit by (unfold int31; lia).
ostep. rewrite sx32_lit by (unfold int31; lia). ostep. rewrite swrap32_small by lia. ostep.
ostep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
-
eapply ps_hdr; try eassumption.
-
destruct (SH2 K2) as (Hhb & Hfit & Hbb).
eapply (ps_tail _ _ (sy_headerbytes sy) (sy_bodybytes sy) sy); try eassumption; try reflexivity; try lia.
unfold ogg_sync_pageseek, ogg_sync_check in RES.
destruct (Z.ltb_spec (sy_storage sy) 0); [lia|].
replace (sy_headerbytes sy =? 0) with false in RES by (symmetry; apply Z.eqb_neq; lia).
cbv beta iota zeta in RES. exact RES.
Qed.
End PS.

Lemma ogg_sync_pageseek_spec : forall (A G D lo : Z) (bytes : list byte) (sy : sync_st bptr) (j0 j1 j2 j3 : list byte)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) r ogo (sy' : sync_st bptr),
sync_fields_ok sy -> sync_inv2 sy -> buf_pre (sy_buf sy) bytes -> Z.of_nat (length bytes) = sy_storage sy ->
0 <= D -> D + Z.of_nat (length bytes) < 2^63 -> 0 < A -> 0 < G -> lo + 128 <= bv_unsigned sp ->
(A + 32 <= lo \/ bv_unsigned sp <= A) -> (G + 32 <= lo \/ bv_unsigned sp <= G) -> (D + Z.of_nat (length bytes) <= lo \/ bv_unsigned sp <= D) ->
(A + 32 <= G \/ G + 32 <= A) -> (A + 32 <= D \/ D + Z.of_nat (length bytes) <= A) -> (G + 32 <= D \/ D + Z.of_nat (length bytes) <= G) ->
stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
rw_cells asegs m A (sync_cells D sy) -> u8arr asegs m D bytes -> rw_cells asegs m G [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3] ->
ogg_sync_pageseek sy = ((r, ogo), sy') ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 G ->
evt asegs (pageseek_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A G D lo bytes [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3] sy m r ogo sy')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_pageseek) fc None m (seg_rom asegs)).
Proof.
intros until sy'. intros FOK INV PRE LENB HD TOPD HA HG LO S1 S2 S3 S4 S5 S6 ST MI SY ARR OG RES -> ->.
eapply (ps_body A G D lo bytes sy j0 j1 j2 j3); eassumption.
Qed.
