(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1cc X1bk X1bj X1cf X1bu.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fc.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ii X1io X1j8 X1j5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1rl X1nw X1qz X1r0 X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section RetRange.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
#[using="Type"] Lemma pageseek_ret_range : forall (sy : sync_st ptr) r og sy',
sync_inv sy -> sy_fill sy < 2^31 -> ogg_sync_pageseek sy = ((r, og), sy') -> -2^31 < r < 2^31.
Proof.
intros sy r og sy' INV Hf E. pose proof INV as sfP_; first [ sf_destruct 5%nat sfP_ as I1 I2 I3 I4 I5 | sf_fb; destruct sfP_ as (I1 & I2 & I3 & I4 & I5) ].
unfold ogg_sync_pageseek in E.
destruct (ogg_sync_check sy). { inversion E; subst; lia. }
assert (SF : forall (sy0 : sync_st ptr) rr oo ss, sy_fill sy0 = sy_fill sy ->
sync_fail sy0 (sy_returned sy) (sy_fill sy - sy_returned sy) = ((rr, oo), ss) -> -2^31 < rr < 2^31).
{ intros sy0 rr oo ss Hf0 ES. unfold sync_fail in ES.
destruct (X1qz.find_byte _ _ _) as [i|] eqn:FB; inversion ES; subst.
- apply find_byte_range in FB. unfold zslice in FB.
unfold zlength, ztake in FB. rewrite length_firstn in FB. lia.
- lia. }
assert (TAIL : forall (crc_ok : bool) (sy0 : sync_st ptr),
sy_fill sy0 = sy_fill sy -> 0 <= sy_headerbytes sy0 -> 0 <= sy_bodybytes sy0 ->
(if sy_fill sy - sy_returned sy <? sy_bodybytes sy0 + sy_headerbytes sy0 then (0, None, sy0)
else if negb crc_ok
then sync_fail sy0 (sy_returned sy) (sy_fill sy - sy_returned sy)
else (sy_headerbytes sy0 + sy_bodybytes sy0,
Some {| pg_hdr := sy_returned sy; pg_header_len := sy_headerbytes sy0; pg_body_len := sy_bodybytes sy0 |},
{| sy_data := sy_data sy0; sy_buf := sy_buf sy; sy_storage := sy_storage sy0; sy_fill := sy_fill sy0;
sy_returned := sy_returned sy + (sy_headerbytes sy0 + sy_bodybytes sy0);
sy_unsynced := 0; sy_headerbytes := 0; sy_bodybytes := 0 |})) = (r, og, sy') -> -2^31 < r < 2^31).
{ intros crc_ok sy0 Hf0 Hh Hb E0.
destruct (Z.ltb_spec (sy_fill sy - sy_returned sy) (sy_bodybytes sy0 + sy_headerbytes sy0)). { inversion E0; subst; lia. }
destruct crc_ok; cbn [negb] in E0. { inversion E0; subst; lia. } eapply SF; eauto. }
destruct (sy_headerbytes sy =? 0) eqn:Hhb0.
- destruct (Z.ltb_spec (sy_fill sy - sy_returned sy) 27). { inversion E; subst; lia. }
destruct (negb (list_eqb _ OGGS_MAGIC)). { eapply SF; eauto. }
pose proof (znth_bytes_ok (sy_buf sy) (sy_returned sy + 26) I5) as Hnseg.
destruct (Z.ltb_spec (sy_fill sy - sy_returned sy) (znth (sy_buf sy) (sy_returned sy + 26) + 27)). { inversion E; subst; lia. }
eapply TAIL; [..|exact E]; cbn; try lia.
pose proof (zsum_bytes_nonneg _ (bytes_ok_zslice (sy_returned sy + 27) (znth (sy_buf sy) (sy_returned sy + 26)) _ I5)). lia.
- eapply TAIL; [..|exact E]; cbn; lia.
Qed.
End RetRange.

Lemma lts0_wz : forall r, -2^63 <= r < 2^63 -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 r) = (0 <? r).
Proof. intros r Hr. unfold bv_lts. rewrite !signed_lit_small by lia. reflexivity. Qed.
Lemma eqb0_wz : forall r, -2^63 <= r < 2^63 -> bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 0) = (r =? 0).
Proof.
intros r Hr. unfold bv_eqb. rewrite (unsigned_lit 0) by lia. rewrite unsigned_lit_wrap.
destruct (Z.eqb_spec r 0) as [->|NE]; [reflexivity|].
apply Z.eqb_neq. intros E. apply NE.
destruct (Z.lt_ge_cases r 0).
- replace (r mod 2^64) with (r + 2^64) in E by (apply Z.mod_unique with (q := -1); lia). lia.
- rewrite Z.mod_small in E by lia. exact E.
Qed.

Definition pageout_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A G D lo : Z) (bytes : list byte) (ogc : list cell) (m : mem)
(r : Z) (ogo : option page) (sy' : sync_st bptr) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (A, A + 32); (G, G + 32); (D, D + Z.of_nat (length bytes))] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' A (sync_cells D sy') /\ sync_fields_ok sy'
/\ u8arr rsegs m' D bytes
/\ rw_cells rsegs m' G (og_cells D ogo ogc).

Section PO.
Context {RCEIL : RunCeiling}.
Variables (A G D lo : Z) (bytes : list byte) (sy : sync_st bptr) (j0 j1 j2 j3 : list byte).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
Local Notation ogc := [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3].
Local Notation W := [(bv_unsigned sp - 160, bv_unsigned sp); (A, A + 32); (G, G + 32); (D, D + Z.of_nat (length bytes))].
Local Notation len := (Z.of_nat (length bytes)).
Hypothesis PRE : buf_pre (sy_buf sy) bytes.
Hypothesis LENB : len = sy_storage sy.
Hypothesis HD : 0 <= D. Hypothesis TOPD : D + len < 2^63.
Hypothesis HA : 0 < A. Hypothesis HG : 0 < G.
Hypothesis LO : lo + 160 <= bv_unsigned sp.
Hypothesis SEP_fA : A + 32 <= lo \/ bv_unsigned sp <= A.
Hypothesis SEP_fG : G + 32 <= lo \/ bv_unsigned sp <= G.
Hypothesis SEP_fD : D + len <= lo \/ bv_unsigned sp <= D.
Hypothesis SEP_AG : A + 32 <= G \/ G + 32 <= A.
Hypothesis SEP_AD : A + 32 <= D \/ D + len <= A.
Hypothesis SEP_GD : G + 32 <= D \/ D + len <= G.

Notation POST := (pageout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A G D lo bytes ogc m0).
Notation FRAME m junk := (rw_cells rsegs m (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra]).

#[using="LO"] Lemma po_epilogue : forall m (junk : list byte) r ogo (sy' : sync_st bptr)
(x1 x5 x6 x7 x8 x9 va0 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
FRAME m junk -> stk rsegs m lo (bv_unsigned sp + -32) ->
munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
rw_cells rsegs m A (sync_cells D sy') -> sync_fields_ok sy' -> u8arr rsegs m D bytes ->
rw_cells rsegs m G (og_cells D ogo ogc) ->
va0 = wz r ->
evt rsegs (POST r ogo sy')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 x8 x9 va0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x3084c) fc None m (seg_rom rsegs)).
Proof.
intros until x31. intros FR ST MU WM MI SY FOK' ARR OG ->. unfold wz.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
zstep. zstep. zstep. zstep.
pose proof (stk_release _ _ _ _ _ ST FR ltac:(lia)) as ST2. clear ST FR.
cbn [cells_size csize Nat.add] in ST2. replace (bv_unsigned sp + -32 + Z.of_nat 32) with (bv_unsigned sp) in ST2 by lia.
zstep. finish.
Qed.

#[using="PRE LENB HD TOPD HA HG LO SEP_fA SEP_fG SEP_fD SEP_AG SEP_AD SEP_GD"] Lemma po_loop : forall (fuel : nat) (sy1 : sync_st bptr) m (junk : list byte) r ogo (sy' : sync_st bptr)
(x1 x5 x6 x7 va0 va1 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
pageout_loop fuel sy1 = Some ((r, ogo), sy') ->
sync_fields_ok sy1 -> sync_inv2 sy1 -> sy_buf sy1 = sy_buf sy -> sy_storage sy1 = sy_storage sy ->
FRAME m junk -> stk rsegs m lo (bv_unsigned sp + -32) ->
munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
rw_cells rsegs m A (sync_cells D sy1) -> u8arr rsegs m D bytes -> rw_cells rsegs m G ogc ->
evt rsegs (POST r ogo sy')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 G) va0 va1 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x30814) fc None m (seg_rom rsegs)).
Proof.
induction fuel as [|fuel IH]; intros sy1 m junk r ogo sy' x1 x5 x6 x7 va0 va1 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
E FOK1 INV1 EB ES FR ST MU WM MI SY ARR OG; [discriminate|].
cbn [pageout_loop] in E.
destruct (ogg_sync_pageseek sy1) as [[r1 og1] sy2] eqn:E1.
pose proof (ogg_sync_pageseek_inv sy1 r1 og1 sy2 (proj1 INV1) E1) as sfP_; first [ sf_destruct 7%nat sfP_ as Iv2 Hf2 Hb2 Hd2 Hs2 Hneg Hpos | sf_fb; destruct sfP_ as (Iv2 & Hf2 & Hb2 & Hd2 & Hs2 & Hneg & Hpos) ].
pose proof (ogg_sync_pageseek_inv2 sy1 r1 og1 sy2 INV1 E1) as [INV2 Hog].
pose proof FOK1 as sfP_; first [ sf_destruct 6%nat sfP_ as Fs Ff Fr Fu Fh Fbb | sf_fb; destruct sfP_ as (Fs & Ff & Fr & Fu & Fh & Fbb) ]. unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb.
pose proof (pageseek_ret_range sy1 r1 og1 sy2 (proj1 INV1) ltac:(lia) E1) as Hr1.
assert (PRE1 : buf_pre (sy_buf sy1) bytes) by (rewrite EB; exact PRE).
pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
pose proof (rw_cells_bound _ _ _ _ SY) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.

zstep. zstep. zstep.
call_sp (ogg_sync_pageseek_spec A G D lo bytes sy1 j0 j1 j2 j3).
all: try eassumption. all: try lia. all: try reflexivity.
rename PC into ST. rename PC1 into FOK2. rename PC0 into SY. rename PC2 into ARR. rename POST into OG. rename MI0 into MI.
pose proof FOK2 as sfP_; first [ sf_destruct 6%nat sfP_ as Fs2 Ff2 Fr2 Fu2 Fh2 Fbb2 | sf_fb; destruct sfP_ as (Fs2 & Ff2 & Fr2 & Fu2 & Fh2 & Fbb2) ]. unfold int31 in Fs2, Ff2, Fr2, Fu2, Fh2, Fbb2.
unfold wz.

zstep. rewrite lts0_wz by lia. if_cases K; [apply Z.ltb_lt in K | apply Z.ltb_ge in K].
-
destruct (Z.ltb_spec 0 r1); [|exfalso; lia]. injection E as <- <- <-.
zstep. eapply po_epilogue; try eassumption. reflexivity.
- destruct (Z.ltb_spec 0 r1); [exfalso; lia|].
destruct og1 as [pg|]; [destruct Hog; lia|]. cbn [og_cells] in OG.

zstep. rewrite eqb0_wz by lia. if_cases K2; [apply Z.eqb_eq in K2 | apply Z.eqb_neq in K2].
+
subst r1. destruct (Z.eqb_spec 0 0); [|lia]. injection E as <- <- <-.
eapply po_epilogue; try eassumption. reflexivity.
+ destruct (Z.eqb_spec r1 0); [lia|].
unfold sync_cells, wz in SY.

zstep. rewrite sx32_lit by (unfold int31; lia). zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
*
destruct (Z.eqb_spec (sy_unsynced sy2) 0); [lia|].
eapply (IH sy2); try eassumption; try congruence.
*
destruct (Z.eqb_spec (sy_unsynced sy2) 0); [|lia]. injection E as <- <- <-.
zstep. zstep. zstep. zstep.
eapply po_epilogue; try eassumption; [|reflexivity].
unfold sync_fields_ok, int31 in *; cbn. lia.
Qed.

#[using="PRE LENB HD TOPD HA HG LO SEP_fA SEP_fG SEP_fD SEP_AG SEP_AD SEP_GD"] Lemma po_body : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) r ogo (sy' : sync_st bptr),
sync_fields_ok sy -> sync_inv2 sy ->
stk rsegs m0 lo (bv_unsigned sp) -> mem_inv rsegs m0 ->
rw_cells rsegs m0 A (sync_cells D sy) -> u8arr rsegs m0 D bytes -> rw_cells rsegs m0 G ogc ->
ogg_sync_pageout sy = Some ((r, ogo), sy') ->
evt rsegs (POST r ogo sy')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_pageout) fc None m0 (seg_rom rsegs)).
Proof.
intros until sy'. intros FOK INV ST MI SY ARR OG RES. unfold A_ogg_sync_pageout.
pose proof FOK as sfP_; first [ sf_destruct 6%nat sfP_ as Fs Ff Fr Fu Fh Fbb | sf_fb; destruct sfP_ as (Fs & Ff & Fr & Fu & Fh & Fbb) ]. unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb.
pose proof (rw_cells_bound _ _ _ _ SY) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (rw_cells_bound _ _ _ _ OG) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl W m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
unfold ogg_sync_pageout, ogg_sync_check in RES. destruct (Z.ltb_spec (sy_storage sy) 0); [lia|].
unfold sync_cells, wz in SY.
carve_frame 32%nat ST.

zstep. zstep. zstep. zstep. zstep. zstep. rewrite sx32_lit by (unfold int31; lia).
zstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia; [exfalso; lia|].

zstep.
eapply (po_loop (pageout_fuel sy) sy); try eassumption; try reflexivity.
Qed.
End PO.

Lemma ogg_sync_pageout_spec : forall (A G D lo : Z) (bytes : list byte) (sy : sync_st bptr) (j0 j1 j2 j3 : list byte)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) r ogo (sy' : sync_st bptr),
sync_fields_ok sy -> sync_inv2 sy -> buf_pre (sy_buf sy) bytes -> Z.of_nat (length bytes) = sy_storage sy ->
0 <= D -> D + Z.of_nat (length bytes) < 2^63 -> 0 < A -> 0 < G -> lo + 160 <= bv_unsigned sp ->
(A + 32 <= lo \/ bv_unsigned sp <= A) -> (G + 32 <= lo \/ bv_unsigned sp <= G) -> (D + Z.of_nat (length bytes) <= lo \/ bv_unsigned sp <= D) ->
(A + 32 <= G \/ G + 32 <= A) -> (A + 32 <= D \/ D + Z.of_nat (length bytes) <= A) -> (G + 32 <= D \/ D + Z.of_nat (length bytes) <= G) ->
stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
rw_cells rsegs m A (sync_cells D sy) -> u8arr rsegs m D bytes -> rw_cells rsegs m G [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3] ->
ogg_sync_pageout sy = Some ((r, ogo), sy') ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 G ->
evt rsegs (pageout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A G D lo bytes [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3] m r ogo sy')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_pageout) fc None m (seg_rom rsegs)).
Proof.
intros until sy'. intros FOK INV PRE LENB HD TOPD HA HG LO S1 S2 S3 S4 S5 S6 ST MI SY ARR OG RES -> ->.
eapply (po_body A G D lo bytes sy j0 j1 j2 j3); eassumption.
Qed.
