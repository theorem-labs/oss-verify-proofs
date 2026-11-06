(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1dk X1cs X1dg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X09u X0ae.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1cu.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X110.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cu.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition RA_po_pageseek : Z := 0xc1a04.
Definition po_frame (ra s0 s1 : word) (j8 : list byte) : list cell := [CB 8 j8; C8 s1; C8 s0; C8 ra].

Section RetRange.
Context {ptr : Type}.
Lemma pageseek_ret_range : forall (sy : sync_st ptr) r og sy',
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

Lemma po_w1 : forall (A G D usp lo : Z) (sy : sync_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m A (sync_cells D sy) -> sync_fields_ok sy ->
stk bsegs m lo usp -> lo <= usp - 32 -> A + 32 <= lo -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (j8 : list byte),
ms = MS (mkR (Z_to_bv 64 RA_po_pageseek) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 G)
(Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_pageseek) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -32)
/\ rw_cells bsegs m1 (usp + -32) (po_frame ra s0 s1 j8))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_pageout) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SY FOK ST LO ALO A0 MI.
unfold A_ogg_sync_pageout, A_ogg_sync_pageseek, RA_po_pageseek, po_frame. unfold sync_cells, wz in SY.
pose proof FOK as (Fs & _). unfold int31 in Fs.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
carve_frame 32%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xc19f0. rewrite (sx32_lit (sy_storage sy)) by (unfold int31; lia). astep. sh_if.
ato 0xc17c4.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Lemma po_w2_ret : forall (A G r usp lo : Z) (j8 : list byte)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cra c0 c1 : word) F fc (m : mem),
0 <= r < 2^31 ->
rw_cells bsegs m (usp + -32) (po_frame cra c0 c1 j8) -> stk bsegs m lo (usp + -32) -> lo <= usp + -32 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 (if 0 <? r then 1 else 0)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp)
(MS (mkR (Z_to_bv 64 RA_po_pageseek) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 G) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_po_pageseek)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros R FR ST LO MI. unfold RA_po_pageseek, po_frame in *.
replace (ret_pc (Z_to_bv 64 0xc1a04)) with (Z_to_bv 64 0xc1a04) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
destruct (Z.ltb_spec 0 r) as [POS|ZERO].
- astep. sh_if. ato 0xc1a3c. release_frame FR ST usp. astep. astep.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
- assert (r = 0) as -> by lia.
astep. ato 0xc1a3c. release_frame FR ST usp. astep. astep.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

Lemma eqb0_wz : forall r, -2^63 <= r < 2^63 -> bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 0) = (r =? 0).
Proof.
intros r Hr. unfold bv_eqb. rewrite (unsigned_lit 0) by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
destruct (Z.eqb_spec r 0) as [->|NE]; [reflexivity|].
apply Z.eqb_neq. intros E. apply NE.
destruct (Z.lt_ge_cases r 0).
- replace (r mod 2^64) with (r + 2^64) in E by (apply Z.mod_unique with (q := -1); lia). lia.
- rewrite Z.mod_small in E by lia. exact E.
Qed.

Definition sync_cells_u (D : Z) (sy : sync_st bptr) (uns : Z) : list cell :=
[C8 (wz D); C4 (wz (sy_storage sy)); C4 (wz (sy_fill sy)); C4 (wz (sy_returned sy));
C4 (wz uns); C4 (wz (sy_headerbytes sy)); C4 (wz (sy_bodybytes sy))].

Lemma po_w2_unsync : forall (A G D r usp lo : Z) (sy : sync_st bptr) (j8 : list byte)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cra c0 c1 : word) F fc (m : mem),
- 2^31 < r < 0 -> sy_unsynced sy = 0 ->
rw_cells bsegs m A (sync_cells D sy) ->
rw_cells bsegs m (usp + -32) (po_frame cra c0 c1 j8) -> stk bsegs m lo (usp + -32) -> lo <= usp + -32 -> A + 32 <= lo -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 32); (usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
/\ rw_cells bsegs m1 A (sync_cells_u D sy 1))
(MS (mkR (Z_to_bv 64 RA_po_pageseek) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 G) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_po_pageseek)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros R U0 SY FR ST LO ALO A0 MI. unfold RA_po_pageseek, po_frame, sync_cells_u, sync_cells, wz in *.
replace (ret_pc (Z_to_bv 64 0xc1a04)) with (Z_to_bv 64 0xc1a04) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 32); (usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
rewrite U0 in SY.
astep. sh_if. astep. rewrite (eqb0_wz r) by lia. replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
ato 0xc1a10. rewrite (sx32_lit 0) by (unfold int31; lia). astep.
ato 0xc1a3c. release_frame FR ST usp. astep. astep.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact SY].
Qed.

Lemma po_w2_loop : forall (A G D r : Z) (sy : sync_st bptr)
(sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
- 2^31 < r < 0 -> sy_unsynced sy <> 0 -> sync_fields_ok sy ->
rw_cells bsegs m A (sync_cells D sy) -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms =>
ms = MS (mkR (Z_to_bv 64 RA_po_pageseek) sp gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 G)
(Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_pageseek) fc None m (seg_rom bsegs))
(MS (mkR (Z_to_bv 64 RA_po_pageseek) sp gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 G) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_po_pageseek)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros R U0 FOK SY A0 MI. unfold RA_po_pageseek, A_ogg_sync_pageseek, sync_cells, wz in *.
replace (ret_pc (Z_to_bv 64 0xc1a04)) with (Z_to_bv 64 0xc1a04) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof FOK as (_ & _ & _ & Fu & _). unfold int31 in Fu.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. sh_if. astep. rewrite (eqb0_wz r) by lia. replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
ato 0xc1a10. rewrite (sx32_lit (sy_unsynced sy)) by (unfold int31; lia). astep. sh_if.
ato 0xc17c4.
apply evt_done. reflexivity.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition RA_po_pageseek : Z := 0xb92d4.
Definition po_frame (ra s0 s1 : word) (j8 : list byte) : list cell := [CB 8 j8; C8 s1; C8 s0; C8 ra].

Section RetRange.
Context {ptr : Type}.
Lemma pageseek_ret_range : forall (sy : sync_st ptr) r og sy',
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

Lemma po_w1 : forall (A G D usp lo : Z) (sy : sync_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m A (sync_cells D sy) -> sync_fields_ok sy ->
stk asegs m lo usp -> lo <= usp - 32 -> A + 32 <= lo -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (j8 : list byte),
ms = MS (mkR (Z_to_bv 64 RA_po_pageseek) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 G)
(Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_pageseek) fc None m1 (seg_rom asegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -32)
/\ rw_cells asegs m1 (usp + -32) (po_frame ra s0 s1 j8))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_pageout) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SY FOK ST LO ALO A0 MI.
unfold A_ogg_sync_pageout, A_ogg_sync_pageseek, RA_po_pageseek, po_frame. unfold sync_cells, wz in SY.
pose proof FOK as (Fs & _). unfold int31 in Fs.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb92c0. rewrite (sx32_lit (sy_storage sy)) by (unfold int31; lia). astep. sh_if.
ato 0xb9094.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Lemma po_w2_ret : forall (A G r usp lo : Z) (j8 : list byte)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cra c0 c1 : word) F fc (m : mem),
0 <= r < 2^31 ->
rw_cells asegs m (usp + -32) (po_frame cra c0 c1 j8) -> stk asegs m lo (usp + -32) -> lo <= usp + -32 -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 (if 0 <? r then 1 else 0)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom asegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp)
(MS (mkR (Z_to_bv 64 RA_po_pageseek) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 G) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_po_pageseek)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros R FR ST LO MI. unfold RA_po_pageseek, po_frame in *.
replace (ret_pc (Z_to_bv 64 0xb92d4)) with (Z_to_bv 64 0xb92d4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
destruct (Z.ltb_spec 0 r) as [POS|ZERO].
- astep. sh_if. ato 0xb930c. release_frame FR ST usp. astep. astep.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
- assert (r = 0) as -> by lia.
astep. ato 0xb930c. release_frame FR ST usp. astep. astep.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

Lemma eqb0_wz : forall r, -2^63 <= r < 2^63 -> bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 0) = (r =? 0).
Proof.
intros r Hr. unfold bv_eqb. rewrite (unsigned_lit 0) by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
destruct (Z.eqb_spec r 0) as [->|NE]; [reflexivity|].
apply Z.eqb_neq. intros E. apply NE.
destruct (Z.lt_ge_cases r 0).
- replace (r mod 2^64) with (r + 2^64) in E by (apply Z.mod_unique with (q := -1); lia). lia.
- rewrite Z.mod_small in E by lia. exact E.
Qed.

Definition sync_cells_u (D : Z) (sy : sync_st bptr) (uns : Z) : list cell :=
[C8 (wz D); C4 (wz (sy_storage sy)); C4 (wz (sy_fill sy)); C4 (wz (sy_returned sy));
C4 (wz uns); C4 (wz (sy_headerbytes sy)); C4 (wz (sy_bodybytes sy))].

Lemma po_w2_unsync : forall (A G D r usp lo : Z) (sy : sync_st bptr) (j8 : list byte)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cra c0 c1 : word) F fc (m : mem),
- 2^31 < r < 0 -> sy_unsynced sy = 0 ->
rw_cells asegs m A (sync_cells D sy) ->
rw_cells asegs m (usp + -32) (po_frame cra c0 c1 j8) -> stk asegs m lo (usp + -32) -> lo <= usp + -32 -> A + 32 <= lo -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 32); (usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
/\ rw_cells asegs m1 A (sync_cells_u D sy 1))
(MS (mkR (Z_to_bv 64 RA_po_pageseek) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 G) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_po_pageseek)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros R U0 SY FR ST LO ALO A0 MI. unfold RA_po_pageseek, po_frame, sync_cells_u, sync_cells, wz in *.
replace (ret_pc (Z_to_bv 64 0xb92d4)) with (Z_to_bv 64 0xb92d4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 32); (usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
rewrite U0 in SY.
astep. sh_if. astep. rewrite (eqb0_wz r) by lia. replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
ato 0xb92e0. rewrite (sx32_lit 0) by (unfold int31; lia). astep.
ato 0xb930c. release_frame FR ST usp. astep. astep.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact SY].
Qed.

Lemma po_w2_loop : forall (A G D r : Z) (sy : sync_st bptr)
(sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
- 2^31 < r < 0 -> sy_unsynced sy <> 0 -> sync_fields_ok sy ->
rw_cells asegs m A (sync_cells D sy) -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms =>
ms = MS (mkR (Z_to_bv 64 RA_po_pageseek) sp gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 G)
(Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_pageseek) fc None m (seg_rom asegs))
(MS (mkR (Z_to_bv 64 RA_po_pageseek) sp gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 G) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_po_pageseek)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros R U0 FOK SY A0 MI. unfold RA_po_pageseek, A_ogg_sync_pageseek, sync_cells, wz in *.
replace (ret_pc (Z_to_bv 64 0xb92d4)) with (Z_to_bv 64 0xb92d4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof FOK as (_ & _ & _ & Fu & _). unfold int31 in Fu.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. sh_if. astep. rewrite (eqb0_wz r) by lia. replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
ato 0xb92e0. rewrite (sx32_lit (sy_unsynced sy)) by (unfold int31; lia). astep. sh_if.
ato 0xb9094.
apply evt_done. reflexivity.
Qed.
