(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedSetupB1), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySchedSetupB1.v. *)
(* Image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/GrantEntrySchedSetupB1.v, ported from a working branch 7c8c67da870 (blob d6eb3c3959e): image B's own cut pcs (0x81a20 .. 0x81a50) and register file (s8 the scene's width and s7 the bytes left for the frame count, where image A has s10 and s8; s4 the table and s5 the scene's base, where image A has s4 and s2), the call contract of GrantBContracts.v (tb_reac_headamp_tx_set_resweep_spec, STK_reac_headamp_tx_set_resweep), and the slots of image B's sch_common, kept one by one, in place of image A's gslots_late. *)

(* Segment B1 of the scheduler's setup (LLVMFEntrySchedSetupDefs.v), the path with at
   most one input byte left at 0x81944: from the return of reac_headamp_tx_arm_scene at
   0x81a20 (GI_sch1a) to the return of reac_headamp_tx_set_resweep at 0x81a50 (GI_sch2).

   The slots 0x81a20 .. 0x81a48 set s8, s7, a2, a1, a3, a4 to 0, build the period
   a1 = (a2 | a1) | sext32 ((a4 | a3) << 16) = 0 and pass the table (s4) in a0; 0x81a4c
   calls reac_headamp_tx_set_resweep (t, 0). No slot of the segment branches or touches
   memory, so none of them can reach the error path, and image B has no UBSan guard in
   this stretch. The table that comes back is GrantSlotPlan.T_sched0: with at most one
   byte left, the scene's width and the four bytes of the period read as 0
   (Seg_sched_setup.sched_rd_bat, bat_out). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
YC1g YC1h YC1i YC45 YC85 GrantACjr ACj1 GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
LLVMFEntryDefs LLVMFEntrySeat LLVMFEntrySchedSetupDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampLayout.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
HeadampModel GrantSlotPlan SlotNeeds_c SegSetModel Seg_sched_setup reac_headamp_tx_set_resweep_c.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* A register the run left as the atom of the same register at the segment's start. *)
Ltac b1_reg HS EE n r H := prreg HS r H; rewrite (EE n r eq_refl) in H.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis RSW : GrantBContracts.tb_reac_headamp_tx_set_resweep_spec B.
Let RUN := paj_run B LAWS.

(* With at most one byte left at 0x81944, the scene's width reads as 0, and the table
   the scheduler starts from is the table after the scene with a re-assert period of 0. *)
Lemma sch_b1_model : forall cx, sch_L cx <= 1 ->
  sch_b cx 1 = 0 /\
  GrantSlotPlan.T_sched0 (c_pl cx) =
    reac_headamp_tx_set_resweep_c.set_resweep_T (sch_T1 cx) (Z_to_bv 64 0).
Proof.
intros cx HL. unfold sch_L, c_n in HL.
assert (OUT : forall j, (1 <= j)%nat ->
  Seg_sched_setup.bat (c_pl cx) (GrantSlotPlan.pos_raw (c_pl cx) + j) = 0)
  by (intros j Hj; apply Seg_sched_setup.bat_out; lia).
split; [unfold sch_b, sbat; apply OUT; lia|].
unfold GrantSlotPlan.T_sched0, sch_T1, sch_b, sbat.
pose proof (Seg_sched_setup.sched_rd_bat (c_pl cx)) as H.
destruct (GrantSlotPlan.sched_rd (c_pl cx)) as [[[[sb sw] per] f] p4].
destruct H as (-> & -> & -> & _).
rewrite (OUT 2%nat), (OUT 3%nat), (OUT 4%nat), (OUT 5%nat) by lia.
rewrite Nat.add_0_r. reflexivity.
Qed.

(* A callee-saved register, as aregs_preserved states it. *)
Lemma sch_b1_pres : forall (regs regs' : bvmap 5 word) (r : bv 5) (z : Z),
  aregs_preserved regs regs' -> acallee_saved z -> bv_unsigned r = z -> getr regs' r = getr regs r.
Proof.
intros regs regs' r z HP Hz Hr. subst z. pose proof (HP _ Hz) as H.
rewrite !Z_to_bv_bv_unsigned in H. exact H.
Qed.

Theorem sch_segB1 : forall POST, sch_segB1_stmt B MT POST.
Proof.
intros POST HN cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HI.
destruct HI as (t & HC & HL1 & R20 & R21 & Htab).
pose proof HC as (HBD & Hk & Hacc & Hbl & Hn26 & R19 & R22 & S8 & S40 & S48 & S64 & S72 & S96 & S112 &
  S128 & S136 & S144 & S152 & HWS & HST & HH & HI1).
pose proof HBD as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfc & HG & HSV & HSHW & HFL & Hlen & HINP).
pose proof HG as (G2 & G8 & G9 & G3 & G4).
pose proof Htab as (Htin & Ht0 & HTl & _).
destruct (sch_b1_model cx HL1) as (Hb1 & HTS).
assert (Hfb8 : fs_frame_bytes GE_CID / 8 = 128) by (vm_compute; reflexivity).
assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
pose proof (SegSetModel.tables_end_inv (c_pl cx)) as (_ & LWS & LST & _ & _).
(* ---- the seat at 0x81a20: the registers as atoms, no region ---- *)
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall (n : nat) (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E n = getr (ms_regs ms3) r0)
  by (intros n0 r0 Hr; subst E; apply ew_Eimg_Ereg_nat; exact Hr).
assert (HGM : gmach cx ms3 GP_sch1a) by exact (conj Hpc (conj Hrv (conj Hsvc (conj Hrom (conj Hfrg (conj Hfc HG)))))).
assert (HS : st_ok_pi SEGS VAL E (mkSS GP_sch1a sr_atoms [] None (mkFacts [] [] [])) (restrict (w_H W3) ms3)).
{ rewrite (gmach_mkst cx ms3 GP_sch1a HGM), restrict_mkst_fx. subst E.
  apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS sch_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
clear HE.
(* ---- 0x81a20 .. 0x81a48, up to the call of reac_headamp_tx_set_resweep at 0x81a4c:
   no branch, no load, no store ---- *)
paj_run_tok RUN HS HJ SHOK sch_span; [apply awr_ok_nil |].
lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msX) |- _ => rename msX into msc end.
lazymatch goal with HFx : frame_of _ _ (ms_mem ms3) (ms_mem msc) |- _ =>
  assert (MEQ : forall x, ms_mem msc x = ms_mem ms3 x) by (intros x; exact (frame_of_nil _ _ _ x HFx))
end.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
b1_reg HS EE 2%nat (2%bv : bv 5) P2. b1_reg HS EE 3%nat (3%bv : bv 5) P3.
b1_reg HS EE 4%nat (4%bv : bv 5) P4. b1_reg HS EE 8%nat (8%bv : bv 5) P8.
b1_reg HS EE 9%nat (9%bv : bv 5) P9. b1_reg HS EE 19%nat (19%bv : bv 5) P19.
b1_reg HS EE 20%nat (20%bv : bv 5) P20. b1_reg HS EE 21%nat (21%bv : bv 5) P21.
b1_reg HS EE 22%nat (22%bv : bv 5) P22.
rewrite (EE 20%nat 20%bv eq_refl), R20 in Q10.
assert (A11 : getr (ms_regs msc) 11 = Z_to_bv 64 0)
  by (rewrite Q11; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
assert (A23 : getr (ms_regs msc) 23 = Z_to_bv 64 0)
  by (rewrite Q23; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
assert (A24 : getr (ms_regs msc) 24 = Z_to_bv 64 0)
  by (rewrite Q24; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
assert (Hra : getr (ms_regs msc) 1 = Z_to_bv 64 (BASE + GP_sch2)) by (rewrite Q1; reflexivity).
(* the memory is the memory at 0x81a20 *)
assert (K0 : forall rs, ge_keep cx fp W3 rs (ms_mem ms3) (ms_mem msc))
  by (intros rs; exact (ge_keep_pointwise cx fp W3 rs _ _ MEQ)).
pose proof (ge_gsaved_keep B MT cx fp W3 HB [] ms3 msc (K0 []) HSV) as HSVc.
pose proof (gtab_obj B cx ly3 S3 W3 msc t (sch_T1 cx)
  (ge_gtab_keep B cx fp W3 ly3 S3 [(t, 460)] ms3 msc t (sch_T1 cx) (K0 [(t, 460)]) (or_introl eq_refl) Htab)) as HOBJ.
assert (HFPt : forall a, inFP [(t + 452, t + 460)] a -> t <= a < t + 460).
{ intros a Ha. apply inFP_cons in Ha as [Ha | Ha]; [lia | destruct (inFP_nil a Ha)]. }
assert (S0 : rdword (aview SEGS (w_H W3) (ms_mem msc)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
{ pose proof (proj2 HSVc 0 ltac:(lia)) as X.
  replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in X by lia.
  rewrite X. reflexivity. }
pmkst HS. rewrite pa_sigma_reac_headamp_tx_set_resweep.
(* ---- 0x81a4c: reac_headamp_tx_set_resweep (t, 0) ---- *)
refine (gcall B MT LAWS GrantBContracts.STK_reac_headamp_tx_set_resweep [(t + 452, t + 460)]
  (fun ly' S' W' regs' mem' md' => ly' = ly3 /\ S' = S3 /\ W' = W3 /\
     obj_at SEGS (mrestrict (w_H W3) mem') t LAY_TX
       (tx_vals (reac_headamp_tx_set_resweep_c.set_resweep_T (sch_T1 cx) (getr (ms_regs msc) 11))))
  _ GP_sch2 POST cx fp k ly3 S3 W3 (ms_regs msc) (ms_mem msc) _ HB HJ
  (eq_trans P2 G2) (eq_trans P8 G8) (eq_trans P3 G3) (eq_trans P4 G4) Hra
  ltac:(unfold GP_sch2; lia) eq_refl (proj1 HSVc) S0
  ltac:(unfold GrantBContracts.STK_reac_headamp_tx_set_resweep, ESTACK; lia) _ _ _).
- intros a Ha. exists t, 460. split; [exact Htin|].
  split; [exact (sch_notin_base B LAWS cx ly3 S3 W3 (ms_mem msc) _ t (proj1 HJ) Hbl)|].
  change (req_size 460) with 460. pose proof (HFPt a Ha). lia.
- intros HPRE.
  pose proof (RSW ly3 S3 W3 (ms_regs msc) (ms_mem msc) _ (gch cx) t (sch_T1 cx) HPRE Q10 Htin HTl HOBJ) as HR.
  unfold GrantBContracts.tb_reac_headamp_tx_set_resweep_post, cfg_at in HR. exact HR.
- intros W2 ly2 S2 regs2 mem2 md2 HJ2 HJc HP (-> & -> & -> & Hobj).
  pose proof (sch_keep_call B MT LAWS cx fp W3 msc ly3 S3 _ k t GrantBContracts.STK_reac_headamp_tx_set_resweep
    [(t + 452, t + 460)] (ms_mem msc) _ mem2 md2 0 HB HJ Hfr Hbl (proj1 HJ) HFPt HJc) as KC.
  pose proof (ge_keep_trans cx fp W3 [] _ _ _ (K0 []) KC) as KC3.
  assert (X : forall (r : bv 5) z, acallee_saved z -> bv_unsigned r = z ->
                getr regs2 r = getr (ms_regs msc) r)
    by (intros r z Hz Hr; exact (sch_b1_pres _ _ r z HP Hz Hr)).
  rewrite A11 in Hobj. rewrite <- HTS in Hobj.
  assert (LT : length (GrantSlotPlan.T_sched0 (c_pl cx)) = 460%nat).
  { rewrite HTS. unfold reac_headamp_tx_set_resweep_c.set_resweep_T.
    assert (L1 : length (Mem.upd_bytes (sch_T1 cx) 452 (Mem.le4 (Z_to_bv 64 0))) = 460%nat)
      by (rewrite Mem.upd_bytes_length; [exact HTl | rewrite Mem.length_le4; lia]).
    rewrite Mem.upd_bytes_length; [exact L1 | rewrite Mem.length_le4; lia]. }
  set (ms4 := mkst regs2 (Z_to_bv 64 (BASE + GP_sch2)) mem2 (seg_rom SEGS)).
  (* a slot of sch_common, kept across the call *)
  assert (SK4 : forall off v, 0 <= off <= 184 -> gslot cx W3 ms3 off v -> gslot cx W3 ms4 off v)
    by (intros off v Hoff Hv; exact (ge_gslot_keep B MT cx fp W3 HB [] ms3 ms4 off v KC3 ltac:(lia) ltac:(lia) Hv)).
  (* a register the run and the call both keep *)
  assert (RK : forall (r : bv 5) z, acallee_saved z -> bv_unsigned r = z ->
                 getr (ms_regs msc) r = getr (ms_regs ms3) r -> getr (ms_regs ms4) r = getr (ms_regs ms3) r)
    by (intros r z Hz Hr Hrr; exact (eq_trans (X r z Hz Hr) Hrr)).
  apply (HN cx fp k acc ly3 S3 W3 ms4 md2 HB HJ2 Hfr Hmo).
  exists t. unfold sch_common. sch_splits.
  + (* the body: pc, registers, saved words, shadow, flag, input *)
    unfold ge_body.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hlen _))))))))))).
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * unfold gregs. refine (conj _ (conj _ (conj _ (conj _ _)))).
      -- exact (eq_trans (RK 2%bv 2 ltac:(unfold acallee_saved; lia) eq_refl P2) G2).
      -- exact (eq_trans (RK 8%bv 8 ltac:(unfold acallee_saved; lia) eq_refl P8) G8).
      -- exact (eq_trans (RK 9%bv 9 ltac:(unfold acallee_saved; lia) eq_refl P9) G9).
      -- exact (eq_trans (RK 3%bv 3 ltac:(unfold acallee_saved; lia) eq_refl P3) G3).
      -- exact (eq_trans (RK 4%bv 4 ltac:(unfold acallee_saved; lia) eq_refl P4) G4).
    * exact (ge_gsaved_keep B MT cx fp W3 HB [] ms3 ms4 KC3 HSV).
    * apply (ge_gshadow_keep cx fp W3 [] ms3 ms4 GSH_c KC3); [rewrite Hlen; unfold GE_NSH; rewrite Hfb8; lia | exact HSHW].
    * exact (ge_flag_keep cx fp W3 [] ms3 ms4 KC3 HFL).
    * exact (ge_input_keep cx fp W3 [] ms3 ms4 KC3 HINP).
  + exact Hk.
  + exact Hacc.
  + exact Hbl.
  + exact Hn26.
  + exact (eq_trans (RK 19%bv 19 ltac:(unfold acallee_saved; lia) eq_refl P19) R19).
  + exact (eq_trans (RK 22%bv 22 ltac:(unfold acallee_saved; lia) eq_refl P22) R22).
  + exact (SK4 8 _ ltac:(lia) S8).
  + exact (SK4 40 _ ltac:(lia) S40).
  + exact (SK4 48 _ ltac:(lia) S48).
  + exact (SK4 64 _ ltac:(lia) S64).
  + exact (SK4 72 _ ltac:(lia) S72).
  + exact (SK4 96 _ ltac:(lia) S96).
  + exact (SK4 112 _ ltac:(lia) S112).
  + exact (SK4 128 _ ltac:(lia) S128).
  + exact (SK4 136 _ ltac:(lia) S136).
  + exact (SK4 144 _ ltac:(lia) S144).
  + exact (SK4 152 _ ltac:(lia) S152).
  + apply (ge_gfarr_keep cx fp W3 [] ms3 ms4 GO_WAS _ KC3); [unfold GO_WAS; lia | rewrite LWS, Hfb; unfold GO_WAS; lia | exact HWS].
  + apply (ge_gfarr_keep cx fp W3 [] ms3 ms4 GO_SET _ KC3); [unfold GO_SET; lia | rewrite LST, Hfb; unfold GO_SET; lia | exact HST].
  + exact HH.
  + exact HI1.
  + exact (eq_trans (RK 20%bv 20 ltac:(unfold acallee_saved; lia) eq_refl P20) R20).
  + exact (eq_trans (RK 21%bv 21 ltac:(unfold acallee_saved; lia) eq_refl P21) R21).
  + (* s8, the scene's width: 0 with at most one byte left *)
    refine (eq_trans (X 24%bv 24 ltac:(unfold acallee_saved; lia) eq_refl) (eq_trans A24 _)).
    rewrite Hb1. reflexivity.
  + (* s7, the bytes left for the frame count: none *)
    refine (eq_trans (X 23%bv 23 ltac:(unfold acallee_saved; lia) eq_refl) (eq_trans A23 _)).
    rewrite Z.max_r by lia. reflexivity.
  + intros H6. lia.
  + exact (obj_gtab B cx ly3 S3 W3 ms4 t _ Htin Ht0 LT Hobj).
Qed.

End c.
End b.
End a.
