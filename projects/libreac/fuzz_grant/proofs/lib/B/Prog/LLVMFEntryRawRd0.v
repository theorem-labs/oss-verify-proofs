(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: image-B walk segment; lines 192-198 follow the shape of cgif_file_fuzzer lib/A/ACgb.v:547 (licscan run). *)
(* Ported from lib/A/Prog/GrantEntryRawRd0.v of a working branch 7c8c67da870 (blob 6a899525174). *)
(* Case 0 of the head of the hand-built allocation phase of LLVMFuzzerTestOneInput on image B
   (fuzz_grant.c:367-368): no byte of input is left. The slots 0x81824 .. 0x818b4, from
   GR_hd0I to GR_malI (LLVMFEntryRawDefs.v).

   `beqz s7` (0x81824) is taken, as s7 = 0, to 0x81868: a1 := 0, s5 := slot 16 (&raw),
   raw.base := 0, `j 0x818a8`, raw.width := a1 = 0, a0 := 17 << 8 = 4352. No input byte is
   read and no slot is written. The model reads the same: SegCLib.raw_rd_0 gives raw = (0, 0)
   and pos_raw = pos_end.

   The symbolic state is ss_r0 / SH_r0 of LLVMFEntryRawHeadLib.v: slot 16 in the stack window
   at s1, `raw` atom 32. The run writes only the two bytes of `raw`; hmem_tr carries the rest
   of the memory, and fin_mal gives GR_malI. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib YC1g YC45 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
LLVMFEntryDefs LLVMFEntrySetDefs LLVMFEntryRawDefs LLVMFEntryRawLib LLVMFEntryRawHeadLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c SegCLib SegSetModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section b. Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Let RUNTO := paj_run_to B LAWS.

(* ---- 0x81824 .. 0x818b4: no byte of input left ---- *)
Theorem seg_raw_rd0 : forall POST, ge_from B MT POST (GR_malI B MT) -> ge_from B MT POST (GR_hd0I B MT).
Proof.
  intros POST HN cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO
    ((t & HBODY & Hk & Hacc & Hbl & Hn & R19 & R20 & R21 & R22 & R23 & S16 & S48 & SL & HTAB & HWS & HST
      & HREL & HI1) & HE0).
  pose proof HBODY as (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & HG & HSV & HSH & HFL & HLEN & HIN).
  pose proof HTAB as (HinT & Ht0 & HLT & HTB).
  pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ HFR Hbl) as HL.
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
  pose proof (proj1 alloc_ceiling_val) as AC.
  assert (HGR : GO_RAW = 560) by reflexivity.
  pose proof (proj1 HJ) as HAR.
  assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp HAR Hfin) as (_ & _ & HFb & _).
  rewrite L6 in HFb. change (fs_frame_bytes GE_CID) with 1024 in HFb.
  (* the model: no byte left, so raw = (0, 0) and the position does not move *)
  pose proof (SegCLib.raw_rd_0 (c_pl cx) HE0) as HRD.
  assert (EPR : GrantSlotPlan.pos_raw (c_pl cx) = GrantSlotPlan.pos_end (c_pl cx))
    by (unfold GrantSlotPlan.pos_raw; rewrite HRD; reflexivity).
  assert (RB0 : raw_b cx = 0) by (unfold raw_b; rewrite HRD; reflexivity).
  assert (RW0 : raw_w cx = 0) by (unfold raw_w; rewrite HRD; reflexivity).
  assert (N23 : c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx)) = 0) by (unfold c_n; rewrite HE0; lia).
  assert (HM0 : hmem cx fp t W3 ms3) by exact (conj HSV (conj HFL (conj HIN (conj SL (conj HTB (conj HWS HST)))))).
  assert (HMA : gmach cx ms3 GR_hd) by exact (conj Hpc (conj Hrv (conj Hsv (conj Hrom (conj Hfr (conj Hfc HG)))))).
  pose proof HG as (G2 & G8 & G9 & G3 & G4).
  rewrite (gmach_mkst cx ms3 _ HMA).
  remember (ms_regs ms3) as regs eqn:Eregs.
  remember (Eimg (Ereg regs [w64 (gF cx fp + GO_RAW)])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (ER : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr regs r).
  { intros q r Hq. subst E. pose proof (u5_range r). rewrite Eimg_low by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat regs _ q r Hq). }
  assert (E32 : ew E 32 = w64 (gF cx fp + GO_RAW)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
  assert (HSR : regs_ok E sr_atoms regs) by (subst E; apply regs_ok_Eimg_Ereg).
  clear HE.
  assert (X9 : bv_unsigned (ew E 9) = c_sp1 cx)
    by (rewrite (ER 9%nat 9%bv eq_refl); subst regs; rewrite G9; unfold w64; apply unsigned_lit_small; lia).
  assert (X32 : bv_unsigned (ew E 32) = gF cx fp + GO_RAW)
    by (rewrite E32; unfold w64, GO_RAW; apply unsigned_lit_small; lia).
  (* the symbolic state at 0x81824: slot 16 at s1, raw on atom 32, s7 = 0 *)
  assert (HS0 : st_ok_pi SEGS VAL E (mkSS GR_hd sr_atoms [RH_stk0; R_raw] None (ss_facts ss_r0))
                  (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + GR_hd)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - exact HSR.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + unfold region_ok, RH_stk0.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite X9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (c_sp1 cx) 16 8 (SOff 32 0) (gF cx fp + GO_RAW));
          [apply gsv0; [exact E32 | unfold GO_RAW; lia] | cbn; unfold GO_RAW; lia | cbn; lia |].
        exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S16).
      + unfold region_ok, R_raw.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite X32. unfold GO_RAW. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
        intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFb (gF cx fp + 560 + o) ltac:(lia))).
    - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, RH_stk0, R_raw.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite X9, X32. unfold GO_RAW. repeat split; lia.
    - split; [|split; exact I]. cbn [ss_facts ss_r0 f_atoms atoms_ok]. unfold afact_ok, RH_SP, RH_PTR.
      cbn [af_lo af_hi af_al2]. rewrite X9, X32.
      try change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold GO_RAW. repeat split; lia. }
  assert (HS : st_ok_pi SEGS VAL E ss_r0
                 (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + GR_hd)) (ms_mem ms3) (seg_rom SEGS)))).
  { apply (st_ok_pi_set_reg E _ _ (23%bv : bv 5) (SLit 0) HS0); [discriminate|].
    cbn [ms_regs restrict mkst]. subst regs. rewrite R23, N23. reflexivity. }
  clear HS0.
  (* raw is marked usable: shadow byte 70 of the frame is 2 *)
  assert (UB : U E GBx = SHADOW_OFF) by (unfold GBx; rewrite U_SLit; vm_compute; reflexivity).
  assert (SHOK : sh_ok SEGS GBx SH_r0 E (mrestrict (w_H W3) (ms_mem ms3))).
  { unfold sh_ok, SH_r0. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E GBx 32%nat (gF cx fp + GO_RAW) 2 (gF cx fp + GO_RAW) 0 2).
    - apply rh_raw_addressable; [exact L9 | lia |].
      pose proof (HSH 70%nat ltac:(rewrite HLEN; unfold GE_NSH; lia)) as H70.
      rewrite gsh_raw_70, L11 in H70. change (Z.of_nat 70) with 70 in H70. exact H70.
    - exact UB.
    - apply U_atom; [exact E32 | unfold GO_RAW; lia].
    - lia.
    - lia.
    - intros x Hx. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF, GO_RAW in *. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK GBspan GR_mal.
  - (* the run writes the two bytes of raw, which the frame owns *)
    lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fp0 ?bl0 ?blc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fp0 bl0 blc ly own) end.
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat (gF cx fp + GO_RAW)); [reflexivity | exact X32 | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists GE_CID, fp. split; [left; reflexivity|]. left.
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite L6.
    change (fs_frame_bytes GE_CID) with 1024. unfold GO_RAW in *. lia.
  - (* at 0x818b4 *)
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
    assert (HWIN : forall a, 0 <= a < 2 ^ 64 -> ~ (gF cx fp + GO_RAW <= a < gF cx fp + GO_RAW + 2) ->
                   aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha Hw.
      lazymatch goal with HFx : frame_of _ ?rs0 (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem msF)) |- _ =>
        apply (frame_wins _ rs0 (w_H W3) (ms_mem ms3) (ms_mem msF)
          (fun x => gF cx fp + GO_RAW <= x < gF cx fp + GO_RAW + 2) HFx); [| exact Ha | exact Hw]
      end.
      intros x (r & Hr & Hx). cbv beta. try unfold ss_r0 in Hr. cbn [ss_mem In] in Hr.
      destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val RH_stk0 R_raw] in Hx;
        rewrite ?X9, ?X32 in Hx; lia. }
    apply (HN cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO).
    destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
    assert (Q2 : getr (ms_regs msF) 2 = getr regs 2) by (prreg HS (2%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
    assert (Q3 : getr (ms_regs msF) 3 = getr regs 3) by (prreg HS (3%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
    assert (Q4 : getr (ms_regs msF) 4 = getr regs 4) by (prreg HS (4%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
    assert (Q8 : getr (ms_regs msF) 8 = getr regs 8) by (prreg HS (8%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
    assert (Q9 : getr (ms_regs msF) 9 = getr regs 9) by (prreg HS (9%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
    assert (Q19 : getr (ms_regs msF) 19 = getr regs 19) by (prreg HS (19%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
    assert (Q20 : getr (ms_regs msF) 20 = getr regs 20) by (prreg HS (20%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
    assert (Q22 : getr (ms_regs msF) 22 = getr regs 22) by (prreg HS (22%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
    prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (10%bv : bv 5) Q10.
    (* the two bytes of raw, read back from the region on atom 32 *)
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
      let rr := eval vm_compute in (nth 1 (ss_mem ssx) R_raw) in
      pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 1 rr HS ltac:(vm_compute; reflexivity)) as FRAW
    end.
    cbn [ms_mem restrict] in FRAW.
    assert (DZ : sv_denot E (SLit 0) = Z_to_bv 64 0) by reflexivity.
    assert (BZ : 0 <= 0 < 2 ^ (8 * Z.of_N 1)) by (change (2 ^ (8 * Z.of_N 1)) with 256; lia).
    assert (W1 : Z.of_N 1 <= 8) by (cbn; lia).
    pose proof (field_of_regionG _ _ 32%nat (gF cx fp + GO_RAW) _ _ _ _ _ 0 1%N (SLit 0) 0
      FRAW X32 ltac:(cbn; tauto) DZ BZ W1) as V0.
    pose proof (field_of_regionG _ _ 32%nat (gF cx fp + GO_RAW) _ _ _ _ _ 1 1%N (SLit 0) 0
      FRAW X32 ltac:(cbn; tauto) DZ BZ W1) as V1.
    change (N.to_nat 1) with 1%nat in V0, V1.
    subst regs.
    apply (fin_mal B MT cx fp k acc ly3 S3 W3 msF _ t).
    + unfold gmach, gregs. splits;
        first [ exact Pc | exact Prv | exact Psv | exact Pro | exact Pfr | exact Pfc
              | (rewrite Q2; exact G2) | (rewrite Q8; exact G8) | (rewrite Q9; exact G9)
              | (rewrite Q3; exact G3) | (rewrite Q4; exact G4) ].
    + exact Hk.
    + exact Hacc.
    + exact Hbl.
    + exact HinT.
    + exact Ht0.
    + exact HLT.
    + exact Hn.
    + intros i Hi. pose proof Hi as Hi'. rewrite HLEN in Hi'. unfold GE_NSH in Hi'.
      assert (Hiz : 0 <= Z.of_nat i < 104) by lia.
      destruct (gshadow_band cx fp t ly3 (Z.of_nat i) HL Hiz) as (B1 & B2 & B3).
      rewrite HWIN; [exact (HSH i Hi) | | ]; unfold kLowShadowBeg, kHighMemBeg, GO_RAW in *; lia.
    + apply (hmem_tr cx fp t ly3 W3 ms3 msF HL); [|exact HM0].
      intros a Ha (_ & _ & Hb2). exact (HWIN a Ha Hb2).
    + rewrite Q19. exact R19.
    + rewrite Q20. exact R20.
    + rewrite Q21, E32. reflexivity.
    + rewrite Q22. exact R22.
    + rewrite Q23, EPR, N23. reflexivity.
    + rewrite Q10. reflexivity.
    + unfold gslot in *. rewrite EPR.
      rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms3)) _ (c_sp1 cx + 48)); [exact S48|].
      intros j Hj. apply HWIN; [lia|]. unfold GO_RAW. lia.
    + unfold gfb. rewrite RB0. apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem msF)); [|lia].
      replace (gF cx fp + GO_RAW) with (gF cx fp + GO_RAW + 0) by lia. exact V0.
    + unfold gfb. rewrite RW0. apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem msF)); [|lia].
      rewrite Z.add_assoc. exact V1.
    + exact HREL.
    + exact HI1.
Qed.

End c.
End b.
End a.
