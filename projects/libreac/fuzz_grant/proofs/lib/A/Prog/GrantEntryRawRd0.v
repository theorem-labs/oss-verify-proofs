(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryRawRd1), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryRawRd1.v; 144 of its 181 lines of code are new or changed and 221 lines of the source are left out. *)
(* The case of the head of the hand-built allocation phase of LLVMFuzzerTestOneInput on the
   ASan build where no byte of input is left (fuzz_grant.c:367-368): the slots
   0x812b4 .. 0x81328, from GR_hd0I (GR_hd) to GR_malI (GR_mal).

   s8 (the bytes of input left) is 0, so `beqz s8` at 0x812b4 is taken to 0x812ec:
   `li a1,0; sb zero,0(s9); j 8131c; sb a1,1(s9)` stores 0 into raw.base and raw.width
   (s9 = this function's frame + GO_RAW: two bytes the frame owns), and
   `li a0,17; slli a0,a0,8` sets a0 = 4352 for the call of malloc at 0x81328. The model
   agrees: SegCLib.raw_rd_0 gives raw_rd = (0, 0, pos_end), so raw_b = raw_w = 0 and
   pos_raw = pos_end; slot 88 and s8 are not written, and still hold c_p + pos_raw and
   c_n - pos_raw.

   The run is on the engine with shadow tokens, from ss_r0 / SH_r0 (GrantEntryRawHeadLib.v);
   no byte this path reads or writes has a shadow check. The two bytes of raw are read back
   from the region on atom 25 (field_of_regionG), the memory outside them is unchanged
   (frame_wins), hmem_tr carries the kept memory and fin_mal gives GR_malI. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YC5d YM05 YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1g YC45 YC88 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryDefs GrantEntryRawDefs GrantEntrySetDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryRawHeadLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c SegCLib SegSetModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The region of raw after the run: both bytes are 0. *)
Definition R_raw0 : YP09.region :=
  YP09.mkRegion (Some 25%nat) 0 2 0 2 [YP09.mkChunk 1 (CVal 1 (SLit 0)); YP09.mkChunk 0 (CVal 1 (SLit 0))].

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

(* ---- 0x812b4 .. 0x81328: no byte of input left ---- *)
Theorem seg_raw_rd0 : forall POST, ge_from B MT POST (GR_malI B MT) -> ge_from B MT POST (GR_hd0I B MT).
Proof.
  intros POST HN cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO
    ((t & HBODY & Hk & Hacc & Hbl & Hn & R20 & R21 & R22 & R24 & R25 & S88 & SL & HTAB & HWS & HST & HREL & HI1) & HE0).
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
  assert (N24 : c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx)) = 0) by (unfold c_n; rewrite HE0; lia).
  assert (HM0 : hmem cx fp t W3 ms3) by exact (conj HSV (conj HFL (conj HIN (conj SL (conj HTB (conj HWS HST)))))).
  assert (HMA : gmach cx ms3 GR_hd) by exact (conj Hpc (conj Hrv (conj Hsv (conj Hrom (conj Hfr (conj Hfc HG)))))).
  pose proof HG as (G2 & G8 & G9 & G3 & G4).
  rewrite (gmach_mkst cx ms3 _ HMA).
  remember (ms_regs ms3) as regs eqn:Eregs. remember (ms_mem ms3) as mem eqn:Emem.
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hr; subst E; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (E21 : ew E 21 = w64 SHADOW_OFF) by (rewrite (ER 21%nat 21%bv eq_refl); subst regs; exact R21).
  assert (E25 : ew E 25 = w64 (gF cx fp + GO_RAW)) by (rewrite (ER 25%nat 25%bv eq_refl); subst regs; exact R25).
  (* the symbolic state at 0x812b4: raw on atom 25, s8 = 0 *)
  assert (HS0 : st_ok_pi SEGS VAL E (mkSS GR_hd sr_atoms [R_raw] None (ss_facts ss_r0))
                  (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + GR_hd)) mem (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      unfold region_ok, R_raw. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E25. unfold w64. rewrite unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). subst mem.
      apply (proj1 (HFb (gF cx fp + GO_RAW + o) ltac:(lia))).
    - split; exact I.
    - unfold ss_r0, RH_SB, RH_PTR. cbn [ss_facts]. split; [|split; exact I].
      cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E21, E25. unfold w64. rewrite !unsigned_lit_small by (try unfold SHADOW_OFF; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. splits; first [exact I | lia | gshow; fail]. }
  assert (HS : st_ok_pi SEGS VAL E ss_r0
                 (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + GR_hd)) mem (seg_rom SEGS)))).
  { apply (st_ok_pi_set_reg E _ _ (24%bv : bv 5) (SLit 0) HS0); [discriminate|].
    cbn [ms_regs restrict mkst]. subst regs. rewrite R24, N24. reflexivity. }
  clear HS0.
  (* raw is marked usable: shadow byte 70 of the frame is 2 *)
  assert (SHOK : sh_ok SEGS RH_Bx SH_r0 E (mrestrict (w_H W3) mem)).
  { unfold sh_ok, SH_r0. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W3) mem E RH_Bx 25%nat (gF cx fp + GO_RAW) 2 (gF cx fp + GO_RAW) 0 2).
    - subst mem. apply rh_raw_addressable; [exact L9 | lia |].
      pose proof (HSH 70%nat ltac:(rewrite HLEN; unfold GE_NSH; lia)) as H70.
      rewrite gsh_raw_70, L11 in H70. change (Z.of_nat 70) with 70 in H70. exact H70.
    - unfold RH_Bx. apply U_atom; [exact E21 | unfold SHADOW_OFF; lia].
    - apply U_atom; [exact E25 | lia].
    - lia.
    - lia.
    - intros x Hx. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
  clear HE. subst mem.
  paj_run_to_tok RUNTO HS HJ SHOK RH_Bspan GR_mal.
  - (* the run writes the two bytes of raw, which the frame owns *)
    try change (ss_mem ss_r0) with [R_raw].
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 25%nat (gF cx fp + GO_RAW));
      [reflexivity | rewrite E25; unfold w64; apply unsigned_lit_small; lia | | apply awr_ok_nil].
    intros a Ha. right; right; right. exists GE_CID, fp. split; [left; reflexivity|]. left.
    unfold in_zr; cbn [fst snd YP09.r_wlo YP09.r_whi R_raw] in Ha |- *. rewrite L6.
    change (fs_frame_bytes GE_CID) with 1024. lia.
  - (* at 0x81328 *)
    let msF := rh_cur HS in
    assert (HWIN : forall a, 0 <= a < 2 ^ 64 -> ~ (gF cx fp + GO_RAW <= a < gF cx fp + GO_RAW + 2) ->
                   aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a);
    [ intros a Ha Hw;
      match goal with HFr : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem msF)) |- _ =>
        apply (frame_wins E _ _ _ _ (fun a => gF cx fp + GO_RAW <= a < gF cx fp + GO_RAW + 2) HFr); [|exact Ha | exact Hw] end;
      intros x (r & Hr & Hx); cbn [ss_mem ss_r0 In] in Hr;
      destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val R_raw] in Hx;
      rewrite E25 in Hx; unfold w64 in Hx; rewrite unsigned_lit_small in Hx by lia; lia
    | apply (HN cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO) ].
    destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
    prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
    prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10.
    prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
    prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
    rewrite (ER 2%nat 2%bv eq_refl) in Q2. rewrite (ER 8%nat 8%bv eq_refl) in Q8. rewrite (ER 9%nat 9%bv eq_refl) in Q9.
    rewrite (ER 3%nat 3%bv eq_refl) in Q3. rewrite (ER 4%nat 4%bv eq_refl) in Q4.
    rewrite (ER 20%nat 20%bv eq_refl) in Q20. rewrite (ER 21%nat 21%bv eq_refl) in Q21.
    rewrite (ER 22%nat 22%bv eq_refl) in Q22. rewrite (ER 25%nat 25%bv eq_refl) in Q25.
    (* the two bytes of raw, read back from the region on atom 25 *)
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
      pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 0 R_raw0 HS ltac:(vm_compute; reflexivity)) as FR0
    end.
    cbn [ms_mem restrict] in FR0. unfold R_raw0 in FR0.
    assert (X25 : bv_unsigned (ew E 25) = gF cx fp + GO_RAW)
      by (rewrite E25; unfold w64; apply unsigned_lit_small; lia).
    let msF := rh_cur HS in
    assert (N0 : aview SEGS (w_H W3) (ms_mem msF) (gF cx fp + GO_RAW) = Some 0);
    [ replace (gF cx fp + GO_RAW) with (gF cx fp + GO_RAW + 0) by lia;
      apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem msF)); [|lia];
      exact (field_of_regionG _ _ 25%nat (gF cx fp + GO_RAW) _ _ _ _ _ 0 1%N (SLit 0) 0 FR0 X25
               ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))
    | ].
    let msF := rh_cur HS in
    assert (N1 : aview SEGS (w_H W3) (ms_mem msF) (gF cx fp + (GO_RAW + 1)) = Some 0);
    [ rewrite Z.add_assoc;
      apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem msF)); [|lia];
      exact (field_of_regionG _ _ 25%nat (gF cx fp + GO_RAW) _ _ _ _ _ 1 1%N (SLit 0) 0 FR0 X25
               ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))
    | ].
    subst regs.
    (* the facts GR_malI asks for *)
    let msF := rh_cur HS in
    assert (HMF : gmach cx msF GR_mal) by (unfold gmach, gregs, GR_mal; splits; first [exact Pc | assumption | congruence]).
    let msF := rh_cur HS in
    assert (HSHF : gshadow cx fp W3 msF GSH_raw);
    [ intros i Hi; pose proof Hi as Hi'; rewrite gsh_raw_len in Hi'; unfold GE_NSH in Hi';
      pose proof (gshadow_band cx fp t ly3 (Z.of_nat i) HL ltac:(lia)) as (B1 & B2 & B3);
      rewrite HWIN; [exact (HSH i Hi) | unfold kLowShadowBeg, kHighMemBeg in *; lia | unfold kLowShadowBeg, kHighMemBeg in *; lia]
    | ].
    let msF := rh_cur HS in
    assert (HMF2 : hmem cx fp t W3 msF)
      by (apply (hmem_tr cx fp t ly3 W3 ms3 msF HL); [intros a Ha (_ & _ & Hr); exact (HWIN a Ha Hr) | exact HM0]).
    let msF := rh_cur HS in
    assert (S88F : gslot cx W3 msF 88 (c_p cx + Z.of_nat (GrantSlotPlan.pos_raw (c_pl cx))));
    [ rewrite EPR; unfold gslot in *;
      rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms3)) _ (c_sp1 cx + 88)); [exact S88|];
      intros j Hj; apply HWIN; lia
    | ].
    let msF := rh_cur HS in
    assert (B0F : gfb cx fp W3 msF GO_RAW (raw_b cx)) by (unfold gfb; rewrite RB0; exact N0).
    let msF := rh_cur HS in
    assert (B1F : gfb cx fp W3 msF (GO_RAW + 1) (raw_w cx)) by (unfold gfb; rewrite RW0; exact N1).
    apply (fin_mal B MT cx fp k acc ly3 S3 W3 _ _ t HMF Hk Hacc Hbl HinT Ht0 HLT Hn HSHF HMF2);
      [ congruence | congruence | congruence
      | rewrite EPR, N24, Q24; reflexivity
      | congruence
      | rewrite Q10; reflexivity
      | exact S88F | exact B0F | exact B1F | exact HREL | exact HI1 ].
Qed.

End c.
End b.
End a.
