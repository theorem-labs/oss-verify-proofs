(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryRawRd1), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntryRawRd1.v. *)
(* Ported from lib/A/Prog/GrantEntryRawRd1.v of a working branch 7c8c67da870 (blob 5fbb8f96a04). *)
(* Case 1 of the head of the hand-built allocation phase of fuzz_grant's entry function
   LLVMFuzzerTestOneInput on image B (fuzz_grant.c:367-368): one byte of input is left. The
   slots 0x81824 .. 0x818b4, from GR_hd1I to GR_malI (LLVMFEntryRawDefs.v).

   `beqz s7` (0x81824) is not taken, as s7 = 1. a0 := s5 + 1; the UBSan check `bgeu a1,a0`
   (0x81830, a1 = 1) into the trap 0x81f48 is not taken, as s5 = c_p + pos_end >= 4096; the
   check of the input byte's shadow byte at (s5 >> 3) + slot 144 does not branch to its slow
   path (0x81f90); raw.base := the input byte (through s5 := slot 16); `bne s7, 1` (0x81858)
   is not taken; s7 := 0, raw.width := 0, slot 48 := a0 = c_p + pos_end + 1,
   a0 := 17 << 8 = 4352. The model reads the same: SegCLib.raw_rd_1 gives
   raw = (pbz pl pos_end, 0) and pos_raw = length pl, so slot 48 is c_p + pos_raw and
   s7 = 0 = c_n - pos_raw.

   The symbolic state is ss_r1 / SH_r1 of LLVMFEntryRawHeadLib.v. The run writes only slot 48
   and the two bytes of `raw`; hmem_tr carries the rest of the memory, and fin_mal gives
   GR_malI. *)
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
GrantBContracts LLVMFEntryDefs LLVMFEntrySetDefs LLVMFEntryRawDefs LLVMFEntryRawLib LLVMFEntryRawHeadLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c SegCLib SegSetModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* The value of a one-byte data word. *)
Lemma rd1_firstn1_skipn : forall {A} (l : list A) n b, nth_error l n = Some b -> firstn 1 (skipn n l) = [b].
Proof.
intros A l. induction l as [|x l IH]; intros n b H; destruct n as [|n]; cbn in H |- *; try discriminate.
- injection H as ->. reflexivity.
- apply IH. exact H.
Qed.

Lemma rd1_U_data1 : forall E i b, 0 <= i -> nth_error (ed E 0) (Z.to_nat i) = Some b -> U E (SData 0 i 1) = bv_unsigned b.
Proof.
intros E i b Hi Hb. unfold U. cbn [sv_denot]. unfold data_word.
change (N.to_nat 1) with 1%nat. rewrite (rd1_firstn1_skipn _ _ _ Hb), bytes_le_single.
apply unsigned_lit_small. pose proof (u8_range b). lia.
Qed.

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

Theorem seg_raw_rd1 : forall POST, ge_from B MT POST (GR_malI B MT) -> ge_from B MT POST (GR_hd1I B MT).
Proof.
intros POST HN cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO
  ((t & HBODY & Hk & Hacc & Hbl & Hn & R19 & R20 & R21 & R22 & R23 & S16 & S48 & SL & HTAB & HWS & HST
    & HREL & HI1) & Hlen1).
pose proof HBODY as (Pc & Prv & Psv & Pro & Pfr & Pfc & HGR & GSV & GSH & GFL & GLEN & GIN).
pose proof HGR as (G2 & G8 & G9 & G3 & G4).
pose proof HTAB as (HinT & Ht0 & HLT & HTB).
pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ HFR Hbl) as HL.
pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
pose proof (proj1 alloc_ceiling_val) as AC.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSP & _).
assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp HAR Hfin) as (_ & _ & HFb & _).
rewrite L6 in HFb. change (fs_frame_bytes GE_CID) with 1024 in HFb.
pose proof SL as (_ & _ & _ & _ & _ & _ & _ & _ & S144 & _).
(* ---- the model: one byte left ---- *)
assert (ERAW : GrantSlotPlan.raw_rd (c_pl cx) =
  (GrantSlotPlan.pbz (c_pl cx) (GrantSlotPlan.pos_end (c_pl cx)), 0, length (c_pl cx)))
  by exact (SegCLib.raw_rd_1 (c_pl cx) Hlen1).
assert (Erb : raw_b cx = GrantSlotPlan.pbz (c_pl cx) (GrantSlotPlan.pos_end (c_pl cx)))
  by (unfold raw_b; rewrite ERAW; reflexivity).
assert (Erw : raw_w cx = 0) by (unfold raw_w; rewrite ERAW; reflexivity).
assert (Epr : GrantSlotPlan.pos_raw (c_pl cx) = length (c_pl cx))
  by (unfold GrantSlotPlan.pos_raw; rewrite ERAW; reflexivity).
assert (Hcn : c_n cx = Z.of_nat (GrantSlotPlan.pos_end (c_pl cx)) + 1) by (unfold c_n; rewrite <- Hlen1; lia).
pose proof HB as (_ & _ & _ & Hpn & _).
destruct Hpn as [(Hn0 & _) | (Hn0 & Hin0)]; [lia|].
assert (HinP : In (c_p cx, c_n cx) (ablocks B ly3 S3))
  by (unfold gblk1 in Hbl; rewrite Hbl; apply in_or_app; left; exact Hin0).
destruct (L16 ltac:(lia)) as (P1 & P2 & P3 & P4 & P5).
remember (GrantSlotPlan.pos_end (c_pl cx)) as pe eqn:Epe.
remember (nth pe (c_pl cx) (Z_to_bv 8 0)) as b0 eqn:Eb0.
assert (Hbyte : mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_p cx + Z.of_nat pe) = Some b0)
  by (rewrite Eb0; apply (rh_in_byte _ _ _ _ GIN); lia).
assert (Hpbz : GrantSlotPlan.pbz (c_pl cx) pe = bv_unsigned b0) by (rewrite Eb0; reflexivity).
unfold gslot in S16, S48, S144.
(* ---- the symbolic state at 0x81824 ---- *)
rewrite (gmach_mkst cx ms3 GR_hd (conj Pc (conj Prv (conj Psv (conj Pro (conj Pfr (conj Pfc HGR))))))).
remember (ms_regs ms3) as regs eqn:Eregs.
remember (Eimg (edset (Ereg regs [w64 (gF cx fp + GO_RAW)]) 0 [b0])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (ER : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr regs r).
{ intros q r Hq. subst E. pose proof (u5_range r). rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs _ q r Hq). }
assert (E32 : ew E 32 = w64 (gF cx fp + GO_RAW)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (ED : ed E 0 = [b0]) by (subst E; reflexivity).
clear HE.
assert (E21 : ew E 21 = w64 (c_p cx + Z.of_nat pe)) by (rewrite (ER 21%nat 21%bv eq_refl); subst regs; exact R21).
assert (R23' : getr regs 23 = Z_to_bv 64 1) by (subst regs; rewrite R23; unfold w64; f_equal; lia).
assert (X9 : bv_unsigned (ew E 9) = c_sp1 cx)
  by (rewrite (ER 9%nat 9%bv eq_refl); subst regs; rewrite G9; unfold w64; apply unsigned_lit_small; lia).
assert (X21 : bv_unsigned (ew E 21) = c_p cx + Z.of_nat pe) by (rewrite E21; unfold w64; apply unsigned_lit_small; lia).
assert (X32 : bv_unsigned (ew E 32) = gF cx fp + GO_RAW)
  by (rewrite E32; unfold w64, GO_RAW; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ss_r1
  (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + GR_hd)) (ms_mem ms3) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_r1. apply pa_entry_st_ok_full.
  - apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
    repeat (destruct Hr as [<-|Hr];
      [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
          let v := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with v end;
        first [ rewrite getr_zero; reflexivity
              | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; apply ER; reflexivity
              | cbn [sv_denot]; exact R23' ]
      | ]).
    destruct Hr.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold region_ok, R_in. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite X21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      intros i Hi. cbn [c_len YP09.c_val YP09.c_off cv_len] in Hi |- *.
      assert (Ei : i = 0) by lia. subst i.
      exists b0. cbn [cbyte]. rewrite ED. split; [reflexivity|].
      rewrite !Z.add_0_r. exact Hbyte.
    + unfold region_ok, RH_stk. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite X9. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply HSP. unfold GE_STK, STK_LLVMFuzzerTestOneInput. lia.
      * apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
        -- apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 32 0) (gF cx fp + GO_RAW));
             [apply gsv0; [exact E32 | unfold GO_RAW; lia] | cbn; unfold GO_RAW; lia | cbn; lia |].
           exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S16).
        -- apply (chunk_ok_val SEGS E _ _ 48 8 (SOff 21 0) (c_p cx + Z.of_nat pe));
             [apply gsv0; [exact E21 | lia] | cbn; lia | cbn; lia |].
           exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S48).
        -- apply (chunk_ok_val SEGS E _ _ 144 8 (SLit GSB) SHADOW_OFF);
             [reflexivity | cbn; unfold SHADOW_OFF; lia | cbn; lia |].
           exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S144).
    + unfold region_ok, R_raw. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite X32. unfold GO_RAW. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFb (gF cx fp + 560 + o) ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, R_in, RH_stk, R_raw.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite X21, X9, X32. unfold GO_RAW. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, RH_SP, RH_PTR. cbn [af_lo af_hi af_al2].
    rewrite X9, X21, X32.
    try change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold GO_RAW. repeat split; lia. }
assert (UB : U E GBx = SHADOW_OFF) by (unfold GBx; rewrite U_SLit; vm_compute; reflexivity).
assert (SHOK : sh_ok SEGS GBx SH_r1 E (mrestrict (w_H W3) (ms_mem ms3))).
{ unfold sh_ok, SH_r1. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E GBx 21 (c_p cx + Z.of_nat pe) 1 (c_p cx + Z.of_nat pe) 0 1).
    + pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
      apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR HinP); lia.
    + exact UB.
    + apply U_atom; [exact E21 | lia].
    + lia.
    + lia.
    + intros x Hx. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
  - apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E GBx 32 (gF cx fp + GO_RAW) 2 (gF cx fp + GO_RAW) 0 2).
    + apply rh_raw_addressable; [exact L9 | lia |].
      pose proof (GSH 70%nat ltac:(rewrite GLEN; unfold GE_NSH; lia)) as H70.
      change (Z.of_nat 70) with 70 in H70. rewrite gsh_raw_70, L11 in H70. exact H70.
    + exact UB.
    + apply U_atom; [exact E32 | unfold GO_RAW; lia].
    + lia.
    + lia.
    + intros x Hx. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF, GO_RAW in *. lia. }
(* ---- 0x81824 .. 0x818b4: the run writes slot 48 and the two bytes of `raw` ---- *)
paj_run_to_tok RUNTO HS HJ SHOK GBspan GR_mal.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fp0 ?bl0 ?blc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fp0 bl0 blc ly own) end.
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
    [reflexivity | rewrite X9; lia | cbn [YP09.r_wlo]; unfold GE_STK, STK_LLVMFuzzerTestOneInput; lia | cbn [YP09.r_whi]; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat (gF cx fp + GO_RAW)); [reflexivity | exact X32 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right.
  exists GE_CID, fp. split; [left; reflexivity|]. left.
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite L6. change (fs_frame_bytes GE_CID) with 1024.
  unfold GO_RAW in Ha. lia. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
(* What the run kept: every byte outside slot 48 and `raw`. *)
assert (HKW : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 48 <= a < c_sp1 cx + 56) ->
   ~ (gF cx fp + GO_RAW <= a < gF cx fp + GO_RAW + 2) ->
   aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hs Hr.
  lazymatch goal with HFx : frame_of _ ?rs0 (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem msF)) |- _ =>
    apply (frame_wins _ rs0 (w_H W3) (ms_mem ms3) (ms_mem msF)
      (fun a => (c_sp1 cx + 48 <= a < c_sp1 cx + 56) \/ (gF cx fp + GO_RAW <= a < gF cx fp + GO_RAW + 2)) HFx);
    [| exact Ha | cbv beta; intros [Hx | Hx]; [exact (Hs Hx) | exact (Hr Hx)]] end.
  intros x (r & Hrin & Hx). cbv beta. try unfold ss_r1 in Hrin. cbn [ss_mem In] in Hrin.
  destruct Hrin as [<- | [<- | [<- | []]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val R_in RH_stk R_raw] in Hx.
  - lia.
  - left. rewrite X9 in Hx. lia.
  - right. rewrite X32 in Hx. lia. }
assert (HK : forall a, 0 <= a < 2 ^ 64 -> happ cx fp a ->
   aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a)
  by (intros a Ha (_ & Hs & Hr); exact (HKW a Ha Hs Hr)).
apply (HN cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO).
destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc' & Prv' & Psv' & Pro' & Pfr' & Pfc'). cbn [ss_pc] in Pc'.
assert (Q2 : getr (ms_regs msF) 2 = getr regs 2) by (prreg HS (2%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
assert (Q3 : getr (ms_regs msF) 3 = getr regs 3) by (prreg HS (3%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
assert (Q4 : getr (ms_regs msF) 4 = getr regs 4) by (prreg HS (4%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
assert (Q8 : getr (ms_regs msF) 8 = getr regs 8) by (prreg HS (8%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
assert (Q9 : getr (ms_regs msF) 9 = getr regs 9) by (prreg HS (9%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
assert (Q19 : getr (ms_regs msF) 19 = getr regs 19) by (prreg HS (19%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
assert (Q20 : getr (ms_regs msF) 20 = getr regs 20) by (prreg HS (20%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
assert (Q22 : getr (ms_regs msF) 22 = getr regs 22) by (prreg HS (22%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (10%bv : bv 5) Q10.
(* slot 48 and the two bytes of `raw`, as the run left them *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
  let rs := eval vm_compute in (nth 1 (ss_mem ssx) R_raw) in
  let rr := eval vm_compute in (nth 2 (ss_mem ssx) R_raw) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 1 rs HS ltac:(vm_compute; reflexivity)) as FR1;
  pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 2 rr HS ltac:(vm_compute; reflexivity)) as FR2
end.
cbn [ms_mem restrict] in FR1, FR2.
assert (D48 : sv_denot E (SOff 21 1) = Z_to_bv 64 (c_p cx + Z.of_nat pe + 1))
  by (cbn [sv_denot]; rewrite X21; reflexivity).
assert (B48 : 0 <= c_p cx + Z.of_nat pe + 1 < 2 ^ (8 * Z.of_N 8)) by (change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia).
assert (W8 : Z.of_N 8 <= 8) by (cbn; lia).
pose proof (field_of_regionG _ _ 9%nat (c_sp1 cx) _ _ _ _ _ 48 8%N (SOff 21 1) (c_p cx + Z.of_nat pe + 1)
  FR1 X9 ltac:(cbn; tauto) D48 B48 W8) as V48.
assert (DB0 : sv_denot E (SData 0 0 1) = Z_to_bv 64 (bv_unsigned b0)).
{ rewrite denot_lit_U, (rd1_U_data1 E 0 b0); [reflexivity | lia | rewrite ED; reflexivity]. }
assert (BB0 : 0 <= bv_unsigned b0 < 2 ^ (8 * Z.of_N 1)) by (pose proof (u8_range b0); change (2 ^ (8 * Z.of_N 1)) with 256; lia).
assert (W1 : Z.of_N 1 <= 8) by (cbn; lia).
pose proof (field_of_regionG _ _ 32%nat (gF cx fp + GO_RAW) _ _ _ _ _ 0 1%N (SData 0 0 1) (bv_unsigned b0)
  FR2 X32 ltac:(cbn; tauto) DB0 BB0 W1) as V0.
assert (DZ : sv_denot E (SLit 0) = Z_to_bv 64 0) by reflexivity.
assert (BZ : 0 <= 0 < 2 ^ (8 * Z.of_N 1)) by (change (2 ^ (8 * Z.of_N 1)) with 256; lia).
pose proof (field_of_regionG _ _ 32%nat (gF cx fp + GO_RAW) _ _ _ _ _ 1 1%N (SLit 0) 0
  FR2 X32 ltac:(cbn; tauto) DZ BZ W1) as V1.
change (N.to_nat 8) with 8%nat in V48. change (N.to_nat 1) with 1%nat in V0, V1.
subst regs.
(* ---- GR_malI at 0x818b4 ---- *)
assert (HM0 : hmem cx fp t W3 ms3)
  by exact (conj GSV (conj GFL (conj GIN (conj SL (conj HTB (conj HWS HST)))))).
pose proof (hmem_tr cx fp t ly3 W3 ms3 msF HL HK HM0) as HM1.
apply (fin_mal B MT cx fp k acc ly3 S3 W3 msF _ t).
- unfold gmach, gregs. splits;
    first [ exact Pc' | exact Prv' | exact Psv' | exact Pro' | exact Pfr' | exact Pfc'
          | (rewrite Q2; exact G2) | (rewrite Q8; exact G8) | (rewrite Q9; exact G9)
          | (rewrite Q3; exact G3) | (rewrite Q4; exact G4) ].
- exact Hk.
- exact Hacc.
- exact Hbl.
- exact HinT.
- exact Ht0.
- exact HLT.
- exact Hn.
- intros i Hi. rewrite gsh_raw_len in Hi. unfold GE_NSH in Hi.
  pose proof (gshadow_band cx fp t ly3 (Z.of_nat i) HL ltac:(lia)) as (S1 & S2 & S3').
  rewrite HKW; [apply GSH; rewrite GLEN; unfold GE_NSH; lia | | |];
    unfold kLowShadowBeg, kHighMemBeg, GO_RAW in *; lia.
- exact HM1.
- rewrite Q19. exact R19.
- rewrite Q20. exact R20.
- rewrite Q21, E32. reflexivity.
- rewrite Q22. exact R22.
- rewrite Q23, Epr. unfold c_n. rewrite Z.sub_diag. reflexivity.
- rewrite Q10. reflexivity.
- unfold gslot. rewrite Epr.
  replace (c_p cx + Z.of_nat (length (c_pl cx))) with (c_p cx + Z.of_nat pe + 1) by lia.
  apply rdword_of_val_mem; [exact V48 | lia].
- unfold gfb. rewrite Erb, Hpbz. apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem msF)).
  rewrite Z.add_0_r in V0. exact V0.
  pose proof (u8_range b0). lia.
- unfold gfb. rewrite Erw. apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem msF)); [|lia].
  rewrite Z.add_assoc. exact V1.
- exact HREL.
- exact HI1.
Qed.

End c.
End b.
End a.
