(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryRawRd1), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v. *)
(* Case 1 of the head of the hand-built allocation phase of fuzz_grant's entry function
   LLVMFuzzerTestOneInput on the ASan build (fuzz_grant.c:367-368): one byte of input is
   left. The slots 0x812b4 .. 0x81328, from GR_hd1I to GR_malI (GrantEntryRawDefs.v).

   `beqz s8` (0x812b4) is not taken, as s8 = 1. a0 := slot 88 (c_p + pos_end); the check of
   the input byte's shadow byte at (a0 >> 3) + s5 does not branch to its slow path
   (0x81a3c); raw.base := the input byte; `bne s8, 1` (0x812dc) is not taken; s8 := 0,
   raw.width := 0, slot 88 := a0 + 1, a0 := 17 << 8 = 4352. The model reads the same:
   SegCLib.raw_rd_1 gives raw = (pbz pl pos_end, 0) and pos_raw = length pl, so slot 88 is
   c_p + pos_raw and s8 = 0 = c_n - pos_raw.

   The symbolic state is ss_r1 / SH_r1 of GrantEntryRawHeadLib.v: the input byte is data
   slot 0 of the environment at atom 32 (c_p + pos_end), slot 88 is in the stack window at
   s1, `raw` is atom 25. The run writes only slot 88 and the two bytes of `raw`; hmem_tr
   carries the rest of the memory, and fin_mal gives GR_malI. *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
GrantEntryDefs GrantEntryRawDefs GrantEntrySetDefs GrantEntryRawHeadLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c SegCLib SegSetModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The value of a one-byte data word (GrantEntrySweepS2.v, U_data1, on a working branch). *)
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
  ((t & HBODY & Hk & Hacc & Hbl & Hn & R20 & R21 & R22 & R24 & R25 & S88 & SL & HTAB & HWS & HST & HREL & HI1) & Hlen1).
pose proof HBODY as (Pc & Prv & Psv & Pro & Pfr & Pfc & HGR & GSV & GSH & GFL & GLEN & GIN).
pose proof HGR as (G2 & G8 & G9 & G3 & G4).
pose proof HTAB as (HinT & Ht0 & HLT & HTB).
pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ HFR Hbl) as HL.
pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
pose proof (proj1 alloc_ceiling_val) as AC.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSP & _).
assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp HAR Hfin) as (_ & _ & HFb & _).
rewrite L6 in HFb. change (fs_frame_bytes GE_CID) with 1024 in HFb.
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
unfold gslot in S88.
(* ---- the symbolic state at 0x812b4 ---- *)
rewrite (gmach_mkst cx ms3 GR_hd (conj Pc (conj Prv (conj Psv (conj Pro (conj Pfr (conj Pfc HGR))))))).
remember (ms_regs ms3) as regs eqn:Eregs.
remember (Eimg (edset (Ereg regs [w64 (c_p cx + Z.of_nat pe)]) 0 [b0])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (ER : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr regs r).
{ intros q r Hq. subst E. pose proof (u5_range r). rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs _ q r Hq). }
assert (E32 : ew E 32 = w64 (c_p cx + Z.of_nat pe)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (ED : ed E 0 = [b0]) by (subst E; reflexivity).
clear HE.
assert (E9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); exact G9).
assert (E21 : ew E 21 = w64 SHADOW_OFF) by (rewrite (ER 21%nat 21%bv eq_refl); exact R21).
assert (E25 : ew E 25 = w64 (gF cx fp + GO_RAW)) by (rewrite (ER 25%nat 25%bv eq_refl); exact R25).
assert (R24' : getr regs 24 = Z_to_bv 64 1) by (rewrite R24; unfold w64; f_equal; lia).
assert (X9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (X25 : bv_unsigned (ew E 25) = gF cx fp + GO_RAW)
  by (rewrite E25; unfold w64, GO_RAW; apply unsigned_lit_small; lia).
assert (X32 : bv_unsigned (ew E 32) = c_p cx + Z.of_nat pe) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ss_r1
  (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + GR_hd)) (ms_mem ms3) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_r1. apply pa_entry_st_ok_full.
  - apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
    repeat (destruct Hr as [<-|Hr];
      [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
          let v := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with v end;
        first [ rewrite getr_zero; reflexivity
              | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; apply ER; reflexivity
              | cbn [sv_denot]; exact R24' ]
      | ]).
    destruct Hr.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold region_ok, R_in. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite X32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      intros i Hi. cbn [c_len YP09.c_val YP09.c_off cv_len] in Hi |- *.
      assert (Ei : i = 0) by lia. subst i.
      exists b0. cbn [cbyte]. rewrite ED. split; [reflexivity|].
      rewrite !Z.add_0_r. exact Hbyte.
    + unfold region_ok, R_s88. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite X9. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply HSP. unfold GE_STK. lia.
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ _ 88 8 (SOff 32 0) (c_p cx + Z.of_nat pe));
          [apply gsv0; [exact E32 | lia] | cbn; lia | cbn; lia |].
        exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S88).
    + unfold region_ok, R_raw. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite X25. unfold GO_RAW. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFb (gF cx fp + 560 + o) ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, R_in, R_s88, R_raw.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite X32, X9, X25. unfold GO_RAW. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, RH_SP, RH_SB, RH_PTR. cbn [af_lo af_hi af_al2].
    rewrite X9, X25, X32. rewrite E21. unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
    try change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold GO_RAW, SHADOW_OFF. repeat split; lia. }
assert (SHOK : sh_ok SEGS RH_Bx SH_r1 E (mrestrict (w_H W3) (ms_mem ms3))).
{ unfold sh_ok, SH_r1. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E RH_Bx 32 (c_p cx + Z.of_nat pe) 1 (c_p cx + Z.of_nat pe) 0 1).
    + pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
      apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR HinP); lia.
    + unfold RH_Bx. apply U_atom; [exact E21 | unfold SHADOW_OFF; lia].
    + apply U_atom; [exact E32 | lia].
    + lia.
    + lia.
    + intros x Hx. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
  - apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E RH_Bx 25 (gF cx fp + GO_RAW) 2 (gF cx fp + GO_RAW) 0 2).
    + apply rh_raw_addressable; [exact L9 | lia |].
      pose proof (GSH 70%nat ltac:(rewrite GLEN; unfold GE_NSH; lia)) as H70.
      change (Z.of_nat 70) with 70 in H70. rewrite gsh_raw_70, L11 in H70. exact H70.
    + unfold RH_Bx. apply U_atom; [exact E21 | unfold SHADOW_OFF; lia].
    + apply U_atom; [exact E25 | unfold GO_RAW; lia].
    + lia.
    + lia.
    + intros x Hx. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF, GO_RAW in *. lia. }
(* ---- 0x812b4 .. 0x81328: the run writes slot 88 and the two bytes of `raw` ---- *)
paj_run_to_tok RUNTO HS HJ SHOK RH_Bspan GR_mal.
{ change (ss_mem ss_r1) with [R_in 1; R_s88; R_raw].
  apply awr_ok_cons_ro; [unfold R_in; cbn; lia|].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
    [reflexivity | rewrite X9; lia | cbn [YP09.r_wlo R_s88]; unfold GE_STK; lia | cbn [YP09.r_whi R_s88]; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 25%nat (gF cx fp + GO_RAW)); [reflexivity | exact X25 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi R_raw] in Ha. right; right; right.
  exists GE_CID, fp. split; [left; reflexivity|]. left.
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite L6. change (fs_frame_bytes GE_CID) with 1024.
  unfold GO_RAW in Ha. lia. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
(* What the run kept: every byte outside slot 88 and `raw`. *)
assert (HKW : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 88 <= a < c_sp1 cx + 96) ->
   ~ (gF cx fp + GO_RAW <= a < gF cx fp + GO_RAW + 2) ->
   aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hs Hr.
  match goal with HFr : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem msF)) |- _ =>
    apply (frame_wins E _ _ _ _
      (fun a => (c_sp1 cx + 88 <= a < c_sp1 cx + 96) \/ (gF cx fp + GO_RAW <= a < gF cx fp + GO_RAW + 2)) HFr);
    [| exact Ha | cbv beta; intros [Hx | Hx]; [exact (Hs Hx) | exact (Hr Hx)]] end.
  intros x (r & Hrin & Hx). cbv beta. cbn [ss_mem ss_r1 In] in Hrin.
  destruct Hrin as [<- | [<- | [<- | []]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val R_in R_s88 R_raw] in Hx.
  - lia.
  - left. rewrite X9 in Hx. lia.
  - right. rewrite X25 in Hx. lia. }
assert (HK : forall a, 0 <= a < 2 ^ 64 -> happ cx fp a ->
   aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a)
  by (intros a Ha (_ & Hs & Hr); exact (HKW a Ha Hs Hr)).
apply (HN cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO).
destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc' & Prv' & Psv' & Pro' & Pfr' & Pfc'). cbn [ss_pc] in Pc'.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (10%bv : bv 5) Q10.
rewrite (ER 2%nat 2%bv eq_refl) in Q2. rewrite (ER 3%nat 3%bv eq_refl) in Q3. rewrite (ER 4%nat 4%bv eq_refl) in Q4.
rewrite (ER 8%nat 8%bv eq_refl) in Q8. rewrite (ER 9%nat 9%bv eq_refl) in Q9.
rewrite (ER 20%nat 20%bv eq_refl) in Q20. rewrite (ER 21%nat 21%bv eq_refl) in Q21.
rewrite (ER 22%nat 22%bv eq_refl) in Q22. rewrite (ER 25%nat 25%bv eq_refl) in Q25.
(* slot 88 and the two bytes of `raw`, as the run left them *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
  pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 1
    (YP09.mkRegion (Some 9%nat) 88 96 88 96 [YP09.mkChunk 88 (CVal 8 (SOff 32 1))]) HS ltac:(vm_compute; reflexivity)) as FR1;
  pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 2
    (YP09.mkRegion (Some 25%nat) 0 2 0 2 [YP09.mkChunk 1 (CVal 1 (SLit 0)); YP09.mkChunk 0 (CVal 1 (SData 0 0 1))])
    HS ltac:(vm_compute; reflexivity)) as FR2
end.
cbn [ms_mem restrict] in FR1, FR2.
assert (D88 : sv_denot E (SOff 32 1) = Z_to_bv 64 (c_p cx + Z.of_nat pe + 1))
  by (cbn [sv_denot]; rewrite X32; reflexivity).
assert (B88 : 0 <= c_p cx + Z.of_nat pe + 1 < 2 ^ (8 * Z.of_N 8)) by (change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia).
assert (W8 : Z.of_N 8 <= 8) by (cbn; lia).
pose proof (field_of_regionG _ _ 9%nat (c_sp1 cx) _ _ _ _ _ 88 8%N (SOff 32 1) (c_p cx + Z.of_nat pe + 1)
  FR1 X9 ltac:(cbn; tauto) D88 B88 W8) as V88.
assert (DB0 : sv_denot E (SData 0 0 1) = Z_to_bv 64 (bv_unsigned b0)).
{ rewrite denot_lit_U, (rd1_U_data1 E 0 b0); [reflexivity | lia | rewrite ED; reflexivity]. }
assert (BB0 : 0 <= bv_unsigned b0 < 2 ^ (8 * Z.of_N 1)) by (pose proof (u8_range b0); change (2 ^ (8 * Z.of_N 1)) with 256; lia).
assert (W1 : Z.of_N 1 <= 8) by (cbn; lia).
pose proof (field_of_regionG _ _ 25%nat (gF cx fp + GO_RAW) _ _ _ _ _ 0 1%N (SData 0 0 1) (bv_unsigned b0)
  FR2 X25 ltac:(cbn; tauto) DB0 BB0 W1) as V0.
assert (DZ : sv_denot E (SLit 0) = Z_to_bv 64 0) by reflexivity.
assert (BZ : 0 <= 0 < 2 ^ (8 * Z.of_N 1)) by (change (2 ^ (8 * Z.of_N 1)) with 256; lia).
pose proof (field_of_regionG _ _ 25%nat (gF cx fp + GO_RAW) _ _ _ _ _ 1 1%N (SLit 0) 0
  FR2 X25 ltac:(cbn; tauto) DZ BZ W1) as V1.
change (N.to_nat 8) with 8%nat in V88. change (N.to_nat 1) with 1%nat in V0, V1.
subst regs.
(* ---- GR_malI at 0x81328 ---- *)
assert (HM0 : hmem cx fp t W3 ms3) by exact (conj GSV (conj GFL (conj GIN (conj SL (conj HTB (conj HWS HST)))))).
pose proof (hmem_tr cx fp t ly3 W3 ms3 msF HL HK HM0) as HM1.
apply (fin_mal B MT cx fp k acc ly3 S3 W3 msF _ t).
- unfold gmach, gregs. splits; try assumption; congruence.
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
- rewrite Q20. exact R20.
- rewrite Q21. exact R21.
- rewrite Q22. exact R22.
- rewrite Q24, Epr. unfold c_n. rewrite Z.sub_diag. reflexivity.
- rewrite Q25. exact R25.
- rewrite Q10. reflexivity.
- unfold gslot. rewrite Epr.
  replace (c_p cx + Z.of_nat (length (c_pl cx))) with (c_p cx + Z.of_nat pe + 1) by lia.
  apply rdword_of_val_mem; [exact V88 | lia].
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
