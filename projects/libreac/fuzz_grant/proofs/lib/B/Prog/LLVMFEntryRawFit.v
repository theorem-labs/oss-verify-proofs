(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryRawRd1), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryRawRd1.v, with its module paths changed; 246 of its 286 lines of code are new or changed and 218 lines of the source are left out. *)
(* Ported from lib/A/Prog/GrantEntryRawFit.v of a working branch 7c8c67da870 (blob 8784a546bc1). *)
(* The call of reac_grant_alloc_fits in the hand-built allocation phase of fuzz_grant's
   entry function LLVMFuzzerTestOneInput on image B (fuzz_grant.c:377-379 and the arguments
   of the call at :383), the slots 0x818e0 .. 0x81918 (GR_fit .. GR_bs2 of
   LLVMFEntryRawDefs.v).

   0x818e0 calls reac_grant_alloc_fits (raw.base, raw.width) with the return address
   BASE + 0xea8; its contract tb_reac_grant_alloc_fits_spec gives a0 = fits base width and
   keeps the layout, the state, the world and every byte. Its premise
   `0 <= base -> 1 <= width <= 40 -> base + width < 2 ^ 31` (OBL_alloc_fits_bound of
   GrantBContracts.v) holds because both are bytes. 0x818e4 branches on a0: when raw fits,
   a0 := 3 * raw.width + 8 (the byte at s5 + 1) and `beq s8, a0` (0x818f8) is taken, as
   s8 = 8 + 3 * raw.width, past the `j 0x81d98` (the abort) at 0x818fc; when raw does not
   fit, a0 := -1 and `bne s8, a0` into the abort (0x81904) is not taken, as s8 = -1.
   0x81908 .. 0x81914 set a0 .. a3 to NULL, 1, &raw and the table for the call at GR_bs2.
   No byte of memory changes.

   The symbolic run uses one region, the byte raw.width at s5 + 1 as atom 32, and keeps it
   across the call; the call's journal and kept registers come from `gcall`. *)
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
GrantTop GrantSyms GrantList GrantPa GrantPaLib YC1g YC1h YC85 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantBContracts LLVMFEntryDefs LLVMFEntrySeat LLVMFEntrySetDefs LLVMFEntryRawDefs LLVMFEntryRawLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantModel BuildSweepModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c SegCLib SegSetModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* The value of an atom, as an unsigned 64-bit number: copied from lib/A/Prog/GrantAllocFits.v,
   an image-A file that an image-B file does not Require. *)
Lemma U_atom_mod : forall E n v, ew E n = Z_to_bv 64 v -> U E (SOff n 0) = v mod 2 ^ 64.
Proof.
intros E n v H. rewrite U_SOff, H, Z.add_0_r, Z_to_bv_unsigned. unfold zcanon, bv_wrap, M64.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.

Lemma fit_raw_range : forall pl : list byte,
  0 <= fst (fst (GrantSlotPlan.raw_rd pl)) < 256 /\ 0 <= snd (fst (GrantSlotPlan.raw_rd pl)) < 256.
Proof.
  intros pl. unfold GrantSlotPlan.raw_rd.
  pose proof (SegSetModel.rd8_range pl (GrantSlotPlan.pos_end pl)) as R1.
  destruct (GrantSlotPlan.rd8 pl (GrantSlotPlan.pos_end pl)) as [rb p1]. cbn [fst] in R1.
  pose proof (SegSetModel.rd8_range pl p1) as R2.
  destruct (GrantSlotPlan.rd8 pl p1) as [rw p2]. cbn [fst] in R2. cbn [fst snd]. lia.
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
Hypothesis FITS : tb_reac_grant_alloc_fits_spec B.

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* raw.width, the byte at s5 + 1 that the slot 0x818e8 reads, as atom 32. *)
Definition R_fitw : YP09.region := YP09.mkRegion (Some 21%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 32 0))].
Definition ss_fit : sstate := mkSS GR_fit sr_atoms [R_fitw] None (mkFacts [] [] []).

(* A run whose regions have no write window keeps every byte: carry the equation of the
   memory with that of 0x818e0 to the run's new memory. *)
Local Ltac fit_upd_hm :=
  repeat match goal with
  | H : frame_of _ _ (mrestrict _ _) _ |- _ => clear H
  | H : mem_grows _ _ |- _ => clear H
  end;
  lazymatch goal with
  | HF : frame_of ?Ex ?rs ?m1 ?m2, HM : forall x, ?m1 x = ?m0 x |- _ =>
      let HM' := fresh "HM" in
      assert (HM' : forall x, m2 x = m0 x)
        by (intros x; transitivity (m1 x); [|exact (HM x)]; apply HF;
            let rs' := eval vm_compute in rs in change rs with rs';
            let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
            intros (r & Hr & Hb);
            repeat (destruct Hr as [Hr | Hr]; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hb; lia |]);
            destruct Hr);
      clear HM HF; rename HM' into HM
  end.

(* a0 at 0x818f4: 3 * raw.width + 8, from the byte at s5 + 1 (atom 32). *)
Definition FIT_W3X : sv :=
  SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 8 (SOff 32 0)) (SLit 1)) (SExt false 8 (SOff 32 0))) (SLit 8).

Lemma U_fit_w3x : forall E w, ew E 32 = Z_to_bv 64 w -> 0 <= w < 256 -> U E FIT_W3X = 8 + 3 * w.
Proof.
  intros E w H Hw. unfold FIT_W3X.
  assert (Ux : U E (SExt false 8 (SOff 32 0)) = w).
  { rewrite U_zext, (U_atom E 32 w H) by lia. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia. }
  rewrite !U_SAlu, Ux, !U_SLit. cbn [zalu_raw].
  rewrite (zcanon_id 1), (zcanon_id 8) by (unfold M64; lia).
  change (Z.land 1 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  rewrite (zcanon_id (w * 2)) by (unfold M64; lia).
  rewrite (zcanon_id (w * 2 + w)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* GR_bs2I at a machine state whose memory is that of 0x818e0 and whose kept registers
   are those of 0x818e0, with the arguments of the call in a0 .. a3. *)
Lemma fit_bs2I : forall cx fp k acc ly3 S3 W3 (ms3 ms : machine_state) md t s,
  ge_base B MT cx ->
  rcore cx fp GR_fit t W3 ms3 -> k <= 4 -> acc <= GE_A2 MT + mo_malloc MT RAW_SW ->
  gblk2 B cx ly3 S3 t s -> gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) -> 4096 <= s ->
  getr (ms_regs ms3) 20 = w64 t -> getr (ms_regs ms3) 18 = w64 s ->
  (forall x, ms_mem ms x = ms_mem ms3 x) ->
  ms_pc_val ms = w64 (BASE + GR_bs2) -> ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  getr (ms_regs ms) 2 = getr (ms_regs ms3) 2 -> getr (ms_regs ms) 3 = getr (ms_regs ms3) 3 ->
  getr (ms_regs ms) 4 = getr (ms_regs ms3) 4 -> getr (ms_regs ms) 8 = getr (ms_regs ms3) 8 ->
  getr (ms_regs ms) 9 = getr (ms_regs ms3) 9 -> getr (ms_regs ms) 18 = getr (ms_regs ms3) 18 ->
  getr (ms_regs ms) 19 = getr (ms_regs ms3) 19 -> getr (ms_regs ms) 20 = getr (ms_regs ms3) 20 ->
  getr (ms_regs ms) 21 = getr (ms_regs ms3) 21 -> getr (ms_regs ms) 22 = getr (ms_regs ms3) 22 ->
  getr (ms_regs ms) 23 = getr (ms_regs ms3) 23 ->
  getr (ms_regs ms) 10 = w64 0 -> getr (ms_regs ms) 11 = w64 1 ->
  getr (ms_regs ms) 12 = w64 (gF cx fp + GO_RAW) -> getr (ms_regs ms) 13 = w64 t ->
  GR_bs2I B MT cx fp k acc ly3 S3 W3 ms md.
Proof.
  intros cx fp k acc ly3 S3 W3 ms3 ms md t s HB HRC Hk Hacc HBL HGT Hs R20 R18 HM P1 P2 P3 P4 P5 P6
    E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 R10 R11 R12 R13.
  destruct HRC as (HBODY & Hn & R19 & R21 & R22 & R23 & S48 & SL & GB0 & GB1 & GWAS & GSET & HREL & HI1).
  destruct HBODY as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4) & (GSV1 & GSV2) & GSH & GFL & GLEN & GIN).
  destruct SL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10).
  destruct HGT as (HGT1 & HGT2 & HGT3 & HGT4).
  assert (AV : forall a, aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a)
    by (intros a; unfold aview, YP09.mbyte, mrestrict; rewrite HM; reflexivity).
  assert (RW : forall a, rdword (aview SEGS (w_H W3) (ms_mem ms)) a = rdword (aview SEGS (w_H W3) (ms_mem ms3)) a)
    by (intros a; apply rdword_tr; intros j _; apply AV).
  assert (GA : forall p L, garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) p L ->
                 garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) p L)
    by (intros p L; apply garr8_aview_kept; intros a _; apply AV).
  exists t, s. unfold rcore, ge_body, gregs, gsaved, gshadow, rslots, gslot, gfb, gfarr, gtab in *.
  repeat match goal with |- _ /\ _ => split end;
  first [ assumption | congruence
        | (rewrite RW; assumption) | (rewrite AV; assumption) | (apply GA; assumption)
        | (intros j Hj; rewrite RW; apply GSV2, Hj)
        | (intros i Hi; rewrite AV; apply GSH, Hi)
        | (intros i H1 H2 H3 H4; rewrite AV; apply HGT4; assumption) ].
Qed.

Theorem seg_raw_fit : forall POST, ge_from B MT POST (GR_bs2I B MT) -> ge_from B MT POST (GR_fitI B MT).
Proof.
intros POST HN cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO (t & s & HRC & Hk & Hacc & HBL & HGT & Hs & R20 & R18 & R24 & R10 & R11).
pose proof HRC as (HBODY & Hn & R19 & R21 & R22 & R23 & S48 & SL & GB0 & GB1 & GWAS & GSET & HREL & HI1).
pose proof HBODY as (Pc & Prv & Psv & Pro & Pfr & Pfc & HGR & GSV & GSH & GFL & GLEN & GIN).
pose proof HGR as (G2 & G8 & G9 & G3 & G4).
pose proof (fit_raw_range (c_pl cx)) as (Hrb & Hrw). fold (raw_b cx) (raw_w cx) in Hrb, Hrw.
pose proof (ge_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & _).
pose proof (proj1 alloc_ceiling_val) as AC.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
rewrite (gmach_mkst cx ms3 GR_fit (conj Pc (conj Prv (conj Psv (conj Pro (conj Pfr (conj Pfc HGR))))))).
remember (ms_regs ms3) as regs eqn:Eregs.
remember (Eimg (Ereg regs [Z_to_bv 64 (raw_w cx)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr regs r)
  by (intros q r Hq; pose proof (bv_unsigned_in_range 5 r) as Hr; change (bv_modulus 5) with 32 in Hr;
      subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
assert (F32 : ew E 32 = Z_to_bv 64 (raw_w cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (F21 : ew E 21 = Z_to_bv 64 (gF cx fp + GO_RAW)) by (rewrite (EE 21%nat 21%bv eq_refl); subst regs; exact R21).
assert (HS : st_ok_pi SEGS VAL E ss_fit
  (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + GR_fit)) (ms_mem ms3) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_fit. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, R_fitw. cbv zeta.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite F21. unfold GO_RAW in *. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ _ 1 1 (SOff 32 0) (raw_w cx)); [apply gsv0; [exact F32 | lia] | cbn; lia | cbn; lia |].
    destruct (val_mem1_of_aview SEGS (w_H W3) (ms_mem ms3) _ _ GB1) as [Hv _].
    replace (gF cx fp + 560 + 1) with (gF cx fp + (560 + 1)) by lia. exact Hv.
  - exact (conj I I).
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS GBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
assert (HM : forall x, ms_mem ms3 x = ms_mem ms3 x) by reflexivity.
(* 0x818e0: the jal into reac_grant_alloc_fits. *)
paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | awr_ok_tac] |].
fit_upd_hm.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
rewrite (EE 2%nat 2%bv eq_refl) in Q2. rewrite (EE 3%nat 3%bv eq_refl) in Q3. rewrite (EE 4%nat 4%bv eq_refl) in Q4.
rewrite (EE 8%nat 8%bv eq_refl) in Q8. rewrite (EE 10%nat 10%bv eq_refl) in Q10. rewrite (EE 11%nat 11%bv eq_refl) in Q11.
rewrite pa_sigma_reac_grant_alloc_fits.
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg _ ?mm _; cfg_model := ?mdq |} _ =>
  assert (AV1 : forall a, aview SEGS (w_H W3) mm a = aview SEGS (w_H W3) (ms_mem ms3) a)
    by (intros a; unfold aview, YP09.mbyte, mrestrict; rewrite HM; reflexivity);
  eapply (gcall B MT LAWS STK_reac_grant_alloc_fits []
    (fun ly' S' W' regs' mem' md' => getr regs' 10 = w64 (Z.b2z (fits (raw_b cx) (raw_w cx))) /\
       ly' = ly3 /\ S' = S3 /\ W' = W3 /\ (forall x, mem' x = mm x) /\ Permutation (ablocks B ly' S') (ablocks B ly3 S3))
    _ 0xea8 POST cx fp k ly3 S3 W3 rg mm mdq HB HJ);
  [ rewrite Q2; exact G2
  | rewrite Q8; exact G8
  | rewrite Q3; exact G3
  | rewrite Q4; exact G4
  | exact Q1
  | lia
  | reflexivity
  | rewrite (rdword_tr _ _ _ (fun j _ => AV1 _)); exact (proj1 GSV)
  | rewrite (rdword_tr _ _ _ (fun j _ => AV1 _));
    pose proof (proj2 GSV 0 ltac:(lia)) as H0; rewrite Z.mul_0_r, Z.sub_0_r in H0; rewrite H0; reflexivity
  | unfold STK_reac_grant_alloc_fits, ESTACK; lia
  | intros a Ha; destruct (inFP_nil a Ha)
  | intros HPRE1;
    exact (FITS ly3 S3 W3 rg mm mdq (gch cx) (raw_b cx) (raw_w cx) HPRE1
      ltac:(rewrite Q10; subst regs; exact R10) ltac:(rewrite Q11; subst regs; exact R11)
      ltac:(unfold int32; lia) ltac:(unfold int32; lia) ltac:(intros; lia))
  | ] end.
intros W2 ly2 S2 regs2 mem2 md2 HJ2 HJc HP (Ha0 & -> & -> & -> & Hmem2 & _).
jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W3) mem2) HP [0%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_cons; [|apply Forall_nil]. unfold region_kept.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val restrict ms_mem].
  split; [intros a _; unfold YP09.mbyte, mrestrict; rewrite Hmem2; reflexivity | intros a Ha; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
assert (HMc : forall x, mem2 x = ms_mem ms3 x) by (intros x; rewrite Hmem2; apply HM).
clear HM Hmem2. rename HMc into HM.
assert (SHOK2 : sh_ok SEGS GBx [] (havoc E 33 (map (getr regs2) CLOB)) (mrestrict (w_H W3) mem2)) by constructor.
clear SHOK HJ HJc. rename SHOK2 into SHOK. rename HJ2 into HJ.
assert (HEI2 : img_env VAL A_LIM (havoc E 33 (map (getr regs2) CLOB))) by (apply img_env_havoc; [exact HEI | cbv; lia]).
assert (F37 : ew (havoc E 33 (map (getr regs2) CLOB)) 37 = Z_to_bv 64 (Z.b2z (fits (raw_b cx) (raw_w cx)))).
{ change 37%nat with (33 + 4)%nat.
  rewrite (YN3v.ew_havoc_new E 33 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbv; lia).
  cbn [nth map]. exact Ha0. }
assert (OLD : forall q, (q < 33)%nat -> ew (havoc E 33 (map (getr regs2) CLOB)) q = ew E q)
  by (intros q Hq; apply YN3v.ew_havoc_old; exact Hq).
assert (F24 : ew (havoc E 33 (map (getr regs2) CLOB)) 24 = Z_to_bv 64 (raw_ans cx))
  by (rewrite OLD, (EE 24%nat 24%bv eq_refl) by lia; subst regs; exact R24).
assert (F32b : ew (havoc E 33 (map (getr regs2) CLOB)) 32 = Z_to_bv 64 (raw_w cx)) by (rewrite OLD by lia; exact F32).
assert (HU37 : U (havoc E 33 (map (getr regs2) CLOB)) (SOff 37 0) = Z.b2z (fits (raw_b cx) (raw_w cx)))
  by (apply (U_atom _ 37 _ F37); destruct (fits (raw_b cx) (raw_w cx)); cbn [Z.b2z]; lia).
assert (HU24 : U (havoc E 33 (map (getr regs2) CLOB)) (SOff 24 0) = raw_ans cx mod 2 ^ 64) by exact (U_atom_mod _ 24 _ F24).
assert (HUW : U (havoc E 33 (map (getr regs2) CLOB)) FIT_W3X = 8 + 3 * raw_w cx) by exact (U_fit_w3x _ _ F32b Hrw).
unfold FIT_W3X in HUW.
assert (HUm1 : forall E', U E' (SLit 18446744073709551615) = 18446744073709551615)
  by (intros E'; rewrite U_SLit; apply zcanon_id; unfold M64; lia).
assert (HU0 : forall E', U E' (SLit 0) = 0) by (intros E'; rewrite U_SLit; apply zcanon_id; unfold M64; lia).
unfold raw_ans in HU24.
destruct (fits (raw_b cx) (raw_w cx)) eqn:Hfit; cbn [Z.b2z] in HU37, HU24.
- (* raw fits: 0x818e4 beqz a0 is not taken. *)
  psrr_branch_tok RUN BR HS SHOK GBspan.
  { rewrite branch_eq_U, HU37, HU0 in Hc. apply Z.eqb_eq in Hc. lia. }
  (* 0x818e8 .. 0x818f8: a0 := 3 * raw.width + 8, beq s8, a0 past the abort. *)
  paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | awr_ok_tac] |].
  fit_upd_hm.
  psrr_branch_tok RUN BR HS SHOK GBspan.
  2: { rewrite branch_eq_U, HU24, HUW in Hc0. rewrite Z.mod_small in Hc0 by lia. rewrite Z.eqb_refl in Hc0. discriminate Hc0. }
  (* 0x81908 .. 0x81918: the arguments of the call at GR_bs2. *)
  paj_run_to_tok RUNTO HS HJ SHOK GBspan GR_bs2; [first [apply awr_ok_nil | awr_ok_tac] |].
  fit_upd_hm.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    apply (HN cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO);
    destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc' & Prv' & Psv' & Pro' & Pfr' & Pfc') end.
  cbn [ss_pc] in Pc'.
  prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18.
  prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20. prreg HS (21%bv : bv 5) T21.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23.
  prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12. prreg HS (13%bv : bv 5) T13.
  rewrite (EE 2%nat 2%bv eq_refl) in T2. rewrite (EE 3%nat 3%bv eq_refl) in T3. rewrite (EE 4%nat 4%bv eq_refl) in T4.
  rewrite (EE 8%nat 8%bv eq_refl) in T8. rewrite (EE 9%nat 9%bv eq_refl) in T9. rewrite (EE 18%nat 18%bv eq_refl) in T18.
  rewrite (EE 19%nat 19%bv eq_refl) in T19. rewrite (EE 20%nat 20%bv eq_refl) in T20.
  rewrite (EE 21%nat 21%bv eq_refl) in T21. rewrite (EE 22%nat 22%bv eq_refl) in T22.
  rewrite (EE 23%nat 23%bv eq_refl) in T23.
  rewrite F21 in T12. rewrite (EE 20%nat 20%bv eq_refl), R20 in T13.
  subst regs.
  exact (fit_bs2I cx fp k acc ly3 S3 W3 ms3 _ _ t s HB HRC Hk Hacc HBL HGT Hs R20 R18 HM Pc' Prv' Psv' Pro' Pfr' Pfc'
    T2 T3 T4 T8 T9 T18 T19 T20 T21 T22 T23 T10 T11 T12 T13).
- (* raw does not fit: 0x818e4 beqz a0 is taken. *)
  psrr_branch_tok RUN BR HS SHOK GBspan; [|rewrite branch_eq_U, HU37, HU0 in Hc; apply Z.eqb_neq in Hc; lia].
  (* 0x81900, 0x81904: li a0, -1; bne s8, a0 into the error path. *)
  paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | awr_ok_tac] |].
  fit_upd_hm.
  psrr_branch_tok RUN BR HS SHOK GBspan.
  { rewrite branch_ne_U, HU24, HUm1 in Hc0. change ((-1) mod 2 ^ 64) with 18446744073709551615 in Hc0.
    rewrite Z.eqb_refl in Hc0. discriminate Hc0. }
  (* 0x81908 .. 0x81918: the arguments of the call at GR_bs2. *)
  paj_run_to_tok RUNTO HS HJ SHOK GBspan GR_bs2; [first [apply awr_ok_nil | awr_ok_tac] |].
  fit_upd_hm.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    apply (HN cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO);
    destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc' & Prv' & Psv' & Pro' & Pfr' & Pfc') end.
  cbn [ss_pc] in Pc'.
  prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18.
  prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20. prreg HS (21%bv : bv 5) T21.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23.
  prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12. prreg HS (13%bv : bv 5) T13.
  rewrite (EE 2%nat 2%bv eq_refl) in T2. rewrite (EE 3%nat 3%bv eq_refl) in T3. rewrite (EE 4%nat 4%bv eq_refl) in T4.
  rewrite (EE 8%nat 8%bv eq_refl) in T8. rewrite (EE 9%nat 9%bv eq_refl) in T9. rewrite (EE 18%nat 18%bv eq_refl) in T18.
  rewrite (EE 19%nat 19%bv eq_refl) in T19. rewrite (EE 20%nat 20%bv eq_refl) in T20.
  rewrite (EE 21%nat 21%bv eq_refl) in T21. rewrite (EE 22%nat 22%bv eq_refl) in T22.
  rewrite (EE 23%nat 23%bv eq_refl) in T23.
  rewrite F21 in T12. rewrite (EE 20%nat 20%bv eq_refl), R20 in T13.
  subst regs.
  exact (fit_bs2I cx fp k acc ly3 S3 W3 ms3 _ _ t s HB HRC Hk Hacc HBL HGT Hs R20 R18 HM Pc' Prv' Psv' Pro' Pfr' Pfc'
    T2 T3 T4 T8 T9 T18 T19 T20 T21 T22 T23 T10 T11 T12 T13).
Qed.

End c.
End b.
End a.
