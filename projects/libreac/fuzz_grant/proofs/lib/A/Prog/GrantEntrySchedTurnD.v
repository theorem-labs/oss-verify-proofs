(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedTurnD), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACa1.v. *)
(* The frame-loop turn of LLVMFuzzerTestOneInput, segment D: 0x816a4 .. 0x816ac, the call of reac_headamp_default and the value against it (GrantEntrySchedTurnDefs.v). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC85 GrantFrame YC1h YC1g ACj1 GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
GrantEntryDefs GrantEntrySeat HeadampTxEffective HeadampDefault HeadampTxNext.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
HeadampModel NextModel GrantModel SlotNeeds_c GrantSlotPlan HeadampSched SegSetModel Seg_sched_turn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntrySchedTurnDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* lia below runs on contexts with many / and mod; the facts it needs about them are posed by hand (dm). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).

(* A run whose regions are read-only keeps every byte. *)
Lemma segD_kept_ro : forall E rs H (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forallb (fun r => Z.leb (YP09.r_whi r) (YP09.r_wlo r)) rs = true ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' HF Hro a. rewrite (aview_wrap H m' a), (aview_wrap H m a).
  apply (aview_kept_out E rs H m m' HF); [apply Z.mod_pos_bound; lia|].
  intros (r & Hin & Ha). rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis DFL : treac_headamp_default_spec B.
Variable POST : ecx -> world SEGS -> config -> Prop.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
(* The names of GrantEntrySchedTurnDefs.v at this section's asyms, meter and laws. *)
#[local] Notation tbody := (tbody B MT).
#[local] Notation tcom := (tcom B MT).
#[local] Notation GSn := (GSn B MT).
#[local] Notation TB := (TB B MT).
#[local] Notation trec := (trec B MT).
#[local] Notation TC := (TC B MT).
#[local] Notation TCr := (TCr B MT).
#[local] Notation TD := (TD B MT).
#[local] Notation TE := (TE B MT).
#[local] Notation TF := (TF B MT).
#[local] Notation gtracked := (gtracked B).
#[local] Notation gctx := (gctx B MT LAWS).
#[local] Notation gaddr_ok := (gaddr_ok B).
#[local] Notation ginput_ok := (ginput_ok B MT LAWS).
#[local] Notation tbody_keep := (tbody_keep B MT).
#[local] Notation tcom_keep := (tcom_keep B MT).
#[local] Notation gpres := (gpres B MT LAWS).
#[local] Notation gtracked_rng := (gtracked_rng B MT LAWS).
#[local] Notation table_out := (table_out B MT LAWS).
#[local] Notation gtab_keep := (gtab_keep B).
#[local] Notation GI_sched_of := (GI_sched_of B MT).
#[local] Notation tcom_of_GI_sched := (tcom_of_GI_sched B MT).
#[local] Notation GI_freeT_of := (GI_freeT_of B MT).
#[local] Notation table_sep := (table_sep B LAWS).
#[local] Notation table_new := (table_new B LAWS).
#[local] Notation garo := (garo B MT).
#[local] Notation gtab_obj := (gtab_obj B).
#[local] Notation obj_gtab := (obj_gtab B).

(* The call of reac_headamp_default(p) at 0x816a4, made from the realigned stack pointer
   with the return address 0x816a8: a0 comes back as Pau's dflt p, the memory, the blocks
   and the world are as they were, and the entry function's journal goes on. *)
Lemma hd_call : forall cx fp k ly3 S3 W3 (regsT : bvmap 5 word) memT mdT p,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 memT mdT k ->
  frames S3 = [(GE_CID, fp)] ->
  getr regsT 2 = w64 (c_sp1 cx) -> getr regsT 3 = getr (c_regs cx) 3 -> getr regsT 4 = getr (c_regs cx) 4 ->
  getr regsT 8 = w64 (spZ (c_regs cx)) ->
  getr regsT 1 = w64 (BASE + 0xff8) ->
  rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  getr regsT 10 = w64 p -> 0 <= p < 2 ^ 64 ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_reac_headamp_default)) memT (seg_rom SEGS)) mdT)
    (fun W2 c2 => W2 = W3 /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (getr regsT 1) mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
         [(GE_CID, fp)] ly3 S3 W3 mem2 md2 k /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (HeadampModel.dflt p) /\ (forall x, mem2 x = memT x)).
Proof.
  intros cx fp k ly3 S3 W3 regsT memT mdT p HB HJ Hfr R2 R3 R4 R8 R1 H8 H16 R10 Hp.
  destruct (gctx cx fp k ly3 S3 W3 memT mdT HB HJ Hfr)
    as (EFA & HF4096 & HFceil & HFapp & HF64 & HSH & Hceil & H47 & Hal16 & Hsp1 & Hsp32).
  pose proof HB as ((_ & _ & _ & Hgp & Htp & _) & _).
  pose proof HJ as (_ & HLY & _ & _ & _ & _ & _ & _ & J9 & _).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  assert (GS : GE_STK = 32768) by reflexivity.
  assert (USP : spZ regsT = c_sp1 cx) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
  assert (US0 : s0Z regsT = spZ (c_regs cx)) by (unfold s0Z; rewrite R8; apply unsigned_lit_small; lia).
  assert (Ho : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0).
  { dm (c_sp1 cx) 32. dm (spZ (c_regs cx)) 16. dm (c_sp1 cx - spZ (c_regs cx)) 16. lia. }
  eapply SRr_mono.
  { apply (cl_callS B LAWS W3 regsT memT _ 32768 (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(GE_CID, fp)] ly3 S3 mdT k REAC_HEADAMP_DEFAULT_STK [] 0 (c_sp1 cx - spZ (c_regs cx)) (getr regsT 1) (gch cx)
      (fun ly' S' W' regs' mem' md' => getr regs' 10 = w64 (HeadampModel.dflt p) /\ ly' = ly3 /\ S' = S3 /\ W' = W3 /\
         (forall x, mem' x = memT x) /\ Permutation (ablocks B ly' S') (ablocks B ly3 S3)) HJ).
    - rewrite USP. lia.
    - exact Ho.
    - lia.
    - unfold REAC_HEADAMP_DEFAULT_STK, ESTACK. lia.
    - unfold REAC_HEADAMP_DEFAULT_STK, ESTACK. lia.
    - rewrite R3. exact Hgp.
    - rewrite R4. exact Htp.
    - reflexivity.
    - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite R1. unfold w64. rewrite unsigned_lit_small by lia. lia.
    - replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
      rewrite US0. apply (achain_ly_top (c_ly cx)); [destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|].
      apply (ge_achain B MT cx HB); [intros a Ha; apply J9; lia | exact H8 | exact H16 | lia].
    - intros HPRE'. exact (DFL ly3 S3 W3 regsT memT mdT (gch cx) p HPRE' R10 Hp).
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & _ & HP & (H10 & -> & -> & -> & HM & _)).
  split; [reflexivity|]. exists regs2, mem2, md2.
  split; [reflexivity|]. split; [rewrite Z.add_0_r in HJ2; exact HJ2|].
  split; [exact HP|]. split; [exact H10 | exact HM].
Qed.

(* 0x816a4 .. 0x816ac: the call of reac_headamp_default and the value against it. *)
Lemma segD : seg_D_ok B MT POST.
Proof.
  intros m HTE cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr HMLE
    (i & t & T & us & c & p & v & T' & HR & R10 & R19 & Htb0).
  pose proof HR as (HT & Hm & Hsch & Hnx & Htab & Hlus & Hus & Cc & Cp & Cv).
  destruct (gctx cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfr)
    as (EFA & HF4096 & HFceil & HFapp & HF64 & HSH & Hceil & H47 & Hal16 & Hsp1 & Hsp32).
  pose proof HT as (HTB0 & Hi & R18).
  pose proof HTB0 as (HBD & Hk & Hacc & Hbl & Hn & R20 & R21 & R22 & R23 & R24 & R25 & R27 & HSC & HSL & HWS & HST & HH).
  pose proof (ginput_ok cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ Hfr Hbl) as HIN.
  pose proof HBD as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfc & HG & HSV & HSHW & HFL & Hlen & HINP).
  pose proof HG as (G2 & G8 & G9 & G3 & G4).
  pose proof Htab as (Hint & Ht0 & HTl & HTb).
  (* HeadampSched.frame_ok: the record's value, for a cell the input did not set, is dflt p *)
  pose proof (HeadampSched.frame_ok (c_pl cx) t i Ht0) as FO.
  destruct (GrantSlotPlan.sched_rd (c_pl cx)) as [[[[sb sw] per] fr] pe] eqn:Hsrd.
  rewrite Hsch, Hnx in FO.
  destruct FO as (FL1 & FL2 & FL3 & FLT' & FI1 & FSch & FR01 & FR1).
  destruct (FR1 eq_refl) as (Hc48 & Hp3 & Hleg & Hveff & Hset & Hunset).
  destruct (Hunset Htb0) as (Hvd & _).
  assert (GS : GE_STK = 32768) by reflexivity.
  (* 0x816a4: the jal *)
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) []) E) by (subst E; apply gagree0).
  assert (HS : st_ok_pi SEGS VAL E (mkSS GP_dfl sr_atoms [] None (mkFacts [] [] [])) (restrict (w_H W3) ms3)).
  { rewrite (gms_eq (w_H W3) GP_dfl ms3 Hpc Hrv Hsvc Hrom Hfrg Hfc). apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  clear HE.
  assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  paj_run_tok RUN HS HJ SHOK Bsp0.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' a1 a2 a3 a4 a5 a6 a7) end. apply awr_ok_nil. }
  lazymatch goal with
  | HSx : st_ok _ _ _ (restrict _ ?msX) |- SRr _ _ (mkCfg ?msX _) _ => rename HSx into HSc; rename msX into msc
  | HSx : st_ok_pi _ _ _ _ (restrict _ ?msX) |- SRr _ _ (mkCfg ?msX _) _ => rename HSx into HSc; rename msX into msc
  end.
  assert (FK1 : forall a, aview SEGS (w_H W3) (ms_mem msc) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a. repeat match goal with HFx : frame_of _ _ (mrestrict _ (ms_mem ?m0)) (mrestrict _ (ms_mem ?m1)) |-
        aview _ _ (ms_mem ?m1) a = _ => rewrite (segD_kept_ro _ _ _ _ _ HFx ltac:(vm_compute; reflexivity) a); clear HFx end.
    reflexivity. }
  first
    [ pose proof (regs_kept_of_st_ok SEGS E _ _ (ms_regs ms3) []
        [2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv HSc HAE ltac:(vm_compute; reflexivity)) as QR
    | pose proof (regs_kept_of_st_ok_pi E _ _ (ms_regs ms3) []
        [2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv HSc HAE ltac:(vm_compute; reflexivity)) as QR ].
  cbn [ms_regs restrict] in QR.
  prreg HSc (1%bv : bv 5) Q1.
  assert (Hra : getr (ms_regs msc) 1 = w64 (BASE + 0xff8)) by (rewrite Q1; reflexivity).
  assert (HSVc : gsaved cx W3 msc).
  { destruct HSV as (S8 & S16). split.
    - rewrite <- S8. apply rdword_ext. intros kk Hkk. apply FK1.
    - intros j Hj. rewrite <- (S16 j Hj). apply rdword_ext. intros kk Hkk. apply FK1. }
  pmkst HSc. rewrite ?pa_sigma_reac_headamp_default.
  eapply SRr_bind.
  { apply (hd_call cx fp k ly3 S3 W3 (ms_regs msc) (ms_mem msc) _ p HB HJ Hfr).
    - rewrite (QR 2%bv ltac:(cbv; tauto)). exact G2.
    - rewrite (QR 3%bv ltac:(cbv; tauto)). exact G3.
    - rewrite (QR 4%bv ltac:(cbv; tauto)). exact G4.
    - rewrite (QR 8%bv ltac:(cbv; tauto)). exact G8.
    - exact Hra.
    - exact (proj1 HSVc).
    - pose proof (proj2 HSVc 0 ltac:(lia)) as S0.
      replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in S0 by lia.
      rewrite S0. reflexivity.
    - rewrite (QR 10%bv ltac:(cbv; tauto)). exact R10.
    - lia. }
  intros W4 c4 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & R10' & HM2).
  (* the callee-saved registers, back from the call *)
  assert (QP : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv ->
               getr regs2 r0 = getr (ms_regs ms3) r0).
  { intros r0 Hr0.
    assert (Hr1 : In r0 [2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv)
      by (cbv [In] in Hr0 |- *; tauto).
    rewrite <- (QR r0 Hr1).
    assert (Hcs : acallee_saved (bv_unsigned r0)).
    { cbv [In] in Hr0. unfold acallee_saved.
      repeat (destruct Hr0 as [<- | Hr0];
        [ lazymatch goal with |- context [bv_unsigned ?r] =>
            let z := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with z end; lia |]);
      destruct Hr0. }
    pose proof (HP2 _ Hcs) as X. rewrite !Z_to_bv_bv_unsigned in X. exact X. }
  assert (FK2 : forall a, aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a. rewrite <- (FK1 a). unfold aview, YP09.mbyte, mrestrict. rewrite HM2. reflexivity. }
  rewrite Hra.
  (* 0x816a8: bne s3,a0 to the error block at 0x81a0c *)
  remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2.
  assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
  assert (HAE2 : env_agree 32 (Ereg regs2 []) E2) by (subst E2; apply gagree0).
  assert (EE2 : forall (n : nat) (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E2 n = getr regs2 r0)
    by (intros n0 r0 Hr; subst E2; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (HS2 : st_ok_pi SEGS VAL E2 (mkSS 0xff8 sr_atoms [] None (mkFacts [] [] []))
     (restrict (w_H W3) (mkst regs2 (w64 (BASE + 0xff8)) mem2 (seg_rom SEGS)))).
  { rewrite (gms_eq (w_H W3) 0xff8 (mkst regs2 (w64 (BASE + 0xff8)) mem2 (seg_rom SEGS))
      eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl).
    apply pa_entry_st_ok_full.
    - rewrite HE2. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  clear HE2.
  assert (SHOK2 : sh_ok SEGS BxL [] E2 (mrestrict (w_H W3) (ms_mem (mkst regs2 (w64 (BASE + 0xff8)) mem2 (seg_rom SEGS)))))
    by constructor.
  psrr_branch_tok RUN BR HS2 SHOK2 Bsp0.
  - (* taken, to the error block: s3 is the record's value v, a0 is dflt p, and v = dflt p
       (HeadampSched.frame_ok, the cell the input did not set) *)
    exfalso.
    rewrite branch_ne_U in Hc. unfold U in Hc. rewrite !ge_sv_SOff0 in Hc.
    rewrite (EE2 19%nat 19%bv eq_refl), (EE2 10%nat 10%bv eq_refl) in Hc.
    rewrite (QP 19%bv ltac:(cbv; tauto)), R19, R10', <- Hvd, Z.eqb_refl in Hc.
    cbn in Hc. discriminate Hc.
  - (* not taken: on to 0x816ac *)
    paj_run_to_tok RUNTO HS2 HJ2 SHOK2 Bsp0 GP_scn.
    { lazymatch goal with |- awr_ok ?E0 ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' a1 a2 a3 a4 a5 a6 a7) end. apply awr_ok_nil. }
    lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msF) |- SRr _ _ (mkCfg ?msF ?mdF) _ =>
      destruct (stf _ _ _ _ HSx eq_refl) as (Fpc & Frv & Fsvc & From & Ffr & Ffc);
      assert (FK : forall a, aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a)
        by (intros a; rewrite <- (FK2 a);
            repeat match goal with HFx : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ (ms_mem ?m1)) |-
              aview _ _ (ms_mem ?m1) a = _ => rewrite (segD_kept_ro _ _ _ _ _ HFx ltac:(vm_compute; reflexivity) a); clear HFx end;
            reflexivity);
      pose proof (regs_kept_of_st_ok_pi E2 ssx (restrict (w_H W3) msF) regs2 []
        [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv HSx HAE2 ltac:(vm_compute; reflexivity)) as FR;
      cbn [ms_regs restrict] in FR;
      apply (HTE cx fp k acc ly3 S3 W3 msF mdF HB HJ2 Hfr HMLE)
    end.
    exists i, t, T, us, c, p, v, T'.
    split.
    { eapply tcom_keep; [exact HF4096 | exact HFceil | exact HFapp | lia | lia | exact HIN | exact HT
        | exact Fpc | exact Frv | exact Fsvc | exact From | exact Ffr | exact Ffc
        | repeat split; (rewrite FR by (cbv; tauto)); apply QP; cbv; tauto
        | exact Hi | rewrite FR by (cbv; tauto); rewrite QP by (cbv; tauto); exact R18
        | intros a _ _; apply FK | | exact GSH_turn_len ].
      intros j Hj. rewrite FK. apply HSHW. exact Hj. }
    split; [exact Hm|]. split; [exact Hsch|]. split; [exact Hnx|].
    split; [eapply gtab_keep; [exact Htab | intros j _; apply FK]|].
    split; [exact Hlus|].
    split; [eapply gfarr_keep; [exact Hus | intros a _; apply FK]|].
    unfold gfb in *. rewrite !FK. split; [exact Cc|]. split; [exact Cp | exact Cv].
Qed.

End c.
End b.
End a.
