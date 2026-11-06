(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 297 of its 339 lines of code are new or changed and 1038 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readDefs.v; 78 of its 136 lines of code are new or changed and 281 lines of the source are left out. *)
(* model_read on image A: small facts its walk segments share about the bytes of the write set (the model block, kind
   and alias): they stay writable at any later memory that shows them with the same value (an image byte of the write
   set lies in a writable segment, as the Pre's `~ in_roP` says, so LinkWalkWseg.v makes it writable at any memory;
   any other byte is present where it shows its value), and a callee keeps them (they are bytes the callee may read,
   LinkWalkCall.v ajw_akb, outside its write set).
   Proves no function (kind: segment lemma of model_read's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkCall LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c index_of_c talk_c model_readDefs LinkWalkWseg.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AE7f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YN2j.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* the join of a state at +pc into a given state TGT: the registers CL forgotten to the atoms from k *)
Ltac mr_joinS HS k pc CL TGT HSn :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?Ex ?ssx (restrict (w_H ?Wx) ?msx) =>
    let HS2 := fresh "HS2" in
    pose proof (st_ok_pi_after_stretch_hi k Ex (abs_ss val ssx) (restrict (w_H Wx) msx) (ms_regs msx)
      (mrestrict (w_H Wx) (ms_mem msx)) (ss_mem ssx) (AF_model_read + pc) CL HS eq_refl
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) (submem_refl _) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) (fun r _ => eq_refl)
      ltac:(apply Forall_forall; intros; apply mr_region_kept_same)) as HS2;
    let HS3 := fresh "HS3" in
    pose proof (mr_st_ok_pi_merge _ TGT _ _ HS2 ltac:(vm_compute; reflexivity)) as HS3;
    assert (HSn : st_ok_pi segs val (havoc Ex k (map (getr (ms_regs msx)) CL)) TGT
      (restrict (w_H Wx) (mkst (ms_regs msx) (Z_to_bv 64 (pa_val A_TEXT + (AF_model_read + pc))) (ms_mem msx)
         (seg_rom pa_segs))))
      by (rewrite restrict_mkst_fx; exact HS3);
    clear HS2 HS3
  end.

(* a segment of the PLAIN engine over ajournal_gx run to a listing offset (LinkWalkSide.v paj_run_to_plain_x) *)
Ltac mr_run_plain_to RUNPT HS HJ stop :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_run_toN_pi link_tpi FUEL stop ss) in
    lazymatch r with
    | (?ss', ?st) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_run_toN_pi link_tpi FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
      let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
      eapply (RUNPT W FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
      [ clear Hrun
      | clear Hrun HS HJ;
        let ms' := fresh "ms" in let mat := fresh "mat" in
        let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
        intros ms' mat HS HJ HF HFr HG; cbn [ms_mem mkst] in HF, HFr, HG, HJ ]
    end
  end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis HSEGS : pa_segs = tfibsegs.

Lemma mr_wr_writable : forall rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    (W2 : world pa_segs) (m2 : word -> option byte) a,
  MR_ENTRY SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  inFP (model_read_awr regs (rdW W memc)) a ->
  writable_at pa_segs (rdW W memc) a ->
  (~ in_img pa_segs a -> aview pa_segs (w_H W2) m2 a = aview pa_segs (w_H W) memc a) ->
  writable_at pa_segs (rdW W2 m2) a.
Proof.
intros rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs W2 m2 a HENT Ha Hw Hv.
destruct (mr_wr_facts SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HENT a Ha)
  as (_ & _ & _ & _ & Ha64).
pose proof HENT as (HPRE & _ & _).
destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnro).
destruct (classic (in_img pa_segs a)) as [Hi | Hn].
- assert (Hw' : writable_at tfibsegs (rdW W2 m2) a).
  { apply wseg_writable_tfib.
    destruct Hi as (sg & Hin & Hr). exists sg. split; [rewrite <- HSEGS; exact Hin|]. split; [|exact Hr].
    destruct (seg_writable sg) eqn:Ew; [reflexivity|]. exfalso. apply (Hnro a Ha). left.
    exists sg. split; [exact Hin|]. split; [exact Ew | exact Hr]. }
  rewrite <- HSEGS in Hw'. exact Hw'.
- apply apresent_writable. apply (apresent_transfer pa_segs (w_H W) (w_H W2) memc m2 a Ha64 Hn (Hv Hn)).
  assert (Hw' : writable_at tfibsegs (rdW W memc) a) by (rewrite <- HSEGS; exact Hw).
  assert (Hn' : ~ in_img tfibsegs a) by (rewrite <- HSEGS; exact Hn).
  exact (AE7f.apresent_of_writable (w_H W) memc a Ha64 Hn' Hw').
Qed.

(* a byte of the write set shows its call-time value at any later memory the kept clause reaches, outside its
   exception set *)
Lemma mr_wr_view : forall rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    (W2 : world pa_segs) (m2 : word -> option byte) (Ex : Z -> Prop) a,
  MR_ENTRY SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  inFP (model_read_awr regs (rdW W memc)) a ->
  akept pa_segs B lyc Sc W memc W2 m2 (spZ regs - MODEL_READ_AK) (spZ regs) Ex -> ~ Ex a ->
  aview pa_segs (w_H W2) m2 a = aview pa_segs (w_H W) memc a.
Proof.
intros rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs W2 m2 Ex a HENT Ha HK HE.
destruct (mr_wr_facts SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HENT a Ha)
  as (Happ & Hwin & Herr & Hajw & Ha64).
pose proof HENT as (HPRE & _ & _).
destruct HPRE as (HJ & HGok & _).
pose proof (ajw_akb SK pa_segs B LAWS G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc Sc
  (spZ regs - MODEL_READ_AK) (spZ regs) a HGok HJ Hajw Hwin Happ Herr eq_refl eq_refl (fun b m H => H)
  (fun c q H => H) (fun c q => eq_refl)) as Hakb.
exact (akept_akb_gx SK pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k W2 m2
  (spZ regs - MODEL_READ_AK) (spZ regs) Ex a HJ HK Hakb HE).
Qed.

(* one instrumented check's shadow entry: the byte range's shadow at the current memory, off the shadow span *)
Lemma mr_shent_ok : forall E (H : word -> bool) (m : word -> option byte) (nn : nat) x len,
  ew E 32 = Z_to_bv 64 MR_SB -> ew E nn = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= len ->
  (forall a, x <= a < x + len -> a < kLowMemEnd \/ kHighMemBeg <= a) ->
  range_addressable (aview pa_segs H m) SHADOW_OFF x len ->
  sh_ok pa_segs MRBx [mkSHE nn 0 len] E (mrestrict H m).
Proof.
  intros E H m nn x len E32 Ex Hx Hl Happ HR. unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  assert (HB : U E MRBx = SHADOW_OFF) by (unfold MRBx; rewrite (U_atom E 32 MR_SB E32) by (unfold MR_SB; lia); reflexivity).
  assert (Hq : U E (SOff nn 0) = x) by (apply U_atom; [exact Ex | lia]).
  rewrite HB, Hq. split.
  - rewrite Z.add_0_r, Z.sub_0_r. rewrite <- (aview_rd_of pa_segs). exact HR.
  - intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. destruct (Happ a ltac:(lia)) as [Ha' | Ha'];
      unfold SHADOW_OFF in *; lia.
Qed.


End b.
End a.
