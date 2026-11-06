(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepS3d), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACgb.v. *)
(* The call of check_groupa (fuzz_grant.c:116) that both group-A loops of the sweep
   phase make (0x810a8 and 0x8118c): from a cut's facts to the callee's contract and
   back. Shared by GrantEntrySweepS3a.v and GrantEntrySweepS3b.v. *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YC5d YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase GrantRo GrantEntryDefs GrantEntrySweepDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
GrantFrame YC1g YC1h YC1i YC88 YC85 GrantEntrySweepS3c HeadampTxEffective CheckGroupa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel SweepRowCheck GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
Context {RO : ro_below_ofl (@pa_segs _ grant_listing PI) (@pa_relro_lo _ grant_listing PI) (@pa_relro_hi _ grant_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* The head-amp table a cut tracks is the object check_groupa's contract reads
   (HeadampTxEffective.v tx_obj_bytes: the layout names every byte but 438, 439, 451). *)
Lemma gtab_obj : forall cx ly S W ms t T, gtab B cx ly S W ms t T ->
  obj_at SEGS (mrestrict (w_H W) (ms_mem ms)) t LAY_TX (tx_vals T).
Proof.
  intros cx ly S W ms t T (_ & _ & _ & HB). apply (proj2 (tx_obj_bytes SEGS _ _ _)). intros i Hi.
  pose proof (tx_fbyte_range i Hi) as Hr.
  assert (H438 : i <> 438) by (intros ->; vm_compute in Hi; discriminate Hi).
  assert (H439 : i <> 439) by (intros ->; vm_compute in Hi; discriminate Hi).
  assert (H451 : i <> 451) by (intros ->; vm_compute in Hi; discriminate Hi).
  destruct (val_mem1_of_aview SEGS _ _ _ _ (HB i Hr H438 H439 H451)) as [Hvm Hr8].
  specialize (Hvm 0%nat ltac:(lia)). cbn [Z.of_nat] in Hvm. rewrite Z.add_0_r in Hvm. rewrite Hvm.
  f_equal. rewrite le_byte_1_0 by exact Hr8. apply tb_nth.
Qed.

(* One call of check_groupa(row, ch, p, t, eff T t ch p) from the realigned stack
   pointer, on a row the sweep holds: the journal grows, the blocks and frames stay,
   the callee-saved registers are kept, and so is every byte the cuts name. *)
Lemma gsw_cga : AR_laws SEGS B -> tcheck_groupa_spec B ->
  forall cx fp k ly3 S3 W3 (regsT : bvmap 5 word) memT mdT ret t s row ch p,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 memT mdT k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  gsw_blk B cx fp ly3 S3 W3 (mkst regsT (Z_to_bv 64 0) memT (seg_rom SEGS)) t s ->
  getr regsT 2 = w64 (c_sp1 cx) -> getr regsT 3 = getr (c_regs cx) 3 -> getr regsT 4 = getr (c_regs cx) 4 ->
  getr regsT 8 = w64 (spZ (c_regs cx)) ->
  getr regsT 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  getr regsT 10 = w64 row -> getr regsT 11 = w64 ch -> getr regsT 12 = w64 p -> getr regsT 13 = w64 t ->
  getr regsT 14 = w64 (eff (T_end (c_pl cx)) t ch p) ->
  0 <= ch < 48 -> 0 <= p < 3 -> s <= row -> row + 34 <= s + sw_mbytes (c_pl cx) ->
  garr8 SEGS (mrestrict (w_H W3) memT) row (GAz ch p (eff (T_end (c_pl cx)) t ch p)) ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA GS_check_groupa)) memT (seg_rom SEGS)) mdT)
    (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
         [(GE_CID, fp)] ly2 S2 W2 mem2 md2 k /\
       YG01.frames S2 = YG01.frames S3 /\ ablocks B ly2 S2 = ablocks B ly3 S3 /\ (exists f, S2 = set_fs f S3) /\
       aregs_preserved regsT regs2 /\ vkeep (gsw_out cx fp t s) W3 memT W2 mem2).
Proof.
  intros LAWS TCG cx fp k ly3 S3 W3 regsT memT mdT ret t s row ch p HB HJ HFR HBLK R2 R3 R4 R8 R1 Hret Hret2 H8 H16
    R10 R11 R12 R13 R14 Rch Rp Hr1 Hr2 HROW.
  destruct (gsw_base_facts B MT cx HB) as (HPRE & HROD0 & Hsp1 & _).
  pose proof HPRE as (_ & _ & _ & Hgp & Htp & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2) & _).
  pose proof HBLK as (Hab & Hins & HTAB & _).
  pose proof HTAB as (Hint & Ht0 & HTl & _).
  pose proof HJ as (_ & Hly & _).
  assert (Etop : ly_top ly3 = ly_top (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _); exact Etop).
  pose proof (@alloc_ceiling_value rc) as HAC. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof (Z.div_mod (spZ (c_regs cx) + -288) 32 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -288) 32 ltac:(lia)) as Hm.
  unfold GE_STK in *.
  assert (USP : spZ regsT = c_sp1 cx) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
  assert (Ho : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0).
  { pose proof (Z.div_mod (spZ (c_regs cx)) 16 ltac:(lia)) as D2. rewrite Hal16 in D2.
    rewrite Hsp1. replace (32 * ((spZ (c_regs cx) + -288) / 32) - spZ (c_regs cx))
      with ((2 * ((spZ (c_regs cx) + -288) / 32) - spZ (c_regs cx) / 16) * 16) by lia.
    apply Z_mod_mult. }
  assert (HTCG : TCG_STK = 8496) by reflexivity.
  rewrite (pa_xcalls GS_check_groupa AF_check_groupa ltac:(unfold grant_xcalls; in_tac)).
  eapply SRr_mono.
  { apply (cl_callS B LAWS W3 regsT memT _ 32768 (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(GE_CID, fp)] ly3 S3 mdT k TCG_STK [] 0 (c_sp1 cx - spZ (c_regs cx)) (getr regsT 1) (gch cx)
      (fun ly' S' W' regs' mem' md' => YG01.frames S' = YG01.frames S3 /\ ablocks B ly' S' = ablocks B ly3 S3 /\
         (exists f, S' = set_fs f S3)) HJ).
    - rewrite USP. lia.
    - exact Ho.
    - lia.
    - rewrite HTCG. lia.
    - rewrite HTCG. lia.
    - rewrite R3. exact Hgp.
    - rewrite R4. exact Htp.
    - reflexivity.
    - rewrite R1. apply ret_ok_codeptr_v; assumption.
    - rewrite R1, unsigned_lit_small by lia. lia.
    - replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
      apply (gsw_achain B MT cx fp k ly3 S3 W3 memT mdT regsT HB HJ R8 H8 H16). lia.
    - intros HPRE'.
      apply (TCG ly3 S3 W3 regsT memT mdT (gch cx) row ch p t s (sw_mbytes (c_pl cx)) (T_end (c_pl cx)) HPRE').
      + rewrite HFR. cbn. lia.
      + rewrite USP, Etop. lia.
      + exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD0).
      + exact R10.
      + exact R11.
      + exact R12.
      + exact R13.
      + exact R14.
      + exact Rch.
      + exact Rp.
      + unfold TX_SIZE. exact Hint.
      + exact HTl.
      + exact (gtab_obj cx ly3 S3 W3 _ t _ HTAB).
      + exact Hins.
      + exact Hr1.
      + exact Hr2.
      + exact HROW.
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ1 & HP & (Hfr2 & Hab2 & Hfs)).
  exists ly2, S2, regs2, mem2, md2.
  split; [rewrite R1; reflexivity|]. split; [rewrite Z.add_0_r in HJ2; exact HJ2|].
  split; [exact Hfr2|]. split; [exact Hab2|]. split; [exact Hfs|]. split; [exact HP|].
  replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HJ1 by lia.
  apply (vkeep_callee B MT cx fp k ly3 S3 W3 memT mdT t s TCG_STK ly2 S2 W2 mem2 md2 0 HB HJ HFR Hab Hab2);
    [rewrite HTCG; unfold GE_STK in *; lia | exact LAWS | exact HJ1].
Qed.

End c.
End b.
End a.
