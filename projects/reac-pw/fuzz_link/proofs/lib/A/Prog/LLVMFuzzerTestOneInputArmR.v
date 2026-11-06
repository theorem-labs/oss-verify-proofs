(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 198 of its 257 lines of code are new or changed and 345 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...): the pieces that
   the two arms (op_read +0x608, op_unmark +0x6e8) share.
   - ar_leaf_call: one call of an own callee whose contract has link_amem.v's `aleaf_rd` shape, made with
     sp = lf_sp1 cx on the walk's journal: the contract's premises from the call's facts, and its post unpacked for
     the continuation.
   - ar_kept / ar_kagree: what a callee's `akept` keeps, as an exception set Keep.v's transport lemmas take.

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro PcapRelroA YC4b link_aro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputKeep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* lia over the arithmetic hypotheses only (lia has failed with "No applicable tactic" in the large contexts of
   these walks; clearing the non-arithmetic hypotheses first avoids it) *)
Ltac ar_is_arith T := lazymatch T with
  | ?A /\ ?B => ar_is_arith A; ar_is_arith B
  | ?A \/ ?B => ar_is_arith A; ar_is_arith B
  | ~ ?A => ar_is_arith A
  | @eq Z _ _ => idtac | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | @eq nat _ _ => idtac | le _ _ => idtac | lt _ _ => idtac
  | False => idtac | True => idtac
  | _ => fail end.
Ltac clia := repeat match goal with H : ?T |- _ =>
    lazymatch type of T with Prop => tryif ar_is_arith T then fail else clear H end end; lia.

(* presence growth as the run lemmas state it (also mark_quietlyDefs.v mem_grows_of_apresent) *)
Lemma ar_grows : forall (H : word -> bool) (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
  intros H m m' Hp x Hx. unfold mrestrict in Hx |- *. destruct (H x) eqn:Eh; [exact Hx|].
  destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
  assert (Ha : apresent H m (bv_unsigned x))
    by (unfold apresent; rewrite Z_to_bv_bv_unsigned; split; [exact Eh | exists b; exact Em]).
  destruct (Hp _ Ha) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

(* the argument registers a0 .. a5 *)
Lemma ar_aarg0 : forall regs, aarg regs 0 = bv_unsigned (getr regs 10).
Proof. intros regs. unfold aarg, argZ. replace (Z_to_bv 5 (10 + 0)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). reflexivity. Qed.
Lemma ar_aarg1 : forall regs, aarg regs 1 = bv_unsigned (getr regs 11).
Proof. intros regs. unfold aarg, argZ. replace (Z_to_bv 5 (10 + 1)) with (11%bv : bv 5) by (apply bv_eq; reflexivity). reflexivity. Qed.
Lemma ar_aarg2 : forall regs, aarg regs 2 = bv_unsigned (getr regs 12).
Proof. intros regs. unfold aarg, argZ. replace (Z_to_bv 5 (10 + 2)) with (12%bv : bv 5) by (apply bv_eq; reflexivity). reflexivity. Qed.
Lemma ar_aarg3 : forall regs, aarg regs 3 = bv_unsigned (getr regs 13).
Proof. intros regs. unfold aarg, argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity). reflexivity. Qed.
Lemma ar_aarg4 : forall regs, aarg regs 4 = bv_unsigned (getr regs 14).
Proof. intros regs. unfold aarg, argZ. replace (Z_to_bv 5 (10 + 4)) with (14%bv : bv 5) by (apply bv_eq; reflexivity). reflexivity. Qed.
Lemma ar_aarg5 : forall regs, aarg regs 5 = bv_unsigned (getr regs 15).
Proof. intros regs. unfold aarg, argZ. replace (Z_to_bv 5 (10 + 5)) with (15%bv : bv 5) by (apply bv_eq; reflexivity). reflexivity. Qed.

(* the callee-saved registers an aleaf post keeps *)
Lemma ar_pres : forall regs regs2 : bvmap 5 word, aregs_preserved regs regs2 ->
  getr regs2 2 = getr regs 2 /\ getr regs2 3 = getr regs 3 /\ getr regs2 4 = getr regs 4 /\
  getr regs2 8 = getr regs 8 /\ getr regs2 9 = getr regs 9 /\
  getr regs2 18 = getr regs 18 /\ getr regs2 19 = getr regs 19 /\ getr regs2 20 = getr regs 20 /\
  getr regs2 21 = getr regs 21 /\ getr regs2 22 = getr regs 22 /\ getr regs2 23 = getr regs 23 /\
  getr regs2 24 = getr regs 24 /\ getr regs2 25 = getr regs 25 /\ getr regs2 26 = getr regs 26 /\
  getr regs2 27 = getr regs 27.
Proof.
  intros regs regs2 H.
  assert (P : forall (r : bv 5) (z : Z), Z_to_bv 5 z = r -> acallee_saved z -> getr regs2 r = getr regs r)
    by (intros r z <- Hz; exact (H z Hz)).
  repeat split; (lazymatch goal with |- getr _ ?r = _ =>
    apply (P r (bv_unsigned r) ltac:(apply Z_to_bv_bv_unsigned)); unfold acallee_saved; vm_compute (bv_unsigned r); lia end).
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.

#[local] Abbreviation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

(* ==========================================================================
   0. Small facts of a call site
   ========================================================================== *)

Lemma ar_gp_tp : forall cx, BASEF cx ->
  getr (c_regs cx) 3 = w64 (as_gp B) /\ getr (c_regs cx) 4 = w64 (as_tp B).
Proof.
  intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (Hafn & _).
  destruct Hafn as (_ & _ & _ & Hgp & Htp & _). split; [exact Hgp | exact Htp].
Qed.

Lemma ar_relro_img : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Proof.
  intros a Ha. destruct pcap_relro_in_image as (s & Hin & H1 & H2 & H3).
  rewrite HSEGS. exists s. split; [exact Hin | lia].
Qed.

Lemma ar_not_ro_G : forall a, inG G_HARNESS a -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a.
Proof.
  intros a Ha. rewrite HSEGS. apply LA_G_not_ro. rewrite G_HARNESS_of_LA_G. unfold inG. apply Exists_cons_tl.
  exact Ha.
Qed.

Lemma ar_not_ro_high : forall a, kLowMemEnd <= a -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a.
Proof. intros a Ha. apply not_ro_high; [exact pa_segs_low | exact ar_relro_img | exact Ha]. Qed.

(* the side-stack room of a callee, with this call's frame the only one *)
Lemma ar_side_room : forall S3 fp SIDE, frames S3 = [(LF_CID, fp)] ->
  forallb (fun cd => count_cid (fst cd) [(LF_CID, 0)] + snd cd <=? fs_frames (fst cd)) SIDE = true ->
  aside_room S3 SIDE.
Proof.
  intros S3 fp SIDE Hfr H. unfold aside_room. rewrite Hfr. apply Forall_forall. intros cd Hin.
  rewrite forallb_forall in H. specialize (H cd Hin). apply Z.leb_le in H.
  replace (count_cid (fst cd) [(LF_CID, fp)]) with (count_cid (fst cd) [(LF_CID, 0)]) by reflexivity. exact H.
Qed.

(* the bytes a callee called on the walk's journal may write: the journal's own window, a harness global, a block
   the call allocated, the call's own side frame *)
Lemma ar_ajw_stack : forall cx fp ly3 S3 a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) ->
  ajw B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) ly3 S3
    [(LF_CID, fp)] a.
Proof. intros cx fp ly3 S3 a Ha. left. split; [left; exact Ha | lia]. Qed.

Lemma ar_ajw_G : forall cx fp ly3 S3 a, inG G_HARNESS a ->
  ajw B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) ly3 S3
    [(LF_CID, fp)] a.
Proof. intros cx fp ly3 S3 a Ha. right; left. exact Ha. Qed.

Lemma ar_ajw_blk : forall cx fp ly3 S3 b n a, In (b, n) (ablocks B ly3 S3) ->
  ~ In (b, n) (ablocks B (c_ly cx) (c_S cx)) -> b <= a < b + n ->
  ajw B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) ly3 S3
    [(LF_CID, fp)] a.
Proof.
  intros cx fp ly3 S3 b n a Hin Hout Ha. left. split; [|lia].
  right; right; left. exists b, n. split; [exact Hin|]. split; [exact Hout|].
  unfold req_size. destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia].
Qed.

Lemma ar_ajw_frame : forall cx fp ly3 S3 a, frame_addr ly3 LF_CID fp <= a < frame_addr ly3 LF_CID fp + fs_frame_bytes LF_CID ->
  (spZ (c_regs cx) <= a -> False) ->
  ajw B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) ly3 S3
    [(LF_CID, fp)] a.
Proof.
  intros cx fp ly3 S3 a Ha Hn. left. split; [|intros H; apply Hn; lia].
  right; right; right. exists LF_CID, fp. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* ==========================================================================
   1. A call of an aleaf_rd callee
   ========================================================================== *)

(* the realigned stack pointer's place, from lf_base and the journal *)
Lemma ar_sp1_facts : forall cx fp ly S W mem mdl k,
  BASEF cx -> JRN cx fp ly S W mem mdl k ->
  spZ (c_regs cx) - 432 <= lf_sp1 cx <= spZ (c_regs cx) - 416 /\ lf_sp1 cx mod 16 = 0 /\
  alloc_ceiling + LLVMF_STK - 432 <= lf_sp1 cx /\ spZ (c_regs cx) <= 2 ^ 47.
Proof.
  intros cx fp ly S W mem mdl k HB HJ.
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem mdl k
    HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (H0 : 0 <= spZ (c_regs cx) - LF_MFRAME).
  { unfold LF_MFRAME. unfold LLVMF_STK in Hceil. revert Hceil C1a. clear. intros. lia. }
  unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) H0 H16) as (R & _ & R16).
  unfold LF_MFRAME in R. unfold LLVMF_STK in *. lia.
Qed.

Lemma ar_leaf_call : forall (fy : YK11.FPState) pc K EV SIDE Pre Rd Wr Post,
  @aleaf_rd fy rc SK SEGS PCAP_RLO PCAP_RHI B pc K EV SIDE Pre Rd Wr Post ->
  forall cx fp ly3 S3 (W3 : world SEGS) memc mdc k (regs : bvmap 5 word) (Q : world SEGS -> config -> Prop),
  BASEF cx -> JRN cx fp ly3 S3 W3 memc mdc k ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W3) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  spZ regs = lf_sp1 cx -> 0 <= K <= LLVMF_STK - 448 ->
  0 <= EV -> k + EV <= EV_LIB ->
  aside_room S3 SIDE ->
  (forall a, inFP (Wr regs (rdW W3 memc)) a ->
     ajw B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) ly3 S3
       [(LF_CID, fp)] a) ->
  (forall a, inFP (Wr regs (rdW W3 memc)) a -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a) ->
  (forall a, Rd regs (rdW W3 memc) a -> akb SEGS B ly3 S3 (lf_sp1 cx - K) (lf_sp1 cx) a) ->
  Pre regs (rdW W3 memc) ->
  (forall (W2 : world SEGS) ly2 S2 (regs2 : bvmap 5 word) mem2 md2, wle W3 W2 ->
     JRN cx fp ly2 S2 W2 mem2 md2 (k + EV) ->
     aregs_preserved regs regs2 -> frames S2 = frames S3 ->
     m_fds md2 = m_fds mdc -> m_fs md2 = m_fs mdc ->
     akept SEGS B ly3 S3 W3 memc W2 mem2 (lf_sp1 cx - K) (lf_sp1 cx) (fun a => inFP (Wr regs (rdW W3 memc)) a) ->
     ashadow_kept SEGS B ly3 S3 ly2 S2 W3 memc W2 mem2 ->
     S2 = set_fs (st_fs S2) S3 -> Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
     Post regs (rdW W3 memc) regs2 (rdW W2 mem2) ->
     SRr SEGS W2 (mkCfg (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (@cfg_at fy SEGS pc regs memc mdc) Q.
Proof.
  intros fy pc K EV SIDE Pre Rd Wr Post CT cx fp ly3 S3 W3 memc mdc k regs Q HB HJ HRO Hra Hra4 Hgp Htp Hsp HK HEV
    Hev Hside Hajw Hnro Hrd Hpre Hk.
  eapply SRr_bind.
  { apply (CT G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 memc mdc k regs).
    - exact (lf_apre_at SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
        cx fp ly3 S3 W3 memc mdc k regs K EV SIDE (Wr regs (rdW W3 memc)) HB HJ HRO Hsp Hgp Htp Hra Hra4 HK HEV Hev
        Hside Hajw Hnro).
    - rewrite Hsp. exact Hrd.
    - exact Hpre. }
  cbv beta. intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hpr & Hfr & Hfd & Hfs & Hkp & Hsk
    & Hs2 & Hperm & Hpost).
  rewrite Hsp in Hkp.
  exact (Hk W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpr Hfr Hfd Hfs Hkp Hsk Hs2 Hperm Hpost).
Qed.

(* ==========================================================================
   2. The state clauses of a cut after a call that keeps the allocator (aleaf: S2 = set_fs _ S3, the block list a
      permutation): the memory clauses are carried by Keep.v's *_callee lemmas at ly3 S3; these re-state the
      state clauses at ly2 S2.
   ========================================================================== *)

Lemma ar_jbk_leaf : forall cx fp k2 ev mo wl lv ly3 S3 ly2 S2 (W2 : world SEGS) ms2 md2 T3 own k,
  BASEF cx -> JRN cx fp ly2 S2 W2 (ms_mem ms2) md2 k ->
  S2 = set_fs (st_fs S2) S3 -> Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W2 ms2 md2 T3 own ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly2 S2 W2 ms2 md2 T3 own.
Proof.
  intros cx fp k2 ev mo wl lv ly3 S3 ly2 S2 W2 ms2 md2 T3 own k HB HJ2 Hs2 Hperm
    (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & (D & HT & HP) & J12 & J13 & J14 & J15 & J16).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MFL).
  assert (Hfa : forall c q, frame_addr ly2 c q = frame_addr (c_ly cx) c q) by (eapply aj_frame_addr; exact HJ2).
  refine (conj J1 (conj _ (conj _ (conj J4 (conj J5 (conj J6 (conj _ (conj _ (conj J9 (conj J10
    (conj _ (conj _ (conj J13 (conj J14 (conj J15 J16))))))))))))))).
  - rewrite Hs2. exact J2.
  - intros c q. rewrite Hfa. reflexivity.
  - rewrite Hs2. apply (mo_le_set_fs_r _ MFL). exact J7.
  - rewrite Hs2. exact J8.
  - exists D. split; [exact HT|]. exact (Permutation_trans Hperm HP).
  - intros x Hx. apply (Permutation_in x (Permutation_sym Hperm)). exact (J12 x Hx).
Qed.

Lemma ar_blocks_leaf : forall cx md mk T3 ly3 S3 ly2 S2 m,
  Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
  lf_blocks B cx md mk T3 ly3 S3 m -> lf_blocks B cx md mk T3 ly2 S2 m.
Proof.
  intros cx md mk T3 ly3 S3 ly2 S2 m Hperm (B1 & B2 & Brest).
  split; [exact (Permutation_in _ (Permutation_sym Hperm) B1)|].
  split; [exact (Permutation_in _ (Permutation_sym Hperm) B2) | exact Brest].
Qed.

(* ==========================================================================
   3. Closing a region's write window after a run (so later runs write nothing)
   ========================================================================== *)

Lemma ar_close1 : forall (fy : YK11.FPState) E ss (ms : machine_state) i r,
  st_ok_pi (fx := fy) SEGS pa_val E ss ms -> nth_error (ss_mem ss) i = Some r ->
  regions_wf (list_upd (ss_mem ss) i (set_window r 0 0)) = true ->
  st_ok_pi (fx := fy) SEGS pa_val E
    (mkSS (ss_pc ss) (ss_regs ss) (list_upd (ss_mem ss) i (set_window r 0 0)) (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros fy E ss ms i r HS Hn Hw. apply (ast_ok_pi_set_region E ss ms i r _ HS Hn); [reflexivity | exact Hw|].
  apply region_ok_rewindow; [exact (st_ok_pi_region_nth E ss ms i r HS Hn)|]. intros o Ho. lia.
Qed.

Definition ar_nowin (rs : smem) : bool := forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs.

Lemma ar_nowin_in : forall E rs a, ar_nowin rs = true -> ~ in_wrange E rs a.
Proof.
  intros E rs a H (r & Hr & Ha). unfold ar_nowin in H. rewrite forallb_forall in H.
  specialize (H r Hr). apply Z.leb_le in H. lia.
Qed.

Lemma ar_awr_nowin : forall E rs G XO OUT STK sp0 FP bl0 blc ly own,
  ar_nowin rs = true -> awr_ok_x E rs G XO OUT STK sp0 FP bl0 blc ly own.
Proof. intros E rs G XO OUT STK sp0 FP bl0 blc ly own H a Ha. exfalso. exact (ar_nowin_in E rs a H Ha). Qed.

Lemma ar_kagree_nowin : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> ar_nowin rs = true -> kagree SEGS (fun _ => False) m m'.
Proof.
  intros E rs m m' HF H a _. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  exact (ar_nowin_in E rs _ H).
Qed.

End b.
End a.
