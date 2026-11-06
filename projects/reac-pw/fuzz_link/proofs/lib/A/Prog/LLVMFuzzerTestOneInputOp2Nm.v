(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 361 of its 425 lines of code are new or changed and 340 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputDec.v; 421 of its 544 lines of code are new or changed and 302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputMq.v; 75 of its 132 lines of code are new or changed and 487 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...), the op_mark arm:
   the facts of the name the selector picked (Sel.v w_name: g_names + 8 k, or odd[j]) at any state of the walk.
   The g_names part follows Mq.v mq_tab_rt (lf_gnames_at and AR's zero shadow of g_names), the
   odd part Mq.v mq_rt_kstr over Sel.v's image booleans (kp_kstr_b of the six odd strings).

   o2_name_rt: the string, astr_rt_ok at a call whose window is above the allocator's ceiling, where it lies.

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom AF0m AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputSu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
  model_decide_c remember_c reac_code_emit_c reac_served_mark_c mark_quietly_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputMq LLVMFuzzerTestOneInputSel
  LLVMFuzzerTestOneInputMdl LLVMFuzzerTestOneInputSu LLVMFuzzerTestOneInputGl LLVMFuzzerTestOneInputKeep
  LLVMFuzzerTestOneInputKpre.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.

(* a prefix of a byte list *)
Lemma o2_abytes_prefix : forall (m : word -> option byte) a l1 l2, abytes SEGS m a (l1 ++ l2) -> abytes SEGS m a l1.
Proof.
  intros m a l1 l2 (H0 & H1 & H2). rewrite length_app in H1. split; [exact H0|]. split; [lia|].
  intros i Hi. rewrite (H2 i ltac:(rewrite length_app; lia)). rewrite nth_error_app1 by exact Hi. reflexivity.
Qed.

Lemma o2_name_rt : forall ly S (W : world SEGS) mem mdl (regs : bvmap 5 word) K s t,
  AR SEGS B ly S W mem mdl ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_gnames_at 64 (rdW W mem) ->
  alloc_ceiling <= spZ regs - K ->
  w_name s (Some t) ->
  acstr_at SEGS (rdW W mem) s t /\ astr_rt_ok SEGS regs K (rdW W mem) s t /\ 0x10000 <= s /\
  (length t <= 11)%nat /\
  (s + Z.of_nat (length t) + 8 <= LA_G_NL \/ (LA_G_NAMES <= s /\ s + 8 <= LA_G_NAMES + G_NAMES_SIZE)).
Proof.
  intros ly S W mem mdl regs K s t HAR HRO Hgn HK Hw.
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof HAR as (M & _).
  destruct Hw as [(Hs0 & Hn) | [(k & Hk & Es & En) | (j & Hj & Es & En)]]; [discriminate Hn | |].
  - (* g_names + 8 k *)
    injection En as ->. subst s.
    destruct (lf_zsh_gnames_rd B TB ly S _ M) as (Gra & Ghv).
    pose proof (lf_gname_len k ltac:(lia)) as Hl4.
    pose proof (gl_gname_nz k ltac:(lia)) as Hnz.
    destruct (Hgn k Hk) as (rest & Hab & Hlen8).
    assert (Hac : acstr_at SEGS (rdW W mem) (LA_G_NAMES + 8 * k) (lf_gname k)).
    { split; [|exact Hnz]. apply (o2_abytes_prefix _ _ _ rest). rewrite <- app_assoc. exact Hab. }
    split; [exact Hac|].
    split.
    + unfold astr_rt_ok. unfold LA_G_NAMES in *.
      split; [lia|]. split; [lia|].
      split; [unfold amem_range, kLowMemEnd; left; lia|].
      split; [rewrite ard_aview; apply (lf_ra_sub _ 0x62fac0 512); [exact Gra | lia | lia]|].
      split; [rewrite ard_aview; apply (lf_hull_sub _ 0x62fac0 512); [exact Ghv | lia | lia | lia | lia]|].
      split.
      * intros b Hb. assert (Hpm : (0x62fac0 + 8 * k + Z.of_nat (length (lf_gname k))) mod 8 =
          Z.of_nat (length (lf_gname k))) by lia.
        destruct Hab as (_ & _ & Hab).
        assert (Hbi : (Z.to_nat (b - (0x62fac0 + 8 * k)) < length (lf_gname k ++ Z_to_bv 8 0 :: rest))%nat)
          by (rewrite Hlen8; lia).
        pose proof (Hab _ Hbi) as Hbb.
        rewrite Z2Nat.id in Hbb by lia.
        replace (0x62fac0 + 8 * k + (b - (0x62fac0 + 8 * k))) with b in Hbb by lia.
        destruct (nth_error_Some (lf_gname k ++ Z_to_bv 8 0 :: rest) (Z.to_nat (b - (0x62fac0 + 8 * k)))) as [_ Hs].
        specialize (Hs Hbi).
        unfold ard. rewrite Hbb.
        destruct (nth_error (lf_gname k ++ Z_to_bv 8 0 :: rest) (Z.to_nat (b - (0x62fac0 + 8 * k)))) as [x|] eqn:Ex;
          [cbn [option_map]; discriminate | exfalso; apply Hs; reflexivity].
      * unfold apart_frame. left. lia.
    + split; [unfold LA_G_NAMES; lia|]. split; [lia|]. right. unfold LA_G_NAMES, G_NAMES_SIZE; lia.
  - (* odd[j] *)
    pose proof (sel_img_here B TB HSEGS) as KI. unfold sel_img_b in KI.
    repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
    pose proof (kp_forallb_seq _ _ KI j Hj) as Hx. cbv beta zeta in Hx. apply andb_prop in Hx as [_ Hks].
    assert (Hp : s = fst (nth j KP_ODD (0, []))) by (rewrite Es; unfold ODD_PTRS; rewrite (map_nth fst KP_ODD (0, [])); reflexivity).
    rewrite <- Hp in Hks.
    assert (Et : t = nth j lf_odd_strs []) by congruence. subst t. rewrite (sel_odd_strs j Hj).
    destruct (mq_rt_kstr B TB ly S W mem mdl regs K s _ HAR HRO Hks ltac:(unfold LA_G_NL; lia)) as (Hac & Hrt).
    destruct (kp_kstr_acstr B (w_H W) mem s _ HRO Hks) as (_ & Hp0 & Hpl).
    split; [exact Hac|]. split; [exact Hrt|].
    assert (Hl : (length (snd (nth j KP_ODD (0%Z, []))) <= 11)%nat /\ 0x10000 <= fst (nth j KP_ODD (0%Z, []))).
    { do 6 (destruct j as [|j]; [cbn; lia|]). lia. }
    rewrite length_map. split; [rewrite Hp; lia|]. split; [lia|]. left. lia.
Qed.

(* the name's bytes and its NUL are image bytes no owned static and no errno byte covers (the read sets' `akb`) *)
Lemma o2_name_img : forall MS la_nul s t, MS = link_amf -> la_nul = LA_NUL -> w_name s (Some t) ->
  forall x, s <= x < s + Z.of_nat (length t) + 1 ->
  in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4).
Proof.
  intros MS la_nul s t HMS HLN Hw x Hx.
  destruct Hw as [(Hs0 & Hn) | [(k & Hk & Es & En) | (j & Hj & Es & En)]]; [discriminate Hn | |].
  - assert (Et : t = lf_gname k) by congruence. subst t s.
    pose proof (lf_gname_len k ltac:(lia)) as Hl4.
    destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & _).
    apply IMG. right; left. unfold LA_G_NAMES, G_NAMES_SIZE in *. lia.
  - pose proof (sel_img_here B TB HSEGS) as KI. unfold sel_img_b in KI.
    repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
    pose proof (kp_forallb_seq _ _ KI j Hj) as Hxj. cbv beta zeta in Hxj. apply andb_prop in Hxj as [_ Hks].
    assert (Hp : s = fst (nth j KP_ODD (0, []))) by (rewrite Es; unfold ODD_PTRS; rewrite (map_nth fst KP_ODD (0, [])); reflexivity).
    assert (Et : t = nth j lf_odd_strs []) by congruence. subst t. rewrite (sel_odd_strs j Hj) in Hx.
    rewrite length_map in Hx. rewrite <- Hp in Hks.
    unfold kp_kstr_b in Hks.
    repeat match type of Hks with (_ && _)%bool = true => apply andb_prop in Hks as [Hks ?] end.
    match goal with Hh : kp_bytes_b _ _ _ _ _ = true |- _ => rename Hh into Hby end.
    pose proof (kp_bytes_place B HSEGS _ _ Hby (Z.to_nat (x - s))) as Hr. rewrite length_app in Hr. cbn [length] in Hr.
    specialize (Hr ltac:(lia)). replace (s + Z.of_nat (Z.to_nat (x - s))) with x in Hr by lia. exact Hr.
Qed.

End k.
