(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AProto. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_asetshadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

#[using="Type"] Lemma poison_cells_of_art : forall m : amem, artcells m -> rw_cells asegs m GOT_MEMSET [C8 (Z_to_bv 64 0xa7360)] -> poison_cells m.
Proof.
  intros m ART GM. unfold artcells in ART. (nd_pre ART 14%nat; intros _ A2 _ A4 A5 _ _ A8 A9 _ _ _ A13 _; nd_post).
  unfold poison_cells, GOT_MEMSET in *. repeat (split; [assumption|]). assumption.
Qed.

#[using="Type"] Lemma set_shadow_post_o : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m : amem) (lo SA n v : Z) ms',
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> 0 < n -> 0 <= v < 256 ->
  set_shadow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SA n v m ms' ->
  exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
    /\ munch [(bv_unsigned sp - FAKE_STACK, bv_unsigned sp); (SA, SA + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' SA [CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n))].
Proof.
  intros until ms'. intros ST LO N0 V0 PO. unfold set_shadow_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MU WM MI DST; nd_post).
  eexists _, _. split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
  split. { eapply munch_weaken; [| exact MU]. apply sub_fp_by_incl'. apply Forall_cons; [apply Exists_cons_tl; apply Exists_cons_hd; cbn [fst snd]; lia| apply Forall_nil]. }
  split; [exact WM|]. split; [exact MI|]. split; [| exact DST].
  eapply stk_transport; [exact ST| exact MU| exact WM|]. intros xa Hx. pose proof atop_range as AR.
  destruct (Z_lt_ge_dec xa SA) as [LT|GE]; [left; cbn [outside]; split; [lia| exact I]|].
  destruct (Z_lt_ge_dec xa (SA + n)) as [LT2|GE2]; [| left; cbn [outside]; split; [lia| exact I]].
  right. destruct DST as [[_ B] _]. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. (nd_pre B 3%nat; intros B0 B1 B; nd_post).
  rewrite repeat_length in B1, B. specialize (B (Z.to_nat (xa - SA)) ltac:(lia)). rewrite Z2Nat.id in B by lia.
  replace (SA + (xa - SA)) with xa in B by lia. rewrite (nth_error_repeat (Z_to_bv 8 v)) in B by lia.
  exists (Z_to_bv 8 v). rewrite <- B. symmetry. apply ref_mrd_overlay. right. (nd_pre ST 3%nat; intros S0 S1 _; nd_post). rewrite wa_unsigned by lia. lia.
Qed.

#[using="Type"] Theorem set_shadow_00_inst : set_shadow_stmt 0x58268 0x00.
Proof.
  red. intros until old. intros MI ST BU LO ART GM Ea0 Ea1 SA0 Hn OLD RSA RSTK RIMG.
  eapply evtF_mono.
  - eapply (set_shadow_00_spec RNG); [exact MI| exact (poison_cells_of_art m ART GM)| exact Ea0| exact Ea1| exact SA0| lia| exact OLD| exact RIMG| exact RSA].
  - cbv beta. intros ms' PO. eapply set_shadow_post_o; [exact ST| exact LO| lia| lia| exact PO].
Qed.

#[using="Type"] Theorem set_shadow_f8_inst : set_shadow_stmt 0x58388 0xf8.
Proof.
  red. intros until old. intros MI ST BU LO ART GM Ea0 Ea1 SA0 Hn OLD RSA RSTK RIMG.
  eapply evtF_mono.
  - eapply (set_shadow_f8_spec RNG); [exact MI| exact (poison_cells_of_art m ART GM)| exact Ea0| exact Ea1| exact SA0| lia| exact OLD| exact RIMG| exact RSA].
  - cbv beta. intros ms' PO. eapply set_shadow_post_o; [exact ST| exact LO| lia| lia| exact PO].
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_asetshadow.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

#[using="Type"] Lemma poison_cells_of_art : forall m : amem, artcells m -> rw_cells asegs m GOT_MEMSET [C8 (Z_to_bv 64 0xa7740)] -> poison_cells m.
Proof.
  intros m ART GM. unfold artcells in ART. (nd_pre ART 14%nat; intros _ A2 _ A4 A5 _ _ A8 A9 _ _ _ A13 _; nd_post).
  unfold poison_cells, GOT_MEMSET in *. repeat (split; [assumption|]). assumption.
Qed.

#[using="Type"] Lemma set_shadow_post_o : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m : amem) (lo SA n v : Z) ms',
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> 0 < n -> 0 <= v < 256 ->
  set_shadow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SA n v m ms' ->
  exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
    /\ munch [(bv_unsigned sp - FAKE_STACK, bv_unsigned sp); (SA, SA + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' SA [CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n))].
Proof.
  intros until ms'. intros ST LO N0 V0 PO. unfold set_shadow_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MU WM MI DST; nd_post).
  eexists _, _. split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
  split. { eapply munch_weaken; [| exact MU]. apply sub_fp_by_incl'. apply Forall_cons; [apply Exists_cons_tl; apply Exists_cons_hd; cbn [fst snd]; lia| apply Forall_nil]. }
  split; [exact WM|]. split; [exact MI|]. split; [| exact DST].
  eapply stk_transport; [exact ST| exact MU| exact WM|]. intros xa Hx. pose proof atop_range as AR.
  destruct (Z_lt_ge_dec xa SA) as [LT|GE]; [left; cbn [outside]; split; [lia| exact I]|].
  destruct (Z_lt_ge_dec xa (SA + n)) as [LT2|GE2]; [| left; cbn [outside]; split; [lia| exact I]].
  right. destruct DST as [[_ B] _]. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. (nd_pre B 3%nat; intros B0 B1 B; nd_post).
  rewrite repeat_length in B1, B. specialize (B (Z.to_nat (xa - SA)) ltac:(lia)). rewrite Z2Nat.id in B by lia.
  replace (SA + (xa - SA)) with xa in B by lia. rewrite (nth_error_repeat (Z_to_bv 8 v)) in B by lia.
  exists (Z_to_bv 8 v). rewrite <- B. symmetry. apply ref_mrd_overlay. right. (nd_pre ST 3%nat; intros S0 S1 _; nd_post). rewrite wa_unsigned by lia. lia.
Qed.

#[using="Type"] Theorem set_shadow_00_inst : set_shadow_stmt 0x582d0 0x00.
Proof.
  red. intros until old. intros MI ST BU LO ART GM Ea0 Ea1 SA0 Hn OLD RSA RSTK RIMG.
  eapply evtF_mono.
  - eapply (set_shadow_00_spec RNG); [exact MI| exact (poison_cells_of_art m ART GM)| exact Ea0| exact Ea1| exact SA0| lia| exact OLD| exact RIMG| exact RSA].
  - cbv beta. intros ms' PO. eapply set_shadow_post_o; [exact ST| exact LO| lia| lia| exact PO].
Qed.

#[using="Type"] Theorem set_shadow_f8_inst : set_shadow_stmt 0x583f0 0xf8.
Proof.
  red. intros until old. intros MI ST BU LO ART GM Ea0 Ea1 SA0 Hn OLD RSA RSTK RIMG.
  eapply evtF_mono.
  - eapply (set_shadow_f8_spec RNG); [exact MI| exact (poison_cells_of_art m ART GM)| exact Ea0| exact Ea1| exact SA0| lia| exact OLD| exact RIMG| exact RSA].
  - cbv beta. intros ms' PO. eapply set_shadow_post_o; [exact ST| exact LO| lia| lia| exact PO].
Qed.
End CANSEC1.
End TwB.
