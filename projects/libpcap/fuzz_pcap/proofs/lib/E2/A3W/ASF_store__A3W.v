(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From Stdlib Require Sorting.Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead F_afree_tail.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_read.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_arep__A3W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ASF_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead F_afree_tail. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_read. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.AFreeStoreK OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation WfS sp t UB gq nodes store lst eb gl :=
  ([(sp - 4096, sp); (0xab308, 0xab330); (0xaf800, 0x130830); (0x13e088, 0x13e08c); (ADEPOT_LO, ADEPOT_HI);
    (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792); (t + 2800, t + 3169);
    (UB - 16, UB + 8); (shad UB, shad UB + gq);
    (nodes, nodes + 1048576); (store, store + 8388608);
    (lst, lst + qsz lst); (eb, eb + qsz eb); (gl, gl + 8)]%Z) (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : ABase.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.
(* [comment removed for export] *)
Local Ltac band_int_k H L U :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (first [ solve [clear - L U; atop_facts; lia] | atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia ]);
      assert (G2 : a + n <= 18446744073709551616) by (first [ solve [clear - L U; atop_facts; lia] | atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia ]);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (first [ solve [clear - L U; atop_facts; lia] | atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia ]);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | _ => band_int H
  end.

(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := solve [fu_focus; lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6303744 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6303744 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Section Kinds.
Variables (sp t mb msz UB gq nodes store res ctx lo lst eb gl : Z).
(* [comment removed for export] *)
Definition kfactsS : Prop :=
     (ATOP <= lo /\ lo <= sp - 4096)
  /\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)
  /\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)
  /\ (ablk mb (mb + msz) /\ mb + 6144 = UB /\ UB + 8 <= mb + msz /\ mb + msz <= ATOP
      /\ (mb + msz <= t \/ t + 4096 <= mb) /\ (mb + msz <= res \/ res + 137439023104 <= mb)
      /\ (mb + msz <= nodes \/ nodes + 1048576 <= mb) /\ (mb + msz <= store \/ store + 8388608 <= mb))
  /\ (2148238848 <= shad mb /\ shad UB = shad mb + 768 /\ 1 <= gq /\ shad UB + gq <= shad mb + msz / 8
      /\ shad mb + msz / 8 <= 17594332446720)
  /\ (sclr nodes 1048576 /\ 6303744 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6303744 <= store /\ store + 8388608 <= ATOP)
  /\ (sclr ctx 65536 /\ 6303744 <= ctx /\ ctx + 65536 <= ATOP)
  /\ ((lst = 0 /\ qsz lst = 8) \/ (res + 4096 <= lst /\ lst + 8192 <= res + 137439023104 /\ qsz lst = 8192))
  /\ ((eb = 0 /\ qsz eb = 8) \/ (res + 4096 <= eb /\ eb + 8192 <= res + 137439023104 /\ qsz eb = 8192))   (* [comment removed for export] *)
  /\ (gl = 0 \/ (res + 4096 <= gl /\ gl + 8192 <= res + 137439023104)).
Hypothesis KF : kfactsS.

(* [comment removed for export] *)
Ltac kind16 tstack timg tt tch tsh tns tlst teb tgl :=
  cbn [disjoint_from];
  split; [tstack|]; split; [timg|]; split; [timg|]; split; [timg|]; split; [timg|];
  split; [tt|]; split; [tt|]; split; [tt|]; split; [tt|];
  split; [tch|]; split; [tsh|]; split; [tns|]; split; [tns|]; split; [tlst|]; split; [teb|]; split; [tgl|]; exact I.
Ltac kfacts := pose proof KF as KF'; unfold kfactsS, AIMG_HI in *;
  sg_set; (nd_pre KF' 10%nat; intros F_lo sgk1 F_res sgk2 F_sh sgk3 sgk4 F_lst F_eb F_gl; nd_post); (nd_pre sgk1 4%nat; intros Ft1 Ft2 Ft3 Ft4; nd_post); (nd_pre sgk2 8%nat; intros C1 C2 C3 C4 C5 C6 C7 C8; nd_post); (nd_pre sgk3 6%nat; intros Fn1 Fn2 Fn3 Fs1 Fs2 Fs3; nd_post); (nd_pre sgk4 3%nat; intros Fc1 Fc2 Fc3; nd_post);
  band_int_k Ft1 Ft3 Ft4; band_int_k Ft2 Ft3 Ft4; band_int_k Fn1 Fn2 Fn3; band_int_k Fs1 Fs2 Fs3; band_int_k Fc1 Fc2 Fc3; band_int C1; clear Ft1 Ft2 Fn1 Fs1 Fc1 C1; sg_unset.   (* [comment removed for export] *)

#[using="rc tlsI mb msz res ctx lo KF"] Lemma KS_img : forall A k, 0x10000 <= A -> 0 <= k ->
  (A + k <= ADEPOT_LO /\ (A + k <= 0xab308 \/ 0xab330 <= A) /\ (A + k <= 0xaf800 \/ 0x130830 <= A) /\ (A + k <= 0x13e088 \/ 0x13e08c <= A))
  \/ (ADEPOT_HI <= A /\ A + k <= AIMG_HI) ->
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros A k HA HK HD. kfacts.
  kind16 ltac:(clear -HA HK HD F_lo; lia) ltac:(clear -HA HK HD; lia) ltac:(clear -HA HK HD Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2; lia) ltac:(clear -HA HK HD C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1; lia)
         ltac:(clear -HA HK HD C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1 F_sh; lia) ltac:(clear -HA HK HD Fn2 Fn3 KAFn1 KBFn1 KCFn1 Fs2 Fs3 KAFs1 KBFs1 KCFs1; lia)
         ltac:(clear -HA HK HD F_lst F_res; lia) ltac:(clear -HA HK HD F_eb F_res; lia) ltac:(clear -HA HK HD F_gl F_res; lia).
Qed.

#[using="rc tlsI mb msz res ctx lo KF"] Lemma KS_low : forall A k, 2147450880 <= A -> A + k <= 2148238848 -> 0 <= k ->      (* [comment removed for export] *)
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros A k HA HB HK. kfacts.
  kind16 ltac:(clear -HA HB HK F_lo; lia) ltac:(clear -HA HB HK; lia) ltac:(clear -HA HB HK Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2; lia) ltac:(clear -HA HB HK C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1; lia)
         ltac:(clear -HA HB HK C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1 F_sh; lia) ltac:(clear -HA HB HK Fn2 Fn3 KAFn1 KBFn1 KCFn1 Fs2 Fs3 KAFs1 KBFs1 KCFs1; lia)
         ltac:(clear -HA HB HK F_lst F_res; lia) ltac:(clear -HA HB HK F_eb F_res; lia) ltac:(clear -HA HB HK F_gl F_res; lia).
Qed.

#[using="rc tlsI mb msz res ctx lo KF"] Lemma KS_hi : forall A k, sp <= A -> 0 <= k ->
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros A k HA HK. kfacts.
  kind16 ltac:(clear -HA HK; lia) ltac:(clear -HA HK F_lo; lia) ltac:(clear -HA HK F_lo Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2; lia) ltac:(clear -HA HK F_lo C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1; lia)
         ltac:(clear -HA HK F_lo C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1 F_sh; lia) ltac:(clear -HA HK F_lo Fn2 Fn3 KAFn1 KBFn1 KCFn1 Fs2 Fs3 KAFs1 KBFs1 KCFs1; lia)
         ltac:(clear -HA HK F_lo F_lst F_res; lia) ltac:(clear -HA HK F_lo F_eb F_res; lia) ltac:(clear -HA HK F_lo F_gl F_res; lia).
Qed.

#[using="rc tlsI mb msz res ctx lo KF"] Lemma KS_shad : forall A k, 2147446784 <= A -> A + k <= 17594333495296 -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= shad UB \/ shad UB + gq <= A) ->
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros A k HA HB HK HD. kfacts.
  kind16 ltac:(clear -HA HB HK F_lo; lia) ltac:(clear -HA HB HK; lia) ltac:(clear -HA HB HK Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2; lia) ltac:(clear -HA HB HK C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1; lia)
         ltac:(clear -HA HB HK HD; lia) ltac:(clear -HA HB HK Fn2 Fn3 KAFn1 KBFn1 KCFn1 Fs2 Fs3 KAFs1 KBFs1 KCFs1; lia)
         ltac:(clear -HA HB HK F_lst F_res; lia) ltac:(clear -HA HB HK F_eb F_res; lia) ltac:(clear -HA HB HK F_gl F_res; lia).
Qed.

#[using="rc tlsI lo KF"] Lemma KS_ctx :
  (ctx + 65536 <= t \/ t + 4096 <= ctx) -> (ctx + 65536 <= res \/ res + 137439023104 <= ctx) ->
  (ctx + 65536 <= nodes \/ nodes + 1048576 <= ctx) -> (ctx + 65536 <= store \/ store + 8388608 <= ctx) ->
  (mb + msz <= ctx \/ ctx + 65536 <= mb) ->
  forall A k, ctx <= A -> A + k <= ctx + 65536 -> 0 <= k ->
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros D1 D2 D3 D4 D5 A k HA HB HK. kfacts.
  kind16 ltac:(clear -HA HB HK F_lo Fc2 Fc3 KAFc1 KBFc1 KCFc1; lia) ltac:(clear -HA HB HK Fc2 Fc3 KAFc1 KBFc1 KCFc1; lia) ltac:(clear -HA HB HK D1; lia) ltac:(clear -HA HB HK D5 C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1; lia)
         ltac:(clear -HA HB HK Fc2 Fc3 KAFc1 KBFc1 KCFc1 C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1 F_sh; lia) ltac:(clear -HA HB HK D3 D4; lia)
         ltac:(clear -HA HB HK Fc2 Fc3 KAFc1 KBFc1 KCFc1 F_lst D2; lia) ltac:(clear -HA HB HK Fc2 Fc3 KAFc1 KBFc1 KCFc1 F_eb D2; lia) ltac:(clear -HA HB HK Fc2 Fc3 KAFc1 KBFc1 KCFc1 F_gl D2; lia).
Qed.

#[using="rc tlsI mb msz ctx lo KF"] Lemma KS_t :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (t + 4096 <= nodes \/ nodes + 1048576 <= t) -> (t + 4096 <= store \/ store + 8388608 <= t) ->
  forall A k, t <= A -> A + k <= t + 4096 -> 0 <= k ->
  (A + k <= t + 80 \/ t + 112 <= A) -> (A + k <= t + 2128 \/ t + 2132 <= A) -> (A + k <= t + 2784 \/ t + 2792 <= A) -> (A + k <= t + 2800 \/ t + 3169 <= A) ->
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros D1 D2 D3 A k HA HB HK E1 E2 E3 E4. kfacts.
  cbn [disjoint_from].
  split; [clear -HA HB HK F_lo Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2; lia|]. do 4 (split; [clear -HA HB HK Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2; lia|]).
  split; [clear -HA HB HK E1; lia|]. split; [clear -HA HB HK E2; lia|]. split; [clear -HA HB HK E3; lia|]. split; [clear -HA HB HK E4; lia|].
  split; [clear -HA HB HK C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1; lia|]. split; [clear -HA HB HK Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2 C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1 F_sh; lia|]. split; [clear -HA HB HK D2; lia|]. split; [clear -HA HB HK D3; lia|].
  split; [clear -HA HB HK Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2 F_lst D1; lia|]. split; [clear -HA HB HK Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2 F_eb D1; lia|]. split; [clear -HA HB HK Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2 F_gl D1; lia|]. exact I.
Qed.

#[using="rc tlsI mb msz ctx lo KF"] Lemma KS_res :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (nodes + 1048576 <= res \/ res + 137439023104 <= nodes) ->
  (store + 8388608 <= res \/ res + 137439023104 <= store) ->
  forall A k, res <= A -> A + k <= res + 137439023104 -> 0 <= k ->
  (A + k <= lst \/ lst + 8192 <= A) -> (A + k <= eb \/ eb + 8192 <= A) -> (A + k <= gl \/ gl + 8 <= A) ->
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros D1 D2 D3 A k HA HB HK E1 E2 E3. kfacts.
  kind16 ltac:(clear -HA HB HK F_lo F_res; lia) ltac:(clear -HA HB HK F_res; lia) ltac:(clear -HA HB HK D1; lia) ltac:(clear -HA HB HK C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1; lia)
         ltac:(clear -HA HB HK F_res C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1 F_sh; lia) ltac:(clear -HA HB HK D2 D3; lia)
         ltac:(clear -HA HB HK E1 F_lst; lia) ltac:(clear -HA HB HK E2 F_eb; lia) ltac:(clear -HA HB HK E3; lia).
Qed.

(* [comment removed for export] *)
#[using="tlsI ctx lo KF"] Lemma KS_obj : forall A k, ((6303744 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  (A + k <= mb \/ mb + msz <= A) ->
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros A k HA HB HK E1 E2 E3 E4 E5. kfacts.
  kind16 ltac:(clear -HA HB HK F_lo; lia) ltac:(clear -HA HB HK; lia) ltac:(clear -HA HB HK E1; lia) ltac:(clear -HA HB HK E5 C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1; lia)
         ltac:(clear -HA HB HK C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1 F_sh; lia) ltac:(clear -HA HB HK E3 E4; lia)
         ltac:(clear -HA HB HK F_lst E2; lia) ltac:(clear -HA HB HK F_eb E2; lia) ltac:(clear -HA HB HK F_gl E2; lia).
Qed.
(* [comment removed for export] *)
#[using="tlsI ctx lo KF"] Lemma KS_objL : forall A k, (4096 <= A /\ (A + k <= 65536 \/ 6303744 <= A) /\ (A + k <= 2147446784 \/ 17594333495296 <= A)) -> A + k <= ATOP -> 0 <= k ->      
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  (A + k <= mb \/ mb + msz <= A) ->
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros A k HA HB HK E1 E2 E3 E4 E5. kfacts.
  kind16 ltac:(clear -HA HB HK F_lo; lia) ltac:(clear -HA HB HK; lia) ltac:(clear -HA HB HK E1; lia) ltac:(clear -HA HB HK E5 C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1; lia)
         ltac:(clear -HA HB HK C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1 F_sh; lia) ltac:(clear -HA HB HK E3 E4; lia)
         ltac:(clear -HA HB HK F_lst E2; lia) ltac:(clear -HA HB HK F_eb E2; lia) ltac:(clear -HA HB HK F_gl E2; lia).
Qed.

(* [comment removed for export] *)
#[using="rc tlsI res ctx lo KF"] Lemma KS_chunk : forall A k, mb <= A -> A + k <= mb + msz -> 0 <= k -> (A + k <= UB - 16 \/ UB + 8 <= A) ->
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros A k HA HB HK E1. kfacts.
  kind16 ltac:(clear -HA HB HK F_lo C4; lia) ltac:(clear -HA HB HK KAC1 KBC1 KEC1 KCC1 KDC1; lia) ltac:(clear -HA HB HK C5; lia) ltac:(clear -HA HB HK E1; lia)
         ltac:(clear -HA HB HK KAC1 KBC1 KEC1 KCC1 KDC1 F_sh; lia) ltac:(clear -HA HB HK C7 C8; lia)
         ltac:(clear -HA HB HK F_lst KAC1 KBC1 KEC1 KCC1 KDC1 C6; lia) ltac:(clear -HA HB HK F_eb KAC1 KBC1 KEC1 KCC1 KDC1 C6; lia) ltac:(clear -HA HB HK F_gl KAC1 KBC1 KEC1 KCC1 KDC1 C6; lia).
Qed.
End Kinds.

(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_freeS : forall (CI : list (Z * Z)) sp t mb msz UB gq nodes store res ctx lo lst eb gl (LB : list ablock) m m',
  kfactsS sp t mb msz UB gq nodes store res ctx lo lst eb gl ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                 /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                 /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                 /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI ->
  munch (WfS sp t UB gq nodes store lst eb gl) m m' -> wmono asegs m m' ->
  (forall b, In b LB -> disjoint_from (WfS sp t UB gq nodes store lst eb gl) (ab_addr b) (ab_size b)) ->
  (forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
       disjoint_from (WfS sp t UB gq nodes store lst eb gl) (shad a') 1) ->
  (forall A k, ATPv + -200 <= A -> A + k <= ATPv + 312 -> 0 <= k -> disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k) ->      (* [comment removed for export] *)
  (forall a', ATPv + -200 <= a' < ATPv + 312 -> disjoint_from (WfS sp t UB gq nodes store lst eb gl) (shad a') 1) ->                  (* [comment removed for export] *)
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) AIMSH_LO AIMSH_LEN ->                                                          (* [comment removed for export] *)
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) AAHMv AAHM_SZ ->                                                          (* [comment removed for export] *)
  aheap_pres CI LB sp m m'.
Proof.
  intros CI sp t mb msz UB gq nodes store res ctx lo lst eb gl LB m m' KF CIOK MU WM HBK HFK TLSK TLSS IMSH AHMK a Ha CL.
  split; [| intros Hw; apply WM; exact Hw].
  apply MU. rewrite wa_unsigned by exact Ha.
  destruct CL as [CL|TL]; [| exact (aextra_outside _ a TLSK TLSS IMSH AHMK TL)].
  pose proof KF as KF'. (nd_pre KF' 10%nat; intros F_lo F_t F_res F_ch F_sh F_ns F_ctx F_lst F_eb F_gl; nd_post).
  destruct CL as [ST | [CIa | [BLK | SH]]].
  - eapply disjoint_outside; [eapply (KS_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); lia | lia].
  - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as ndP__; nd_pre ndP__ 6%nat; intros Q1 Q2 Q3 Q4 Q5 Q6; nd_post). cbn [fst snd] in *.
    eapply disjoint_outside; [eapply (KS_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); unfold AIMG_HI in *; clear - Ha R Q1 Q2 Q3 Q4 Q5 Q6; lia | lia].   (* [comment removed for export] *)
  - (nd_pre BLK 3%nat; intros b Hb R; nd_post). eapply disjoint_outside; [exact (HBK b Hb) | lia].
  - (nd_pre SH 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->).
    pose proof (shad_div a') as SD. pose proof (shad_div ATOP) as SDs. pose proof (shad_div mb) as SDm. unfold ASHOFF in *.
    destruct Ha' as [ST | [CIa | FK]].
    + eapply disjoint_outside; [eapply (KS_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: unfold AIMG_HI in *; clear -ST SD SDs SDm F_sh F_lo F_ch; Z.div_mod_to_equations; lia.   (* [comment removed for export] *)
    + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as ndP__; nd_pre ndP__ 4%nat; intros Q1 Q2 Q3 _; nd_post). cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (KS_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: unfold AIMG_HI in *; clear -R SD Q1 Q3; Z.div_mod_to_equations; lia.
    + (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). eapply disjoint_outside; [exact (HFK cls FA sz Hin a' R) | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xfreeS (X : aconc) (app : bool) (k24 : Z) : aconc := if app then X else xbatch X k24.

#[using="Type"] Lemma xfreeS_free : forall X app k24 c', xc_free (x_cls (xfreeS X app k24) c') = xc_free (x_cls X c').
Proof. intros. unfold xfreeS, xbatch. destruct app; cbn; [reflexivity|]. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma xfreeS_cache : forall X app k24 c',
  xc_cache (x_cls (xfreeS X app k24) c') =
  if (negb app) && (c' =? K_BATCH_CLASS) then removelast (xc_cache (x_cls X K_BATCH_CLASS)) else xc_cache (x_cls X c').
Proof.
  intros. unfold xfreeS, xbatch. destruct app; cbn; [reflexivity|]. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [->|]; reflexivity.
Qed.
#[using="Type"] Lemma busy_of_xfreeS : forall X app k24 c' k',
  busy_of (xfreeS X app k24) c' k' = if (negb app) && (K_BATCH_CLASS =? c') && (k24 =? k') then Some (bbatch k24) else busy_of X c' k'.
Proof.
  intros. unfold xfreeS. destruct app; cbn [negb andb]; [reflexivity|]. apply busy_of_xbatch'.
Qed.
#[using="Type"] Lemma In_xfreeS : forall X app k24 y, In y (x_busy X) -> In y (x_busy (xfreeS X app k24)).
Proof. intros X app k24 y Hy. unfold xfreeS. destruct app; [exact Hy|]. apply In_xbatch. right. exact Hy. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.

Definition store_freeS__stmt : Prop := store_freeS_stmt DI AFK CI.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 5).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 6).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 7).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 8).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 9).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 10).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 11).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 12).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 13).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 14).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 15).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 16).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 17).
Variable F : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 18).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 19).
Variable m : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 20).
Variable st : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 21).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 22).
Variable X : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 23).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 24).
Variable p : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 25).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 26).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 27).
Variable n : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 28).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 29).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 30).
Variable A : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 31).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 32).
Variable k24 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 33).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 34).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 35).
Let ch := CSec mb ms n.
Let st1 := set_live (delete p (a_live st)) st.
Let st2 := st_enq st1 ch.
Let ek := ek_of L st X Q n k24 stj chunks.
Let g := g_of L st Q (ek_delta ek n).
Let UB := mb + 6144.
Let lst := qlast L (q_loc Q).
Let eb := ek_b ek lst.
Let gl := dk_glst g lst.
Let gq := shlen (rup n 8).
Let st' := st_after st2.
#[using="HL CI_OK ch st1 st2 ek g UB lst eb gl gq st'"] Lemma store_freeS__body : ltac:(let T := type of (fun (h : store_freeS__stmt) => h L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p mb ms n b1 ctx A lo k24 stj chunks) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (F, (fc, (m, (st, (LB, (X, (Q, (p, (mb, (ms, (n, (b1, (ctx, (A, (lo, (k24, (stj, chunks)))))))))))))))))))))))))))))))))))) as _.
  unfold store_freeS_stmt. 
  cbv zeta. intros ALO ARNG AR AQ BL HFK LIVE HIN NQM HDR B1 B13 CTX NEWF NOREC EK DK CEIL LO ms' PM. unfold AFREE_STACK in LO.
  chg (CSec mb ms n) ch.
  chg (set_live (delete p (a_live st)) st) st1.
  chg (st_enq st1 ch) st2.
  chg (ek_of L st X Q n k24 stj chunks) ek.
  chg (g_of L st Q (ek_delta ek n)) g.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS0 UNW; nd_post).
  (nd_pre (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) 3%nat; intros EAu _ WFch; nd_post).
  (nd_pre (sec_wf1_facts' L mb ms n WFch) 13%nat; intros MAL MLO MCE MSE NB RZ MSB MSAL NMS NS0 SCL NPR N6; nd_post).
  (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post). unfold AIMG_HI in ML1. (pose proof (ablk_int _ _ MLO) as ndP__; nd_pre ndP__ 6%nat; intros kM KAM KBM KEM KCM KDM; nd_post).   (* [comment removed for export] *)
  (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros SC_t SC_c SC_r SC_p SC_n SC_st SC_f SC_d SC_tls SC_ahm0; nd_post).
  pose proof HS as HS0. (nd_pre HS0 5%nat; intros WFS _ SINST PZ SHZ; nd_post).
  (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros _ WP WR WL WB WF1 WD; nd_post).
  (nd_pre (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE) 25%nat; intros order i b1r cxr uw PO NTH IL LENO WF1o WDo U64 JK PER CH H1 H5 _ _ _ HUW UJ S1 S2 S3; nd_post).
  cbv zeta in H5, HUW, UJ, S2, S3.
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  (pose proof (aobj4_int _ OT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ OC ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci _ [kC CBND]; nd_post). (pose proof (aobj_int _ _ ON ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni _ [kN NBND]; nd_post).
  (pose proof (aobj_int _ _ OS ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si _ [kS SBND]; nd_post). pose proof (ao_res_hi L ALO) as RHI.
  unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
  box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
  word_range sp SPR.
  chg (mb + 6144) UB.
  assert (EUB : UB = mb + 6144) by reflexivity.
  assert (EHM : mb + 6128 = UB - 16) by (subst UB; clear; lia).
  assert (UB16' : UB mod 8 = 0) by (subst UB; clear -MAL; Z.div_mod_to_equations; lia).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  rewrite EHM in PM, EK, DK, HDR.
  (pose proof (rup8_facts n ltac:(clear -NB; lia)) as ndP__; nd_pre ndP__ 3%nat; intros RUP RUP8 RUPS; nd_post).
  assert (SHGEO : shad UB = shad mb + 768 /\ shlen (rup n 8) <= ms / 8 - 768 /\ 0 < shlen (rup n 8) /\ UB + rup n 8 <= mb + ms
                  /\ 2148238848 <= shad mb /\ shad mb + ms / 8 <= 17594332446720).   (* [comment removed for export] *)
  { subst UB. rewrite !shad_div, RUPS. unfold ASHOFF. (pose proof (sec_facts n ltac:(clear -NB; lia) NPR) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ RS1 _ NSE _; nd_post).
    unfold K_HIGH_MEM in *. pose proof atop_range as AR8. clear -MAL RUP RUP8 RS1 NSE NMS N6 NB ML1 ML3 MCE MSAL AR8. Z.div_mod_to_equations. lia. }
  (nd_pre SHGEO 6%nat; intros SHE SHL SHP UBS SHLO SHHI; nd_post).
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof NUM as NUM0. (nd_pre NUM0 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof CP as CP0. (nd_pre CP0 7%nat; intros LN1 LN2 _ _ ND2 BSI _; nd_post).
  (* [comment removed for export] *)
  pose proof (st_enq_bytes st p (CSec mb ms n) L X Q k24 stj chunks) as SB. cbn [chunk_size] in SB. fold ch in SB.
  assert (CNT : enq_app st1 ch = None -> 0 < c_count (get_cls st K_BATCH_CLASS)).
  { intros E. destruct (enq_is_app st) eqn:EAx.
    - exfalso. assert (EA1 : enq_is_app st1 = true) by exact EAx. destruct (proj1 (enq_is_app_spec st1 ch) EA1) as [s Hs]. congruence.
    - exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NEWF eq_refl)))))))). }
  specialize (SB CNT). fold st1 st2 ek in SB. (nd_pre SB 3%nat; intros SB1 SB2 SB3; nd_post).
  assert (ED0 : 0 <= ek_delta ek n /\ ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; clear -NB; destruct (enq_is_app st); cbn [ek_delta]; lia).
  assert (EBK : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q) \/ (enq_is_app st = false /\ ek_b ek (qlast L (q_loc Q)) = abatch_addr L k24)).
  { subst ek. unfold ek_of. destruct (enq_is_app st) eqn:EAx; cbn [ek_b]; [left; reflexivity| right; split; reflexivity]. }
  assert (EBB : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
      \/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q))).
  { destruct EBK as [E|[EAx E]]; [left; exact E| right; exists k24]. (nd_pre (NEWF EAx) 5%nat; intros NK NBk KK NIB _; nd_post). split; [exact E|]. split; [exact KK| exact NIB]. }
  assert (HMSEP : forall kk, 0 <= kk < ndist st K_BATCH_CLASS -> UB - 16 + 24 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= UB - 16).
  { intros kk KK. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ _ _ _ PERC _; nd_post).
    (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros Q1 Q2 _; nd_post).
    (pose proof (slot_in_region L st K_BATCH_CLASS kk ltac:(rewrite size_of_class_24; lia) (proj1 Q1) KK) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 _; nd_post).
    rewrite size_of_class_24 in P4. subst UB. unfold abatch_addr, aregion, K_REGION, K_FREEARR_OFF, K_BATCH_CLASS in *.
    clear -P5 P4 Q1 Q2 RSP SC_r MSB. lia. }
  (nd_pre (read_dkS (AHQ DI ASEC_of AFK) L st X Q m RNG (UB - 16) ALO ARNG AR AQ HMSEP (ek_b ek (qlast L (q_loc Q))) (ek_delta ek n) ek
              (proj1 ED0) EBB ltac:(rewrite <- SB1, <- SB2; exact NOREC) eq_refl) 4%nat; intros _ _ GL GLST; nd_post).
  fold g in GL, GLST.
  chg (qlast L (q_loc Q)) lst. chg (ek_b ek lst) eb. chg (dk_glst g lst) gl. chg (shlen (rup n 8)) gq.
  (* [comment removed for export] *)
  assert (BGEO : forall q, In q (q_loc Q ++ q_glob Q) ->
      aregion L K_BATCH_CLASS <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
      /\ al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
  { intros q Hq. (pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
    rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
    generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  assert (A24 : c_allocated_user (get_cls st K_BATCH_CLASS) <= K_FREEARR_OFF).
  { (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros Q1 Q2 _; nd_post). lia. }
  assert (LSTF : lst = 0 \/ ((exists q, In q (q_loc Q) /\ lst = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= lst /\ lst + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104)).
  { subst lst. destruct (qlast_cases L (q_loc Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (GDR : g_drain g = (Q_CACHE <? a_qloc_bytes st + ek_delta ek n)) by reflexivity.
  assert (GLF : (g_drain g = false /\ gl = lst)
             \/ (g_drain g = true /\ gl = qlast L (q_glob Q)
                 /\ (gl = 0 \/ ((exists q, In q (q_glob Q) /\ gl = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104)))).
  { subst gl. rewrite GLST, GDR. destruct (Q_CACHE <? a_qloc_bytes st + ek_delta ek n); [right| left; split; reflexivity].
    split; [reflexivity|]. split; [reflexivity|].
    destruct (qlast_cases L (q_glob Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (EBF : eb = 0 \/ (aregion L K_BATCH_CLASS <= eb /\ eb + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104)).
  { subst eb. destruct EBK as [E|[EAx E]].
    - rewrite E. destruct LSTF as [Z0|(_ & FF)]; [left; exact Z0| right; exact FF].
    - right. rewrite E. (nd_pre (NEWF EAx) 4%nat; intros _ _ KK _; nd_post). (pose proof (slot_geo L st X K_BATCH_CLASS k24 ALO WF (K24) KK) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
      rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
      generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  (* [comment removed for export] *)
  (nd_pre PM 19%nat; intros id t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' sj' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MU WM MI' ST' IDR HDR' FC' SH' QC' EKP DKP STATS' LSJ' UW' FL' IAS' IAM' DEP'; nd_post).
  fold lst in MU, QC', EKP, DKP, EBK. fold eb in MU, EBK. fold gl in MU. fold gq in MU, SH'.
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  assert (ELST : lst = qlast L (q_loc Q)) by reflexivity. assert (EEB : eb = ek_b ek lst) by reflexivity.
  assert (EGL : gl = dk_glst g lst) by reflexivity. assert (EGQ : gq = shlen (rup n 8)) by reflexivity.
  clearbody lst eb gl gq.
  (* [comment removed for export] *)
  assert (EBNZ : 0x10007fff8000 <= eb) by (rewrite EEB; exact (ek_pre_b_hi _ _ _ _ _ _ _ _ EK)).   (* [comment removed for export] *)
  replace (eb + 8192) with (eb + qsz eb) in MU by (rewrite (qsz_pos eb) by (clear -EBNZ; lia); reflexivity).   (* [comment removed for export] *)
  assert (MUn : munch (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  clear MU.
  assert (KF : kfactsS (bv_unsigned sp) (al_t L) mb ms UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo lst eb gl).
  { unfold kfactsS. unfold K_HIGH_MEM in *.
    assert (GQ1 : 1 <= gq) by (clear -SHP EGQ; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP MLO ML1 ML3 MCE EUB UBS NB RUP SC_t SC_r SC_n SC_st SHE SHL SHLO SHHI GQ1 EGQ LSTF EBF GLF EBNZ. clear. intros.
    rewrite ?EGQ in SHL. unfold iclr, AIMG_LO, AIMG_HI in *.   (* [comment removed for export] *)
    (destruct LSTF as [Z0|(_ & FF)]; [rewrite (qsz_eq0 lst Z0) | rewrite (qsz_pos lst) by (atop_facts; lia)]);
    (destruct EBF as [Z1|FF1]; [exfalso; atop_facts; lia|]); rewrite (qsz_pos eb) by (atop_facts; lia); destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & FF2)])];
    sg_destr; repeat split; first [assumption | lia]. }
  pose proof (KS_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KS_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KS_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KS_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KS_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s) SC_c) as Kctx.
  pose proof (KS_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
  pose proof (KS_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
  pose proof (KS_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KS_objL _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as KobjL.      (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
  unfold adisj in D_l_t, D_l_r, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
  pose proof (KS_chunk _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kchunk.
  (* [comment removed for export] *)
  assert (SC : same_core st1 (st_after st2) /\ a_cinit (st_after st2) = a_cinit st /\ a_live (st_after st2) = delete p (a_live st) /\ a_next (st_after st2) = a_next st
               /\ a_space_beg (st_after st2) = a_space_beg st /\ a_ptr_array (st_after st2) = a_ptr_array st
               /\ (enq_is_app st = true -> a_cls (st_after st2) = a_cls st)
               /\ (enq_is_app st = false -> a_cls (st_after st2) = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
  { pose proof (st_after_core st2) as [SC2 CL2'].
    assert (SC1 : same_core st1 st2 /\ (enq_is_app st = true -> a_cls st2 = a_cls st) /\ (enq_is_app st = false -> a_cls st2 = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
    { subst st2. unfold st_enq. destruct (enq_app st1 ch) as [sx|] eqn:EAPP.
      - (nd_pre (enq_app_Some st1 _ sx EAPP) 5%nat; intros l bl QL NFz ndR1__; nd_post; revert ndR1__; intros ->). split; [repeat split; intros; reflexivity|].
        split; [intros _; reflexivity|]. intros EAx. exfalso.
        assert (EA1 : enq_is_app st1 = true) by (apply (proj2 (enq_is_app_spec st1 ch)); eexists; exact EAPP).
        change (enq_is_app st1) with (enq_is_app st) in EA1. congruence.
      - (pose proof (enq_new_core ch st1) as ndP__; nd_pre ndP__ 7%nat; intros C1 _ _ _ _ _ C7; nd_post). split; [exact C1|].
        split; [| intros _; exact C7]. intros EAx. exfalso.
        assert (EA1 : enq_is_app st1 = true) by exact EAx. destruct (proj1 (enq_is_app_spec st1 ch) EA1) as [s Hs]. congruence. }
    (nd_pre SC1 3%nat; intros SC1 CLa CLb; nd_post). pose proof (same_core_trans _ _ _ SC1 SC2) as SC3.
    pose proof SC3 as SC0. (nd_pre SC0 8%nat; intros F1 F2 F3 F4 F5 F6 F7 _; nd_post).
    split; [exact SC3|]. split; [exact F3|]. split; [exact F1|]. split; [exact F2|]. split; [exact F4|]. split; [exact F5|].
    split; [intros EAx; rewrite CL2'; exact (CLa EAx)| intros EAx; rewrite CL2'; exact (CLb EAx)]. }
  (nd_pre SC 8%nat; intros SC ECIN ELIVE ENEXT ESB EPA CLa CLb; nd_post).
  pose proof SC as SC0. (nd_pre SC0 12%nat; intros _ _ _ _ _ ENRES ENSEC GCo M24a M24b M24c M24d; nd_post).
  chg (st_after st2) st'.
  set (X' := xfreeS X (enq_is_app st) k24).
  assert (GC24 : get_cls st' K_BATCH_CLASS = (if enq_is_app st then get_cls st K_BATCH_CLASS else cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS))).
  { unfold get_cls at 1. destruct (enq_is_app st) eqn:EAx; [rewrite (CLa eq_refl); reflexivity| rewrite (CLb eq_refl), lookup_insert_eq; reflexivity]. }
  assert (GCo' : forall c', c' <> K_BATCH_CLASS -> get_cls st' c' = get_cls st c') by (intros c' NE; rewrite (GCo c' NE); reflexivity).
  assert (NDS : forall c', ndist st' c' = ndist st c').
  { intros c'. unfold ndist. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24b; reflexivity| rewrite (GCo' c' NE); reflexivity]. }
  assert (MC' : forall c', max_count st' c' = max_count st c') by (intros c'; unfold max_count; rewrite ECIN; reflexivity).
  (* [comment removed for export] *)
  assert (WFst1 : awf L st1 X) by (apply (awf_delete_sec L st X p mb ms n st1 WF LIVE); reflexivity).
  assert (WF' : awf L st' X').
  { subst X'. unfold xfreeS. destruct (enq_is_app st) eqn:EAx.
    - apply (awf_delete_sec L st X p mb ms n st' WF LIVE); [exact ESB| exact EPA| exact ECIN| exact (CLa eq_refl)| exact ELIVE| exact ENEXT].
    - (nd_pre (NEWF eq_refl) 8%nat; intros NK NBk KK NIB JKb FSH CIN POS; nd_post).
      apply (awf_xbatch L st1 X k24 (c_count (get_cls st K_BATCH_CLASS)) WFst1 eq_refl POS NK).
      + exact ESB. + exact EPA. + exact ECIN. + rewrite ELIVE; reflexivity. + exact ENEXT.
      + intros c' NE. rewrite (GCo' c' NE). reflexivity.
      + rewrite GC24. reflexivity. }
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L st' m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | exact ENRES | exact ENSEC | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
  assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
  assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
  (* [comment removed for export] *)
  assert (THR' : athread L st' X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE].
      + destruct (CACHES K_BATCH_CLASS Hc') as [tail (CR & CHc & LCH)]. unfold acache_cells. cbv zeta.
        rewrite GC24, MC', ECIN. subst X'. rewrite xfreeS_cache, Z.eqb_refl, andb_true_r.
        replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR, CHc |- * by (unfold acache_addr, K_BATCH_CLASS; clear; lia).
        subst ek. unfold ek_of in EKP. destruct (enq_is_app st) eqn:EAx; cbn [ek_post negb] in EKP |- *.
        * (nd_pre EKP 5%nat; intros _ _ _ CR' _; nd_post). exists tail. split; [exact CR'|]. split; [| exact LCH].
          eapply u32arr_frame; [exact CHc | exact MUn | exact WM |]. rewrite length_app, length_map. apply Kt; clear -LCH; lia.
        * destruct EKP as (CR' & _). (nd_pre (NEWF eq_refl) 8%nat; intros NK NBk KK NIB JKb FSH CIN POS; nd_post).
          cbn [c_count cls_set_count]. exists (Z_to_bv 64 (acompact K_BATCH_CLASS k24) :: tail).
          pose proof (cache24_split L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK) as [CACHE LRL].
          split; [exact CR'|]. split.
          -- eapply u32arr_frame; [| exact MUn | exact WM |].
             ++ rewrite CACHE, map_app in CHc. cbn [map] in CHc. rewrite <- app_assoc in CHc. cbn [app] in CHc. exact CHc.
             ++ rewrite length_app, length_map. cbn [length].
                replace (length (removelast (xc_cache (x_cls X K_BATCH_CLASS))) + Datatypes.S (length tail))%nat with 16%nat
                  by (rewrite CACHE, length_app in LCH; cbn [length] in LCH; clear -LCH; lia).
                apply Kt; clear; lia.
          -- cbn [length]. rewrite CACHE, length_app in LCH. cbn [length] in LCH. clear -LCH. lia.
      + eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | rewrite (GCo' c' NE); reflexivity | exact ECIN | |].
        * subst X'. rewrite xfreeS_cache. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [E|_]; [exfalso; exact (NE E)|]. rewrite andb_false_r. reflexivity.
        * unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply Kt; clear -Hc' NE; lia.
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + eapply junk_frame; [exact (proj1 (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia))) | exact MUn | exact WM | intros _; apply Kt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia).
          assert (STJ' : exists w : word, rw_cells asegs m' (al_t L + 2784) [C8 w]).
          { subst ek. unfold ek_of in EKP. destruct (enq_is_app st); cbn [ek_post] in EKP.
            - (nd_pre EKP 5%nat; intros _ _ _ _ STS'; nd_post). exists stj. exact STS'.
            - (nd_pre EKP 3%nat; intros _ STS' _; nd_post). exact STS'. }
          destruct STJ' as [w STS']. pose proof (junk_of_cells m' _ _ STS') as J. cbn in J. exact J.
        * replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) by (clear; lia).
          eapply junk_frame; [| exact MUn | exact WM | intros _; apply Kt; clear; lia].
          pose proof (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ CSb].
          pose proof (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(clear; lia) ltac:(clear; lia)) as [_ CSc].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by (clear; lia). exact CSc.
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  (* [comment removed for export] *)
  assert (BDIS : forall q1 q2, In q1 (q_loc Q ++ q_glob Q) -> In q2 (q_loc Q ++ q_glob Q) ->
      abatch_addr L (qb_slot q1) = abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q1) + 8192 <= abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q2) + 8192 <= abatch_addr L (qb_slot q1)).
  { intros q1 q2 Hq1 Hq2. destruct (Z.eq_dec (qb_slot q1) (qb_slot q2)) as [E|NE]; [left; rewrite E; reflexivity| right].
    pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot q1) (qb_slot q2) ltac:(pose proof (bslot_range L st X Q WF CP q1 Hq1); lia)
                  ltac:(pose proof (bslot_range L st X Q WF CP q2 Hq2); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (KDIS : forall q, In q (q_loc Q ++ q_glob Q) -> enq_is_app st = false ->
      abatch_addr L k24 + 8192 <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= abatch_addr L k24).
  { intros q Hq EAx. (nd_pre (NEWF EAx) 5%nat; intros NK NBk KK NIB _; nd_post).
    assert (NE : k24 <> qb_slot q) by (intros ->; apply NIB; apply in_map; exact Hq).
    pose proof (slots_disjoint L K_BATCH_CLASS k24 (qb_slot q) ltac:(lia) ltac:(pose proof (bslot_range L st X Q WF CP q Hq); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L st' m' c'' /\ afreearray L st' X' m' c'' /\ aslots L st' X' m' c'' /\ aslot_shadow L st' X' m' c'').
  { intros c'' Hc''. (nd_pre (CLS c'' Hc'') 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC1 : c_num_freed (get_cls st' c'') = c_num_freed (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24c| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC3 : c_allocated_user (get_cls st' c'') = c_allocated_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24b| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 4%nat; intros RI1 RI2 RI3 RI4; nd_post).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | exact EC1 | exact EC2 | exact EC3 | exact EC4 |].
      unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      apply Kres; try (clear -Hc'' RSP; lia).
      + destruct LSTF as [Z0|(_ & F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + destruct EBF as [Z0|(F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + assert (GLR : gl = 0 \/ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)).
        { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; exact F2].
          destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; exact F2]. }
        destruct GLR as [Z0|F2]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | exact EC1 | exact EC2 | | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + subst X'. apply xfreeS_free.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia | | |].
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          pose proof (farr_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2) as D. clear -D. lia.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, AIMG_HI, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
          rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) (afreearr L c'') ltac:(clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D RI2 RI3 FA2; lia| exact AM] | clear; lia].
    - (* [comment removed for export] *)
      eapply (aslots_update_gen L _ m m' MUn WM st st' X X' c''); [exact SLOTS | apply NDS | exact EC3 | exact EC4 | |].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D2 : (enq_is_app st = false /\ c'' = K_BATCH_CLASS /\ k'' = k24) \/ (enq_is_app st = true \/ c'' <> K_BATCH_CLASS \/ k'' <> k24))
          by (clear; destruct (enq_is_app st); lia).
        destruct D2 as [(EAx & E24 & EK24)|NE2].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X'. rewrite (busy_of_xfreeS X (enq_is_app st) k24 K_BATCH_CLASS k24), EAx. cbn [negb andb]. rewrite !Z.eqb_refl. cbn [andb].
          unfold aslot_busy, bbatch. cbn [xb_st xb_class xb_slot]. unfold xb_alloc. cbn [xb_class xb_slot]. rewrite size_of_class_24.
          subst ek. unfold ek_of in EKP. rewrite EAx in EKP. cbn [ek_post] in EKP. (nd_pre EKP 6%nat; intros _ _ BC BA [bsb BJ] _; nd_post).
          fold (abatch_addr L k24) in BC, BA, BJ |- *. change (aslot_addr L K_BATCH_CLASS k24) with (abatch_addr L k24).
          replace 8192 with (24 + (8 * Z.of_nat (length [Z_to_bv 64 (UB - 16)]) + (8192 - 24 - 8 * 1))) by (cbn; lia).
          apply junk_merge; [| | clear; lia| cbn; clear; lia].
          -- pose proof (junk_of_cells m' _ _ BC) as J. cbn in J. exact J.
          -- apply junk_merge; [apply junk_of_u64arr; exact BA | | cbn; clear; lia | clear; lia].
             cbn [length Z.of_nat Pos.of_succ_nat]. eexists. exact BJ.
        * assert (T1 : negb (enq_is_app st) && (K_BATCH_CLASS =? c'') && (k24 =? k'') = false).
          { destruct (enq_is_app st); cbn [negb andb]; [reflexivity|].
            destruct (Z.eqb_spec K_BATCH_CLASS c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k24 k'') as [E'|]; [| reflexivity]. exfalso.
            destruct NE2 as [NE|[NE|NE]]; [discriminate| apply NE; symmetry; exact E| apply NE; symmetry; exact E']. }
          assert (BX : busy_of X' c'' k'' = busy_of X c'' k'').
          { subst X'. rewrite (busy_of_xfreeS X (enq_is_app st) k24 c'' k''), T1. reflexivity. }
          (* [comment removed for export] *)
          assert (BQ : forall q, In q (q_loc Q ++ q_glob Q) -> c'' = K_BATCH_CLASS -> aslot_addr L c'' k'' = abatch_addr L (qb_slot q) ->
              exists yq, busy_of X c'' k'' = Some yq /\ xb_st yq = BBatch /\ xb_class yq = K_BATCH_CLASS /\ xb_slot yq = k''
                         /\ junk_at m (abatch_addr L (qb_slot q)) 8192 /\ k'' = qb_slot q).
          { intros q Hq -> EQA. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
            assert (EK' : k'' = qb_slot q) by (unfold abatch_addr, aslot_addr in EQA; rewrite size_of_class_24 in EQA; clear -EQA; lia). subst k''.
            exists yq. pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq in BY.
            split; [exact BY|]. split; [exact Syq|]. split; [exact Cyq|]. split; [exact Kyq|]. split; [| reflexivity].
            destruct SLOTS as [SLK _]. specialize (SLK (qb_slot q) Hk''). rewrite BY in SLK. unfold aslot_busy in SLK. rewrite Syq in SLK.
            unfold xb_alloc in SLK. rewrite Cyq, Kyq, size_of_class_24 in SLK. exact SLK. }
          assert (D3 : (c'' = K_BATCH_CLASS /\ lst <> 0 /\ aslot_addr L c'' k'' = lst) \/ (c'' <> K_BATCH_CLASS \/ lst = 0 \/ aslot_addr L c'' k'' <> lst)) by (clear; lia).
          destruct D3 as [(E24 & LNZ & EL)|NE3].
          -- (* [comment removed for export] *)
             right. rewrite BX. destruct LSTF as [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)]; [exfalso; exact (LNZ Z0)|].
             (nd_pre (BQ q ltac:(apply in_or_app; left; exact Hq) E24 ltac:(rewrite EL; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
             rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EL.
             assert (QNE : a_qloc st <> []) by (intros QL0; apply LNZ; rewrite ELST; replace (q_loc Q) with (@nil qbatchc) by (clear -QL0 LN1; destruct (q_loc Q); [reflexivity| rewrite QL0 in LN1; cbn in LN1; discriminate]); reflexivity).
             subst ek. unfold ek_of in EKP, EK. destruct (enq_is_app st) eqn:EAx; cbn [ek_post ek_pre] in EKP, EK.
             ** (nd_pre EKP 4%nat; intros LB' LA' [bs LJ'] _; nd_post). (nd_pre EK 9%nat; intros _ _ CNT' _ _ _ _ LEN _; nd_post).
                rewrite ELST in LB', LA', LJ' |- *.
                set (cnt := b_count (List.last (a_qloc st) dummy_batch)) in *.
                replace 8192 with (24 + (8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))) ++ [Z_to_bv 64 (UB - 16)])) + (8192 - 24 - 8 * (cnt + 1))))
                  by (rewrite length_app, LEN; cbn [length]; clear -CNT'; lia).
                apply junk_merge; [| | clear; lia| rewrite length_app, LEN; cbn [length]; clear -CNT'; lia].
                +++ pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
                +++ apply junk_merge; [apply junk_of_u64arr; exact LA' | | rewrite length_app, LEN; cbn [length]; clear -CNT'; lia | clear -CNT'; lia].
                    rewrite length_app, LEN. cbn [length]. replace (8 * Z.of_nat (Z.to_nat cnt + 1)) with (8 * (cnt + 1)) by (clear -CNT'; lia). eexists. exact LJ'.
             ** destruct (a_qloc st) as [|b0 bs0] eqn:QL0; [exfalso; exact (QNE eq_refl)|]. rewrite <- QL0 in *.
                (nd_pre EKP 6%nat; intros _ _ _ _ _ [LB' LA']; nd_post). destruct EK as ((_ & _ & _ & _ & _ & _ & _ & LEN0 & _) & _).
                rewrite ELST in LB', LA' |- *.
                replace 8192 with (24 + 8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))))))
                  by (rewrite LEN0; clear; lia).
                apply junk_merge; [| apply junk_of_u64arr; exact LA' | clear; lia| rewrite LEN0; clear; lia].
                pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
          -- assert (D4 : (g_drain g = true /\ c'' = K_BATCH_CLASS /\ gl <> 0 /\ aslot_addr L c'' k'' = gl /\ gl <> lst)
                        \/ (g_drain g = false \/ c'' <> K_BATCH_CLASS \/ gl = 0 \/ aslot_addr L c'' k'' <> gl \/ gl = lst)) by (destruct (g_drain g); clear; lia).
             destruct D4 as [(GD & E24 & GNZ & EG & GNL)|NE4].
             ** (* [comment removed for export] *)
                right. rewrite BX. destruct GLF as [[GD' _]|(_ & GQL & [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)])]; [congruence| exfalso; exact (GNZ Z0)|].
                (nd_pre (BQ q ltac:(apply in_or_app; right; exact Hq) E24 ltac:(rewrite EG; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
                rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EG.
                assert (GNE : a_qglob st <> []) by (intros QG0; clear -QG0 Hq LN2; destruct (q_glob Q) eqn:QQ0; [destruct Hq| rewrite QG0 in LN2; cbn in LN2; discriminate]).
                unfold dk_post in DKP. rewrite GD in DKP. (nd_pre DKP 3%nat; intros _ _ GLN; nd_post).
                assert (GF : g_full g = true) by (subst g; unfold g_of; cbn [g_full]; clear -GNE; destruct (a_qglob st); [exfalso; exact (GNE eq_refl)| reflexivity]).
                rewrite GF, GL, <- GQL in GLN.
                replace 8192 with (8 + 8184) by (clear; lia). apply junk_merge; [| | clear; lia | clear; lia].
                +++ pose proof (junk_of_cells m' _ _ GLN) as J. cbn in J. exact J.
                +++ rewrite <- Eq in JQ. destruct (junk_split m gl 8 8184 JQ ltac:(clear; lia) ltac:(clear; lia)) as [_ J2].
                    eapply junk_frame; [exact J2 | exact MUn | exact WM |]. intros _.
                    assert (DL : lst = 0 \/ lst + 8192 <= gl \/ gl + 8192 <= lst).
                    { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql, Eq.
                      destruct (BDIS ql q ltac:(apply in_or_app; left; exact Hql) ltac:(apply in_or_app; right; exact Hq)) as [E|E]; [| exact E].
                      exfalso. apply GNL. rewrite Eq, Eql. symmetry. exact E. }
                    assert (DE : eb = lst \/ eb + 8192 <= gl \/ gl + 8192 <= eb).
                    { destruct EBK as [E|[EAx E]]; [left; exact E| right]. rewrite E, Eq. exact (KDIS q ltac:(apply in_or_app; right; exact Hq) EAx). }
                    apply Kres; clear -F3 F4 RES RHI GNZ DL DE; lia.
             ** (* [comment removed for export] *)
                left. split; [exact BX|]. split.
                +++ assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> (c'' <> K_BATCH_CLASS \/ aslot_addr L c'' k'' <> abatch_addr L (qb_slot q)) ->
                        aslot_addr L c'' k'' + size_of_class c'' <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= aslot_addr L c'' k'').
                    { intros q Hq NE. pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS (qb_slot q) ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk''
                                    (bslot_range L st X Q WF CP q Hq) ltac:(destruct NE as [NE|NE]; [left; exact NE| destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NC']; [right| left; exact NC']];
                                                                                 intros EKK; apply NE; rewrite EKK; reflexivity)) as D.
                      rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                    assert (DW13 : lst = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= lst \/ lst + 8192 <= aslot_addr L c'' k'').
                    { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql. apply DQ; [apply in_or_app; left; exact Hql|].
                      destruct NE3 as [NE|[Z0|NE]]; [left; exact NE| exfalso| right; rewrite <- Eql; exact NE].
                      rewrite Eql in Z0. (nd_pre (BGEO ql ltac:(apply in_or_app; left; exact Hql)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                    assert (DW14 : eb = lst \/ aslot_addr L c'' k'' + size_of_class c'' <= eb \/ eb + 8192 <= aslot_addr L c'' k'').
                    { destruct EBK as [E|[EAx E]]; [left; exact E| right]. rewrite E. (nd_pre (NEWF EAx) 4%nat; intros _ _ KK _; nd_post).
                      pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS k24 ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk'' KK
                                    ltac:(destruct NE2 as [NE|[NE|NE]]; [rewrite EAx in NE; discriminate| left; exact NE| right; exact NE])) as D.
                      rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                    assert (DW15 : gl = lst \/ gl = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= gl \/ gl + 8192 <= aslot_addr L c'' k'').
                    { destruct GLF as [[_ E]|(GD & GQL & [Z0|((q & Hq & Eq) & _)])]; [left; exact E| right; left; exact Z0| right; right].
                      rewrite Eq. apply DQ; [apply in_or_app; right; exact Hq|].
                      destruct NE4 as [NE|[NE|[NE|[NE|NE]]]]; [congruence| left; exact NE| | right; rewrite <- Eq; exact NE| ].
                      - exfalso. rewrite Eq in NE. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -NE B3 RES RHI. lia.
                      - rewrite NE in *. destruct NE3 as [NE'|[Z0|NE']]; [left; exact NE'| exfalso| right; rewrite <- Eq; exact NE'].
                        rewrite Eq in Z0. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                    apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia
                                | clear -DW13 P5 RSP RES RHI; lia | clear -DW14 DW13 P5 RSP RES RHI; lia | clear -DW15 DW13 P5 RSP RES RHI; lia].
                +++ intros b Hb. (nd_pre (busy_of_Some_facts X c'' k'' b Hb) 3%nat; intros IB CB' KB'; nd_post). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U2 : c'' = K_BATCH_CLASS -> aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia | | |].
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 _ F1 F2 A24 U2 U0 U0').
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 _ F1 F2 A24 U2 U0 U0').
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          pose proof (undist_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 _ F1 F2 A24 U2 U0 U0') as D. clear -D. lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update_gen L _ m m' MUn WM st st' X X' c''); [exact SHADOW | apply NDS | exact EC3 | exact EC4 | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk''. left.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        split.
        -- subst X'. rewrite (busy_of_xfreeS X (enq_is_app st) k24 c'' k'').
           destruct (negb (enq_is_app st) && (K_BATCH_CLASS =? c'') && (k24 =? k'')) eqn:T1; [| reflexivity].
           destruct (enq_is_app st) eqn:EAx; [cbn in T1; discriminate|]. cbn [negb andb] in T1.
           destruct (Z.eqb_spec K_BATCH_CLASS c'') as [<-|]; [| discriminate]. destruct (Z.eqb_spec k24 k'') as [<-|]; [| discriminate].
           (nd_pre (NEWF eq_refl) 3%nat; intros _ NBk _; nd_post). rewrite NBk. rewrite size_of_class_24. rewrite slot_shadow_bbatch by (clear; change (shlen 8192) with 1024; lia).
           reflexivity.
        -- pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
           apply Kshad.
           ++ rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
           ++ rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
           ++ apply shlen_nonneg. clear -T16; lia.
           ++ rewrite SHE. destruct SC_r as [D|D].
              ** right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
                 pose proof (shad_mono (al_res L) (aslot_addr L c'' k'') ltac:(clear -P5 RSP; lia)) as MM. clear -HH MM SHL. lia.
              ** left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D P6 RI3; unfold K_SPACE_SIZE in *; lia| clear -AL''; Z.div_mod_to_equations; lia] | clear; lia].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) AU ltac:(clear -U0 RI4; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D U0' RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia].
  }
  (* [comment removed for export] *)
  assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st' m' c'').
  { intros c'' Hc''. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post).
    eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | exact EC4 | exact EC2 | |].
    - intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
      assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
      destruct U0 as [U0 U0'].
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) AU ltac:(clear -U0 RI1; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D U0' RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) AU ltac:(clear -FA1 RI1; unfold K_FREEARR_OFF in *; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D FA2 RI2 RI3; unfold K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia]. }
  (* [comment removed for export] *)
  assert (PD : Permutation (sec_chunks_of st') (sec_chunks_of st)).
  { apply (sec_chunks_of_free_sec st p mb ms n st' LIVE ELIVE). exact (st_after_enq_qfilt_sec st1 ch eq_refl). }
  assert (NOTL : ~ sec_live st' ch) by (apply (sec_not_live_after L st _ p mb ms n st' WFS (Permutation_refl _) LIVE ELIVE)).
  assert (LVE : forall j c, nth_error order j = Some c -> j <> i -> (sec_live st' c <-> sec_live st c)).
  { intros j c Hj NEj. apply (sec_live_other st p mb ms n st' c LIVE ELIVE).
    intros E. apply NEj. destruct WDo as [ND _].
    apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH. unfold ch. rewrite E. reflexivity. }
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p.
  pose proof (ao_ptr L ALO) as OP. (pose proof (aobj_int _ _ OP ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OPi OPa [kP OPs]; nd_post). unfold adisj, aobj in D_t_p, D_p_r, D_n_p, D_s_p, OP.   (* [comment removed for export] *)
  assert (HS' : ASEC_of L st' X' m').
  { unfold ASEC_of, ASECc.
    pose proof HS as HS1. (nd_pre HS1 5%nat; intros _ _ _ _ SHZ0; nd_post).
    split; [| split; [| split; [| split]]].
    - (* [comment removed for export] *) unfold asec_wf. rewrite EPA, WP, ENRES, ENSEC. change (a_nres st1) with (a_nres st). change (a_nsec st1) with (a_nsec st).
      split; [exact ALO|]. split; [reflexivity|]. split; [exact WR|]. split; [rewrite (Permutation_length PD); exact WL|]. split; [exact WB|].
      split; [rewrite Forall_forall in WF1 |- *; intros c Hc; apply WF1; eapply Permutation_in; [exact PD| exact Hc]|].
      eapply sec_disjoint_perm; [apply Permutation_sym; exact PD| exact WD].
    - (* [comment removed for export] *) exists order. rewrite ?ENRES, ?ENSEC. change (a_nres st1) with (a_nres st). change (a_nsec st1) with (a_nsec st).
      split; [eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]|].
      unfold K_HIGH_MEM in *.
      split; [| split].
      + eapply u64arr_frame; [exact U64| exact MUn| exact WM|]. rewrite length_map, LENO.
        apply Kobj; [clear -OP OPi OPs WB WR LENO; lia| clear -OP OPi OPs WB WR; lia| clear -WB; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
      + eapply junk_frame; [exact JK| exact MUn| exact WM|]. intros POS.
        apply Kobj; [clear -OP OPi OPs WB WR POS; lia| clear -OP OPi OPs WB WR; lia| clear -WB POS; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
      + intros j c Hj. destruct (Nat.eq_dec j i) as [->|NEji].
        * (* [comment removed for export] *)
          rewrite NTH in Hj. injection Hj as <-. exists false. split; [split; [discriminate| intros Hl; exfalso; exact (NOTL Hl)]|].
          unfold ch. cbn [asec_chunk]. pose proof CH as CH0. cbn [asec_chunk] in CH0.
          (nd_pre CH0 9%nat; intros G1 G2 G3 G4 _ _ _ _ _; nd_post). unfold SEC_UOFF in *. rewrite <- ?EUB in *.
          replace (UB - 16 + 16) with UB in FC' by (clear; lia).
          split; [eapply cells_frame; [exact G1| exact MUn| exact WM| cbn; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply junk_frame; [exact G2| exact MUn| exact WM| intros _; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply cells_frame; [exact G3| exact MUn| exact WM| cbn; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply junk_frame; [exact G4| exact MUn| exact WM| intros _; apply Kchunk; clear -EUB MSB; lia]|].
          split; [exists b1, ctx; split; [exact HDR'| split; [exact B1| split; [exact B13| exact CTX]]]|].
          split. { replace (ms - 6144) with (8 + (ms - 6144 - 8)) by (clear; lia). apply junk_merge; [| | clear; lia| clear -NMS N6 NB; lia].
                   - pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
                   - eapply junk_frame; [| exact MUn| exact WM| intros POS; apply Kchunk; clear -EUB MSB POS; lia].
                     replace (mb + 6128 + 24) with (UB + 8) in UJ by (rewrite EUB; clear; lia). exact UJ. }
          split; [eapply fill_frame; [exact S1| exact MUn| exact WM| intros _; apply Kshad; clear -SHLO SHHI SHE MSB; unfold AIMG_HI; Z.div_mod_to_equations; lia]|].
          rewrite (granules_rup n) by (clear -NB; lia). rewrite <- EGQ. unfold sec_user_shadow.
          split; [rewrite (granules_rup n) by (clear -NB; lia); rewrite <- EGQ; exact SH'|].
          replace (mb + 6128 + 16) with UB in S3 by (rewrite EUB; clear; lia).
          eapply fill_frame; [exact S3| exact MUn| exact WM| intros POS; apply Kshad; clear -SHLO SHHI SHE SHL SHP POS MSB; unfold AIMG_HI; Z.div_mod_to_equations; lia].
        * (* [comment removed for export] *)
          (nd_pre (PER j c Hj) 3%nat; intros lvj LVj CHj; nd_post). exists lvj. split; [rewrite (LVE j c Hj NEji); exact LVj|].
          assert (INj : In c order) by (eapply nth_error_In; exact Hj).
          pose proof (proj1 (Forall_forall _ _) WF1o c INj) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
          (nd_pre (sec_wf1_facts' L mb' ms' n' Wc) 12%nat; intros JAL JLO JCE _ _ _ JMSB _ _ _ (JC_t & _ & JC_r & _ & JC_n & JC_st & _) _; nd_post).
          assert (NEc : CSec mb' ms' n' <> ch).
          { intros E. apply NEji. destruct WDo as [ND _]. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
          destruct WDo as [_ DJ]. assert (INo : In ch order) by (eapply nth_error_In; exact NTH).
          destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
          all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
          all: unfold K_HIGH_MEM in JLO, JCE.
          all: (pose proof (ablk_lin _ _ JLO) as ndP__; nd_pre ndP__ 4%nat; intros JL1 JL2 JL3 JL4; nd_post); unfold AIMG_HI in JL1; (pose proof (ablk_int _ _ JLO) as ndP__; nd_pre ndP__ 6%nat; intros kJ KAJ KBJ KEJ KCJ KDJ; nd_post).   (* [comment removed for export] *)
          all: eapply asec_chunk_frameD'; [exact MUn| exact Wc| | | | exists (Z.of_nat j); exact CHj].
          all: try (intros Ad kk Z1 Z2 Z3; apply Kobj; [clear -Z1 Z3 JLO JL1 KAJ KBJ KEJ KCJ KDJ; lia| clear -Z3 JCE; lia| clear -Z2; lia| clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_r; lia| clear -Z1 Z3 JC_n; lia| clear -Z1 Z3 JC_st; lia| clear -Z1 Z3 Dc; lia]).
          all: try (pose proof CHj as CH1; cbn [asec_chunk] in CH1; destruct CH1 as (Hh & _);
                    eapply cells_frame; [exact Hh| exact MUn| exact WM| cbn; apply Kobj; [clear -JLO JL1 JMSB KAJ KBJ KEJ KCJ KDJ; lia| clear -JCE JMSB; lia| clear; lia| clear -JC_t JMSB; lia| clear -JC_r JMSB; lia| clear -JC_n JMSB; lia| clear -JC_st JMSB; lia| clear -Dc JMSB; lia]]).
          -- intros Ad kk Z1 Z2 Z3. apply Kshad; [rewrite shad_div in Z1; unfold ASHOFF, AIMG_HI in *; clear -Z1 JLO JL1; Z.div_mod_to_equations; lia| rewrite shad_div in Z3; unfold ASHOFF in *; clear -Z3 JCE JAL8; Z.div_mod_to_equations; lia| clear -Z2; lia|].
             left. rewrite SHE. pose proof (shad_sep _ _ _ Dc JAL8) as HH. rewrite shlen_div in HH. clear -HH Z3. lia.
          -- intros Ad kk Z1 Z2 Z3. apply Kshad; [rewrite shad_div in Z1; unfold ASHOFF, AIMG_HI in *; clear -Z1 JLO JL1; Z.div_mod_to_equations; lia| rewrite shad_div in Z3; unfold ASHOFF in *; clear -Z3 JCE JAL8; Z.div_mod_to_equations; lia| clear -Z2; lia|].
             right. rewrite SHE. pose proof (shad_sep _ _ _ Dc MAL8) as HH. rewrite shlen_div in HH. clear -HH Z1 SHL. lia.
    - (* [comment removed for export] *) (nd_pre SINST 6%nat; intros I1 [srt I2] I3 I4 I5 I6; nd_post). unfold asec_inst. unfold AINSTANCE in *.
      split; [eapply cells_frame; [exact I1| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [exists srt; eapply cells_frame; [exact I2| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply junk_frame; [exact I3| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply junk_frame; [exact I4| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply cells_frame; [exact I5| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      eapply junk_frame; [exact I6| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia].
    - (* [comment removed for export] *) unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MUn| exact WM|]. intros POS.
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -RSP RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP2. unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *. Z.div_mod_to_equations. lia.
      + clear -POS; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) (al_space_beg L) ltac:(clear -RSP; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D SP2 RSP; unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia| clear -SP3; unfold K_ALIGN in SP3; Z.div_mod_to_equations; lia] | clear; lia].
    - (* [comment removed for export] *) intros x Hx HFh HC.
      assert (HC0 : Forall (fun c => ~ (sec_mb c <= x < sec_mb c + sec_ms c)) (sec_chunks_of st)).
      { rewrite Forall_forall in HC |- *. intros c Hin. apply HC. eapply Permutation_in; [apply Permutation_sym; exact PD| exact Hin]. }
      assert (INst : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
      pose proof (proj1 (Forall_forall _ _) HC0 ch INst) as NX. unfold ch in NX. cbn [sec_mb sec_ms] in NX.
      unfold K_HIGH_MEM, AIMG_HI, KLS in Hx.   (* [comment removed for export] *)
      assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM in *; unfold AIMG_HI, KLS in Hx; clear -Hx; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      rewrite <- (SHZ0 x ltac:(unfold K_HIGH_MEM; exact Hx) HFh HC0). apply MUn. rewrite wa_unsigned by exact SX.
      eapply (disjoint_outside _ (shad x) 1); [| clear; lia]. apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -Hx; Z.div_mod_to_equations; lia| rewrite shad_div; unfold ASHOFF; pose proof atop_range as AR8; clear -Hx AR8; Z.div_mod_to_equations; lia| clear; lia|].   (* [comment removed for export] *)
      rewrite SHE. destruct (Z_lt_le_dec x mb) as [LT|GE].
      + left. rewrite !shad_div. clear -LT MAL8. Z.div_mod_to_equations. lia.
      + right. rewrite !shad_div in *. clear -GE NX SHL MAL8 MSAL. Z.div_mod_to_equations. lia. }
  assert (BL' : ablocks L st' X' (lb_remove p LB)).
  { eapply (ablocks_free_sec L st X LB p mb ms n st' X' LIVE WF ELIVE); [| exact BL]. intros y Hy. subst X'. apply In_xfreeS. exact Hy. }
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi FKa [kF FBND]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (SHB : 2148238848 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SHE SHL; lia).   (* [comment removed for export] *)
  assert (HFK' : AFK L (lb_remove p LB) m').
  { eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
    - pose proof (ao_dtls L ALO) as DTO. (pose proof (aobj4_int _ DTO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DBND] [jD DIMG]; nd_post). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE, K_HIGH_MEM in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148238848 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
        rewrite SHE. destruct SC_f as [D|D].
        - right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH. clear -HH SHL. lia.
        - left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [exact D| clear -FKO FKi FBND; Z.div_mod_to_equations; lia] | clear; lia]. }
      (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      assert (LSTR : (lst = 0 /\ qsz lst = 8) \/ (al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104 /\ qsz lst = 8192))   (* [comment removed for export] *)
        by (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; split; [exact Z0| apply qsz_eq0; exact Z0]| right; split; [exact F3| split; [exact F4| apply qsz_pos; clear -F3 RES RHI; lia]]]).
      assert (EBR : al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104 /\ qsz eb = 8192) by (destruct EBF as [Z0|(_ & _ & F3 & F4)]; [exfalso; clear -Z0 EBNZ; lia| split; [assumption| split; [assumption| apply qsz_pos; clear -EBNZ; lia]]]).   (* [comment removed for export] *)
      assert (GLRR : gl = lst \/ gl = 0 \/ (al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104))
        by (destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])]; [left; exact Z2| right; left; exact Z2| right; right; split; assumption]).
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_nil.
    - intros cls FA sz. rewrite (In_lb_remove p LB). cbn. split; [intros [Hin _]; exact Hin| intros Hin; split; [exact Hin| discriminate]]. }
  assert (QH : qhdr L ch 0 = UB - 16) by (unfold ch; cbn [qhdr]; unfold PG; rewrite RZ, EUB; clear; lia).
  (* [comment removed for export] *)
  assert (GNB : g_nb g = Z.of_nat (length (a_qglob st))) by reflexivity.
  assert (GFST : g_fst g = qfirst L (q_glob Q)) by reflexivity.
  assert (GQB : g_qb g = a_qglob_bytes st) by reflexivity.
  assert (GFU : g_full g = match a_qglob st with [] => false | _ :: _ => true end) by reflexivity.
  destruct DKP as [MX' DKP'].
  (pose proof (qnum_free st p ch NUM ltac:(unfold ch; cbn [chunk_size]; clear -NB; lia) NOREC) as ndP__; nd_pre ndP__ 5%nat; intros NUM' NB2a NB2b NB2c NF2; nd_post).
  fold st1 st2 st' in NUM', NB2a, NB2b, NB2c, NF2.
  pose proof (st_after_q st2) as [DRN NDR]. fold st' in DRN, NDR.
  assert (QK' : aquar_glob_const m').
  { split; [| exact MX']. eapply cells_frame; [exact QK | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia. }
  assert (IA' : aintal true m').
  { split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. revert Hj. clear. unfold AIA_MAP1_LEN. intros Hj. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (BLST : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst ->
      abatch_addr L (qb_slot q) + 8192 <= lst \/ lst + 8192 <= abatch_addr L (qb_slot q) \/ lst = 0).
  { intros q Hq NE. destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [right; right; exact Z0|].
    destruct (BDIS q ql Hq ltac:(apply in_or_app; left; exact Hql)) as [E|E]; [exfalso; apply NE; rewrite Eql; exact E| rewrite Eql].
    destruct E as [E|E]; [left; exact E| right; left; exact E]. }
  assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst -> abatch_addr L (qb_slot q) <> gl ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (abatch_addr L (qb_slot q)) 8192).
  { intros q Hq NL NG. (nd_pre (BGEO q Hq) 4%nat; intros _ _ F3 F4; nd_post). pose proof (BLST q Hq NL) as DL.
    assert (DE : eb = lst \/ abatch_addr L (qb_slot q) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot q)).
    { destruct EBK as [E|[EA E]]; [left; exact E| right]. rewrite E.
      destruct (KDIS q Hq EA) as [D|D]; [right; exact D| left; exact D]. }
    assert (DG : gl = lst \/ gl = 0 \/ abatch_addr L (qb_slot q) + 8192 <= gl \/ gl + 8192 <= abatch_addr L (qb_slot q)).
    { destruct GLF as [[_ E]|(_ & _ & [Z0|((qg & Hqg & Eqg) & _)])]; [left; exact E| right; left; exact Z0| right; right].
      destruct (BDIS q qg Hq ltac:(apply in_or_app; right; exact Hqg)) as [E|E]; [exfalso; apply NG; rewrite Eqg; exact E| rewrite Eqg; exact E]. }
    apply Kres; clear -F3 F4 RES RHI DL DE DG; lia. }
  assert (HQ' : AQUAR L st' X' m').
  { subst ek. unfold ek_of in EKP, EK, QC', DKP', EEB, SB1, GDR, GL, GLST.
    destruct (enq_is_app st) eqn:EA; cbn [ek_nb ek_fst ek_lst ek_delta ek_b ek_post ek_pre] in EKP, EK, QC', DKP', EEB, SB1, GDR, GL, GLST.
    - (* [comment removed for export] *)
      (nd_pre EKP 4%nat; intros LB' LA' [bs LJ'] _; nd_post). (nd_pre EK 9%nat; intros _ _ CNT' _ _ _ _ LEN _; nd_post).
      (* [comment removed for export] *)
      pose proof EA as EA0. unfold enq_is_app in EA0. destruct (rev (a_qloc st)) as [|blr rl] eqn:RV; [discriminate|].
      assert (QL : a_qloc st = rev rl ++ [blr]) by (rewrite <- (rev_involutive (a_qloc st)), RV; reflexivity).
      destruct (Z.eqb_spec (b_count blr) Q_BATCH) as [|NFULL]; [discriminate|]. clear EA0.
      set (l := rev rl) in *. set (bl := blr) in *.
      assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL, length_app; cbn; clear; lia).
      assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; clear -LQ; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
      set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
      assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
      assert (LST : List.last (a_qloc st) dummy_batch = bl) by (rewrite QL; apply last_app1). rewrite LST in *.
      assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
      set (bl' := mkABatch (b_count bl + 1) (b_size bl + n) (ch :: b_chunks bl)) in *.
      set (qz' := mkQB (qb_slot qz) (0 :: qb_ks qz)) in *.
      assert (EAPP : enq_app st1 ch = Some (set_qloc (l ++ [bl']) (a_qloc_bytes st1 + n) st1)).
      { unfold enq_app. change (a_qloc st1) with (a_qloc st). rewrite RV. fold bl. replace (b_count bl =? Q_BATCH) with false by (symmetry; apply Z.eqb_neq; exact NFULL).
        subst bl'. reflexivity. }
      assert (Q2 : a_qloc st2 = l ++ [bl'] /\ a_qloc_bytes st2 = a_qloc_bytes st + n /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. subst st1. cbn. repeat split; reflexivity. }
      (nd_pre Q2 4%nat; intros QL2 QB2 QG2 QGB2; nd_post).
      (* [comment removed for export] *)
      unfold abatches in ABL, ABG. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
      cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
      assert (ABl' : abatches_to L m' l ql (hd 0 (qaddrs L [qz']))).
      { cbn [qaddrs map hd qz' qb_slot]. cbn [qaddrs map hd] in ABl. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
        intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
        assert (NEq : abatch_addr L (qb_slot q) <> lst).
        { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post).
          apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
          unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
        apply BFR; [exact INq | exact NEq |].
        destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post); clear -F3 RES RHI; lia|].
        rewrite Eqg. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post). apply in_split in Hqg. (nd_pre Hqg 3%nat; intros gs1 gs2 EQg; nd_post).
        apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
        pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
        unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      assert (ABz' : abatch_cells L m' bl' qz' 0).
      { unfold abatch_cells. cbv zeta. cbn [qb_slot qb_ks b_size b_count b_chunks bl' qz']. rewrite <- QLST. rewrite qhdrs_cons, map_app. cbn [map qhdr]. rewrite QH.
        split; [exact LB'|]. split; [exact LA'|]. split; [| split; [cbn [length]; rewrite Z4; clear; lia| split; [cbn [length]; rewrite Z5; reflexivity| unfold Q_BATCH in *; clear -CNT' Z6; lia]]].
        exists bs. unfold Q_BATCH_BYTES. exact LJ'. }
      assert (ABL' : abatches_to L m' (l ++ [bl']) (ql ++ [qz']) 0).
      { apply abatches_to_app; [exact LNl|]. split; [exact ABl'|]. cbn. split; [exact ABz'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (ql ++ [qz']) (q_glob Q) true (q_pend Q))).
      { subst X'. unfold xfreeS. apply (qcoupled_app_sec L st X Q mb ms n CP st2 l bl ql qz true 0 QL QQ QL2 QG2). }
      subst qz'.
      destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [DR|NDRN].
      + (* [comment removed for export] *)
        (nd_pre (DRN DR) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        destruct DKP' as [GC' GLN].
        exists (mkQConc [] (q_glob Q ++ (ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}])) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length].
             replace (Z.of_nat (length l + 1)) with (Z.of_nat (length (a_qloc st))) by (rewrite QL, length_app; cbn; reflexivity).
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite qlast_reslot, <- QQ, <- ELST.
             assert (FE : qfirst L (q_glob Q ++ ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}]) = (if g_full g then g_fst g else qfirst L (q_loc Q))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). cbn [app]. rewrite qfirst_reslot, <- QQ. reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite qfirst_reslot, <- QQ.
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; clear -LQg; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
                   set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
                   set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
                   assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
                   rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
                   cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
                   assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
                   rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
                   rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
                   +++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
                       intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQg; apply in_or_app; left; exact Hq).
                       assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
                       { intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                         apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       apply BFR; [exact INq | | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
                       rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                       apply (bslots_nodup_split L st X Q CP ql qz gs1 q (gs2 ++ [qgz])); [rewrite QQ, QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                       pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
                       unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
                   +++ cbn [abatches_to]. split; [| exact I].
                       (* [comment removed for export] *)
                       unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q)) (qaddrs L [])) with (qfirst L (q_loc Q)).
                       assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
                       assert (NGL : abatch_addr L (qb_slot qgz) <> lst).
                       { rewrite QLST. intros E. apply (bslots_nodup_split L st X Q CP ql qz qg qgz []); [rewrite QQ, QQg; rewrite <- ?app_assoc; cbn [app]; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
                         pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity).
                       (nd_pre (BGEO qgz INgz) 4%nat; intros _ _ F3 F4; nd_post). pose proof (BLST qgz INgz NGL) as DL.
                       assert (DE : eb = lst \/ abatch_addr L (qb_slot qgz) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot qgz)).
                       { destruct EBK as [E|[EA' E]]; [left; exact E| discriminate]. }
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI DL DE GLS HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_drain L st2 st' X' (mkQConc (ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}]) (q_glob Q) true (q_pend Q)) true CP2 QL3 QG3).
        * exact NUM'.
      + (* [comment removed for export] *)
        pose proof (NDR NDRN) as EST. 
        assert (GD : g_drain g = false) by (rewrite GDR; apply Z.ltb_ge; rewrite <- QB2; exact NDRN).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        exists (mkQConc (ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}]) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite EST, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [| exact ABL'].
          rewrite length_app, qfirst_reslot, qlast_reslot, <- QQ, <- ELST. cbn [length].
          replace (Z.of_nat (length l + 1)) with (Z.of_nat (length (a_qloc st))) by (rewrite QL, length_app; cbn; reflexivity). exact QC'.
        * split; [rewrite <- GNB, <- GFST, <- GL, <- GQB; exact DKP'|].
          unfold abatches. eapply abatches_to_frame; [exact MUn | exact WM | exact ABG |].
          intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
          assert (NEq : abatch_addr L (qb_slot q) <> lst).
          { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
            apply (bslots_nodup_split L st X Q CP ql qz gs1 q gs2); [rewrite QQ, EQg; rewrite <- ?app_assoc; cbn [app]; reflexivity|].
            pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
            unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
          apply BFR; [exact INq | exact NEq | rewrite EGL; unfold dk_glst; rewrite GD; exact NEq].
        * first [rewrite EST | idtac]. exact CP2.
        * first [rewrite <- EST | idtac]. exact NUM'.
    - (* [comment removed for export] *)
      (nd_pre (NEWF eq_refl) 8%nat; intros NK24 NB24 KK24 NIB JK24 FK CIN POS; nd_post).
      (nd_pre EKP 6%nat; intros C24' [stj' SJ'] NBc NAc [bs NJc] OLDc; nd_post).
      assert (EAPP : enq_app st1 ch = None).
      { destruct (enq_app st1 ch) as [sx|] eqn:EAPP; [exfalso| reflexivity].
        assert (EA1 : enq_is_app st1 = true) by (apply (proj2 (enq_is_app_spec st1 ch)); eexists; exact EAPP).
        change (enq_is_app st1) with (enq_is_app st) in EA1. congruence. }
      set (nbt := mkABatch 1 (n + 8192) [ch]) in *.
      set (qn := mkQB k24 [0]) in *.
      assert (Q2 : a_qloc st2 = a_qloc st ++ [nbt] /\ a_qloc_bytes st2 = a_qloc_bytes st + (n + 8192) /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. (pose proof (enq_new_core ch st1) as ndP__; nd_pre ndP__ 7%nat; intros _ E1 E2 _ E3 E4 _; nd_post).
        rewrite E1, E2, E3, E4. subst st1 nbt. unfold ch. cbn [a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_live chunk_size]. fold ch. unfold Q_BATCH_BYTES.
        split; [reflexivity|]. split; [clear; lia|]. split; reflexivity. }
      (nd_pre Q2 4%nat; intros QL2 QB2 QG2 QGB2; nd_post).
      assert (FSTE : (if match a_qloc st with [] => false | _ :: _ => true end then qfirst L (q_loc Q) else abatch_addr L k24) = qfirst L (q_loc Q ++ [qn])).
      { rewrite qfirst_app_r. subst qn; cbn [qb_slot]. generalize LN1. clear. generalize (a_qloc st) (q_loc Q).
        intros [|x1 r1] [|x2 r2] LL; cbn in LL; first [reflexivity | discriminate]. }
      rewrite FSTE in QC'. rewrite FSTE in DKP'.
      assert (QLST' : qlast L (q_loc Q ++ [qn]) = abatch_addr L k24) by (subst qn; apply qlast_app1).
      (* [comment removed for export] *)
      assert (GNL : forall q, In q (q_glob Q) -> abatch_addr L (qb_slot q) <> lst).
      { intros q Hq E. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
        destruct LSTF as [Z0|((q' & Hq' & Eq') & _)].
        - (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post). clear -F3 RES RHI E Z0. lia.
        - apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post). apply in_split in Hq'. (nd_pre Hq' 3%nat; intros qs1 qs2 EQl; nd_post).
          apply (bslots_nodup_split L st X Q CP qs1 q' (qs2 ++ gs1) q gs2); [rewrite EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP q' ltac:(apply in_or_app; left; rewrite EQl; apply in_or_app; right; left; reflexivity)).
          rewrite Eq' in E. unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      (* [comment removed for export] *)
      assert (ABO' : abatches_to L m' (a_qloc st) (q_loc Q) (abatch_addr L k24)).
      { destruct (a_qloc st) as [|b0 l0] eqn:QL0.
        - replace (q_loc Q) with (@nil qbatchc) by (clear -LN1; destruct (q_loc Q); [reflexivity| cbn in LN1; discriminate]). exact I.
        - cbv iota beta in OLDc. destruct OLDc as [OLD1 OLD2]. rewrite <- QL0 in *.
          assert (LNE : a_qloc st <> []) by (rewrite QL0; discriminate).
          assert (QL : a_qloc st = removelast (a_qloc st) ++ [List.last (a_qloc st) dummy_batch]) by (apply app_removelast_last; exact LNE).
          assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL0; cbn; clear; lia).
          assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; clear -LQ; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
          set (l := removelast (a_qloc st)) in *. set (bl := List.last (a_qloc st) dummy_batch) in *.
          set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
          assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
          assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
          assert (FULL : b_count bl = Q_BATCH).
          { pose proof EA as EA0. unfold enq_is_app in EA0. rewrite QL, rev_unit in EA0. cbv iota beta in EA0.
            revert EA0. destruct (Z.eqb_spec (b_count bl) Q_BATCH) as [E|NE]; intros EA0; [exact E| discriminate]. }
          unfold abatches in ABL. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
          cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
          rewrite QL, QQ. apply abatches_to_app; [exact LNl|]. split.
          + cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
            intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
            assert (NEq : abatch_addr L (qb_slot q) <> lst).
            { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post).
              apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
              pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
              unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
            apply BFR; [exact INq | exact NEq |].
            destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post); clear -F3 RES RHI; lia|].
            rewrite Eqg. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post). apply in_split in Hqg. (nd_pre Hqg 3%nat; intros gs1 gs2 EQg; nd_post).
            apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
            pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
            unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
          + cbn [abatches_to]. split; [| exact I].
            unfold abatch_cells. cbv zeta. change (hd (abatch_addr L k24) (qaddrs L [])) with (abatch_addr L k24). rewrite <- QLST.
            split; [rewrite FULL; exact OLD1|]. split; [exact OLD2|]. split; [| split; [exact Z4| split; [exact Z5| exact Z6]]].
            rewrite FULL. replace (Q_BATCH_BYTES - 24 - 8 * Q_BATCH) with 0 by reflexivity. unfold Q_BATCH. apply junk_nil; (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [clear -Z0; lia | atop_facts; clear -F3 F4 RES RHI; lia]). }
      (* [comment removed for export] *)
      assert (ABN' : abatch_cells L m' nbt qn 0).
      { unfold abatch_cells. cbv zeta. subst nbt qn. cbn [qb_slot qb_ks b_size b_count b_chunks]. rewrite qhdrs_cons. cbn [qhdrs app map qhdr]. rewrite QH.
        split; [exact NBc|]. split; [exact NAc|]. split; [exists bs; unfold Q_BATCH_BYTES; exact NJc|]. split; [reflexivity|]. split; [reflexivity| unfold Q_BATCH; clear; lia]. }
      assert (ABL' : abatches_to L m' (a_qloc st ++ [nbt]) (q_loc Q ++ [qn]) 0).
      { apply abatches_to_app; [exact LN1|]. split; [cbn [qaddrs map hd]; subst qn; cbn [qb_slot]; exact ABO'|]. cbn [abatches_to]. split; [exact ABN'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q))).
      { subst X' qn nbt. rewrite ?EA. unfold xfreeS. cbv iota beta.
        apply (qcoupled_new_sec L st X Q mb ms n WF CP st2 k24 (c_count (get_cls st K_BATCH_CLASS)) (n + 8192) true 0 eq_refl POS NK24 QL2 QG2). }
      destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [DR|NDRN].
      + (* [comment removed for export] *)
        (nd_pre (DRN DR) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        destruct DKP' as [GC' GLN].
        exists (mkQConc [] (q_glob Q ++ (q_loc Q ++ [qn])) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite QLST'.
             assert (FE : qfirst L (q_glob Q ++ q_loc Q ++ [qn]) = (if g_full g then g_fst g else qfirst L (q_loc Q ++ [qn]))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate).
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; clear -LQg; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
                   set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
                   set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
                   assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
                   rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
                   cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
                   assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
                   rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
                   rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
                   +++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
                       intros q Hq. assert (INg : In q (q_glob Q)) by (rewrite QQg; apply in_or_app; left; exact Hq).
                       assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INg).
                       assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
                       { intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                         apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       apply BFR; [exact INq | exact (GNL q INg) | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
                   +++ cbn [abatches_to]. split; [| exact I].
                       (* [comment removed for export] *)
                       unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q ++ [qn])) (qaddrs L [])) with (qfirst L (q_loc Q ++ [qn])).
                       assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
                       assert (INgzg : In qgz (q_glob Q)) by (rewrite QQg; apply in_or_app; right; left; reflexivity).
                       assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INgzg).
                       pose proof (GNL qgz INgzg) as NGL.
                       (nd_pre (BGEO qgz INgz) 4%nat; intros _ _ F3 F4; nd_post). pose proof (BLST qgz INgz NGL) as DL.
                       pose proof (KDIS qgz INgz eq_refl) as DE.
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI DL DE EEB GLS HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_drain L st2 st' X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q)) true CP2 QL3 QG3).
        * exact NUM'.
      + (* [comment removed for export] *)
        pose proof (NDR NDRN) as EST.
        assert (GD : g_drain g = false) by (rewrite GDR; apply Z.ltb_ge; rewrite <- QB2; exact NDRN).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        exists (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite EST, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [| exact ABL'].
          rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1. rewrite QLST'. exact QC'.
        * split; [rewrite <- GNB, <- GFST, <- GL, <- GQB; exact DKP'|].
          unfold abatches. eapply abatches_to_frame; [exact MUn | exact WM | exact ABG |].
          intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
          apply BFR; [exact INq | exact (GNL q Hq) | rewrite EGL; unfold dk_glst; rewrite GD; exact (GNL q Hq)].
        * first [rewrite EST | idtac]. exact CP2.
        * first [rewrite <- EST | idtac]. exact NUM'. }
  (* [comment removed for export] *)
  assert (HBK : forall blk, In blk (lb_remove p LB) -> disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (ab_addr blk) (ab_size blk)).
  { intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size]; apply (proj1 (In_lb_remove p LB _)) in Hin; destruct Hin as [Hin NEp]; cbn [ab_kind] in NEp.
    - destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb' & msz' & Lp & EUA & Gs)].
      + destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        pose proof (busy_of_In_nodup L st X b WF Hb) as BOF.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
        (pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (DQ : forall q', In q' (q_loc Q ++ q_glob Q) ->
            aslot_addr L cb kb + size_of_class cb <= abatch_addr L (qb_slot q') \/ abatch_addr L (qb_slot q') + 8192 <= aslot_addr L cb kb).
        { intros q' Hq'. (nd_pre (bslot_busy L st X Q CP q' Hq') 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> qb_slot q').
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2.
            pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq, <- E1, <- E2, BOF in BY. injection BY as EE. subst yq. rewrite Sb in Syq. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS (qb_slot q') ALO WF HCb (K24) HKb (bslot_range L st X Q WF CP q' Hq') NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DK24 : enq_is_app st = false -> aslot_addr L cb kb + size_of_class cb <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= aslot_addr L cb kb).
        { intros EAx. (nd_pre (NEWF EAx) 4%nat; intros _ NBk KK _; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> k24).
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2. rewrite <- E1, <- E2, BOF in NBk. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS k24 ALO WF HCb (K24) HKb KK NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DL : lst = 0 \/ aslot_addr L cb kb + size_of_class cb <= lst \/ lst + 8192 <= aslot_addr L cb kb).
        { destruct LSTF as [Z0|((q' & Hq' & Eq') & _)]; [left; exact Z0| right]. rewrite Eq'. apply DQ. apply in_or_app; left; exact Hq'. }
        assert (DE : eb = lst \/ aslot_addr L cb kb + size_of_class cb <= eb \/ eb + 8192 <= aslot_addr L cb kb).
        { destruct EBK as [E|[EAx E]]; [left; exact E| right]. rewrite E. exact (DK24 EAx). }
        assert (DG : gl = lst \/ gl = 0 \/ aslot_addr L cb kb + size_of_class cb <= gl \/ gl + 8192 <= aslot_addr L cb kb).
        { destruct GLF as [[_ E]|(_ & _ & [Z0|((q' & Hq' & Eq') & _)])]; [left; exact E| right; left; exact Z0| right; right].
          rewrite Eq'. apply DQ. apply in_or_app; right; exact Hq'. }
        apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia
                    | clear -DL FIT P5 RSP RES RHI; lia | clear -DE DL FIT P5 RSP RES RHI; lia | clear -DG DL FIT P5 RSP RES RHI; lia].
      + (* [comment removed for export] *)
        assert (NEq : q <> p) by (intros ->; apply NEp; reflexivity).
        assert (NEc : CSec mb' msz' n' <> ch).
        { intros E. apply NOTL. exists q. rewrite ELIVE, lookup_delete_ne by (intros E'; exact (NEq (eq_sym E'))). rewrite <- E. exact Lp. }
        assert (INc : In (CSec mb' msz' n') (sec_chunks_of st)) by (eapply live_sec_in; exact Lp).
        assert (INs : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
        destruct WD as [_ DJ]. destruct (DJ _ _ INc INs NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
        all: cbn [sec_wf1] in Gs; (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        all: pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF; subst A'; unfold SEC_UOFF, K_HIGH_MEM in *.
        all: unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        all: apply Kobj; [clear -Gs2 Gs4 Gs5 SF; lia| clear -Gs3 Gs4 Gs5 SF; lia| clear -Gs5; lia| clear -Gs4 Gs5 SF Ct; lia| clear -Gs4 Gs5 SF Cr; lia| clear -Gs4 Gs5 SF Cn; lia| clear -Gs4 Gs5 SF Cs; lia| clear -Gs4 Gs5 SF Dc; lia].
    - (nd_pre (FKD cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post). unfold K_HIGH_MEM in *.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia | clear -K1 K3 SC_f; lia]. }
  (* [comment removed for export] *)
  assert (TLSK : forall TA tk, ATPv + -200 <= TA -> TA + tk <= ATPv + 312 -> 0 <= tk ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) TA tk).
  { intros TA tk TH1 TH2 TH3. pose proof ATPv_img as TI. apply Kimg; clear -TH1 TH2 TH3 TI; unfold AIMG_HI; lia. }
  assert (TLSS : forall a', ATPv + -200 <= a' < ATPv + 312 ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros a' Ha'. pose proof ATPv_img as TI. apply Klow; clear -Ha' TI; try (rewrite shad_div; unfold ASHOFF); try Z.div_mod_to_equations; lia. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) (lb_remove p LB) -> forall a', FA <= a' < FA + sz ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros cls FA sz Hin a' Ha'. apply (proj1 (In_lb_remove p LB _)) in Hin. destruct Hin as [Hin _].
    (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). unfold K_HIGH_MEM in *.
    assert (FAL8 : al_fake L mod 8 = 0) by (destruct FKO as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
    apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
    rewrite SHE. destruct SC_f as [D|D].
    - right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
      pose proof (shad_mono (al_fake L) a' ltac:(clear -K1 Ha'; lia)) as MM. clear -HH MM SHL. lia.
    - left. pose proof (shad_sep _ _ _ D FAL8) as HH. rewrite (shad_div a'), (shad_div (al_fake L)), shlen_div in *.
      clear -HH Ha' K3 FAL8. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  split; [apply fp_le_refl|].
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split.
  { eapply (aheap_pres_freeS CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact TLSK | exact TLSS | apply Klow; unfold AIMSH_LO, AIMSH_LEN; clear; lia
      | rewrite <- (ao_ahm_eq L ALO); unfold AAHM_SZ; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI;
      pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; pose proof (ad_ahm_nodes L ALO) as DA3; pose proof (ad_ahm_store L ALO) as DA4;
      (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ SC_ahm; nd_post);
      unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OAH, OAHI, DA1, DA2, DA3, DA4; apply Kobj; clear -OAH OAHI DA1 DA2 DA3 DA4 SC_ahm; lia]. }
  split; [exact ALO|].
  split. { (pose proof ARNG as ndP__; nd_pre ndP__ 14%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 RCl RPA RSC RPSH RTLS; nd_post).
           unfold arng. repeat (split; [assumption|]). split; [| split; [rewrite ENRES; exact RPA| split; [eapply RSEC_perm; [apply Permutation_sym; exact PD| exact RSC]| split; [exact RPSH | exact RTLS]]]].
           intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24a, M24d; exact (RCl K_BATCH_CLASS Hc')| rewrite (GCo' c' NE); exact (RCl c' Hc')]. }
  split; [| exact HFK'].
  exists X'. split; [| exact BL'].
  split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
  split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3'].
Qed.
End Zd1.
#[using="HL CI_OK"] Theorem store_freeS : ltac:(let t := eval cbv delta [store_freeS__stmt] in store_freeS__stmt in exact t).
Proof. exact store_freeS__body. Qed.

(* [comment removed for export] *)
Definition afree_sec_fastP := afree_sec_fast DI AFK CI store_freeS.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.AFreeStoreK.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation WfS sp t UB gq nodes store lst eb gl :=
  ([(sp - 4096, sp); (0xab708, 0xab730); (0xafc00, 0x130c30); (0x13e488, 0x13e48c); (ADEPOT_LO, ADEPOT_HI);
    (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792); (t + 2800, t + 3169);
    (UB - 16, UB + 8); (shad UB, shad UB + gq);
    (nodes, nodes + 1048576); (store, store + 8388608);
    (lst, lst + qsz lst); (eb, eb + qsz eb); (gl, gl + 8)]%Z) (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.
(* [comment removed for export] *)
Local Ltac band_int_k H L U :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (first [ solve [clear - L U; atop_facts; lia] | atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia ]);
      assert (G2 : a + n <= 18446744073709551616) by (first [ solve [clear - L U; atop_facts; lia] | atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia ]);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (first [ solve [clear - L U; atop_facts; lia] | atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia ]);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | _ => band_int H
  end.

(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := solve [fu_focus; lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6307840 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6307840 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Section Kinds.
Variables (sp t mb msz UB gq nodes store res ctx lo lst eb gl : Z).
(* [comment removed for export] *)
Definition kfactsS : Prop :=
     (ATOP <= lo /\ lo <= sp - 4096)
  /\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)
  /\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)
  /\ (ablk mb (mb + msz) /\ mb + 6144 = UB /\ UB + 8 <= mb + msz /\ mb + msz <= ATOP
      /\ (mb + msz <= t \/ t + 4096 <= mb) /\ (mb + msz <= res \/ res + 137439023104 <= mb)
      /\ (mb + msz <= nodes \/ nodes + 1048576 <= mb) /\ (mb + msz <= store \/ store + 8388608 <= mb))
  /\ (2148239360 <= shad mb /\ shad UB = shad mb + 768 /\ 1 <= gq /\ shad UB + gq <= shad mb + msz / 8
      /\ shad mb + msz / 8 <= 17594332446720)
  /\ (sclr nodes 1048576 /\ 6307840 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6307840 <= store /\ store + 8388608 <= ATOP)
  /\ (sclr ctx 65536 /\ 6307840 <= ctx /\ ctx + 65536 <= ATOP)
  /\ ((lst = 0 /\ qsz lst = 8) \/ (res + 4096 <= lst /\ lst + 8192 <= res + 137439023104 /\ qsz lst = 8192))
  /\ ((eb = 0 /\ qsz eb = 8) \/ (res + 4096 <= eb /\ eb + 8192 <= res + 137439023104 /\ qsz eb = 8192))   (* [comment removed for export] *)
  /\ (gl = 0 \/ (res + 4096 <= gl /\ gl + 8192 <= res + 137439023104)).
Hypothesis KF : kfactsS.

(* [comment removed for export] *)
Ltac kind16 tstack timg tt tch tsh tns tlst teb tgl :=
  cbn [disjoint_from];
  split; [tstack|]; split; [timg|]; split; [timg|]; split; [timg|]; split; [timg|];
  split; [tt|]; split; [tt|]; split; [tt|]; split; [tt|];
  split; [tch|]; split; [tsh|]; split; [tns|]; split; [tns|]; split; [tlst|]; split; [teb|]; split; [tgl|]; exact I.
Ltac kfacts := pose proof KF as KF'; unfold kfactsS, AIMG_HI in *;
  sg_set; (nd_pre KF' 10%nat; intros F_lo sgk1 F_res sgk2 F_sh sgk3 sgk4 F_lst F_eb F_gl; nd_post); (nd_pre sgk1 4%nat; intros Ft1 Ft2 Ft3 Ft4; nd_post); (nd_pre sgk2 8%nat; intros C1 C2 C3 C4 C5 C6 C7 C8; nd_post); (nd_pre sgk3 6%nat; intros Fn1 Fn2 Fn3 Fs1 Fs2 Fs3; nd_post); (nd_pre sgk4 3%nat; intros Fc1 Fc2 Fc3; nd_post);
  band_int_k Ft1 Ft3 Ft4; band_int_k Ft2 Ft3 Ft4; band_int_k Fn1 Fn2 Fn3; band_int_k Fs1 Fs2 Fs3; band_int_k Fc1 Fc2 Fc3; band_int C1; clear Ft1 Ft2 Fn1 Fs1 Fc1 C1; sg_unset.   (* [comment removed for export] *)

#[using="rc tlsI mb msz res ctx lo KF"] Lemma KS_img : forall A k, 0x10000 <= A -> 0 <= k ->
  (A + k <= ADEPOT_LO /\ (A + k <= 0xab708 \/ 0xab730 <= A) /\ (A + k <= 0xafc00 \/ 0x130c30 <= A) /\ (A + k <= 0x13e488 \/ 0x13e48c <= A))
  \/ (ADEPOT_HI <= A /\ A + k <= AIMG_HI) ->
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros A k HA HK HD. kfacts.
  kind16 ltac:(clear -HA HK HD F_lo; lia) ltac:(clear -HA HK HD; lia) ltac:(clear -HA HK HD Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2; lia) ltac:(clear -HA HK HD C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1; lia)
         ltac:(clear -HA HK HD C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1 F_sh; lia) ltac:(clear -HA HK HD Fn2 Fn3 KAFn1 KBFn1 KCFn1 Fs2 Fs3 KAFs1 KBFs1 KCFs1; lia)
         ltac:(clear -HA HK HD F_lst F_res; lia) ltac:(clear -HA HK HD F_eb F_res; lia) ltac:(clear -HA HK HD F_gl F_res; lia).
Qed.

#[using="rc tlsI mb msz res ctx lo KF"] Lemma KS_low : forall A k, 2147450880 <= A -> A + k <= 2148239360 -> 0 <= k ->      (* [comment removed for export] *)
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros A k HA HB HK. kfacts.
  kind16 ltac:(clear -HA HB HK F_lo; lia) ltac:(clear -HA HB HK; lia) ltac:(clear -HA HB HK Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2; lia) ltac:(clear -HA HB HK C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1; lia)
         ltac:(clear -HA HB HK C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1 F_sh; lia) ltac:(clear -HA HB HK Fn2 Fn3 KAFn1 KBFn1 KCFn1 Fs2 Fs3 KAFs1 KBFs1 KCFs1; lia)
         ltac:(clear -HA HB HK F_lst F_res; lia) ltac:(clear -HA HB HK F_eb F_res; lia) ltac:(clear -HA HB HK F_gl F_res; lia).
Qed.

#[using="rc tlsI mb msz res ctx lo KF"] Lemma KS_hi : forall A k, sp <= A -> 0 <= k ->
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros A k HA HK. kfacts.
  kind16 ltac:(clear -HA HK; lia) ltac:(clear -HA HK F_lo; lia) ltac:(clear -HA HK F_lo Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2; lia) ltac:(clear -HA HK F_lo C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1; lia)
         ltac:(clear -HA HK F_lo C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1 F_sh; lia) ltac:(clear -HA HK F_lo Fn2 Fn3 KAFn1 KBFn1 KCFn1 Fs2 Fs3 KAFs1 KBFs1 KCFs1; lia)
         ltac:(clear -HA HK F_lo F_lst F_res; lia) ltac:(clear -HA HK F_lo F_eb F_res; lia) ltac:(clear -HA HK F_lo F_gl F_res; lia).
Qed.

#[using="rc tlsI mb msz res ctx lo KF"] Lemma KS_shad : forall A k, 2147446784 <= A -> A + k <= 17594333495296 -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= shad UB \/ shad UB + gq <= A) ->
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros A k HA HB HK HD. kfacts.
  kind16 ltac:(clear -HA HB HK F_lo; lia) ltac:(clear -HA HB HK; lia) ltac:(clear -HA HB HK Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2; lia) ltac:(clear -HA HB HK C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1; lia)
         ltac:(clear -HA HB HK HD; lia) ltac:(clear -HA HB HK Fn2 Fn3 KAFn1 KBFn1 KCFn1 Fs2 Fs3 KAFs1 KBFs1 KCFs1; lia)
         ltac:(clear -HA HB HK F_lst F_res; lia) ltac:(clear -HA HB HK F_eb F_res; lia) ltac:(clear -HA HB HK F_gl F_res; lia).
Qed.

#[using="rc tlsI lo KF"] Lemma KS_ctx :
  (ctx + 65536 <= t \/ t + 4096 <= ctx) -> (ctx + 65536 <= res \/ res + 137439023104 <= ctx) ->
  (ctx + 65536 <= nodes \/ nodes + 1048576 <= ctx) -> (ctx + 65536 <= store \/ store + 8388608 <= ctx) ->
  (mb + msz <= ctx \/ ctx + 65536 <= mb) ->
  forall A k, ctx <= A -> A + k <= ctx + 65536 -> 0 <= k ->
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros D1 D2 D3 D4 D5 A k HA HB HK. kfacts.
  kind16 ltac:(clear -HA HB HK F_lo Fc2 Fc3 KAFc1 KBFc1 KCFc1; lia) ltac:(clear -HA HB HK Fc2 Fc3 KAFc1 KBFc1 KCFc1; lia) ltac:(clear -HA HB HK D1; lia) ltac:(clear -HA HB HK D5 C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1; lia)
         ltac:(clear -HA HB HK Fc2 Fc3 KAFc1 KBFc1 KCFc1 C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1 F_sh; lia) ltac:(clear -HA HB HK D3 D4; lia)
         ltac:(clear -HA HB HK Fc2 Fc3 KAFc1 KBFc1 KCFc1 F_lst D2; lia) ltac:(clear -HA HB HK Fc2 Fc3 KAFc1 KBFc1 KCFc1 F_eb D2; lia) ltac:(clear -HA HB HK Fc2 Fc3 KAFc1 KBFc1 KCFc1 F_gl D2; lia).
Qed.

#[using="rc tlsI mb msz ctx lo KF"] Lemma KS_t :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (t + 4096 <= nodes \/ nodes + 1048576 <= t) -> (t + 4096 <= store \/ store + 8388608 <= t) ->
  forall A k, t <= A -> A + k <= t + 4096 -> 0 <= k ->
  (A + k <= t + 80 \/ t + 112 <= A) -> (A + k <= t + 2128 \/ t + 2132 <= A) -> (A + k <= t + 2784 \/ t + 2792 <= A) -> (A + k <= t + 2800 \/ t + 3169 <= A) ->
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros D1 D2 D3 A k HA HB HK E1 E2 E3 E4. kfacts.
  cbn [disjoint_from].
  split; [clear -HA HB HK F_lo Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2; lia|]. do 4 (split; [clear -HA HB HK Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2; lia|]).
  split; [clear -HA HB HK E1; lia|]. split; [clear -HA HB HK E2; lia|]. split; [clear -HA HB HK E3; lia|]. split; [clear -HA HB HK E4; lia|].
  split; [clear -HA HB HK C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1; lia|]. split; [clear -HA HB HK Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2 C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1 F_sh; lia|]. split; [clear -HA HB HK D2; lia|]. split; [clear -HA HB HK D3; lia|].
  split; [clear -HA HB HK Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2 F_lst D1; lia|]. split; [clear -HA HB HK Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2 F_eb D1; lia|]. split; [clear -HA HB HK Ft3 Ft4 KAFt1 KBFt1 KCFt1 KAFt2 KBFt2 KCFt2 KDFt2 F_gl D1; lia|]. exact I.
Qed.

#[using="rc tlsI mb msz ctx lo KF"] Lemma KS_res :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (nodes + 1048576 <= res \/ res + 137439023104 <= nodes) ->
  (store + 8388608 <= res \/ res + 137439023104 <= store) ->
  forall A k, res <= A -> A + k <= res + 137439023104 -> 0 <= k ->
  (A + k <= lst \/ lst + 8192 <= A) -> (A + k <= eb \/ eb + 8192 <= A) -> (A + k <= gl \/ gl + 8 <= A) ->
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros D1 D2 D3 A k HA HB HK E1 E2 E3. kfacts.
  kind16 ltac:(clear -HA HB HK F_lo F_res; lia) ltac:(clear -HA HB HK F_res; lia) ltac:(clear -HA HB HK D1; lia) ltac:(clear -HA HB HK C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1; lia)
         ltac:(clear -HA HB HK F_res C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1 F_sh; lia) ltac:(clear -HA HB HK D2 D3; lia)
         ltac:(clear -HA HB HK E1 F_lst; lia) ltac:(clear -HA HB HK E2 F_eb; lia) ltac:(clear -HA HB HK E3; lia).
Qed.

(* [comment removed for export] *)
#[using="tlsI ctx lo KF"] Lemma KS_obj : forall A k, ((6307840 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  (A + k <= mb \/ mb + msz <= A) ->
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros A k HA HB HK E1 E2 E3 E4 E5. kfacts.
  kind16 ltac:(clear -HA HB HK F_lo; lia) ltac:(clear -HA HB HK; lia) ltac:(clear -HA HB HK E1; lia) ltac:(clear -HA HB HK E5 C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1; lia)
         ltac:(clear -HA HB HK C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1 F_sh; lia) ltac:(clear -HA HB HK E3 E4; lia)
         ltac:(clear -HA HB HK F_lst E2; lia) ltac:(clear -HA HB HK F_eb E2; lia) ltac:(clear -HA HB HK F_gl E2; lia).
Qed.
(* [comment removed for export] *)
#[using="tlsI ctx lo KF"] Lemma KS_objL : forall A k, (4096 <= A /\ (A + k <= 65536 \/ 6307840 <= A) /\ (A + k <= 2147446784 \/ 17594333495296 <= A)) -> A + k <= ATOP -> 0 <= k ->      
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  (A + k <= mb \/ mb + msz <= A) ->
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros A k HA HB HK E1 E2 E3 E4 E5. kfacts.
  kind16 ltac:(clear -HA HB HK F_lo; lia) ltac:(clear -HA HB HK; lia) ltac:(clear -HA HB HK E1; lia) ltac:(clear -HA HB HK E5 C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1; lia)
         ltac:(clear -HA HB HK C2 C3 C4 C5 C6 C7 C8 KAC1 KBC1 KEC1 KCC1 KDC1 F_sh; lia) ltac:(clear -HA HB HK E3 E4; lia)
         ltac:(clear -HA HB HK F_lst E2; lia) ltac:(clear -HA HB HK F_eb E2; lia) ltac:(clear -HA HB HK F_gl E2; lia).
Qed.

(* [comment removed for export] *)
#[using="rc tlsI res ctx lo KF"] Lemma KS_chunk : forall A k, mb <= A -> A + k <= mb + msz -> 0 <= k -> (A + k <= UB - 16 \/ UB + 8 <= A) ->
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k.
Proof.
  intros A k HA HB HK E1. kfacts.
  kind16 ltac:(clear -HA HB HK F_lo C4; lia) ltac:(clear -HA HB HK KAC1 KBC1 KEC1 KCC1 KDC1; lia) ltac:(clear -HA HB HK C5; lia) ltac:(clear -HA HB HK E1; lia)
         ltac:(clear -HA HB HK KAC1 KBC1 KEC1 KCC1 KDC1 F_sh; lia) ltac:(clear -HA HB HK C7 C8; lia)
         ltac:(clear -HA HB HK F_lst KAC1 KBC1 KEC1 KCC1 KDC1 C6; lia) ltac:(clear -HA HB HK F_eb KAC1 KBC1 KEC1 KCC1 KDC1 C6; lia) ltac:(clear -HA HB HK F_gl KAC1 KBC1 KEC1 KCC1 KDC1 C6; lia).
Qed.
End Kinds.

(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_freeS : forall (CI : list (Z * Z)) sp t mb msz UB gq nodes store res ctx lo lst eb gl (LB : list ablock) m m',
  kfactsS sp t mb msz UB gq nodes store res ctx lo lst eb gl ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                 /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                 /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                 /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI ->
  munch (WfS sp t UB gq nodes store lst eb gl) m m' -> wmono asegs m m' ->
  (forall b, In b LB -> disjoint_from (WfS sp t UB gq nodes store lst eb gl) (ab_addr b) (ab_size b)) ->
  (forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
       disjoint_from (WfS sp t UB gq nodes store lst eb gl) (shad a') 1) ->
  (forall A k, ATPv + -200 <= A -> A + k <= ATPv + 312 -> 0 <= k -> disjoint_from (WfS sp t UB gq nodes store lst eb gl) A k) ->      (* [comment removed for export] *)
  (forall a', ATPv + -200 <= a' < ATPv + 312 -> disjoint_from (WfS sp t UB gq nodes store lst eb gl) (shad a') 1) ->                  (* [comment removed for export] *)
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) AIMSH_LO AIMSH_LEN ->                                                          (* [comment removed for export] *)
  disjoint_from (WfS sp t UB gq nodes store lst eb gl) AAHMv AAHM_SZ ->                                                          (* [comment removed for export] *)
  aheap_pres CI LB sp m m'.
Proof.
  intros CI sp t mb msz UB gq nodes store res ctx lo lst eb gl LB m m' KF CIOK MU WM HBK HFK TLSK TLSS IMSH AHMK a Ha CL.
  split; [| intros Hw; apply WM; exact Hw].
  apply MU. rewrite wa_unsigned by exact Ha.
  destruct CL as [CL|TL]; [| exact (aextra_outside _ a TLSK TLSS IMSH AHMK TL)].
  pose proof KF as KF'. (nd_pre KF' 10%nat; intros F_lo F_t F_res F_ch F_sh F_ns F_ctx F_lst F_eb F_gl; nd_post).
  destruct CL as [ST | [CIa | [BLK | SH]]].
  - eapply disjoint_outside; [eapply (KS_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); lia | lia].
  - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as ndP__; nd_pre ndP__ 6%nat; intros Q1 Q2 Q3 Q4 Q5 Q6; nd_post). cbn [fst snd] in *.
    eapply disjoint_outside; [eapply (KS_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); unfold AIMG_HI in *; clear - Ha R Q1 Q2 Q3 Q4 Q5 Q6; lia | lia].   (* [comment removed for export] *)
  - (nd_pre BLK 3%nat; intros b Hb R; nd_post). eapply disjoint_outside; [exact (HBK b Hb) | lia].
  - (nd_pre SH 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->).
    pose proof (shad_div a') as SD. pose proof (shad_div ATOP) as SDs. pose proof (shad_div mb) as SDm. unfold ASHOFF in *.
    destruct Ha' as [ST | [CIa | FK]].
    + eapply disjoint_outside; [eapply (KS_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: unfold AIMG_HI in *; clear -ST SD SDs SDm F_sh F_lo F_ch; Z.div_mod_to_equations; lia.   (* [comment removed for export] *)
    + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as ndP__; nd_pre ndP__ 4%nat; intros Q1 Q2 Q3 _; nd_post). cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (KS_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: unfold AIMG_HI in *; clear -R SD Q1 Q3; Z.div_mod_to_equations; lia.
    + (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). eapply disjoint_outside; [exact (HFK cls FA sz Hin a' R) | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xfreeS (X : aconc) (app : bool) (k24 : Z) : aconc := if app then X else xbatch X k24.

#[using="Type"] Lemma xfreeS_free : forall X app k24 c', xc_free (x_cls (xfreeS X app k24) c') = xc_free (x_cls X c').
Proof. intros. unfold xfreeS, xbatch. destruct app; cbn; [reflexivity|]. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma xfreeS_cache : forall X app k24 c',
  xc_cache (x_cls (xfreeS X app k24) c') =
  if (negb app) && (c' =? K_BATCH_CLASS) then removelast (xc_cache (x_cls X K_BATCH_CLASS)) else xc_cache (x_cls X c').
Proof.
  intros. unfold xfreeS, xbatch. destruct app; cbn; [reflexivity|]. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [->|]; reflexivity.
Qed.
#[using="Type"] Lemma busy_of_xfreeS : forall X app k24 c' k',
  busy_of (xfreeS X app k24) c' k' = if (negb app) && (K_BATCH_CLASS =? c') && (k24 =? k') then Some (bbatch k24) else busy_of X c' k'.
Proof.
  intros. unfold xfreeS. destruct app; cbn [negb andb]; [reflexivity|]. apply busy_of_xbatch'.
Qed.
#[using="Type"] Lemma In_xfreeS : forall X app k24 y, In y (x_busy X) -> In y (x_busy (xfreeS X app k24)).
Proof. intros X app k24 y Hy. unfold xfreeS. destruct app; [exact Hy|]. apply In_xbatch. right. exact Hy. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.

Definition store_freeS__stmt : Prop := store_freeS_stmt DI AFK CI.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 5).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 6).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 7).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 8).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 9).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 10).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 11).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 12).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 13).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 14).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 15).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 16).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 17).
Variable F : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 18).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 19).
Variable m : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 20).
Variable st : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 21).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 22).
Variable X : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 23).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 24).
Variable p : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 25).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 26).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 27).
Variable n : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 28).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 29).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 30).
Variable A : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 31).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 32).
Variable k24 : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 33).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 34).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'store_freeS__stmt 35).
Let ch := CSec mb ms n.
Let st1 := set_live (delete p (a_live st)) st.
Let st2 := st_enq st1 ch.
Let ek := ek_of L st X Q n k24 stj chunks.
Let g := g_of L st Q (ek_delta ek n).
Let UB := mb + 6144.
Let lst := qlast L (q_loc Q).
Let eb := ek_b ek lst.
Let gl := dk_glst g lst.
Let gq := shlen (rup n 8).
Let st' := st_after st2.
#[using="HL CI_OK ch st1 st2 ek g UB lst eb gl gq st'"] Lemma store_freeS__body : ltac:(let T := type of (fun (h : store_freeS__stmt) => h L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p mb ms n b1 ctx A lo k24 stj chunks) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (F, (fc, (m, (st, (LB, (X, (Q, (p, (mb, (ms, (n, (b1, (ctx, (A, (lo, (k24, (stj, chunks)))))))))))))))))))))))))))))))))))) as _.
  unfold store_freeS_stmt. 
  cbv zeta. intros ALO ARNG AR AQ BL HFK LIVE HIN NQM HDR B1 B13 CTX NEWF NOREC EK DK CEIL LO ms' PM. unfold AFREE_STACK in LO.
  chg (CSec mb ms n) ch.
  chg (set_live (delete p (a_live st)) st) st1.
  chg (st_enq st1 ch) st2.
  chg (ek_of L st X Q n k24 stj chunks) ek.
  chg (g_of L st Q (ek_delta ek n)) g.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS0 UNW; nd_post).
  (nd_pre (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) 3%nat; intros EAu _ WFch; nd_post).
  (nd_pre (sec_wf1_facts' L mb ms n WFch) 13%nat; intros MAL MLO MCE MSE NB RZ MSB MSAL NMS NS0 SCL NPR N6; nd_post).
  (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post). unfold AIMG_HI in ML1. (pose proof (ablk_int _ _ MLO) as ndP__; nd_pre ndP__ 6%nat; intros kM KAM KBM KEM KCM KDM; nd_post).   (* [comment removed for export] *)
  (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros SC_t SC_c SC_r SC_p SC_n SC_st SC_f SC_d SC_tls SC_ahm0; nd_post).
  pose proof HS as HS0. (nd_pre HS0 5%nat; intros WFS _ SINST PZ SHZ; nd_post).
  (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros _ WP WR WL WB WF1 WD; nd_post).
  (nd_pre (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE) 25%nat; intros order i b1r cxr uw PO NTH IL LENO WF1o WDo U64 JK PER CH H1 H5 _ _ _ HUW UJ S1 S2 S3; nd_post).
  cbv zeta in H5, HUW, UJ, S2, S3.
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  (pose proof (aobj4_int _ OT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ OC ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci _ [kC CBND]; nd_post). (pose proof (aobj_int _ _ ON ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni _ [kN NBND]; nd_post).
  (pose proof (aobj_int _ _ OS ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si _ [kS SBND]; nd_post). pose proof (ao_res_hi L ALO) as RHI.
  unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
  box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
  word_range sp SPR.
  chg (mb + 6144) UB.
  assert (EUB : UB = mb + 6144) by reflexivity.
  assert (EHM : mb + 6128 = UB - 16) by (subst UB; clear; lia).
  assert (UB16' : UB mod 8 = 0) by (subst UB; clear -MAL; Z.div_mod_to_equations; lia).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  rewrite EHM in PM, EK, DK, HDR.
  (pose proof (rup8_facts n ltac:(clear -NB; lia)) as ndP__; nd_pre ndP__ 3%nat; intros RUP RUP8 RUPS; nd_post).
  assert (SHGEO : shad UB = shad mb + 768 /\ shlen (rup n 8) <= ms / 8 - 768 /\ 0 < shlen (rup n 8) /\ UB + rup n 8 <= mb + ms
                  /\ 2148239360 <= shad mb /\ shad mb + ms / 8 <= 17594332446720).   (* [comment removed for export] *)
  { subst UB. rewrite !shad_div, RUPS. unfold ASHOFF. (pose proof (sec_facts n ltac:(clear -NB; lia) NPR) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ RS1 _ NSE _; nd_post).
    unfold K_HIGH_MEM in *. pose proof atop_range as AR8. clear -MAL RUP RUP8 RS1 NSE NMS N6 NB ML1 ML3 MCE MSAL AR8. Z.div_mod_to_equations. lia. }
  (nd_pre SHGEO 6%nat; intros SHE SHL SHP UBS SHLO SHHI; nd_post).
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof NUM as NUM0. (nd_pre NUM0 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof CP as CP0. (nd_pre CP0 7%nat; intros LN1 LN2 _ _ ND2 BSI _; nd_post).
  (* [comment removed for export] *)
  pose proof (st_enq_bytes st p (CSec mb ms n) L X Q k24 stj chunks) as SB. cbn [chunk_size] in SB. fold ch in SB.
  assert (CNT : enq_app st1 ch = None -> 0 < c_count (get_cls st K_BATCH_CLASS)).
  { intros E. destruct (enq_is_app st) eqn:EAx.
    - exfalso. assert (EA1 : enq_is_app st1 = true) by exact EAx. destruct (proj1 (enq_is_app_spec st1 ch) EA1) as [s Hs]. congruence.
    - exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NEWF eq_refl)))))))). }
  specialize (SB CNT). fold st1 st2 ek in SB. (nd_pre SB 3%nat; intros SB1 SB2 SB3; nd_post).
  assert (ED0 : 0 <= ek_delta ek n /\ ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; clear -NB; destruct (enq_is_app st); cbn [ek_delta]; lia).
  assert (EBK : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q) \/ (enq_is_app st = false /\ ek_b ek (qlast L (q_loc Q)) = abatch_addr L k24)).
  { subst ek. unfold ek_of. destruct (enq_is_app st) eqn:EAx; cbn [ek_b]; [left; reflexivity| right; split; reflexivity]. }
  assert (EBB : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
      \/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q))).
  { destruct EBK as [E|[EAx E]]; [left; exact E| right; exists k24]. (nd_pre (NEWF EAx) 5%nat; intros NK NBk KK NIB _; nd_post). split; [exact E|]. split; [exact KK| exact NIB]. }
  assert (HMSEP : forall kk, 0 <= kk < ndist st K_BATCH_CLASS -> UB - 16 + 24 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= UB - 16).
  { intros kk KK. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ _ _ _ PERC _; nd_post).
    (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros Q1 Q2 _; nd_post).
    (pose proof (slot_in_region L st K_BATCH_CLASS kk ltac:(rewrite size_of_class_24; lia) (proj1 Q1) KK) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 _; nd_post).
    rewrite size_of_class_24 in P4. subst UB. unfold abatch_addr, aregion, K_REGION, K_FREEARR_OFF, K_BATCH_CLASS in *.
    clear -P5 P4 Q1 Q2 RSP SC_r MSB. lia. }
  (nd_pre (read_dkS (AHQ DI ASEC_of AFK) L st X Q m RNG (UB - 16) ALO ARNG AR AQ HMSEP (ek_b ek (qlast L (q_loc Q))) (ek_delta ek n) ek
              (proj1 ED0) EBB ltac:(rewrite <- SB1, <- SB2; exact NOREC) eq_refl) 4%nat; intros _ _ GL GLST; nd_post).
  fold g in GL, GLST.
  chg (qlast L (q_loc Q)) lst. chg (ek_b ek lst) eb. chg (dk_glst g lst) gl. chg (shlen (rup n 8)) gq.
  (* [comment removed for export] *)
  assert (BGEO : forall q, In q (q_loc Q ++ q_glob Q) ->
      aregion L K_BATCH_CLASS <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
      /\ al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
  { intros q Hq. (pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
    rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
    generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  assert (A24 : c_allocated_user (get_cls st K_BATCH_CLASS) <= K_FREEARR_OFF).
  { (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros Q1 Q2 _; nd_post). lia. }
  assert (LSTF : lst = 0 \/ ((exists q, In q (q_loc Q) /\ lst = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= lst /\ lst + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104)).
  { subst lst. destruct (qlast_cases L (q_loc Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (GDR : g_drain g = (Q_CACHE <? a_qloc_bytes st + ek_delta ek n)) by reflexivity.
  assert (GLF : (g_drain g = false /\ gl = lst)
             \/ (g_drain g = true /\ gl = qlast L (q_glob Q)
                 /\ (gl = 0 \/ ((exists q, In q (q_glob Q) /\ gl = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104)))).
  { subst gl. rewrite GLST, GDR. destruct (Q_CACHE <? a_qloc_bytes st + ek_delta ek n); [right| left; split; reflexivity].
    split; [reflexivity|]. split; [reflexivity|].
    destruct (qlast_cases L (q_glob Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (EBF : eb = 0 \/ (aregion L K_BATCH_CLASS <= eb /\ eb + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104)).
  { subst eb. destruct EBK as [E|[EAx E]].
    - rewrite E. destruct LSTF as [Z0|(_ & FF)]; [left; exact Z0| right; exact FF].
    - right. rewrite E. (nd_pre (NEWF EAx) 4%nat; intros _ _ KK _; nd_post). (pose proof (slot_geo L st X K_BATCH_CLASS k24 ALO WF (K24) KK) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
      rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
      generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  (* [comment removed for export] *)
  (nd_pre PM 19%nat; intros id t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' sj' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MU WM MI' ST' IDR HDR' FC' SH' QC' EKP DKP STATS' LSJ' UW' FL' IAS' IAM' DEP'; nd_post).
  fold lst in MU, QC', EKP, DKP, EBK. fold eb in MU, EBK. fold gl in MU. fold gq in MU, SH'.
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  assert (ELST : lst = qlast L (q_loc Q)) by reflexivity. assert (EEB : eb = ek_b ek lst) by reflexivity.
  assert (EGL : gl = dk_glst g lst) by reflexivity. assert (EGQ : gq = shlen (rup n 8)) by reflexivity.
  clearbody lst eb gl gq.
  (* [comment removed for export] *)
  assert (EBNZ : 0x10007fff8000 <= eb) by (rewrite EEB; exact (ek_pre_b_hi _ _ _ _ _ _ _ _ EK)).   (* [comment removed for export] *)
  replace (eb + 8192) with (eb + qsz eb) in MU by (rewrite (qsz_pos eb) by (clear -EBNZ; lia); reflexivity).   (* [comment removed for export] *)
  assert (MUn : munch (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  clear MU.
  assert (KF : kfactsS (bv_unsigned sp) (al_t L) mb ms UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo lst eb gl).
  { unfold kfactsS. unfold K_HIGH_MEM in *.
    assert (GQ1 : 1 <= gq) by (clear -SHP EGQ; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP MLO ML1 ML3 MCE EUB UBS NB RUP SC_t SC_r SC_n SC_st SHE SHL SHLO SHHI GQ1 EGQ LSTF EBF GLF EBNZ. clear. intros.
    rewrite ?EGQ in SHL. unfold iclr, AIMG_LO, AIMG_HI in *.   (* [comment removed for export] *)
    (destruct LSTF as [Z0|(_ & FF)]; [rewrite (qsz_eq0 lst Z0) | rewrite (qsz_pos lst) by (atop_facts; lia)]);
    (destruct EBF as [Z1|FF1]; [exfalso; atop_facts; lia|]); rewrite (qsz_pos eb) by (atop_facts; lia); destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & FF2)])];
    sg_destr; repeat split; first [assumption | lia]. }
  pose proof (KS_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KS_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KS_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KS_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KS_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s) SC_c) as Kctx.
  pose proof (KS_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
  pose proof (KS_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
  pose proof (KS_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KS_objL _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as KobjL.      (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
  unfold adisj in D_l_t, D_l_r, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
  pose proof (KS_chunk _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kchunk.
  (* [comment removed for export] *)
  assert (SC : same_core st1 (st_after st2) /\ a_cinit (st_after st2) = a_cinit st /\ a_live (st_after st2) = delete p (a_live st) /\ a_next (st_after st2) = a_next st
               /\ a_space_beg (st_after st2) = a_space_beg st /\ a_ptr_array (st_after st2) = a_ptr_array st
               /\ (enq_is_app st = true -> a_cls (st_after st2) = a_cls st)
               /\ (enq_is_app st = false -> a_cls (st_after st2) = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
  { pose proof (st_after_core st2) as [SC2 CL2'].
    assert (SC1 : same_core st1 st2 /\ (enq_is_app st = true -> a_cls st2 = a_cls st) /\ (enq_is_app st = false -> a_cls st2 = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
    { subst st2. unfold st_enq. destruct (enq_app st1 ch) as [sx|] eqn:EAPP.
      - (nd_pre (enq_app_Some st1 _ sx EAPP) 5%nat; intros l bl QL NFz ndR1__; nd_post; revert ndR1__; intros ->). split; [repeat split; intros; reflexivity|].
        split; [intros _; reflexivity|]. intros EAx. exfalso.
        assert (EA1 : enq_is_app st1 = true) by (apply (proj2 (enq_is_app_spec st1 ch)); eexists; exact EAPP).
        change (enq_is_app st1) with (enq_is_app st) in EA1. congruence.
      - (pose proof (enq_new_core ch st1) as ndP__; nd_pre ndP__ 7%nat; intros C1 _ _ _ _ _ C7; nd_post). split; [exact C1|].
        split; [| intros _; exact C7]. intros EAx. exfalso.
        assert (EA1 : enq_is_app st1 = true) by exact EAx. destruct (proj1 (enq_is_app_spec st1 ch) EA1) as [s Hs]. congruence. }
    (nd_pre SC1 3%nat; intros SC1 CLa CLb; nd_post). pose proof (same_core_trans _ _ _ SC1 SC2) as SC3.
    pose proof SC3 as SC0. (nd_pre SC0 8%nat; intros F1 F2 F3 F4 F5 F6 F7 _; nd_post).
    split; [exact SC3|]. split; [exact F3|]. split; [exact F1|]. split; [exact F2|]. split; [exact F4|]. split; [exact F5|].
    split; [intros EAx; rewrite CL2'; exact (CLa EAx)| intros EAx; rewrite CL2'; exact (CLb EAx)]. }
  (nd_pre SC 8%nat; intros SC ECIN ELIVE ENEXT ESB EPA CLa CLb; nd_post).
  pose proof SC as SC0. (nd_pre SC0 12%nat; intros _ _ _ _ _ ENRES ENSEC GCo M24a M24b M24c M24d; nd_post).
  chg (st_after st2) st'.
  set (X' := xfreeS X (enq_is_app st) k24).
  assert (GC24 : get_cls st' K_BATCH_CLASS = (if enq_is_app st then get_cls st K_BATCH_CLASS else cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS))).
  { unfold get_cls at 1. destruct (enq_is_app st) eqn:EAx; [rewrite (CLa eq_refl); reflexivity| rewrite (CLb eq_refl), lookup_insert_eq; reflexivity]. }
  assert (GCo' : forall c', c' <> K_BATCH_CLASS -> get_cls st' c' = get_cls st c') by (intros c' NE; rewrite (GCo c' NE); reflexivity).
  assert (NDS : forall c', ndist st' c' = ndist st c').
  { intros c'. unfold ndist. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24b; reflexivity| rewrite (GCo' c' NE); reflexivity]. }
  assert (MC' : forall c', max_count st' c' = max_count st c') by (intros c'; unfold max_count; rewrite ECIN; reflexivity).
  (* [comment removed for export] *)
  assert (WFst1 : awf L st1 X) by (apply (awf_delete_sec L st X p mb ms n st1 WF LIVE); reflexivity).
  assert (WF' : awf L st' X').
  { subst X'. unfold xfreeS. destruct (enq_is_app st) eqn:EAx.
    - apply (awf_delete_sec L st X p mb ms n st' WF LIVE); [exact ESB| exact EPA| exact ECIN| exact (CLa eq_refl)| exact ELIVE| exact ENEXT].
    - (nd_pre (NEWF eq_refl) 8%nat; intros NK NBk KK NIB JKb FSH CIN POS; nd_post).
      apply (awf_xbatch L st1 X k24 (c_count (get_cls st K_BATCH_CLASS)) WFst1 eq_refl POS NK).
      + exact ESB. + exact EPA. + exact ECIN. + rewrite ELIVE; reflexivity. + exact ENEXT.
      + intros c' NE. rewrite (GCo' c' NE). reflexivity.
      + rewrite GC24. reflexivity. }
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L st' m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | exact ENRES | exact ENSEC | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
  assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
  assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
  (* [comment removed for export] *)
  assert (THR' : athread L st' X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE].
      + destruct (CACHES K_BATCH_CLASS Hc') as [tail (CR & CHc & LCH)]. unfold acache_cells. cbv zeta.
        rewrite GC24, MC', ECIN. subst X'. rewrite xfreeS_cache, Z.eqb_refl, andb_true_r.
        replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR, CHc |- * by (unfold acache_addr, K_BATCH_CLASS; clear; lia).
        subst ek. unfold ek_of in EKP. destruct (enq_is_app st) eqn:EAx; cbn [ek_post negb] in EKP |- *.
        * (nd_pre EKP 5%nat; intros _ _ _ CR' _; nd_post). exists tail. split; [exact CR'|]. split; [| exact LCH].
          eapply u32arr_frame; [exact CHc | exact MUn | exact WM |]. rewrite length_app, length_map. apply Kt; clear -LCH; lia.
        * destruct EKP as (CR' & _). (nd_pre (NEWF eq_refl) 8%nat; intros NK NBk KK NIB JKb FSH CIN POS; nd_post).
          cbn [c_count cls_set_count]. exists (Z_to_bv 64 (acompact K_BATCH_CLASS k24) :: tail).
          pose proof (cache24_split L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK) as [CACHE LRL].
          split; [exact CR'|]. split.
          -- eapply u32arr_frame; [| exact MUn | exact WM |].
             ++ rewrite CACHE, map_app in CHc. cbn [map] in CHc. rewrite <- app_assoc in CHc. cbn [app] in CHc. exact CHc.
             ++ rewrite length_app, length_map. cbn [length].
                replace (length (removelast (xc_cache (x_cls X K_BATCH_CLASS))) + Datatypes.S (length tail))%nat with 16%nat
                  by (rewrite CACHE, length_app in LCH; cbn [length] in LCH; clear -LCH; lia).
                apply Kt; clear; lia.
          -- cbn [length]. rewrite CACHE, length_app in LCH. cbn [length] in LCH. clear -LCH. lia.
      + eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | rewrite (GCo' c' NE); reflexivity | exact ECIN | |].
        * subst X'. rewrite xfreeS_cache. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [E|_]; [exfalso; exact (NE E)|]. rewrite andb_false_r. reflexivity.
        * unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply Kt; clear -Hc' NE; lia.
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + eapply junk_frame; [exact (proj1 (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia))) | exact MUn | exact WM | intros _; apply Kt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia).
          assert (STJ' : exists w : word, rw_cells asegs m' (al_t L + 2784) [C8 w]).
          { subst ek. unfold ek_of in EKP. destruct (enq_is_app st); cbn [ek_post] in EKP.
            - (nd_pre EKP 5%nat; intros _ _ _ _ STS'; nd_post). exists stj. exact STS'.
            - (nd_pre EKP 3%nat; intros _ STS' _; nd_post). exact STS'. }
          destruct STJ' as [w STS']. pose proof (junk_of_cells m' _ _ STS') as J. cbn in J. exact J.
        * replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) by (clear; lia).
          eapply junk_frame; [| exact MUn | exact WM | intros _; apply Kt; clear; lia].
          pose proof (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ CSb].
          pose proof (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(clear; lia) ltac:(clear; lia)) as [_ CSc].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by (clear; lia). exact CSc.
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  (* [comment removed for export] *)
  assert (BDIS : forall q1 q2, In q1 (q_loc Q ++ q_glob Q) -> In q2 (q_loc Q ++ q_glob Q) ->
      abatch_addr L (qb_slot q1) = abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q1) + 8192 <= abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q2) + 8192 <= abatch_addr L (qb_slot q1)).
  { intros q1 q2 Hq1 Hq2. destruct (Z.eq_dec (qb_slot q1) (qb_slot q2)) as [E|NE]; [left; rewrite E; reflexivity| right].
    pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot q1) (qb_slot q2) ltac:(pose proof (bslot_range L st X Q WF CP q1 Hq1); lia)
                  ltac:(pose proof (bslot_range L st X Q WF CP q2 Hq2); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (KDIS : forall q, In q (q_loc Q ++ q_glob Q) -> enq_is_app st = false ->
      abatch_addr L k24 + 8192 <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= abatch_addr L k24).
  { intros q Hq EAx. (nd_pre (NEWF EAx) 5%nat; intros NK NBk KK NIB _; nd_post).
    assert (NE : k24 <> qb_slot q) by (intros ->; apply NIB; apply in_map; exact Hq).
    pose proof (slots_disjoint L K_BATCH_CLASS k24 (qb_slot q) ltac:(lia) ltac:(pose proof (bslot_range L st X Q WF CP q Hq); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L st' m' c'' /\ afreearray L st' X' m' c'' /\ aslots L st' X' m' c'' /\ aslot_shadow L st' X' m' c'').
  { intros c'' Hc''. (nd_pre (CLS c'' Hc'') 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC1 : c_num_freed (get_cls st' c'') = c_num_freed (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24c| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC3 : c_allocated_user (get_cls st' c'') = c_allocated_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24b| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 4%nat; intros RI1 RI2 RI3 RI4; nd_post).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | exact EC1 | exact EC2 | exact EC3 | exact EC4 |].
      unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      apply Kres; try (clear -Hc'' RSP; lia).
      + destruct LSTF as [Z0|(_ & F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + destruct EBF as [Z0|(F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + assert (GLR : gl = 0 \/ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)).
        { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; exact F2].
          destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; exact F2]. }
        destruct GLR as [Z0|F2]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | exact EC1 | exact EC2 | | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + subst X'. apply xfreeS_free.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia | | |].
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          pose proof (farr_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2) as D. clear -D. lia.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, AIMG_HI, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
          rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) (afreearr L c'') ltac:(clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D RI2 RI3 FA2; lia| exact AM] | clear; lia].
    - (* [comment removed for export] *)
      eapply (aslots_update_gen L _ m m' MUn WM st st' X X' c''); [exact SLOTS | apply NDS | exact EC3 | exact EC4 | |].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D2 : (enq_is_app st = false /\ c'' = K_BATCH_CLASS /\ k'' = k24) \/ (enq_is_app st = true \/ c'' <> K_BATCH_CLASS \/ k'' <> k24))
          by (clear; destruct (enq_is_app st); lia).
        destruct D2 as [(EAx & E24 & EK24)|NE2].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X'. rewrite (busy_of_xfreeS X (enq_is_app st) k24 K_BATCH_CLASS k24), EAx. cbn [negb andb]. rewrite !Z.eqb_refl. cbn [andb].
          unfold aslot_busy, bbatch. cbn [xb_st xb_class xb_slot]. unfold xb_alloc. cbn [xb_class xb_slot]. rewrite size_of_class_24.
          subst ek. unfold ek_of in EKP. rewrite EAx in EKP. cbn [ek_post] in EKP. (nd_pre EKP 6%nat; intros _ _ BC BA [bsb BJ] _; nd_post).
          fold (abatch_addr L k24) in BC, BA, BJ |- *. change (aslot_addr L K_BATCH_CLASS k24) with (abatch_addr L k24).
          replace 8192 with (24 + (8 * Z.of_nat (length [Z_to_bv 64 (UB - 16)]) + (8192 - 24 - 8 * 1))) by (cbn; lia).
          apply junk_merge; [| | clear; lia| cbn; clear; lia].
          -- pose proof (junk_of_cells m' _ _ BC) as J. cbn in J. exact J.
          -- apply junk_merge; [apply junk_of_u64arr; exact BA | | cbn; clear; lia | clear; lia].
             cbn [length Z.of_nat Pos.of_succ_nat]. eexists. exact BJ.
        * assert (T1 : negb (enq_is_app st) && (K_BATCH_CLASS =? c'') && (k24 =? k'') = false).
          { destruct (enq_is_app st); cbn [negb andb]; [reflexivity|].
            destruct (Z.eqb_spec K_BATCH_CLASS c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k24 k'') as [E'|]; [| reflexivity]. exfalso.
            destruct NE2 as [NE|[NE|NE]]; [discriminate| apply NE; symmetry; exact E| apply NE; symmetry; exact E']. }
          assert (BX : busy_of X' c'' k'' = busy_of X c'' k'').
          { subst X'. rewrite (busy_of_xfreeS X (enq_is_app st) k24 c'' k''), T1. reflexivity. }
          (* [comment removed for export] *)
          assert (BQ : forall q, In q (q_loc Q ++ q_glob Q) -> c'' = K_BATCH_CLASS -> aslot_addr L c'' k'' = abatch_addr L (qb_slot q) ->
              exists yq, busy_of X c'' k'' = Some yq /\ xb_st yq = BBatch /\ xb_class yq = K_BATCH_CLASS /\ xb_slot yq = k''
                         /\ junk_at m (abatch_addr L (qb_slot q)) 8192 /\ k'' = qb_slot q).
          { intros q Hq -> EQA. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
            assert (EK' : k'' = qb_slot q) by (unfold abatch_addr, aslot_addr in EQA; rewrite size_of_class_24 in EQA; clear -EQA; lia). subst k''.
            exists yq. pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq in BY.
            split; [exact BY|]. split; [exact Syq|]. split; [exact Cyq|]. split; [exact Kyq|]. split; [| reflexivity].
            destruct SLOTS as [SLK _]. specialize (SLK (qb_slot q) Hk''). rewrite BY in SLK. unfold aslot_busy in SLK. rewrite Syq in SLK.
            unfold xb_alloc in SLK. rewrite Cyq, Kyq, size_of_class_24 in SLK. exact SLK. }
          assert (D3 : (c'' = K_BATCH_CLASS /\ lst <> 0 /\ aslot_addr L c'' k'' = lst) \/ (c'' <> K_BATCH_CLASS \/ lst = 0 \/ aslot_addr L c'' k'' <> lst)) by (clear; lia).
          destruct D3 as [(E24 & LNZ & EL)|NE3].
          -- (* [comment removed for export] *)
             right. rewrite BX. destruct LSTF as [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)]; [exfalso; exact (LNZ Z0)|].
             (nd_pre (BQ q ltac:(apply in_or_app; left; exact Hq) E24 ltac:(rewrite EL; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
             rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EL.
             assert (QNE : a_qloc st <> []) by (intros QL0; apply LNZ; rewrite ELST; replace (q_loc Q) with (@nil qbatchc) by (clear -QL0 LN1; destruct (q_loc Q); [reflexivity| rewrite QL0 in LN1; cbn in LN1; discriminate]); reflexivity).
             subst ek. unfold ek_of in EKP, EK. destruct (enq_is_app st) eqn:EAx; cbn [ek_post ek_pre] in EKP, EK.
             ** (nd_pre EKP 4%nat; intros LB' LA' [bs LJ'] _; nd_post). (nd_pre EK 9%nat; intros _ _ CNT' _ _ _ _ LEN _; nd_post).
                rewrite ELST in LB', LA', LJ' |- *.
                set (cnt := b_count (List.last (a_qloc st) dummy_batch)) in *.
                replace 8192 with (24 + (8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))) ++ [Z_to_bv 64 (UB - 16)])) + (8192 - 24 - 8 * (cnt + 1))))
                  by (rewrite length_app, LEN; cbn [length]; clear -CNT'; lia).
                apply junk_merge; [| | clear; lia| rewrite length_app, LEN; cbn [length]; clear -CNT'; lia].
                +++ pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
                +++ apply junk_merge; [apply junk_of_u64arr; exact LA' | | rewrite length_app, LEN; cbn [length]; clear -CNT'; lia | clear -CNT'; lia].
                    rewrite length_app, LEN. cbn [length]. replace (8 * Z.of_nat (Z.to_nat cnt + 1)) with (8 * (cnt + 1)) by (clear -CNT'; lia). eexists. exact LJ'.
             ** destruct (a_qloc st) as [|b0 bs0] eqn:QL0; [exfalso; exact (QNE eq_refl)|]. rewrite <- QL0 in *.
                (nd_pre EKP 6%nat; intros _ _ _ _ _ [LB' LA']; nd_post). destruct EK as ((_ & _ & _ & _ & _ & _ & _ & LEN0 & _) & _).
                rewrite ELST in LB', LA' |- *.
                replace 8192 with (24 + 8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))))))
                  by (rewrite LEN0; clear; lia).
                apply junk_merge; [| apply junk_of_u64arr; exact LA' | clear; lia| rewrite LEN0; clear; lia].
                pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
          -- assert (D4 : (g_drain g = true /\ c'' = K_BATCH_CLASS /\ gl <> 0 /\ aslot_addr L c'' k'' = gl /\ gl <> lst)
                        \/ (g_drain g = false \/ c'' <> K_BATCH_CLASS \/ gl = 0 \/ aslot_addr L c'' k'' <> gl \/ gl = lst)) by (destruct (g_drain g); clear; lia).
             destruct D4 as [(GD & E24 & GNZ & EG & GNL)|NE4].
             ** (* [comment removed for export] *)
                right. rewrite BX. destruct GLF as [[GD' _]|(_ & GQL & [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)])]; [congruence| exfalso; exact (GNZ Z0)|].
                (nd_pre (BQ q ltac:(apply in_or_app; right; exact Hq) E24 ltac:(rewrite EG; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
                rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EG.
                assert (GNE : a_qglob st <> []) by (intros QG0; clear -QG0 Hq LN2; destruct (q_glob Q) eqn:QQ0; [destruct Hq| rewrite QG0 in LN2; cbn in LN2; discriminate]).
                unfold dk_post in DKP. rewrite GD in DKP. (nd_pre DKP 3%nat; intros _ _ GLN; nd_post).
                assert (GF : g_full g = true) by (subst g; unfold g_of; cbn [g_full]; clear -GNE; destruct (a_qglob st); [exfalso; exact (GNE eq_refl)| reflexivity]).
                rewrite GF, GL, <- GQL in GLN.
                replace 8192 with (8 + 8184) by (clear; lia). apply junk_merge; [| | clear; lia | clear; lia].
                +++ pose proof (junk_of_cells m' _ _ GLN) as J. cbn in J. exact J.
                +++ rewrite <- Eq in JQ. destruct (junk_split m gl 8 8184 JQ ltac:(clear; lia) ltac:(clear; lia)) as [_ J2].
                    eapply junk_frame; [exact J2 | exact MUn | exact WM |]. intros _.
                    assert (DL : lst = 0 \/ lst + 8192 <= gl \/ gl + 8192 <= lst).
                    { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql, Eq.
                      destruct (BDIS ql q ltac:(apply in_or_app; left; exact Hql) ltac:(apply in_or_app; right; exact Hq)) as [E|E]; [| exact E].
                      exfalso. apply GNL. rewrite Eq, Eql. symmetry. exact E. }
                    assert (DE : eb = lst \/ eb + 8192 <= gl \/ gl + 8192 <= eb).
                    { destruct EBK as [E|[EAx E]]; [left; exact E| right]. rewrite E, Eq. exact (KDIS q ltac:(apply in_or_app; right; exact Hq) EAx). }
                    apply Kres; clear -F3 F4 RES RHI GNZ DL DE; lia.
             ** (* [comment removed for export] *)
                left. split; [exact BX|]. split.
                +++ assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> (c'' <> K_BATCH_CLASS \/ aslot_addr L c'' k'' <> abatch_addr L (qb_slot q)) ->
                        aslot_addr L c'' k'' + size_of_class c'' <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= aslot_addr L c'' k'').
                    { intros q Hq NE. pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS (qb_slot q) ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk''
                                    (bslot_range L st X Q WF CP q Hq) ltac:(destruct NE as [NE|NE]; [left; exact NE| destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NC']; [right| left; exact NC']];
                                                                                 intros EKK; apply NE; rewrite EKK; reflexivity)) as D.
                      rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                    assert (DW13 : lst = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= lst \/ lst + 8192 <= aslot_addr L c'' k'').
                    { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql. apply DQ; [apply in_or_app; left; exact Hql|].
                      destruct NE3 as [NE|[Z0|NE]]; [left; exact NE| exfalso| right; rewrite <- Eql; exact NE].
                      rewrite Eql in Z0. (nd_pre (BGEO ql ltac:(apply in_or_app; left; exact Hql)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                    assert (DW14 : eb = lst \/ aslot_addr L c'' k'' + size_of_class c'' <= eb \/ eb + 8192 <= aslot_addr L c'' k'').
                    { destruct EBK as [E|[EAx E]]; [left; exact E| right]. rewrite E. (nd_pre (NEWF EAx) 4%nat; intros _ _ KK _; nd_post).
                      pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS k24 ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk'' KK
                                    ltac:(destruct NE2 as [NE|[NE|NE]]; [rewrite EAx in NE; discriminate| left; exact NE| right; exact NE])) as D.
                      rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                    assert (DW15 : gl = lst \/ gl = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= gl \/ gl + 8192 <= aslot_addr L c'' k'').
                    { destruct GLF as [[_ E]|(GD & GQL & [Z0|((q & Hq & Eq) & _)])]; [left; exact E| right; left; exact Z0| right; right].
                      rewrite Eq. apply DQ; [apply in_or_app; right; exact Hq|].
                      destruct NE4 as [NE|[NE|[NE|[NE|NE]]]]; [congruence| left; exact NE| | right; rewrite <- Eq; exact NE| ].
                      - exfalso. rewrite Eq in NE. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -NE B3 RES RHI. lia.
                      - rewrite NE in *. destruct NE3 as [NE'|[Z0|NE']]; [left; exact NE'| exfalso| right; rewrite <- Eq; exact NE'].
                        rewrite Eq in Z0. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                    apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia
                                | clear -DW13 P5 RSP RES RHI; lia | clear -DW14 DW13 P5 RSP RES RHI; lia | clear -DW15 DW13 P5 RSP RES RHI; lia].
                +++ intros b Hb. (nd_pre (busy_of_Some_facts X c'' k'' b Hb) 3%nat; intros IB CB' KB'; nd_post). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U2 : c'' = K_BATCH_CLASS -> aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia | | |].
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 _ F1 F2 A24 U2 U0 U0').
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 _ F1 F2 A24 U2 U0 U0').
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          pose proof (undist_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 _ F1 F2 A24 U2 U0 U0') as D. clear -D. lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update_gen L _ m m' MUn WM st st' X X' c''); [exact SHADOW | apply NDS | exact EC3 | exact EC4 | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk''. left.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        split.
        -- subst X'. rewrite (busy_of_xfreeS X (enq_is_app st) k24 c'' k'').
           destruct (negb (enq_is_app st) && (K_BATCH_CLASS =? c'') && (k24 =? k'')) eqn:T1; [| reflexivity].
           destruct (enq_is_app st) eqn:EAx; [cbn in T1; discriminate|]. cbn [negb andb] in T1.
           destruct (Z.eqb_spec K_BATCH_CLASS c'') as [<-|]; [| discriminate]. destruct (Z.eqb_spec k24 k'') as [<-|]; [| discriminate].
           (nd_pre (NEWF eq_refl) 3%nat; intros _ NBk _; nd_post). rewrite NBk. rewrite size_of_class_24. rewrite slot_shadow_bbatch by (clear; change (shlen 8192) with 1024; lia).
           reflexivity.
        -- pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
           apply Kshad.
           ++ rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
           ++ rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
           ++ apply shlen_nonneg. clear -T16; lia.
           ++ rewrite SHE. destruct SC_r as [D|D].
              ** right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
                 pose proof (shad_mono (al_res L) (aslot_addr L c'' k'') ltac:(clear -P5 RSP; lia)) as MM. clear -HH MM SHL. lia.
              ** left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D P6 RI3; unfold K_SPACE_SIZE in *; lia| clear -AL''; Z.div_mod_to_equations; lia] | clear; lia].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) AU ltac:(clear -U0 RI4; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D U0' RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia].
  }
  (* [comment removed for export] *)
  assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st' m' c'').
  { intros c'' Hc''. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post).
    eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | exact EC4 | exact EC2 | |].
    - intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
      assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
      destruct U0 as [U0 U0'].
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) AU ltac:(clear -U0 RI1; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D U0' RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) AU ltac:(clear -FA1 RI1; unfold K_FREEARR_OFF in *; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D FA2 RI2 RI3; unfold K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia]. }
  (* [comment removed for export] *)
  assert (PD : Permutation (sec_chunks_of st') (sec_chunks_of st)).
  { apply (sec_chunks_of_free_sec st p mb ms n st' LIVE ELIVE). exact (st_after_enq_qfilt_sec st1 ch eq_refl). }
  assert (NOTL : ~ sec_live st' ch) by (apply (sec_not_live_after L st _ p mb ms n st' WFS (Permutation_refl _) LIVE ELIVE)).
  assert (LVE : forall j c, nth_error order j = Some c -> j <> i -> (sec_live st' c <-> sec_live st c)).
  { intros j c Hj NEj. apply (sec_live_other st p mb ms n st' c LIVE ELIVE).
    intros E. apply NEj. destruct WDo as [ND _].
    apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH. unfold ch. rewrite E. reflexivity. }
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p.
  pose proof (ao_ptr L ALO) as OP. (pose proof (aobj_int _ _ OP ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OPi OPa [kP OPs]; nd_post). unfold adisj, aobj in D_t_p, D_p_r, D_n_p, D_s_p, OP.   (* [comment removed for export] *)
  assert (HS' : ASEC_of L st' X' m').
  { unfold ASEC_of, ASECc.
    pose proof HS as HS1. (nd_pre HS1 5%nat; intros _ _ _ _ SHZ0; nd_post).
    split; [| split; [| split; [| split]]].
    - (* [comment removed for export] *) unfold asec_wf. rewrite EPA, WP, ENRES, ENSEC. change (a_nres st1) with (a_nres st). change (a_nsec st1) with (a_nsec st).
      split; [exact ALO|]. split; [reflexivity|]. split; [exact WR|]. split; [rewrite (Permutation_length PD); exact WL|]. split; [exact WB|].
      split; [rewrite Forall_forall in WF1 |- *; intros c Hc; apply WF1; eapply Permutation_in; [exact PD| exact Hc]|].
      eapply sec_disjoint_perm; [apply Permutation_sym; exact PD| exact WD].
    - (* [comment removed for export] *) exists order. rewrite ?ENRES, ?ENSEC. change (a_nres st1) with (a_nres st). change (a_nsec st1) with (a_nsec st).
      split; [eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]|].
      unfold K_HIGH_MEM in *.
      split; [| split].
      + eapply u64arr_frame; [exact U64| exact MUn| exact WM|]. rewrite length_map, LENO.
        apply Kobj; [clear -OP OPi OPs WB WR LENO; lia| clear -OP OPi OPs WB WR; lia| clear -WB; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
      + eapply junk_frame; [exact JK| exact MUn| exact WM|]. intros POS.
        apply Kobj; [clear -OP OPi OPs WB WR POS; lia| clear -OP OPi OPs WB WR; lia| clear -WB POS; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
      + intros j c Hj. destruct (Nat.eq_dec j i) as [->|NEji].
        * (* [comment removed for export] *)
          rewrite NTH in Hj. injection Hj as <-. exists false. split; [split; [discriminate| intros Hl; exfalso; exact (NOTL Hl)]|].
          unfold ch. cbn [asec_chunk]. pose proof CH as CH0. cbn [asec_chunk] in CH0.
          (nd_pre CH0 9%nat; intros G1 G2 G3 G4 _ _ _ _ _; nd_post). unfold SEC_UOFF in *. rewrite <- ?EUB in *.
          replace (UB - 16 + 16) with UB in FC' by (clear; lia).
          split; [eapply cells_frame; [exact G1| exact MUn| exact WM| cbn; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply junk_frame; [exact G2| exact MUn| exact WM| intros _; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply cells_frame; [exact G3| exact MUn| exact WM| cbn; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply junk_frame; [exact G4| exact MUn| exact WM| intros _; apply Kchunk; clear -EUB MSB; lia]|].
          split; [exists b1, ctx; split; [exact HDR'| split; [exact B1| split; [exact B13| exact CTX]]]|].
          split. { replace (ms - 6144) with (8 + (ms - 6144 - 8)) by (clear; lia). apply junk_merge; [| | clear; lia| clear -NMS N6 NB; lia].
                   - pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
                   - eapply junk_frame; [| exact MUn| exact WM| intros POS; apply Kchunk; clear -EUB MSB POS; lia].
                     replace (mb + 6128 + 24) with (UB + 8) in UJ by (rewrite EUB; clear; lia). exact UJ. }
          split; [eapply fill_frame; [exact S1| exact MUn| exact WM| intros _; apply Kshad; clear -SHLO SHHI SHE MSB; unfold AIMG_HI; Z.div_mod_to_equations; lia]|].
          rewrite (granules_rup n) by (clear -NB; lia). rewrite <- EGQ. unfold sec_user_shadow.
          split; [rewrite (granules_rup n) by (clear -NB; lia); rewrite <- EGQ; exact SH'|].
          replace (mb + 6128 + 16) with UB in S3 by (rewrite EUB; clear; lia).
          eapply fill_frame; [exact S3| exact MUn| exact WM| intros POS; apply Kshad; clear -SHLO SHHI SHE SHL SHP POS MSB; unfold AIMG_HI; Z.div_mod_to_equations; lia].
        * (* [comment removed for export] *)
          (nd_pre (PER j c Hj) 3%nat; intros lvj LVj CHj; nd_post). exists lvj. split; [rewrite (LVE j c Hj NEji); exact LVj|].
          assert (INj : In c order) by (eapply nth_error_In; exact Hj).
          pose proof (proj1 (Forall_forall _ _) WF1o c INj) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
          (nd_pre (sec_wf1_facts' L mb' ms' n' Wc) 12%nat; intros JAL JLO JCE _ _ _ JMSB _ _ _ (JC_t & _ & JC_r & _ & JC_n & JC_st & _) _; nd_post).
          assert (NEc : CSec mb' ms' n' <> ch).
          { intros E. apply NEji. destruct WDo as [ND _]. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
          destruct WDo as [_ DJ]. assert (INo : In ch order) by (eapply nth_error_In; exact NTH).
          destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
          all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
          all: unfold K_HIGH_MEM in JLO, JCE.
          all: (pose proof (ablk_lin _ _ JLO) as ndP__; nd_pre ndP__ 4%nat; intros JL1 JL2 JL3 JL4; nd_post); unfold AIMG_HI in JL1; (pose proof (ablk_int _ _ JLO) as ndP__; nd_pre ndP__ 6%nat; intros kJ KAJ KBJ KEJ KCJ KDJ; nd_post).   (* [comment removed for export] *)
          all: eapply asec_chunk_frameD'; [exact MUn| exact Wc| | | | exists (Z.of_nat j); exact CHj].
          all: try (intros Ad kk Z1 Z2 Z3; apply Kobj; [clear -Z1 Z3 JLO JL1 KAJ KBJ KEJ KCJ KDJ; lia| clear -Z3 JCE; lia| clear -Z2; lia| clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_r; lia| clear -Z1 Z3 JC_n; lia| clear -Z1 Z3 JC_st; lia| clear -Z1 Z3 Dc; lia]).
          all: try (pose proof CHj as CH1; cbn [asec_chunk] in CH1; destruct CH1 as (Hh & _);
                    eapply cells_frame; [exact Hh| exact MUn| exact WM| cbn; apply Kobj; [clear -JLO JL1 JMSB KAJ KBJ KEJ KCJ KDJ; lia| clear -JCE JMSB; lia| clear; lia| clear -JC_t JMSB; lia| clear -JC_r JMSB; lia| clear -JC_n JMSB; lia| clear -JC_st JMSB; lia| clear -Dc JMSB; lia]]).
          -- intros Ad kk Z1 Z2 Z3. apply Kshad; [rewrite shad_div in Z1; unfold ASHOFF, AIMG_HI in *; clear -Z1 JLO JL1; Z.div_mod_to_equations; lia| rewrite shad_div in Z3; unfold ASHOFF in *; clear -Z3 JCE JAL8; Z.div_mod_to_equations; lia| clear -Z2; lia|].
             left. rewrite SHE. pose proof (shad_sep _ _ _ Dc JAL8) as HH. rewrite shlen_div in HH. clear -HH Z3. lia.
          -- intros Ad kk Z1 Z2 Z3. apply Kshad; [rewrite shad_div in Z1; unfold ASHOFF, AIMG_HI in *; clear -Z1 JLO JL1; Z.div_mod_to_equations; lia| rewrite shad_div in Z3; unfold ASHOFF in *; clear -Z3 JCE JAL8; Z.div_mod_to_equations; lia| clear -Z2; lia|].
             right. rewrite SHE. pose proof (shad_sep _ _ _ Dc MAL8) as HH. rewrite shlen_div in HH. clear -HH Z1 SHL. lia.
    - (* [comment removed for export] *) (nd_pre SINST 6%nat; intros I1 [srt I2] I3 I4 I5 I6; nd_post). unfold asec_inst. unfold AINSTANCE in *.
      split; [eapply cells_frame; [exact I1| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [exists srt; eapply cells_frame; [exact I2| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply junk_frame; [exact I3| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply junk_frame; [exact I4| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply cells_frame; [exact I5| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      eapply junk_frame; [exact I6| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia].
    - (* [comment removed for export] *) unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MUn| exact WM|]. intros POS.
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -RSP RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP2. unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *. Z.div_mod_to_equations. lia.
      + clear -POS; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) (al_space_beg L) ltac:(clear -RSP; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D SP2 RSP; unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia| clear -SP3; unfold K_ALIGN in SP3; Z.div_mod_to_equations; lia] | clear; lia].
    - (* [comment removed for export] *) intros x Hx HFh HC.
      assert (HC0 : Forall (fun c => ~ (sec_mb c <= x < sec_mb c + sec_ms c)) (sec_chunks_of st)).
      { rewrite Forall_forall in HC |- *. intros c Hin. apply HC. eapply Permutation_in; [apply Permutation_sym; exact PD| exact Hin]. }
      assert (INst : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
      pose proof (proj1 (Forall_forall _ _) HC0 ch INst) as NX. unfold ch in NX. cbn [sec_mb sec_ms] in NX.
      unfold K_HIGH_MEM, AIMG_HI, KLS in Hx.   (* [comment removed for export] *)
      assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM in *; unfold AIMG_HI, KLS in Hx; clear -Hx; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      rewrite <- (SHZ0 x ltac:(unfold K_HIGH_MEM; exact Hx) HFh HC0). apply MUn. rewrite wa_unsigned by exact SX.
      eapply (disjoint_outside _ (shad x) 1); [| clear; lia]. apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -Hx; Z.div_mod_to_equations; lia| rewrite shad_div; unfold ASHOFF; pose proof atop_range as AR8; clear -Hx AR8; Z.div_mod_to_equations; lia| clear; lia|].   (* [comment removed for export] *)
      rewrite SHE. destruct (Z_lt_le_dec x mb) as [LT|GE].
      + left. rewrite !shad_div. clear -LT MAL8. Z.div_mod_to_equations. lia.
      + right. rewrite !shad_div in *. clear -GE NX SHL MAL8 MSAL. Z.div_mod_to_equations. lia. }
  assert (BL' : ablocks L st' X' (lb_remove p LB)).
  { eapply (ablocks_free_sec L st X LB p mb ms n st' X' LIVE WF ELIVE); [| exact BL]. intros y Hy. subst X'. apply In_xfreeS. exact Hy. }
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi FKa [kF FBND]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (SHB : 2148239360 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SHE SHL; lia).   (* [comment removed for export] *)
  assert (HFK' : AFK L (lb_remove p LB) m').
  { eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
    - pose proof (ao_dtls L ALO) as DTO. (pose proof (aobj4_int _ DTO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DBND] [jD DIMG]; nd_post). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE, K_HIGH_MEM in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148239360 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
        rewrite SHE. destruct SC_f as [D|D].
        - right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH. clear -HH SHL. lia.
        - left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [exact D| clear -FKO FKi FBND; Z.div_mod_to_equations; lia] | clear; lia]. }
      (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      assert (LSTR : (lst = 0 /\ qsz lst = 8) \/ (al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104 /\ qsz lst = 8192))   (* [comment removed for export] *)
        by (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; split; [exact Z0| apply qsz_eq0; exact Z0]| right; split; [exact F3| split; [exact F4| apply qsz_pos; clear -F3 RES RHI; lia]]]).
      assert (EBR : al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104 /\ qsz eb = 8192) by (destruct EBF as [Z0|(_ & _ & F3 & F4)]; [exfalso; clear -Z0 EBNZ; lia| split; [assumption| split; [assumption| apply qsz_pos; clear -EBNZ; lia]]]).   (* [comment removed for export] *)
      assert (GLRR : gl = lst \/ gl = 0 \/ (al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104))
        by (destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])]; [left; exact Z2| right; left; exact Z2| right; right; split; assumption]).
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *; first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | match goal with |- ?G => idtac "FAKELEFT" G end ] ] |].
      apply Forall_nil.
    - intros cls FA sz. rewrite (In_lb_remove p LB). cbn. split; [intros [Hin _]; exact Hin| intros Hin; split; [exact Hin| discriminate]]. }
  assert (QH : qhdr L ch 0 = UB - 16) by (unfold ch; cbn [qhdr]; unfold PG; rewrite RZ, EUB; clear; lia).
  (* [comment removed for export] *)
  assert (GNB : g_nb g = Z.of_nat (length (a_qglob st))) by reflexivity.
  assert (GFST : g_fst g = qfirst L (q_glob Q)) by reflexivity.
  assert (GQB : g_qb g = a_qglob_bytes st) by reflexivity.
  assert (GFU : g_full g = match a_qglob st with [] => false | _ :: _ => true end) by reflexivity.
  destruct DKP as [MX' DKP'].
  (pose proof (qnum_free st p ch NUM ltac:(unfold ch; cbn [chunk_size]; clear -NB; lia) NOREC) as ndP__; nd_pre ndP__ 5%nat; intros NUM' NB2a NB2b NB2c NF2; nd_post).
  fold st1 st2 st' in NUM', NB2a, NB2b, NB2c, NF2.
  pose proof (st_after_q st2) as [DRN NDR]. fold st' in DRN, NDR.
  assert (QK' : aquar_glob_const m').
  { split; [| exact MX']. eapply cells_frame; [exact QK | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia. }
  assert (IA' : aintal true m').
  { split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. revert Hj. clear. unfold AIA_MAP1_LEN. intros Hj. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (BLST : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst ->
      abatch_addr L (qb_slot q) + 8192 <= lst \/ lst + 8192 <= abatch_addr L (qb_slot q) \/ lst = 0).
  { intros q Hq NE. destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [right; right; exact Z0|].
    destruct (BDIS q ql Hq ltac:(apply in_or_app; left; exact Hql)) as [E|E]; [exfalso; apply NE; rewrite Eql; exact E| rewrite Eql].
    destruct E as [E|E]; [left; exact E| right; left; exact E]. }
  assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst -> abatch_addr L (qb_slot q) <> gl ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (abatch_addr L (qb_slot q)) 8192).
  { intros q Hq NL NG. (nd_pre (BGEO q Hq) 4%nat; intros _ _ F3 F4; nd_post). pose proof (BLST q Hq NL) as DL.
    assert (DE : eb = lst \/ abatch_addr L (qb_slot q) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot q)).
    { destruct EBK as [E|[EA E]]; [left; exact E| right]. rewrite E.
      destruct (KDIS q Hq EA) as [D|D]; [right; exact D| left; exact D]. }
    assert (DG : gl = lst \/ gl = 0 \/ abatch_addr L (qb_slot q) + 8192 <= gl \/ gl + 8192 <= abatch_addr L (qb_slot q)).
    { destruct GLF as [[_ E]|(_ & _ & [Z0|((qg & Hqg & Eqg) & _)])]; [left; exact E| right; left; exact Z0| right; right].
      destruct (BDIS q qg Hq ltac:(apply in_or_app; right; exact Hqg)) as [E|E]; [exfalso; apply NG; rewrite Eqg; exact E| rewrite Eqg; exact E]. }
    apply Kres; clear -F3 F4 RES RHI DL DE DG; lia. }
  assert (HQ' : AQUAR L st' X' m').
  { subst ek. unfold ek_of in EKP, EK, QC', DKP', EEB, SB1, GDR, GL, GLST.
    destruct (enq_is_app st) eqn:EA; cbn [ek_nb ek_fst ek_lst ek_delta ek_b ek_post ek_pre] in EKP, EK, QC', DKP', EEB, SB1, GDR, GL, GLST.
    - (* [comment removed for export] *)
      (nd_pre EKP 4%nat; intros LB' LA' [bs LJ'] _; nd_post). (nd_pre EK 9%nat; intros _ _ CNT' _ _ _ _ LEN _; nd_post).
      (* [comment removed for export] *)
      pose proof EA as EA0. unfold enq_is_app in EA0. destruct (rev (a_qloc st)) as [|blr rl] eqn:RV; [discriminate|].
      assert (QL : a_qloc st = rev rl ++ [blr]) by (rewrite <- (rev_involutive (a_qloc st)), RV; reflexivity).
      destruct (Z.eqb_spec (b_count blr) Q_BATCH) as [|NFULL]; [discriminate|]. clear EA0.
      set (l := rev rl) in *. set (bl := blr) in *.
      assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL, length_app; cbn; clear; lia).
      assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; clear -LQ; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
      set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
      assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
      assert (LST : List.last (a_qloc st) dummy_batch = bl) by (rewrite QL; apply last_app1). rewrite LST in *.
      assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
      set (bl' := mkABatch (b_count bl + 1) (b_size bl + n) (ch :: b_chunks bl)) in *.
      set (qz' := mkQB (qb_slot qz) (0 :: qb_ks qz)) in *.
      assert (EAPP : enq_app st1 ch = Some (set_qloc (l ++ [bl']) (a_qloc_bytes st1 + n) st1)).
      { unfold enq_app. change (a_qloc st1) with (a_qloc st). rewrite RV. fold bl. replace (b_count bl =? Q_BATCH) with false by (symmetry; apply Z.eqb_neq; exact NFULL).
        subst bl'. reflexivity. }
      assert (Q2 : a_qloc st2 = l ++ [bl'] /\ a_qloc_bytes st2 = a_qloc_bytes st + n /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. subst st1. cbn. repeat split; reflexivity. }
      (nd_pre Q2 4%nat; intros QL2 QB2 QG2 QGB2; nd_post).
      (* [comment removed for export] *)
      unfold abatches in ABL, ABG. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
      cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
      assert (ABl' : abatches_to L m' l ql (hd 0 (qaddrs L [qz']))).
      { cbn [qaddrs map hd qz' qb_slot]. cbn [qaddrs map hd] in ABl. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
        intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
        assert (NEq : abatch_addr L (qb_slot q) <> lst).
        { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post).
          apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
          unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
        apply BFR; [exact INq | exact NEq |].
        destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post); clear -F3 RES RHI; lia|].
        rewrite Eqg. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post). apply in_split in Hqg. (nd_pre Hqg 3%nat; intros gs1 gs2 EQg; nd_post).
        apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
        pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
        unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      assert (ABz' : abatch_cells L m' bl' qz' 0).
      { unfold abatch_cells. cbv zeta. cbn [qb_slot qb_ks b_size b_count b_chunks bl' qz']. rewrite <- QLST. rewrite qhdrs_cons, map_app. cbn [map qhdr]. rewrite QH.
        split; [exact LB'|]. split; [exact LA'|]. split; [| split; [cbn [length]; rewrite Z4; clear; lia| split; [cbn [length]; rewrite Z5; reflexivity| unfold Q_BATCH in *; clear -CNT' Z6; lia]]].
        exists bs. unfold Q_BATCH_BYTES. exact LJ'. }
      assert (ABL' : abatches_to L m' (l ++ [bl']) (ql ++ [qz']) 0).
      { apply abatches_to_app; [exact LNl|]. split; [exact ABl'|]. cbn. split; [exact ABz'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (ql ++ [qz']) (q_glob Q) true (q_pend Q))).
      { subst X'. unfold xfreeS. apply (qcoupled_app_sec L st X Q mb ms n CP st2 l bl ql qz true 0 QL QQ QL2 QG2). }
      subst qz'.
      destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [DR|NDRN].
      + (* [comment removed for export] *)
        (nd_pre (DRN DR) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        destruct DKP' as [GC' GLN].
        exists (mkQConc [] (q_glob Q ++ (ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}])) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length].
             replace (Z.of_nat (length l + 1)) with (Z.of_nat (length (a_qloc st))) by (rewrite QL, length_app; cbn; reflexivity).
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite qlast_reslot, <- QQ, <- ELST.
             assert (FE : qfirst L (q_glob Q ++ ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}]) = (if g_full g then g_fst g else qfirst L (q_loc Q))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). cbn [app]. rewrite qfirst_reslot, <- QQ. reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite qfirst_reslot, <- QQ.
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; clear -LQg; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
                   set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
                   set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
                   assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
                   rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
                   cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
                   assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
                   rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
                   rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
                   +++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
                       intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQg; apply in_or_app; left; exact Hq).
                       assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
                       { intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                         apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       apply BFR; [exact INq | | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
                       rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                       apply (bslots_nodup_split L st X Q CP ql qz gs1 q (gs2 ++ [qgz])); [rewrite QQ, QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                       pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
                       unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
                   +++ cbn [abatches_to]. split; [| exact I].
                       (* [comment removed for export] *)
                       unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q)) (qaddrs L [])) with (qfirst L (q_loc Q)).
                       assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
                       assert (NGL : abatch_addr L (qb_slot qgz) <> lst).
                       { rewrite QLST. intros E. apply (bslots_nodup_split L st X Q CP ql qz qg qgz []); [rewrite QQ, QQg; rewrite <- ?app_assoc; cbn [app]; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
                         pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity).
                       (nd_pre (BGEO qgz INgz) 4%nat; intros _ _ F3 F4; nd_post). pose proof (BLST qgz INgz NGL) as DL.
                       assert (DE : eb = lst \/ abatch_addr L (qb_slot qgz) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot qgz)).
                       { destruct EBK as [E|[EA' E]]; [left; exact E| discriminate]. }
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI DL DE GLS HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_drain L st2 st' X' (mkQConc (ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}]) (q_glob Q) true (q_pend Q)) true CP2 QL3 QG3).
        * exact NUM'.
      + (* [comment removed for export] *)
        pose proof (NDR NDRN) as EST. 
        assert (GD : g_drain g = false) by (rewrite GDR; apply Z.ltb_ge; rewrite <- QB2; exact NDRN).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        exists (mkQConc (ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}]) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite EST, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [| exact ABL'].
          rewrite length_app, qfirst_reslot, qlast_reslot, <- QQ, <- ELST. cbn [length].
          replace (Z.of_nat (length l + 1)) with (Z.of_nat (length (a_qloc st))) by (rewrite QL, length_app; cbn; reflexivity). exact QC'.
        * split; [rewrite <- GNB, <- GFST, <- GL, <- GQB; exact DKP'|].
          unfold abatches. eapply abatches_to_frame; [exact MUn | exact WM | exact ABG |].
          intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
          assert (NEq : abatch_addr L (qb_slot q) <> lst).
          { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
            apply (bslots_nodup_split L st X Q CP ql qz gs1 q gs2); [rewrite QQ, EQg; rewrite <- ?app_assoc; cbn [app]; reflexivity|].
            pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
            unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
          apply BFR; [exact INq | exact NEq | rewrite EGL; unfold dk_glst; rewrite GD; exact NEq].
        * first [rewrite EST | idtac]. exact CP2.
        * first [rewrite <- EST | idtac]. exact NUM'.
    - (* [comment removed for export] *)
      (nd_pre (NEWF eq_refl) 8%nat; intros NK24 NB24 KK24 NIB JK24 FK CIN POS; nd_post).
      (nd_pre EKP 6%nat; intros C24' [stj' SJ'] NBc NAc [bs NJc] OLDc; nd_post).
      assert (EAPP : enq_app st1 ch = None).
      { destruct (enq_app st1 ch) as [sx|] eqn:EAPP; [exfalso| reflexivity].
        assert (EA1 : enq_is_app st1 = true) by (apply (proj2 (enq_is_app_spec st1 ch)); eexists; exact EAPP).
        change (enq_is_app st1) with (enq_is_app st) in EA1. congruence. }
      set (nbt := mkABatch 1 (n + 8192) [ch]) in *.
      set (qn := mkQB k24 [0]) in *.
      assert (Q2 : a_qloc st2 = a_qloc st ++ [nbt] /\ a_qloc_bytes st2 = a_qloc_bytes st + (n + 8192) /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. (pose proof (enq_new_core ch st1) as ndP__; nd_pre ndP__ 7%nat; intros _ E1 E2 _ E3 E4 _; nd_post).
        rewrite E1, E2, E3, E4. subst st1 nbt. unfold ch. cbn [a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_live chunk_size]. fold ch. unfold Q_BATCH_BYTES.
        split; [reflexivity|]. split; [clear; lia|]. split; reflexivity. }
      (nd_pre Q2 4%nat; intros QL2 QB2 QG2 QGB2; nd_post).
      assert (FSTE : (if match a_qloc st with [] => false | _ :: _ => true end then qfirst L (q_loc Q) else abatch_addr L k24) = qfirst L (q_loc Q ++ [qn])).
      { rewrite qfirst_app_r. subst qn; cbn [qb_slot]. generalize LN1. clear. generalize (a_qloc st) (q_loc Q).
        intros [|x1 r1] [|x2 r2] LL; cbn in LL; first [reflexivity | discriminate]. }
      rewrite FSTE in QC'. rewrite FSTE in DKP'.
      assert (QLST' : qlast L (q_loc Q ++ [qn]) = abatch_addr L k24) by (subst qn; apply qlast_app1).
      (* [comment removed for export] *)
      assert (GNL : forall q, In q (q_glob Q) -> abatch_addr L (qb_slot q) <> lst).
      { intros q Hq E. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
        destruct LSTF as [Z0|((q' & Hq' & Eq') & _)].
        - (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post). clear -F3 RES RHI E Z0. lia.
        - apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post). apply in_split in Hq'. (nd_pre Hq' 3%nat; intros qs1 qs2 EQl; nd_post).
          apply (bslots_nodup_split L st X Q CP qs1 q' (qs2 ++ gs1) q gs2); [rewrite EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP q' ltac:(apply in_or_app; left; rewrite EQl; apply in_or_app; right; left; reflexivity)).
          rewrite Eq' in E. unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      (* [comment removed for export] *)
      assert (ABO' : abatches_to L m' (a_qloc st) (q_loc Q) (abatch_addr L k24)).
      { destruct (a_qloc st) as [|b0 l0] eqn:QL0.
        - replace (q_loc Q) with (@nil qbatchc) by (clear -LN1; destruct (q_loc Q); [reflexivity| cbn in LN1; discriminate]). exact I.
        - cbv iota beta in OLDc. destruct OLDc as [OLD1 OLD2]. rewrite <- QL0 in *.
          assert (LNE : a_qloc st <> []) by (rewrite QL0; discriminate).
          assert (QL : a_qloc st = removelast (a_qloc st) ++ [List.last (a_qloc st) dummy_batch]) by (apply app_removelast_last; exact LNE).
          assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL0; cbn; clear; lia).
          assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; clear -LQ; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
          set (l := removelast (a_qloc st)) in *. set (bl := List.last (a_qloc st) dummy_batch) in *.
          set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
          assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
          assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
          assert (FULL : b_count bl = Q_BATCH).
          { pose proof EA as EA0. unfold enq_is_app in EA0. rewrite QL, rev_unit in EA0. cbv iota beta in EA0.
            revert EA0. destruct (Z.eqb_spec (b_count bl) Q_BATCH) as [E|NE]; intros EA0; [exact E| discriminate]. }
          unfold abatches in ABL. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
          cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
          rewrite QL, QQ. apply abatches_to_app; [exact LNl|]. split.
          + cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
            intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
            assert (NEq : abatch_addr L (qb_slot q) <> lst).
            { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post).
              apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
              pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
              unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
            apply BFR; [exact INq | exact NEq |].
            destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post); clear -F3 RES RHI; lia|].
            rewrite Eqg. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post). apply in_split in Hqg. (nd_pre Hqg 3%nat; intros gs1 gs2 EQg; nd_post).
            apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
            pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
            unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
          + cbn [abatches_to]. split; [| exact I].
            unfold abatch_cells. cbv zeta. change (hd (abatch_addr L k24) (qaddrs L [])) with (abatch_addr L k24). rewrite <- QLST.
            split; [rewrite FULL; exact OLD1|]. split; [exact OLD2|]. split; [| split; [exact Z4| split; [exact Z5| exact Z6]]].
            rewrite FULL. replace (Q_BATCH_BYTES - 24 - 8 * Q_BATCH) with 0 by reflexivity. unfold Q_BATCH. apply junk_nil; (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [clear -Z0; lia | atop_facts; clear -F3 F4 RES RHI; lia]). }
      (* [comment removed for export] *)
      assert (ABN' : abatch_cells L m' nbt qn 0).
      { unfold abatch_cells. cbv zeta. subst nbt qn. cbn [qb_slot qb_ks b_size b_count b_chunks]. rewrite qhdrs_cons. cbn [qhdrs app map qhdr]. rewrite QH.
        split; [exact NBc|]. split; [exact NAc|]. split; [exists bs; unfold Q_BATCH_BYTES; exact NJc|]. split; [reflexivity|]. split; [reflexivity| unfold Q_BATCH; clear; lia]. }
      assert (ABL' : abatches_to L m' (a_qloc st ++ [nbt]) (q_loc Q ++ [qn]) 0).
      { apply abatches_to_app; [exact LN1|]. split; [cbn [qaddrs map hd]; subst qn; cbn [qb_slot]; exact ABO'|]. cbn [abatches_to]. split; [exact ABN'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q))).
      { subst X' qn nbt. rewrite ?EA. unfold xfreeS. cbv iota beta.
        apply (qcoupled_new_sec L st X Q mb ms n WF CP st2 k24 (c_count (get_cls st K_BATCH_CLASS)) (n + 8192) true 0 eq_refl POS NK24 QL2 QG2). }
      destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [DR|NDRN].
      + (* [comment removed for export] *)
        (nd_pre (DRN DR) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        destruct DKP' as [GC' GLN].
        exists (mkQConc [] (q_glob Q ++ (q_loc Q ++ [qn])) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite QLST'.
             assert (FE : qfirst L (q_glob Q ++ q_loc Q ++ [qn]) = (if g_full g then g_fst g else qfirst L (q_loc Q ++ [qn]))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate).
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; clear -LQg; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
                   set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
                   set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
                   assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
                   rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
                   cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
                   assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
                   rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
                   rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
                   +++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
                       intros q Hq. assert (INg : In q (q_glob Q)) by (rewrite QQg; apply in_or_app; left; exact Hq).
                       assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INg).
                       assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
                       { intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                         apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       apply BFR; [exact INq | exact (GNL q INg) | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
                   +++ cbn [abatches_to]. split; [| exact I].
                       (* [comment removed for export] *)
                       unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q ++ [qn])) (qaddrs L [])) with (qfirst L (q_loc Q ++ [qn])).
                       assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
                       assert (INgzg : In qgz (q_glob Q)) by (rewrite QQg; apply in_or_app; right; left; reflexivity).
                       assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INgzg).
                       pose proof (GNL qgz INgzg) as NGL.
                       (nd_pre (BGEO qgz INgz) 4%nat; intros _ _ F3 F4; nd_post). pose proof (BLST qgz INgz NGL) as DL.
                       pose proof (KDIS qgz INgz eq_refl) as DE.
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI DL DE EEB GLS HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_drain L st2 st' X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q)) true CP2 QL3 QG3).
        * exact NUM'.
      + (* [comment removed for export] *)
        pose proof (NDR NDRN) as EST.
        assert (GD : g_drain g = false) by (rewrite GDR; apply Z.ltb_ge; rewrite <- QB2; exact NDRN).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        exists (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite EST, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [| exact ABL'].
          rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1. rewrite QLST'. exact QC'.
        * split; [rewrite <- GNB, <- GFST, <- GL, <- GQB; exact DKP'|].
          unfold abatches. eapply abatches_to_frame; [exact MUn | exact WM | exact ABG |].
          intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
          apply BFR; [exact INq | exact (GNL q Hq) | rewrite EGL; unfold dk_glst; rewrite GD; exact (GNL q Hq)].
        * first [rewrite EST | idtac]. exact CP2.
        * first [rewrite <- EST | idtac]. exact NUM'. }
  (* [comment removed for export] *)
  assert (HBK : forall blk, In blk (lb_remove p LB) -> disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (ab_addr blk) (ab_size blk)).
  { intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size]; apply (proj1 (In_lb_remove p LB _)) in Hin; destruct Hin as [Hin NEp]; cbn [ab_kind] in NEp.
    - destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb' & msz' & Lp & EUA & Gs)].
      + destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        pose proof (busy_of_In_nodup L st X b WF Hb) as BOF.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
        (pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (DQ : forall q', In q' (q_loc Q ++ q_glob Q) ->
            aslot_addr L cb kb + size_of_class cb <= abatch_addr L (qb_slot q') \/ abatch_addr L (qb_slot q') + 8192 <= aslot_addr L cb kb).
        { intros q' Hq'. (nd_pre (bslot_busy L st X Q CP q' Hq') 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> qb_slot q').
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2.
            pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq, <- E1, <- E2, BOF in BY. injection BY as EE. subst yq. rewrite Sb in Syq. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS (qb_slot q') ALO WF HCb (K24) HKb (bslot_range L st X Q WF CP q' Hq') NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DK24 : enq_is_app st = false -> aslot_addr L cb kb + size_of_class cb <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= aslot_addr L cb kb).
        { intros EAx. (nd_pre (NEWF EAx) 4%nat; intros _ NBk KK _; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> k24).
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2. rewrite <- E1, <- E2, BOF in NBk. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS k24 ALO WF HCb (K24) HKb KK NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DL : lst = 0 \/ aslot_addr L cb kb + size_of_class cb <= lst \/ lst + 8192 <= aslot_addr L cb kb).
        { destruct LSTF as [Z0|((q' & Hq' & Eq') & _)]; [left; exact Z0| right]. rewrite Eq'. apply DQ. apply in_or_app; left; exact Hq'. }
        assert (DE : eb = lst \/ aslot_addr L cb kb + size_of_class cb <= eb \/ eb + 8192 <= aslot_addr L cb kb).
        { destruct EBK as [E|[EAx E]]; [left; exact E| right]. rewrite E. exact (DK24 EAx). }
        assert (DG : gl = lst \/ gl = 0 \/ aslot_addr L cb kb + size_of_class cb <= gl \/ gl + 8192 <= aslot_addr L cb kb).
        { destruct GLF as [[_ E]|(_ & _ & [Z0|((q' & Hq' & Eq') & _)])]; [left; exact E| right; left; exact Z0| right; right].
          rewrite Eq'. apply DQ. apply in_or_app; right; exact Hq'. }
        apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia
                    | clear -DL FIT P5 RSP RES RHI; lia | clear -DE DL FIT P5 RSP RES RHI; lia | clear -DG DL FIT P5 RSP RES RHI; lia].
      + (* [comment removed for export] *)
        assert (NEq : q <> p) by (intros ->; apply NEp; reflexivity).
        assert (NEc : CSec mb' msz' n' <> ch).
        { intros E. apply NOTL. exists q. rewrite ELIVE, lookup_delete_ne by (intros E'; exact (NEq (eq_sym E'))). rewrite <- E. exact Lp. }
        assert (INc : In (CSec mb' msz' n') (sec_chunks_of st)) by (eapply live_sec_in; exact Lp).
        assert (INs : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
        destruct WD as [_ DJ]. destruct (DJ _ _ INc INs NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
        all: cbn [sec_wf1] in Gs; (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        all: pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF; subst A'; unfold SEC_UOFF, K_HIGH_MEM in *.
        all: unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        all: apply Kobj; [clear -Gs2 Gs4 Gs5 SF; lia| clear -Gs3 Gs4 Gs5 SF; lia| clear -Gs5; lia| clear -Gs4 Gs5 SF Ct; lia| clear -Gs4 Gs5 SF Cr; lia| clear -Gs4 Gs5 SF Cn; lia| clear -Gs4 Gs5 SF Cs; lia| clear -Gs4 Gs5 SF Dc; lia].
    - (nd_pre (FKD cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post). unfold K_HIGH_MEM in *.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia | clear -K1 K3 SC_f; lia]. }
  (* [comment removed for export] *)
  assert (TLSK : forall TA tk, ATPv + -200 <= TA -> TA + tk <= ATPv + 312 -> 0 <= tk ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) TA tk).
  { intros TA tk TH1 TH2 TH3. pose proof ATPv_img as TI. apply Kimg; clear -TH1 TH2 TH3 TI; unfold AIMG_HI; lia. }
  assert (TLSS : forall a', ATPv + -200 <= a' < ATPv + 312 ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros a' Ha'. pose proof ATPv_img as TI. apply Klow; clear -Ha' TI; try (rewrite shad_div; unfold ASHOFF); try Z.div_mod_to_equations; lia. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) (lb_remove p LB) -> forall a', FA <= a' < FA + sz ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros cls FA sz Hin a' Ha'. apply (proj1 (In_lb_remove p LB _)) in Hin. destruct Hin as [Hin _].
    (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). unfold K_HIGH_MEM in *.
    assert (FAL8 : al_fake L mod 8 = 0) by (destruct FKO as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
    apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
    rewrite SHE. destruct SC_f as [D|D].
    - right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
      pose proof (shad_mono (al_fake L) a' ltac:(clear -K1 Ha'; lia)) as MM. clear -HH MM SHL. lia.
    - left. pose proof (shad_sep _ _ _ D FAL8) as HH. rewrite (shad_div a'), (shad_div (al_fake L)), shlen_div in *.
      clear -HH Ha' K3 FAL8. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  split; [apply fp_le_refl|].
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split.
  { eapply (aheap_pres_freeS CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact TLSK | exact TLSS | apply Klow; unfold AIMSH_LO, AIMSH_LEN; clear; lia
      | rewrite <- (ao_ahm_eq L ALO); unfold AAHM_SZ; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI;
      pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; pose proof (ad_ahm_nodes L ALO) as DA3; pose proof (ad_ahm_store L ALO) as DA4;
      (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ SC_ahm; nd_post);
      unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OAH, OAHI, DA1, DA2, DA3, DA4; apply Kobj; clear -OAH OAHI DA1 DA2 DA3 DA4 SC_ahm; lia]. }
  split; [exact ALO|].
  split. { (pose proof ARNG as ndP__; nd_pre ndP__ 14%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 RCl RPA RSC RPSH RTLS; nd_post).
           unfold arng. repeat (split; [assumption|]). split; [| split; [rewrite ENRES; exact RPA| split; [eapply RSEC_perm; [apply Permutation_sym; exact PD| exact RSC]| split; [exact RPSH | exact RTLS]]]].
           intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24a, M24d; exact (RCl K_BATCH_CLASS Hc')| rewrite (GCo' c' NE); exact (RCl c' Hc')]. }
  split; [| exact HFK'].
  exists X'. split; [| exact BL'].
  split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
  split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3'].
Qed.
End Zd1.
#[using="HL CI_OK"] Theorem store_freeS : ltac:(let t := eval cbv delta [store_freeS__stmt] in store_freeS__stmt in exact t).
Proof. exact store_freeS__body. Qed.

(* [comment removed for export] *)
Definition afree_sec_fastP := afree_sec_fast DI AFK CI store_freeS.
End S.
End CANSEC1.
End TwB.
End ASF_store.

(* [comment removed for export] *)
Module ASF_mid.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead F_afree_tail. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_read. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_icptR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.AFreeStoreK OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_store OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : ABase.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6303744 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6303744 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.

Definition mid_kitS__stmt : Prop := mid_stmtS DI AFK CI.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 1).
Variable full : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 2).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 3).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 4).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 5).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 6).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 7).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 8).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 9).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 10).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 11).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 12).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 13).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 14).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 15).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 16).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 17).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 18).
Variable F : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 19).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 20).
Variable m : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 21).
Variable st : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 22).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 23).
Variable X : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 24).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 25).
Variable p : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 26).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 27).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 28).
Variable n : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 29).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 30).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 31).
Variable A : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 32).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 33).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 34).
Variable nx : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 35).
Variable bsz : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 36).
Variable hs : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 37).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 38).
Let ch := CSec mb ms n.
Let st1 := set_live (delete p (a_live st)) st.
Let QM := mkQConc (q_loc Q) (q_glob Q) true (q_pend Q).
Let UB := mb + 6144.
Let gq := shlen (rup n 8).
#[using="HL CI_OK ch st1 QM UB gq"] Lemma mid_kitS__body : ltac:(let T := type of (fun (h : mid_kitS__stmt) => h L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p mb ms n b1 ctx A lo lst nx bsz hs tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (full, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (F, (fc, (m, (st, (LB, (X, (Q, (p, (mb, (ms, (n, (b1, (ctx, (A, (lo, (lst, (nx, (bsz, (hs, tr))))))))))))))))))))))))))))))))))))))) as _.
  unfold mid_stmtS. 
  cbv zeta. intros ALO ARNG AR AQ BL HFK LIVE HIN NQM HDR B1 B13 CTX CEIL LO ms1 PM. unfold AFREE_STACK in LO.
  chg (CSec mb ms n) ch.
  chg (set_live (delete p (a_live st)) st) st1.
  chg (mkQConc (q_loc Q) (q_glob Q) true (q_pend Q)) QM.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS0 UNW; nd_post).
  (nd_pre (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) 3%nat; intros EAu _ WFch; nd_post).
  (nd_pre (sec_wf1_facts' L mb ms n WFch) 13%nat; intros MAL MLO MCE MSE NB RZ MSB MSAL NMS NS0 SCL NPR N6; nd_post).
  (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post). unfold AIMG_HI in ML1. (pose proof (ablk_int _ _ MLO) as ndP__; nd_pre ndP__ 6%nat; intros kM KAM KBM KEM KCM KDM; nd_post).   (* [comment removed for export] *)
  (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros SC_t SC_c SC_r SC_p SC_n SC_st SC_f SC_d SC_tls SC_ahm0; nd_post).
  pose proof HS as HS0. (nd_pre HS0 5%nat; intros WFS _ SINST PZ SHZ; nd_post).
  (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros _ WP WR WL WB WF1 WD; nd_post).
  (nd_pre (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE) 25%nat; intros order i b1r cxr uw PO NTH IL LENO WF1o WDo U64 JK PER CH H1 H5 _ _ _ HUW UJ S1 S2 S3; nd_post).
  cbv zeta in H5, HUW, UJ, S2, S3.
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  (pose proof (aobj4_int _ OT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ OC ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci _ [kC CBND]; nd_post). (pose proof (aobj_int _ _ ON ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni _ [kN NBND]; nd_post).
  (pose proof (aobj_int _ _ OS ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si _ [kS SBND]; nd_post). pose proof (ao_res_hi L ALO) as RHI.
  unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
  box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
  word_range sp SPR.
  chg (mb + 6144) UB.
  assert (EUB : UB = mb + 6144) by reflexivity.
  assert (EHM : mb + 6128 = UB - 16) by (subst UB; clear; lia).
  assert (UB16' : UB mod 8 = 0) by (subst UB; clear -MAL; Z.div_mod_to_equations; lia).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  rewrite EHM in PM, HDR.
  (pose proof (rup8_facts n ltac:(clear -NB; lia)) as ndP__; nd_pre ndP__ 3%nat; intros RUP RUP8 RUPS; nd_post).
  assert (SHGEO : shad UB = shad mb + 768 /\ shlen (rup n 8) <= ms / 8 - 768 /\ 0 < shlen (rup n 8) /\ UB + rup n 8 <= mb + ms
                  /\ 2148238848 <= shad mb /\ shad mb + ms / 8 <= 17594332446720).   (* [comment removed for export] *)
  { subst UB. rewrite !shad_div, RUPS. unfold ASHOFF. (pose proof (sec_facts n ltac:(clear -NB; lia) NPR) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ RS1 _ NSE _; nd_post).
    unfold K_HIGH_MEM in *. pose proof atop_range as AR8. clear -MAL RUP RUP8 RS1 NSE NMS N6 NB ML1 ML3 MCE MSAL AR8. Z.div_mod_to_equations. lia. }
  (nd_pre SHGEO 6%nat; intros SHE SHL SHP UBS SHLO SHHI; nd_post).
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof NUM as NUM0. (nd_pre NUM0 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof CP as CP0. (nd_pre CP0 7%nat; intros LN1 LN2 _ _ ND2 BSI _; nd_post).
  (* [comment removed for export] *)
  unfold free_to_refill_post in PM.
  (nd_pre PM 18%nat; intros id t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' m' sj' tb' junk2 j0 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 22%nat; intros MU WM MI' ST' IDR HDR' FC' SH' STATS' LSJ' UW' FL' IAS' IAM' SS' TB' LTB' FRS' FRP' FRE' LBS' DEP'; nd_post).
  cbn [ms_mem MS].
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  chg (shlen (rup n 8)) gq. assert (EGQ : gq = shlen (rup n 8)) by reflexivity. clearbody gq.
  (* [comment removed for export] *)
  assert (MUn : munch (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) 0 0 0) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  assert (KF : kfactsS (bv_unsigned sp) (al_t L) mb ms UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo 0 0 0).
  { unfold kfactsS. unfold K_HIGH_MEM in *.
    assert (GQ1 : 1 <= gq) by (clear -SHP EGQ; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP MLO ML1 ML3 MCE EUB UBS NB RUP SC_t SC_r SC_n SC_st SHE SHL SHLO SHHI GQ1 EGQ. clear. intros.
    rewrite ?EGQ in SHL. unfold iclr, AIMG_LO, AIMG_HI in *. rewrite ?qsz_0.   (* [comment removed for export] *)
    sg_destr; repeat split; first [assumption | lia]. }
  pose proof (KS_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KS_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KS_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KS_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KS_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s) SC_c) as Kctx.
  pose proof (KS_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
  pose proof (KS_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
  pose proof (KS_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KS_objL _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as KobjL.      (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
  unfold adisj in D_l_t, D_l_r, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
  pose proof (KS_chunk _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kchunk.
  (* [comment removed for export] *)
  lazymatch type of MU with munch ?W0 _ _ =>
    assert (KtO : forall Ad kk, al_t L + 80 <= Ad -> Ad + kk <= al_t L + 2800 -> 0 <= kk -> disjoint_from W0 Ad kk);
    [ intros Ad kk Y1 Y2 Y3; pose proof DL7 as X7; unbox X7; pose proof DL8 as X8; unbox X8;
      cbn [disjoint_from]; unfold K_HIGH_MEM in *; clear -Y1 Y2 Y3 TL1 TL2 TBND TIMG LO CEIL X7 X8 SC_t MSB EUB UBS NB RUP SHLO SHHI SHE SHL; repeat (split; [lia|]); exact I |];   (* [comment removed for export] *)
    assert (KgO : forall Ad kk, 0xab270 <= Ad -> Ad + kk <= 0xab330 -> 0 <= kk -> disjoint_from W0 Ad kk);
    [ intros Ad kk Y1 Y2 Y3; cbn [disjoint_from]; unfold K_HIGH_MEM in *; clear -Y1 Y2 Y3 TL1 TBND TIMG LO CEIL MLO ML1 ML3 KAM KBM KEM KCM KDM EUB DL1 DL4 Ni Si NBND SBND SHLO SHE; repeat (split; [lia|]); exact I |]   (* [comment removed for export] *)
  end.
  (* [comment removed for export] *)
  assert (ELIVE : a_live st1 = delete p (a_live st)) by reflexivity.
  assert (NDS : forall c', ndist st1 c' = ndist st c') by (intros c'; reflexivity).
  assert (WF' : awf L st1 X) by (apply (awf_delete_sec L st X p mb ms n st1 WF LIVE); reflexivity).
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    (first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |])] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]). apply Forall_nil. }
  assert (INST' : ainstance L st1 m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
  assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
  assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
  (* [comment removed for export] *)
  assert (THR' : athread L st1 X m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - intros c' Hc'. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c' Hc') | reflexivity | reflexivity | reflexivity |].
      unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply KtO; clear -Hc'; lia.
    - eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply KtO; clear; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  (* [comment removed for export] *)
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L st1 m' c'' /\ afreearray L st1 X m' c'' /\ aslots L st1 X m' c'' /\ aslot_shadow L st1 X m' c'').
  { intros c'' Hc''. (nd_pre (CLS c'' Hc'') 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (aregion_mod L c'' SAL) as RM''.
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 4%nat; intros RI1 RI2 RI3 RI4; nd_post).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      apply Kres; try (clear -Hc'' RSP; lia); right; clear -Hc'' RSP RES RHI; lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia | | |]; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, AIMG_HI, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
          rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) (afreearr L c'') ltac:(clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D RI2 RI3 FA2; lia| exact AM] | clear; lia].
    - (* [comment removed for export] *)
      eapply (aslots_update_gen L _ m m' MUn WM st st1 X X c''); [exact SLOTS | apply NDS | reflexivity | reflexivity | |].
      + intros k'' Hk''. left.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        split; [reflexivity|]. split.
        * apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia | | |]; right; clear -P5 RSP RES RHI; lia.
        * intros b Hb. (nd_pre (busy_of_Some_facts X c'' k'' b Hb) 3%nat; intros IB CB' KB'; nd_post). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia | | |]; right; clear -RI4 Q1 U0 RES RHI; lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update_gen L _ m m' MUn WM st st1 X X c''); [exact SHADOW | apply NDS | reflexivity | reflexivity | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk''. left.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        split; [reflexivity|].
        pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -T16; lia.
        * rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) (aslot_addr L c'' k'') ltac:(clear -P5 RSP; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D P6 RI3; unfold K_SPACE_SIZE in *; lia| clear -AL''; Z.div_mod_to_equations; lia] | clear; lia].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) AU ltac:(clear -U0 RI4; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D U0' RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia].
  }
  (* [comment removed for export] *)
  assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st1 m' c'').
  { intros c'' Hc''. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). pose proof (aregion_mod L c'' SAL) as RM''.
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post).
    eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | reflexivity | reflexivity | |].
    - intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
      assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
      destruct U0 as [U0 U0'].
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) AU ltac:(clear -U0 RI1; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D U0' RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) AU ltac:(clear -FA1 RI1; unfold K_FREEARR_OFF in *; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D FA2 RI2 RI3; unfold K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia]. }
  (* [comment removed for export] *)
  assert (NOTL : ~ sec_live st1 ch) by (apply (sec_not_live_after L st _ p mb ms n st1 WFS (Permutation_refl _) LIVE ELIVE)).
  assert (LVE : forall j c, nth_error order j = Some c -> j <> i -> (sec_live st1 c <-> sec_live st c)).
  { intros j c Hj NEj. apply (sec_live_other st p mb ms n st1 c LIVE ELIVE).
    intros E. apply NEj. destruct WDo as [ND _].
    apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH. unfold ch. rewrite E. reflexivity. }
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p.
  pose proof (ao_ptr L ALO) as OP. (pose proof (aobj_int _ _ OP ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OPi OPa [kP OPs]; nd_post). unfold adisj, aobj in D_t_p, D_p_r, D_n_p, D_s_p, OP.   (* [comment removed for export] *)
  assert (HS' : ASECc (sec_chunks_of st) L st1 X m').
  { unfold ASECc.
    pose proof HS as HS1. (nd_pre HS1 5%nat; intros _ _ _ _ SHZ0; nd_post).
    split; [| split; [| split; [| split]]].
    - (* [comment removed for export] *) exact WFS.
    - (* [comment removed for export] *) exists order. change (a_nres st1) with (a_nres st). change (a_nsec st1) with (a_nsec st).
      split; [exact PO|].
      unfold K_HIGH_MEM in *.
      split; [| split].
      + eapply u64arr_frame; [exact U64| exact MUn| exact WM|]. rewrite length_map, LENO.
        apply Kobj; [clear -OP OPi OPs WB WR LENO; lia| clear -OP OPi OPs WB WR; lia| clear -WB; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
      + eapply junk_frame; [exact JK| exact MUn| exact WM|]. intros POS.
        apply Kobj; [clear -OP OPi OPs WB WR POS; lia| clear -OP OPi OPs WB WR; lia| clear -WB POS; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
      + intros j c Hj. destruct (Nat.eq_dec j i) as [->|NEji].
        * (* [comment removed for export] *)
          rewrite NTH in Hj. injection Hj as <-. exists false. split; [split; [discriminate| intros Hl; exfalso; exact (NOTL Hl)]|].
          unfold ch. cbn [asec_chunk]. pose proof CH as CH0. cbn [asec_chunk] in CH0.
          (nd_pre CH0 9%nat; intros G1 G2 G3 G4 _ _ _ _ _; nd_post). unfold SEC_UOFF in *. rewrite <- ?EUB in *.
          replace (UB - 16 + 16) with UB in FC' by (clear; lia).
          split; [eapply cells_frame; [exact G1| exact MUn| exact WM| cbn; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply junk_frame; [exact G2| exact MUn| exact WM| intros _; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply cells_frame; [exact G3| exact MUn| exact WM| cbn; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply junk_frame; [exact G4| exact MUn| exact WM| intros _; apply Kchunk; clear -EUB MSB; lia]|].
          split; [exists b1, ctx; split; [exact HDR'| split; [exact B1| split; [exact B13| exact CTX]]]|].
          split. { replace (ms - 6144) with (8 + (ms - 6144 - 8)) by (clear; lia). apply junk_merge; [| | clear; lia| clear -NMS N6 NB; lia].
                   - pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
                   - eapply junk_frame; [| exact MUn| exact WM| intros POS; apply Kchunk; clear -EUB MSB POS; lia].
                     replace (mb + 6128 + 24) with (UB + 8) in UJ by (rewrite EUB; clear; lia). exact UJ. }
          split; [eapply fill_frame; [exact S1| exact MUn| exact WM| intros _; apply Kshad; clear -SHLO SHHI SHE MSB; unfold AIMG_HI; Z.div_mod_to_equations; lia]|].
          rewrite (granules_rup n) by (clear -NB; lia). rewrite <- EGQ. unfold sec_user_shadow.
          split; [rewrite (granules_rup n) by (clear -NB; lia); rewrite <- EGQ; exact SH'|].
          replace (mb + 6128 + 16) with UB in S3 by (rewrite EUB; clear; lia).
          eapply fill_frame; [exact S3| exact MUn| exact WM| intros POS; apply Kshad; clear -SHLO SHHI SHE SHL SHP POS MSB; unfold AIMG_HI; Z.div_mod_to_equations; lia].
        * (* [comment removed for export] *)
          (nd_pre (PER j c Hj) 3%nat; intros lvj LVj CHj; nd_post). exists lvj. split; [rewrite (LVE j c Hj NEji); exact LVj|].
          assert (INj : In c order) by (eapply nth_error_In; exact Hj).
          pose proof (proj1 (Forall_forall _ _) WF1o c INj) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
          (nd_pre (sec_wf1_facts' L mb' ms' n' Wc) 12%nat; intros JAL JLO JCE _ _ _ JMSB _ _ _ (JC_t & _ & JC_r & _ & JC_n & JC_st & _) _; nd_post).
          assert (NEc : CSec mb' ms' n' <> ch).
          { intros E. apply NEji. destruct WDo as [ND _]. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
          destruct WDo as [_ DJ]. assert (INo : In ch order) by (eapply nth_error_In; exact NTH).
          destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
          all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
          all: unfold K_HIGH_MEM in JLO, JCE.
          all: (pose proof (ablk_lin _ _ JLO) as ndP__; nd_pre ndP__ 4%nat; intros JL1 JL2 JL3 JL4; nd_post); unfold AIMG_HI in JL1; (pose proof (ablk_int _ _ JLO) as ndP__; nd_pre ndP__ 6%nat; intros kJ KAJ KBJ KEJ KCJ KDJ; nd_post).   (* [comment removed for export] *)
          all: eapply asec_chunk_frameD'; [exact MUn| exact Wc| | | | exists (Z.of_nat j); exact CHj].
          all: try (intros Ad kk Z1 Z2 Z3; apply Kobj; [clear -Z1 Z3 JLO JL1 KAJ KBJ KEJ KCJ KDJ; lia| clear -Z3 JCE; lia| clear -Z2; lia| clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_r; lia| clear -Z1 Z3 JC_n; lia| clear -Z1 Z3 JC_st; lia| clear -Z1 Z3 Dc; lia]).
          all: try (pose proof CHj as CH1; cbn [asec_chunk] in CH1; destruct CH1 as (Hh & _);
                    eapply cells_frame; [exact Hh| exact MUn| exact WM| cbn; apply Kobj; [clear -JLO JL1 JMSB KAJ KBJ KEJ KCJ KDJ; lia| clear -JCE JMSB; lia| clear; lia| clear -JC_t JMSB; lia| clear -JC_r JMSB; lia| clear -JC_n JMSB; lia| clear -JC_st JMSB; lia| clear -Dc JMSB; lia]]).
          -- intros Ad kk Z1 Z2 Z3. apply Kshad; [rewrite shad_div in Z1; unfold ASHOFF, AIMG_HI in *; clear -Z1 JLO JL1; Z.div_mod_to_equations; lia| rewrite shad_div in Z3; unfold ASHOFF in *; clear -Z3 JCE JAL8; Z.div_mod_to_equations; lia| clear -Z2; lia|].
             left. rewrite SHE. pose proof (shad_sep _ _ _ Dc JAL8) as HH. rewrite shlen_div in HH. clear -HH Z3. lia.
          -- intros Ad kk Z1 Z2 Z3. apply Kshad; [rewrite shad_div in Z1; unfold ASHOFF, AIMG_HI in *; clear -Z1 JLO JL1; Z.div_mod_to_equations; lia| rewrite shad_div in Z3; unfold ASHOFF in *; clear -Z3 JCE JAL8; Z.div_mod_to_equations; lia| clear -Z2; lia|].
             right. rewrite SHE. pose proof (shad_sep _ _ _ Dc MAL8) as HH. rewrite shlen_div in HH. clear -HH Z1 SHL. lia.
    - (* [comment removed for export] *) (nd_pre SINST 6%nat; intros I1 [srt I2] I3 I4 I5 I6; nd_post). unfold asec_inst. unfold AINSTANCE in *.
      split; [eapply cells_frame; [exact I1| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [exists srt; eapply cells_frame; [exact I2| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply junk_frame; [exact I3| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply junk_frame; [exact I4| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply cells_frame; [exact I5| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      eapply junk_frame; [exact I6| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia].
    - (* [comment removed for export] *) unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MUn| exact WM|]. intros POS.
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -RSP RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP2. unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *. Z.div_mod_to_equations. lia.
      + clear -POS; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) (al_space_beg L) ltac:(clear -RSP; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D SP2 RSP; unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia| clear -SP3; unfold K_ALIGN in SP3; Z.div_mod_to_equations; lia] | clear; lia].
    - (* [comment removed for export] *) intros x Hx HFh HC.
      pose proof HC as HC0.
      assert (INst : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
      pose proof (proj1 (Forall_forall _ _) HC0 ch INst) as NX. unfold ch in NX. cbn [sec_mb sec_ms] in NX.
      unfold K_HIGH_MEM, AIMG_HI, KLS in Hx.   (* [comment removed for export] *)
      assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM in *; clear -Hx; Z.div_mod_to_equations; lia).
      rewrite <- (SHZ0 x ltac:(unfold K_HIGH_MEM; exact Hx) HFh HC0). apply MUn. rewrite wa_unsigned by exact SX.
      eapply (disjoint_outside _ (shad x) 1); [| clear; lia]. apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -Hx; Z.div_mod_to_equations; lia| rewrite shad_div; unfold ASHOFF; pose proof atop_range as AR8; clear -Hx AR8; Z.div_mod_to_equations; lia| clear; lia|].
      rewrite SHE. destruct (Z_lt_le_dec x mb) as [LT|GE].
      + left. rewrite !shad_div. clear -LT MAL8. Z.div_mod_to_equations. lia.
      + right. rewrite !shad_div in *. clear -GE NX SHL MAL8 MSAL. Z.div_mod_to_equations. lia. }
  assert (BL' : ablocks L st1 X (lb_remove p LB)).
  { eapply (ablocks_free_sec L st X LB p mb ms n st1 X LIVE WF ELIVE); [| exact BL]. intros y Hy. exact Hy. }
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi FKa [kF FBND]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (SHB : 2148238848 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SHE SHL; lia).   (* [comment removed for export] *)
  assert (HFK' : AFK L (lb_remove p LB) m').
  { eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
    - pose proof (ao_dtls L ALO) as DTO. (pose proof (aobj4_int _ DTO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DBND] [jD DIMG]; nd_post). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE, K_HIGH_MEM in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148238848 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
        rewrite SHE. destruct SC_f as [D|D].
        - right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH. clear -HH SHL. lia.
        - left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [exact D| clear -FKO FKi FBND; Z.div_mod_to_equations; lia] | clear; lia]. }
      (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *) | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *) | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | idtac]]]]]]]]]]]]]]]]).
      apply Forall_nil.
    - intros cls FA sz. rewrite (In_lb_remove p LB). cbn. split; [intros [Hin _]; exact Hin| intros Hin; split; [exact Hin| discriminate]]. }
  (* [comment removed for export] *)
  assert (BGEOq : forall q, In q (q_loc Q ++ q_glob Q) ->
      al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
  { intros q Hq. (pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ P1 P2 P3 P4 P5 P6 _; nd_post).
    rewrite size_of_class_24 in P2, P6. unfold abatch_addr. unfold K_SPACE_SIZE in P6. change (2^37) with 137438953472 in P6.
    generalize P1 P2 P5 P6 RSP; clear; intros. lia. }
  assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) 0 0 0) (abatch_addr L (qb_slot q)) 8192).
  { intros q Hq. destruct (BGEOq q Hq) as [F3 F4]. apply Kres; [clear -F3; lia| exact F4| clear; lia| | |]; right; clear -F3 RES RHI; lia. }
  assert (HQ' : AQUAR_at L st1 X QM m').
  { subst QM. unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend].
    change (a_qloc st1) with (a_qloc st). change (a_qglob st1) with (a_qglob st). change (a_qloc_bytes st1) with (a_qloc_bytes st). change (a_qglob_bytes st1) with (a_qglob_bytes st).
    split; [| split; [| split; [| split; [| split]]]].
    - split; [eapply cells_frame; [exact QK| exact MUn| exact WM| cbn [cells_size csize Nat.add]; apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia]|].
      eapply cells_frame; [exact MX| exact MU| exact WM| cbn [cells_size csize Nat.add]; apply KgO; clear; unfold AQ_MUTEX; lia].
    - split; [eapply cells_frame; [exact QC| exact MU| exact WM| cbn [cells_size csize Nat.add]; unfold aq_tcache; apply KtO; clear; lia]|].
      eapply (abatches_frame L _ m m' MUn WM); [exact ABL|]. intros q Hq. unfold Q_BATCH_BYTES. apply BFR. apply in_or_app. left. exact Hq.
    - split; [eapply cells_frame; [exact GCQ| exact MU| exact WM| cbn [cells_size csize Nat.add]; apply KgO; clear; unfold AQ_GCACHE; lia]|].
      eapply (abatches_frame L _ m m' MUn WM); [exact ABG|]. intros q Hq. unfold Q_BATCH_BYTES. apply BFR. apply in_or_app. right. exact Hq.
    - split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. revert Hj. clear. unfold AIA_MAP1_LEN. intros Hj. Z.div_mod_to_equations. lia.
    - exact CP.
    - exact NUM. }
  (* [comment removed for export] *)
  assert (HBK : forall blk, In blk (lb_remove p LB) -> disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) 0 0 0) (ab_addr blk) (ab_size blk)).
  { intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size]; apply (proj1 (In_lb_remove p LB _)) in Hin; destruct Hin as [Hin NEp]; cbn [ab_kind] in NEp.
    - destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb' & msz' & Lp & EUA & Gs)].
      + destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        pose proof (busy_of_In_nodup L st X b WF Hb) as BOF.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
        (pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (DQ : forall q', In q' (q_loc Q ++ q_glob Q) ->
            aslot_addr L cb kb + size_of_class cb <= abatch_addr L (qb_slot q') \/ abatch_addr L (qb_slot q') + 8192 <= aslot_addr L cb kb).
        { intros q' Hq'. (nd_pre (bslot_busy L st X Q CP q' Hq') 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> qb_slot q').
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2.
            pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq, <- E1, <- E2, BOF in BY. injection BY as EE. subst yq. rewrite Sb in Syq. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS (qb_slot q') ALO WF HCb (K24) HKb (bslot_range L st X Q WF CP q' Hq') NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia | | |]; right; clear -FIT P5 RSP RES RHI; lia.
      + (* [comment removed for export] *)
        assert (NEq : q <> p) by (intros ->; apply NEp; reflexivity).
        assert (NEc : CSec mb' msz' n' <> ch).
        { intros E. apply NOTL. exists q. rewrite ELIVE, lookup_delete_ne by (intros E'; exact (NEq (eq_sym E'))). rewrite <- E. exact Lp. }
        assert (INc : In (CSec mb' msz' n') (sec_chunks_of st)) by (eapply live_sec_in; exact Lp).
        assert (INs : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
        destruct WD as [_ DJ]. destruct (DJ _ _ INc INs NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
        all: cbn [sec_wf1] in Gs; (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        all: pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF; subst A'; unfold SEC_UOFF, K_HIGH_MEM in *.
        all: unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        all: apply Kobj; [clear -Gs2 Gs4 Gs5 SF; lia| clear -Gs3 Gs4 Gs5 SF; lia| clear -Gs5; lia| clear -Gs4 Gs5 SF Ct; lia| clear -Gs4 Gs5 SF Cr; lia| clear -Gs4 Gs5 SF Cn; lia| clear -Gs4 Gs5 SF Cs; lia| clear -Gs4 Gs5 SF Dc; lia].
    - (nd_pre (FKD cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post). unfold K_HIGH_MEM in *.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia | clear -K1 K3 SC_f; lia]. }
  (* [comment removed for export] *)
  assert (TLSK : forall TA tk, ATPv + -200 <= TA -> TA + tk <= ATPv + 312 -> 0 <= tk ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) 0 0 0) TA tk).
  { intros TA tk TH1 TH2 TH3. pose proof ATPv_img as TI. apply Kimg; clear -TH1 TH2 TH3 TI; unfold AIMG_HI; lia. }
  assert (TLSS : forall a', ATPv + -200 <= a' < ATPv + 312 ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) 0 0 0) (shad a') 1).
  { intros a' Ha'. pose proof ATPv_img as TI. apply Klow; clear -Ha' TI; try (rewrite shad_div; unfold ASHOFF); try Z.div_mod_to_equations; lia. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) (lb_remove p LB) -> forall a', FA <= a' < FA + sz ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) 0 0 0) (shad a') 1).
  { intros cls FA sz Hin a' Ha'. apply (proj1 (In_lb_remove p LB _)) in Hin. destruct Hin as [Hin _].
    (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). unfold K_HIGH_MEM in *.
    assert (FAL8 : al_fake L mod 8 = 0) by (destruct FKO as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
    apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
    rewrite SHE. destruct SC_f as [D|D].
    - right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
      pose proof (shad_mono (al_fake L) a' ltac:(clear -K1 Ha'; lia)) as MM. clear -HH MM SHL. lia.
    - left. pose proof (shad_sep _ _ _ D FAL8) as HH. rewrite (shad_div a'), (shad_div (al_fake L)), shlen_div in *.
      clear -HH Ha' K3 FAL8. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  split; [| split; [exact BL'| split; [exact HFK'|]]].
  - split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3'].
  - eapply (aheap_pres_freeS CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact TLSK | exact TLSS | apply Klow; unfold AIMSH_LO, AIMSH_LEN; clear; lia
      | rewrite <- (ao_ahm_eq L ALO); unfold AAHM_SZ; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI;
      pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; pose proof (ad_ahm_nodes L ALO) as DA3; pose proof (ad_ahm_store L ALO) as DA4;
      (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ SC_ahm; nd_post);
      unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OAH, OAHI, DA1, DA2, DA3, DA4; apply Kobj; clear -OAH OAHI DA1 DA2 DA3 DA4 SC_ahm; lia].
Qed.
End Zd1.
#[using="HL CI_OK"] Theorem mid_kitS : ltac:(let t := eval cbv delta [mid_kitS__stmt] in mid_kitS__stmt in exact t).
Proof. exact mid_kitS__body. Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_icptR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.AFreeStoreK.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_store.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6307840 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6307840 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.

Definition mid_kitS__stmt : Prop := mid_stmtS DI AFK CI.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 1).
Variable full : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 2).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 3).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 4).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 5).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 6).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 7).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 8).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 9).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 10).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 11).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 12).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 13).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 14).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 15).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 16).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 17).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 18).
Variable F : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 19).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 20).
Variable m : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 21).
Variable st : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 22).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 23).
Variable X : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 24).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 25).
Variable p : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 26).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 27).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 28).
Variable n : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 29).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 30).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 31).
Variable A : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 32).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 33).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 34).
Variable nx : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 35).
Variable bsz : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 36).
Variable hs : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 37).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'mid_kitS__stmt 38).
Let ch := CSec mb ms n.
Let st1 := set_live (delete p (a_live st)) st.
Let QM := mkQConc (q_loc Q) (q_glob Q) true (q_pend Q).
Let UB := mb + 6144.
Let gq := shlen (rup n 8).
#[using="HL CI_OK ch st1 QM UB gq"] Lemma mid_kitS__body : ltac:(let T := type of (fun (h : mid_kitS__stmt) => h L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p mb ms n b1 ctx A lo lst nx bsz hs tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (full, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (F, (fc, (m, (st, (LB, (X, (Q, (p, (mb, (ms, (n, (b1, (ctx, (A, (lo, (lst, (nx, (bsz, (hs, tr))))))))))))))))))))))))))))))))))))))) as _.
  unfold mid_stmtS. 
  cbv zeta. intros ALO ARNG AR AQ BL HFK LIVE HIN NQM HDR B1 B13 CTX CEIL LO ms1 PM. unfold AFREE_STACK in LO.
  chg (CSec mb ms n) ch.
  chg (set_live (delete p (a_live st)) st) st1.
  chg (mkQConc (q_loc Q) (q_glob Q) true (q_pend Q)) QM.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS0 UNW; nd_post).
  (nd_pre (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) 3%nat; intros EAu _ WFch; nd_post).
  (nd_pre (sec_wf1_facts' L mb ms n WFch) 13%nat; intros MAL MLO MCE MSE NB RZ MSB MSAL NMS NS0 SCL NPR N6; nd_post).
  (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post). unfold AIMG_HI in ML1. (pose proof (ablk_int _ _ MLO) as ndP__; nd_pre ndP__ 6%nat; intros kM KAM KBM KEM KCM KDM; nd_post).   (* [comment removed for export] *)
  (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros SC_t SC_c SC_r SC_p SC_n SC_st SC_f SC_d SC_tls SC_ahm0; nd_post).
  pose proof HS as HS0. (nd_pre HS0 5%nat; intros WFS _ SINST PZ SHZ; nd_post).
  (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros _ WP WR WL WB WF1 WD; nd_post).
  (nd_pre (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE) 25%nat; intros order i b1r cxr uw PO NTH IL LENO WF1o WDo U64 JK PER CH H1 H5 _ _ _ HUW UJ S1 S2 S3; nd_post).
  cbv zeta in H5, HUW, UJ, S2, S3.
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  (pose proof (aobj4_int _ OT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ OC ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci _ [kC CBND]; nd_post). (pose proof (aobj_int _ _ ON ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni _ [kN NBND]; nd_post).
  (pose proof (aobj_int _ _ OS ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si _ [kS SBND]; nd_post). pose proof (ao_res_hi L ALO) as RHI.
  unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
  box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
  word_range sp SPR.
  chg (mb + 6144) UB.
  assert (EUB : UB = mb + 6144) by reflexivity.
  assert (EHM : mb + 6128 = UB - 16) by (subst UB; clear; lia).
  assert (UB16' : UB mod 8 = 0) by (subst UB; clear -MAL; Z.div_mod_to_equations; lia).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  rewrite EHM in PM, HDR.
  (pose proof (rup8_facts n ltac:(clear -NB; lia)) as ndP__; nd_pre ndP__ 3%nat; intros RUP RUP8 RUPS; nd_post).
  assert (SHGEO : shad UB = shad mb + 768 /\ shlen (rup n 8) <= ms / 8 - 768 /\ 0 < shlen (rup n 8) /\ UB + rup n 8 <= mb + ms
                  /\ 2148239360 <= shad mb /\ shad mb + ms / 8 <= 17594332446720).   (* [comment removed for export] *)
  { subst UB. rewrite !shad_div, RUPS. unfold ASHOFF. (pose proof (sec_facts n ltac:(clear -NB; lia) NPR) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ RS1 _ NSE _; nd_post).
    unfold K_HIGH_MEM in *. pose proof atop_range as AR8. clear -MAL RUP RUP8 RS1 NSE NMS N6 NB ML1 ML3 MCE MSAL AR8. Z.div_mod_to_equations. lia. }
  (nd_pre SHGEO 6%nat; intros SHE SHL SHP UBS SHLO SHHI; nd_post).
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof NUM as NUM0. (nd_pre NUM0 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof CP as CP0. (nd_pre CP0 7%nat; intros LN1 LN2 _ _ ND2 BSI _; nd_post).
  (* [comment removed for export] *)
  unfold free_to_refill_post in PM.
  (nd_pre PM 18%nat; intros id t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' m' sj' tb' junk2 j0 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 22%nat; intros MU WM MI' ST' IDR HDR' FC' SH' STATS' LSJ' UW' FL' IAS' IAM' SS' TB' LTB' FRS' FRP' FRE' LBS' DEP'; nd_post).
  cbn [ms_mem MS].
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  chg (shlen (rup n 8)) gq. assert (EGQ : gq = shlen (rup n 8)) by reflexivity. clearbody gq.
  (* [comment removed for export] *)
  assert (MUn : munch (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) 0 0 0) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  assert (KF : kfactsS (bv_unsigned sp) (al_t L) mb ms UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo 0 0 0).
  { unfold kfactsS. unfold K_HIGH_MEM in *.
    assert (GQ1 : 1 <= gq) by (clear -SHP EGQ; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP MLO ML1 ML3 MCE EUB UBS NB RUP SC_t SC_r SC_n SC_st SHE SHL SHLO SHHI GQ1 EGQ. clear. intros.
    rewrite ?EGQ in SHL. unfold iclr, AIMG_LO, AIMG_HI in *. rewrite ?qsz_0.   (* [comment removed for export] *)
    sg_destr; repeat split; first [assumption | lia]. }
  pose proof (KS_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KS_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KS_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KS_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KS_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s) SC_c) as Kctx.
  pose proof (KS_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
  pose proof (KS_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
  pose proof (KS_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KS_objL _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as KobjL.      (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
  unfold adisj in D_l_t, D_l_r, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
  pose proof (KS_chunk _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kchunk.
  (* [comment removed for export] *)
  lazymatch type of MU with munch ?W0 _ _ =>
    assert (KtO : forall Ad kk, al_t L + 80 <= Ad -> Ad + kk <= al_t L + 2800 -> 0 <= kk -> disjoint_from W0 Ad kk);
    [ intros Ad kk Y1 Y2 Y3; pose proof DL7 as X7; unbox X7; pose proof DL8 as X8; unbox X8;
      cbn [disjoint_from]; unfold K_HIGH_MEM in *; clear -Y1 Y2 Y3 TL1 TL2 TBND TIMG LO CEIL X7 X8 SC_t MSB EUB UBS NB RUP SHLO SHHI SHE SHL; repeat (split; [lia|]); exact I |];   (* [comment removed for export] *)
    assert (KgO : forall Ad kk, 0xab670 <= Ad -> Ad + kk <= 0xab730 -> 0 <= kk -> disjoint_from W0 Ad kk);
    [ intros Ad kk Y1 Y2 Y3; cbn [disjoint_from]; unfold K_HIGH_MEM in *; clear -Y1 Y2 Y3 TL1 TBND TIMG LO CEIL MLO ML1 ML3 KAM KBM KEM KCM KDM EUB DL1 DL4 Ni Si NBND SBND SHLO SHE; repeat (split; [lia|]); exact I |]   (* [comment removed for export] *)
  end.
  (* [comment removed for export] *)
  assert (ELIVE : a_live st1 = delete p (a_live st)) by reflexivity.
  assert (NDS : forall c', ndist st1 c' = ndist st c') by (intros c'; reflexivity).
  assert (WF' : awf L st1 X) by (apply (awf_delete_sec L st X p mb ms n st1 WF LIVE); reflexivity).
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    (first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |])] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]). apply Forall_nil. }
  assert (INST' : ainstance L st1 m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
  assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
  assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
  (* [comment removed for export] *)
  assert (THR' : athread L st1 X m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - intros c' Hc'. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c' Hc') | reflexivity | reflexivity | reflexivity |].
      unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply KtO; clear -Hc'; lia.
    - eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply KtO; clear; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  (* [comment removed for export] *)
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L st1 m' c'' /\ afreearray L st1 X m' c'' /\ aslots L st1 X m' c'' /\ aslot_shadow L st1 X m' c'').
  { intros c'' Hc''. (nd_pre (CLS c'' Hc'') 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (aregion_mod L c'' SAL) as RM''.
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 4%nat; intros RI1 RI2 RI3 RI4; nd_post).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      apply Kres; try (clear -Hc'' RSP; lia); right; clear -Hc'' RSP RES RHI; lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia | | |]; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, AIMG_HI, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
          rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) (afreearr L c'') ltac:(clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D RI2 RI3 FA2; lia| exact AM] | clear; lia].
    - (* [comment removed for export] *)
      eapply (aslots_update_gen L _ m m' MUn WM st st1 X X c''); [exact SLOTS | apply NDS | reflexivity | reflexivity | |].
      + intros k'' Hk''. left.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        split; [reflexivity|]. split.
        * apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia | | |]; right; clear -P5 RSP RES RHI; lia.
        * intros b Hb. (nd_pre (busy_of_Some_facts X c'' k'' b Hb) 3%nat; intros IB CB' KB'; nd_post). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia | | |]; right; clear -RI4 Q1 U0 RES RHI; lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update_gen L _ m m' MUn WM st st1 X X c''); [exact SHADOW | apply NDS | reflexivity | reflexivity | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk''. left.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        split; [reflexivity|].
        pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -T16; lia.
        * rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) (aslot_addr L c'' k'') ltac:(clear -P5 RSP; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D P6 RI3; unfold K_SPACE_SIZE in *; lia| clear -AL''; Z.div_mod_to_equations; lia] | clear; lia].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) AU ltac:(clear -U0 RI4; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D U0' RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia].
  }
  (* [comment removed for export] *)
  assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st1 m' c'').
  { intros c'' Hc''. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). pose proof (aregion_mod L c'' SAL) as RM''.
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post).
    eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | reflexivity | reflexivity | |].
    - intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
      assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
      destruct U0 as [U0 U0'].
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) AU ltac:(clear -U0 RI1; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D U0' RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) AU ltac:(clear -FA1 RI1; unfold K_FREEARR_OFF in *; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D FA2 RI2 RI3; unfold K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia]. }
  (* [comment removed for export] *)
  assert (NOTL : ~ sec_live st1 ch) by (apply (sec_not_live_after L st _ p mb ms n st1 WFS (Permutation_refl _) LIVE ELIVE)).
  assert (LVE : forall j c, nth_error order j = Some c -> j <> i -> (sec_live st1 c <-> sec_live st c)).
  { intros j c Hj NEj. apply (sec_live_other st p mb ms n st1 c LIVE ELIVE).
    intros E. apply NEj. destruct WDo as [ND _].
    apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH. unfold ch. rewrite E. reflexivity. }
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p.
  pose proof (ao_ptr L ALO) as OP. (pose proof (aobj_int _ _ OP ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OPi OPa [kP OPs]; nd_post). unfold adisj, aobj in D_t_p, D_p_r, D_n_p, D_s_p, OP.   (* [comment removed for export] *)
  assert (HS' : ASECc (sec_chunks_of st) L st1 X m').
  { unfold ASECc.
    pose proof HS as HS1. (nd_pre HS1 5%nat; intros _ _ _ _ SHZ0; nd_post).
    split; [| split; [| split; [| split]]].
    - (* [comment removed for export] *) exact WFS.
    - (* [comment removed for export] *) exists order. change (a_nres st1) with (a_nres st). change (a_nsec st1) with (a_nsec st).
      split; [exact PO|].
      unfold K_HIGH_MEM in *.
      split; [| split].
      + eapply u64arr_frame; [exact U64| exact MUn| exact WM|]. rewrite length_map, LENO.
        apply Kobj; [clear -OP OPi OPs WB WR LENO; lia| clear -OP OPi OPs WB WR; lia| clear -WB; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
      + eapply junk_frame; [exact JK| exact MUn| exact WM|]. intros POS.
        apply Kobj; [clear -OP OPi OPs WB WR POS; lia| clear -OP OPi OPs WB WR; lia| clear -WB POS; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
      + intros j c Hj. destruct (Nat.eq_dec j i) as [->|NEji].
        * (* [comment removed for export] *)
          rewrite NTH in Hj. injection Hj as <-. exists false. split; [split; [discriminate| intros Hl; exfalso; exact (NOTL Hl)]|].
          unfold ch. cbn [asec_chunk]. pose proof CH as CH0. cbn [asec_chunk] in CH0.
          (nd_pre CH0 9%nat; intros G1 G2 G3 G4 _ _ _ _ _; nd_post). unfold SEC_UOFF in *. rewrite <- ?EUB in *.
          replace (UB - 16 + 16) with UB in FC' by (clear; lia).
          split; [eapply cells_frame; [exact G1| exact MUn| exact WM| cbn; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply junk_frame; [exact G2| exact MUn| exact WM| intros _; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply cells_frame; [exact G3| exact MUn| exact WM| cbn; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply junk_frame; [exact G4| exact MUn| exact WM| intros _; apply Kchunk; clear -EUB MSB; lia]|].
          split; [exists b1, ctx; split; [exact HDR'| split; [exact B1| split; [exact B13| exact CTX]]]|].
          split. { replace (ms - 6144) with (8 + (ms - 6144 - 8)) by (clear; lia). apply junk_merge; [| | clear; lia| clear -NMS N6 NB; lia].
                   - pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
                   - eapply junk_frame; [| exact MUn| exact WM| intros POS; apply Kchunk; clear -EUB MSB POS; lia].
                     replace (mb + 6128 + 24) with (UB + 8) in UJ by (rewrite EUB; clear; lia). exact UJ. }
          split; [eapply fill_frame; [exact S1| exact MUn| exact WM| intros _; apply Kshad; clear -SHLO SHHI SHE MSB; unfold AIMG_HI; Z.div_mod_to_equations; lia]|].
          rewrite (granules_rup n) by (clear -NB; lia). rewrite <- EGQ. unfold sec_user_shadow.
          split; [rewrite (granules_rup n) by (clear -NB; lia); rewrite <- EGQ; exact SH'|].
          replace (mb + 6128 + 16) with UB in S3 by (rewrite EUB; clear; lia).
          eapply fill_frame; [exact S3| exact MUn| exact WM| intros POS; apply Kshad; clear -SHLO SHHI SHE SHL SHP POS MSB; unfold AIMG_HI; Z.div_mod_to_equations; lia].
        * (* [comment removed for export] *)
          (nd_pre (PER j c Hj) 3%nat; intros lvj LVj CHj; nd_post). exists lvj. split; [rewrite (LVE j c Hj NEji); exact LVj|].
          assert (INj : In c order) by (eapply nth_error_In; exact Hj).
          pose proof (proj1 (Forall_forall _ _) WF1o c INj) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
          (nd_pre (sec_wf1_facts' L mb' ms' n' Wc) 12%nat; intros JAL JLO JCE _ _ _ JMSB _ _ _ (JC_t & _ & JC_r & _ & JC_n & JC_st & _) _; nd_post).
          assert (NEc : CSec mb' ms' n' <> ch).
          { intros E. apply NEji. destruct WDo as [ND _]. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
          destruct WDo as [_ DJ]. assert (INo : In ch order) by (eapply nth_error_In; exact NTH).
          destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
          all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
          all: unfold K_HIGH_MEM in JLO, JCE.
          all: (pose proof (ablk_lin _ _ JLO) as ndP__; nd_pre ndP__ 4%nat; intros JL1 JL2 JL3 JL4; nd_post); unfold AIMG_HI in JL1; (pose proof (ablk_int _ _ JLO) as ndP__; nd_pre ndP__ 6%nat; intros kJ KAJ KBJ KEJ KCJ KDJ; nd_post).   (* [comment removed for export] *)
          all: eapply asec_chunk_frameD'; [exact MUn| exact Wc| | | | exists (Z.of_nat j); exact CHj].
          all: try (intros Ad kk Z1 Z2 Z3; apply Kobj; [clear -Z1 Z3 JLO JL1 KAJ KBJ KEJ KCJ KDJ; lia| clear -Z3 JCE; lia| clear -Z2; lia| clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_r; lia| clear -Z1 Z3 JC_n; lia| clear -Z1 Z3 JC_st; lia| clear -Z1 Z3 Dc; lia]).
          all: try (pose proof CHj as CH1; cbn [asec_chunk] in CH1; destruct CH1 as (Hh & _);
                    eapply cells_frame; [exact Hh| exact MUn| exact WM| cbn; apply Kobj; [clear -JLO JL1 JMSB KAJ KBJ KEJ KCJ KDJ; lia| clear -JCE JMSB; lia| clear; lia| clear -JC_t JMSB; lia| clear -JC_r JMSB; lia| clear -JC_n JMSB; lia| clear -JC_st JMSB; lia| clear -Dc JMSB; lia]]).
          -- intros Ad kk Z1 Z2 Z3. apply Kshad; [rewrite shad_div in Z1; unfold ASHOFF, AIMG_HI in *; clear -Z1 JLO JL1; Z.div_mod_to_equations; lia| rewrite shad_div in Z3; unfold ASHOFF in *; clear -Z3 JCE JAL8; Z.div_mod_to_equations; lia| clear -Z2; lia|].
             left. rewrite SHE. pose proof (shad_sep _ _ _ Dc JAL8) as HH. rewrite shlen_div in HH. clear -HH Z3. lia.
          -- intros Ad kk Z1 Z2 Z3. apply Kshad; [rewrite shad_div in Z1; unfold ASHOFF, AIMG_HI in *; clear -Z1 JLO JL1; Z.div_mod_to_equations; lia| rewrite shad_div in Z3; unfold ASHOFF in *; clear -Z3 JCE JAL8; Z.div_mod_to_equations; lia| clear -Z2; lia|].
             right. rewrite SHE. pose proof (shad_sep _ _ _ Dc MAL8) as HH. rewrite shlen_div in HH. clear -HH Z1 SHL. lia.
    - (* [comment removed for export] *) (nd_pre SINST 6%nat; intros I1 [srt I2] I3 I4 I5 I6; nd_post). unfold asec_inst. unfold AINSTANCE in *.
      split; [eapply cells_frame; [exact I1| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [exists srt; eapply cells_frame; [exact I2| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply junk_frame; [exact I3| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply junk_frame; [exact I4| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply cells_frame; [exact I5| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      eapply junk_frame; [exact I6| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia].
    - (* [comment removed for export] *) unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MUn| exact WM|]. intros POS.
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -RSP RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP2. unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *. Z.div_mod_to_equations. lia.
      + clear -POS; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) (al_space_beg L) ltac:(clear -RSP; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D SP2 RSP; unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia| clear -SP3; unfold K_ALIGN in SP3; Z.div_mod_to_equations; lia] | clear; lia].
    - (* [comment removed for export] *) intros x Hx HFh HC.
      pose proof HC as HC0.
      assert (INst : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
      pose proof (proj1 (Forall_forall _ _) HC0 ch INst) as NX. unfold ch in NX. cbn [sec_mb sec_ms] in NX.
      unfold K_HIGH_MEM, AIMG_HI, KLS in Hx.   (* [comment removed for export] *)
      assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM in *; clear -Hx; Z.div_mod_to_equations; lia).
      rewrite <- (SHZ0 x ltac:(unfold K_HIGH_MEM; exact Hx) HFh HC0). apply MUn. rewrite wa_unsigned by exact SX.
      eapply (disjoint_outside _ (shad x) 1); [| clear; lia]. apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -Hx; Z.div_mod_to_equations; lia| rewrite shad_div; unfold ASHOFF; pose proof atop_range as AR8; clear -Hx AR8; Z.div_mod_to_equations; lia| clear; lia|].
      rewrite SHE. destruct (Z_lt_le_dec x mb) as [LT|GE].
      + left. rewrite !shad_div. clear -LT MAL8. Z.div_mod_to_equations. lia.
      + right. rewrite !shad_div in *. clear -GE NX SHL MAL8 MSAL. Z.div_mod_to_equations. lia. }
  assert (BL' : ablocks L st1 X (lb_remove p LB)).
  { eapply (ablocks_free_sec L st X LB p mb ms n st1 X LIVE WF ELIVE); [| exact BL]. intros y Hy. exact Hy. }
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi FKa [kF FBND]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (SHB : 2148239360 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SHE SHL; lia).   (* [comment removed for export] *)
  assert (HFK' : AFK L (lb_remove p LB) m').
  { eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
    - pose proof (ao_dtls L ALO) as DTO. (pose proof (aobj4_int _ DTO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DBND] [jD DIMG]; nd_post). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE, K_HIGH_MEM in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148239360 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
        rewrite SHE. destruct SC_f as [D|D].
        - right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH. clear -HH SHL. lia.
        - left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [exact D| clear -FKO FKi FBND; Z.div_mod_to_equations; lia] | clear; lia]. }
      (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *) | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *) | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | idtac]]]]]]]]]]]]]]]]).
      apply Forall_nil.
    - intros cls FA sz. rewrite (In_lb_remove p LB). cbn. split; [intros [Hin _]; exact Hin| intros Hin; split; [exact Hin| discriminate]]. }
  (* [comment removed for export] *)
  assert (BGEOq : forall q, In q (q_loc Q ++ q_glob Q) ->
      al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
  { intros q Hq. (pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ P1 P2 P3 P4 P5 P6 _; nd_post).
    rewrite size_of_class_24 in P2, P6. unfold abatch_addr. unfold K_SPACE_SIZE in P6. change (2^37) with 137438953472 in P6.
    generalize P1 P2 P5 P6 RSP; clear; intros. lia. }
  assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) 0 0 0) (abatch_addr L (qb_slot q)) 8192).
  { intros q Hq. destruct (BGEOq q Hq) as [F3 F4]. apply Kres; [clear -F3; lia| exact F4| clear; lia| | |]; right; clear -F3 RES RHI; lia. }
  assert (HQ' : AQUAR_at L st1 X QM m').
  { subst QM. unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend].
    change (a_qloc st1) with (a_qloc st). change (a_qglob st1) with (a_qglob st). change (a_qloc_bytes st1) with (a_qloc_bytes st). change (a_qglob_bytes st1) with (a_qglob_bytes st).
    split; [| split; [| split; [| split; [| split]]]].
    - split; [eapply cells_frame; [exact QK| exact MUn| exact WM| cbn [cells_size csize Nat.add]; apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia]|].
      eapply cells_frame; [exact MX| exact MU| exact WM| cbn [cells_size csize Nat.add]; apply KgO; clear; unfold AQ_MUTEX; lia].
    - split; [eapply cells_frame; [exact QC| exact MU| exact WM| cbn [cells_size csize Nat.add]; unfold aq_tcache; apply KtO; clear; lia]|].
      eapply (abatches_frame L _ m m' MUn WM); [exact ABL|]. intros q Hq. unfold Q_BATCH_BYTES. apply BFR. apply in_or_app. left. exact Hq.
    - split; [eapply cells_frame; [exact GCQ| exact MU| exact WM| cbn [cells_size csize Nat.add]; apply KgO; clear; unfold AQ_GCACHE; lia]|].
      eapply (abatches_frame L _ m m' MUn WM); [exact ABG|]. intros q Hq. unfold Q_BATCH_BYTES. apply BFR. apply in_or_app. right. exact Hq.
    - split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. revert Hj. clear. unfold AIA_MAP1_LEN. intros Hj. Z.div_mod_to_equations. lia.
    - exact CP.
    - exact NUM. }
  (* [comment removed for export] *)
  assert (HBK : forall blk, In blk (lb_remove p LB) -> disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) 0 0 0) (ab_addr blk) (ab_size blk)).
  { intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size]; apply (proj1 (In_lb_remove p LB _)) in Hin; destruct Hin as [Hin NEp]; cbn [ab_kind] in NEp.
    - destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb' & msz' & Lp & EUA & Gs)].
      + destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        pose proof (busy_of_In_nodup L st X b WF Hb) as BOF.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
        (pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (DQ : forall q', In q' (q_loc Q ++ q_glob Q) ->
            aslot_addr L cb kb + size_of_class cb <= abatch_addr L (qb_slot q') \/ abatch_addr L (qb_slot q') + 8192 <= aslot_addr L cb kb).
        { intros q' Hq'. (nd_pre (bslot_busy L st X Q CP q' Hq') 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> qb_slot q').
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2.
            pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq, <- E1, <- E2, BOF in BY. injection BY as EE. subst yq. rewrite Sb in Syq. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS (qb_slot q') ALO WF HCb (K24) HKb (bslot_range L st X Q WF CP q' Hq') NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia | | |]; right; clear -FIT P5 RSP RES RHI; lia.
      + (* [comment removed for export] *)
        assert (NEq : q <> p) by (intros ->; apply NEp; reflexivity).
        assert (NEc : CSec mb' msz' n' <> ch).
        { intros E. apply NOTL. exists q. rewrite ELIVE, lookup_delete_ne by (intros E'; exact (NEq (eq_sym E'))). rewrite <- E. exact Lp. }
        assert (INc : In (CSec mb' msz' n') (sec_chunks_of st)) by (eapply live_sec_in; exact Lp).
        assert (INs : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
        destruct WD as [_ DJ]. destruct (DJ _ _ INc INs NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
        all: cbn [sec_wf1] in Gs; (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        all: pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF; subst A'; unfold SEC_UOFF, K_HIGH_MEM in *.
        all: unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        all: apply Kobj; [clear -Gs2 Gs4 Gs5 SF; lia| clear -Gs3 Gs4 Gs5 SF; lia| clear -Gs5; lia| clear -Gs4 Gs5 SF Ct; lia| clear -Gs4 Gs5 SF Cr; lia| clear -Gs4 Gs5 SF Cn; lia| clear -Gs4 Gs5 SF Cs; lia| clear -Gs4 Gs5 SF Dc; lia].
    - (nd_pre (FKD cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post). unfold K_HIGH_MEM in *.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia | clear -K1 K3 SC_f; lia]. }
  (* [comment removed for export] *)
  assert (TLSK : forall TA tk, ATPv + -200 <= TA -> TA + tk <= ATPv + 312 -> 0 <= tk ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) 0 0 0) TA tk).
  { intros TA tk TH1 TH2 TH3. pose proof ATPv_img as TI. apply Kimg; clear -TH1 TH2 TH3 TI; unfold AIMG_HI; lia. }
  assert (TLSS : forall a', ATPv + -200 <= a' < ATPv + 312 ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) 0 0 0) (shad a') 1).
  { intros a' Ha'. pose proof ATPv_img as TI. apply Klow; clear -Ha' TI; try (rewrite shad_div; unfold ASHOFF); try Z.div_mod_to_equations; lia. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) (lb_remove p LB) -> forall a', FA <= a' < FA + sz ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) 0 0 0) (shad a') 1).
  { intros cls FA sz Hin a' Ha'. apply (proj1 (In_lb_remove p LB _)) in Hin. destruct Hin as [Hin _].
    (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). unfold K_HIGH_MEM in *.
    assert (FAL8 : al_fake L mod 8 = 0) by (destruct FKO as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
    apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
    rewrite SHE. destruct SC_f as [D|D].
    - right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
      pose proof (shad_mono (al_fake L) a' ltac:(clear -K1 Ha'; lia)) as MM. clear -HH MM SHL. lia.
    - left. pose proof (shad_sep _ _ _ D FAL8) as HH. rewrite (shad_div a'), (shad_div (al_fake L)), shlen_div in *.
      clear -HH Ha' K3 FAL8. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  split; [| split; [exact BL'| split; [exact HFK'|]]].
  - split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3'].
  - eapply (aheap_pres_freeS CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact TLSK | exact TLSS | apply Klow; unfold AIMSH_LO, AIMSH_LEN; clear; lia
      | rewrite <- (ao_ahm_eq L ALO); unfold AAHM_SZ; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI;
      pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; pose proof (ad_ahm_nodes L ALO) as DA3; pose proof (ad_ahm_store L ALO) as DA4;
      (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ SC_ahm; nd_post);
      unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OAH, OAHI, DA1, DA2, DA3, DA4; apply Kobj; clear -OAH OAHI DA1 DA2 DA3 DA4 SC_ahm; lia].
Qed.
End Zd1.
#[using="HL CI_OK"] Theorem mid_kitS : ltac:(let t := eval cbv delta [mid_kitS__stmt] in mid_kitS__stmt in exact t).
Proof. exact mid_kitS__body. Qed.
End S.
End CANSEC1.
End TwB.
End ASF_mid.

(* [comment removed for export] *)
Module ASF_storeR.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead F_afree_tail. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_read. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.AFreeStoreK OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeStoreR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_store OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : ABase.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6303744 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6303744 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ek_pre_b_hi : forall ek RNG t nb lst n hm m, ek_pre ek RNG t nb lst n hm m -> 0x10007fff8000 <= ek_b ek lst.
Proof.
  intros ek RNG t nb lst n hm m EK.
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0]; cbn [ek_pre ek_b] in *.
  - (nd_pre EK 16%nat; intros NB1 LB CNT BSZ BSZN NX LA LEN LJ L0 L1 DTL DHL CR' STS' RL; nd_post). exact L0.
  - (nd_pre EK 20%nat; intros FULL SB CR CH LCH CNT NTH IXS STS HB BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB; nd_post). exact B0.
Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Definition store_freeRS__stmt : Prop := store_freeRS_stmt DI AFK CI.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 5).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 6).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 7).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 8).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 9).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 10).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 11).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 12).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 13).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 14).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 15).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 16).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 17).
Variable F : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 18).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 19).
Variable m : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 20).
Variable st : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 21).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 22).
Variable X : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 23).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 24).
Variable cs : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 25).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 26).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 27).
Variable n : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 28).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 29).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 30).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 31).
Variable k24 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 32).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 33).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 34).
Let ch := CSec mb ms n.
Let st2 := st_enq st ch.
Let ek := ek_of L st X Q n k24 stj chunks.
Let g := g_of L st Q (ek_delta ek n).
Let UB := mb + 6144.
Let lst := qlast L (q_loc Q).
Let eb := ek_b ek lst.
Let gl := dk_glst g lst.
Let gq := shlen (rup n 8).
Let st' := st_after st2.
#[using="HL CI_OK ch st2 ek g UB lst eb gl gq st'"] Lemma store_freeRS__body : ltac:(let T := type of (fun (h : store_freeRS__stmt) => h L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q cs mb ms n b1 ctx lo k24 stj chunks) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (F, (fc, (m, (st, (LB, (X, (Q, (cs, (mb, (ms, (n, (b1, (ctx, (lo, (k24, (stj, chunks))))))))))))))))))))))))))))))))))) as _.
  unfold store_freeRS_stmt. 
  cbv zeta. intros ALO ARNG AR BL HFK PCS RSCS NOTL NQM B1 B13 CTX EAF NK0 NB0 KK0 NIB0 JK0 FSH0 CIN0 POS0 NOREC EK DK CEIL LO ms' PM. unfold AFREE_STACK in LO.
  assert (NEWF : enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) by (intros _; repeat (split; [assumption|]); exact POS0).
  clear NK0 NB0 KK0 NIB0 JK0 FSH0 CIN0 POS0.
  chg (CSec mb ms n) ch.
  chg (st_enq st ch) st2.
  chg (ek_of L st X Q n k24 stj chunks) ek.
  chg (g_of L st Q (ek_delta ek n)) g.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHSm] in HQ, HS, HD. rename HQ into AQ.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS0 UNW; nd_post).
  pose proof HS as HS0. (nd_pre HS0 5%nat; intros WFS ARR0 SINST PZ SHZ; nd_post).
  (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros _ WP WR WL WB WF1 WD; nd_post).
  assert (INcs : In ch cs) by (eapply Permutation_in; [apply Permutation_sym; exact PCS| left; reflexivity]).
  pose proof (proj1 (Forall_forall _ _) WF1 ch INcs) as WFch.
  (nd_pre (sec_wf1_facts' L mb ms n WFch) 13%nat; intros MAL MLO MCE MSE NB RZ MSB MSAL NMS NS0 SCL NPR N6; nd_post).
  (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post). unfold AIMG_HI in ML1. (pose proof (ablk_int _ _ MLO) as ndP__; nd_pre ndP__ 6%nat; intros kM KAM KBM KEM KCM KDM; nd_post).   (* [comment removed for export] *)
  (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros SC_t SC_c SC_r SC_p SC_n SC_st SC_f SC_d SC_tls SC_ahm0; nd_post).
  (* [comment removed for export] *)
  (nd_pre ARR0 5%nat; intros order PO U64 JK PER; nd_post).
  assert (INo : In ch order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact INcs]).
  destruct (In_nth_error _ _ INo) as [i NTH].
  assert (IL : (i < length order)%nat) by (apply (proj1 (nth_error_Some order i)); rewrite NTH; discriminate).
  assert (LENO : Z.of_nat (length order) = a_nsec st) by (rewrite (Permutation_length PO); exact WL).
  assert (WF1o : Forall (sec_wf1 L) order).
  { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PO| exact Hc]. }
  assert (WDo : sec_disjoint order) by (eapply sec_disjoint_perm; [apply Permutation_sym; exact PO| exact WD]).
  (nd_pre (PER i _ NTH) 3%nat; intros lv0 LV0 CH; nd_post).
  assert (Elv : lv0 = false) by (destruct lv0; [exfalso; apply NOTL; apply (proj1 LV0); reflexivity| reflexivity]). subst lv0.
  pose proof CH as CH0. unfold ch in CH0. cbn [asec_chunk] in CH0.
  (nd_pre CH0 9%nat; intros H1 _ _ _ _ H6 S1 _ S3; nd_post). unfold SEC_UOFF in H6, S3.
  destruct (junk_split m _ 8 (ms - 6144 - 8) ltac:(replace (8 + (ms - 6144 - 8)) with (ms - 6144) by lia; exact H6) ltac:(lia) ltac:(lia)) as [_ UJ].
  rewrite (granules_rup n) in S3 by (clear -NB; lia).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  (pose proof (aobj4_int _ OT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ OC ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci _ [kC CBND]; nd_post). (pose proof (aobj_int _ _ ON ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni _ [kN NBND]; nd_post).
  (pose proof (aobj_int _ _ OS ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si _ [kS SBND]; nd_post). pose proof (ao_res_hi L ALO) as RHI.
  unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
  box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
  word_range sp SPR.
  chg (mb + 6144) UB.
  assert (EUB : UB = mb + 6144) by reflexivity.
  assert (EHM : mb + 6128 = UB - 16) by (subst UB; clear; lia).
  assert (UB16' : UB mod 8 = 0) by (subst UB; clear -MAL; Z.div_mod_to_equations; lia).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  rewrite EHM in PM, EK, DK.
  replace (mb + 6144) with UB in UJ, S3 by reflexivity.
  (pose proof (rup8_facts n ltac:(clear -NB; lia)) as ndP__; nd_pre ndP__ 3%nat; intros RUP RUP8 RUPS; nd_post).
  assert (SHGEO : shad UB = shad mb + 768 /\ shlen (rup n 8) <= ms / 8 - 768 /\ 0 < shlen (rup n 8) /\ UB + rup n 8 <= mb + ms
                  /\ 2148238848 <= shad mb /\ shad mb + ms / 8 <= 17594332446720).   (* [comment removed for export] *)
  { subst UB. rewrite !shad_div, RUPS. unfold ASHOFF. (pose proof (sec_facts n ltac:(clear -NB; lia) NPR) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ RS1 _ NSE _; nd_post).
    unfold K_HIGH_MEM in *. pose proof atop_range as AR8. clear -MAL RUP RUP8 RS1 NSE NMS N6 NB ML1 ML3 MCE MSAL AR8. Z.div_mod_to_equations. lia. }
  (nd_pre SHGEO 6%nat; intros SHE SHL SHP UBS SHLO SHHI; nd_post).
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof NUM as NUM0. (nd_pre NUM0 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof CP as CP0. (nd_pre CP0 7%nat; intros LN1 LN2 _ _ ND2 BSI _; nd_post).
  (* [comment removed for export] *)
  assert (CNT : enq_app st ch = None -> 0 < c_count (get_cls st K_BATCH_CLASS)) by (intros _; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NEWF EAF))))))))).
  assert (EAPP0 : enq_app st ch = None).
  { destruct (enq_app st ch) as [sx|] eqn:EAPP; [exfalso| reflexivity].
    assert (EA1 : enq_is_app st = true) by (apply (proj2 (enq_is_app_spec st ch)); eexists; exact EAPP). congruence. }
  assert (SB : a_qloc_bytes st2 = a_qloc_bytes st + ek_delta ek n /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st).
  { subst st2 ek. unfold st_enq, ek_of. rewrite EAPP0, EAF. cbn [ek_delta]. (pose proof (enq_new_core ch st) as ndP__; nd_pre ndP__ 7%nat; intros _ G1' G2' _ _ L2' _; nd_post).
    rewrite G1', G2', L2'. unfold ch. cbn [chunk_size]. unfold Q_BATCH_BYTES. repeat split; try reflexivity. clear; lia. }
  (nd_pre SB 3%nat; intros SB1 SB2 SB3; nd_post).
  assert (ED0 : 0 <= ek_delta ek n /\ ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; clear -NB; destruct (enq_is_app st); cbn [ek_delta]; lia).
  assert (EBK : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q) \/ (enq_is_app st = false /\ ek_b ek (qlast L (q_loc Q)) = abatch_addr L k24)).
  { subst ek. unfold ek_of. destruct (enq_is_app st) eqn:EAx; cbn [ek_b]; [left; reflexivity| right; split; reflexivity]. }
  assert (EBB : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
      \/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q))).
  { destruct EBK as [E|[EAx E]]; [left; exact E| right; exists k24]. (nd_pre (NEWF EAx) 5%nat; intros NK NBk KK NIB _; nd_post). split; [exact E|]. split; [exact KK| exact NIB]. }
  assert (HMSEP : forall kk, 0 <= kk < ndist st K_BATCH_CLASS -> UB - 16 + 24 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= UB - 16).
  { intros kk KK. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ _ _ _ PERC _; nd_post).
    (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros Q1 Q2 _; nd_post).
    (pose proof (slot_in_region L st K_BATCH_CLASS kk ltac:(rewrite size_of_class_24; lia) (proj1 Q1) KK) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 _; nd_post).
    rewrite size_of_class_24 in P4. subst UB. unfold abatch_addr, aregion, K_REGION, K_FREEARR_OFF, K_BATCH_CLASS in *.
    clear -P5 P4 Q1 Q2 RSP SC_r MSB. lia. }
  (nd_pre (read_dkS (AHSm DI AFK cs Q) L st X Q m RNG (UB - 16) ALO ARNG AR AQ HMSEP (ek_b ek (qlast L (q_loc Q))) (ek_delta ek n) ek
              (proj1 ED0) EBB ltac:(rewrite <- SB1, <- SB2; exact NOREC) eq_refl) 4%nat; intros _ _ GL GLST; nd_post).
  fold g in GL, GLST.
  chg (qlast L (q_loc Q)) lst. chg (ek_b ek lst) eb. chg (dk_glst g lst) gl. chg (shlen (rup n 8)) gq.
  (* [comment removed for export] *)
  assert (BGEO : forall q, In q (q_loc Q ++ q_glob Q) ->
      aregion L K_BATCH_CLASS <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
      /\ al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
  { intros q Hq. (pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
    rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
    generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  assert (A24 : c_allocated_user (get_cls st K_BATCH_CLASS) <= K_FREEARR_OFF).
  { (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros Q1 Q2 _; nd_post). lia. }
  assert (LSTF : lst = 0 \/ ((exists q, In q (q_loc Q) /\ lst = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= lst /\ lst + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104)).
  { subst lst. destruct (qlast_cases L (q_loc Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (GDR : g_drain g = (Q_CACHE <? a_qloc_bytes st + ek_delta ek n)) by reflexivity.
  assert (GLF : (g_drain g = false /\ gl = lst)
             \/ (g_drain g = true /\ gl = qlast L (q_glob Q)
                 /\ (gl = 0 \/ ((exists q, In q (q_glob Q) /\ gl = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104)))).
  { subst gl. rewrite GLST, GDR. destruct (Q_CACHE <? a_qloc_bytes st + ek_delta ek n); [right| left; split; reflexivity].
    split; [reflexivity|]. split; [reflexivity|].
    destruct (qlast_cases L (q_glob Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (EBF : eb = 0 \/ (aregion L K_BATCH_CLASS <= eb /\ eb + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104)).
  { subst eb. destruct EBK as [E|[EAx E]].
    - rewrite E. destruct LSTF as [Z0|(_ & FF)]; [left; exact Z0| right; exact FF].
    - right. rewrite E. (nd_pre (NEWF EAx) 4%nat; intros _ _ KK _; nd_post). (pose proof (slot_geo L st X K_BATCH_CLASS k24 ALO WF (K24) KK) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
      rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
      generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  (* [comment removed for export] *)
  (nd_pre PM 19%nat; intros id t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' sj' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MU WM MI' ST' IDR HDR' FC' SH' QC' EKP DKP STATS' LSJ' UW' FL' IAS' IAM' DEP'; nd_post).
  fold lst in MU, QC', EKP, DKP, EBK. fold eb in MU, EBK. fold gl in MU. fold gq in MU, SH'.
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  assert (ELST : lst = qlast L (q_loc Q)) by reflexivity. assert (EEB : eb = ek_b ek lst) by reflexivity.
  assert (EGL : gl = dk_glst g lst) by reflexivity. assert (EGQ : gq = shlen (rup n 8)) by reflexivity.
  clearbody lst eb gl gq.
  (* [comment removed for export] *)
  assert (EBNZ : 0x10007fff8000 <= eb) by (rewrite EEB; exact (ek_pre_b_hi _ _ _ _ _ _ _ _ EK)).   (* [comment removed for export] *)
  replace (eb + 8192) with (eb + qsz eb) in MU by (rewrite (qsz_pos eb) by (clear -EBNZ; lia); reflexivity).   (* [comment removed for export] *)
  assert (MUn : munch (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  clear MU.
  assert (KF : kfactsS (bv_unsigned sp) (al_t L) mb ms UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo lst eb gl).
  { unfold kfactsS. unfold K_HIGH_MEM in *.
    assert (GQ1 : 1 <= gq) by (clear -SHP EGQ; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP MLO ML1 ML3 MCE EUB UBS NB RUP SC_t SC_r SC_n SC_st SHE SHL SHLO SHHI GQ1 EGQ LSTF EBF GLF EBNZ. clear. intros.
    rewrite ?EGQ in SHL. unfold iclr, AIMG_LO, AIMG_HI in *.   (* [comment removed for export] *)
    (destruct LSTF as [Z0|(_ & FF)]; [rewrite (qsz_eq0 lst Z0) | rewrite (qsz_pos lst) by (atop_facts; lia)]);
    (destruct EBF as [Z1|FF1]; [exfalso; atop_facts; lia|]); rewrite (qsz_pos eb) by (atop_facts; lia); destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & FF2)])];
    sg_destr; repeat split; first [assumption | lia]. }
  pose proof (KS_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KS_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KS_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KS_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KS_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s) SC_c) as Kctx.
  pose proof (KS_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
  pose proof (KS_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
  pose proof (KS_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KS_objL _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as KobjL.      (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
  unfold adisj in D_l_t, D_l_r, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
  pose proof (KS_chunk _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kchunk.
  (* [comment removed for export] *)
  assert (SC : same_core st (st_after st2) /\ a_cinit (st_after st2) = a_cinit st /\ a_live (st_after st2) = a_live st /\ a_next (st_after st2) = a_next st
               /\ a_space_beg (st_after st2) = a_space_beg st /\ a_ptr_array (st_after st2) = a_ptr_array st
               /\ (enq_is_app st = true -> a_cls (st_after st2) = a_cls st)
               /\ (enq_is_app st = false -> a_cls (st_after st2) = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
  { pose proof (st_after_core st2) as [SC2 CL2'].
    assert (SC1 : same_core st st2 /\ (enq_is_app st = true -> a_cls st2 = a_cls st) /\ (enq_is_app st = false -> a_cls st2 = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
    { subst st2. unfold st_enq. destruct (enq_app st ch) as [sx|] eqn:EAPP.
      - (nd_pre (enq_app_Some st _ sx EAPP) 5%nat; intros l bl QL NFz ndR1__; nd_post; revert ndR1__; intros ->). split; [repeat split; intros; reflexivity|].
        split; [intros _; reflexivity|]. intros EAx. exfalso.
        assert (EA1 : enq_is_app st = true) by (apply (proj2 (enq_is_app_spec st ch)); eexists; exact EAPP).
        congruence.
      - (pose proof (enq_new_core ch st) as ndP__; nd_pre ndP__ 7%nat; intros C1 _ _ _ _ _ C7; nd_post). split; [exact C1|].
        split; [| intros _; exact C7]. intros EAx. exfalso.
        assert (EA1 : enq_is_app st = true) by exact EAx. destruct (proj1 (enq_is_app_spec st ch) EA1) as [s Hs]. congruence. }
    (nd_pre SC1 3%nat; intros SC1 CLa CLb; nd_post). pose proof (same_core_trans _ _ _ SC1 SC2) as SC3.
    pose proof SC3 as SC0. (nd_pre SC0 8%nat; intros F1 F2 F3 F4 F5 F6 F7 _; nd_post).
    split; [exact SC3|]. split; [exact F3|]. split; [exact F1|]. split; [exact F2|]. split; [exact F4|]. split; [exact F5|].
    split; [intros EAx; rewrite CL2'; exact (CLa EAx)| intros EAx; rewrite CL2'; exact (CLb EAx)]. }
  (nd_pre SC 8%nat; intros SC ECIN ELIVE ENEXT ESB EPA CLa CLb; nd_post).
  pose proof SC as SC0. (nd_pre SC0 12%nat; intros _ _ _ _ _ ENRES ENSEC GCo M24a M24b M24c M24d; nd_post).
  chg (st_after st2) st'.
  set (X' := xfreeS X (enq_is_app st) k24).
  assert (GC24 : get_cls st' K_BATCH_CLASS = (if enq_is_app st then get_cls st K_BATCH_CLASS else cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS))).
  { unfold get_cls at 1. destruct (enq_is_app st) eqn:EAx; [rewrite (CLa eq_refl); reflexivity| rewrite (CLb eq_refl), lookup_insert_eq; reflexivity]. }
  assert (GCo' : forall c', c' <> K_BATCH_CLASS -> get_cls st' c' = get_cls st c') by (intros c' NE; rewrite (GCo c' NE); reflexivity).
  assert (NDS : forall c', ndist st' c' = ndist st c').
  { intros c'. unfold ndist. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24b; reflexivity| rewrite (GCo' c' NE); reflexivity]. }
  assert (MC' : forall c', max_count st' c' = max_count st c') by (intros c'; unfold max_count; rewrite ECIN; reflexivity).
  (* [comment removed for export] *)
  assert (WF' : awf L st' X').
  { subst X'. unfold xfreeS. destruct (enq_is_app st) eqn:EAx.
    - exfalso. clear -EAF EAx. congruence.
    - (nd_pre (NEWF eq_refl) 8%nat; intros NK NBk KK NIB JKb FSH CIN POS; nd_post).
      apply (awf_xbatch L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK).
      + exact ESB. + exact EPA. + exact ECIN. + exact ELIVE. + exact ENEXT.
      + intros c' NE. rewrite (GCo' c' NE). reflexivity.
      + rewrite GC24. reflexivity. }
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    (first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |])] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]). apply Forall_nil. }
  assert (INST' : ainstance L st' m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | exact ENRES | exact ENSEC | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
  assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
  assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
  (* [comment removed for export] *)
  assert (THR' : athread L st' X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE].
      + destruct (CACHES K_BATCH_CLASS Hc') as [tail (CR & CHc & LCH)]. unfold acache_cells. cbv zeta.
        rewrite GC24, MC', ECIN. subst X'. rewrite xfreeS_cache, Z.eqb_refl, andb_true_r.
        replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR, CHc |- * by (unfold acache_addr, K_BATCH_CLASS; clear; lia).
        subst ek. unfold ek_of in EKP. destruct (enq_is_app st) eqn:EAx; cbn [ek_post negb] in EKP |- *.
        * (nd_pre EKP 5%nat; intros _ _ _ CR' _; nd_post). exists tail. split; [exact CR'|]. split; [| exact LCH].
          eapply u32arr_frame; [exact CHc | exact MUn | exact WM |]. rewrite length_app, length_map. apply Kt; clear -LCH; lia.
        * destruct EKP as (CR' & _). (nd_pre (NEWF eq_refl) 8%nat; intros NK NBk KK NIB JKb FSH CIN POS; nd_post).
          cbn [c_count cls_set_count]. exists (Z_to_bv 64 (acompact K_BATCH_CLASS k24) :: tail).
          pose proof (cache24_split L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK) as [CACHE LRL].
          split; [exact CR'|]. split.
          -- eapply u32arr_frame; [| exact MUn | exact WM |].
             ++ rewrite CACHE, map_app in CHc. cbn [map] in CHc. rewrite <- app_assoc in CHc. cbn [app] in CHc. exact CHc.
             ++ rewrite length_app, length_map. cbn [length].
                replace (length (removelast (xc_cache (x_cls X K_BATCH_CLASS))) + Datatypes.S (length tail))%nat with 16%nat
                  by (rewrite CACHE, length_app in LCH; cbn [length] in LCH; clear -LCH; lia).
                apply Kt; clear; lia.
          -- cbn [length]. rewrite CACHE, length_app in LCH. cbn [length] in LCH. clear -LCH. lia.
      + eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | rewrite (GCo' c' NE); reflexivity | exact ECIN | |].
        * subst X'. rewrite xfreeS_cache. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [E|_]; [exfalso; exact (NE E)|]. rewrite andb_false_r. reflexivity.
        * unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply Kt; clear -Hc' NE; lia.
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + eapply junk_frame; [exact (proj1 (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia))) | exact MUn | exact WM | intros _; apply Kt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia).
          assert (STJ' : exists w : word, rw_cells asegs m' (al_t L + 2784) [C8 w]).
          { subst ek. unfold ek_of in EKP. destruct (enq_is_app st); cbn [ek_post] in EKP.
            - (nd_pre EKP 5%nat; intros _ _ _ _ STS'; nd_post). exists stj. exact STS'.
            - (nd_pre EKP 3%nat; intros _ STS' _; nd_post). exact STS'. }
          destruct STJ' as [w STS']. pose proof (junk_of_cells m' _ _ STS') as J. cbn in J. exact J.
        * replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) by (clear; lia).
          eapply junk_frame; [| exact MUn | exact WM | intros _; apply Kt; clear; lia].
          pose proof (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ CSb].
          pose proof (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(clear; lia) ltac:(clear; lia)) as [_ CSc].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by (clear; lia). exact CSc.
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  (* [comment removed for export] *)
  assert (BDIS : forall q1 q2, In q1 (q_loc Q ++ q_glob Q) -> In q2 (q_loc Q ++ q_glob Q) ->
      abatch_addr L (qb_slot q1) = abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q1) + 8192 <= abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q2) + 8192 <= abatch_addr L (qb_slot q1)).
  { intros q1 q2 Hq1 Hq2. destruct (Z.eq_dec (qb_slot q1) (qb_slot q2)) as [E|NE]; [left; rewrite E; reflexivity| right].
    pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot q1) (qb_slot q2) ltac:(pose proof (bslot_range L st X Q WF CP q1 Hq1); lia)
                  ltac:(pose proof (bslot_range L st X Q WF CP q2 Hq2); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (KDIS : forall q, In q (q_loc Q ++ q_glob Q) -> enq_is_app st = false ->
      abatch_addr L k24 + 8192 <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= abatch_addr L k24).
  { intros q Hq EAx. (nd_pre (NEWF EAx) 5%nat; intros NK NBk KK NIB _; nd_post).
    assert (NE : k24 <> qb_slot q) by (intros ->; apply NIB; apply in_map; exact Hq).
    pose proof (slots_disjoint L K_BATCH_CLASS k24 (qb_slot q) ltac:(lia) ltac:(pose proof (bslot_range L st X Q WF CP q Hq); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L st' m' c'' /\ afreearray L st' X' m' c'' /\ aslots L st' X' m' c'' /\ aslot_shadow L st' X' m' c'').
  { intros c'' Hc''. (nd_pre (CLS c'' Hc'') 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC1 : c_num_freed (get_cls st' c'') = c_num_freed (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24c| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC3 : c_allocated_user (get_cls st' c'') = c_allocated_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24b| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 4%nat; intros RI1 RI2 RI3 RI4; nd_post).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | exact EC1 | exact EC2 | exact EC3 | exact EC4 |].
      unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      apply Kres; try (clear -Hc'' RSP; lia).
      + destruct LSTF as [Z0|(_ & F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + destruct EBF as [Z0|(F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + assert (GLR : gl = 0 \/ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)).
        { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; exact F2].
          destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; exact F2]. }
        destruct GLR as [Z0|F2]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | exact EC1 | exact EC2 | | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + subst X'. apply xfreeS_free.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia | | |].
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          pose proof (farr_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2) as D. clear -D. lia.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, AIMG_HI, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
          rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) (afreearr L c'') ltac:(clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D RI2 RI3 FA2; lia| exact AM] | clear; lia].
    - (* [comment removed for export] *)
      eapply (aslots_update_gen L _ m m' MUn WM st st' X X' c''); [exact SLOTS | apply NDS | exact EC3 | exact EC4 | |].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D2 : (enq_is_app st = false /\ c'' = K_BATCH_CLASS /\ k'' = k24) \/ (enq_is_app st = true \/ c'' <> K_BATCH_CLASS \/ k'' <> k24))
          by (clear; destruct (enq_is_app st); lia).
        destruct D2 as [(EAx & E24 & EK24)|NE2].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X'. rewrite (busy_of_xfreeS X (enq_is_app st) k24 K_BATCH_CLASS k24), EAx. cbn [negb andb]. rewrite !Z.eqb_refl. cbn [andb].
          unfold aslot_busy, bbatch. cbn [xb_st xb_class xb_slot]. unfold xb_alloc. cbn [xb_class xb_slot]. rewrite size_of_class_24.
          subst ek. unfold ek_of in EKP. rewrite EAx in EKP. cbn [ek_post] in EKP. (nd_pre EKP 6%nat; intros _ _ BC BA [bsb BJ] _; nd_post).
          fold (abatch_addr L k24) in BC, BA, BJ |- *. change (aslot_addr L K_BATCH_CLASS k24) with (abatch_addr L k24).
          replace 8192 with (24 + (8 * Z.of_nat (length [Z_to_bv 64 (UB - 16)]) + (8192 - 24 - 8 * 1))) by (cbn; lia).
          apply junk_merge; [| | clear; lia| cbn; clear; lia].
          -- pose proof (junk_of_cells m' _ _ BC) as J. cbn in J. exact J.
          -- apply junk_merge; [apply junk_of_u64arr; exact BA | | cbn; clear; lia | clear; lia].
             cbn [length Z.of_nat Pos.of_succ_nat]. eexists. exact BJ.
        * assert (T1 : negb (enq_is_app st) && (K_BATCH_CLASS =? c'') && (k24 =? k'') = false).
          { destruct (enq_is_app st); cbn [negb andb]; [reflexivity|].
            destruct (Z.eqb_spec K_BATCH_CLASS c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k24 k'') as [E'|]; [| reflexivity]. exfalso.
            destruct NE2 as [NE|[NE|NE]]; [discriminate| apply NE; symmetry; exact E| apply NE; symmetry; exact E']. }
          assert (BX : busy_of X' c'' k'' = busy_of X c'' k'').
          { subst X'. rewrite (busy_of_xfreeS X (enq_is_app st) k24 c'' k''), T1. reflexivity. }
          (* [comment removed for export] *)
          assert (BQ : forall q, In q (q_loc Q ++ q_glob Q) -> c'' = K_BATCH_CLASS -> aslot_addr L c'' k'' = abatch_addr L (qb_slot q) ->
              exists yq, busy_of X c'' k'' = Some yq /\ xb_st yq = BBatch /\ xb_class yq = K_BATCH_CLASS /\ xb_slot yq = k''
                         /\ junk_at m (abatch_addr L (qb_slot q)) 8192 /\ k'' = qb_slot q).
          { intros q Hq -> EQA. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
            assert (EK' : k'' = qb_slot q) by (unfold abatch_addr, aslot_addr in EQA; rewrite size_of_class_24 in EQA; clear -EQA; lia). subst k''.
            exists yq. pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq in BY.
            split; [exact BY|]. split; [exact Syq|]. split; [exact Cyq|]. split; [exact Kyq|]. split; [| reflexivity].
            destruct SLOTS as [SLK _]. specialize (SLK (qb_slot q) Hk''). rewrite BY in SLK. unfold aslot_busy in SLK. rewrite Syq in SLK.
            unfold xb_alloc in SLK. rewrite Cyq, Kyq, size_of_class_24 in SLK. exact SLK. }
          assert (D3 : (c'' = K_BATCH_CLASS /\ lst <> 0 /\ aslot_addr L c'' k'' = lst) \/ (c'' <> K_BATCH_CLASS \/ lst = 0 \/ aslot_addr L c'' k'' <> lst)) by (clear; lia).
          destruct D3 as [(E24 & LNZ & EL)|NE3].
          -- (* [comment removed for export] *)
             right. rewrite BX. destruct LSTF as [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)]; [exfalso; exact (LNZ Z0)|].
             (nd_pre (BQ q ltac:(apply in_or_app; left; exact Hq) E24 ltac:(rewrite EL; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
             rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EL.
             assert (QNE : a_qloc st <> []) by (intros QL0; apply LNZ; rewrite ELST; replace (q_loc Q) with (@nil qbatchc) by (clear -QL0 LN1; destruct (q_loc Q); [reflexivity| rewrite QL0 in LN1; cbn in LN1; discriminate]); reflexivity).
             subst ek. unfold ek_of in EKP, EK. destruct (enq_is_app st) eqn:EAx; cbn [ek_post ek_pre] in EKP, EK.
             ** (nd_pre EKP 4%nat; intros LB' LA' [bs LJ'] _; nd_post). (nd_pre EK 9%nat; intros _ _ CNT' _ _ _ _ LEN _; nd_post).
                rewrite ELST in LB', LA', LJ' |- *.
                set (cnt := b_count (List.last (a_qloc st) dummy_batch)) in *.
                replace 8192 with (24 + (8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))) ++ [Z_to_bv 64 (UB - 16)])) + (8192 - 24 - 8 * (cnt + 1))))
                  by (rewrite length_app, LEN; cbn [length]; clear -CNT'; lia).
                apply junk_merge; [| | clear; lia| rewrite length_app, LEN; cbn [length]; clear -CNT'; lia].
                +++ pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
                +++ apply junk_merge; [apply junk_of_u64arr; exact LA' | | rewrite length_app, LEN; cbn [length]; clear -CNT'; lia | clear -CNT'; lia].
                    rewrite length_app, LEN. cbn [length]. replace (8 * Z.of_nat (Z.to_nat cnt + 1)) with (8 * (cnt + 1)) by (clear -CNT'; lia). eexists. exact LJ'.
             ** destruct (a_qloc st) as [|b0 bs0] eqn:QL0; [exfalso; exact (QNE eq_refl)|]. rewrite <- QL0 in *.
                (nd_pre EKP 6%nat; intros _ _ _ _ _ [LB' LA']; nd_post). destruct EK as ((_ & _ & _ & _ & _ & _ & _ & LEN0 & _) & _).
                rewrite ELST in LB', LA' |- *.
                replace 8192 with (24 + 8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))))))
                  by (rewrite LEN0; clear; lia).
                apply junk_merge; [| apply junk_of_u64arr; exact LA' | clear; lia| rewrite LEN0; clear; lia].
                pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
          -- assert (D4 : (g_drain g = true /\ c'' = K_BATCH_CLASS /\ gl <> 0 /\ aslot_addr L c'' k'' = gl /\ gl <> lst)
                        \/ (g_drain g = false \/ c'' <> K_BATCH_CLASS \/ gl = 0 \/ aslot_addr L c'' k'' <> gl \/ gl = lst)) by (destruct (g_drain g); clear; lia).
             destruct D4 as [(GD & E24 & GNZ & EG & GNL)|NE4].
             ** (* [comment removed for export] *)
                right. rewrite BX. destruct GLF as [[GD' _]|(_ & GQL & [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)])]; [congruence| exfalso; exact (GNZ Z0)|].
                (nd_pre (BQ q ltac:(apply in_or_app; right; exact Hq) E24 ltac:(rewrite EG; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
                rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EG.
                assert (GNE : a_qglob st <> []) by (intros QG0; clear -QG0 Hq LN2; destruct (q_glob Q) eqn:QQ0; [destruct Hq| rewrite QG0 in LN2; cbn in LN2; discriminate]).
                unfold dk_post in DKP. rewrite GD in DKP. (nd_pre DKP 3%nat; intros _ _ GLN; nd_post).
                assert (GF : g_full g = true) by (subst g; unfold g_of; cbn [g_full]; clear -GNE; destruct (a_qglob st); [exfalso; exact (GNE eq_refl)| reflexivity]).
                rewrite GF, GL, <- GQL in GLN.
                replace 8192 with (8 + 8184) by (clear; lia). apply junk_merge; [| | clear; lia | clear; lia].
                +++ pose proof (junk_of_cells m' _ _ GLN) as J. cbn in J. exact J.
                +++ rewrite <- Eq in JQ. destruct (junk_split m gl 8 8184 JQ ltac:(clear; lia) ltac:(clear; lia)) as [_ J2].
                    eapply junk_frame; [exact J2 | exact MUn | exact WM |]. intros _.
                    assert (DL : lst = 0 \/ lst + 8192 <= gl \/ gl + 8192 <= lst).
                    { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql, Eq.
                      destruct (BDIS ql q ltac:(apply in_or_app; left; exact Hql) ltac:(apply in_or_app; right; exact Hq)) as [E|E]; [| exact E].
                      exfalso. apply GNL. rewrite Eq, Eql. symmetry. exact E. }
                    assert (DE : eb = lst \/ eb + 8192 <= gl \/ gl + 8192 <= eb).
                    { destruct EBK as [E|[EAx E]]; [left; exact E| right]. rewrite E, Eq. exact (KDIS q ltac:(apply in_or_app; right; exact Hq) EAx). }
                    apply Kres; clear -F3 F4 RES RHI GNZ DL DE; lia.
             ** (* [comment removed for export] *)
                left. split; [exact BX|]. split.
                +++ assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> (c'' <> K_BATCH_CLASS \/ aslot_addr L c'' k'' <> abatch_addr L (qb_slot q)) ->
                        aslot_addr L c'' k'' + size_of_class c'' <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= aslot_addr L c'' k'').
                    { intros q Hq NE. pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS (qb_slot q) ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk''
                                    (bslot_range L st X Q WF CP q Hq) ltac:(destruct NE as [NE|NE]; [left; exact NE| destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NC']; [right| left; exact NC']];
                                                                                 intros EKK; apply NE; rewrite EKK; reflexivity)) as D.
                      rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                    assert (DW13 : lst = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= lst \/ lst + 8192 <= aslot_addr L c'' k'').
                    { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql. apply DQ; [apply in_or_app; left; exact Hql|].
                      destruct NE3 as [NE|[Z0|NE]]; [left; exact NE| exfalso| right; rewrite <- Eql; exact NE].
                      rewrite Eql in Z0. (nd_pre (BGEO ql ltac:(apply in_or_app; left; exact Hql)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                    assert (DW14 : eb = lst \/ aslot_addr L c'' k'' + size_of_class c'' <= eb \/ eb + 8192 <= aslot_addr L c'' k'').
                    { destruct EBK as [E|[EAx E]]; [left; exact E| right]. rewrite E. (nd_pre (NEWF EAx) 4%nat; intros _ _ KK _; nd_post).
                      pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS k24 ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk'' KK
                                    ltac:(destruct NE2 as [NE|[NE|NE]]; [rewrite EAx in NE; discriminate| left; exact NE| right; exact NE])) as D.
                      rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                    assert (DW15 : gl = lst \/ gl = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= gl \/ gl + 8192 <= aslot_addr L c'' k'').
                    { destruct GLF as [[_ E]|(GD & GQL & [Z0|((q & Hq & Eq) & _)])]; [left; exact E| right; left; exact Z0| right; right].
                      rewrite Eq. apply DQ; [apply in_or_app; right; exact Hq|].
                      destruct NE4 as [NE|[NE|[NE|[NE|NE]]]]; [congruence| left; exact NE| | right; rewrite <- Eq; exact NE| ].
                      - exfalso. rewrite Eq in NE. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -NE B3 RES RHI. lia.
                      - rewrite NE in *. destruct NE3 as [NE'|[Z0|NE']]; [left; exact NE'| exfalso| right; rewrite <- Eq; exact NE'].
                        rewrite Eq in Z0. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                    apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia
                                | clear -DW13 P5 RSP RES RHI; lia | clear -DW14 DW13 P5 RSP RES RHI; lia | clear -DW15 DW13 P5 RSP RES RHI; lia].
                +++ intros b Hb. (nd_pre (busy_of_Some_facts X c'' k'' b Hb) 3%nat; intros IB CB' KB'; nd_post). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U2 : c'' = K_BATCH_CLASS -> aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia | | |].
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 _ F1 F2 A24 U2 U0 U0').
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 _ F1 F2 A24 U2 U0 U0').
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          pose proof (undist_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 _ F1 F2 A24 U2 U0 U0') as D. clear -D. lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update_gen L _ m m' MUn WM st st' X X' c''); [exact SHADOW | apply NDS | exact EC3 | exact EC4 | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk''. left.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        split.
        -- subst X'. rewrite (busy_of_xfreeS X (enq_is_app st) k24 c'' k'').
           destruct (negb (enq_is_app st) && (K_BATCH_CLASS =? c'') && (k24 =? k'')) eqn:T1; [| reflexivity].
           destruct (enq_is_app st) eqn:EAx; [cbn in T1; discriminate|]. cbn [negb andb] in T1.
           destruct (Z.eqb_spec K_BATCH_CLASS c'') as [<-|]; [| discriminate]. destruct (Z.eqb_spec k24 k'') as [<-|]; [| discriminate].
           (nd_pre (NEWF eq_refl) 3%nat; intros _ NBk _; nd_post). rewrite NBk. rewrite size_of_class_24. rewrite slot_shadow_bbatch by (clear; change (shlen 8192) with 1024; lia).
           reflexivity.
        -- pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
           apply Kshad.
           ++ rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
           ++ rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
           ++ apply shlen_nonneg. clear -T16; lia.
           ++ rewrite SHE. destruct SC_r as [D|D].
              ** right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
                 pose proof (shad_mono (al_res L) (aslot_addr L c'' k'') ltac:(clear -P5 RSP; lia)) as MM. clear -HH MM SHL. lia.
              ** left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D P6 RI3; unfold K_SPACE_SIZE in *; lia| clear -AL''; Z.div_mod_to_equations; lia] | clear; lia].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) AU ltac:(clear -U0 RI4; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D U0' RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia].
  }
  (* [comment removed for export] *)
  assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st' m' c'').
  { intros c'' Hc''. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post).
    eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | exact EC4 | exact EC2 | |].
    - intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
      assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
      destruct U0 as [U0 U0'].
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) AU ltac:(clear -U0 RI1; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D U0' RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) AU ltac:(clear -FA1 RI1; unfold K_FREEARR_OFF in *; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D FA2 RI2 RI3; unfold K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia]. }
  (* [comment removed for export] *)
  assert (PD : Permutation (sec_chunks_of st') cs).
  { eapply Permutation_trans; [| apply Permutation_sym; exact PCS]. apply (sec_chunks_of_quar_sec st st' mb ms n ELIVE). exact (st_after_enq_qfilt_sec st ch eq_refl). }
  assert (NOTL' : ~ sec_live st' ch) by (unfold sec_live; rewrite ELIVE; exact NOTL).
  assert (LVE : forall j c, nth_error order j = Some c -> j <> i -> (sec_live st' c <-> sec_live st c)) by (intros; unfold sec_live; rewrite ELIVE; reflexivity).
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p.
  pose proof (ao_ptr L ALO) as OP. (pose proof (aobj_int _ _ OP ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OPi OPa [kP OPs]; nd_post). unfold adisj, aobj in D_t_p, D_p_r, D_n_p, D_s_p, OP.   (* [comment removed for export] *)
  assert (HS' : ASEC_of L st' X' m').
  { unfold ASEC_of, ASECc.
    pose proof HS as HS1. (nd_pre HS1 5%nat; intros _ _ _ _ SHZ0; nd_post).
    split; [| split; [| split; [| split]]].
    - (* [comment removed for export] *) unfold asec_wf. rewrite EPA, WP, ENRES, ENSEC.
      split; [exact ALO|]. split; [reflexivity|]. split; [exact WR|]. split; [rewrite (Permutation_length PD); exact WL|]. split; [exact WB|].
      split; [rewrite Forall_forall in WF1 |- *; intros c Hc; apply WF1; eapply Permutation_in; [exact PD| exact Hc]|].
      eapply sec_disjoint_perm; [apply Permutation_sym; exact PD| exact WD].
    - (* [comment removed for export] *) exists order. rewrite ?ENRES, ?ENSEC.
      split; [eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]|].
      unfold K_HIGH_MEM in *.
      split; [| split].
      + eapply u64arr_frame; [exact U64| exact MUn| exact WM|]. rewrite length_map, LENO.
        apply Kobj; [clear -OP OPi OPs WB WR LENO; lia| clear -OP OPi OPs WB WR; lia| clear -WB; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
      + eapply junk_frame; [exact JK| exact MUn| exact WM|]. intros POS.
        apply Kobj; [clear -OP OPi OPs WB WR POS; lia| clear -OP OPi OPs WB WR; lia| clear -WB POS; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
      + intros j c Hj. destruct (Nat.eq_dec j i) as [->|NEji].
        * (* [comment removed for export] *)
          rewrite NTH in Hj. injection Hj as <-. exists false. split; [split; [discriminate| intros Hl; exfalso; exact (NOTL' Hl)]|].
          unfold ch. cbn [asec_chunk]. pose proof CH as CH0. cbn [asec_chunk] in CH0.
          pose proof CH as CH1. unfold ch in CH1. cbn [asec_chunk] in CH1. (nd_pre CH1 5%nat; intros G1 G2 G3 G4 _; nd_post). unfold SEC_UOFF in G1, G2, G3, G4 |- *. rewrite <- ?EUB in *.
          replace (UB - 16 + 16) with UB in FC' by (clear; lia).
          split; [eapply cells_frame; [exact G1| exact MUn| exact WM| cbn; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply junk_frame; [exact G2| exact MUn| exact WM| intros _; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply cells_frame; [exact G3| exact MUn| exact WM| cbn; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply junk_frame; [exact G4| exact MUn| exact WM| intros _; apply Kchunk; clear -EUB MSB; lia]|].
          split; [exists b1, ctx; split; [exact HDR'| split; [exact B1| split; [exact B13| exact CTX]]]|].
          split. { replace (ms - 6144) with (8 + (ms - 6144 - 8)) by (clear; lia). apply junk_merge; [| | clear; lia| clear -NMS N6 NB; lia].
                   - pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
                   - eapply junk_frame; [| exact MUn| exact WM| intros POS; apply Kchunk; clear -EUB MSB POS; lia].
                     exact UJ. }
          split; [eapply fill_frame; [exact S1| exact MUn| exact WM| intros _; apply Kshad; clear -SHLO SHHI SHE MSB; unfold AIMG_HI; Z.div_mod_to_equations; lia]|].
          rewrite (granules_rup n) by (clear -NB; lia). rewrite <- EGQ. unfold sec_user_shadow.
          split; [rewrite (granules_rup n) by (clear -NB; lia); rewrite <- EGQ; exact SH'|].
          eapply fill_frame; [exact S3| exact MUn| exact WM| intros POS; apply Kshad; clear -SHLO SHHI SHE SHL SHP POS MSB; unfold AIMG_HI; Z.div_mod_to_equations; lia].
        * (* [comment removed for export] *)
          (nd_pre (PER j c Hj) 3%nat; intros lvj LVj CHj; nd_post). exists lvj. split; [rewrite (LVE j c Hj NEji); exact LVj|].
          assert (INj : In c order) by (eapply nth_error_In; exact Hj).
          pose proof (proj1 (Forall_forall _ _) WF1o c INj) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
          (nd_pre (sec_wf1_facts' L mb' ms' n' Wc) 12%nat; intros JAL JLO JCE _ _ _ JMSB _ _ _ (JC_t & _ & JC_r & _ & JC_n & JC_st & _) _; nd_post).
          assert (NEc : CSec mb' ms' n' <> ch).
          { intros E. apply NEji. destruct WDo as [ND _]. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
          destruct WDo as [_ DJ].
          destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
          all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
          all: unfold K_HIGH_MEM in JLO, JCE.
          all: (pose proof (ablk_lin _ _ JLO) as ndP__; nd_pre ndP__ 4%nat; intros JL1 JL2 JL3 JL4; nd_post); unfold AIMG_HI in JL1; (pose proof (ablk_int _ _ JLO) as ndP__; nd_pre ndP__ 6%nat; intros kJ KAJ KBJ KEJ KCJ KDJ; nd_post).   (* [comment removed for export] *)
          all: eapply asec_chunk_frameD'; [exact MUn| exact Wc| | | | exists (Z.of_nat j); exact CHj].
          all: try (intros Ad kk Z1 Z2 Z3; apply Kobj; [clear -Z1 Z3 JLO JL1 KAJ KBJ KEJ KCJ KDJ; lia| clear -Z3 JCE; lia| clear -Z2; lia| clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_r; lia| clear -Z1 Z3 JC_n; lia| clear -Z1 Z3 JC_st; lia| clear -Z1 Z3 Dc; lia]).
          all: try (pose proof CHj as CH1; cbn [asec_chunk] in CH1; destruct CH1 as (Hh & _);
                    eapply cells_frame; [exact Hh| exact MUn| exact WM| cbn; apply Kobj; [clear -JLO JL1 JMSB KAJ KBJ KEJ KCJ KDJ; lia| clear -JCE JMSB; lia| clear; lia| clear -JC_t JMSB; lia| clear -JC_r JMSB; lia| clear -JC_n JMSB; lia| clear -JC_st JMSB; lia| clear -Dc JMSB; lia]]).
          -- intros Ad kk Z1 Z2 Z3. apply Kshad; [rewrite shad_div in Z1; unfold ASHOFF, AIMG_HI in *; clear -Z1 JLO JL1; Z.div_mod_to_equations; lia| rewrite shad_div in Z3; unfold ASHOFF in *; clear -Z3 JCE JAL8; Z.div_mod_to_equations; lia| clear -Z2; lia|].
             left. rewrite SHE. pose proof (shad_sep _ _ _ Dc JAL8) as HH. rewrite shlen_div in HH. clear -HH Z3. lia.
          -- intros Ad kk Z1 Z2 Z3. apply Kshad; [rewrite shad_div in Z1; unfold ASHOFF, AIMG_HI in *; clear -Z1 JLO JL1; Z.div_mod_to_equations; lia| rewrite shad_div in Z3; unfold ASHOFF in *; clear -Z3 JCE JAL8; Z.div_mod_to_equations; lia| clear -Z2; lia|].
             right. rewrite SHE. pose proof (shad_sep _ _ _ Dc MAL8) as HH. rewrite shlen_div in HH. clear -HH Z1 SHL. lia.
    - (* [comment removed for export] *) (nd_pre SINST 6%nat; intros I1 [srt I2] I3 I4 I5 I6; nd_post). unfold asec_inst. unfold AINSTANCE in *.
      split; [eapply cells_frame; [exact I1| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [exists srt; eapply cells_frame; [exact I2| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply junk_frame; [exact I3| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply junk_frame; [exact I4| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply cells_frame; [exact I5| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      eapply junk_frame; [exact I6| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia].
    - (* [comment removed for export] *) unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MUn| exact WM|]. intros POS.
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -RSP RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP2. unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *. Z.div_mod_to_equations. lia.
      + clear -POS; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) (al_space_beg L) ltac:(clear -RSP; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D SP2 RSP; unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia| clear -SP3; unfold K_ALIGN in SP3; Z.div_mod_to_equations; lia] | clear; lia].
    - (* [comment removed for export] *) intros x Hx HFh HC.
      assert (HC0 : Forall (fun c => ~ (sec_mb c <= x < sec_mb c + sec_ms c)) cs).
      { rewrite Forall_forall in HC |- *. intros c Hin. apply HC. eapply Permutation_in; [apply Permutation_sym; exact PD| exact Hin]. }
      pose proof INcs as INst.
      pose proof (proj1 (Forall_forall _ _) HC0 ch INst) as NX. unfold ch in NX. cbn [sec_mb sec_ms] in NX.
      unfold K_HIGH_MEM, AIMG_HI, KLS in Hx.   (* [comment removed for export] *)
      assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM in *; clear -Hx; Z.div_mod_to_equations; lia).
      rewrite <- (SHZ0 x ltac:(unfold K_HIGH_MEM; exact Hx) HFh HC0). apply MUn. rewrite wa_unsigned by exact SX.
      eapply (disjoint_outside _ (shad x) 1); [| clear; lia]. apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -Hx; Z.div_mod_to_equations; lia| rewrite shad_div; unfold ASHOFF; pose proof atop_range as AR8; clear -Hx AR8; Z.div_mod_to_equations; lia| clear; lia|].
      rewrite SHE. destruct (Z_lt_le_dec x mb) as [LT|GE].
      + left. rewrite !shad_div. clear -LT MAL8. Z.div_mod_to_equations. lia.
      + right. rewrite !shad_div in *. clear -GE NX SHL MAL8 MSAL. Z.div_mod_to_equations. lia. }
  assert (BL' : ablocks L st' X' LB).
  { eapply ablocks_mono; [exact BL| intros y q Hy _; subst X'; apply In_xfreeS; exact Hy| intros q mb' ms' n' Hl; rewrite ELIVE; exact Hl]. }
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi FKa [kF FBND]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (SHB : 2148238848 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SHE SHL; lia).   (* [comment removed for export] *)
  assert (HFK' : AFK L LB m').
  { eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |].
    - pose proof (ao_dtls L ALO) as DTO. (pose proof (aobj4_int _ DTO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DBND] [jD DIMG]; nd_post). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE, K_HIGH_MEM in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148238848 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
        rewrite SHE. destruct SC_f as [D|D].
        - right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH. clear -HH SHL. lia.
        - left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [exact D| clear -FKO FKi FBND; Z.div_mod_to_equations; lia] | clear; lia]. }
      (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      assert (LSTR : (lst = 0 /\ qsz lst = 8) \/ (al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104 /\ qsz lst = 8192))   (* [comment removed for export] *)
        by (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; split; [exact Z0| apply qsz_eq0; exact Z0]| right; split; [exact F3| split; [exact F4| apply qsz_pos; clear -F3 RES RHI; lia]]]).
      assert (EBR : al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104 /\ qsz eb = 8192) by (destruct EBF as [Z0|(_ & _ & F3 & F4)]; [exfalso; clear -Z0 EBNZ; lia| split; [assumption| split; [assumption| apply qsz_pos; clear -EBNZ; lia]]]).   (* [comment removed for export] *)
      assert (GLRR : gl = lst \/ gl = 0 \/ (al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104))
        by (destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])]; [left; exact Z2| right; left; exact Z2| right; right; split; assumption]).
      (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | idtac]]]]]]]]]]]]]]]]).
      apply Forall_nil. }
  assert (QH : qhdr L ch 0 = UB - 16) by (unfold ch; cbn [qhdr]; unfold PG; rewrite RZ, EUB; clear; lia).
  (* [comment removed for export] *)
  assert (GNB : g_nb g = Z.of_nat (length (a_qglob st))) by reflexivity.
  assert (GFST : g_fst g = qfirst L (q_glob Q)) by reflexivity.
  assert (GQB : g_qb g = a_qglob_bytes st) by reflexivity.
  assert (GFU : g_full g = match a_qglob st with [] => false | _ :: _ => true end) by reflexivity.
  destruct DKP as [MX' DKP'].
  (pose proof (qnum_freeR st ch NUM ltac:(unfold ch; cbn [chunk_size]; clear -NB; lia) NOREC) as ndP__; nd_pre ndP__ 5%nat; intros NUM' NB2a NB2b NB2c NF2; nd_post).
  fold st2 st' in NUM', NB2a, NB2b, NB2c, NF2.
  pose proof (st_after_q st2) as [DRN NDR]. fold st' in DRN, NDR.
  assert (QK' : aquar_glob_const m').
  { split; [| exact MX']. eapply cells_frame; [exact QK | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia. }
  assert (IA' : aintal true m').
  { split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. revert Hj. clear. unfold AIA_MAP1_LEN. intros Hj. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (BLST : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst ->
      abatch_addr L (qb_slot q) + 8192 <= lst \/ lst + 8192 <= abatch_addr L (qb_slot q) \/ lst = 0).
  { intros q Hq NE. destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [right; right; exact Z0|].
    destruct (BDIS q ql Hq ltac:(apply in_or_app; left; exact Hql)) as [E|E]; [exfalso; apply NE; rewrite Eql; exact E| rewrite Eql].
    destruct E as [E|E]; [left; exact E| right; left; exact E]. }
  assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst -> abatch_addr L (qb_slot q) <> gl ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (abatch_addr L (qb_slot q)) 8192).
  { intros q Hq NL NG. (nd_pre (BGEO q Hq) 4%nat; intros _ _ F3 F4; nd_post). pose proof (BLST q Hq NL) as DL.
    assert (DE : eb = lst \/ abatch_addr L (qb_slot q) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot q)).
    { destruct EBK as [E|[EA E]]; [left; exact E| right]. rewrite E.
      destruct (KDIS q Hq EA) as [D|D]; [right; exact D| left; exact D]. }
    assert (DG : gl = lst \/ gl = 0 \/ abatch_addr L (qb_slot q) + 8192 <= gl \/ gl + 8192 <= abatch_addr L (qb_slot q)).
    { destruct GLF as [[_ E]|(_ & _ & [Z0|((qg & Hqg & Eqg) & _)])]; [left; exact E| right; left; exact Z0| right; right].
      destruct (BDIS q qg Hq ltac:(apply in_or_app; right; exact Hqg)) as [E|E]; [exfalso; apply NG; rewrite Eqg; exact E| rewrite Eqg; exact E]. }
    apply Kres; clear -F3 F4 RES RHI DL DE DG; lia. }
  assert (HQ' : AQUAR L st' X' m').
  { subst ek. unfold ek_of in EKP, EK, QC', DKP', EEB, SB1, GDR, GL, GLST.
    destruct (enq_is_app st) eqn:EA; cbn [ek_nb ek_fst ek_lst ek_delta ek_b ek_post ek_pre] in EKP, EK, QC', DKP', EEB, SB1, GDR, GL, GLST.
    - (* [comment removed for export] *)
      (nd_pre EKP 4%nat; intros LB' LA' [bs LJ'] _; nd_post). (nd_pre EK 9%nat; intros _ _ CNT' _ _ _ _ LEN _; nd_post).
      (* [comment removed for export] *)
      pose proof EA as EA0. unfold enq_is_app in EA0. destruct (rev (a_qloc st)) as [|blr rl] eqn:RV; [discriminate|].
      assert (QL : a_qloc st = rev rl ++ [blr]) by (rewrite <- (rev_involutive (a_qloc st)), RV; reflexivity).
      destruct (Z.eqb_spec (b_count blr) Q_BATCH) as [|NFULL]; [discriminate|]. clear EA0.
      set (l := rev rl) in *. set (bl := blr) in *.
      assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL, length_app; cbn; clear; lia).
      assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; clear -LQ; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
      set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
      assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
      assert (LST : List.last (a_qloc st) dummy_batch = bl) by (rewrite QL; apply last_app1). rewrite LST in *.
      assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
      set (bl' := mkABatch (b_count bl + 1) (b_size bl + n) (ch :: b_chunks bl)) in *.
      set (qz' := mkQB (qb_slot qz) (0 :: qb_ks qz)) in *.
      assert (EAPP : enq_app st ch = Some (set_qloc (l ++ [bl']) (a_qloc_bytes st + n) st)).
      { unfold enq_app. rewrite RV. fold bl. replace (b_count bl =? Q_BATCH) with false by (symmetry; apply Z.eqb_neq; exact NFULL).
        subst bl'. reflexivity. }
      assert (Q2 : a_qloc st2 = l ++ [bl'] /\ a_qloc_bytes st2 = a_qloc_bytes st + n /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. cbn. repeat split; reflexivity. }
      (nd_pre Q2 4%nat; intros QL2 QB2 QG2 QGB2; nd_post).
      (* [comment removed for export] *)
      unfold abatches in ABL, ABG. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
      cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
      assert (ABl' : abatches_to L m' l ql (hd 0 (qaddrs L [qz']))).
      { cbn [qaddrs map hd qz' qb_slot]. cbn [qaddrs map hd] in ABl. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
        intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
        assert (NEq : abatch_addr L (qb_slot q) <> lst).
        { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post).
          apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
          unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
        apply BFR; [exact INq | exact NEq |].
        destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post); clear -F3 RES RHI; lia|].
        rewrite Eqg. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post). apply in_split in Hqg. (nd_pre Hqg 3%nat; intros gs1 gs2 EQg; nd_post).
        apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
        pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
        unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      assert (ABz' : abatch_cells L m' bl' qz' 0).
      { unfold abatch_cells. cbv zeta. cbn [qb_slot qb_ks b_size b_count b_chunks bl' qz']. rewrite <- QLST. rewrite qhdrs_cons, map_app. cbn [map qhdr]. rewrite QH.
        split; [exact LB'|]. split; [exact LA'|]. split; [| split; [cbn [length]; rewrite Z4; clear; lia| split; [cbn [length]; rewrite Z5; reflexivity| unfold Q_BATCH in *; clear -CNT' Z6; lia]]].
        exists bs. unfold Q_BATCH_BYTES. exact LJ'. }
      assert (ABL' : abatches_to L m' (l ++ [bl']) (ql ++ [qz']) 0).
      { apply abatches_to_app; [exact LNl|]. split; [exact ABl'|]. cbn. split; [exact ABz'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (ql ++ [qz']) (q_glob Q) true (q_pend Q))).
      { subst X'. unfold xfreeS. apply (qcoupled_app_sec L st X Q mb ms n CP st2 l bl ql qz true 0 QL QQ QL2 QG2). }
      subst qz'.
      destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [DR|NDRN].
      + (* [comment removed for export] *)
        (nd_pre (DRN DR) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        destruct DKP' as [GC' GLN].
        exists (mkQConc [] (q_glob Q ++ (ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}])) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length].
             replace (Z.of_nat (length l + 1)) with (Z.of_nat (length (a_qloc st))) by (rewrite QL, length_app; cbn; reflexivity).
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite qlast_reslot, <- QQ, <- ELST.
             assert (FE : qfirst L (q_glob Q ++ ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}]) = (if g_full g then g_fst g else qfirst L (q_loc Q))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). cbn [app]. rewrite qfirst_reslot, <- QQ. reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite qfirst_reslot, <- QQ.
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; clear -LQg; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
                   set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
                   set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
                   assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
                   rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
                   cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
                   assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
                   rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
                   rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
                   +++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
                       intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQg; apply in_or_app; left; exact Hq).
                       assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
                       { intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                         apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       apply BFR; [exact INq | | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
                       rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                       apply (bslots_nodup_split L st X Q CP ql qz gs1 q (gs2 ++ [qgz])); [rewrite QQ, QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                       pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
                       unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
                   +++ cbn [abatches_to]. split; [| exact I].
                       (* [comment removed for export] *)
                       unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q)) (qaddrs L [])) with (qfirst L (q_loc Q)).
                       assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
                       assert (NGL : abatch_addr L (qb_slot qgz) <> lst).
                       { rewrite QLST. intros E. apply (bslots_nodup_split L st X Q CP ql qz qg qgz []); [rewrite QQ, QQg; rewrite <- ?app_assoc; cbn [app]; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
                         pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity).
                       (nd_pre (BGEO qgz INgz) 4%nat; intros _ _ F3 F4; nd_post). pose proof (BLST qgz INgz NGL) as DL.
                       assert (DE : eb = lst \/ abatch_addr L (qb_slot qgz) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot qgz)).
                       { destruct EBK as [E|[EA' E]]; [left; exact E| discriminate]. }
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI DL DE GLS HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_drain L st2 st' X' (mkQConc (ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}]) (q_glob Q) true (q_pend Q)) true CP2 QL3 QG3).
        * exact NUM'.
      + (* [comment removed for export] *)
        pose proof (NDR NDRN) as EST. 
        assert (GD : g_drain g = false) by (rewrite GDR; apply Z.ltb_ge; rewrite <- QB2; exact NDRN).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        exists (mkQConc (ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}]) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite EST, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [| exact ABL'].
          rewrite length_app, qfirst_reslot, qlast_reslot, <- QQ, <- ELST. cbn [length].
          replace (Z.of_nat (length l + 1)) with (Z.of_nat (length (a_qloc st))) by (rewrite QL, length_app; cbn; reflexivity). exact QC'.
        * split; [rewrite <- GNB, <- GFST, <- GL, <- GQB; exact DKP'|].
          unfold abatches. eapply abatches_to_frame; [exact MUn | exact WM | exact ABG |].
          intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
          assert (NEq : abatch_addr L (qb_slot q) <> lst).
          { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
            apply (bslots_nodup_split L st X Q CP ql qz gs1 q gs2); [rewrite QQ, EQg; rewrite <- ?app_assoc; cbn [app]; reflexivity|].
            pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
            unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
          apply BFR; [exact INq | exact NEq | rewrite EGL; unfold dk_glst; rewrite GD; exact NEq].
        * first [rewrite EST | idtac]. exact CP2.
        * first [rewrite <- EST | idtac]. exact NUM'.
    - (* [comment removed for export] *)
      (nd_pre (NEWF eq_refl) 8%nat; intros NK24 NB24 KK24 NIB JK24 FK CIN POS; nd_post).
      (nd_pre EKP 6%nat; intros C24' [stj' SJ'] NBc NAc [bs NJc] OLDc; nd_post).
      pose proof EAPP0 as EAPP.
      set (nbt := mkABatch 1 (n + 8192) [ch]) in *.
      set (qn := mkQB k24 [0]) in *.
      assert (Q2 : a_qloc st2 = a_qloc st ++ [nbt] /\ a_qloc_bytes st2 = a_qloc_bytes st + (n + 8192) /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. (pose proof (enq_new_core ch st) as ndP__; nd_pre ndP__ 7%nat; intros _ E1 E2 _ E3 E4 _; nd_post).
        rewrite E1, E2, E3, E4. subst nbt. unfold ch. cbn [a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_live chunk_size]. fold ch. unfold Q_BATCH_BYTES.
        split; [reflexivity|]. split; [clear; lia|]. split; reflexivity. }
      (nd_pre Q2 4%nat; intros QL2 QB2 QG2 QGB2; nd_post).
      assert (FSTE : (if match a_qloc st with [] => false | _ :: _ => true end then qfirst L (q_loc Q) else abatch_addr L k24) = qfirst L (q_loc Q ++ [qn])).
      { rewrite qfirst_app_r. subst qn; cbn [qb_slot]. generalize LN1. clear. generalize (a_qloc st) (q_loc Q).
        intros [|x1 r1] [|x2 r2] LL; cbn in LL; first [reflexivity | discriminate]. }
      rewrite FSTE in QC'. rewrite FSTE in DKP'.
      assert (QLST' : qlast L (q_loc Q ++ [qn]) = abatch_addr L k24) by (subst qn; apply qlast_app1).
      (* [comment removed for export] *)
      assert (GNL : forall q, In q (q_glob Q) -> abatch_addr L (qb_slot q) <> lst).
      { intros q Hq E. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
        destruct LSTF as [Z0|((q' & Hq' & Eq') & _)].
        - (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post). clear -F3 RES RHI E Z0. lia.
        - apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post). apply in_split in Hq'. (nd_pre Hq' 3%nat; intros qs1 qs2 EQl; nd_post).
          apply (bslots_nodup_split L st X Q CP qs1 q' (qs2 ++ gs1) q gs2); [rewrite EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP q' ltac:(apply in_or_app; left; rewrite EQl; apply in_or_app; right; left; reflexivity)).
          rewrite Eq' in E. unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      (* [comment removed for export] *)
      assert (ABO' : abatches_to L m' (a_qloc st) (q_loc Q) (abatch_addr L k24)).
      { destruct (a_qloc st) as [|b0 l0] eqn:QL0.
        - replace (q_loc Q) with (@nil qbatchc) by (clear -LN1; destruct (q_loc Q); [reflexivity| cbn in LN1; discriminate]). exact I.
        - cbv iota beta in OLDc. destruct OLDc as [OLD1 OLD2]. rewrite <- QL0 in *.
          assert (LNE : a_qloc st <> []) by (rewrite QL0; discriminate).
          assert (QL : a_qloc st = removelast (a_qloc st) ++ [List.last (a_qloc st) dummy_batch]) by (apply app_removelast_last; exact LNE).
          assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL0; cbn; clear; lia).
          assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; clear -LQ; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
          set (l := removelast (a_qloc st)) in *. set (bl := List.last (a_qloc st) dummy_batch) in *.
          set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
          assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
          assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
          assert (FULL : b_count bl = Q_BATCH).
          { pose proof EA as EA0. unfold enq_is_app in EA0. rewrite QL, rev_unit in EA0. cbv iota beta in EA0.
            revert EA0. destruct (Z.eqb_spec (b_count bl) Q_BATCH) as [E|NE]; intros EA0; [exact E| discriminate]. }
          unfold abatches in ABL. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
          cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
          rewrite QL, QQ. apply abatches_to_app; [exact LNl|]. split.
          + cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
            intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
            assert (NEq : abatch_addr L (qb_slot q) <> lst).
            { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post).
              apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
              pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
              unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
            apply BFR; [exact INq | exact NEq |].
            destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post); clear -F3 RES RHI; lia|].
            rewrite Eqg. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post). apply in_split in Hqg. (nd_pre Hqg 3%nat; intros gs1 gs2 EQg; nd_post).
            apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
            pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
            unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
          + cbn [abatches_to]. split; [| exact I].
            unfold abatch_cells. cbv zeta. change (hd (abatch_addr L k24) (qaddrs L [])) with (abatch_addr L k24). rewrite <- QLST.
            split; [rewrite FULL; exact OLD1|]. split; [exact OLD2|]. split; [| split; [exact Z4| split; [exact Z5| exact Z6]]].
            rewrite FULL. replace (Q_BATCH_BYTES - 24 - 8 * Q_BATCH) with 0 by reflexivity. unfold Q_BATCH. apply junk_nil; (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [clear -Z0; lia | atop_facts; clear -F3 F4 RES RHI; lia]). }
      (* [comment removed for export] *)
      assert (ABN' : abatch_cells L m' nbt qn 0).
      { unfold abatch_cells. cbv zeta. subst nbt qn. cbn [qb_slot qb_ks b_size b_count b_chunks]. rewrite qhdrs_cons. cbn [qhdrs app map qhdr]. rewrite QH.
        split; [exact NBc|]. split; [exact NAc|]. split; [exists bs; unfold Q_BATCH_BYTES; exact NJc|]. split; [reflexivity|]. split; [reflexivity| unfold Q_BATCH; clear; lia]. }
      assert (ABL' : abatches_to L m' (a_qloc st ++ [nbt]) (q_loc Q ++ [qn]) 0).
      { apply abatches_to_app; [exact LN1|]. split; [cbn [qaddrs map hd]; subst qn; cbn [qb_slot]; exact ABO'|]. cbn [abatches_to]. split; [exact ABN'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q))).
      { subst X' qn nbt. rewrite ?EA. unfold xfreeS. cbv iota beta.
        apply (qcoupled_new_sec L st X Q mb ms n WF CP st2 k24 (c_count (get_cls st K_BATCH_CLASS)) (n + 8192) true 0 eq_refl POS NK24 QL2 QG2). }
      destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [DR|NDRN].
      + (* [comment removed for export] *)
        (nd_pre (DRN DR) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        destruct DKP' as [GC' GLN].
        exists (mkQConc [] (q_glob Q ++ (q_loc Q ++ [qn])) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite QLST'.
             assert (FE : qfirst L (q_glob Q ++ q_loc Q ++ [qn]) = (if g_full g then g_fst g else qfirst L (q_loc Q ++ [qn]))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate).
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; clear -LQg; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
                   set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
                   set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
                   assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
                   rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
                   cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
                   assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
                   rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
                   rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
                   +++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
                       intros q Hq. assert (INg : In q (q_glob Q)) by (rewrite QQg; apply in_or_app; left; exact Hq).
                       assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INg).
                       assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
                       { intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                         apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       apply BFR; [exact INq | exact (GNL q INg) | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
                   +++ cbn [abatches_to]. split; [| exact I].
                       (* [comment removed for export] *)
                       unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q ++ [qn])) (qaddrs L [])) with (qfirst L (q_loc Q ++ [qn])).
                       assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
                       assert (INgzg : In qgz (q_glob Q)) by (rewrite QQg; apply in_or_app; right; left; reflexivity).
                       assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INgzg).
                       pose proof (GNL qgz INgzg) as NGL.
                       (nd_pre (BGEO qgz INgz) 4%nat; intros _ _ F3 F4; nd_post). pose proof (BLST qgz INgz NGL) as DL.
                       pose proof (KDIS qgz INgz eq_refl) as DE.
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI DL DE EEB GLS HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_drain L st2 st' X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q)) true CP2 QL3 QG3).
        * exact NUM'.
      + (* [comment removed for export] *)
        pose proof (NDR NDRN) as EST.
        assert (GD : g_drain g = false) by (rewrite GDR; apply Z.ltb_ge; rewrite <- QB2; exact NDRN).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        exists (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite EST, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [| exact ABL'].
          rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1. rewrite QLST'. exact QC'.
        * split; [rewrite <- GNB, <- GFST, <- GL, <- GQB; exact DKP'|].
          unfold abatches. eapply abatches_to_frame; [exact MUn | exact WM | exact ABG |].
          intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
          apply BFR; [exact INq | exact (GNL q Hq) | rewrite EGL; unfold dk_glst; rewrite GD; exact (GNL q Hq)].
        * first [rewrite EST | idtac]. exact CP2.
        * first [rewrite <- EST | idtac]. exact NUM'. }
  (* [comment removed for export] *)
  assert (HBK : forall blk, In blk LB -> disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (ab_addr blk) (ab_size blk)).
  { intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size].
    - destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb' & msz' & Lp & EUA & Gs)].
      + destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        pose proof (busy_of_In_nodup L st X b WF Hb) as BOF.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
        (pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (DQ : forall q', In q' (q_loc Q ++ q_glob Q) ->
            aslot_addr L cb kb + size_of_class cb <= abatch_addr L (qb_slot q') \/ abatch_addr L (qb_slot q') + 8192 <= aslot_addr L cb kb).
        { intros q' Hq'. (nd_pre (bslot_busy L st X Q CP q' Hq') 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> qb_slot q').
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2.
            pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq, <- E1, <- E2, BOF in BY. injection BY as EE. subst yq. rewrite Sb in Syq. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS (qb_slot q') ALO WF HCb (K24) HKb (bslot_range L st X Q WF CP q' Hq') NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DK24 : enq_is_app st = false -> aslot_addr L cb kb + size_of_class cb <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= aslot_addr L cb kb).
        { intros EAx. (nd_pre (NEWF EAx) 4%nat; intros _ NBk KK _; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> k24).
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2. rewrite <- E1, <- E2, BOF in NBk. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS k24 ALO WF HCb (K24) HKb KK NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DL : lst = 0 \/ aslot_addr L cb kb + size_of_class cb <= lst \/ lst + 8192 <= aslot_addr L cb kb).
        { destruct LSTF as [Z0|((q' & Hq' & Eq') & _)]; [left; exact Z0| right]. rewrite Eq'. apply DQ. apply in_or_app; left; exact Hq'. }
        assert (DE : eb = lst \/ aslot_addr L cb kb + size_of_class cb <= eb \/ eb + 8192 <= aslot_addr L cb kb).
        { destruct EBK as [E|[EAx E]]; [left; exact E| right]. rewrite E. exact (DK24 EAx). }
        assert (DG : gl = lst \/ gl = 0 \/ aslot_addr L cb kb + size_of_class cb <= gl \/ gl + 8192 <= aslot_addr L cb kb).
        { destruct GLF as [[_ E]|(_ & _ & [Z0|((q' & Hq' & Eq') & _)])]; [left; exact E| right; left; exact Z0| right; right].
          rewrite Eq'. apply DQ. apply in_or_app; right; exact Hq'. }
        apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia
                    | clear -DL FIT P5 RSP RES RHI; lia | clear -DE DL FIT P5 RSP RES RHI; lia | clear -DG DL FIT P5 RSP RES RHI; lia].
      + (* [comment removed for export] *)
        assert (NEc : CSec mb' msz' n' <> ch).
        { intros E. apply NOTL. exists q. rewrite <- E. exact Lp. }
        assert (INc : In (CSec mb' msz' n') cs) by (eapply Permutation_in; [apply Permutation_sym; exact PCS| right; eapply live_sec_in; exact Lp]).
        pose proof INcs as INs.
        destruct WD as [_ DJ]. destruct (DJ _ _ INc INs NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
        all: cbn [sec_wf1] in Gs; (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        all: pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF; subst A'; unfold SEC_UOFF, K_HIGH_MEM in *.
        all: unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        all: apply Kobj; [clear -Gs2 Gs4 Gs5 SF; lia| clear -Gs3 Gs4 Gs5 SF; lia| clear -Gs5; lia| clear -Gs4 Gs5 SF Ct; lia| clear -Gs4 Gs5 SF Cr; lia| clear -Gs4 Gs5 SF Cn; lia| clear -Gs4 Gs5 SF Cs; lia| clear -Gs4 Gs5 SF Dc; lia].
    - (nd_pre (FKD cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post). unfold K_HIGH_MEM in *.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia | clear -K1 K3 SC_f; lia]. }
  (* [comment removed for export] *)
  assert (TLSK : forall TA tk, ATPv + -200 <= TA -> TA + tk <= ATPv + 312 -> 0 <= tk ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) TA tk).
  { intros TA tk TH1 TH2 TH3. pose proof ATPv_img as TI. apply Kimg; clear -TH1 TH2 TH3 TI; unfold AIMG_HI; lia. }
  assert (TLSS : forall a', ATPv + -200 <= a' < ATPv + 312 ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros a' Ha'. pose proof ATPv_img as TI. apply Klow; clear -Ha' TI; try (rewrite shad_div; unfold ASHOFF); try Z.div_mod_to_equations; lia. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros cls FA sz Hin a' Ha'.
    (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). unfold K_HIGH_MEM in *.
    assert (FAL8 : al_fake L mod 8 = 0) by (destruct FKO as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
    apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
    rewrite SHE. destruct SC_f as [D|D].
    - right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
      pose proof (shad_mono (al_fake L) a' ltac:(clear -K1 Ha'; lia)) as MM. clear -HH MM SHL. lia.
    - left. pose proof (shad_sep _ _ _ D FAL8) as HH. rewrite (shad_div a'), (shad_div (al_fake L)), shlen_div in *.
      clear -HH Ha' K3 FAL8. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split.
  { eapply (aheap_pres_freeS CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact TLSK | exact TLSS | apply Klow; unfold AIMSH_LO, AIMSH_LEN; clear; lia
      | rewrite <- (ao_ahm_eq L ALO); unfold AAHM_SZ; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI;
      pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; pose proof (ad_ahm_nodes L ALO) as DA3; pose proof (ad_ahm_store L ALO) as DA4;
      (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ SC_ahm; nd_post);
      unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OAH, OAHI, DA1, DA2, DA3, DA4; apply Kobj; clear -OAH OAHI DA1 DA2 DA3 DA4 SC_ahm; lia]. }
  split; [exact ALO|].
  split. { (pose proof ARNG as ndP__; nd_pre ndP__ 14%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 RCl RPA RSC RPSH RTLS; nd_post).
           unfold arng. repeat (split; [assumption|]). split; [| split; [rewrite ENRES; exact RPA| split; [eapply RSEC_perm; [apply Permutation_sym; exact PD| exact RSCS]| split; [exact RPSH | exact RTLS]]]].
           intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24a, M24d; exact (RCl K_BATCH_CLASS Hc')| rewrite (GCo' c' NE); exact (RCl c' Hc')]. }
  split; [| exact HFK'].
  exists X'. split; [| exact BL'].
  split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
  split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3'].
Qed.
End Zd1.
#[using="HL CI_OK"] Theorem store_freeRS : ltac:(let t := eval cbv delta [store_freeRS__stmt] in store_freeRS__stmt in exact t).
Proof. exact store_freeRS__body. Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.AFreeStoreK.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeStoreR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_store.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6307840 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6307840 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ek_pre_b_hi : forall ek RNG t nb lst n hm m, ek_pre ek RNG t nb lst n hm m -> 0x10007fff8000 <= ek_b ek lst.
Proof.
  intros ek RNG t nb lst n hm m EK.
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0]; cbn [ek_pre ek_b] in *.
  - (nd_pre EK 16%nat; intros NB1 LB CNT BSZ BSZN NX LA LEN LJ L0 L1 DTL DHL CR' STS' RL; nd_post). exact L0.
  - (nd_pre EK 20%nat; intros FULL SB CR CH LCH CNT NTH IXS STS HB BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB; nd_post). exact B0.
Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Definition store_freeRS__stmt : Prop := store_freeRS_stmt DI AFK CI.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 5).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 6).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 7).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 8).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 9).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 10).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 11).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 12).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 13).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 14).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 15).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 16).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 17).
Variable F : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 18).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 19).
Variable m : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 20).
Variable st : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 21).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 22).
Variable X : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 23).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 24).
Variable cs : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 25).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 26).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 27).
Variable n : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 28).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 29).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 30).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 31).
Variable k24 : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 32).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 33).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'store_freeRS__stmt 34).
Let ch := CSec mb ms n.
Let st2 := st_enq st ch.
Let ek := ek_of L st X Q n k24 stj chunks.
Let g := g_of L st Q (ek_delta ek n).
Let UB := mb + 6144.
Let lst := qlast L (q_loc Q).
Let eb := ek_b ek lst.
Let gl := dk_glst g lst.
Let gq := shlen (rup n 8).
Let st' := st_after st2.
#[using="HL CI_OK ch st2 ek g UB lst eb gl gq st'"] Lemma store_freeRS__body : ltac:(let T := type of (fun (h : store_freeRS__stmt) => h L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q cs mb ms n b1 ctx lo k24 stj chunks) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (F, (fc, (m, (st, (LB, (X, (Q, (cs, (mb, (ms, (n, (b1, (ctx, (lo, (k24, (stj, chunks))))))))))))))))))))))))))))))))))) as _.
  unfold store_freeRS_stmt. 
  cbv zeta. intros ALO ARNG AR BL HFK PCS RSCS NOTL NQM B1 B13 CTX EAF NK0 NB0 KK0 NIB0 JK0 FSH0 CIN0 POS0 NOREC EK DK CEIL LO ms' PM. unfold AFREE_STACK in LO.
  assert (NEWF : enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) by (intros _; repeat (split; [assumption|]); exact POS0).
  clear NK0 NB0 KK0 NIB0 JK0 FSH0 CIN0 POS0.
  chg (CSec mb ms n) ch.
  chg (st_enq st ch) st2.
  chg (ek_of L st X Q n k24 stj chunks) ek.
  chg (g_of L st Q (ek_delta ek n)) g.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHSm] in HQ, HS, HD. rename HQ into AQ.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS0 UNW; nd_post).
  pose proof HS as HS0. (nd_pre HS0 5%nat; intros WFS ARR0 SINST PZ SHZ; nd_post).
  (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros _ WP WR WL WB WF1 WD; nd_post).
  assert (INcs : In ch cs) by (eapply Permutation_in; [apply Permutation_sym; exact PCS| left; reflexivity]).
  pose proof (proj1 (Forall_forall _ _) WF1 ch INcs) as WFch.
  (nd_pre (sec_wf1_facts' L mb ms n WFch) 13%nat; intros MAL MLO MCE MSE NB RZ MSB MSAL NMS NS0 SCL NPR N6; nd_post).
  (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post). unfold AIMG_HI in ML1. (pose proof (ablk_int _ _ MLO) as ndP__; nd_pre ndP__ 6%nat; intros kM KAM KBM KEM KCM KDM; nd_post).   (* [comment removed for export] *)
  (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros SC_t SC_c SC_r SC_p SC_n SC_st SC_f SC_d SC_tls SC_ahm0; nd_post).
  (* [comment removed for export] *)
  (nd_pre ARR0 5%nat; intros order PO U64 JK PER; nd_post).
  assert (INo : In ch order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact INcs]).
  destruct (In_nth_error _ _ INo) as [i NTH].
  assert (IL : (i < length order)%nat) by (apply (proj1 (nth_error_Some order i)); rewrite NTH; discriminate).
  assert (LENO : Z.of_nat (length order) = a_nsec st) by (rewrite (Permutation_length PO); exact WL).
  assert (WF1o : Forall (sec_wf1 L) order).
  { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PO| exact Hc]. }
  assert (WDo : sec_disjoint order) by (eapply sec_disjoint_perm; [apply Permutation_sym; exact PO| exact WD]).
  (nd_pre (PER i _ NTH) 3%nat; intros lv0 LV0 CH; nd_post).
  assert (Elv : lv0 = false) by (destruct lv0; [exfalso; apply NOTL; apply (proj1 LV0); reflexivity| reflexivity]). subst lv0.
  pose proof CH as CH0. unfold ch in CH0. cbn [asec_chunk] in CH0.
  (nd_pre CH0 9%nat; intros H1 _ _ _ _ H6 S1 _ S3; nd_post). unfold SEC_UOFF in H6, S3.
  destruct (junk_split m _ 8 (ms - 6144 - 8) ltac:(replace (8 + (ms - 6144 - 8)) with (ms - 6144) by lia; exact H6) ltac:(lia) ltac:(lia)) as [_ UJ].
  rewrite (granules_rup n) in S3 by (clear -NB; lia).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  (pose proof (aobj4_int _ OT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ OC ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci _ [kC CBND]; nd_post). (pose proof (aobj_int _ _ ON ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni _ [kN NBND]; nd_post).
  (pose proof (aobj_int _ _ OS ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si _ [kS SBND]; nd_post). pose proof (ao_res_hi L ALO) as RHI.
  unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
  box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
  word_range sp SPR.
  chg (mb + 6144) UB.
  assert (EUB : UB = mb + 6144) by reflexivity.
  assert (EHM : mb + 6128 = UB - 16) by (subst UB; clear; lia).
  assert (UB16' : UB mod 8 = 0) by (subst UB; clear -MAL; Z.div_mod_to_equations; lia).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  rewrite EHM in PM, EK, DK.
  replace (mb + 6144) with UB in UJ, S3 by reflexivity.
  (pose proof (rup8_facts n ltac:(clear -NB; lia)) as ndP__; nd_pre ndP__ 3%nat; intros RUP RUP8 RUPS; nd_post).
  assert (SHGEO : shad UB = shad mb + 768 /\ shlen (rup n 8) <= ms / 8 - 768 /\ 0 < shlen (rup n 8) /\ UB + rup n 8 <= mb + ms
                  /\ 2148239360 <= shad mb /\ shad mb + ms / 8 <= 17594332446720).   (* [comment removed for export] *)
  { subst UB. rewrite !shad_div, RUPS. unfold ASHOFF. (pose proof (sec_facts n ltac:(clear -NB; lia) NPR) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ RS1 _ NSE _; nd_post).
    unfold K_HIGH_MEM in *. pose proof atop_range as AR8. clear -MAL RUP RUP8 RS1 NSE NMS N6 NB ML1 ML3 MCE MSAL AR8. Z.div_mod_to_equations. lia. }
  (nd_pre SHGEO 6%nat; intros SHE SHL SHP UBS SHLO SHHI; nd_post).
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof NUM as NUM0. (nd_pre NUM0 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof CP as CP0. (nd_pre CP0 7%nat; intros LN1 LN2 _ _ ND2 BSI _; nd_post).
  (* [comment removed for export] *)
  assert (CNT : enq_app st ch = None -> 0 < c_count (get_cls st K_BATCH_CLASS)) by (intros _; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NEWF EAF))))))))).
  assert (EAPP0 : enq_app st ch = None).
  { destruct (enq_app st ch) as [sx|] eqn:EAPP; [exfalso| reflexivity].
    assert (EA1 : enq_is_app st = true) by (apply (proj2 (enq_is_app_spec st ch)); eexists; exact EAPP). congruence. }
  assert (SB : a_qloc_bytes st2 = a_qloc_bytes st + ek_delta ek n /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st).
  { subst st2 ek. unfold st_enq, ek_of. rewrite EAPP0, EAF. cbn [ek_delta]. (pose proof (enq_new_core ch st) as ndP__; nd_pre ndP__ 7%nat; intros _ G1' G2' _ _ L2' _; nd_post).
    rewrite G1', G2', L2'. unfold ch. cbn [chunk_size]. unfold Q_BATCH_BYTES. repeat split; try reflexivity. clear; lia. }
  (nd_pre SB 3%nat; intros SB1 SB2 SB3; nd_post).
  assert (ED0 : 0 <= ek_delta ek n /\ ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; clear -NB; destruct (enq_is_app st); cbn [ek_delta]; lia).
  assert (EBK : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q) \/ (enq_is_app st = false /\ ek_b ek (qlast L (q_loc Q)) = abatch_addr L k24)).
  { subst ek. unfold ek_of. destruct (enq_is_app st) eqn:EAx; cbn [ek_b]; [left; reflexivity| right; split; reflexivity]. }
  assert (EBB : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
      \/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q))).
  { destruct EBK as [E|[EAx E]]; [left; exact E| right; exists k24]. (nd_pre (NEWF EAx) 5%nat; intros NK NBk KK NIB _; nd_post). split; [exact E|]. split; [exact KK| exact NIB]. }
  assert (HMSEP : forall kk, 0 <= kk < ndist st K_BATCH_CLASS -> UB - 16 + 24 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= UB - 16).
  { intros kk KK. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ _ _ _ PERC _; nd_post).
    (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros Q1 Q2 _; nd_post).
    (pose proof (slot_in_region L st K_BATCH_CLASS kk ltac:(rewrite size_of_class_24; lia) (proj1 Q1) KK) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 _; nd_post).
    rewrite size_of_class_24 in P4. subst UB. unfold abatch_addr, aregion, K_REGION, K_FREEARR_OFF, K_BATCH_CLASS in *.
    clear -P5 P4 Q1 Q2 RSP SC_r MSB. lia. }
  (nd_pre (read_dkS (AHSm DI AFK cs Q) L st X Q m RNG (UB - 16) ALO ARNG AR AQ HMSEP (ek_b ek (qlast L (q_loc Q))) (ek_delta ek n) ek
              (proj1 ED0) EBB ltac:(rewrite <- SB1, <- SB2; exact NOREC) eq_refl) 4%nat; intros _ _ GL GLST; nd_post).
  fold g in GL, GLST.
  chg (qlast L (q_loc Q)) lst. chg (ek_b ek lst) eb. chg (dk_glst g lst) gl. chg (shlen (rup n 8)) gq.
  (* [comment removed for export] *)
  assert (BGEO : forall q, In q (q_loc Q ++ q_glob Q) ->
      aregion L K_BATCH_CLASS <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
      /\ al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
  { intros q Hq. (pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
    rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
    generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  assert (A24 : c_allocated_user (get_cls st K_BATCH_CLASS) <= K_FREEARR_OFF).
  { (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros Q1 Q2 _; nd_post). lia. }
  assert (LSTF : lst = 0 \/ ((exists q, In q (q_loc Q) /\ lst = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= lst /\ lst + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104)).
  { subst lst. destruct (qlast_cases L (q_loc Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (GDR : g_drain g = (Q_CACHE <? a_qloc_bytes st + ek_delta ek n)) by reflexivity.
  assert (GLF : (g_drain g = false /\ gl = lst)
             \/ (g_drain g = true /\ gl = qlast L (q_glob Q)
                 /\ (gl = 0 \/ ((exists q, In q (q_glob Q) /\ gl = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104)))).
  { subst gl. rewrite GLST, GDR. destruct (Q_CACHE <? a_qloc_bytes st + ek_delta ek n); [right| left; split; reflexivity].
    split; [reflexivity|]. split; [reflexivity|].
    destruct (qlast_cases L (q_glob Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (EBF : eb = 0 \/ (aregion L K_BATCH_CLASS <= eb /\ eb + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104)).
  { subst eb. destruct EBK as [E|[EAx E]].
    - rewrite E. destruct LSTF as [Z0|(_ & FF)]; [left; exact Z0| right; exact FF].
    - right. rewrite E. (nd_pre (NEWF EAx) 4%nat; intros _ _ KK _; nd_post). (pose proof (slot_geo L st X K_BATCH_CLASS k24 ALO WF (K24) KK) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
      rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
      generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  (* [comment removed for export] *)
  (nd_pre PM 19%nat; intros id t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' sj' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MU WM MI' ST' IDR HDR' FC' SH' QC' EKP DKP STATS' LSJ' UW' FL' IAS' IAM' DEP'; nd_post).
  fold lst in MU, QC', EKP, DKP, EBK. fold eb in MU, EBK. fold gl in MU. fold gq in MU, SH'.
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  assert (ELST : lst = qlast L (q_loc Q)) by reflexivity. assert (EEB : eb = ek_b ek lst) by reflexivity.
  assert (EGL : gl = dk_glst g lst) by reflexivity. assert (EGQ : gq = shlen (rup n 8)) by reflexivity.
  clearbody lst eb gl gq.
  (* [comment removed for export] *)
  assert (EBNZ : 0x10007fff8000 <= eb) by (rewrite EEB; exact (ek_pre_b_hi _ _ _ _ _ _ _ _ EK)).   (* [comment removed for export] *)
  replace (eb + 8192) with (eb + qsz eb) in MU by (rewrite (qsz_pos eb) by (clear -EBNZ; lia); reflexivity).   (* [comment removed for export] *)
  assert (MUn : munch (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  clear MU.
  assert (KF : kfactsS (bv_unsigned sp) (al_t L) mb ms UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo lst eb gl).
  { unfold kfactsS. unfold K_HIGH_MEM in *.
    assert (GQ1 : 1 <= gq) by (clear -SHP EGQ; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP MLO ML1 ML3 MCE EUB UBS NB RUP SC_t SC_r SC_n SC_st SHE SHL SHLO SHHI GQ1 EGQ LSTF EBF GLF EBNZ. clear. intros.
    rewrite ?EGQ in SHL. unfold iclr, AIMG_LO, AIMG_HI in *.   (* [comment removed for export] *)
    (destruct LSTF as [Z0|(_ & FF)]; [rewrite (qsz_eq0 lst Z0) | rewrite (qsz_pos lst) by (atop_facts; lia)]);
    (destruct EBF as [Z1|FF1]; [exfalso; atop_facts; lia|]); rewrite (qsz_pos eb) by (atop_facts; lia); destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & FF2)])];
    sg_destr; repeat split; first [assumption | lia]. }
  pose proof (KS_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KS_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KS_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KS_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KS_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s) SC_c) as Kctx.
  pose proof (KS_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
  pose proof (KS_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
  pose proof (KS_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KS_objL _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as KobjL.      (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
  unfold adisj in D_l_t, D_l_r, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
  pose proof (KS_chunk _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kchunk.
  (* [comment removed for export] *)
  assert (SC : same_core st (st_after st2) /\ a_cinit (st_after st2) = a_cinit st /\ a_live (st_after st2) = a_live st /\ a_next (st_after st2) = a_next st
               /\ a_space_beg (st_after st2) = a_space_beg st /\ a_ptr_array (st_after st2) = a_ptr_array st
               /\ (enq_is_app st = true -> a_cls (st_after st2) = a_cls st)
               /\ (enq_is_app st = false -> a_cls (st_after st2) = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
  { pose proof (st_after_core st2) as [SC2 CL2'].
    assert (SC1 : same_core st st2 /\ (enq_is_app st = true -> a_cls st2 = a_cls st) /\ (enq_is_app st = false -> a_cls st2 = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
    { subst st2. unfold st_enq. destruct (enq_app st ch) as [sx|] eqn:EAPP.
      - (nd_pre (enq_app_Some st _ sx EAPP) 5%nat; intros l bl QL NFz ndR1__; nd_post; revert ndR1__; intros ->). split; [repeat split; intros; reflexivity|].
        split; [intros _; reflexivity|]. intros EAx. exfalso.
        assert (EA1 : enq_is_app st = true) by (apply (proj2 (enq_is_app_spec st ch)); eexists; exact EAPP).
        congruence.
      - (pose proof (enq_new_core ch st) as ndP__; nd_pre ndP__ 7%nat; intros C1 _ _ _ _ _ C7; nd_post). split; [exact C1|].
        split; [| intros _; exact C7]. intros EAx. exfalso.
        assert (EA1 : enq_is_app st = true) by exact EAx. destruct (proj1 (enq_is_app_spec st ch) EA1) as [s Hs]. congruence. }
    (nd_pre SC1 3%nat; intros SC1 CLa CLb; nd_post). pose proof (same_core_trans _ _ _ SC1 SC2) as SC3.
    pose proof SC3 as SC0. (nd_pre SC0 8%nat; intros F1 F2 F3 F4 F5 F6 F7 _; nd_post).
    split; [exact SC3|]. split; [exact F3|]. split; [exact F1|]. split; [exact F2|]. split; [exact F4|]. split; [exact F5|].
    split; [intros EAx; rewrite CL2'; exact (CLa EAx)| intros EAx; rewrite CL2'; exact (CLb EAx)]. }
  (nd_pre SC 8%nat; intros SC ECIN ELIVE ENEXT ESB EPA CLa CLb; nd_post).
  pose proof SC as SC0. (nd_pre SC0 12%nat; intros _ _ _ _ _ ENRES ENSEC GCo M24a M24b M24c M24d; nd_post).
  chg (st_after st2) st'.
  set (X' := xfreeS X (enq_is_app st) k24).
  assert (GC24 : get_cls st' K_BATCH_CLASS = (if enq_is_app st then get_cls st K_BATCH_CLASS else cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS))).
  { unfold get_cls at 1. destruct (enq_is_app st) eqn:EAx; [rewrite (CLa eq_refl); reflexivity| rewrite (CLb eq_refl), lookup_insert_eq; reflexivity]. }
  assert (GCo' : forall c', c' <> K_BATCH_CLASS -> get_cls st' c' = get_cls st c') by (intros c' NE; rewrite (GCo c' NE); reflexivity).
  assert (NDS : forall c', ndist st' c' = ndist st c').
  { intros c'. unfold ndist. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24b; reflexivity| rewrite (GCo' c' NE); reflexivity]. }
  assert (MC' : forall c', max_count st' c' = max_count st c') by (intros c'; unfold max_count; rewrite ECIN; reflexivity).
  (* [comment removed for export] *)
  assert (WF' : awf L st' X').
  { subst X'. unfold xfreeS. destruct (enq_is_app st) eqn:EAx.
    - exfalso. clear -EAF EAx. congruence.
    - (nd_pre (NEWF eq_refl) 8%nat; intros NK NBk KK NIB JKb FSH CIN POS; nd_post).
      apply (awf_xbatch L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK).
      + exact ESB. + exact EPA. + exact ECIN. + exact ELIVE. + exact ENEXT.
      + intros c' NE. rewrite (GCo' c' NE). reflexivity.
      + rewrite GC24. reflexivity. }
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    (first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |])] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s SC_tls TLN ATR0; lia] |]) ]). apply Forall_nil. }
  assert (INST' : ainstance L st' m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | exact ENRES | exact ENSEC | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
  assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
  assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
  (* [comment removed for export] *)
  assert (THR' : athread L st' X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE].
      + destruct (CACHES K_BATCH_CLASS Hc') as [tail (CR & CHc & LCH)]. unfold acache_cells. cbv zeta.
        rewrite GC24, MC', ECIN. subst X'. rewrite xfreeS_cache, Z.eqb_refl, andb_true_r.
        replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR, CHc |- * by (unfold acache_addr, K_BATCH_CLASS; clear; lia).
        subst ek. unfold ek_of in EKP. destruct (enq_is_app st) eqn:EAx; cbn [ek_post negb] in EKP |- *.
        * (nd_pre EKP 5%nat; intros _ _ _ CR' _; nd_post). exists tail. split; [exact CR'|]. split; [| exact LCH].
          eapply u32arr_frame; [exact CHc | exact MUn | exact WM |]. rewrite length_app, length_map. apply Kt; clear -LCH; lia.
        * destruct EKP as (CR' & _). (nd_pre (NEWF eq_refl) 8%nat; intros NK NBk KK NIB JKb FSH CIN POS; nd_post).
          cbn [c_count cls_set_count]. exists (Z_to_bv 64 (acompact K_BATCH_CLASS k24) :: tail).
          pose proof (cache24_split L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK) as [CACHE LRL].
          split; [exact CR'|]. split.
          -- eapply u32arr_frame; [| exact MUn | exact WM |].
             ++ rewrite CACHE, map_app in CHc. cbn [map] in CHc. rewrite <- app_assoc in CHc. cbn [app] in CHc. exact CHc.
             ++ rewrite length_app, length_map. cbn [length].
                replace (length (removelast (xc_cache (x_cls X K_BATCH_CLASS))) + Datatypes.S (length tail))%nat with 16%nat
                  by (rewrite CACHE, length_app in LCH; cbn [length] in LCH; clear -LCH; lia).
                apply Kt; clear; lia.
          -- cbn [length]. rewrite CACHE, length_app in LCH. cbn [length] in LCH. clear -LCH. lia.
      + eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | rewrite (GCo' c' NE); reflexivity | exact ECIN | |].
        * subst X'. rewrite xfreeS_cache. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [E|_]; [exfalso; exact (NE E)|]. rewrite andb_false_r. reflexivity.
        * unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply Kt; clear -Hc' NE; lia.
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + eapply junk_frame; [exact (proj1 (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia))) | exact MUn | exact WM | intros _; apply Kt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia).
          assert (STJ' : exists w : word, rw_cells asegs m' (al_t L + 2784) [C8 w]).
          { subst ek. unfold ek_of in EKP. destruct (enq_is_app st); cbn [ek_post] in EKP.
            - (nd_pre EKP 5%nat; intros _ _ _ _ STS'; nd_post). exists stj. exact STS'.
            - (nd_pre EKP 3%nat; intros _ STS' _; nd_post). exact STS'. }
          destruct STJ' as [w STS']. pose proof (junk_of_cells m' _ _ STS') as J. cbn in J. exact J.
        * replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) by (clear; lia).
          eapply junk_frame; [| exact MUn | exact WM | intros _; apply Kt; clear; lia].
          pose proof (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ CSb].
          pose proof (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(clear; lia) ltac:(clear; lia)) as [_ CSc].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by (clear; lia). exact CSc.
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  (* [comment removed for export] *)
  assert (BDIS : forall q1 q2, In q1 (q_loc Q ++ q_glob Q) -> In q2 (q_loc Q ++ q_glob Q) ->
      abatch_addr L (qb_slot q1) = abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q1) + 8192 <= abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q2) + 8192 <= abatch_addr L (qb_slot q1)).
  { intros q1 q2 Hq1 Hq2. destruct (Z.eq_dec (qb_slot q1) (qb_slot q2)) as [E|NE]; [left; rewrite E; reflexivity| right].
    pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot q1) (qb_slot q2) ltac:(pose proof (bslot_range L st X Q WF CP q1 Hq1); lia)
                  ltac:(pose proof (bslot_range L st X Q WF CP q2 Hq2); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (KDIS : forall q, In q (q_loc Q ++ q_glob Q) -> enq_is_app st = false ->
      abatch_addr L k24 + 8192 <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= abatch_addr L k24).
  { intros q Hq EAx. (nd_pre (NEWF EAx) 5%nat; intros NK NBk KK NIB _; nd_post).
    assert (NE : k24 <> qb_slot q) by (intros ->; apply NIB; apply in_map; exact Hq).
    pose proof (slots_disjoint L K_BATCH_CLASS k24 (qb_slot q) ltac:(lia) ltac:(pose proof (bslot_range L st X Q WF CP q Hq); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L st' m' c'' /\ afreearray L st' X' m' c'' /\ aslots L st' X' m' c'' /\ aslot_shadow L st' X' m' c'').
  { intros c'' Hc''. (nd_pre (CLS c'' Hc'') 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC1 : c_num_freed (get_cls st' c'') = c_num_freed (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24c| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC3 : c_allocated_user (get_cls st' c'') = c_allocated_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24b| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 4%nat; intros RI1 RI2 RI3 RI4; nd_post).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | exact EC1 | exact EC2 | exact EC3 | exact EC4 |].
      unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      apply Kres; try (clear -Hc'' RSP; lia).
      + destruct LSTF as [Z0|(_ & F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + destruct EBF as [Z0|(F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + assert (GLR : gl = 0 \/ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)).
        { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; exact F2].
          destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; exact F2]. }
        destruct GLR as [Z0|F2]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | exact EC1 | exact EC2 | | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + subst X'. apply xfreeS_free.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia | | |].
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          pose proof (farr_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2) as D. clear -D. lia.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, AIMG_HI, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
          rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) (afreearr L c'') ltac:(clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D RI2 RI3 FA2; lia| exact AM] | clear; lia].
    - (* [comment removed for export] *)
      eapply (aslots_update_gen L _ m m' MUn WM st st' X X' c''); [exact SLOTS | apply NDS | exact EC3 | exact EC4 | |].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D2 : (enq_is_app st = false /\ c'' = K_BATCH_CLASS /\ k'' = k24) \/ (enq_is_app st = true \/ c'' <> K_BATCH_CLASS \/ k'' <> k24))
          by (clear; destruct (enq_is_app st); lia).
        destruct D2 as [(EAx & E24 & EK24)|NE2].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X'. rewrite (busy_of_xfreeS X (enq_is_app st) k24 K_BATCH_CLASS k24), EAx. cbn [negb andb]. rewrite !Z.eqb_refl. cbn [andb].
          unfold aslot_busy, bbatch. cbn [xb_st xb_class xb_slot]. unfold xb_alloc. cbn [xb_class xb_slot]. rewrite size_of_class_24.
          subst ek. unfold ek_of in EKP. rewrite EAx in EKP. cbn [ek_post] in EKP. (nd_pre EKP 6%nat; intros _ _ BC BA [bsb BJ] _; nd_post).
          fold (abatch_addr L k24) in BC, BA, BJ |- *. change (aslot_addr L K_BATCH_CLASS k24) with (abatch_addr L k24).
          replace 8192 with (24 + (8 * Z.of_nat (length [Z_to_bv 64 (UB - 16)]) + (8192 - 24 - 8 * 1))) by (cbn; lia).
          apply junk_merge; [| | clear; lia| cbn; clear; lia].
          -- pose proof (junk_of_cells m' _ _ BC) as J. cbn in J. exact J.
          -- apply junk_merge; [apply junk_of_u64arr; exact BA | | cbn; clear; lia | clear; lia].
             cbn [length Z.of_nat Pos.of_succ_nat]. eexists. exact BJ.
        * assert (T1 : negb (enq_is_app st) && (K_BATCH_CLASS =? c'') && (k24 =? k'') = false).
          { destruct (enq_is_app st); cbn [negb andb]; [reflexivity|].
            destruct (Z.eqb_spec K_BATCH_CLASS c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k24 k'') as [E'|]; [| reflexivity]. exfalso.
            destruct NE2 as [NE|[NE|NE]]; [discriminate| apply NE; symmetry; exact E| apply NE; symmetry; exact E']. }
          assert (BX : busy_of X' c'' k'' = busy_of X c'' k'').
          { subst X'. rewrite (busy_of_xfreeS X (enq_is_app st) k24 c'' k''), T1. reflexivity. }
          (* [comment removed for export] *)
          assert (BQ : forall q, In q (q_loc Q ++ q_glob Q) -> c'' = K_BATCH_CLASS -> aslot_addr L c'' k'' = abatch_addr L (qb_slot q) ->
              exists yq, busy_of X c'' k'' = Some yq /\ xb_st yq = BBatch /\ xb_class yq = K_BATCH_CLASS /\ xb_slot yq = k''
                         /\ junk_at m (abatch_addr L (qb_slot q)) 8192 /\ k'' = qb_slot q).
          { intros q Hq -> EQA. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
            assert (EK' : k'' = qb_slot q) by (unfold abatch_addr, aslot_addr in EQA; rewrite size_of_class_24 in EQA; clear -EQA; lia). subst k''.
            exists yq. pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq in BY.
            split; [exact BY|]. split; [exact Syq|]. split; [exact Cyq|]. split; [exact Kyq|]. split; [| reflexivity].
            destruct SLOTS as [SLK _]. specialize (SLK (qb_slot q) Hk''). rewrite BY in SLK. unfold aslot_busy in SLK. rewrite Syq in SLK.
            unfold xb_alloc in SLK. rewrite Cyq, Kyq, size_of_class_24 in SLK. exact SLK. }
          assert (D3 : (c'' = K_BATCH_CLASS /\ lst <> 0 /\ aslot_addr L c'' k'' = lst) \/ (c'' <> K_BATCH_CLASS \/ lst = 0 \/ aslot_addr L c'' k'' <> lst)) by (clear; lia).
          destruct D3 as [(E24 & LNZ & EL)|NE3].
          -- (* [comment removed for export] *)
             right. rewrite BX. destruct LSTF as [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)]; [exfalso; exact (LNZ Z0)|].
             (nd_pre (BQ q ltac:(apply in_or_app; left; exact Hq) E24 ltac:(rewrite EL; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
             rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EL.
             assert (QNE : a_qloc st <> []) by (intros QL0; apply LNZ; rewrite ELST; replace (q_loc Q) with (@nil qbatchc) by (clear -QL0 LN1; destruct (q_loc Q); [reflexivity| rewrite QL0 in LN1; cbn in LN1; discriminate]); reflexivity).
             subst ek. unfold ek_of in EKP, EK. destruct (enq_is_app st) eqn:EAx; cbn [ek_post ek_pre] in EKP, EK.
             ** (nd_pre EKP 4%nat; intros LB' LA' [bs LJ'] _; nd_post). (nd_pre EK 9%nat; intros _ _ CNT' _ _ _ _ LEN _; nd_post).
                rewrite ELST in LB', LA', LJ' |- *.
                set (cnt := b_count (List.last (a_qloc st) dummy_batch)) in *.
                replace 8192 with (24 + (8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))) ++ [Z_to_bv 64 (UB - 16)])) + (8192 - 24 - 8 * (cnt + 1))))
                  by (rewrite length_app, LEN; cbn [length]; clear -CNT'; lia).
                apply junk_merge; [| | clear; lia| rewrite length_app, LEN; cbn [length]; clear -CNT'; lia].
                +++ pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
                +++ apply junk_merge; [apply junk_of_u64arr; exact LA' | | rewrite length_app, LEN; cbn [length]; clear -CNT'; lia | clear -CNT'; lia].
                    rewrite length_app, LEN. cbn [length]. replace (8 * Z.of_nat (Z.to_nat cnt + 1)) with (8 * (cnt + 1)) by (clear -CNT'; lia). eexists. exact LJ'.
             ** destruct (a_qloc st) as [|b0 bs0] eqn:QL0; [exfalso; exact (QNE eq_refl)|]. rewrite <- QL0 in *.
                (nd_pre EKP 6%nat; intros _ _ _ _ _ [LB' LA']; nd_post). destruct EK as ((_ & _ & _ & _ & _ & _ & _ & LEN0 & _) & _).
                rewrite ELST in LB', LA' |- *.
                replace 8192 with (24 + 8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))))))
                  by (rewrite LEN0; clear; lia).
                apply junk_merge; [| apply junk_of_u64arr; exact LA' | clear; lia| rewrite LEN0; clear; lia].
                pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
          -- assert (D4 : (g_drain g = true /\ c'' = K_BATCH_CLASS /\ gl <> 0 /\ aslot_addr L c'' k'' = gl /\ gl <> lst)
                        \/ (g_drain g = false \/ c'' <> K_BATCH_CLASS \/ gl = 0 \/ aslot_addr L c'' k'' <> gl \/ gl = lst)) by (destruct (g_drain g); clear; lia).
             destruct D4 as [(GD & E24 & GNZ & EG & GNL)|NE4].
             ** (* [comment removed for export] *)
                right. rewrite BX. destruct GLF as [[GD' _]|(_ & GQL & [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)])]; [congruence| exfalso; exact (GNZ Z0)|].
                (nd_pre (BQ q ltac:(apply in_or_app; right; exact Hq) E24 ltac:(rewrite EG; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
                rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EG.
                assert (GNE : a_qglob st <> []) by (intros QG0; clear -QG0 Hq LN2; destruct (q_glob Q) eqn:QQ0; [destruct Hq| rewrite QG0 in LN2; cbn in LN2; discriminate]).
                unfold dk_post in DKP. rewrite GD in DKP. (nd_pre DKP 3%nat; intros _ _ GLN; nd_post).
                assert (GF : g_full g = true) by (subst g; unfold g_of; cbn [g_full]; clear -GNE; destruct (a_qglob st); [exfalso; exact (GNE eq_refl)| reflexivity]).
                rewrite GF, GL, <- GQL in GLN.
                replace 8192 with (8 + 8184) by (clear; lia). apply junk_merge; [| | clear; lia | clear; lia].
                +++ pose proof (junk_of_cells m' _ _ GLN) as J. cbn in J. exact J.
                +++ rewrite <- Eq in JQ. destruct (junk_split m gl 8 8184 JQ ltac:(clear; lia) ltac:(clear; lia)) as [_ J2].
                    eapply junk_frame; [exact J2 | exact MUn | exact WM |]. intros _.
                    assert (DL : lst = 0 \/ lst + 8192 <= gl \/ gl + 8192 <= lst).
                    { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql, Eq.
                      destruct (BDIS ql q ltac:(apply in_or_app; left; exact Hql) ltac:(apply in_or_app; right; exact Hq)) as [E|E]; [| exact E].
                      exfalso. apply GNL. rewrite Eq, Eql. symmetry. exact E. }
                    assert (DE : eb = lst \/ eb + 8192 <= gl \/ gl + 8192 <= eb).
                    { destruct EBK as [E|[EAx E]]; [left; exact E| right]. rewrite E, Eq. exact (KDIS q ltac:(apply in_or_app; right; exact Hq) EAx). }
                    apply Kres; clear -F3 F4 RES RHI GNZ DL DE; lia.
             ** (* [comment removed for export] *)
                left. split; [exact BX|]. split.
                +++ assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> (c'' <> K_BATCH_CLASS \/ aslot_addr L c'' k'' <> abatch_addr L (qb_slot q)) ->
                        aslot_addr L c'' k'' + size_of_class c'' <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= aslot_addr L c'' k'').
                    { intros q Hq NE. pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS (qb_slot q) ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk''
                                    (bslot_range L st X Q WF CP q Hq) ltac:(destruct NE as [NE|NE]; [left; exact NE| destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NC']; [right| left; exact NC']];
                                                                                 intros EKK; apply NE; rewrite EKK; reflexivity)) as D.
                      rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                    assert (DW13 : lst = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= lst \/ lst + 8192 <= aslot_addr L c'' k'').
                    { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql. apply DQ; [apply in_or_app; left; exact Hql|].
                      destruct NE3 as [NE|[Z0|NE]]; [left; exact NE| exfalso| right; rewrite <- Eql; exact NE].
                      rewrite Eql in Z0. (nd_pre (BGEO ql ltac:(apply in_or_app; left; exact Hql)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                    assert (DW14 : eb = lst \/ aslot_addr L c'' k'' + size_of_class c'' <= eb \/ eb + 8192 <= aslot_addr L c'' k'').
                    { destruct EBK as [E|[EAx E]]; [left; exact E| right]. rewrite E. (nd_pre (NEWF EAx) 4%nat; intros _ _ KK _; nd_post).
                      pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS k24 ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk'' KK
                                    ltac:(destruct NE2 as [NE|[NE|NE]]; [rewrite EAx in NE; discriminate| left; exact NE| right; exact NE])) as D.
                      rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                    assert (DW15 : gl = lst \/ gl = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= gl \/ gl + 8192 <= aslot_addr L c'' k'').
                    { destruct GLF as [[_ E]|(GD & GQL & [Z0|((q & Hq & Eq) & _)])]; [left; exact E| right; left; exact Z0| right; right].
                      rewrite Eq. apply DQ; [apply in_or_app; right; exact Hq|].
                      destruct NE4 as [NE|[NE|[NE|[NE|NE]]]]; [congruence| left; exact NE| | right; rewrite <- Eq; exact NE| ].
                      - exfalso. rewrite Eq in NE. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -NE B3 RES RHI. lia.
                      - rewrite NE in *. destruct NE3 as [NE'|[Z0|NE']]; [left; exact NE'| exfalso| right; rewrite <- Eq; exact NE'].
                        rewrite Eq in Z0. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                    apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia
                                | clear -DW13 P5 RSP RES RHI; lia | clear -DW14 DW13 P5 RSP RES RHI; lia | clear -DW15 DW13 P5 RSP RES RHI; lia].
                +++ intros b Hb. (nd_pre (busy_of_Some_facts X c'' k'' b Hb) 3%nat; intros IB CB' KB'; nd_post). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U2 : c'' = K_BATCH_CLASS -> aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia | | |].
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 _ F1 F2 A24 U2 U0 U0').
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 _ F1 F2 A24 U2 U0 U0').
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          pose proof (undist_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 _ F1 F2 A24 U2 U0 U0') as D. clear -D. lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update_gen L _ m m' MUn WM st st' X X' c''); [exact SHADOW | apply NDS | exact EC3 | exact EC4 | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk''. left.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        split.
        -- subst X'. rewrite (busy_of_xfreeS X (enq_is_app st) k24 c'' k'').
           destruct (negb (enq_is_app st) && (K_BATCH_CLASS =? c'') && (k24 =? k'')) eqn:T1; [| reflexivity].
           destruct (enq_is_app st) eqn:EAx; [cbn in T1; discriminate|]. cbn [negb andb] in T1.
           destruct (Z.eqb_spec K_BATCH_CLASS c'') as [<-|]; [| discriminate]. destruct (Z.eqb_spec k24 k'') as [<-|]; [| discriminate].
           (nd_pre (NEWF eq_refl) 3%nat; intros _ NBk _; nd_post). rewrite NBk. rewrite size_of_class_24. rewrite slot_shadow_bbatch by (clear; change (shlen 8192) with 1024; lia).
           reflexivity.
        -- pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
           apply Kshad.
           ++ rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
           ++ rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
           ++ apply shlen_nonneg. clear -T16; lia.
           ++ rewrite SHE. destruct SC_r as [D|D].
              ** right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
                 pose proof (shad_mono (al_res L) (aslot_addr L c'' k'') ltac:(clear -P5 RSP; lia)) as MM. clear -HH MM SHL. lia.
              ** left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D P6 RI3; unfold K_SPACE_SIZE in *; lia| clear -AL''; Z.div_mod_to_equations; lia] | clear; lia].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) AU ltac:(clear -U0 RI4; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D U0' RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia].
  }
  (* [comment removed for export] *)
  assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st' m' c'').
  { intros c'' Hc''. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post).
    eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | exact EC4 | exact EC2 | |].
    - intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
      assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
      destruct U0 as [U0 U0'].
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) AU ltac:(clear -U0 RI1; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D U0' RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) AU ltac:(clear -FA1 RI1; unfold K_FREEARR_OFF in *; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D FA2 RI2 RI3; unfold K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia]. }
  (* [comment removed for export] *)
  assert (PD : Permutation (sec_chunks_of st') cs).
  { eapply Permutation_trans; [| apply Permutation_sym; exact PCS]. apply (sec_chunks_of_quar_sec st st' mb ms n ELIVE). exact (st_after_enq_qfilt_sec st ch eq_refl). }
  assert (NOTL' : ~ sec_live st' ch) by (unfold sec_live; rewrite ELIVE; exact NOTL).
  assert (LVE : forall j c, nth_error order j = Some c -> j <> i -> (sec_live st' c <-> sec_live st c)) by (intros; unfold sec_live; rewrite ELIVE; reflexivity).
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p.
  pose proof (ao_ptr L ALO) as OP. (pose proof (aobj_int _ _ OP ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OPi OPa [kP OPs]; nd_post). unfold adisj, aobj in D_t_p, D_p_r, D_n_p, D_s_p, OP.   (* [comment removed for export] *)
  assert (HS' : ASEC_of L st' X' m').
  { unfold ASEC_of, ASECc.
    pose proof HS as HS1. (nd_pre HS1 5%nat; intros _ _ _ _ SHZ0; nd_post).
    split; [| split; [| split; [| split]]].
    - (* [comment removed for export] *) unfold asec_wf. rewrite EPA, WP, ENRES, ENSEC.
      split; [exact ALO|]. split; [reflexivity|]. split; [exact WR|]. split; [rewrite (Permutation_length PD); exact WL|]. split; [exact WB|].
      split; [rewrite Forall_forall in WF1 |- *; intros c Hc; apply WF1; eapply Permutation_in; [exact PD| exact Hc]|].
      eapply sec_disjoint_perm; [apply Permutation_sym; exact PD| exact WD].
    - (* [comment removed for export] *) exists order. rewrite ?ENRES, ?ENSEC.
      split; [eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]|].
      unfold K_HIGH_MEM in *.
      split; [| split].
      + eapply u64arr_frame; [exact U64| exact MUn| exact WM|]. rewrite length_map, LENO.
        apply Kobj; [clear -OP OPi OPs WB WR LENO; lia| clear -OP OPi OPs WB WR; lia| clear -WB; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
      + eapply junk_frame; [exact JK| exact MUn| exact WM|]. intros POS.
        apply Kobj; [clear -OP OPi OPs WB WR POS; lia| clear -OP OPi OPs WB WR; lia| clear -WB POS; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
      + intros j c Hj. destruct (Nat.eq_dec j i) as [->|NEji].
        * (* [comment removed for export] *)
          rewrite NTH in Hj. injection Hj as <-. exists false. split; [split; [discriminate| intros Hl; exfalso; exact (NOTL' Hl)]|].
          unfold ch. cbn [asec_chunk]. pose proof CH as CH0. cbn [asec_chunk] in CH0.
          pose proof CH as CH1. unfold ch in CH1. cbn [asec_chunk] in CH1. (nd_pre CH1 5%nat; intros G1 G2 G3 G4 _; nd_post). unfold SEC_UOFF in G1, G2, G3, G4 |- *. rewrite <- ?EUB in *.
          replace (UB - 16 + 16) with UB in FC' by (clear; lia).
          split; [eapply cells_frame; [exact G1| exact MUn| exact WM| cbn; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply junk_frame; [exact G2| exact MUn| exact WM| intros _; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply cells_frame; [exact G3| exact MUn| exact WM| cbn; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply junk_frame; [exact G4| exact MUn| exact WM| intros _; apply Kchunk; clear -EUB MSB; lia]|].
          split; [exists b1, ctx; split; [exact HDR'| split; [exact B1| split; [exact B13| exact CTX]]]|].
          split. { replace (ms - 6144) with (8 + (ms - 6144 - 8)) by (clear; lia). apply junk_merge; [| | clear; lia| clear -NMS N6 NB; lia].
                   - pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
                   - eapply junk_frame; [| exact MUn| exact WM| intros POS; apply Kchunk; clear -EUB MSB POS; lia].
                     exact UJ. }
          split; [eapply fill_frame; [exact S1| exact MUn| exact WM| intros _; apply Kshad; clear -SHLO SHHI SHE MSB; unfold AIMG_HI; Z.div_mod_to_equations; lia]|].
          rewrite (granules_rup n) by (clear -NB; lia). rewrite <- EGQ. unfold sec_user_shadow.
          split; [rewrite (granules_rup n) by (clear -NB; lia); rewrite <- EGQ; exact SH'|].
          eapply fill_frame; [exact S3| exact MUn| exact WM| intros POS; apply Kshad; clear -SHLO SHHI SHE SHL SHP POS MSB; unfold AIMG_HI; Z.div_mod_to_equations; lia].
        * (* [comment removed for export] *)
          (nd_pre (PER j c Hj) 3%nat; intros lvj LVj CHj; nd_post). exists lvj. split; [rewrite (LVE j c Hj NEji); exact LVj|].
          assert (INj : In c order) by (eapply nth_error_In; exact Hj).
          pose proof (proj1 (Forall_forall _ _) WF1o c INj) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
          (nd_pre (sec_wf1_facts' L mb' ms' n' Wc) 12%nat; intros JAL JLO JCE _ _ _ JMSB _ _ _ (JC_t & _ & JC_r & _ & JC_n & JC_st & _) _; nd_post).
          assert (NEc : CSec mb' ms' n' <> ch).
          { intros E. apply NEji. destruct WDo as [ND _]. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
          destruct WDo as [_ DJ].
          destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
          all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
          all: unfold K_HIGH_MEM in JLO, JCE.
          all: (pose proof (ablk_lin _ _ JLO) as ndP__; nd_pre ndP__ 4%nat; intros JL1 JL2 JL3 JL4; nd_post); unfold AIMG_HI in JL1; (pose proof (ablk_int _ _ JLO) as ndP__; nd_pre ndP__ 6%nat; intros kJ KAJ KBJ KEJ KCJ KDJ; nd_post).   (* [comment removed for export] *)
          all: eapply asec_chunk_frameD'; [exact MUn| exact Wc| | | | exists (Z.of_nat j); exact CHj].
          all: try (intros Ad kk Z1 Z2 Z3; apply Kobj; [clear -Z1 Z3 JLO JL1 KAJ KBJ KEJ KCJ KDJ; lia| clear -Z3 JCE; lia| clear -Z2; lia| clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_r; lia| clear -Z1 Z3 JC_n; lia| clear -Z1 Z3 JC_st; lia| clear -Z1 Z3 Dc; lia]).
          all: try (pose proof CHj as CH1; cbn [asec_chunk] in CH1; destruct CH1 as (Hh & _);
                    eapply cells_frame; [exact Hh| exact MUn| exact WM| cbn; apply Kobj; [clear -JLO JL1 JMSB KAJ KBJ KEJ KCJ KDJ; lia| clear -JCE JMSB; lia| clear; lia| clear -JC_t JMSB; lia| clear -JC_r JMSB; lia| clear -JC_n JMSB; lia| clear -JC_st JMSB; lia| clear -Dc JMSB; lia]]).
          -- intros Ad kk Z1 Z2 Z3. apply Kshad; [rewrite shad_div in Z1; unfold ASHOFF, AIMG_HI in *; clear -Z1 JLO JL1; Z.div_mod_to_equations; lia| rewrite shad_div in Z3; unfold ASHOFF in *; clear -Z3 JCE JAL8; Z.div_mod_to_equations; lia| clear -Z2; lia|].
             left. rewrite SHE. pose proof (shad_sep _ _ _ Dc JAL8) as HH. rewrite shlen_div in HH. clear -HH Z3. lia.
          -- intros Ad kk Z1 Z2 Z3. apply Kshad; [rewrite shad_div in Z1; unfold ASHOFF, AIMG_HI in *; clear -Z1 JLO JL1; Z.div_mod_to_equations; lia| rewrite shad_div in Z3; unfold ASHOFF in *; clear -Z3 JCE JAL8; Z.div_mod_to_equations; lia| clear -Z2; lia|].
             right. rewrite SHE. pose proof (shad_sep _ _ _ Dc MAL8) as HH. rewrite shlen_div in HH. clear -HH Z1 SHL. lia.
    - (* [comment removed for export] *) (nd_pre SINST 6%nat; intros I1 [srt I2] I3 I4 I5 I6; nd_post). unfold asec_inst. unfold AINSTANCE in *.
      split; [eapply cells_frame; [exact I1| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [exists srt; eapply cells_frame; [exact I2| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply junk_frame; [exact I3| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply junk_frame; [exact I4| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply cells_frame; [exact I5| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      eapply junk_frame; [exact I6| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia].
    - (* [comment removed for export] *) unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MUn| exact WM|]. intros POS.
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -RSP RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP2. unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *. Z.div_mod_to_equations. lia.
      + clear -POS; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) (al_space_beg L) ltac:(clear -RSP; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D SP2 RSP; unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia| clear -SP3; unfold K_ALIGN in SP3; Z.div_mod_to_equations; lia] | clear; lia].
    - (* [comment removed for export] *) intros x Hx HFh HC.
      assert (HC0 : Forall (fun c => ~ (sec_mb c <= x < sec_mb c + sec_ms c)) cs).
      { rewrite Forall_forall in HC |- *. intros c Hin. apply HC. eapply Permutation_in; [apply Permutation_sym; exact PD| exact Hin]. }
      pose proof INcs as INst.
      pose proof (proj1 (Forall_forall _ _) HC0 ch INst) as NX. unfold ch in NX. cbn [sec_mb sec_ms] in NX.
      unfold K_HIGH_MEM, AIMG_HI, KLS in Hx.   (* [comment removed for export] *)
      assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM in *; clear -Hx; Z.div_mod_to_equations; lia).
      rewrite <- (SHZ0 x ltac:(unfold K_HIGH_MEM; exact Hx) HFh HC0). apply MUn. rewrite wa_unsigned by exact SX.
      eapply (disjoint_outside _ (shad x) 1); [| clear; lia]. apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -Hx; Z.div_mod_to_equations; lia| rewrite shad_div; unfold ASHOFF; pose proof atop_range as AR8; clear -Hx AR8; Z.div_mod_to_equations; lia| clear; lia|].
      rewrite SHE. destruct (Z_lt_le_dec x mb) as [LT|GE].
      + left. rewrite !shad_div. clear -LT MAL8. Z.div_mod_to_equations. lia.
      + right. rewrite !shad_div in *. clear -GE NX SHL MAL8 MSAL. Z.div_mod_to_equations. lia. }
  assert (BL' : ablocks L st' X' LB).
  { eapply ablocks_mono; [exact BL| intros y q Hy _; subst X'; apply In_xfreeS; exact Hy| intros q mb' ms' n' Hl; rewrite ELIVE; exact Hl]. }
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi FKa [kF FBND]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (SHB : 2148239360 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SHE SHL; lia).   (* [comment removed for export] *)
  assert (HFK' : AFK L LB m').
  { eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |].
    - pose proof (ao_dtls L ALO) as DTO. (pose proof (aobj4_int _ DTO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DBND] [jD DIMG]; nd_post). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE, K_HIGH_MEM in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148239360 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
        rewrite SHE. destruct SC_f as [D|D].
        - right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH. clear -HH SHL. lia.
        - left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [exact D| clear -FKO FKi FBND; Z.div_mod_to_equations; lia] | clear; lia]. }
      (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      assert (LSTR : (lst = 0 /\ qsz lst = 8) \/ (al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104 /\ qsz lst = 8192))   (* [comment removed for export] *)
        by (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; split; [exact Z0| apply qsz_eq0; exact Z0]| right; split; [exact F3| split; [exact F4| apply qsz_pos; clear -F3 RES RHI; lia]]]).
      assert (EBR : al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104 /\ qsz eb = 8192) by (destruct EBF as [Z0|(_ & _ & F3 & F4)]; [exfalso; clear -Z0 EBNZ; lia| split; [assumption| split; [assumption| apply qsz_pos; clear -EBNZ; lia]]]).   (* [comment removed for export] *)
      assert (GLRR : gl = lst \/ gl = 0 \/ (al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104))
        by (destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])]; [left; exact Z2| right; left; exact Z2| right; right; split; assumption]).
      (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3 SC_tls; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | idtac]]]]]]]]]]]]]]]]).
      apply Forall_nil. }
  assert (QH : qhdr L ch 0 = UB - 16) by (unfold ch; cbn [qhdr]; unfold PG; rewrite RZ, EUB; clear; lia).
  (* [comment removed for export] *)
  assert (GNB : g_nb g = Z.of_nat (length (a_qglob st))) by reflexivity.
  assert (GFST : g_fst g = qfirst L (q_glob Q)) by reflexivity.
  assert (GQB : g_qb g = a_qglob_bytes st) by reflexivity.
  assert (GFU : g_full g = match a_qglob st with [] => false | _ :: _ => true end) by reflexivity.
  destruct DKP as [MX' DKP'].
  (pose proof (qnum_freeR st ch NUM ltac:(unfold ch; cbn [chunk_size]; clear -NB; lia) NOREC) as ndP__; nd_pre ndP__ 5%nat; intros NUM' NB2a NB2b NB2c NF2; nd_post).
  fold st2 st' in NUM', NB2a, NB2b, NB2c, NF2.
  pose proof (st_after_q st2) as [DRN NDR]. fold st' in DRN, NDR.
  assert (QK' : aquar_glob_const m').
  { split; [| exact MX']. eapply cells_frame; [exact QK | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia. }
  assert (IA' : aintal true m').
  { split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. revert Hj. clear. unfold AIA_MAP1_LEN. intros Hj. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (BLST : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst ->
      abatch_addr L (qb_slot q) + 8192 <= lst \/ lst + 8192 <= abatch_addr L (qb_slot q) \/ lst = 0).
  { intros q Hq NE. destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [right; right; exact Z0|].
    destruct (BDIS q ql Hq ltac:(apply in_or_app; left; exact Hql)) as [E|E]; [exfalso; apply NE; rewrite Eql; exact E| rewrite Eql].
    destruct E as [E|E]; [left; exact E| right; left; exact E]. }
  assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst -> abatch_addr L (qb_slot q) <> gl ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (abatch_addr L (qb_slot q)) 8192).
  { intros q Hq NL NG. (nd_pre (BGEO q Hq) 4%nat; intros _ _ F3 F4; nd_post). pose proof (BLST q Hq NL) as DL.
    assert (DE : eb = lst \/ abatch_addr L (qb_slot q) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot q)).
    { destruct EBK as [E|[EA E]]; [left; exact E| right]. rewrite E.
      destruct (KDIS q Hq EA) as [D|D]; [right; exact D| left; exact D]. }
    assert (DG : gl = lst \/ gl = 0 \/ abatch_addr L (qb_slot q) + 8192 <= gl \/ gl + 8192 <= abatch_addr L (qb_slot q)).
    { destruct GLF as [[_ E]|(_ & _ & [Z0|((qg & Hqg & Eqg) & _)])]; [left; exact E| right; left; exact Z0| right; right].
      destruct (BDIS q qg Hq ltac:(apply in_or_app; right; exact Hqg)) as [E|E]; [exfalso; apply NG; rewrite Eqg; exact E| rewrite Eqg; exact E]. }
    apply Kres; clear -F3 F4 RES RHI DL DE DG; lia. }
  assert (HQ' : AQUAR L st' X' m').
  { subst ek. unfold ek_of in EKP, EK, QC', DKP', EEB, SB1, GDR, GL, GLST.
    destruct (enq_is_app st) eqn:EA; cbn [ek_nb ek_fst ek_lst ek_delta ek_b ek_post ek_pre] in EKP, EK, QC', DKP', EEB, SB1, GDR, GL, GLST.
    - (* [comment removed for export] *)
      (nd_pre EKP 4%nat; intros LB' LA' [bs LJ'] _; nd_post). (nd_pre EK 9%nat; intros _ _ CNT' _ _ _ _ LEN _; nd_post).
      (* [comment removed for export] *)
      pose proof EA as EA0. unfold enq_is_app in EA0. destruct (rev (a_qloc st)) as [|blr rl] eqn:RV; [discriminate|].
      assert (QL : a_qloc st = rev rl ++ [blr]) by (rewrite <- (rev_involutive (a_qloc st)), RV; reflexivity).
      destruct (Z.eqb_spec (b_count blr) Q_BATCH) as [|NFULL]; [discriminate|]. clear EA0.
      set (l := rev rl) in *. set (bl := blr) in *.
      assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL, length_app; cbn; clear; lia).
      assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; clear -LQ; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
      set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
      assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
      assert (LST : List.last (a_qloc st) dummy_batch = bl) by (rewrite QL; apply last_app1). rewrite LST in *.
      assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
      set (bl' := mkABatch (b_count bl + 1) (b_size bl + n) (ch :: b_chunks bl)) in *.
      set (qz' := mkQB (qb_slot qz) (0 :: qb_ks qz)) in *.
      assert (EAPP : enq_app st ch = Some (set_qloc (l ++ [bl']) (a_qloc_bytes st + n) st)).
      { unfold enq_app. rewrite RV. fold bl. replace (b_count bl =? Q_BATCH) with false by (symmetry; apply Z.eqb_neq; exact NFULL).
        subst bl'. reflexivity. }
      assert (Q2 : a_qloc st2 = l ++ [bl'] /\ a_qloc_bytes st2 = a_qloc_bytes st + n /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. cbn. repeat split; reflexivity. }
      (nd_pre Q2 4%nat; intros QL2 QB2 QG2 QGB2; nd_post).
      (* [comment removed for export] *)
      unfold abatches in ABL, ABG. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
      cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
      assert (ABl' : abatches_to L m' l ql (hd 0 (qaddrs L [qz']))).
      { cbn [qaddrs map hd qz' qb_slot]. cbn [qaddrs map hd] in ABl. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
        intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
        assert (NEq : abatch_addr L (qb_slot q) <> lst).
        { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post).
          apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
          unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
        apply BFR; [exact INq | exact NEq |].
        destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post); clear -F3 RES RHI; lia|].
        rewrite Eqg. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post). apply in_split in Hqg. (nd_pre Hqg 3%nat; intros gs1 gs2 EQg; nd_post).
        apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
        pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
        unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      assert (ABz' : abatch_cells L m' bl' qz' 0).
      { unfold abatch_cells. cbv zeta. cbn [qb_slot qb_ks b_size b_count b_chunks bl' qz']. rewrite <- QLST. rewrite qhdrs_cons, map_app. cbn [map qhdr]. rewrite QH.
        split; [exact LB'|]. split; [exact LA'|]. split; [| split; [cbn [length]; rewrite Z4; clear; lia| split; [cbn [length]; rewrite Z5; reflexivity| unfold Q_BATCH in *; clear -CNT' Z6; lia]]].
        exists bs. unfold Q_BATCH_BYTES. exact LJ'. }
      assert (ABL' : abatches_to L m' (l ++ [bl']) (ql ++ [qz']) 0).
      { apply abatches_to_app; [exact LNl|]. split; [exact ABl'|]. cbn. split; [exact ABz'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (ql ++ [qz']) (q_glob Q) true (q_pend Q))).
      { subst X'. unfold xfreeS. apply (qcoupled_app_sec L st X Q mb ms n CP st2 l bl ql qz true 0 QL QQ QL2 QG2). }
      subst qz'.
      destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [DR|NDRN].
      + (* [comment removed for export] *)
        (nd_pre (DRN DR) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        destruct DKP' as [GC' GLN].
        exists (mkQConc [] (q_glob Q ++ (ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}])) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length].
             replace (Z.of_nat (length l + 1)) with (Z.of_nat (length (a_qloc st))) by (rewrite QL, length_app; cbn; reflexivity).
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite qlast_reslot, <- QQ, <- ELST.
             assert (FE : qfirst L (q_glob Q ++ ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}]) = (if g_full g then g_fst g else qfirst L (q_loc Q))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). cbn [app]. rewrite qfirst_reslot, <- QQ. reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite qfirst_reslot, <- QQ.
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; clear -LQg; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
                   set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
                   set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
                   assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
                   rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
                   cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
                   assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
                   rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
                   rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
                   +++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
                       intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQg; apply in_or_app; left; exact Hq).
                       assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
                       { intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                         apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       apply BFR; [exact INq | | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
                       rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                       apply (bslots_nodup_split L st X Q CP ql qz gs1 q (gs2 ++ [qgz])); [rewrite QQ, QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                       pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
                       unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
                   +++ cbn [abatches_to]. split; [| exact I].
                       (* [comment removed for export] *)
                       unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q)) (qaddrs L [])) with (qfirst L (q_loc Q)).
                       assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
                       assert (NGL : abatch_addr L (qb_slot qgz) <> lst).
                       { rewrite QLST. intros E. apply (bslots_nodup_split L st X Q CP ql qz qg qgz []); [rewrite QQ, QQg; rewrite <- ?app_assoc; cbn [app]; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
                         pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity).
                       (nd_pre (BGEO qgz INgz) 4%nat; intros _ _ F3 F4; nd_post). pose proof (BLST qgz INgz NGL) as DL.
                       assert (DE : eb = lst \/ abatch_addr L (qb_slot qgz) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot qgz)).
                       { destruct EBK as [E|[EA' E]]; [left; exact E| discriminate]. }
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI DL DE GLS HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_drain L st2 st' X' (mkQConc (ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}]) (q_glob Q) true (q_pend Q)) true CP2 QL3 QG3).
        * exact NUM'.
      + (* [comment removed for export] *)
        pose proof (NDR NDRN) as EST. 
        assert (GD : g_drain g = false) by (rewrite GDR; apply Z.ltb_ge; rewrite <- QB2; exact NDRN).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        exists (mkQConc (ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}]) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite EST, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [| exact ABL'].
          rewrite length_app, qfirst_reslot, qlast_reslot, <- QQ, <- ELST. cbn [length].
          replace (Z.of_nat (length l + 1)) with (Z.of_nat (length (a_qloc st))) by (rewrite QL, length_app; cbn; reflexivity). exact QC'.
        * split; [rewrite <- GNB, <- GFST, <- GL, <- GQB; exact DKP'|].
          unfold abatches. eapply abatches_to_frame; [exact MUn | exact WM | exact ABG |].
          intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
          assert (NEq : abatch_addr L (qb_slot q) <> lst).
          { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
            apply (bslots_nodup_split L st X Q CP ql qz gs1 q gs2); [rewrite QQ, EQg; rewrite <- ?app_assoc; cbn [app]; reflexivity|].
            pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
            unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
          apply BFR; [exact INq | exact NEq | rewrite EGL; unfold dk_glst; rewrite GD; exact NEq].
        * first [rewrite EST | idtac]. exact CP2.
        * first [rewrite <- EST | idtac]. exact NUM'.
    - (* [comment removed for export] *)
      (nd_pre (NEWF eq_refl) 8%nat; intros NK24 NB24 KK24 NIB JK24 FK CIN POS; nd_post).
      (nd_pre EKP 6%nat; intros C24' [stj' SJ'] NBc NAc [bs NJc] OLDc; nd_post).
      pose proof EAPP0 as EAPP.
      set (nbt := mkABatch 1 (n + 8192) [ch]) in *.
      set (qn := mkQB k24 [0]) in *.
      assert (Q2 : a_qloc st2 = a_qloc st ++ [nbt] /\ a_qloc_bytes st2 = a_qloc_bytes st + (n + 8192) /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. (pose proof (enq_new_core ch st) as ndP__; nd_pre ndP__ 7%nat; intros _ E1 E2 _ E3 E4 _; nd_post).
        rewrite E1, E2, E3, E4. subst nbt. unfold ch. cbn [a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_live chunk_size]. fold ch. unfold Q_BATCH_BYTES.
        split; [reflexivity|]. split; [clear; lia|]. split; reflexivity. }
      (nd_pre Q2 4%nat; intros QL2 QB2 QG2 QGB2; nd_post).
      assert (FSTE : (if match a_qloc st with [] => false | _ :: _ => true end then qfirst L (q_loc Q) else abatch_addr L k24) = qfirst L (q_loc Q ++ [qn])).
      { rewrite qfirst_app_r. subst qn; cbn [qb_slot]. generalize LN1. clear. generalize (a_qloc st) (q_loc Q).
        intros [|x1 r1] [|x2 r2] LL; cbn in LL; first [reflexivity | discriminate]. }
      rewrite FSTE in QC'. rewrite FSTE in DKP'.
      assert (QLST' : qlast L (q_loc Q ++ [qn]) = abatch_addr L k24) by (subst qn; apply qlast_app1).
      (* [comment removed for export] *)
      assert (GNL : forall q, In q (q_glob Q) -> abatch_addr L (qb_slot q) <> lst).
      { intros q Hq E. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
        destruct LSTF as [Z0|((q' & Hq' & Eq') & _)].
        - (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post). clear -F3 RES RHI E Z0. lia.
        - apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post). apply in_split in Hq'. (nd_pre Hq' 3%nat; intros qs1 qs2 EQl; nd_post).
          apply (bslots_nodup_split L st X Q CP qs1 q' (qs2 ++ gs1) q gs2); [rewrite EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP q' ltac:(apply in_or_app; left; rewrite EQl; apply in_or_app; right; left; reflexivity)).
          rewrite Eq' in E. unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      (* [comment removed for export] *)
      assert (ABO' : abatches_to L m' (a_qloc st) (q_loc Q) (abatch_addr L k24)).
      { destruct (a_qloc st) as [|b0 l0] eqn:QL0.
        - replace (q_loc Q) with (@nil qbatchc) by (clear -LN1; destruct (q_loc Q); [reflexivity| cbn in LN1; discriminate]). exact I.
        - cbv iota beta in OLDc. destruct OLDc as [OLD1 OLD2]. rewrite <- QL0 in *.
          assert (LNE : a_qloc st <> []) by (rewrite QL0; discriminate).
          assert (QL : a_qloc st = removelast (a_qloc st) ++ [List.last (a_qloc st) dummy_batch]) by (apply app_removelast_last; exact LNE).
          assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL0; cbn; clear; lia).
          assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; clear -LQ; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
          set (l := removelast (a_qloc st)) in *. set (bl := List.last (a_qloc st) dummy_batch) in *.
          set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
          assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
          assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
          assert (FULL : b_count bl = Q_BATCH).
          { pose proof EA as EA0. unfold enq_is_app in EA0. rewrite QL, rev_unit in EA0. cbv iota beta in EA0.
            revert EA0. destruct (Z.eqb_spec (b_count bl) Q_BATCH) as [E|NE]; intros EA0; [exact E| discriminate]. }
          unfold abatches in ABL. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
          cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
          rewrite QL, QQ. apply abatches_to_app; [exact LNl|]. split.
          + cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
            intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
            assert (NEq : abatch_addr L (qb_slot q) <> lst).
            { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post).
              apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
              pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
              unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
            apply BFR; [exact INq | exact NEq |].
            destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post); clear -F3 RES RHI; lia|].
            rewrite Eqg. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post). apply in_split in Hqg. (nd_pre Hqg 3%nat; intros gs1 gs2 EQg; nd_post).
            apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
            pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
            unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
          + cbn [abatches_to]. split; [| exact I].
            unfold abatch_cells. cbv zeta. change (hd (abatch_addr L k24) (qaddrs L [])) with (abatch_addr L k24). rewrite <- QLST.
            split; [rewrite FULL; exact OLD1|]. split; [exact OLD2|]. split; [| split; [exact Z4| split; [exact Z5| exact Z6]]].
            rewrite FULL. replace (Q_BATCH_BYTES - 24 - 8 * Q_BATCH) with 0 by reflexivity. unfold Q_BATCH. apply junk_nil; (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [clear -Z0; lia | atop_facts; clear -F3 F4 RES RHI; lia]). }
      (* [comment removed for export] *)
      assert (ABN' : abatch_cells L m' nbt qn 0).
      { unfold abatch_cells. cbv zeta. subst nbt qn. cbn [qb_slot qb_ks b_size b_count b_chunks]. rewrite qhdrs_cons. cbn [qhdrs app map qhdr]. rewrite QH.
        split; [exact NBc|]. split; [exact NAc|]. split; [exists bs; unfold Q_BATCH_BYTES; exact NJc|]. split; [reflexivity|]. split; [reflexivity| unfold Q_BATCH; clear; lia]. }
      assert (ABL' : abatches_to L m' (a_qloc st ++ [nbt]) (q_loc Q ++ [qn]) 0).
      { apply abatches_to_app; [exact LN1|]. split; [cbn [qaddrs map hd]; subst qn; cbn [qb_slot]; exact ABO'|]. cbn [abatches_to]. split; [exact ABN'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q))).
      { subst X' qn nbt. rewrite ?EA. unfold xfreeS. cbv iota beta.
        apply (qcoupled_new_sec L st X Q mb ms n WF CP st2 k24 (c_count (get_cls st K_BATCH_CLASS)) (n + 8192) true 0 eq_refl POS NK24 QL2 QG2). }
      destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [DR|NDRN].
      + (* [comment removed for export] *)
        (nd_pre (DRN DR) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        destruct DKP' as [GC' GLN].
        exists (mkQConc [] (q_glob Q ++ (q_loc Q ++ [qn])) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite QLST'.
             assert (FE : qfirst L (q_glob Q ++ q_loc Q ++ [qn]) = (if g_full g then g_fst g else qfirst L (q_loc Q ++ [qn]))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate).
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; clear -LQg; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
                   set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
                   set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
                   assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
                   rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
                   cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
                   assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
                   rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
                   rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
                   +++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
                       intros q Hq. assert (INg : In q (q_glob Q)) by (rewrite QQg; apply in_or_app; left; exact Hq).
                       assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INg).
                       assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
                       { intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
                         apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       apply BFR; [exact INq | exact (GNL q INg) | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
                   +++ cbn [abatches_to]. split; [| exact I].
                       (* [comment removed for export] *)
                       unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q ++ [qn])) (qaddrs L [])) with (qfirst L (q_loc Q ++ [qn])).
                       assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
                       assert (INgzg : In qgz (q_glob Q)) by (rewrite QQg; apply in_or_app; right; left; reflexivity).
                       assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INgzg).
                       pose proof (GNL qgz INgzg) as NGL.
                       (nd_pre (BGEO qgz INgz) 4%nat; intros _ _ F3 F4; nd_post). pose proof (BLST qgz INgz NGL) as DL.
                       pose proof (KDIS qgz INgz eq_refl) as DE.
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI DL DE EEB GLS HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_drain L st2 st' X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q)) true CP2 QL3 QG3).
        * exact NUM'.
      + (* [comment removed for export] *)
        pose proof (NDR NDRN) as EST.
        assert (GD : g_drain g = false) by (rewrite GDR; apply Z.ltb_ge; rewrite <- QB2; exact NDRN).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        exists (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite EST, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [| exact ABL'].
          rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1. rewrite QLST'. exact QC'.
        * split; [rewrite <- GNB, <- GFST, <- GL, <- GQB; exact DKP'|].
          unfold abatches. eapply abatches_to_frame; [exact MUn | exact WM | exact ABG |].
          intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
          apply BFR; [exact INq | exact (GNL q Hq) | rewrite EGL; unfold dk_glst; rewrite GD; exact (GNL q Hq)].
        * first [rewrite EST | idtac]. exact CP2.
        * first [rewrite <- EST | idtac]. exact NUM'. }
  (* [comment removed for export] *)
  assert (HBK : forall blk, In blk LB -> disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (ab_addr blk) (ab_size blk)).
  { intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size].
    - destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb' & msz' & Lp & EUA & Gs)].
      + destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        pose proof (busy_of_In_nodup L st X b WF Hb) as BOF.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
        (pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (DQ : forall q', In q' (q_loc Q ++ q_glob Q) ->
            aslot_addr L cb kb + size_of_class cb <= abatch_addr L (qb_slot q') \/ abatch_addr L (qb_slot q') + 8192 <= aslot_addr L cb kb).
        { intros q' Hq'. (nd_pre (bslot_busy L st X Q CP q' Hq') 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> qb_slot q').
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2.
            pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq, <- E1, <- E2, BOF in BY. injection BY as EE. subst yq. rewrite Sb in Syq. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS (qb_slot q') ALO WF HCb (K24) HKb (bslot_range L st X Q WF CP q' Hq') NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DK24 : enq_is_app st = false -> aslot_addr L cb kb + size_of_class cb <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= aslot_addr L cb kb).
        { intros EAx. (nd_pre (NEWF EAx) 4%nat; intros _ NBk KK _; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> k24).
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2. rewrite <- E1, <- E2, BOF in NBk. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS k24 ALO WF HCb (K24) HKb KK NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DL : lst = 0 \/ aslot_addr L cb kb + size_of_class cb <= lst \/ lst + 8192 <= aslot_addr L cb kb).
        { destruct LSTF as [Z0|((q' & Hq' & Eq') & _)]; [left; exact Z0| right]. rewrite Eq'. apply DQ. apply in_or_app; left; exact Hq'. }
        assert (DE : eb = lst \/ aslot_addr L cb kb + size_of_class cb <= eb \/ eb + 8192 <= aslot_addr L cb kb).
        { destruct EBK as [E|[EAx E]]; [left; exact E| right]. rewrite E. exact (DK24 EAx). }
        assert (DG : gl = lst \/ gl = 0 \/ aslot_addr L cb kb + size_of_class cb <= gl \/ gl + 8192 <= aslot_addr L cb kb).
        { destruct GLF as [[_ E]|(_ & _ & [Z0|((q' & Hq' & Eq') & _)])]; [left; exact E| right; left; exact Z0| right; right].
          rewrite Eq'. apply DQ. apply in_or_app; right; exact Hq'. }
        apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia
                    | clear -DL FIT P5 RSP RES RHI; lia | clear -DE DL FIT P5 RSP RES RHI; lia | clear -DG DL FIT P5 RSP RES RHI; lia].
      + (* [comment removed for export] *)
        assert (NEc : CSec mb' msz' n' <> ch).
        { intros E. apply NOTL. exists q. rewrite <- E. exact Lp. }
        assert (INc : In (CSec mb' msz' n') cs) by (eapply Permutation_in; [apply Permutation_sym; exact PCS| right; eapply live_sec_in; exact Lp]).
        pose proof INcs as INs.
        destruct WD as [_ DJ]. destruct (DJ _ _ INc INs NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
        all: cbn [sec_wf1] in Gs; (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        all: pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF; subst A'; unfold SEC_UOFF, K_HIGH_MEM in *.
        all: unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        all: apply Kobj; [clear -Gs2 Gs4 Gs5 SF; lia| clear -Gs3 Gs4 Gs5 SF; lia| clear -Gs5; lia| clear -Gs4 Gs5 SF Ct; lia| clear -Gs4 Gs5 SF Cr; lia| clear -Gs4 Gs5 SF Cn; lia| clear -Gs4 Gs5 SF Cs; lia| clear -Gs4 Gs5 SF Dc; lia].
    - (nd_pre (FKD cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post). unfold K_HIGH_MEM in *.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia | clear -K1 K3 SC_f; lia]. }
  (* [comment removed for export] *)
  assert (TLSK : forall TA tk, ATPv + -200 <= TA -> TA + tk <= ATPv + 312 -> 0 <= tk ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) TA tk).
  { intros TA tk TH1 TH2 TH3. pose proof ATPv_img as TI. apply Kimg; clear -TH1 TH2 TH3 TI; unfold AIMG_HI; lia. }
  assert (TLSS : forall a', ATPv + -200 <= a' < ATPv + 312 ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros a' Ha'. pose proof ATPv_img as TI. apply Klow; clear -Ha' TI; try (rewrite shad_div; unfold ASHOFF); try Z.div_mod_to_equations; lia. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros cls FA sz Hin a' Ha'.
    (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). unfold K_HIGH_MEM in *.
    assert (FAL8 : al_fake L mod 8 = 0) by (destruct FKO as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
    apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
    rewrite SHE. destruct SC_f as [D|D].
    - right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
      pose proof (shad_mono (al_fake L) a' ltac:(clear -K1 Ha'; lia)) as MM. clear -HH MM SHL. lia.
    - left. pose proof (shad_sep _ _ _ D FAL8) as HH. rewrite (shad_div a'), (shad_div (al_fake L)), shlen_div in *.
      clear -HH Ha' K3 FAL8. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split.
  { eapply (aheap_pres_freeS CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact TLSK | exact TLSS | apply Klow; unfold AIMSH_LO, AIMSH_LEN; clear; lia
      | rewrite <- (ao_ahm_eq L ALO); unfold AAHM_SZ; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI;
      pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; pose proof (ad_ahm_nodes L ALO) as DA3; pose proof (ad_ahm_store L ALO) as DA4;
      (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ SC_ahm; nd_post);
      unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OAH, OAHI, DA1, DA2, DA3, DA4; apply Kobj; clear -OAH OAHI DA1 DA2 DA3 DA4 SC_ahm; lia]. }
  split; [exact ALO|].
  split. { (pose proof ARNG as ndP__; nd_pre ndP__ 14%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 RCl RPA RSC RPSH RTLS; nd_post).
           unfold arng. repeat (split; [assumption|]). split; [| split; [rewrite ENRES; exact RPA| split; [eapply RSEC_perm; [apply Permutation_sym; exact PD| exact RSCS]| split; [exact RPSH | exact RTLS]]]].
           intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24a, M24d; exact (RCl K_BATCH_CLASS Hc')| rewrite (GCo' c' NE); exact (RCl c' Hc')]. }
  split; [| exact HFK'].
  exists X'. split; [| exact BL'].
  split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
  split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3'].
Qed.
End Zd1.
#[using="HL CI_OK"] Theorem store_freeRS : ltac:(let t := eval cbv delta [store_freeRS__stmt] in store_freeRS__stmt in exact t).
Proof. exact store_freeRS__body. Qed.
End S.
End CANSEC1.
End TwB.
End ASF_storeR.
