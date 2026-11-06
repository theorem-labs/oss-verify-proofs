(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AProto AMalloc_iface AFake_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Import Drv_ifaceA GStatKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition cg_okb (g : Z * Z) : bool := (0x10000 <=? fst g) && (fst g + snd g <=? 0x603000) && (0 <? snd g).
Lemma client_globals_ok : forall g, In g client_globals -> 0x10000 <= fst g /\ fst g + snd g <= 0x603000 /\ 0 < snd g.
Proof.
  assert (C : forallb cg_okb client_globals = true) by (vm_compute; reflexivity).
  intros g Hg. pose proof (proj1 (forallb_forall _ _) C g Hg) as K. unfold cg_okb in K.
  apply andb_prop in K as [K K3]. apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2. apply Z.ltb_lt in K3. auto.
Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Statics.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).

  (* [comment removed for export] *)
  #[using="Type"] Lemma img_shadow_window : forall lo hi sa, 0x10000 <= lo -> hi <= 0x603000 -> lo < hi -> shad lo <= sa <= shad (hi - 1) ->
    AIMSH_LO <= sa < AIMSH_LO + AIMSH_LEN.
  Proof. intros lo hi sa H1 H2 H3 Hs. rewrite !shad_div in Hs. change AsanEmbed.ASHOFF with 2147450880 in Hs. unfold AIMSH_LO, AIMSH_LEN. Z.div_mod_to_equations. lia. Qed.

  Definition win_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop := AIMSH_LO <= a < AIMSH_LO + AIMSH_LEN.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition globals_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop :=
    wr_at asegs m 0x7fffa000 779776 /\ Forall (fun g => unpoisoned m (fst g) (fst g + snd g)) client_globals.
  Definition globals_comp : gcomp := mkGC globals_P win_dom.

  #[using="AF"] Lemma globals_ok : gcomp_ok AI globals_comp.
  Proof.
    constructor; cbn [gc_P gc_dom globals_comp]; unfold win_dom.
    - intros L RNG RNG' s s' FB m m' (W & U) _ AG _ _ _. split.
      + eapply agrees_wr_at; [exact AG| exact W|]. intros a Ha. unfold AIMSH_LO, AIMSH_LEN. lia.
      + apply Forall_forall. intros g Hg. pose proof (proj1 (Forall_forall _ _) U g Hg) as Ug. (nd_pre (client_globals_ok g Hg) 3%nat; intros G1 G2 G3; nd_post).
        eapply unpoisoned_agree; [exact Ug|]. intros sa Hs.
        pose proof (img_shadow_window (fst g) (fst g + snd g) sa G1 G2 ltac:(lia) Hs) as WIN.
        apply AG; [unfold AIMSH_LO, AIMSH_LEN in WIN; lia| exact WIN].
    - intros L RNG s FB m LB SP a _ _ _ _ Da. right. right. left. exact Da.
    - intros L RNG s CL FB FL m a AH _ _ Da. eapply (imsh_not_client AI AF); [exact AH| exact Da].
    - intros L s FB a Da. exact (imsh_not_drv a Da).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition stdinp_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop := unpoisoned m STDIN_P (STDIN_P + 8).
  Definition stdinp_comp : gcomp := mkGC stdinp_P win_dom.

  #[using="AF"] Lemma stdinp_ok : gcomp_ok AI stdinp_comp.
  Proof.
    constructor; cbn [gc_P gc_dom stdinp_comp]; unfold win_dom, stdinp_P.
    - intros L RNG RNG' s s' FB m m' U _ AG _ _ _. eapply unpoisoned_agree; [exact U|]. intros sa Hs.
      pose proof (img_shadow_window STDIN_P (STDIN_P + 8) sa ltac:(unfold STDIN_P; lia) ltac:(unfold STDIN_P; lia) ltac:(lia) Hs) as WIN.
      apply AG; [unfold AIMSH_LO, AIMSH_LEN in WIN; lia| exact WIN].
    - intros L RNG s FB m LB SP a _ _ _ _ Da. right. right. left. exact Da.
    - intros L RNG s CL FB FL m a AH _ _ Da. eapply (imsh_not_client AI AF); [exact AH| exact Da].
    - intros L s FB a Da. exact (imsh_not_drv a Da).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition stacksh_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop :=
    al_top L mod 4096 = 0 /\ ATOP + 4096 <= al_top L <= 2^47
    /\ unpoisoned m (ATOP + 4096) (al_top L)
    /\ wr_at asegs m (shad (ATOP + 4096)) (shad (al_top L) - shad (ATOP + 4096))
    /\ rng RNG (shad (ATOP + 4096)) (shad (al_top L) - shad (ATOP + 4096)).
  Definition stacksh_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop := shad (ATOP + 4096) <= a < shad (al_top L) /\ al_top L <= 2^47.
  Definition stacksh_comp : gcomp := mkGC stacksh_P stacksh_dom.

  #[using="Type"] Lemma stacksh_band : forall L a, shad (ATOP + 4096) <= a < shad (al_top L) -> al_top L <= 2^47 ->
    ATOP / 8 + 2147450880 <= a < 0x10007fff8000 /\ ATOP <= 8 * (a - ASHOFF) < 2^47.
  Proof.
    intros L a Ha H47. rewrite !shad_div in Ha. change AsanEmbed.ASHOFF with 2147450880 in *. pose proof atop_range as AR. pose proof ATOP_pg as PG.
    change (2^47) with 140737488355328 in *. clear - Ha H47 AR PG. Z.div_mod_to_equations. lia.
  Qed.

  #[using="AF"] Lemma stacksh_ok : gcomp_ok AI stacksh_comp.
  Proof.
    constructor; cbn [gc_P gc_dom stacksh_comp]; unfold stacksh_dom.
    - intros L RNG RNG' s s' FB m m' (T1 & T2 & U & W & R) FP AG _ _ _. pose proof atop_range as AR. pose proof ATOP_pg as PG.
      split; [exact T1|]. split; [exact T2|]. split.
      { eapply unpoisoned_agree; [exact U|]. intros sa Hs. change (2^47) with 140737488355328 in T2. apply AG.
        - rewrite !shad_div in Hs. change AsanEmbed.ASHOFF with 2147450880 in Hs. clear - Hs T2 AR. Z.div_mod_to_equations. lia.
        - split; [| change (2^47) with 140737488355328; lia]. rewrite !shad_div in *. clear - Hs T1 T2 AR PG. Z.div_mod_to_equations. lia. }
      split; [| eapply rng_fp_le; [exact FP| exact R]].
      eapply agrees_wr_at; [exact AG| exact W|]. intros a Ha. split; [lia| exact (proj2 T2)].
    - intros L RNG s FB m LB SP a _ _ _ Ha [Da D47]. left. right. right. right.
      destruct (stacksh_band L a Da D47) as [_ B]. exists (8 * (a - ASHOFF)). split; [left; exact B| symmetry; apply shad_unshad].
    - intros L RNG s CL FB FL m a AH _ Ha [Da D47]. eapply (stksh_not_client AI AF); [exact AH| exact (proj1 (stacksh_band L a Da D47))].
    - intros L s FB a [Da D47] [D|D]; destruct (stacksh_band L a Da D47) as [B _]; pose proof atop_range as AR.
      + unfold READ_STAGE in D. clear - D B AR. Z.div_mod_to_equations. lia.
      + pose proof ATPv_sh as TS. unfold ATP in D. clear - D B AR TS. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma stacksh_use : forall L RNG s FB m A n, stacksh_P L RNG s FB m -> ATOP + 4096 <= A -> 0 <= n -> A + n <= al_top L ->
    unpoisoned m A (A + n) /\ arenaA RNG m A n.
  Proof.
    intros L RNG s FB m A n (T1 & T2 & U & W & R) HA Hn HT. pose proof atop_range as AR. pose proof ATOP_pg as PG. change (2^47) with 140737488355328 in T2.
    split; [eapply unpoisoned_sub; [exact U| lia| lia]|].
    exists (64 * (A / 64)), (64 * ((A + n + 63) / 64)). unfold KEND.
    split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
    split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|]. split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
    split; [Z.div_mod_to_equations; lia|]. split; [clear - HT T1 T2; Z.div_mod_to_equations; lia|].
    assert (SUB : shad (ATOP + 4096) <= shad (64 * (A / 64)) /\ shad (64 * ((A + n + 63) / 64)) <= shad (al_top L) /\ shad (64 * (A / 64)) <= shad (64 * ((A + n + 63) / 64))).
    { rewrite !shad_div. clear - HA Hn HT T1 T2 AR PG. Z.div_mod_to_equations. lia. }
    split; [eapply wr_at_sub; [exact W| lia| lia]| eapply rng_sub; [exact R| lia| lia]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Laws.
    Variable cs : list gcomp.
    Hypothesis IN_GLOBALS : In globals_comp cs.
    Hypothesis IN_STDINP : In stdinp_comp cs.
    Hypothesis IN_STACKSH : In stacksh_comp cs.

    #[using="IN_GLOBALS"] Lemma GS_globals : forall L RNG (s : PS) FB (m : mem), GSTAT_of cs L RNG s FB m ->
      wr_at asegs m 0x7fffa000 779776 /\ Forall (fun g => unpoisoned m (fst g) (fst g + snd g)) client_globals.
    Proof. intros L RNG s FB m [_ GC]. exact (gconj_In _ _ _ _ _ _ _ GC IN_GLOBALS). Qed.
    #[using="IN_STDINP"] Lemma GS_stdin_unp : forall L RNG (s : PS) FB (m : mem), GSTAT_of cs L RNG s FB m -> unpoisoned m STDIN_P (STDIN_P + 8).
    Proof. intros L RNG s FB m [_ GC]. exact (gconj_In _ _ _ _ _ _ _ GC IN_STDINP). Qed.
    #[using="IN_STACKSH"] Lemma GS_stack : forall L RNG (s : PS) FB (m : mem) A n, GSTAT_of cs L RNG s FB m -> ATOP + 4096 <= A -> 0 <= n -> A + n <= al_top L ->
      unpoisoned m A (A + n) /\ arenaA RNG m A n.
    Proof. intros L RNG s FB m A n [_ GC]. exact (stacksh_use L RNG s FB m A n (gconj_In _ _ _ _ _ _ _ GC IN_STACKSH)). Qed.
  End Laws.
End Statics.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition cg_okb (g : Z * Z) : bool := (0x10000 <=? fst g) && (fst g + snd g <=? 0x604000) && (0 <? snd g).
Lemma client_globals_ok : forall g, In g client_globals -> 0x10000 <= fst g /\ fst g + snd g <= 0x604000 /\ 0 < snd g.
Proof.
  assert (C : forallb cg_okb client_globals = true) by (vm_compute; reflexivity).
  intros g Hg. pose proof (proj1 (forallb_forall _ _) C g Hg) as K. unfold cg_okb in K.
  apply andb_prop in K as [K K3]. apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2. apply Z.ltb_lt in K3. auto.
Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Statics.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).

  (* [comment removed for export] *)
  #[using="Type"] Lemma img_shadow_window : forall lo hi sa, 0x10000 <= lo -> hi <= 0x604000 -> lo < hi -> shad lo <= sa <= shad (hi - 1) ->
    AIMSH_LO <= sa < AIMSH_LO + AIMSH_LEN.
  Proof. intros lo hi sa H1 H2 H3 Hs. rewrite !shad_div in Hs. change AsanEmbed.ASHOFF with 2147450880 in Hs. unfold AIMSH_LO, AIMSH_LEN. Z.div_mod_to_equations. lia. Qed.

  Definition win_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop := AIMSH_LO <= a < AIMSH_LO + AIMSH_LEN.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition globals_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop :=
    wr_at asegs m 0x7fffa000 780288 /\ Forall (fun g => unpoisoned m (fst g) (fst g + snd g)) client_globals.
  Definition globals_comp : gcomp := mkGC globals_P win_dom.

  #[using="AF"] Lemma globals_ok : gcomp_ok AI globals_comp.
  Proof.
    constructor; cbn [gc_P gc_dom globals_comp]; unfold win_dom.
    - intros L RNG RNG' s s' FB m m' (W & U) _ AG _ _ _. split.
      + eapply agrees_wr_at; [exact AG| exact W|]. intros a Ha. unfold AIMSH_LO, AIMSH_LEN. lia.
      + apply Forall_forall. intros g Hg. pose proof (proj1 (Forall_forall _ _) U g Hg) as Ug. (nd_pre (client_globals_ok g Hg) 3%nat; intros G1 G2 G3; nd_post).
        eapply unpoisoned_agree; [exact Ug|]. intros sa Hs.
        pose proof (img_shadow_window (fst g) (fst g + snd g) sa G1 G2 ltac:(lia) Hs) as WIN.
        apply AG; [unfold AIMSH_LO, AIMSH_LEN in WIN; lia| exact WIN].
    - intros L RNG s FB m LB SP a _ _ _ _ Da. right. right. left. exact Da.
    - intros L RNG s CL FB FL m a AH _ _ Da. eapply (imsh_not_client AI AF); [exact AH| exact Da].
    - intros L s FB a Da. exact (imsh_not_drv a Da).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition stdinp_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop := unpoisoned m STDIN_P (STDIN_P + 8).
  Definition stdinp_comp : gcomp := mkGC stdinp_P win_dom.

  #[using="AF"] Lemma stdinp_ok : gcomp_ok AI stdinp_comp.
  Proof.
    constructor; cbn [gc_P gc_dom stdinp_comp]; unfold win_dom, stdinp_P.
    - intros L RNG RNG' s s' FB m m' U _ AG _ _ _. eapply unpoisoned_agree; [exact U|]. intros sa Hs.
      pose proof (img_shadow_window STDIN_P (STDIN_P + 8) sa ltac:(unfold STDIN_P; lia) ltac:(unfold STDIN_P; lia) ltac:(lia) Hs) as WIN.
      apply AG; [unfold AIMSH_LO, AIMSH_LEN in WIN; lia| exact WIN].
    - intros L RNG s FB m LB SP a _ _ _ _ Da. right. right. left. exact Da.
    - intros L RNG s CL FB FL m a AH _ _ Da. eapply (imsh_not_client AI AF); [exact AH| exact Da].
    - intros L s FB a Da. exact (imsh_not_drv a Da).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition stacksh_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop :=
    al_top L mod 4096 = 0 /\ ATOP + 4096 <= al_top L <= 2^47
    /\ unpoisoned m (ATOP + 4096) (al_top L)
    /\ wr_at asegs m (shad (ATOP + 4096)) (shad (al_top L) - shad (ATOP + 4096))
    /\ rng RNG (shad (ATOP + 4096)) (shad (al_top L) - shad (ATOP + 4096)).
  Definition stacksh_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop := shad (ATOP + 4096) <= a < shad (al_top L) /\ al_top L <= 2^47.
  Definition stacksh_comp : gcomp := mkGC stacksh_P stacksh_dom.

  #[using="Type"] Lemma stacksh_band : forall L a, shad (ATOP + 4096) <= a < shad (al_top L) -> al_top L <= 2^47 ->
    ATOP / 8 + 2147450880 <= a < 0x10007fff8000 /\ ATOP <= 8 * (a - ASHOFF) < 2^47.
  Proof.
    intros L a Ha H47. rewrite !shad_div in Ha. change AsanEmbed.ASHOFF with 2147450880 in *. pose proof atop_range as AR. pose proof ATOP_pg as PG.
    change (2^47) with 140737488355328 in *. clear - Ha H47 AR PG. Z.div_mod_to_equations. lia.
  Qed.

  #[using="AF"] Lemma stacksh_ok : gcomp_ok AI stacksh_comp.
  Proof.
    constructor; cbn [gc_P gc_dom stacksh_comp]; unfold stacksh_dom.
    - intros L RNG RNG' s s' FB m m' (T1 & T2 & U & W & R) FP AG _ _ _. pose proof atop_range as AR. pose proof ATOP_pg as PG.
      split; [exact T1|]. split; [exact T2|]. split.
      { eapply unpoisoned_agree; [exact U|]. intros sa Hs. change (2^47) with 140737488355328 in T2. apply AG.
        - rewrite !shad_div in Hs. change AsanEmbed.ASHOFF with 2147450880 in Hs. clear - Hs T2 AR. Z.div_mod_to_equations. lia.
        - split; [| change (2^47) with 140737488355328; lia]. rewrite !shad_div in *. clear - Hs T1 T2 AR PG. Z.div_mod_to_equations. lia. }
      split; [| eapply rng_fp_le; [exact FP| exact R]].
      eapply agrees_wr_at; [exact AG| exact W|]. intros a Ha. split; [lia| exact (proj2 T2)].
    - intros L RNG s FB m LB SP a _ _ _ Ha [Da D47]. left. right. right. right.
      destruct (stacksh_band L a Da D47) as [_ B]. exists (8 * (a - ASHOFF)). split; [left; exact B| symmetry; apply shad_unshad].
    - intros L RNG s CL FB FL m a AH _ Ha [Da D47]. eapply (stksh_not_client AI AF); [exact AH| exact (proj1 (stacksh_band L a Da D47))].
    - intros L s FB a [Da D47] [D|D]; destruct (stacksh_band L a Da D47) as [B _]; pose proof atop_range as AR.
      + unfold READ_STAGE in D. clear - D B AR. Z.div_mod_to_equations. lia.
      + pose proof ATPv_sh as TS. unfold ATP in D. clear - D B AR TS. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma stacksh_use : forall L RNG s FB m A n, stacksh_P L RNG s FB m -> ATOP + 4096 <= A -> 0 <= n -> A + n <= al_top L ->
    unpoisoned m A (A + n) /\ arenaA RNG m A n.
  Proof.
    intros L RNG s FB m A n (T1 & T2 & U & W & R) HA Hn HT. pose proof atop_range as AR. pose proof ATOP_pg as PG. change (2^47) with 140737488355328 in T2.
    split; [eapply unpoisoned_sub; [exact U| lia| lia]|].
    exists (64 * (A / 64)), (64 * ((A + n + 63) / 64)). unfold KEND.
    split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
    split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|]. split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
    split; [Z.div_mod_to_equations; lia|]. split; [clear - HT T1 T2; Z.div_mod_to_equations; lia|].
    assert (SUB : shad (ATOP + 4096) <= shad (64 * (A / 64)) /\ shad (64 * ((A + n + 63) / 64)) <= shad (al_top L) /\ shad (64 * (A / 64)) <= shad (64 * ((A + n + 63) / 64))).
    { rewrite !shad_div. clear - HA Hn HT T1 T2 AR PG. Z.div_mod_to_equations. lia. }
    split; [eapply wr_at_sub; [exact W| lia| lia]| eapply rng_sub; [exact R| lia| lia]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Laws.
    Variable cs : list gcomp.
    Hypothesis IN_GLOBALS : In globals_comp cs.
    Hypothesis IN_STDINP : In stdinp_comp cs.
    Hypothesis IN_STACKSH : In stacksh_comp cs.

    #[using="IN_GLOBALS"] Lemma GS_globals : forall L RNG (s : PS) FB (m : mem), GSTAT_of cs L RNG s FB m ->
      wr_at asegs m 0x7fffa000 780288 /\ Forall (fun g => unpoisoned m (fst g) (fst g + snd g)) client_globals.
    Proof. intros L RNG s FB m [_ GC]. exact (gconj_In _ _ _ _ _ _ _ GC IN_GLOBALS). Qed.
    #[using="IN_STDINP"] Lemma GS_stdin_unp : forall L RNG (s : PS) FB (m : mem), GSTAT_of cs L RNG s FB m -> unpoisoned m STDIN_P (STDIN_P + 8).
    Proof. intros L RNG s FB m [_ GC]. exact (gconj_In _ _ _ _ _ _ _ GC IN_STDINP). Qed.
    #[using="IN_STACKSH"] Lemma GS_stack : forall L RNG (s : PS) FB (m : mem) A n, GSTAT_of cs L RNG s FB m -> ATOP + 4096 <= A -> 0 <= n -> A + n <= al_top L ->
      unpoisoned m A (A + n) /\ arenaA RNG m A n.
    Proof. intros L RNG s FB m A n [_ GC]. exact (stacksh_use L RNG s FB m A n (gconj_In _ _ _ _ _ _ _ GC IN_STACKSH)). Qed.
  End Laws.
End Statics.
End CANSEC1.
End TwB.
