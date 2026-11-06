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

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section TlsObj.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  Hypothesis AI_block_tls : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
      ab_addr b + ab_size b <= ATP + -200 \/ ATP + -200 + 504 <= ab_addr b.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).

  #[using="Type"] Lemma tls_sh : shad (ATP + -248) = 2147450880 + (ATPv + -248) / 8 /\ (ATPv + -248) mod 64 = 0 /\ 4096 <= ATPv + -248 /\ ATPv + 3896 <= ATOP.
  Proof.
    pose proof ATPv_img as TI. pose proof ATPv_hi as HI. unfold ATP. rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880.
    split; [reflexivity|]. rewrite TI in *. split; [reflexivity|]. split; [lia| exact HI].
  Qed.

  (* The thread block [ATP - 200, ATP + 304) lies in .bss; its 64-byte-aligned hull is [ATP - 248, ATP + 328). *)
  Definition tlsobj_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop :=
    unpoisoned m (ATP + -200) (ATP + 304) /\ wr_at asegs m (shad (ATP + -248)) 72 /\ rng RNG (shad (ATP + -248)) 72.
  Definition tlsobj_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop := shad (ATP + -248) <= a < shad (ATP + -248) + 72.
  Definition tlsobj_comp : gcomp := mkGC tlsobj_P tlsobj_dom.

  (* [comment removed for export] *)
  #[using="Type"] Lemma tlsobj_band : forall a, shad (ATP + -248) <= a < shad (ATP + -248) + 72 ->
    2147450880 + 512 <= a < 0x10007fff8000 /\ ATPv + -248 <= 8 * (a - ASHOFF) < ATPv + 328 /\ a < ATOP / 8 + 2147450880.
  Proof.
    intros a Ha. (nd_pre tls_sh 4%nat; intros E PG LO HI; nd_post). rewrite E in Ha. pose proof atop_range as AR. change AsanEmbed.ASHOFF with 2147450880.
    clear - Ha PG LO HI AR. Z.div_mod_to_equations. lia.
  Qed.

  #[using="AF AI_block_tls"] Lemma tlsobj_ok : gcomp_ok AI tlsobj_comp.
  Proof.
    constructor; cbn [gc_P gc_dom tlsobj_comp]; unfold tlsobj_dom.
    - intros L RNG RNG' s s' FB m m' (U & W & R) FP AG _ _ _. (nd_pre tls_sh 4%nat; intros E PG LO HI; nd_post). pose proof atop_range as AR.
      split.
      { eapply unpoisoned_agree; [exact U|]. intros sa Hs. unfold ATP in Hs. rewrite !shad_div in Hs. change AsanEmbed.ASHOFF with 2147450880 in Hs.
        apply AG; [clear - Hs LO HI AR; Z.div_mod_to_equations; lia| rewrite E; clear - Hs PG LO; Z.div_mod_to_equations; lia]. }
      split; [| eapply rng_fp_le; [exact FP| exact R]].
      eapply agrees_wr_at; [exact AG| exact W|]. intros a Ha. exact Ha.
    - intros L RNG s FB m LB SP a _ _ _ Ha Da. right. right. left.
      (nd_pre (tlsobj_band a Da) 3%nat; intros _ B _; nd_post). pose proof ATPv_img as TI. unfold AIMSH_LO, AIMSH_LEN. change AsanEmbed.ASHOFF with 2147450880 in B.
      clear - B TI. lia.
    - intros L RNG s CL FB FL m a AH _ Ha Da K. (nd_pre (tlsobj_band a Da) 3%nat; intros B1 B2 B3; nd_post). pose proof atop_range as AR.
      destruct (client_reg_cases AI AF _ _ _ _ _ _ _ _ AH K) as [C|[C|[C|(F & n & C1 & C2 & C3 & C4 & C5)]]]; try lia.
      (* [comment removed for export] *)
      unfold client_reg, client_keeps in K. (nd_pre tls_sh 4%nat; intros E PG LO HI; nd_post).
      destruct K as [K|[K|[K|K]]]; [lia| | |].
      + apply in_block_In in K as (b & Hb & Rb).
        (nd_pre (AI_block AI _ _ _ _ _ (cb_tok b) (cb_addr b) (cb_size b) AH (In_hb CL FB FL b ltac:(apply in_or_app; left; exact Hb))) 3%nat; intros _ BR _; nd_post).
        destruct BR as (BAND & _). unfold ablk, AIMG_HI, KLS in BAND. lia.
      + apply in_frames_In in K as (fr & Hf & Rf).
        (nd_pre (AF_frame AI AF _ _ _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) 5%nat; intros _ _ _ BAND _; nd_post). unfold ablk, AIMG_HI, KLS in BAND. lia.
      + apply in_frame_sh_In in K as (fr & Hf & Rf).
        (nd_pre (AF_frame AI AF _ _ _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) 6%nat; intros _ Hn F64 BAND TOP _; nd_post).
        pose proof (AI_block_tls _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) as D. unfold fkb_of in D. cbn [ab_addr ab_size] in D. unfold ATP in D.
        (pose proof (ablk_lin _ _ BAND) as ndP__; nd_pre ndP__ 3%nat; intros IMG F0 _; nd_post).
        rewrite (Z.shiftr_div_pow2 (fb_addr fr) 3) in Rf by lia. rewrite (Z.shiftr_div_pow2 (fb_size fr) 3) in Rf by lia. change (2^3) with 8 in Rf.
        change AsanEmbed.ASHOFF with 2147450880 in B2. unfold AIMG_HI in IMG. pose proof ATPv_img as TI. clear - Rf IMG F64 B2 TI. Z.div_mod_to_equations. lia.
    - intros L s FB a Da [D|D]; destruct (tlsobj_band a Da) as (B1 & B2 & B3).
      + unfold READ_STAGE in D. lia.
      + pose proof ATPv_sh as TS. unfold ATP in D. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma tlsobj_use : forall L RNG s FB m, tlsobj_P L RNG s FB m -> rng_atls RNG -> mobjA RNG m (ATP + -200) 504.
  Proof.
    intros L RNG s FB m (U & W & R) RT. (nd_pre tls_sh 4%nat; intros E PG LO HI; nd_post). pose proof atop_range as AR. pose proof ATPv_sh as TS. unfold ATP in *.
    split; [lia|]. split; [change (2^47) with 140737488355328; lia|]. split; [replace (ATPv + -200 + 504) with (ATPv + 304) by lia; exact U|]. split; [exact RT|]. split.
    - exists (ATPv + -248), (ATPv + 328). unfold KEND.
      split; [lia|]. split; [lia|]. split; [clear - PG; Z.div_mod_to_equations; lia|]. split; [clear - PG; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
      assert (E72 : shad (ATPv + 328) - shad (ATPv + -248) = 72) by (rewrite !shad_div; clear - PG; Z.div_mod_to_equations; lia).
      rewrite E72. split; [exact W| exact R].
    - unfold app_blk, KLOW, KHIGH, KEND. split; [lia|]. clear - TS HI AR LO. lia.
  Qed.

  Section Laws.
    Variable cs : list gcomp.
    Hypothesis IN_TLSOBJ : In tlsobj_comp cs.
    #[using="IN_TLSOBJ"] Lemma GS_tls : forall L RNG (s : PS) FB (m : mem), GSTAT_of cs L RNG s FB m -> rng_atls RNG -> mobjA RNG m (ATP + -200) 504.
    Proof. intros L RNG s FB m [_ GC]. exact (tlsobj_use L RNG s FB m (gconj_In _ _ _ _ _ _ _ GC IN_TLSOBJ)). Qed.
  End Laws.
End TlsObj.
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

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section TlsObj.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  Hypothesis AI_block_tls : forall L RNG st LB m b, AHEAP AI L RNG st LB m -> In b LB ->
      ab_addr b + ab_size b <= ATP + -200 \/ ATP + -200 + 504 <= ab_addr b.
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).

  #[using="Type"] Lemma tls_sh : shad (ATP + -248) = 2147450880 + (ATPv + -248) / 8 /\ (ATPv + -248) mod 64 = 0 /\ 4096 <= ATPv + -248 /\ ATPv + 3896 <= ATOP.
  Proof.
    pose proof ATPv_img as TI. pose proof ATPv_hi as HI. unfold ATP. rewrite shad_div. change AsanEmbed.ASHOFF with 2147450880.
    split; [reflexivity|]. rewrite TI in *. split; [reflexivity|]. split; [lia| exact HI].
  Qed.

  (* The thread block [ATP - 200, ATP + 304) lies in .bss; its 64-byte-aligned hull is [ATP - 248, ATP + 328). *)
  Definition tlsobj_P (L : alayout) (RNG : footprint) (s : PS) (FB : list cblk) (m : mem) : Prop :=
    unpoisoned m (ATP + -200) (ATP + 304) /\ wr_at asegs m (shad (ATP + -248)) 72 /\ rng RNG (shad (ATP + -248)) 72.
  Definition tlsobj_dom (L : alayout) (s : PS) (FB : list cblk) (a : Z) : Prop := shad (ATP + -248) <= a < shad (ATP + -248) + 72.
  Definition tlsobj_comp : gcomp := mkGC tlsobj_P tlsobj_dom.

  (* [comment removed for export] *)
  #[using="Type"] Lemma tlsobj_band : forall a, shad (ATP + -248) <= a < shad (ATP + -248) + 72 ->
    2147450880 + 512 <= a < 0x10007fff8000 /\ ATPv + -248 <= 8 * (a - ASHOFF) < ATPv + 328 /\ a < ATOP / 8 + 2147450880.
  Proof.
    intros a Ha. (nd_pre tls_sh 4%nat; intros E PG LO HI; nd_post). rewrite E in Ha. pose proof atop_range as AR. change AsanEmbed.ASHOFF with 2147450880.
    clear - Ha PG LO HI AR. Z.div_mod_to_equations. lia.
  Qed.

  #[using="AF AI_block_tls"] Lemma tlsobj_ok : gcomp_ok AI tlsobj_comp.
  Proof.
    constructor; cbn [gc_P gc_dom tlsobj_comp]; unfold tlsobj_dom.
    - intros L RNG RNG' s s' FB m m' (U & W & R) FP AG _ _ _. (nd_pre tls_sh 4%nat; intros E PG LO HI; nd_post). pose proof atop_range as AR.
      split.
      { eapply unpoisoned_agree; [exact U|]. intros sa Hs. unfold ATP in Hs. rewrite !shad_div in Hs. change AsanEmbed.ASHOFF with 2147450880 in Hs.
        apply AG; [clear - Hs LO HI AR; Z.div_mod_to_equations; lia| rewrite E; clear - Hs PG LO; Z.div_mod_to_equations; lia]. }
      split; [| eapply rng_fp_le; [exact FP| exact R]].
      eapply agrees_wr_at; [exact AG| exact W|]. intros a Ha. exact Ha.
    - intros L RNG s FB m LB SP a _ _ _ Ha Da. right. right. left.
      (nd_pre (tlsobj_band a Da) 3%nat; intros _ B _; nd_post). pose proof ATPv_img as TI. unfold AIMSH_LO, AIMSH_LEN. change AsanEmbed.ASHOFF with 2147450880 in B.
      clear - B TI. lia.
    - intros L RNG s CL FB FL m a AH _ Ha Da K. (nd_pre (tlsobj_band a Da) 3%nat; intros B1 B2 B3; nd_post). pose proof atop_range as AR.
      destruct (client_reg_cases AI AF _ _ _ _ _ _ _ _ AH K) as [C|[C|[C|(F & n & C1 & C2 & C3 & C4 & C5)]]]; try lia.
      (* [comment removed for export] *)
      unfold client_reg, client_keeps in K. (nd_pre tls_sh 4%nat; intros E PG LO HI; nd_post).
      destruct K as [K|[K|[K|K]]]; [lia| | |].
      + apply in_block_In in K as (b & Hb & Rb).
        (nd_pre (AI_block AI _ _ _ _ _ (cb_tok b) (cb_addr b) (cb_size b) AH (In_hb CL FB FL b ltac:(apply in_or_app; left; exact Hb))) 3%nat; intros _ BR _; nd_post).
        destruct BR as (BAND & _). unfold ablk, AIMG_HI, KLS in BAND. lia.
      + apply in_frames_In in K as (fr & Hf & Rf).
        (nd_pre (AF_frame AI AF _ _ _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) 5%nat; intros _ _ _ BAND _; nd_post). unfold ablk, AIMG_HI, KLS in BAND. lia.
      + apply in_frame_sh_In in K as (fr & Hf & Rf).
        (nd_pre (AF_frame AI AF _ _ _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) 6%nat; intros _ Hn F64 BAND TOP _; nd_post).
        pose proof (AI_block_tls _ _ _ _ _ _ AH (In_fkb CL FB FL fr Hf)) as D. unfold fkb_of in D. cbn [ab_addr ab_size] in D. unfold ATP in D.
        (pose proof (ablk_lin _ _ BAND) as ndP__; nd_pre ndP__ 3%nat; intros IMG F0 _; nd_post).
        rewrite (Z.shiftr_div_pow2 (fb_addr fr) 3) in Rf by lia. rewrite (Z.shiftr_div_pow2 (fb_size fr) 3) in Rf by lia. change (2^3) with 8 in Rf.
        change AsanEmbed.ASHOFF with 2147450880 in B2. unfold AIMG_HI in IMG. pose proof ATPv_img as TI. clear - Rf IMG F64 B2 TI. Z.div_mod_to_equations. lia.
    - intros L s FB a Da [D|D]; destruct (tlsobj_band a Da) as (B1 & B2 & B3).
      + unfold READ_STAGE in D. lia.
      + pose proof ATPv_sh as TS. unfold ATP in D. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma tlsobj_use : forall L RNG s FB m, tlsobj_P L RNG s FB m -> rng_atls RNG -> mobjA RNG m (ATP + -200) 504.
  Proof.
    intros L RNG s FB m (U & W & R) RT. (nd_pre tls_sh 4%nat; intros E PG LO HI; nd_post). pose proof atop_range as AR. pose proof ATPv_sh as TS. unfold ATP in *.
    split; [lia|]. split; [change (2^47) with 140737488355328; lia|]. split; [replace (ATPv + -200 + 504) with (ATPv + 304) by lia; exact U|]. split; [exact RT|]. split.
    - exists (ATPv + -248), (ATPv + 328). unfold KEND.
      split; [lia|]. split; [lia|]. split; [clear - PG; Z.div_mod_to_equations; lia|]. split; [clear - PG; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
      assert (E72 : shad (ATPv + 328) - shad (ATPv + -248) = 72) by (rewrite !shad_div; clear - PG; Z.div_mod_to_equations; lia).
      rewrite E72. split; [exact W| exact R].
    - unfold app_blk, KLOW, KHIGH, KEND. split; [lia|]. clear - TS HI AR LO. lia.
  Qed.

  Section Laws.
    Variable cs : list gcomp.
    Hypothesis IN_TLSOBJ : In tlsobj_comp cs.
    #[using="IN_TLSOBJ"] Lemma GS_tls : forall L RNG (s : PS) FB (m : mem), GSTAT_of cs L RNG s FB m -> rng_atls RNG -> mobjA RNG m (ATP + -200) 504.
    Proof. intros L RNG s FB m [_ GC]. exact (tlsobj_use L RNG s FB m (gconj_In _ _ _ _ _ _ _ GC IN_TLSOBJ)). Qed.
  End Laws.
End TlsObj.
End CANSEC1.
End TwB.
