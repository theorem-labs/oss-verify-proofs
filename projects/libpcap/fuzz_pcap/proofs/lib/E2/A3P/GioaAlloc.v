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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanCtrlProps AsanEmbed. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrlProps OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AProto AMalloc_iface AFake_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_acalloc_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.ACalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARealloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA HeapRulesS GioaReal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.HeapRulesS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section GioaAlloc.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  Variable GSTAT : alayout -> footprint -> PState aheap aptr -> list (@cblock aptr) -> mem -> Prop.
  #[local] Notation GIOA := (GIOA_real AI GSTAT).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis GS_pres : forall L RNG RNG' s s' FB (LB : list ablock) SP (m m' : mem),
      GSTAT L RNG s FB m -> fp_le RNG RNG' -> aheap_pres (aci AI) LB SP m m' -> (forall b, In b FB -> In (hb_of b) LB) -> ATOP + 4096 <= SP ->
      ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> ps_tls s' = ps_tls s -> GSTAT L RNG' s' FB m'.

  (* [comment removed for export] *)
  Definition malloc_core__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PState aheap aptr) (CL FB : list (@cblock aptr)) (FL : list fblock) (lo n : Z),
    GIOA L RNG s CL FB FL m -> stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo + MALLOC_STACK <= bv_unsigned sp ->
    mem_inv asegs m -> tp = Z_to_bv 64 ATP -> bv_unsigned sp mod 16 = 0 -> rng RNG lo (bv_unsigned sp - lo) ->
    1 <= n < 2^29 - 2^16 -> unw_okA L RNG m lo AMALLOC_PC sp s0 ra ->
    implMG RNG (pmalloc asan_ops n) s
      (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
         /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
         /\ match r with
            | None => False
            | Some q => exists A junk, a0v = Z_to_bv 64 A /\ GIOA L RNG' s' ((q, A, n) :: CL) FB FL m' /\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
            end)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MALLOC_ENTRY) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo n : ltac2:(SecDiet.SzSec.tyM 'malloc_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="AF GS_pres"] Lemma malloc_core__body : ltac2:(SecDiet.SzSec.bodyP 'malloc_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros G ST LO BU MI TPE ALN RSP Hn UNW.
    pose proof G as (AH & RV & AD & EF & SZ & ND & GS).
    destruct UNW as ((tr & AU) & S0 & RA1 & RA2).
    unfold implMG, pmalloc. cbn [ho_malloc asan_ops]. change MALLOC_ENTRY with AMALLOC_SYM.
    eapply implS_ah_malloc with (P := amalloc_post (aci AI) (AHEAP AI) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (ah_st (ps_heap s)) (LBof CL FB FL) n lo m).
    - change (@alloc_ceiling ceil_of_rc) with ATOP.
      eapply (AI_malloc AI L RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (ah_st (ps_heap s)) (LBof CL FB FL) n lo tr (ah_resv (ps_heap s)));
        [ exact AH | exact MI | exact ST | exact LO | unfold MALLOC_STACK, AMALLOC_STACK in *; lia | exact TPE | reflexivity | unfold AREQMAX; lia
        | exact AU | exact S0 | exact RA1 | exact RA2 | exact ALN | exact RSP | exact RV ].
    - intros [st' [id|]] RNG' ms' PO; cbn [fst snd]; unfold amalloc_post in PO; destruct PO as (FP & PO); destruct_exs PO;
        destruct PO as (-> & MI' & ST' & HP & PO); cbn [snd fst] in PO; [| destruct PO].
      destruct PO as (A & junk & -> & BR & AH' & CELL & R1 & R2 & _).
      pose proof BR as (BAND & N0 & TOP & A16). pose proof (ablk_lin _ _ BAND) as (_ & A0 & _ & T47'). 
      assert (EA : a0_of (MS (mkR ra sp gp tp x x0 x1 s0 s1 (Z_to_bv 64 A) x3 x4 x5 x6 x7 x8 x9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x10 x11 x12 x13) F (ret_pc ra) fc None x14 (seg_rom asegs)) = A).
      { unfold a0_of. etransitivity; [| apply (unsigned_lit A); lia]. reflexivity. }
      rewrite EA. split; [lia|].
      cbn [enomem_on_null]. apply implF_ret_ok. apply evtF_done. cbn [fst snd].
      split; [exact FP|]. exists (Z_to_bv 64 A), x14.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
      split; [eapply (pres_keeps AI AF GSTAT); [exact G| first [apply incl_refl | apply incl_tl; apply incl_refl]| exact HP| intros b Hb; exact Hb]|].
      exists A, junk. split; [reflexivity|]. split; [| exact CELL].
      (* [comment removed for export] *)
      split; [exact AH'|]. cbn [ps_heap set_heap ah_resv ah_addr ah_frames ah_st ah_set_addr ah_set_st].
      split; [exact RV|]. split.
      { intros b Hb. cbn [app] in Hb. destruct Hb as [<-|Hb]; cbn [cb_tok cb_addr fst snd].
        - apply lookup_insert_eq.
        - rewrite lookup_insert_ne; [exact (AD b Hb)|].
          pose proof (AI_hb_ids AI _ _ _ _ _ AH') as NI. unfold LBof in NI. cbn [map app hb_ids flat_map hb_of ab_kind cb_tok fst snd] in NI.
          apply List.NoDup_cons_iff in NI as [NI _]. intros E. apply NI. rewrite E.
          apply in_flat_map. exists (hb_of b). split; [apply in_or_app; left; apply in_map; exact Hb| left; reflexivity]. }
      split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
      eapply GS_pres; [exact GS| exact FP| exact HP| intros b Hb; apply In_hb; apply in_or_app; right; exact Hb| unfold MALLOC_STACK in BU; lia| reflexivity| reflexivity| reflexivity].
  Qed.
  End Sz1.
  #[using="AF GS_pres"] Lemma malloc_core : ltac:(let t := eval cbv delta [malloc_core__stmt] in malloc_core__stmt in exact t).
  Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo n. ltac2:(SecDiet.SzSec.closeP 'malloc_core__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Hypothesis AI_calloc : acalloc_stmt (aci AI) (AHEAP AI).
  Hypothesis AI_realloc : arealloc_stmt (aci AI) (AHEAP AI).
  Variable TP : tparams.
  Hypothesis HCPC : tp_cpc TP = ACALLOC_PC.
  Hypothesis HRPC : tp_rpc TP = AREALLOC_PC.

  #[using="AF GS_pres"] Theorem malloc_o_real : malloc_stmt_o asan_ops GIOA.
  Proof.
    red. intros until n. intros PRE -> Hn UNW.
    destruct PRE as (G & ST & LO & BU & [SPT T47] & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    eapply malloc_core; try eassumption. eapply rng_sub'; [exact RSTK| lia].
  Qed.

  Definition calloc_core__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PState aheap aptr) (CL FB : list (@cblock aptr)) (FL : list fblock) (lo cnt sz : Z),
    GIOA L RNG s CL FB FL m -> stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo + MALLOC_STACK <= bv_unsigned sp ->
    mem_inv asegs m -> tp = Z_to_bv 64 ATP -> bv_unsigned sp mod 16 = 0 -> rng RNG lo (bv_unsigned sp - lo) ->
    0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> 1 <= cnt * sz <= 3260 -> unw_okA L RNG m lo (tp_cpc TP) sp s0 ra ->
    implMG RNG (pcalloc asan_ops cnt sz) s
      (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
         /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
         /\ match r with
            | None => False
            | Some q => exists A, a0v = Z_to_bv 64 A /\ GIOA L RNG' s' ((q, A, cnt * sz) :: CL) FB FL m'
                        /\ rw_cells asegs m' A [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))]
            end)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cnt) (Z_to_bv 64 sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CALLOC_ENTRY) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo cnt sz : ltac2:(SecDiet.SzSec.tyM 'calloc_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="AF GS_pres AI_calloc HCPC"] Lemma calloc_core__body : ltac2:(SecDiet.SzSec.bodyP 'calloc_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros G ST LO BU MI TPE ALN RSP Hc Hs Hn UNW.
    pose proof G as (AH & RV & AD & EF & SZ & ND & GS). rewrite HCPC in UNW.
    destruct UNW as ((tr & AU) & S0 & RA1 & RA2).
    assert (C1 : 1 <= cnt) by nia. assert (S1 : 1 <= sz) by nia.
    unfold implMG, pcalloc. cbn [ho_calloc asan_ops]. change CALLOC_ENTRY with ACALLOC_SYM.
    eapply implS_ah_calloc with (P := amalloc_postU (aci AI) (AHEAP AI) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (ah_st (ps_heap s)) (LBof CL FB FL)
                                         (cnt * sz) lo m (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))).
    - change (@alloc_ceiling ceil_of_rc) with ATOP.
      eapply (AI_calloc L RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cnt) (Z_to_bv 64 sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (ah_st (ps_heap s)) (LBof CL FB FL) cnt sz (cnt * sz) lo tr (ah_resv (ps_heap s)));
        [ exact AH | exact MI | exact ST | exact LO | unfold MALLOC_STACK, ACALLOC_STACK in *; lia | exact TPE | reflexivity | reflexivity
        | exact C1 | exact S1 | reflexivity | unfold AREQMAX; lia | rewrite is_primary_iff by lia; apply Z.leb_le; lia
        | exact AU | exact S0 | exact RA1 | exact RA2 | exact ALN | exact RSP | exact RV ].
    - intros [st' [id|]] RNG' ms' PO; cbn [fst snd]; unfold amalloc_postU in PO; destruct PO as (FP & PO); destruct_exs PO;
        destruct PO as (-> & MI' & ST' & HP & PO); cbn [snd fst] in PO; [| destruct PO].
      destruct PO as (A & -> & BR & AH' & CELL & R1 & R2 & _).
      pose proof BR as (BAND & N0 & TOP & A16). pose proof (ablk_lin _ _ BAND) as (_ & A0 & _ & T47').
      assert (EA : a0_of (MS (mkR ra sp gp tp x x0 x1 s0 s1 (Z_to_bv 64 A) x3 x4 x5 x6 x7 x8 x9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x10 x11 x12 x13) F (ret_pc ra) fc None x14 (seg_rom asegs)) = A).
      { unfold a0_of. etransitivity; [| apply (unsigned_lit A); lia]. reflexivity. }
      rewrite EA. split; [lia|].
      cbn [enomem_on_null]. apply implF_ret_ok. apply evtF_done. cbn [fst snd].
      split; [exact FP|]. exists (Z_to_bv 64 A), x14.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
      split; [eapply (pres_keeps AI AF GSTAT); [exact G| first [apply incl_refl | apply incl_tl; apply incl_refl]| exact HP| intros b Hb; exact Hb]|].
      exists A. split; [reflexivity|]. split; [| exact CELL].
      split; [exact AH'|]. cbn [ps_heap set_heap ah_resv ah_addr ah_frames ah_st ah_set_addr ah_set_st].
      split; [exact RV|]. split.
      { intros b Hb. cbn [app] in Hb. destruct Hb as [<-|Hb]; cbn [cb_tok cb_addr fst snd].
        - apply lookup_insert_eq.
        - rewrite lookup_insert_ne; [exact (AD b Hb)|].
          pose proof (AI_hb_ids AI _ _ _ _ _ AH') as NI. unfold LBof in NI. cbn [map app hb_ids flat_map hb_of ab_kind cb_tok fst snd] in NI.
          apply List.NoDup_cons_iff in NI as [NI _]. intros E. apply NI. rewrite E.
          apply in_flat_map. exists (hb_of b). split; [apply in_or_app; left; apply in_map; exact Hb| left; reflexivity]. }
      split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
      eapply GS_pres; [exact GS| exact FP| exact HP| intros b Hb; apply In_hb; apply in_or_app; right; exact Hb| unfold MALLOC_STACK in BU; lia| reflexivity| reflexivity| reflexivity].
  Qed.
  End Sz3.
  #[using="AF GS_pres AI_calloc HCPC"] Lemma calloc_core : ltac:(let t := eval cbv delta [calloc_core__stmt] in calloc_core__stmt in exact t).
  Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo cnt sz. ltac2:(SecDiet.SzSec.closeP 'calloc_core__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  #[using="AF GS_pres AI_calloc HCPC"] Theorem calloc_o_real : calloc_stmt_o asan_ops GIOA TP.
  Proof.
    red. intros until sz. intros PRE -> -> Hc Hs Hn UNW.
    destruct PRE as (G & ST & LO & BU & [SPT T47] & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    eapply calloc_core; try eassumption. eapply rng_sub'; [exact RSTK| lia].
  Qed.

  (* [comment removed for export] *)
  Definition lb_remove_LBof__stmt : Prop := forall (C1 C2 FB : list (@cblock aptr)) FL q A n,
    List.NoDup (hb_ids (LBof (C1 ++ (q, A, n) :: C2) FB FL)) ->
    lb_remove q (LBof (C1 ++ (q, A, n) :: C2) FB FL) = LBof (C1 ++ C2) FB FL.
  Section Sz5.
  Variables C1 C2 FB FL q A n : ltac2:(SecDiet.SzSec.tyM 'lb_remove_LBof__stmt "vvvvvvv" @C1).
  #[using="Type"] Lemma lb_remove_LBof__body : ltac2:(SecDiet.SzSec.bodyP 'lb_remove_LBof__stmt "vvvvvvv").
  Proof.
    intros ND.
 unfold lb_remove, LBof in *.
    rewrite <- !app_assoc in *. cbn [app] in *. rewrite !map_app in *. cbn [map] in *.
    assert (IDS : forall l, hb_ids (map hb_of l) = map cb_tok l) by (induction l as [|b l IH]; [reflexivity| cbn; f_equal; exact IH]).
    assert (IDF0 : forall l, hb_ids (map fkb_of l) = []) by (induction l as [|fr l IH]; [reflexivity| cbn; exact IH]). pose proof (IDF0 FL) as IDF.
    unfold hb_ids in ND. rewrite !flat_map_app in ND. cbn [flat_map hb_of ab_kind app cb_tok fst snd] in ND.
    fold (hb_ids (map hb_of C1)) (hb_ids (map hb_of C2)) (hb_ids (map hb_of FB)) (hb_ids (map fkb_of FL)) in ND. rewrite !IDS, IDF, app_nil_r in ND. rewrite ?map_app in ND.
    assert (N1 : ~ In q (map cb_tok C1)) by (intros X; apply NoDup_remove_2 in ND; apply ND; apply in_or_app; left; exact X).
    assert (N2 : ~ In q (map cb_tok C2)) by (intros X; apply NoDup_remove_2 in ND; apply ND; apply in_or_app; right; apply in_or_app; left; exact X).
    assert (N3 : ~ In q (map cb_tok FB)) by (intros X; apply NoDup_remove_2 in ND; apply ND; apply in_or_app; right; apply in_or_app; right; exact X).
    assert (KEEP : forall l, ~ In q (map cb_tok l) -> filter (fun b => negb (abkind_eqb (ab_kind b) (ABHeap q))) (map hb_of l) = map hb_of l).
    { induction l as [|b l IH]; intros NI; [reflexivity|]. cbn [map] in *. rewrite filter_cons_True.
      - f_equal. apply IH. intros X. apply NI. right. exact X.
      - unfold hb_of. cbn [ab_kind abkind_eqb]. apply Is_true_true. apply Bool.negb_true_iff, N.eqb_neq. intros E. apply NI. left. exact E. }
    assert (KEEPF : forall l, filter (fun b => negb (abkind_eqb (ab_kind b) (ABHeap q))) (map fkb_of l) = map fkb_of l).
    { induction l as [|fr l IH]; [reflexivity|]. cbn [map]. rewrite filter_cons_True; [f_equal; exact IH| reflexivity]. }
    rewrite ?map_app. rewrite !list.filter_app. rewrite filter_cons_False.
    - rewrite ?list.filter_app. rewrite (KEEP C1 N1), (KEEP C2 N2), (KEEP FB N3), KEEPF. reflexivity.
    - unfold hb_of. cbn [ab_kind abkind_eqb cb_tok fst snd]. rewrite N.eqb_refl. cbn. intros X; exact X.
  Qed.
  End Sz5.
  #[using="Type"] Lemma lb_remove_LBof : ltac:(let t := eval cbv delta [lb_remove_LBof__stmt] in lb_remove_LBof__stmt in exact t).
  Proof. intros C1 C2 FB FL q A n. ltac2:(SecDiet.SzSec.closeP 'lb_remove_LBof__body "vvvvvvv"). Qed.

  Definition free_core__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PState aheap aptr) (C1 C2 FB : list (@cblock aptr)) (FL : list fblock) (q : aptr) (A n lo : Z),
    GIOA L RNG s (C1 ++ (q, A, n) :: C2) FB FL m -> stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo + FREE_STACK <= bv_unsigned sp ->
    mem_inv asegs m -> tp = Z_to_bv 64 ATP -> bv_unsigned sp mod 16 = 0 -> rng RNG lo (bv_unsigned sp - lo) ->
    unw_okA L RNG m lo AFREE_PC sp s0 ra ->
    implMG RNG (pfree asan_ops q) s
      (fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
         /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL (C1 ++ C2) (bv_unsigned sp)) m m'
         /\ GIOA L RNG' s' (C1 ++ C2) FB FL m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FREE_ENTRY) fc None m (seg_rom asegs)).
  Section Sz6.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s C1 C2 FB FL q A n lo : ltac2:(SecDiet.SzSec.tyM 'free_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="AF GS_pres"] Lemma free_core__body : ltac2:(SecDiet.SzSec.bodyP 'free_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros G ST LO BU MI TPE ALN RSP UNW.
    pose proof G as (AH & RV & AD & EF & SZ & ND & GS).
    destruct UNW as ((tr & AU) & S0 & RA1 & RA2).
    pose proof (lb_remove_LBof C1 C2 FB FL q A n (AI_hb_ids AI _ _ _ _ _ AH)) as ELB.
    unfold implMG, pfree. cbn [ho_free asan_ops]. change FREE_ENTRY with AFREE_SYM.
    eapply implS_ah_free0 with (P := afree_post (aci AI) (AHEAP AI) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (ah_st (ps_heap s))
                                        (LBof (C1 ++ (q, A, n) :: C2) FB FL) q lo m).
    - change (@alloc_ceiling ceil_of_rc) with ATOP.
      eapply (AI_free AI L RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (ah_st (ps_heap s)) (LBof (C1 ++ (q, A, n) :: C2) FB FL) q A n lo tr);
        [ exact AH | apply (In_hb _ _ FL (q, A, n)); apply in_or_app; left; apply in_or_app; right; left; reflexivity
        | exact MI | exact ST | exact LO | unfold FREE_STACK, AFREE_STACK in *; lia | exact TPE | reflexivity
        | exact AU | exact S0 | exact RA1 | exact RA2 | exact ALN | exact RSP ].
    - intros st' RNG' ms' PO. unfold afree_post in PO. destruct PO as (FP & PO). destruct_exs PO. destruct PO as (-> & MI' & ST' & HP & AH').
      rewrite ELB in HP, AH'. cbn [fst snd].
      split; [exact FP|]. eexists _, x14.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
      split; [eapply (pres_keeps AI AF GSTAT); [exact G| first [apply incl_refl | apply incl_tl; apply incl_refl]| exact HP| intros b Hb; exact Hb]|].
      split; [exact AH'|]. cbn [ps_heap set_heap ah_resv ah_addr ah_frames ah_st ah_set_addr ah_set_st].
      split; [exact RV|]. split.
      { intros b Hb.
        assert (Hb' : In b ((C1 ++ (q, A, n) :: C2) ++ FB))
          by (apply in_app_or in Hb as [Hb|Hb]; [apply in_app_or in Hb as [Hb|Hb]|]; apply in_or_app;
              [left; apply in_or_app; left; exact Hb| left; apply in_or_app; right; right; exact Hb| right; exact Hb]).
        rewrite lookup_delete_ne; [exact (AD b Hb')|].
        (* [comment removed for export] *)
        pose proof (AI_hb_ids AI _ _ _ _ _ AH) as NI. intros E.
        assert (IDS : forall l, hb_ids (map hb_of l) = map cb_tok l) by (induction l as [|b0 l IH]; [reflexivity| cbn; f_equal; exact IH]).
        unfold LBof in NI. unfold hb_ids in NI. rewrite flat_map_app in NI. apply NoDup_app_remove_r in NI. fold (hb_ids (map hb_of ((C1 ++ (q, A, n) :: C2) ++ FB))) in NI.
        rewrite IDS, <- app_assoc, map_app in NI. cbn [app map cb_tok fst snd] in NI. apply NoDup_remove_2 in NI. apply NI.
        rewrite E. rewrite <- map_app. apply in_map. rewrite <- app_assoc in Hb. exact Hb. }
      split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
      eapply GS_pres; [exact GS| exact FP| exact HP| intros b Hb; apply In_hb; apply in_or_app; right; exact Hb| unfold FREE_STACK in BU; lia| reflexivity| reflexivity| reflexivity].
  Qed.
  End Sz6.
  #[using="AF GS_pres"] Lemma free_core : ltac:(let t := eval cbv delta [free_core__stmt] in free_core__stmt in exact t).
  Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s C1 C2 FB FL q A n lo. ltac2:(SecDiet.SzSec.closeP 'free_core__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  #[using="AF GS_pres"] Theorem free_o_real : free_stmt_o asan_ops GIOA.
  Proof.
    red. intros until lo. intros PRE -> UNW.
    destruct PRE as (G & ST & LO & BU & [SPT T47] & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    eapply free_core; try eassumption. eapply rng_sub'; [exact RSTK| lia].
  Qed.

  (* [comment removed for export] *)
  Definition free_null_core__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PState aheap aptr) (CL FB : list (@cblock aptr)) (FL : list fblock) (lo : Z),
    GIOA L RNG s CL FB FL m -> stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo + FREE_STACK <= bv_unsigned sp ->
    mem_inv asegs m -> tp = Z_to_bv 64 ATP -> bv_unsigned sp mod 16 = 0 -> rng RNG lo (bv_unsigned sp - lo) ->
    unw_okA L RNG m lo AFREE_PC sp s0 ra ->
    evtF asegs RNG (fun ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
         /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
         /\ GIOA L RNG s CL FB FL m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FREE_ENTRY) fc None m (seg_rom asegs)).
  Section Sz8.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo : ltac2:(SecDiet.SzSec.tyM 'free_null_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="AF GS_pres"] Lemma free_null_core__body : ltac2:(SecDiet.SzSec.bodyP 'free_null_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros G ST LO BU MI TPE ALN RSP UNW.
    pose proof G as (AH & RV & AD & EF & SZ & ND & GS).
    destruct UNW as ((tr & AU) & S0 & RA1 & RA2). change FREE_ENTRY with AFREE_SYM.
    eapply evtF_mono.
    - eapply (AI_free_null AI L RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (ah_st (ps_heap s)) (LBof CL FB FL) lo tr);
        [ exact AH | exact MI | exact ST | exact LO | unfold FREE_STACK, AFREE_STACK in *; lia | exact TPE | reflexivity
        | exact AU | exact S0 | exact RA1 | exact RA2 | exact ALN | exact RSP ].
    - cbv beta. intros ms' PO. unfold afree_null_post in PO. destruct_exs PO. destruct PO as (-> & MI' & ST' & HP & AH').
      eexists _, x14. split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [exact MI'|]. split; [exact ST'|]. split; [eapply (pres_keeps AI AF GSTAT); [exact G| first [apply incl_refl | apply incl_tl; apply incl_refl]| exact HP| intros b Hb; exact Hb]|].
      split; [exact AH'|]. split; [exact RV|]. split; [exact AD|]. split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
      eapply GS_pres; [exact GS| apply fp_le_refl| exact HP| intros b Hb; apply In_hb; apply in_or_app; right; exact Hb| unfold FREE_STACK in BU; lia| reflexivity| reflexivity| reflexivity].
  Qed.
  End Sz8.
  #[using="AF GS_pres"] Lemma free_null_core : ltac:(let t := eval cbv delta [free_null_core__stmt] in free_null_core__stmt in exact t).
  Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo. ltac2:(SecDiet.SzSec.closeP 'free_null_core__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  #[using="AF GS_pres"] Theorem free_null_o_real : free_null_stmt_o GIOA.
  Proof.
    red. intros until lo. intros PRE -> UNW.
    destruct PRE as (G & ST & LO & BU & [SPT T47] & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    eapply free_null_core; try eassumption. eapply rng_sub'; [exact RSTK| lia].
  Qed.

  (* [comment removed for export] *)
  Definition realloc_core__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PState aheap aptr) (C1 C2 FB : list (@cblock aptr)) (FL : list fblock)
      (q : aptr) (A sz lo n : Z) (bs : list byte),
    GIOA L RNG s (C1 ++ (q, A, sz) :: C2) FB FL m -> stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo + REALLOC_STACK <= bv_unsigned sp ->
    mem_inv asegs m -> tp = Z_to_bv 64 ATP -> bv_unsigned sp mod 16 = 0 -> rng RNG lo (bv_unsigned sp - lo) ->
    1 <= n < 2^29 - 2^16 -> rw_cells asegs m A [CB (Z.to_nat sz) bs] -> unw_okA L RNG m lo (tp_rpc TP) sp s0 ra ->
    implMG RNG (prealloc asan_ops q n) s
      (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
         /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL (C1 ++ C2) (bv_unsigned sp)) m m'
         /\ match r with
            | None => False
            | Some q' => exists A' junk, a0v = Z_to_bv 64 A' /\ GIOA L RNG' s' ((q', A', n) :: C1 ++ C2) FB FL m'
                        /\ rw_cells asegs m' A' [CB (Z.to_nat (Z.min sz n)) (firstn (Z.to_nat (Z.min sz n)) bs); CB (Z.to_nat (n - Z.min sz n)) junk]
            end)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REALLOC_ENTRY) fc None m (seg_rom asegs)).
  Section Sz10.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s C1 C2 FB FL q A sz lo n bs : ltac2:(SecDiet.SzSec.tyM 'realloc_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="AF GS_pres AI_realloc HRPC"] Lemma realloc_core__body : ltac2:(SecDiet.SzSec.bodyP 'realloc_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros G ST LO BU MI TPE ALN RSP Hn OLD UNW.
    pose proof G as (AH & RV & AD & EF & SZ & ND & GS). rewrite HRPC in UNW.
    destruct UNW as ((tr & AU) & S0 & RA1 & RA2).
    pose proof (lb_remove_LBof C1 C2 FB FL q A sz (AI_hb_ids AI _ _ _ _ _ AH)) as ELB.
    destruct (AI_block AI _ _ _ _ _ q A sz AH ltac:(apply (In_hb _ _ FL (q, A, sz)); apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as (SZ1 & _).
    assert (LBS : length bs = Z.to_nat sz) by (destruct OLD as [[WFc _] _]; cbn [cells_wf cell_wf] in WFc; lia).
    unfold implMG, prealloc. cbn [ho_realloc asan_ops]. change REALLOC_ENTRY with AREALLOC_SYM.
    eapply implS_ah_realloc with (P := arealloc_post (aci AI) (AHEAP AI) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (ah_st (ps_heap s))
                                          (LBof (C1 ++ (q, A, sz) :: C2) FB FL) q sz bs n lo m).
    - change (@alloc_ceiling ceil_of_rc) with ATOP.
      eapply (AI_realloc L RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (ah_st (ps_heap s)) (LBof (C1 ++ (q, A, sz) :: C2) FB FL) q A sz n lo bs tr (ah_resv (ps_heap s)));
        [ exact AH | apply (In_hb _ _ FL (q, A, sz)); apply in_or_app; left; apply in_or_app; right; left; reflexivity | exact OLD
        | exact MI | exact ST | exact LO | unfold REALLOC_STACK, AREALLOC_STACK in *; lia | exact TPE | reflexivity | reflexivity | unfold AREQMAX; lia
        | exact AU | exact S0 | exact RA1 | exact RA2 | exact ALN | exact RSP | exact RV ].
    - intros [st' [id|]] RNG' ms' PO; cbn [fst snd]; unfold arealloc_post in PO; destruct PO as (FP & PO); destruct_exs PO;
        destruct PO as (-> & MI' & ST' & HP & PO); cbn [snd fst] in PO; [| destruct PO].
      destruct PO as (A' & junk & -> & BR & AH' & LJ & CELL & R1 & R2X).
      (* [comment removed for export] *)
      assert (R2 : rng RNG' (shad A') (AsanEmbed.shlen (n + 7))) by (first [exact R2X | exact (proj1 R2X)]). clear R2X.
      rewrite ELB in HP, AH'.
      pose proof BR as (BAND & N0 & TOP & A16). pose proof (ablk_lin _ _ BAND) as (_ & A0 & _ & T47').
      assert (EA : a0_of (MS (mkR ra sp gp tp x x0 x1 s0 s1 (Z_to_bv 64 A') x3 x4 x5 x6 x7 x8 x9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x10 x11 x12 x13) F (ret_pc ra) fc None x14 (seg_rom asegs)) = A').
      { unfold a0_of. etransitivity; [| apply (unsigned_lit A'); lia]. reflexivity. }
      rewrite EA. split; [lia|].
      cbn [enomem_on_null]. apply implF_ret_ok. apply evtF_done. cbn [fst snd].
      split; [exact FP|]. exists (Z_to_bv 64 A'), x14.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
      split; [eapply (pres_keeps AI AF GSTAT); [exact G| first [apply incl_refl | apply incl_tl; apply incl_refl]| exact HP| intros b Hb; exact Hb]|].
      exists A', junk. split; [reflexivity|]. split.
      2:{ (* [comment removed for export] *)
          assert (E : Z.to_nat n = (Z.to_nat (Z.min sz n) + Z.to_nat (n - Z.min sz n))%nat) by lia.
          apply (rw_cells_split_CB asegs _ _ [] _ _ [] [Z.to_nat (Z.min sz n); Z.to_nat (n - Z.min sz n)]) in CELL; [| cbn; lia].
          cbn [mk_CB_cells app] in CELL.
          assert (LF : length (firstn (Z.to_nat (Z.min sz n)) bs) = Z.to_nat (Z.min sz n)) by (rewrite length_firstn; lia).
          rewrite firstn_app, LF, Nat.sub_diag, firstn_O, app_nil_r, firstn_firstn, Nat.min_id in CELL.
          rewrite skipn_app, LF, Nat.sub_diag, skipn_O in CELL.
          rewrite (skipn_all2 (firstn _ bs)) in CELL by lia. cbn [app] in CELL.
          rewrite (firstn_all2 (n := Z.to_nat (n - Z.min sz n)) junk) in CELL by lia. exact CELL. }
      split; [exact AH'|]. cbn [ps_heap set_heap ah_resv ah_addr ah_frames ah_st ah_set_addr ah_set_st].
      split; [exact RV|]. split.
      { intros b Hb. cbn [app] in Hb. destruct Hb as [<-|Hb]; cbn [cb_tok cb_addr fst snd]; [apply lookup_insert_eq|].
        assert (Hb' : In b ((C1 ++ (q, A, sz) :: C2) ++ FB))
          by (apply in_app_or in Hb as [Hb|Hb]; [apply in_app_or in Hb as [Hb|Hb]|]; apply in_or_app;
              [left; apply in_or_app; left; exact Hb| left; apply in_or_app; right; right; exact Hb| right; exact Hb]).
        assert (IDS : forall l, hb_ids (map hb_of l) = map cb_tok l) by (induction l as [|b0 l IH]; [reflexivity| cbn; f_equal; exact IH]).
        rewrite lookup_insert_ne.
        - rewrite lookup_delete_ne; [exact (AD b Hb')|].
          pose proof (AI_hb_ids AI _ _ _ _ _ AH) as NI. intros E.
          unfold LBof in NI. unfold hb_ids in NI. rewrite flat_map_app in NI. apply NoDup_app_remove_r in NI. fold (hb_ids (map hb_of ((C1 ++ (q, A, sz) :: C2) ++ FB))) in NI.
          rewrite IDS, <- app_assoc, map_app in NI. cbn [app map cb_tok fst snd] in NI. apply NoDup_remove_2 in NI. apply NI.
          rewrite E. rewrite <- map_app. apply in_map. rewrite <- app_assoc in Hb. exact Hb.
        - pose proof (AI_hb_ids AI _ _ _ _ _ AH') as NI. unfold LBof in NI. cbn [map app hb_ids flat_map hb_of ab_kind cb_tok fst snd] in NI.
          apply List.NoDup_cons_iff in NI as [NI _]. intros E. apply NI. rewrite E.
          apply in_flat_map. exists (hb_of b). split; [apply in_or_app; left; apply in_map; exact Hb| left; reflexivity]. }
      split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
      eapply GS_pres; [exact GS| exact FP| exact HP| intros b Hb; apply In_hb; apply in_or_app; right; exact Hb| unfold REALLOC_STACK in BU; lia| reflexivity| reflexivity| reflexivity].
  Qed.
  End Sz10.
  #[using="AF GS_pres AI_realloc HRPC"] Lemma realloc_core : ltac:(let t := eval cbv delta [realloc_core__stmt] in realloc_core__stmt in exact t).
  Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s C1 C2 FB FL q A sz lo n bs. ltac2:(SecDiet.SzSec.closeP 'realloc_core__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  #[using="AF GS_pres AI_realloc HRPC"] Theorem realloc_o_real : realloc_stmt_o asan_ops GIOA TP.
  Proof.
    red. intros until bs. intros PRE -> -> Hn OLD UNW.
    destruct PRE as (G & ST & LO & BU & [SPT T47] & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    eapply realloc_core; try eassumption. eapply rng_sub'; [exact RSTK| lia].
  Qed.
End GioaAlloc.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrlProps OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_acalloc_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.ACalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARealloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.HeapRulesS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section GioaAlloc.
  Variable AI : AMallocIface.
  Hypothesis AF : AFakeIface AI.
  Variable GSTAT : alayout -> footprint -> PState aheap aptr -> list (@cblock aptr) -> mem -> Prop.
  #[local] Notation GIOA := (GIOA_real AI GSTAT).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis GS_pres : forall L RNG RNG' s s' FB (LB : list ablock) SP (m m' : mem),
      GSTAT L RNG s FB m -> fp_le RNG RNG' -> aheap_pres (aci AI) LB SP m m' -> (forall b, In b FB -> In (hb_of b) LB) -> ATOP + 4096 <= SP ->
      ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> ps_tls s' = ps_tls s -> GSTAT L RNG' s' FB m'.

  (* [comment removed for export] *)
  Definition malloc_core__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PState aheap aptr) (CL FB : list (@cblock aptr)) (FL : list fblock) (lo n : Z),
    GIOA L RNG s CL FB FL m -> stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo + MALLOC_STACK <= bv_unsigned sp ->
    mem_inv asegs m -> tp = Z_to_bv 64 ATP -> bv_unsigned sp mod 16 = 0 -> rng RNG lo (bv_unsigned sp - lo) ->
    1 <= n < 2^29 - 2^16 -> unw_okA L RNG m lo AMALLOC_PC sp s0 ra ->
    implMG RNG (pmalloc asan_ops n) s
      (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
         /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
         /\ match r with
            | None => False
            | Some q => exists A junk, a0v = Z_to_bv 64 A /\ GIOA L RNG' s' ((q, A, n) :: CL) FB FL m' /\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
            end)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MALLOC_ENTRY) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo n : ltac2:(SecDiet.SzSec.tyM 'malloc_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="AF GS_pres"] Lemma malloc_core__body : ltac2:(SecDiet.SzSec.bodyP 'malloc_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros G ST LO BU MI TPE ALN RSP Hn UNW.
    pose proof G as (AH & RV & AD & EF & SZ & ND & GS).
    destruct UNW as ((tr & AU) & S0 & RA1 & RA2).
    unfold implMG, pmalloc. cbn [ho_malloc asan_ops]. change MALLOC_ENTRY with AMALLOC_SYM.
    eapply implS_ah_malloc with (P := amalloc_post (aci AI) (AHEAP AI) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (ah_st (ps_heap s)) (LBof CL FB FL) n lo m).
    - change (@alloc_ceiling ceil_of_rc) with ATOP.
      eapply (AI_malloc AI L RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (ah_st (ps_heap s)) (LBof CL FB FL) n lo tr (ah_resv (ps_heap s)));
        [ exact AH | exact MI | exact ST | exact LO | unfold MALLOC_STACK, AMALLOC_STACK in *; lia | exact TPE | reflexivity | unfold AREQMAX; lia
        | exact AU | exact S0 | exact RA1 | exact RA2 | exact ALN | exact RSP | exact RV ].
    - intros [st' [id|]] RNG' ms' PO; cbn [fst snd]; unfold amalloc_post in PO; destruct PO as (FP & PO); destruct_exs PO;
        destruct PO as (-> & MI' & ST' & HP & PO); cbn [snd fst] in PO; [| destruct PO].
      destruct PO as (A & junk & -> & BR & AH' & CELL & R1 & R2 & _).
      pose proof BR as (BAND & N0 & TOP & A16). pose proof (ablk_lin _ _ BAND) as (_ & A0 & _ & T47'). 
      assert (EA : a0_of (MS (mkR ra sp gp tp x x0 x1 s0 s1 (Z_to_bv 64 A) x3 x4 x5 x6 x7 x8 x9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x10 x11 x12 x13) F (ret_pc ra) fc None x14 (seg_rom asegs)) = A).
      { unfold a0_of. etransitivity; [| apply (unsigned_lit A); lia]. reflexivity. }
      rewrite EA. split; [lia|].
      cbn [enomem_on_null]. apply implF_ret_ok. apply evtF_done. cbn [fst snd].
      split; [exact FP|]. exists (Z_to_bv 64 A), x14.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
      split; [eapply (pres_keeps AI AF GSTAT); [exact G| first [apply incl_refl | apply incl_tl; apply incl_refl]| exact HP| intros b Hb; exact Hb]|].
      exists A, junk. split; [reflexivity|]. split; [| exact CELL].
      (* [comment removed for export] *)
      split; [exact AH'|]. cbn [ps_heap set_heap ah_resv ah_addr ah_frames ah_st ah_set_addr ah_set_st].
      split; [exact RV|]. split.
      { intros b Hb. cbn [app] in Hb. destruct Hb as [<-|Hb]; cbn [cb_tok cb_addr fst snd].
        - apply lookup_insert_eq.
        - rewrite lookup_insert_ne; [exact (AD b Hb)|].
          pose proof (AI_hb_ids AI _ _ _ _ _ AH') as NI. unfold LBof in NI. cbn [map app hb_ids flat_map hb_of ab_kind cb_tok fst snd] in NI.
          apply List.NoDup_cons_iff in NI as [NI _]. intros E. apply NI. rewrite E.
          apply in_flat_map. exists (hb_of b). split; [apply in_or_app; left; apply in_map; exact Hb| left; reflexivity]. }
      split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
      eapply GS_pres; [exact GS| exact FP| exact HP| intros b Hb; apply In_hb; apply in_or_app; right; exact Hb| unfold MALLOC_STACK in BU; lia| reflexivity| reflexivity| reflexivity].
  Qed.
  End Sz1.
  #[using="AF GS_pres"] Lemma malloc_core : ltac:(let t := eval cbv delta [malloc_core__stmt] in malloc_core__stmt in exact t).
  Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo n. ltac2:(SecDiet.SzSec.closeP 'malloc_core__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Hypothesis AI_calloc : acalloc_stmt (aci AI) (AHEAP AI).
  Hypothesis AI_realloc : arealloc_stmt (aci AI) (AHEAP AI).
  Variable TP : tparams.
  Hypothesis HCPC : tp_cpc TP = ACALLOC_PC.
  Hypothesis HRPC : tp_rpc TP = AREALLOC_PC.

  #[using="AF GS_pres"] Theorem malloc_o_real : malloc_stmt_o asan_ops GIOA.
  Proof.
    red. intros until n. intros PRE -> Hn UNW.
    destruct PRE as (G & ST & LO & BU & [SPT T47] & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    eapply malloc_core; try eassumption. eapply rng_sub'; [exact RSTK| lia].
  Qed.

  Definition calloc_core__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PState aheap aptr) (CL FB : list (@cblock aptr)) (FL : list fblock) (lo cnt sz : Z),
    GIOA L RNG s CL FB FL m -> stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo + MALLOC_STACK <= bv_unsigned sp ->
    mem_inv asegs m -> tp = Z_to_bv 64 ATP -> bv_unsigned sp mod 16 = 0 -> rng RNG lo (bv_unsigned sp - lo) ->
    0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> 1 <= cnt * sz <= 3260 -> unw_okA L RNG m lo (tp_cpc TP) sp s0 ra ->
    implMG RNG (pcalloc asan_ops cnt sz) s
      (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
         /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
         /\ match r with
            | None => False
            | Some q => exists A, a0v = Z_to_bv 64 A /\ GIOA L RNG' s' ((q, A, cnt * sz) :: CL) FB FL m'
                        /\ rw_cells asegs m' A [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))]
            end)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cnt) (Z_to_bv 64 sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CALLOC_ENTRY) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo cnt sz : ltac2:(SecDiet.SzSec.tyM 'calloc_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="AF GS_pres AI_calloc HCPC"] Lemma calloc_core__body : ltac2:(SecDiet.SzSec.bodyP 'calloc_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros G ST LO BU MI TPE ALN RSP Hc Hs Hn UNW.
    pose proof G as (AH & RV & AD & EF & SZ & ND & GS). rewrite HCPC in UNW.
    destruct UNW as ((tr & AU) & S0 & RA1 & RA2).
    assert (C1 : 1 <= cnt) by nia. assert (S1 : 1 <= sz) by nia.
    unfold implMG, pcalloc. cbn [ho_calloc asan_ops]. change CALLOC_ENTRY with ACALLOC_SYM.
    eapply implS_ah_calloc with (P := amalloc_postU (aci AI) (AHEAP AI) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (ah_st (ps_heap s)) (LBof CL FB FL)
                                         (cnt * sz) lo m (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))).
    - change (@alloc_ceiling ceil_of_rc) with ATOP.
      eapply (AI_calloc L RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cnt) (Z_to_bv 64 sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (ah_st (ps_heap s)) (LBof CL FB FL) cnt sz (cnt * sz) lo tr (ah_resv (ps_heap s)));
        [ exact AH | exact MI | exact ST | exact LO | unfold MALLOC_STACK, ACALLOC_STACK in *; lia | exact TPE | reflexivity | reflexivity
        | exact C1 | exact S1 | reflexivity | unfold AREQMAX; lia | rewrite is_primary_iff by lia; apply Z.leb_le; lia
        | exact AU | exact S0 | exact RA1 | exact RA2 | exact ALN | exact RSP | exact RV ].
    - intros [st' [id|]] RNG' ms' PO; cbn [fst snd]; unfold amalloc_postU in PO; destruct PO as (FP & PO); destruct_exs PO;
        destruct PO as (-> & MI' & ST' & HP & PO); cbn [snd fst] in PO; [| destruct PO].
      destruct PO as (A & -> & BR & AH' & CELL & R1 & R2 & _).
      pose proof BR as (BAND & N0 & TOP & A16). pose proof (ablk_lin _ _ BAND) as (_ & A0 & _ & T47').
      assert (EA : a0_of (MS (mkR ra sp gp tp x x0 x1 s0 s1 (Z_to_bv 64 A) x3 x4 x5 x6 x7 x8 x9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x10 x11 x12 x13) F (ret_pc ra) fc None x14 (seg_rom asegs)) = A).
      { unfold a0_of. etransitivity; [| apply (unsigned_lit A); lia]. reflexivity. }
      rewrite EA. split; [lia|].
      cbn [enomem_on_null]. apply implF_ret_ok. apply evtF_done. cbn [fst snd].
      split; [exact FP|]. exists (Z_to_bv 64 A), x14.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
      split; [eapply (pres_keeps AI AF GSTAT); [exact G| first [apply incl_refl | apply incl_tl; apply incl_refl]| exact HP| intros b Hb; exact Hb]|].
      exists A. split; [reflexivity|]. split; [| exact CELL].
      split; [exact AH'|]. cbn [ps_heap set_heap ah_resv ah_addr ah_frames ah_st ah_set_addr ah_set_st].
      split; [exact RV|]. split.
      { intros b Hb. cbn [app] in Hb. destruct Hb as [<-|Hb]; cbn [cb_tok cb_addr fst snd].
        - apply lookup_insert_eq.
        - rewrite lookup_insert_ne; [exact (AD b Hb)|].
          pose proof (AI_hb_ids AI _ _ _ _ _ AH') as NI. unfold LBof in NI. cbn [map app hb_ids flat_map hb_of ab_kind cb_tok fst snd] in NI.
          apply List.NoDup_cons_iff in NI as [NI _]. intros E. apply NI. rewrite E.
          apply in_flat_map. exists (hb_of b). split; [apply in_or_app; left; apply in_map; exact Hb| left; reflexivity]. }
      split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
      eapply GS_pres; [exact GS| exact FP| exact HP| intros b Hb; apply In_hb; apply in_or_app; right; exact Hb| unfold MALLOC_STACK in BU; lia| reflexivity| reflexivity| reflexivity].
  Qed.
  End Sz3.
  #[using="AF GS_pres AI_calloc HCPC"] Lemma calloc_core : ltac:(let t := eval cbv delta [calloc_core__stmt] in calloc_core__stmt in exact t).
  Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo cnt sz. ltac2:(SecDiet.SzSec.closeP 'calloc_core__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  #[using="AF GS_pres AI_calloc HCPC"] Theorem calloc_o_real : calloc_stmt_o asan_ops GIOA TP.
  Proof.
    red. intros until sz. intros PRE -> -> Hc Hs Hn UNW.
    destruct PRE as (G & ST & LO & BU & [SPT T47] & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    eapply calloc_core; try eassumption. eapply rng_sub'; [exact RSTK| lia].
  Qed.

  (* [comment removed for export] *)
  Definition lb_remove_LBof__stmt : Prop := forall (C1 C2 FB : list (@cblock aptr)) FL q A n,
    List.NoDup (hb_ids (LBof (C1 ++ (q, A, n) :: C2) FB FL)) ->
    lb_remove q (LBof (C1 ++ (q, A, n) :: C2) FB FL) = LBof (C1 ++ C2) FB FL.
  Section Sz5.
  Variables C1 C2 FB FL q A n : ltac2:(SecDiet.SzSec.tyM 'lb_remove_LBof__stmt "vvvvvvv" @C1).
  #[using="Type"] Lemma lb_remove_LBof__body : ltac2:(SecDiet.SzSec.bodyP 'lb_remove_LBof__stmt "vvvvvvv").
  Proof.
    intros ND.
 unfold lb_remove, LBof in *.
    rewrite <- !app_assoc in *. cbn [app] in *. rewrite !map_app in *. cbn [map] in *.
    assert (IDS : forall l, hb_ids (map hb_of l) = map cb_tok l) by (induction l as [|b l IH]; [reflexivity| cbn; f_equal; exact IH]).
    assert (IDF0 : forall l, hb_ids (map fkb_of l) = []) by (induction l as [|fr l IH]; [reflexivity| cbn; exact IH]). pose proof (IDF0 FL) as IDF.
    unfold hb_ids in ND. rewrite !flat_map_app in ND. cbn [flat_map hb_of ab_kind app cb_tok fst snd] in ND.
    fold (hb_ids (map hb_of C1)) (hb_ids (map hb_of C2)) (hb_ids (map hb_of FB)) (hb_ids (map fkb_of FL)) in ND. rewrite !IDS, IDF, app_nil_r in ND. rewrite ?map_app in ND.
    assert (N1 : ~ In q (map cb_tok C1)) by (intros X; apply NoDup_remove_2 in ND; apply ND; apply in_or_app; left; exact X).
    assert (N2 : ~ In q (map cb_tok C2)) by (intros X; apply NoDup_remove_2 in ND; apply ND; apply in_or_app; right; apply in_or_app; left; exact X).
    assert (N3 : ~ In q (map cb_tok FB)) by (intros X; apply NoDup_remove_2 in ND; apply ND; apply in_or_app; right; apply in_or_app; right; exact X).
    assert (KEEP : forall l, ~ In q (map cb_tok l) -> filter (fun b => negb (abkind_eqb (ab_kind b) (ABHeap q))) (map hb_of l) = map hb_of l).
    { induction l as [|b l IH]; intros NI; [reflexivity|]. cbn [map] in *. rewrite filter_cons_True.
      - f_equal. apply IH. intros X. apply NI. right. exact X.
      - unfold hb_of. cbn [ab_kind abkind_eqb]. apply Is_true_true. apply Bool.negb_true_iff, N.eqb_neq. intros E. apply NI. left. exact E. }
    assert (KEEPF : forall l, filter (fun b => negb (abkind_eqb (ab_kind b) (ABHeap q))) (map fkb_of l) = map fkb_of l).
    { induction l as [|fr l IH]; [reflexivity|]. cbn [map]. rewrite filter_cons_True; [f_equal; exact IH| reflexivity]. }
    rewrite ?map_app. rewrite !list.filter_app. rewrite filter_cons_False.
    - rewrite ?list.filter_app. rewrite (KEEP C1 N1), (KEEP C2 N2), (KEEP FB N3), KEEPF. reflexivity.
    - unfold hb_of. cbn [ab_kind abkind_eqb cb_tok fst snd]. rewrite N.eqb_refl. cbn. intros X; exact X.
  Qed.
  End Sz5.
  #[using="Type"] Lemma lb_remove_LBof : ltac:(let t := eval cbv delta [lb_remove_LBof__stmt] in lb_remove_LBof__stmt in exact t).
  Proof. intros C1 C2 FB FL q A n. ltac2:(SecDiet.SzSec.closeP 'lb_remove_LBof__body "vvvvvvv"). Qed.

  Definition free_core__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PState aheap aptr) (C1 C2 FB : list (@cblock aptr)) (FL : list fblock) (q : aptr) (A n lo : Z),
    GIOA L RNG s (C1 ++ (q, A, n) :: C2) FB FL m -> stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo + FREE_STACK <= bv_unsigned sp ->
    mem_inv asegs m -> tp = Z_to_bv 64 ATP -> bv_unsigned sp mod 16 = 0 -> rng RNG lo (bv_unsigned sp - lo) ->
    unw_okA L RNG m lo AFREE_PC sp s0 ra ->
    implMG RNG (pfree asan_ops q) s
      (fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
         /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL (C1 ++ C2) (bv_unsigned sp)) m m'
         /\ GIOA L RNG' s' (C1 ++ C2) FB FL m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FREE_ENTRY) fc None m (seg_rom asegs)).
  Section Sz6.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s C1 C2 FB FL q A n lo : ltac2:(SecDiet.SzSec.tyM 'free_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="AF GS_pres"] Lemma free_core__body : ltac2:(SecDiet.SzSec.bodyP 'free_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros G ST LO BU MI TPE ALN RSP UNW.
    pose proof G as (AH & RV & AD & EF & SZ & ND & GS).
    destruct UNW as ((tr & AU) & S0 & RA1 & RA2).
    pose proof (lb_remove_LBof C1 C2 FB FL q A n (AI_hb_ids AI _ _ _ _ _ AH)) as ELB.
    unfold implMG, pfree. cbn [ho_free asan_ops]. change FREE_ENTRY with AFREE_SYM.
    eapply implS_ah_free0 with (P := afree_post (aci AI) (AHEAP AI) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (ah_st (ps_heap s))
                                        (LBof (C1 ++ (q, A, n) :: C2) FB FL) q lo m).
    - change (@alloc_ceiling ceil_of_rc) with ATOP.
      eapply (AI_free AI L RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (ah_st (ps_heap s)) (LBof (C1 ++ (q, A, n) :: C2) FB FL) q A n lo tr);
        [ exact AH | apply (In_hb _ _ FL (q, A, n)); apply in_or_app; left; apply in_or_app; right; left; reflexivity
        | exact MI | exact ST | exact LO | unfold FREE_STACK, AFREE_STACK in *; lia | exact TPE | reflexivity
        | exact AU | exact S0 | exact RA1 | exact RA2 | exact ALN | exact RSP ].
    - intros st' RNG' ms' PO. unfold afree_post in PO. destruct PO as (FP & PO). destruct_exs PO. destruct PO as (-> & MI' & ST' & HP & AH').
      rewrite ELB in HP, AH'. cbn [fst snd].
      split; [exact FP|]. eexists _, x14.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
      split; [eapply (pres_keeps AI AF GSTAT); [exact G| first [apply incl_refl | apply incl_tl; apply incl_refl]| exact HP| intros b Hb; exact Hb]|].
      split; [exact AH'|]. cbn [ps_heap set_heap ah_resv ah_addr ah_frames ah_st ah_set_addr ah_set_st].
      split; [exact RV|]. split.
      { intros b Hb.
        assert (Hb' : In b ((C1 ++ (q, A, n) :: C2) ++ FB))
          by (apply in_app_or in Hb as [Hb|Hb]; [apply in_app_or in Hb as [Hb|Hb]|]; apply in_or_app;
              [left; apply in_or_app; left; exact Hb| left; apply in_or_app; right; right; exact Hb| right; exact Hb]).
        rewrite lookup_delete_ne; [exact (AD b Hb')|].
        (* [comment removed for export] *)
        pose proof (AI_hb_ids AI _ _ _ _ _ AH) as NI. intros E.
        assert (IDS : forall l, hb_ids (map hb_of l) = map cb_tok l) by (induction l as [|b0 l IH]; [reflexivity| cbn; f_equal; exact IH]).
        unfold LBof in NI. unfold hb_ids in NI. rewrite flat_map_app in NI. apply NoDup_app_remove_r in NI. fold (hb_ids (map hb_of ((C1 ++ (q, A, n) :: C2) ++ FB))) in NI.
        rewrite IDS, <- app_assoc, map_app in NI. cbn [app map cb_tok fst snd] in NI. apply NoDup_remove_2 in NI. apply NI.
        rewrite E. rewrite <- map_app. apply in_map. rewrite <- app_assoc in Hb. exact Hb. }
      split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
      eapply GS_pres; [exact GS| exact FP| exact HP| intros b Hb; apply In_hb; apply in_or_app; right; exact Hb| unfold FREE_STACK in BU; lia| reflexivity| reflexivity| reflexivity].
  Qed.
  End Sz6.
  #[using="AF GS_pres"] Lemma free_core : ltac:(let t := eval cbv delta [free_core__stmt] in free_core__stmt in exact t).
  Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s C1 C2 FB FL q A n lo. ltac2:(SecDiet.SzSec.closeP 'free_core__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  #[using="AF GS_pres"] Theorem free_o_real : free_stmt_o asan_ops GIOA.
  Proof.
    red. intros until lo. intros PRE -> UNW.
    destruct PRE as (G & ST & LO & BU & [SPT T47] & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    eapply free_core; try eassumption. eapply rng_sub'; [exact RSTK| lia].
  Qed.

  (* [comment removed for export] *)
  Definition free_null_core__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PState aheap aptr) (CL FB : list (@cblock aptr)) (FL : list fblock) (lo : Z),
    GIOA L RNG s CL FB FL m -> stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo + FREE_STACK <= bv_unsigned sp ->
    mem_inv asegs m -> tp = Z_to_bv 64 ATP -> bv_unsigned sp mod 16 = 0 -> rng RNG lo (bv_unsigned sp - lo) ->
    unw_okA L RNG m lo AFREE_PC sp s0 ra ->
    evtF asegs RNG (fun ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
         /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
         /\ GIOA L RNG s CL FB FL m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FREE_ENTRY) fc None m (seg_rom asegs)).
  Section Sz8.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo : ltac2:(SecDiet.SzSec.tyM 'free_null_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="AF GS_pres"] Lemma free_null_core__body : ltac2:(SecDiet.SzSec.bodyP 'free_null_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros G ST LO BU MI TPE ALN RSP UNW.
    pose proof G as (AH & RV & AD & EF & SZ & ND & GS).
    destruct UNW as ((tr & AU) & S0 & RA1 & RA2). change FREE_ENTRY with AFREE_SYM.
    eapply evtF_mono.
    - eapply (AI_free_null AI L RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (ah_st (ps_heap s)) (LBof CL FB FL) lo tr);
        [ exact AH | exact MI | exact ST | exact LO | unfold FREE_STACK, AFREE_STACK in *; lia | exact TPE | reflexivity
        | exact AU | exact S0 | exact RA1 | exact RA2 | exact ALN | exact RSP ].
    - cbv beta. intros ms' PO. unfold afree_null_post in PO. destruct_exs PO. destruct PO as (-> & MI' & ST' & HP & AH').
      eexists _, x14. split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [exact MI'|]. split; [exact ST'|]. split; [eapply (pres_keeps AI AF GSTAT); [exact G| first [apply incl_refl | apply incl_tl; apply incl_refl]| exact HP| intros b Hb; exact Hb]|].
      split; [exact AH'|]. split; [exact RV|]. split; [exact AD|]. split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
      eapply GS_pres; [exact GS| apply fp_le_refl| exact HP| intros b Hb; apply In_hb; apply in_or_app; right; exact Hb| unfold FREE_STACK in BU; lia| reflexivity| reflexivity| reflexivity].
  Qed.
  End Sz8.
  #[using="AF GS_pres"] Lemma free_null_core : ltac:(let t := eval cbv delta [free_null_core__stmt] in free_null_core__stmt in exact t).
  Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo. ltac2:(SecDiet.SzSec.closeP 'free_null_core__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  #[using="AF GS_pres"] Theorem free_null_o_real : free_null_stmt_o GIOA.
  Proof.
    red. intros until lo. intros PRE -> UNW.
    destruct PRE as (G & ST & LO & BU & [SPT T47] & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    eapply free_null_core; try eassumption. eapply rng_sub'; [exact RSTK| lia].
  Qed.

  (* [comment removed for export] *)
  Definition realloc_core__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PState aheap aptr) (C1 C2 FB : list (@cblock aptr)) (FL : list fblock)
      (q : aptr) (A sz lo n : Z) (bs : list byte),
    GIOA L RNG s (C1 ++ (q, A, sz) :: C2) FB FL m -> stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo + REALLOC_STACK <= bv_unsigned sp ->
    mem_inv asegs m -> tp = Z_to_bv 64 ATP -> bv_unsigned sp mod 16 = 0 -> rng RNG lo (bv_unsigned sp - lo) ->
    1 <= n < 2^29 - 2^16 -> rw_cells asegs m A [CB (Z.to_nat sz) bs] -> unw_okA L RNG m lo (tp_rpc TP) sp s0 ra ->
    implMG RNG (prealloc asan_ops q n) s
      (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
         /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL (C1 ++ C2) (bv_unsigned sp)) m m'
         /\ match r with
            | None => False
            | Some q' => exists A' junk, a0v = Z_to_bv 64 A' /\ GIOA L RNG' s' ((q', A', n) :: C1 ++ C2) FB FL m'
                        /\ rw_cells asegs m' A' [CB (Z.to_nat (Z.min sz n)) (firstn (Z.to_nat (Z.min sz n)) bs); CB (Z.to_nat (n - Z.min sz n)) junk]
            end)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REALLOC_ENTRY) fc None m (seg_rom asegs)).
  Section Sz10.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s C1 C2 FB FL q A sz lo n bs : ltac2:(SecDiet.SzSec.tyM 'realloc_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="AF GS_pres AI_realloc HRPC"] Lemma realloc_core__body : ltac2:(SecDiet.SzSec.bodyP 'realloc_core__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros G ST LO BU MI TPE ALN RSP Hn OLD UNW.
    pose proof G as (AH & RV & AD & EF & SZ & ND & GS). rewrite HRPC in UNW.
    destruct UNW as ((tr & AU) & S0 & RA1 & RA2).
    pose proof (lb_remove_LBof C1 C2 FB FL q A sz (AI_hb_ids AI _ _ _ _ _ AH)) as ELB.
    destruct (AI_block AI _ _ _ _ _ q A sz AH ltac:(apply (In_hb _ _ FL (q, A, sz)); apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as (SZ1 & _).
    assert (LBS : length bs = Z.to_nat sz) by (destruct OLD as [[WFc _] _]; cbn [cells_wf cell_wf] in WFc; lia).
    unfold implMG, prealloc. cbn [ho_realloc asan_ops]. change REALLOC_ENTRY with AREALLOC_SYM.
    eapply implS_ah_realloc with (P := arealloc_post (aci AI) (AHEAP AI) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (ah_st (ps_heap s))
                                          (LBof (C1 ++ (q, A, sz) :: C2) FB FL) q sz bs n lo m).
    - change (@alloc_ceiling ceil_of_rc) with ATOP.
      eapply (AI_realloc L RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (ah_st (ps_heap s)) (LBof (C1 ++ (q, A, sz) :: C2) FB FL) q A sz n lo bs tr (ah_resv (ps_heap s)));
        [ exact AH | apply (In_hb _ _ FL (q, A, sz)); apply in_or_app; left; apply in_or_app; right; left; reflexivity | exact OLD
        | exact MI | exact ST | exact LO | unfold REALLOC_STACK, AREALLOC_STACK in *; lia | exact TPE | reflexivity | reflexivity | unfold AREQMAX; lia
        | exact AU | exact S0 | exact RA1 | exact RA2 | exact ALN | exact RSP | exact RV ].
    - intros [st' [id|]] RNG' ms' PO; cbn [fst snd]; unfold arealloc_post in PO; destruct PO as (FP & PO); destruct_exs PO;
        destruct PO as (-> & MI' & ST' & HP & PO); cbn [snd fst] in PO; [| destruct PO].
      destruct PO as (A' & junk & -> & BR & AH' & LJ & CELL & R1 & R2X).
      (* [comment removed for export] *)
      assert (R2 : rng RNG' (shad A') (AsanEmbed.shlen (n + 7))) by (first [exact R2X | exact (proj1 R2X)]). clear R2X.
      rewrite ELB in HP, AH'.
      pose proof BR as (BAND & N0 & TOP & A16). pose proof (ablk_lin _ _ BAND) as (_ & A0 & _ & T47').
      assert (EA : a0_of (MS (mkR ra sp gp tp x x0 x1 s0 s1 (Z_to_bv 64 A') x3 x4 x5 x6 x7 x8 x9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x10 x11 x12 x13) F (ret_pc ra) fc None x14 (seg_rom asegs)) = A').
      { unfold a0_of. etransitivity; [| apply (unsigned_lit A'); lia]. reflexivity. }
      rewrite EA. split; [lia|].
      cbn [enomem_on_null]. apply implF_ret_ok. apply evtF_done. cbn [fst snd].
      split; [exact FP|]. exists (Z_to_bv 64 A'), x14.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
      split; [eapply (pres_keeps AI AF GSTAT); [exact G| first [apply incl_refl | apply incl_tl; apply incl_refl]| exact HP| intros b Hb; exact Hb]|].
      exists A', junk. split; [reflexivity|]. split.
      2:{ (* [comment removed for export] *)
          assert (E : Z.to_nat n = (Z.to_nat (Z.min sz n) + Z.to_nat (n - Z.min sz n))%nat) by lia.
          apply (rw_cells_split_CB asegs _ _ [] _ _ [] [Z.to_nat (Z.min sz n); Z.to_nat (n - Z.min sz n)]) in CELL; [| cbn; lia].
          cbn [mk_CB_cells app] in CELL.
          assert (LF : length (firstn (Z.to_nat (Z.min sz n)) bs) = Z.to_nat (Z.min sz n)) by (rewrite length_firstn; lia).
          rewrite firstn_app, LF, Nat.sub_diag, firstn_O, app_nil_r, firstn_firstn, Nat.min_id in CELL.
          rewrite skipn_app, LF, Nat.sub_diag, skipn_O in CELL.
          rewrite (skipn_all2 (firstn _ bs)) in CELL by lia. cbn [app] in CELL.
          rewrite (firstn_all2 (n := Z.to_nat (n - Z.min sz n)) junk) in CELL by lia. exact CELL. }
      split; [exact AH'|]. cbn [ps_heap set_heap ah_resv ah_addr ah_frames ah_st ah_set_addr ah_set_st].
      split; [exact RV|]. split.
      { intros b Hb. cbn [app] in Hb. destruct Hb as [<-|Hb]; cbn [cb_tok cb_addr fst snd]; [apply lookup_insert_eq|].
        assert (Hb' : In b ((C1 ++ (q, A, sz) :: C2) ++ FB))
          by (apply in_app_or in Hb as [Hb|Hb]; [apply in_app_or in Hb as [Hb|Hb]|]; apply in_or_app;
              [left; apply in_or_app; left; exact Hb| left; apply in_or_app; right; right; exact Hb| right; exact Hb]).
        assert (IDS : forall l, hb_ids (map hb_of l) = map cb_tok l) by (induction l as [|b0 l IH]; [reflexivity| cbn; f_equal; exact IH]).
        rewrite lookup_insert_ne.
        - rewrite lookup_delete_ne; [exact (AD b Hb')|].
          pose proof (AI_hb_ids AI _ _ _ _ _ AH) as NI. intros E.
          unfold LBof in NI. unfold hb_ids in NI. rewrite flat_map_app in NI. apply NoDup_app_remove_r in NI. fold (hb_ids (map hb_of ((C1 ++ (q, A, sz) :: C2) ++ FB))) in NI.
          rewrite IDS, <- app_assoc, map_app in NI. cbn [app map cb_tok fst snd] in NI. apply NoDup_remove_2 in NI. apply NI.
          rewrite E. rewrite <- map_app. apply in_map. rewrite <- app_assoc in Hb. exact Hb.
        - pose proof (AI_hb_ids AI _ _ _ _ _ AH') as NI. unfold LBof in NI. cbn [map app hb_ids flat_map hb_of ab_kind cb_tok fst snd] in NI.
          apply List.NoDup_cons_iff in NI as [NI _]. intros E. apply NI. rewrite E.
          apply in_flat_map. exists (hb_of b). split; [apply in_or_app; left; apply in_map; exact Hb| left; reflexivity]. }
      split; [exact EF|]. split; [exact SZ|]. split; [exact ND|].
      eapply GS_pres; [exact GS| exact FP| exact HP| intros b Hb; apply In_hb; apply in_or_app; right; exact Hb| unfold REALLOC_STACK in BU; lia| reflexivity| reflexivity| reflexivity].
  Qed.
  End Sz10.
  #[using="AF GS_pres AI_realloc HRPC"] Lemma realloc_core : ltac:(let t := eval cbv delta [realloc_core__stmt] in realloc_core__stmt in exact t).
  Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s C1 C2 FB FL q A sz lo n bs. ltac2:(SecDiet.SzSec.closeP 'realloc_core__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  #[using="AF GS_pres AI_realloc HRPC"] Theorem realloc_o_real : realloc_stmt_o asan_ops GIOA TP.
  Proof.
    red. intros until bs. intros PRE -> -> Hn OLD UNW.
    destruct PRE as (G & ST & LO & BU & [SPT T47] & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    eapply realloc_core; try eassumption. eapply rng_sub'; [exact RSTK| lia].
  Qed.
End GioaAlloc.
End CANSEC1.
End TwB.
