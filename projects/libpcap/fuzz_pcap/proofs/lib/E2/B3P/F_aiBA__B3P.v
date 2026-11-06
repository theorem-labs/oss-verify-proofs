(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB AiAuxB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require AccFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnEA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_aiBA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require Import UbGuardB AiAuxB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AccFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac ck_branch :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      tryif (match c with context [?x] => is_var x end) then first [ if_false | if_true ]
      else (let v := eval vm_compute in c in
            lazymatch v with true => first [ if_true | if_false ] | false => first [ if_false | if_true ] | _ => first [ if_false | if_true ] end)
  | _ => first [ if_false | if_true ]
  end.
Local Ltac ck_go ::= ck_steps 8%nat; ck_branch.
(* [comment removed for export] *)
Local Ltac ck_sh_small A1 A2 := first [ clear - A1 A2; sh_lia | sh_lia ].
Local Ltac ck0_at UNP P ::=
  ck_clear;
  lazymatch goal with
  | |- evtF _ ?RNG _ (MS _ _ _ _ _ ?m _) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
        let RD := fresh "RDsh" in let A1 := fresh "CKlo" in let A2 := fresh "CKhi" in
        assert (A1 : (lo <= P)%Z) by ck_lia;
        assert (A2 : (8 * (P / 8) + 8 <= hi)%Z) by (pose proof (Z.mul_div_le P 8 (eq_refl : (0 < 8)%Z)) as CKgr; ck_lia);
        pose proof (ck_full_rd m lo hi P UNP A1 A2) as RD;
        first [ let ACC := fresh "ACCsh" in
                match goal with
                | H : rng RNG (shad lo) ?len |- _ => pose proof (ck_acc RNG (shad lo) len P H ltac:(ck_sh_small A1 A2) ltac:(ck_sh_small A1 A2)) as ACC
                end
              | clear A1 A2; ck_fp_at lo P ];
        try clear A1 A2
    | unpoisoned ?m' _ _ => fail "ck0: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
(* [comment removed for export] *)
Local Ltac acc_hint ::= acc_hint_cheap.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.


Ltac apA lem := eapply lem; try eassumption.
Ltac transport H m' AG tac :=
  lazymatch type of H with rw_cells ?sg _ ?A ?cs =>
    let X := fresh in
    assert (X : rw_cells sg m' A cs) by (eapply agrees_rw_cells; [exact AG | exact H | tac]);
    clear H; rename X into H end.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section AIX.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (L : alayout) (RNG : footprint) (st : PS) (C1 C2 FB : list cblk) (FL : list fblock) (P B I CUR EB lo idb_off : Z).
  Variables (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte).
  Hypothesis G : GIOA L RNG st (C1 ++ IBLK i I s ++ C2) FB FL m.
  Hypothesis LO : (ATOP + 4096 <= lo)%Z.
  Hypothesis BU : (lo + 16528 <= bv_unsigned sp)%Z.
  Hypothesis SPT : (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RTLS : rng_atls RNG.
  Hypothesis TPE : tp = Z_to_bv 64 ATP.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.

  #[local] Abbreviation POSTQ := (add_interface_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st)).
  #[local] Abbreviation AGP := (ai_AGP FL sp C1 C2 P B CUR EB p m).
  #[local] Abbreviation FRAME := (ai_FRAME ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

  (* [comment removed for export] *)
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis HinP : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2).
  Hypothesis HinB : In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2).
  Hypothesis P14 : (0 < P /\ P + 680 <= ATOP)%Z.
  Hypothesis B14 : (0 < B /\ B + pc_bufalloc p <= ATOP)%Z.
  Hypothesis LENB : (Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32)%Z.
  Hypothesis CURS : (bv_unsigned sp <= CUR /\ CUR + 24 <= al_top L)%Z.
  (* [comment removed for export] *)
  Hypothesis EBL : clocA FL (C1 ++ C2) EB 256.
  Hypothesis EBP : (EB + 256 <= P + 648 \/ P + 680 <= EB)%Z.
  Hypothesis EBB : (EB + 256 <= B \/ B + pc_bufalloc p <= EB)%Z.

  #[local] Abbreviation AIREST_F := (ai_REST_F GIOA L).
  Hypothesis EBO : cobjA RNG m FL (C1 ++ C2) EB 256 \/ (P + 216 = EB)%Z.

  Hypothesis UTS : (0 < ng_user_tsresol s < 2^64)%Z.
  Hypothesis IFW : Forall if_wf (ng_ifaces s).

  #[local] Abbreviation ai_snap := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_snap idb_off p).
  #[local] Abbreviation ai_slot := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot idb_off p s).
  #[local] Abbreviation ai_result := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result idb_off p s c).

  (* [comment removed for export] *)
  Definition ai_head__stmt : Prop := forall (RNG3 : footprint) (st3 : PS) (q1 : hptr) (I' N : Z) (m3 : mem),
    GIOA L RNG3 st3 ((q1, I', N) :: C1 ++ C2) FB FL m3 -> (0 < N)%Z ->
    (0 < I' /\ I' + N <= ATOP /\ I' mod 16 = 0)%Z /\ unpoisoned m3 I' (I' + N) /\ rng RNG3 I' N /\ rng RNG3 (shad I') (nshad N)
    /\ (exists bI, (0 <= bI <= 1 /\ I' + N <= 2147446784 + bI * 140737479966720 /\ 17594333495296 * bI <= I' /\ 6307840 <= I')%Z)
    /\ (P + 680 <= I' \/ I' + N <= P)%Z /\ (B + pc_bufalloc p <= I' \/ I' + N <= B)%Z /\ (EB + 256 <= I' \/ I' + N <= EB)%Z.
  Section Sz1.
  Variables RNG3 st3 q1 I' N m3 : ltac2:(SecDiet.SzSec.tyM 'ai_head__stmt "vvvvvv" @RNG3).
  Lemma ai_head__body : ltac2:(SecDiet.SzSec.bodyP 'ai_head__stmt "vvvvvv").
  Proof using BU EBL GL GPL HinB HinP LO.
    intros G3 HN.
 pose proof atop_range as AR.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G3 (or_introl eq_refl : In (q1, I', N) (((q1, I', N) :: C1 ++ C2) ++ FB))) as ((IBAND & I3 & ITOP & I2) & I1 & IUNP & IRNG & IRSH & IAR).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G3) as BA. cbn [app blocks_apart] in BA. destruct BA as [FA _].
    pose proof (proj1 (Forall_forall _ _) FA _ (in_or_app _ _ _ (or_introl HinP))) as AP. pose proof (proj1 (Forall_forall _ _) FA _ (in_or_app _ _ _ (or_introl HinB))) as AB.
    unfold apart in AP, AB. cbn [cb_addr cb_size fst snd] in AP, AB. unfold PCAP_NG_SF_TOTAL in AP.
    assert (G3p : GIOA L RNG3 st3 ((C1 ++ C2) ++ [(q1, I', N)]) FB FL m3) by (eapply GPL; [exact G3| change ((q1, I', N) :: C1 ++ C2) with ([(q1, I', N)] ++ (C1 ++ C2)); apply Permutation.Permutation_app_comm]).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G3p EBL (or_introl eq_refl : In (q1, I', N) [(q1, I', N)]) ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kI & kIr & kI1 & kI2).
    cbn [cb_addr cb_size fst snd] in kI1, kI2.
    assert (EBL3 : clocA FL ((q1, I', N) :: C1 ++ C2) EB 256) by (eapply clocA_incl; [exact EBL | apply incl_tl, incl_refl | apply incl_refl]).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G3 EBL3) as (EBLO & EBHI).
    split; [lia|]. split; [exact IUNP|]. split; [exact IRNG|]. split; [exact IRSH|].
    split; [band_ind IBAND bI; exists bI; lia|]. split; [lia|]. split; [lia|]. lia.
  Qed.
  End Sz1.
  Lemma ai_head : ltac:(let t := eval cbv delta [ai_head__stmt] in ai_head__stmt in exact t).
  Proof using BU EBL GL GPL HinB HinP LO. intros RNG3 st3 q1 I' N m3. ltac2:(SecDiet.SzSec.closeP 'ai_head__body "vvvvvv"). Qed.

  Lemma ifs_cells_app : forall (l1 l2 : list ng_if) (j1 j2 : list if_junk),
    length j1 = length l1 -> ifs_cells l1 j1 ++ ifs_cells l2 j2 = ifs_cells (l1 ++ l2) (j1 ++ j2).
  Proof using .
    clear. induction l1 as [|i0 l1 IH]; intros l2 [|j j1] j2 HL; cbn [length] in HL; try discriminate HL; [reflexivity|].
    cbn [ifs_cells app]. rewrite <- app_assoc. f_equal. apply IH. lia.
  Qed.

  (* [comment removed for export] *)
  Definition ai_tail__stmt : Prop := forall (ra' t0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t5' y0 y3 y4 y7 y8 y9 y10 y11 : word)
      (m3 : mem) (RNG3 : footprint) (stG : PS) (sg : pcap_ng_sf) (q1 : hptr) (I' SA : Z) (js : list if_junk) (pad1 sj tail3 bs3 cpad3 : list byte)
      (opts : idbopts) (c' : cursor) (buf' : list Z) (hj h0 h1 h2 : cell),
    ng_user_tsresol sg = ng_user_tsresol s -> ng_max_blocksize sg = ng_max_blocksize s -> ng_ifaces sg = ng_ifaces s ->
    (ng_ifcount sg = Z.of_nat (length (ng_ifaces s)) + 1)%Z -> (ng_ifcount sg <= ng_ifaces_size sg)%Z -> (1 <= ng_ifaces_size sg < 2^26)%Z ->
    length js = length (ng_ifaces s) ->
    (SA = I' + 40 * (ng_ifcount sg - 1))%Z ->
    (0 <= ai_snap < 2^32)%Z -> (0 < io_tsresol opts < 2^64)%Z ->
    fp_le RNG RNG3 ->
    mem_inv asegs m3 -> stk asegs m3 lo (bv_unsigned sp + -144) -> AGP m3 ->
    rw_cells asegs m3 (bv_unsigned sp + -144) [hj; h0; h1; h2; C8 (Z_to_bv 64 (Z.shiftr (P + 672) 3 + 2147450880))] ->
    csize hj = 8%nat -> csize h0 = 8%nat -> csize h1 = 8%nat -> csize h2 = 8%nat -> FRAME m3 ->      (* [comment removed for export] *)
    rw_cells asegs m3 (P + 648) (ng_cells sg I' pad1) ->
    rw_cells asegs m3 I' (ifs_cells (rev (ng_ifaces s)) js) ->
    rw_cells asegs m3 SA [C4 (Z_to_bv 64 ai_snap); CB 36 sj] ->
    rw_cells asegs m3 (SA + 40) [CB (Z.to_nat (40 * (ng_ifaces_size sg - ng_ifcount sg))) tail3] ->
    GIOA L RNG3 stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB FL m3 ->
    rw_cells asegs m3 B [CB (Z.to_nat (pc_bufalloc p)) bs3] -> firstn (length buf') bs3 = map b8 buf' -> length buf' = length (pc_bufdata p) ->
    Forall (fun z => 0 <= z < 256)%Z buf' ->
    rw_cells asegs m3 CUR (cursor_cells B c' cpad3) ->
    (0 <= cur_remaining c')%Z -> (cur_off c <= cur_off c')%Z -> (cur_off c' + cur_remaining c' <= cur_off c + cur_remaining c)%Z -> cur_block_type c' = cur_block_type c ->
    rw_cells asegs m3 EB [CB 256 ej] -> ps_outfile stG = ps_outfile st ->
    evtF asegs RNG3 (POSTQ (ai_result sg (Some q1) (buf', inr (opts, c'))) stG RNG3)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' (Z_to_bv 64 (io_tsresol opts)) (Z_to_bv 64 (Z.b2z (io_is_binary opts)))
               y0 (Z_to_bv 64 (P + 648)) a0' a1' a2' a3' a4' a5' a6' a7'
               (Z_to_bv 64 (P + 660)) y3 y4 (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 660) 3 + 2147450880)) y7 y8 y9 y10 y11
               t3' (Z_to_bv 64 (io_tsoffset opts)) t5' (Z_to_bv 64 (P + 672)))
          F (Z_to_bv 64 0x8c850) fc None m3 (seg_rom asegs)).
  Section Sz3.
  Variables ra' t0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t5' y0 y3 y4 y7 y8 y9 y10 y11 m3 RNG3 stG sg q1 I' SA js pad1 sj tail3 bs3 cpad3 opts c' buf' hj h0 h1 h2 : ltac2:(SecDiet.SzSec.tyM 'ai_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ai_tail__body : ltac2:(SecDiet.SzSec.bodyP 'ai_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU CURS EBB EBL EBP GL GPL HinB HinP IFW LENB LO P14 RSTK SPT UTS.
 intros U1 U2 U5 IC1 IC2 SZ LJS HSA SNR TSR FP3 MI3 ST3 AG3 HD3 Hhj Hh0 Hh1 Hh2 FR3 NG3 AR1 SL3 AR2 G3 BUF3 PFX3 LB3 GR3 CC3 CR1 CR2 CR3 CR4 HEB3 OFG.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as AR.
    set (hd := [hj; h0; h1; h2; C8 (Z_to_bv 64 (Z.shiftr (P + 672) 3 + 2147450880))]) in *.
    assert (Hhd : cells_size hd = 40%nat) by (subst hd; cbn [cells_size csize Nat.add]; rewrite Hhj, Hh0, Hh1, Hh2; reflexivity).
    assert (HD32 : rw_cells asegs m3 (bv_unsigned sp + -112) [C8 (Z_to_bv 64 (Z.shiftr (P + 672) 3 + 2147450880))]).
    { destruct (rw_cells_cut _ _ _ 4 HD3) as [_ HDJ]. subst hd. cbn [firstn skipn cells_size Nat.add] in HDJ. rewrite Hhj, Hh0, Hh1, Hh2 in HDJ.
      replace (bv_unsigned sp + -144 + Z.of_nat (8 + (8 + (8 + (8 + 0)))))%Z with (bv_unsigned sp + -112)%Z in HDJ by lia. exact HDJ. }
    destruct (ai_head _ _ _ _ _ _ G3 ltac:(lia)) as ((Q1 & Q4 & Q2) & IUNP & IRNG & IRSH & (bI & bIr & bIhi & bIlo & bIimg) & API & APIB & APIE).
    assert (HinP3 : In (pc_self p, P, PCAP_NG_SF_TOTAL) (((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) ++ FB)) by (apply in_or_app; left; right; exact HinP).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G3 HinP3) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    cbn [cb_addr cb_size fst snd] in PBAND, P3, PTOP, P2, P1, PUNP, PRNG, PRSH. unfold PCAP_NG_SF_TOTAL in *.
    band_ind PBAND bP.
    assert (RSPW : rng RNG3 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact (rng_fp_le _ _ _ _ FP3 RSTK)| lia]).
    unfold ai_FRAME in FR3. unfold ng_cells in NG3.
    pose proof (rw_cells_bound _ _ _ _ AR1) as BA1. rewrite ifs_cells_size in BA1 by (rewrite length_rev; lia). rewrite length_rev in BA1.
    assert (LSJ : length sj = 36%nat) by (destruct SL3 as [[WF _] _]; cbn in WF; lia).
    (* [comment removed for export] *)
    assert (FIN : forall (m5 : mem) (jn : if_junk),
      munch [(SA, SA + 40)]%Z m3 m5 -> wmono asegs m3 m5 ->
      rw_cells asegs m5 SA (if_cells (ai_slot opts) jn) ->
      ai_REST GIOA L RNG3 FL C1 C2 FB P B CUR EB p s c ej (ps_outfile st) m5 stG (ai_result sg (Some q1) (buf', inr (opts, c')))).
    { intros m5 jn MU WM SL5.
      assert (AGS : agrees_on (fun a => outside [(SA, SA + 40)]%Z a) m3 m5) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      transport NG3 m5 AGS ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
      transport AR2 m5 AGS ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
      transport BUF3 m5 AGS ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
      transport AR1 m5 AGS ltac:(intros a Ha; rewrite ifs_cells_size in Ha by (rewrite length_rev; lia); rewrite length_rev in Ha; cbn [outside fst snd]; split; [lia| exact Logic.I]).
      transport CC3 m5 AGS ltac:(intros a Ha; unfold cursor_cells in Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
      transport HEB3 m5 AGS ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
      assert (G5 : GIOA L RNG3 stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB FL m5).
      { eapply (gl_client_frame _ _ _ GL); [exact G3 | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil]. right; left. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result. exists (mkNg (ng_user_tsresol sg) (ng_max_blocksize sg) (ng_ifcount sg) (ng_ifaces_size sg) (ai_slot opts :: ng_ifaces sg)), (Some q1), I', pad1, bs3.
      split; [exact OFG|]. split; [reflexivity|]. split; [exact G5|]. split; [exact NG3|]. split; [cbn; exact U1|]. split; [cbn; exact U2|]. split; [cbn; lia|]. split; [cbn; lia|].
      split; [exact BUF3|]. split; [exact PFX3|]. split; [exact LB3|]. split; [exact GR3|]. cbv iota.
      split.
      { unfold ifaces_ok. cbn [pc_priv set_ng set_priv set_bufdata ng_ifaces ng_ifaces_size ng_ifcount].
        exists (js ++ [jn]), tail3. split; [rewrite !length_app, LJS, U5; cbn [length]; lia|].
        split; [| rewrite U5; cbn [length]; split; [lia|]; split; [lia|]; split; [lia|];
                  constructor; [| exact IFW];
                  unfold if_wf, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_scale; cbn [if_tsresol if_scale_type if_scale_factor];
                  destruct (io_tsresol opts =? ng_user_tsresol s)%Z eqn:QX1; [cbn; split; [exact TSR| discriminate]|];
                  destruct (ng_user_tsresol s <? io_tsresol opts)%Z eqn:QX2; destruct (io_is_binary opts); cbn [is_dec if_scale_factor];
                  (split; [exact TSR|]); intros Hd; try discriminate Hd;
                  [ apply Z.ltb_lt in QX2; split; [apply Z.div_str_pos; lia| apply Z.div_lt_upper_bound; lia]
                  | apply Z.ltb_ge in QX2; apply Z.eqb_neq in QX1; split; [apply Z.div_str_pos; lia| apply Z.div_lt_upper_bound; lia] ] ].
        cbn [rev]. rewrite <- (ifs_cells_app (rev (ng_ifaces sg)) [ai_slot opts] js [jn]) by (rewrite length_rev, LJS, U5; reflexivity).
        cbn [ifs_cells]. rewrite app_nil_r, U5.
        pose proof (rw_cells_uncut _ _ _ _ _ AR1 SL5 ltac:(rewrite ifs_cells_size by (rewrite length_rev; lia); rewrite length_rev; lia)) as J1.
        pose proof (rw_cells_uncut _ _ _ _ _ J1 AR2 ltac:(rewrite cells_size_app, ifs_cells_size, if_cells_size by (rewrite length_rev; lia); rewrite length_rev; lia)) as J2.
        exact J2. }
      split; [exists cpad3; exact CC3|]. split; [exact CR1|]. split; [exact CR2|]. split; [exact CR3|]. split; [exact CR4|]. split; [exact HEB3| reflexivity]. }
    hide HD3. hide FR3. hide AR1. hide AR2. hide BUF3. hide CC3. hide HEB3.
    pose proof (munch_refl [(SA, SA + 40)]%Z m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    ck0_at PUNP (P + 672)%Z.
    zstep.                                   (* [comment removed for export] *)
    ck_go.
    ck0_at PUNP (P + 660)%Z; ck_go.
    zstep. rewrite (sx32_small (ng_ifcount sg)) by lia.
    do 6 zstep.
  replace (Z.shiftr ((Z.shiftl (ng_ifcount sg + -1) 32) mod 18446744073709551616 * 171798691840) 64) with ((ng_ifcount sg - 1) * 40)%Z
    by (rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mod_small by lia; change (2^32)%Z with 4294967296%Z; rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.mulhu40 (ng_ifcount sg + -1)) by lia; lia).
  replace (I' + (ng_ifcount sg - 1) * 40)%Z with SA by lia.
  assert (SAR : (I' <= SA /\ SA + 40 <= I' + 40 * ng_ifaces_size sg /\ SA mod 8 = 0)%Z) by (clear -HSA IC1 IC2 SZ Q2; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  zstep. ub_ltu.
  do 4 zstep. ub_xnull.
  ub_null.
  zstep. ub_al 7%Z ltac:(exact (proj2 (proj2 SAR))). zstep. if_false.
  zstep. ck0 IUNP; ck_go.
  zstep.
  ub_null.                                   (* [comment removed for export] *)
  zstep. ck0 IUNP; ck_go.
  zstep.
  ck0_at PUNP (P + 648)%Z; ck_go.
  zstep. zstep.
    (* [comment removed for export] *)
    assert (LEAF : forall (ra'' t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 : word) (m5 : mem) (jn : if_junk),
      mem_inv asegs m5 -> stk asegs m5 lo (bv_unsigned sp + -144) ->
      munch [(SA, SA + 40)]%Z m3 m5 -> wmono asegs m3 m5 ->
      rw_cells asegs m5 SA (if_cells (ai_slot opts) jn) ->
      evtF asegs RNG3 (POSTQ (ai_result sg (Some q1) (buf', inr (opts, c'))) stG RNG3)
        (MS (mkR ra'' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0'' t1'' t2'' z0 z1 (Z_to_bv 64 1) a1'' a2'' a3'' a4'' a5'' a6'' a7''
                 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 t3'' t4'' t5'' t6'') F (Z_to_bv 64 0x8caf4) fc None m5 (seg_rom asegs))).
    { intros until jn. intros MI5 ST5 MU5 WM5 SL5.
      assert (AGS : agrees_on (fun a => outside [(SA, SA + 40)]%Z a) m3 m5) by (eapply agrees_on_of_munch; [exact MU5 | exact WM5 | intros a _ Ho; exact Ho]).
      unhide HD3. unhide FR3.
      transport HD3 m5 AGS ltac:(intros a Ha; rewrite Hhd in Ha; cbn [outside fst snd]; lia).
      transport FR3 m5 AGS ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
      unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result.
      eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB.ai_exit with (ok := true) (hd := hd); try eassumption.
      - eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|[Ha|[Ha|Ha]]] _]; cbn [outside fst snd]; (split; [| exact Logic.I]).
        + lia.
        + destruct (proj1 (in_block_In _ _) Ha) as (b' & Hin & Hr).
          pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G3) as BA. cbn [app blocks_apart] in BA. destruct BA as [FA _].
          pose proof (proj1 (Forall_forall _ _) FA _ (in_or_app _ _ _ (or_introl Hin))) as AP. unfold apart in AP. cbn [cb_addr cb_size fst snd] in AP. lia.
        + intros Hr. apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G3 Ha). apply in_block_app. left. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
        + pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G3 Ha) as SBD. lia.
      - pose proof (FIN m5 jn MU5 WM5 SL5) as X. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result in X. exact X. }
    assert (U0 : (0 < ng_user_tsresol sg < 2^64)%Z) by (rewrite U1; exact UTS).
    destruct (Z.eq_dec (io_tsresol opts) (ng_user_tsresol sg)) as [TE|TE].
    - (* [comment removed for export] *)
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ TE). cbn [negb]. cbv iota.
      zstep.
  ck0 IUNP; ck_go.
  do 3 zstep.
        eapply LEAF; [assumption | assumption | exact MU | exact WM |].
      lazymatch type of SL3 with rw_cells _ _ _ [_; CB 4 ?a; _; _; CB 12 ?b; _] =>
        eapply (rw_cells_recell _ _ _ (if_cells (ai_slot opts) (mkIJ a (firstn 4 b) (bv_extract 0 64 (le_bytes_to_word (skipn 4 b))))));
        [exact SL3 | pose proof (proj1 (proj1 SL3)) as WF; cbn in WF |- *; repeat split; try exact Logic.I; rewrite ?length_firstn, ?length_skipn in *; lia |];
        unfold if_cells, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_scale; rewrite (proj2 (Z.eqb_eq (io_tsresol opts) (ng_user_tsresol s)) ltac:(lia));
        cbn [cells_bytes cbytes app ij_p1 ij_p2 ij_sf if_snaplen if_tsresol if_scale_type if_scale_factor if_tsoffset ngscale_code is_dec];
        pose proof (proj1 (proj1 SL3)) as WF; cbn in WF; rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_memmove.le8_ld (skipn 4 b)) by (rewrite ?length_skipn, ?length_firstn in *; lia);
        rewrite <- (firstn_skipn 4 b) at 3; rewrite <- ?app_assoc; reflexivity
      end.
    - rewrite (eqb_lits_false (io_tsresol opts) (ng_user_tsresol sg) ltac:(lia) ltac:(lia) TE). cbn [negb]. cbv iota.
      zstep.
      destruct (Z.lt_ge_cases (ng_user_tsresol sg) (io_tsresol opts)) as [LT|GE].
      + (* [comment removed for export] *)
        replace (bv_ltu (Z_to_bv 64 (ng_user_tsresol sg)) (Z_to_bv 64 (io_tsresol opts))) with true
          by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
        destruct (io_is_binary opts) eqn:BIN; cbn [Z.b2z].
        * (* [comment removed for export] *)
          zstep. if_false. zstep.
          ck0 IUNP; ck_go.
          do 5 zstep.
          eapply LEAF; [assumption | assumption | exact MU | exact WM |].
          lazymatch type of SL3 with rw_cells _ _ _ [_; CB 4 ?a; _; _; CB 12 ?b; _] =>
            eapply (rw_cells_recell _ _ _ (if_cells (ai_slot opts) (mkIJ a (firstn 4 b) (bv_extract 0 64 (le_bytes_to_word (skipn 4 b))))));
            [exact SL3 | pose proof (proj1 (proj1 SL3)) as WF; cbn in WF |- *; repeat split; try exact Logic.I; rewrite ?length_firstn, ?length_skipn in *; lia |];
            unfold if_cells, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_scale; rewrite (proj2 (Z.eqb_neq (io_tsresol opts) (ng_user_tsresol s)) ltac:(lia)), (proj2 (Z.ltb_lt (ng_user_tsresol s) (io_tsresol opts)) ltac:(lia)), BIN;
            cbn [cells_bytes cbytes app ij_p1 ij_p2 ij_sf if_snaplen if_tsresol if_scale_type if_scale_factor if_tsoffset ngscale_code is_dec];
            pose proof (proj1 (proj1 SL3)) as WF; cbn in WF; rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_memmove.le8_ld (skipn 4 b)) by (rewrite ?length_skipn, ?length_firstn in *; lia);
            rewrite <- (firstn_skipn 4 b) at 3; rewrite <- ?app_assoc; reflexivity
          end.
        * (* [comment removed for export] *)
          zstep. if_true.
          ub_null.                               (* [comment removed for export] *)
          zstep.
          ck0 IUNP; ck_go.
          zstep.
          rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.m_divu (Z_to_bv 64 (io_tsresol opts)) (Z_to_bv 64 (ng_user_tsresol sg))) by (rewrite unsigned_lit by lia; lia).
          rewrite !(unsigned_lit (io_tsresol opts)), !(unsigned_lit (ng_user_tsresol sg)) by lia.
          zstep. zstep.
          ck0 IUNP; ck_go.
          do 4 zstep.
          eapply LEAF; [assumption | assumption | exact MU | exact WM |].
          lazymatch type of SL3 with rw_cells _ _ _ [_; CB 4 ?a; _; _; CB 4 ?b; _; _] =>
            eapply (rw_cells_recell _ _ _ (if_cells (ai_slot opts) (mkIJ a b (Z_to_bv 64 0))));
            [exact SL3 | pose proof (proj1 (proj1 SL3)) as WF; cbn in WF |- *; repeat split; try exact Logic.I; rewrite ?length_firstn, ?length_skipn in *; lia |];
            unfold if_cells, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_scale; rewrite (proj2 (Z.eqb_neq (io_tsresol opts) (ng_user_tsresol s)) ltac:(lia)), (proj2 (Z.ltb_lt (ng_user_tsresol s) (io_tsresol opts)) ltac:(lia)), BIN;
            cbn [cells_bytes cbytes app ij_p1 ij_p2 ij_sf if_snaplen if_tsresol if_scale_type if_scale_factor if_tsoffset ngscale_code is_dec];
            rewrite <- U1; rewrite <- ?app_assoc; reflexivity
          end.
      + (* [comment removed for export] *)
        replace (bv_ltu (Z_to_bv 64 (ng_user_tsresol sg)) (Z_to_bv 64 (io_tsresol opts))) with false
          by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_ge; lia). cbn [negb]. cbv iota.
        destruct (io_is_binary opts) eqn:BIN; cbn [Z.b2z].
        * (* [comment removed for export] *)
          zstep. if_false. zstep.
          ck0 IUNP; ck_go.
          do 5 zstep.
          eapply LEAF; [assumption | assumption | exact MU | exact WM |].
          lazymatch type of SL3 with rw_cells _ _ _ [_; CB 4 ?a; _; _; CB 12 ?b; _] =>
            eapply (rw_cells_recell _ _ _ (if_cells (ai_slot opts) (mkIJ a (firstn 4 b) (bv_extract 0 64 (le_bytes_to_word (skipn 4 b))))));
            [exact SL3 | pose proof (proj1 (proj1 SL3)) as WF; cbn in WF |- *; repeat split; try exact Logic.I; rewrite ?length_firstn, ?length_skipn in *; lia |];
            unfold if_cells, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_scale; rewrite (proj2 (Z.eqb_neq (io_tsresol opts) (ng_user_tsresol s)) ltac:(lia)), (proj2 (Z.ltb_ge (ng_user_tsresol s) (io_tsresol opts)) ltac:(lia)), BIN;
            cbn [cells_bytes cbytes app ij_p1 ij_p2 ij_sf if_snaplen if_tsresol if_scale_type if_scale_factor if_tsoffset ngscale_code is_dec];
            pose proof (proj1 (proj1 SL3)) as WF; cbn in WF; rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_memmove.le8_ld (skipn 4 b)) by (rewrite ?length_skipn, ?length_firstn in *; lia);
            rewrite <- (firstn_skipn 4 b) at 3; rewrite <- ?app_assoc; reflexivity
          end.
        * (* [comment removed for export] *)
          zstep. if_true.
          ub_null.                               (* [comment removed for export] *)
          zstep.
          ck0 IUNP; ck_go.
          zstep.
          rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.m_divu (Z_to_bv 64 (ng_user_tsresol sg)) (Z_to_bv 64 (io_tsresol opts))) by (rewrite unsigned_lit by lia; lia).
          rewrite !(unsigned_lit (io_tsresol opts)), !(unsigned_lit (ng_user_tsresol sg)) by lia.
          zstep. zstep.
          ck0 IUNP; ck_go.
          do 3 zstep.
          eapply LEAF; [assumption | assumption | exact MU | exact WM |].
          lazymatch type of SL3 with rw_cells _ _ _ [_; CB 4 ?a; _; _; CB 4 ?b; _; _] =>
            eapply (rw_cells_recell _ _ _ (if_cells (ai_slot opts) (mkIJ a b (Z_to_bv 64 0))));
            [exact SL3 | pose proof (proj1 (proj1 SL3)) as WF; cbn in WF |- *; repeat split; try exact Logic.I; rewrite ?length_firstn, ?length_skipn in *; lia |];
            unfold if_cells, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_scale; rewrite (proj2 (Z.eqb_neq (io_tsresol opts) (ng_user_tsresol s)) ltac:(lia)), (proj2 (Z.ltb_ge (ng_user_tsresol s) (io_tsresol opts)) ltac:(lia)), BIN;
            cbn [cells_bytes cbytes app ij_p1 ij_p2 ij_sf if_snaplen if_tsresol if_scale_type if_scale_factor if_tsoffset ngscale_code is_dec];
            rewrite <- U1; rewrite <- ?app_assoc; reflexivity
          end.
  Qed.
  End Sz3.
  Lemma ai_tail : ltac:(let t := eval cbv delta [ai_tail__stmt] in ai_tail__stmt in exact t).
  Proof using BU CURS EBB EBL EBP GL GPL HinB HinP IFW LENB LO P14 RSTK SPT UTS. intros ra' t0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t5' y0 y3 y4 y7 y8 y9 y10 y11 m3 RNG3 stG sg q1 I' SA js pad1 sj tail3 bs3 cpad3 opts c' buf' hj h0 h1 h2. ltac2:(SecDiet.SzSec.closeP 'ai_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End AIX.
End CANSEC1.
End F_aiBA.

(* [comment removed for export] *)
Module F_aiEA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require Import UbGuardB AiAuxB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiBA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.


Ltac apA lem := eapply lem; try eassumption.
Ltac transport H m' AG tac :=
  lazymatch type of H with rw_cells ?sg _ ?A ?cs =>
    let X := fresh in
    assert (X : rw_cells sg m' A cs) by (eapply agrees_rw_cells; [exact AG | exact H | tac]);
    clear H; rename X into H end.

Ltac msg_ok := vm_compute; repeat first [apply Forall_nil | apply Forall_cons; [split; reflexivity|]].
(* [comment removed for export] *)
Ltac fmt_at_tac MI ADDR str :=
  split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs _ ADDR (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string str) ++ [Z_to_bv 8 0])
                   MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
  split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right]).

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac ckp_at UNP P N :=
    ck_clear;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      lazymatch type of UNP with
      | unpoisoned m ?lo ?hi =>
        let b := fresh "shb" in let RD := fresh "RDsh" in let CK := fresh "CKsh" in let SR := fresh "SRsh" in
        destruct (ck_part_rd m lo hi P N UNP ltac:(ck_lia) ltac:(ck_lia) ltac:(lia) ltac:(ck_lia)) as (b & RD & CK);
        ck_fp_at lo P;
        pose proof (sval_range b) as SR
      | unpoisoned ?m' _ _ => fail "ckp: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
      end
    end.
  Ltac ck_cut OK RS :=
    cbv beta delta [mkR];
    lazymatch goal with
    | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
        eapply (evtF_cut segs RNG (fun ms' => ck_post RS (fun R' => ms' = MS R' F (Z_to_bv 64 OK) fc rv m ro) R));
        [ ck_arm OK 16%nat
        | let ms' := fresh "ms'" in let H := fresh "Hck" in
          intros ms' H; cbn [ck_post] in H; destruct_exs H; subst ms'; simp_regs ]
    end.
  
  (* [comment removed for export] *)
  Definition swap_hdrA__stmt : Prop := forall (RNGx : footprint) (ra_ sp_ gp_ tp_ t1 t2 s0_ s1_ a1 a2 a3 a4 a5 a7 s2_ s3_ s4_ s6_ s7_ s8_ s9_ s10_ s11_ t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc_ : bv 32)
           (mx : mem) (u0 u1 u2 u3 : Z) (Bq alloc bB D : Z),
      (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> (0 <= u2 < 256)%Z -> (0 <= u3 < 256)%Z ->
      rw_cells asegs mx D [Cells.C2 (Z_to_bv 64 (u0 + 256 * u1)); Cells.C2 (Z_to_bv 64 (u2 + 256 * u3))] ->
      mem_inv asegs mx ->
      unpoisoned mx Bq (Bq + alloc) -> (Bq <= D)%Z -> (D + 4 <= Bq + alloc)%Z -> (D mod 4 = 0)%Z ->
      (Bq + alloc <= ATOP)%Z -> (Bq mod 16 = 0)%Z -> (0 < Bq)%Z ->
      (0 <= bB <= 1)%Z -> (Bq + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= Bq)%Z -> (6307840 <= Bq)%Z ->
      rng RNGx Bq alloc -> rng RNGx (shad Bq) (nshad alloc) ->
      evtF asegs RNGx (fun ms' => exists (a3v a5v s9v : word) (m' : mem),
          ms' = MS (mkR ra_ sp_ gp_ tp_ (Z_to_bv 64 (Z.shiftr D 3)) t1 t2 s0_ s1_ (Z_to_bv 64 D) a1 a2 a3v a4 a5v (Z_to_bv 64 (D + 2)) a7
                       s2_ s3_ s4_ (Z_to_bv 64 2147450880) s6_ s7_ s8_ s9v s10_ s11_ t3 t4 t5 t6) F_ (Z_to_bv 64 0x8c5d8) fc_ None m' (seg_rom asegs)
          /\ munch [(D, D + 4)]%Z mx m' /\ wmono asegs mx m' /\ mem_inv asegs m'
          /\ rw_cells asegs m' D [Cells.C2 (Z_to_bv 64 (u1 + 256 * u0)); Cells.C2 (Z_to_bv 64 (u3 + 256 * u2))]
          /\ unpoisoned m' Bq (Bq + alloc))
        (MS (mkR ra_ sp_ gp_ tp_ (Z_to_bv 64 (Z.shiftr D 3)) t1 t2 s0_ s1_ (Z_to_bv 64 D) a1 a2 a3 a4 a5 (Z_to_bv 64 (D + 2)) a7
                 s2_ s3_ s4_ (Z_to_bv 64 2147450880) s6_ s7_ s8_ s9_ s10_ s11_ t3 t4 t5 t6) F_ (Z_to_bv 64 0x8c574) fc_ None mx (seg_rom asegs)).
  Section Sz8.
  Variables RNGx ra_ sp_ gp_ tp_ t1 t2 s0_ s1_ a1 a2 a3 a4 a5 a7 s2_ s3_ s4_ s6_ s7_ s8_ s9_ s10_ s11_ t3 t4 t5 t6 F_ fc_ mx u0 u1 u2 u3 Bq alloc bB D : ltac2:(SecDiet.SzSec.tyM 'swap_hdrA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  #[using="Type"] Lemma swap_hdrA__core : ltac2:(SecDiet.SzSec.bodyP 'swap_hdrA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros B0 B1x B2x B3 HOPT MIx BUNP INB1 INB2 DM4 BTOP BM16 BPOS bBr bBhi bBlo bBimg BRNG BRSH.
    pose proof atop_range as AR.
    pose proof (munch_refl [(D, D + 4)]%Z mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    ckp_at BUNP D 2%Z.
  do 2 zstep.
  ck_cut 0x8c580%Z [15%Z].
  do 2 zstep.
  ck_cut 0x8c58c%Z [15%Z].
  rewrite (zx16_lit (u0 + 256 * u1)) by lia.
  do 3 zstep.
  match goal with |- context [Z_to_bv 64 (Z.lor ?a ?b)] =>
    replace (Z.lor a b) with (u1 + 256 * u0 + 65536 * u1)%Z
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia;
          replace ((u0 + 256 * u1) / 2 ^ 8)%Z with u1 by (Z.div_mod_to_equations; lia);
          rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.lor_high_low (u0 + 256 * u1) u1 8) by lia; lia) end.
  zstep.
  zstep.
  ckp_at BUNP (D + 2)%Z 2%Z.
  do 2 zstep.
  ck_cut 0x8c5ac%Z [15%Z].
  do 2 zstep.
  ck_cut 0x8c5b8%Z [15%Z].
  rewrite (zx16_lit (u2 + 256 * u3)) by lia.
  do 3 zstep.
  match goal with |- context [Z_to_bv 64 (Z.lor ?a ?b)] =>
    replace (Z.lor a b) with (u3 + 256 * u2 + 65536 * u3)%Z
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia;
          replace ((u2 + 256 * u3) / 2 ^ 8)%Z with u3 by (Z.div_mod_to_equations; lia);
          rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.lor_high_low (u2 + 256 * u3) u3 8) by lia; lia) end.
  zstep.
  zstep.                                     (* [comment removed for export] *)
  apply evtF_done.
  lazymatch goal with |- exists _ _ _ _, MS _ _ _ _ _ ?mm _ = _ /\ _ => do 3 eexists; exists mm end.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MIx|]. split; [| exact BUNP].
  exact (rw_cells_recell _ _ _ [Cells.C2 (Z_to_bv 64 (u1 + 256 * u0)); Cells.C2 (Z_to_bv 64 (u3 + 256 * u2))] HOPT ltac:(cbn; auto)
           ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit by lia;
                 rewrite (le2_of_val _ u1 u0 u1) by (try lia; rewrite unsigned_lit by lia; lia);
                 rewrite (le2_of_val _ u3 u2 u3) by (try lia; rewrite unsigned_lit by lia; lia); reflexivity)).
  Qed.
  End Sz8.
Section AIX.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (L : alayout) (RNG : footprint) (st : PS) (C1 C2 FB : list cblk) (FL : list fblock) (P B I CUR EB lo idb_off : Z).
  Variables (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte).
  Hypothesis G : GIOA L RNG st (C1 ++ IBLK i I s ++ C2) FB FL m.
  Hypothesis LO : (ATOP + 4096 <= lo)%Z.
  Hypothesis BU : (lo + 16528 <= bv_unsigned sp)%Z.
  Hypothesis SPT : (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RTLS : rng_atls RNG.
  Hypothesis TPE : tp = Z_to_bv 64 ATP.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.

  #[local] Abbreviation POSTQ := (add_interface_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st)).
  #[local] Abbreviation AGP := (ai_AGP FL sp C1 C2 P B CUR EB p m).
  #[local] Abbreviation FRAME := (ai_FRAME ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

  (* [comment removed for export] *)
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis HinP : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2).
  Hypothesis HinB : In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2).
  Hypothesis P14 : (0 < P /\ P + 680 <= ATOP)%Z.
  Hypothesis B14 : (0 < B /\ B + pc_bufalloc p <= ATOP)%Z.
  Hypothesis LENB : (Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32)%Z.
  Hypothesis CURS : (bv_unsigned sp <= CUR /\ CUR + 24 <= al_top L)%Z.
  (* [comment removed for export] *)
  Hypothesis EBL : clocA FL (C1 ++ C2) EB 256.
  Hypothesis EBP : (EB + 256 <= P + 648 \/ P + 680 <= EB)%Z.
  Hypothesis EBB : (EB + 256 <= B \/ B + pc_bufalloc p <= EB)%Z.

  #[local] Abbreviation AIREST_F := (ai_REST_F GIOA L).
  Hypothesis EBO : cobjA RNG m FL (C1 ++ C2) EB 256 \/ (P + 216 = EB)%Z.

  Hypothesis UTS : (0 < ng_user_tsresol s < 2^64)%Z.
  Hypothesis IFW : Forall if_wf (ng_ifaces s).
  Hypothesis P2 : (P mod 16 = 0)%Z.
  Hypothesis B2 : (B mod 16 = 0)%Z.
  Hypothesis IDB0 : (0 <= idb_off)%Z.
  Hypothesis IDB4 : (idb_off mod 4 = 0)%Z.
  Hypothesis COFF : (cur_off c = idb_off + 8)%Z.
  Hypothesis CREM : (0 <= cur_remaining c)%Z.
  Hypothesis CEND : (cur_off c + cur_remaining c <= Z.of_nat (length (pc_bufdata p)))%Z.
  Hypothesis CBT : (0 <= cur_block_type c < 2^32)%Z.
  Hypothesis CUR8 : (CUR mod 8 = 0)%Z.
  Hypothesis APB : (P + 680 <= B \/ B + pc_bufalloc p <= P)%Z.
  Hypothesis EBP2 : (EB + 256 <= P + 48 \/ P + 60 <= EB)%Z.
  Hypothesis HPV : rw_cells asegs m (P + 48) [C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))].

  #[local] Abbreviation ai_snap := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_snap idb_off p).
  #[local] Abbreviation ai_slot0 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot0 idb_off p).
  #[local] Abbreviation ai_result := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result idb_off p s c).

  (* [comment removed for export] *)
  Variables (RNG3 : footprint) (stG : PS) (sg : pcap_ng_sf) (q1 : hptr) (I' SA : Z) (js : list if_junk) (pad1 sj tail3 : list byte).
  Hypothesis FP3 : fp_le RNG RNG3.
  Hypothesis U1 : ng_user_tsresol sg = ng_user_tsresol s.
  Hypothesis U2 : ng_max_blocksize sg = ng_max_blocksize s.
  Hypothesis U5 : ng_ifaces sg = ng_ifaces s.
  Hypothesis IC1 : (ng_ifcount sg = Z.of_nat (length (ng_ifaces s)) + 1)%Z.
  Hypothesis IC2 : (ng_ifcount sg <= ng_ifaces_size sg)%Z.
  Hypothesis SZ : (1 <= ng_ifaces_size sg < 2^26)%Z.
  Hypothesis LJS : length js = length (ng_ifaces s).
  Hypothesis HSA : (SA = I' + 40 * (ng_ifcount sg - 1))%Z.
  Hypothesis SNR : (0 <= ai_snap < 2^32)%Z.
  Hypothesis OFG : ps_outfile stG = ps_outfile st.

  (* [comment removed for export] *)
  Variable hj0 : list byte.
  Definition ai_hd : list cell := [CB 8 hj0; C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 EB); C8 (Z_to_bv 64 65280); C8 (Z_to_bv 64 (Z.shiftr (P + 672) 3 + 2147450880))].

  (* [comment removed for export] *)
  Definition sgF : pcap_ng_sf := mkNg (ng_user_tsresol sg) (ng_max_blocksize sg) (ng_ifcount sg) (ng_ifaces_size sg) (ai_slot0 :: ng_ifaces sg).
  Definition pF (buf' : list Z) : pcapT := set_bufdata buf' (set_ng sgF (Some q1) (set_ng sg (Some q1) p)).
  #[using="Type"] Lemma ai_result_inl : forall buf' msg, ai_result sg (Some q1) (buf', inl msg) = (false, c, pF buf', msg).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition AIM (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte) : Prop :=
    (0 < io_tsresol io < 2^64)%Z /\
    mem_inv asegs m3 /\ stk asegs m3 lo (bv_unsigned sp + -144) /\ AGP m3 /\
    rw_cells asegs m3 (bv_unsigned sp + -144) ai_hd /\ FRAME m3 /\
    rw_cells asegs m3 (P + 648) (ng_cells sg I' pad1) /\
    rw_cells asegs m3 I' (ifs_cells (rev (ng_ifaces s)) js) /\
    rw_cells asegs m3 SA [C4 (Z_to_bv 64 ai_snap); CB 36 sj] /\
    rw_cells asegs m3 (SA + 40) [CB (Z.to_nat (40 * (ng_ifaces_size sg - ng_ifcount sg))) tail3] /\
    GIOA L RNG3 stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB FL m3 /\
    rw_cells asegs m3 B [CB (Z.to_nat (pc_bufalloc p)) bs3] /\ firstn (length buf') bs3 = map b8 buf' /\ length buf' = length (pc_bufdata p) /\
    Forall (fun z => 0 <= z < 256)%Z buf' /\
    rw_cells asegs m3 CUR (cursor_cells B c' cpad3) /\
    (0 <= cur_remaining c')%Z /\ (cur_off c <= cur_off c')%Z /\ (cur_off c' + cur_remaining c' <= cur_off c + cur_remaining c)%Z /\
    cur_block_type c' = cur_block_type c /\
    rw_cells asegs m3 EB [CB 256 ej] /\ (cur_off c' mod 4 = 0)%Z.

  (* [comment removed for export] *)
  Definition LREGS (t0' x8 a0' a3' a4' a5' x25 x26 : word) (io : idbopts) (c' : cursor) :=
    mkR (Z_to_bv 64 (Z.shiftr CUR 3 + 2147450880)) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' (Z_to_bv 64 (io_tsresol io)) (Z_to_bv 64 (Z.b2z (io_is_binary io)))
        x8 (Z_to_bv 64 (P + 648)) a0' (Z_to_bv 64 (CUR + 8)) (Z_to_bv 64 CUR) a3' a4' a5' (Z_to_bv 64 (cur_remaining c')) (Z_to_bv 64 (P + 56))
        (Z_to_bv 64 (P + 660)) (Z_to_bv 64 5) (Z_to_bv 64 (Z.b2z (io_saw_tsoffset io))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 660) 3 + 2147450880))
        (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 10) x25 x26 (Z_to_bv 64 (Z.b2z (io_saw_tsresol io)))
        (Z_to_bv 64 (Z.shiftr (CUR + 8) 3 + 2147450880)) (Z_to_bv 64 (io_tsoffset io)) (Z_to_bv 64 4) (Z_to_bv 64 (P + 672)).

  Definition LOOPK (fuel : nat) : Prop :=
    forall (t0' x8 a0' a3' a4' a5' x25 x26 : word) (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte),
      AIM io c' buf' m3 bs3 cpad3 -> (cur_remaining c' / 4 < Z.of_nat fuel)%Z ->
      evtF asegs RNG3 (POSTQ (ai_result sg (Some q1) (process_idb_options_loop fuel (pc_swapped p) io c' buf')) stG RNG3)
        (MS (LREGS t0' x8 a0' a3' a4' a5' x25 x26 io c') F (Z_to_bv 64 0x8c51c) fc None m3 (seg_rom asegs)).
  Definition ITERK (fuel : nat) : Prop :=
    forall (t0' x8 a0' a3' a4' a5' x25 x26 : word) (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte),
      AIM io c' buf' m3 bs3 cpad3 -> (cur_remaining c' / 4 < Z.of_nat (S fuel))%Z -> (0 < cur_remaining c')%Z ->
      evtF asegs RNG3 (POSTQ (ai_result sg (Some q1) (process_idb_options_loop (S fuel) (pc_swapped p) io c' buf')) stG RNG3)
        (MS (LREGS t0' x8 a0' a3' a4' a5' x25 x26 io c') F (Z_to_bv 64 0x8c520) fc None m3 (seg_rom asegs)).

  #[using="Type"] Lemma ai_loop0 : LOOPK O.
  Proof. red. intros until cpad3. intros IV FUEL. destruct IV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR1 & _). exfalso. clear - FUEL CR1. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Definition ai_loop_step__stmt : Prop := forall fuel, ITERK fuel -> LOOPK (S fuel).
  Section Sz3.
  Variables fuel t0' x8 a0' a3' a4' a5' x25 x26 io c' buf' m3 bs3 cpad3 : ltac2:(SecDiet.SzSec.tyM 'ai_loop_step__stmt "vhvvvvvvvvvvvvvv" @fuel).
  Lemma ai_loop_step__body : ltac2:(SecDiet.SzSec.bodyP 'ai_loop_step__stmt "vhvvvvvvvvvvvvvv").
  Proof using rc tlsI H hptr FO GIOA fflagA GL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej LO BU SPT RSTK GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB UTS IFW IDB0 COFF CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG hj0 fuel t0' x8 a0' a3' a4' a5' x25 x26 io c' buf' m3 bs3 cpad3.
    intros IT.
 intros IV FUEL.
    pose proof IV as IV'. destruct IV' as (TSR & MI3 & ST3 & AG3 & HD3 & FR3 & NG3 & AR1 & SL3 & AR2 & G3 & BUF3 & PFX3 & LB3 & GR3 & CC3 & CR1 & CR2 & CR3 & CR4 & HEB3 & OFF4).
    hide HD3. hide FR3. hide NG3. hide AR1. hide SL3. hide AR2. hide BUF3. hide CC3. hide HEB3.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    unfold LREGS. zstep.
    destruct (Z.eq_dec (cur_remaining c') 0) as [R0|R0].
    - rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ R0). cbv iota. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_unfold. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_iter. rewrite (proj2 (Z.eqb_eq _ _) R0).
      unhide HD3. unhide FR3. unhide NG3. unhide AR1. unhide SL3. unhide AR2. unhide BUF3. unhide CC3. unhide HEB3.
      eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiBA.ai_tail with (SA := SA) (js := js); eassumption || (try exact IC1; try exact HSA; try reflexivity; try lia).
    - rewrite (eqb_lits_false (cur_remaining c') 0) by lia. cbv iota.
      unhide HD3. unhide FR3. unhide NG3. unhide AR1. unhide SL3. unhide AR2. unhide BUF3. unhide CC3. unhide HEB3.
      apply (IT _ _ _ _ _ _ _ _ io c' buf' m3 bs3 cpad3 IV FUEL ltac:(lia)).
  Qed.
  End Sz3.
  #[using="rc tlsI FO fflagA GL LO BU SPT RSTK GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB UTS IFW IDB0 COFF CEND APB EBP2 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG"] Lemma ai_loop_step : ltac:(let t := eval cbv delta [ai_loop_step__stmt] in ai_loop_step__stmt in exact t).
  Proof. intros fuel IT t0' x8 a0' a3' a4' a5' x25 x26 io c' buf' m3 bs3 cpad3. ltac2:(SecDiet.SzSec.closeP 'ai_loop_step__body "vhvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition loop_restf__stmt : Prop := forall (m3 : mem) (buf' : list Z) (bs3 : list byte) (ccs : list cell),
    GIOA L RNG3 stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB FL m3 ->
    rw_cells asegs m3 (P + 648) (ng_cells sg I' pad1) ->
    rw_cells asegs m3 I' (ifs_cells (rev (ng_ifaces s)) js) ->
    rw_cells asegs m3 SA [C4 (Z_to_bv 64 ai_snap); CB 36 sj] ->
    rw_cells asegs m3 (SA + 40) [CB (Z.to_nat (40 * (ng_ifaces_size sg - ng_ifcount sg))) tail3] ->
    rw_cells asegs m3 B [CB (Z.to_nat (pc_bufalloc p)) bs3] -> firstn (length buf') bs3 = map b8 buf' -> length buf' = length (pc_bufdata p) ->
    Forall (fun z => 0 <= z < 256)%Z buf' ->
    rw_cells asegs m3 CUR ccs -> cells_size ccs = 24%nat ->
    AIREST_F RNG3 FL C1 C2 FB P B CUR p s (ps_outfile st) m3 stG c (pF buf').
  Section Sz4.
  Variables m3 buf' bs3 ccs : ltac2:(SecDiet.SzSec.tyM 'loop_restf__stmt "vvvv" @m3).
  Lemma loop_restf__body : ltac2:(SecDiet.SzSec.bodyP 'loop_restf__stmt "vvvv").
  Proof using rc H hptr GIOA sp L st C1 C2 FB FL P B CUR EB lo idb_off p s c LO BU P14 B14 LENB CURS EBP EBB IDB0 COFF CREM CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 U1 U2 IC1 IC2 SZ LJS HSA OFG m3 buf' bs3 ccs.
    intros G3 NG3 AR1 SL3 AR2 BUF3 PFX3 LB3 GR3 CC3 Hccs.
    exists sgF, (Some q1), I', pad1, bs3.
    split; [exact OFG|]. split; [reflexivity|]. split; [exact G3|]. split; [exact NG3|]. split; [cbn; exact U1|]. split; [cbn; exact U2|]. split; [cbn; lia|]. split; [cbn; lia|].
    split; [exact BUF3|]. split; [exact PFX3|]. split; [exact LB3|]. split; [exact GR3|]. split.
    - cbn [ng_ifaces_closable sgF ng_ifaces_size]. split; [| lia].
      pose proof (rw_cells_bound _ _ _ _ AR1) as BA1. rewrite ifs_cells_size in BA1 by (rewrite length_rev; lia). rewrite length_rev in BA1.
      pose proof (rw_cells_uncut _ _ _ _ _ AR1 SL3 ltac:(rewrite ifs_cells_size by (rewrite length_rev; lia); rewrite length_rev; lia)) as J1.
      pose proof (rw_cells_uncut _ _ _ _ _ J1 AR2 ltac:(rewrite cells_size_app, ifs_cells_size by (rewrite length_rev; lia); rewrite length_rev; cbn [cells_size csize]; lia)) as J2.
      destruct (rw_cells_forget _ _ _ _ J2) as [junk HJ]. exists junk.
      rewrite !cells_size_app, ifs_cells_size in HJ by (rewrite length_rev; lia). rewrite length_rev in HJ. cbn [cells_size csize Nat.add] in HJ.
      lazymatch type of HJ with rw_cells _ _ _ [CB ?n _] => replace (Z.to_nat (40 * ng_ifaces_size sg)) with n by lia end. exact HJ.
    - exists ccs. split; [exact CC3| exact Hccs].
  Qed.
  End Sz4.
  #[using="rc sp EB lo LO BU P14 B14 LENB CURS EBP EBB IDB0 COFF CREM CEND APB EBP2 U1 U2 IC1 IC2 SZ LJS HSA OFG"] Lemma loop_restf : ltac:(let t := eval cbv delta [loop_restf__stmt] in loop_restf__stmt in exact t).
  Proof. intros m3 buf' bs3 ccs. ltac2:(SecDiet.SzSec.closeP 'loop_restf__body "vvvv"). Qed.

  (* [comment removed for export] *)
  Definition loop_facts__stmt : Prop := forall (io : idbopts) (c' : cursor) (pre post : list Z) (u0 u1 u2 u3 : Z) (bsr cpad3 : list byte) (m3 m5 : mem)
      (c0 c1 l0 l1 : Z) (D : Z) (ccs : list cell),
      AIM io c' (pre ++ u0 :: u1 :: u2 :: u3 :: post) m3 (map b8 pre ++ [b8 u0; b8 u1; b8 u2; b8 u3] ++ bsr) cpad3 ->
      (4 <= cur_remaining c')%Z -> Z.of_nat (length pre) = cur_off c' -> D = (B + cur_off c')%Z ->
      firstn (length post) bsr = map b8 post ->
      (0 <= c0 < 256)%Z -> (0 <= c1 < 256)%Z -> (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z ->
      mem_inv asegs m5 -> munch [(CUR, CUR + 16); (D, D + 4)]%Z m3 m5 -> wmono asegs m3 m5 ->
      rw_cells asegs m5 D [Cells.C2 (Z_to_bv 64 (c0 + 256 * c1)); Cells.C2 (Z_to_bv 64 (l0 + 256 * l1))] ->
      rw_cells asegs m5 CUR ccs -> cells_size ccs = 24%nat ->
      let buf5 := pre ++ c0 :: c1 :: l0 :: l1 :: post in let bs5 := map b8 pre ++ [b8 c0; b8 c1; b8 l0; b8 l1] ++ bsr in
      stk asegs m5 lo (bv_unsigned sp + -144) /\ AGP m5 /\
      rw_cells asegs m5 (bv_unsigned sp + -144) ai_hd /\ FRAME m5 /\
      rw_cells asegs m5 (P + 648) (ng_cells sg I' pad1) /\
      rw_cells asegs m5 I' (ifs_cells (rev (ng_ifaces s)) js) /\
      rw_cells asegs m5 SA [C4 (Z_to_bv 64 ai_snap); CB 36 sj] /\
      rw_cells asegs m5 (SA + 40) [CB (Z.to_nat (40 * (ng_ifaces_size sg - ng_ifcount sg))) tail3] /\
      GIOA L RNG3 stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB FL m5 /\
      rw_cells asegs m5 B [CB (Z.to_nat (pc_bufalloc p)) bs5] /\ firstn (length buf5) bs5 = map b8 buf5 /\ length buf5 = length (pc_bufdata p) /\
      Forall (fun z => 0 <= z < 256)%Z buf5 /\ Forall (fun z => 0 <= z < 256)%Z post /\
      rw_cells asegs m5 EB [CB 256 ej] /\
      rw_cells asegs m5 (D + 4) [CB (length bsr) bsr] /\
      AIREST_F RNG3 FL C1 C2 FB P B CUR p s (ps_outfile st) m5 stG c (pF buf5).

  #[local] Abbreviation pio_body := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_body.
  #[local] Abbreviation pio_value := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_value.
  #[local] Abbreviation le8val := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val.

  (* [comment removed for export] *)
  Definition ai_disp__stmt : Prop := forall fuel, LOOPK fuel ->
    forall (t0' x25 x26 : word) (io : idbopts) (c' : cursor) (sw : bool) (pre post : list Z) (c0 c1 l0 l1 : Z) (bsr cpad3 : list byte) (m5 : mem) (D : Z),
      let code := (c0 + 256 * c1)%Z in let olen := (l0 + 256 * l1)%Z in let padded := ((olen + 3) / 4 * 4)%Z in
      let buf5 := pre ++ c0 :: c1 :: l0 :: l1 :: post in let bs5 := map b8 pre ++ [b8 c0; b8 c1; b8 l0; b8 l1] ++ bsr in
      let c2 := mkCursor (cur_off c' + 4 + padded) (cur_remaining c' - 4 - padded) (cur_block_type c') in
      (forall io', (0 < io_tsresol io' < 2^64)%Z -> AIM io' c2 buf5 m5 bs5 cpad3) ->
      (0 < io_tsresol io < 2^64)%Z -> pc_swapped p = sw ->
      (cur_remaining c' / 4 < Z.of_nat (S fuel))%Z -> (4 <= cur_remaining c')%Z -> (padded <= cur_remaining c' - 4)%Z ->
      (8 <= cur_off c')%Z -> (cur_off c' mod 4 = 0)%Z -> (cur_off c' + cur_remaining c' <= Z.of_nat (length buf5))%Z ->
      D = (B + cur_off c')%Z -> Z.of_nat (length pre) = cur_off c' ->
      firstn (length post) bsr = map b8 post ->
      (0 <= c0 < 256)%Z -> (0 <= c1 < 256)%Z -> (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z ->
      Forall (fun z => 0 <= z < 256)%Z post ->
      rw_cells asegs m5 (D + 4) [CB (length bsr) bsr] ->
      evtF asegs RNG3 (POSTQ (ai_result sg (Some q1) (pio_body fuel sw io code olen (cur_off c' + 4) c2 buf5)) stG RNG3)
        (MS (mkR (Z_to_bv 64 (Z.shiftr CUR 3 + 2147450880)) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' (Z_to_bv 64 (io_tsresol io)) (Z_to_bv 64 (Z.b2z (io_is_binary io)))
                 (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 (P + 648)) (Z_to_bv 64 D) (Z_to_bv 64 (CUR + 8)) (Z_to_bv 64 CUR) (Z_to_bv 64 olen) (Z_to_bv 64 (D + 4)) (Z_to_bv 64 code)
                 (Z_to_bv 64 (cur_remaining c' - 4 - padded)) (Z_to_bv 64 (P + 56))
                 (Z_to_bv 64 (P + 660)) (Z_to_bv 64 5) (Z_to_bv 64 (Z.b2z (io_saw_tsoffset io))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 660) 3 + 2147450880))
                 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 10) x25 x26 (Z_to_bv 64 (Z.b2z (io_saw_tsresol io)))
                 (Z_to_bv 64 (Z.shiftr (CUR + 8) 3 + 2147450880)) (Z_to_bv 64 (io_tsoffset io)) (Z_to_bv 64 4) (Z_to_bv 64 (P + 672)))
            F (Z_to_bv 64 0x8c630) fc None m5 (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition ai_body__stmt : Prop := forall fuel, LOOPK fuel ->
    forall (a3' a5' x25 : word) (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte)
           (sw : bool) (pre post : list Z) (u0 u1 u2 u3 : Z) (bsr : list byte) (m4 : mem),
      AIM io c' buf' m3 bs3 cpad3 -> (cur_remaining c' / 4 < Z.of_nat (S fuel))%Z -> (4 <= cur_remaining c')%Z ->
      pc_swapped p = sw ->
      buf' = pre ++ u0 :: u1 :: u2 :: u3 :: post -> Z.of_nat (length pre) = cur_off c' ->
      bs3 = map b8 pre ++ [b8 u0; b8 u1; b8 u2; b8 u3] ++ bsr -> firstn (length post) bsr = map b8 post ->
      let c0 := (if sw then u1 else u0) in let c1 := (if sw then u0 else u1) in
      let l0 := (if sw then u3 else u2) in let l1 := (if sw then u2 else u3) in
      let code := (c0 + 256 * c1)%Z in let olen := (l0 + 256 * l1)%Z in
      mem_inv asegs m4 ->
      munch [(CUR, CUR + 16); (B + cur_off c', B + cur_off c' + 4)]%Z m3 m4 -> wmono asegs m3 m4 ->
      rw_cells asegs m4 CUR [C8 (Z_to_bv 64 (B + cur_off c' + 4)); C8 (Z_to_bv 64 (cur_remaining c' - 4)); C4 (Z_to_bv 64 (cur_block_type c')); CB 4 cpad3] ->
      rw_cells asegs m4 (B + cur_off c') [Cells.C2 (Z_to_bv 64 code); Cells.C2 (Z_to_bv 64 olen)] ->
      evtF asegs RNG3 (POSTQ (ai_result sg (Some q1)
                   (pio_value fuel sw io code olen (mkCursor (cur_off c' + 4) (cur_remaining c' - 4) (cur_block_type c')) (pre ++ c0 :: c1 :: l0 :: l1 :: post))) stG RNG3)
        (MS (mkR (Z_to_bv 64 (Z.shiftr CUR 3 + 2147450880)) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp (Z_to_bv 64 (Z.shiftr (B + cur_off c') 3)) (Z_to_bv 64 (io_tsresol io)) (Z_to_bv 64 (Z.b2z (io_is_binary io)))
                 (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 (P + 648)) (Z_to_bv 64 (B + cur_off c')) (Z_to_bv 64 (CUR + 8)) (Z_to_bv 64 CUR)
                 a3' (Z_to_bv 64 (B + cur_off c' + 4)) a5'
                 (Z_to_bv 64 (B + cur_off c' + 2)) (Z_to_bv 64 (P + 56))
                 (Z_to_bv 64 (P + 660)) (Z_to_bv 64 5) (Z_to_bv 64 (Z.b2z (io_saw_tsoffset io))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 660) 3 + 2147450880))
                 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 10) x25 (Z_to_bv 64 (cur_remaining c' - 4)) (Z_to_bv 64 (Z.b2z (io_saw_tsresol io)))
                 (Z_to_bv 64 (Z.shiftr (CUR + 8) 3 + 2147450880)) (Z_to_bv 64 (io_tsoffset io)) (Z_to_bv 64 4) (Z_to_bv 64 (P + 672)))
            F (Z_to_bv 64 0x8c5d8) fc None m4 (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition ai_iter__stmt : Prop := forall fuel, LOOPK fuel -> ITERK fuel.

  Section Sz8.
  Variables RNGx ra_ sp_ gp_ tp_ t1 t2 s0_ s1_ a1 a2 a3 a4 a5 a7 s2_ s3_ s4_ s6_ s7_ s8_ s9_ s10_ s11_ t3 t4 t5 t6 F_ fc_ mx u0 u1 u2 u3 Bq alloc bB D : ltac2:(SecDiet.SzSec.tyM 'swap_hdrA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  Lemma swap_hdrA__body : ltac2:(SecDiet.SzSec.bodyP 'swap_hdrA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using rc hptr sp L P B CUR EB lo idb_off p s c LO BU ALN P14 B14 LENB CURS EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 js LJS RNGx ra_ sp_ gp_ tp_ t1 t2 s0_ s1_ a1 a2 a3 a4 a5 a7 s2_ s3_ s4_ s6_ s7_ s8_ s9_ s10_ s11_ t3 t4 t5 t6 F_ fc_ mx u0 u1 u2 u3 Bq alloc bB D. exact (swap_hdrA__core RNGx ra_ sp_ gp_ tp_ t1 t2 s0_ s1_ a1 a2 a3 a4 a5 a7 s2_ s3_ s4_ s6_ s7_ s8_ s9_ s10_ s11_ t3 t4 t5 t6 F_ fc_ mx u0 u1 u2 u3 Bq alloc bB D). Qed.
  End Sz8.
  #[using="hptr sp L P B CUR EB lo idb_off p s c LO BU ALN P14 B14 LENB CURS EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 js LJS"] Lemma swap_hdrA : ltac:(let t := eval cbv delta [swap_hdrA__stmt] in swap_hdrA__stmt in exact t).
  Proof. intros RNGx ra_ sp_ gp_ tp_ t1 t2 s0_ s1_ a1 a2 a3 a4 a5 a7 s2_ s3_ s4_ s6_ s7_ s8_ s9_ s10_ s11_ t3 t4 t5 t6 F_ fc_ mx u0 u1 u2 u3 Bq alloc bB D. ltac2:(SecDiet.SzSec.closeP 'swap_hdrA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  End AIX.
  End CANSEC1.
End F_aiEA.

(* [comment removed for export] *)
Module F_aiEA_facts.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require Import UbGuardB AiAuxB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiBA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.


Ltac apA lem := eapply lem; try eassumption.
Ltac transport H m' AG tac :=
  lazymatch type of H with rw_cells ?sg _ ?A ?cs =>
    let X := fresh in
    assert (X : rw_cells sg m' A cs) by (eapply agrees_rw_cells; [exact AG | exact H | tac]);
    clear H; rename X into H end.

Ltac msg_ok := vm_compute; repeat first [apply Forall_nil | apply Forall_cons; [split; reflexivity|]].
(* [comment removed for export] *)
Ltac fmt_at_tac MI ADDR str :=
  split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs _ ADDR (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string str) ++ [Z_to_bv 8 0])
                   MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
  split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right]).

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AccFast.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= plia.
Local Ltac flia ::= first [ sassumption | plia | assumption ].
Local Ltac acc_hint ::= acc_hint_cheap.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section AIX.
  Context {H : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.CANSEC1.AIX.u0}} {hptr : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.CANSEC1.AIX.u1}} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (L : alayout) (RNG : footprint) (st : PS) (C1 C2 FB : list cblk) (FL : list fblock) (P B I CUR EB lo idb_off : Z).
  Variables (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte).
  Hypothesis G : GIOA L RNG st (C1 ++ IBLK i I s ++ C2) FB FL m.
  Hypothesis LO : (ATOP + 4096 <= lo)%Z.
  Hypothesis BU : (lo + 16528 <= bv_unsigned sp)%Z.
  Hypothesis SPT : (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RTLS : rng_atls RNG.
  Hypothesis TPE : tp = Z_to_bv 64 ATP.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.

  #[local] Abbreviation POSTQ := (add_interface_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st)).
  #[local] Abbreviation AGP := (ai_AGP FL sp C1 C2 P B CUR EB p m).
  #[local] Abbreviation FRAME := (ai_FRAME ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

  (* [comment removed for export] *)
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis HinP : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2).
  Hypothesis HinB : In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2).
  Hypothesis P14 : (0 < P /\ P + 680 <= ATOP)%Z.
  Hypothesis B14 : (0 < B /\ B + pc_bufalloc p <= ATOP)%Z.
  Hypothesis LENB : (Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32)%Z.
  Hypothesis CURS : (bv_unsigned sp <= CUR /\ CUR + 24 <= al_top L)%Z.
  (* [comment removed for export] *)
  Hypothesis EBL : clocA FL (C1 ++ C2) EB 256.
  Hypothesis EBP : (EB + 256 <= P + 648 \/ P + 680 <= EB)%Z.
  Hypothesis EBB : (EB + 256 <= B \/ B + pc_bufalloc p <= EB)%Z.

  #[local] Abbreviation AIREST_F := (ai_REST_F GIOA L).
  Hypothesis EBO : cobjA RNG m FL (C1 ++ C2) EB 256 \/ (P + 216 = EB)%Z.

  Hypothesis UTS : (0 < ng_user_tsresol s < 2^64)%Z.
  Hypothesis IFW : Forall if_wf (ng_ifaces s).
  Hypothesis P2 : (P mod 16 = 0)%Z.
  Hypothesis B2 : (B mod 16 = 0)%Z.
  Hypothesis IDB0 : (0 <= idb_off)%Z.
  Hypothesis IDB4 : (idb_off mod 4 = 0)%Z.
  Hypothesis COFF : (cur_off c = idb_off + 8)%Z.
  Hypothesis CREM : (0 <= cur_remaining c)%Z.
  Hypothesis CEND : (cur_off c + cur_remaining c <= Z.of_nat (length (pc_bufdata p)))%Z.
  Hypothesis CBT : (0 <= cur_block_type c < 2^32)%Z.
  Hypothesis CUR8 : (CUR mod 8 = 0)%Z.
  Hypothesis APB : (P + 680 <= B \/ B + pc_bufalloc p <= P)%Z.
  Hypothesis EBP2 : (EB + 256 <= P + 48 \/ P + 60 <= EB)%Z.
  Hypothesis HPV : rw_cells asegs m (P + 48) [C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))].

  #[local] Abbreviation ai_snap := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_snap idb_off p).
  #[local] Abbreviation ai_slot0 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot0 idb_off p).
  #[local] Abbreviation ai_result := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result idb_off p s c).

  (* [comment removed for export] *)
  Variables (RNG3 : footprint) (stG : PS) (sg : pcap_ng_sf) (q1 : hptr) (I' SA : Z) (js : list if_junk) (pad1 sj tail3 : list byte).
  Hypothesis FP3 : fp_le RNG RNG3.
  Hypothesis U1 : ng_user_tsresol sg = ng_user_tsresol s.
  Hypothesis U2 : ng_max_blocksize sg = ng_max_blocksize s.
  Hypothesis U5 : ng_ifaces sg = ng_ifaces s.
  Hypothesis IC1 : (ng_ifcount sg = Z.of_nat (length (ng_ifaces s)) + 1)%Z.
  Hypothesis IC2 : (ng_ifcount sg <= ng_ifaces_size sg)%Z.
  Hypothesis SZ : (1 <= ng_ifaces_size sg < 2^26)%Z.
  Hypothesis LJS : length js = length (ng_ifaces s).
  Hypothesis HSA : (SA = I' + 40 * (ng_ifcount sg - 1))%Z.
  Hypothesis SNR : (0 <= ai_snap < 2^32)%Z.
  Hypothesis OFG : ps_outfile stG = ps_outfile st.

  (* [comment removed for export] *)
  Variable hj0 : list byte.
  (* [comment removed for export] *)
  #[local] Abbreviation ai_hd := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_hd P EB hj0).
  #[local] Abbreviation sgF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.sgF hptr idb_off p sg).
  #[local] Abbreviation pF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.pF hptr idb_off p sg q1).
  #[local] Abbreviation ai_result_inl := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_result_inl hptr idb_off p s c sg q1).
  #[local] Abbreviation AIM := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.AIM H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation LREGS := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.LREGS sp gp tp P CUR).
  #[local] Abbreviation LOOPK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.LOOPK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ITERK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ITERK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_loop0 := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_loop0 H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_loop_step__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_loop_step__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_loop_step := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_loop_step rc tlsI H hptr FO GIOA fflagA GL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej LO BU SPT RSTK GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB UTS IFW IDB0 COFF CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG hj0).
  #[local] Abbreviation loop_restf__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.loop_restf__stmt H hptr GIOA L st C1 C2 FB FL P B CUR idb_off p s c RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation loop_restf := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.loop_restf rc H hptr GIOA sp L st C1 C2 FB FL P B CUR EB lo idb_off p s c LO BU P14 B14 LENB CURS EBP EBB IDB0 COFF CREM CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 U1 U2 IC1 IC2 SZ LJS HSA OFG).
  #[local] Abbreviation loop_facts__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.loop_facts__stmt H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L st C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_disp__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_disp__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_body__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_body__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_iter__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_iter__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation swap_hdrA := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.swap_hdrA rc hptr sp L P B CUR EB lo idb_off p s c LO BU ALN P14 B14 LENB CURS EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 js LJS).

  Section Sz5.
  Variables io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m5 c0 c1 l0 l1 D ccs : ltac2:(SecDiet.SzSec.tyM 'loop_facts__stmt "vvvvvvvvvvvvvvvvvv" @io).
  Lemma loop_facts__body : ltac2:(SecDiet.SzSec.bodyP 'loop_facts__stmt "vvvvvvvvvvvvvvvvvv").
  Proof using rc tlsI H hptr FO GIOA fflagA GL ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L st C1 C2 FB FL P B CUR EB lo idb_off p s c ej LO BU GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 U1 U2 IC1 IC2 SZ LJS HSA OFG hj0 io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m5 c0 c1 l0 l1 D ccs.
 intros IV GE4 Lpre HDd PFXr HC0 HC1 HL0 HL1 MI5 MU WM HOPT5 CC5 Hccs buf5 bs5.
    destruct IV as (TSR & MI3 & ST3 & AG3 & HD3 & FR3 & NG3 & AR1 & SL3 & AR2 & G3 & BUF3 & PFX3 & LB3 & GR3 & CC3 & CR1 & CR2 & CR3 & CR4 & HEB3 & OFF4).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as AR.
    assert (LBS : (length pre + (4 + length bsr))%nat = Z.to_nat (pc_bufalloc p)).
    { destruct BUF3 as [[WF _] _]. cbn [cells_wf cell_wf] in WF. rewrite !length_app, !length_map in WF. cbn [length] in WF. lia. }
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiBA.ai_head FO GIOA fflagA GL sp L C1 C2 FB FL P B EB lo p LO BU GPL HinP HinB EBL _ _ _ _ _ _ G3 ltac:(lia)) as ((Q1 & Q4 & Q2) & _ & _ & _ & _ & API & APIB & APIE).
    assert (LEN4 : (cur_off c' + cur_remaining c' <= Z.of_nat (length (pre ++ u0 :: u1 :: u2 :: u3 :: post)))%Z) by lia.
    rewrite length_app in LEN4. cbn [length] in LEN4.
    apply Forall_app in GR3 as [GRpre GB].
    pose proof (Forall_inv GB) as B0. pose proof (Forall_inv (Forall_inv_tail GB)) as B1. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail GB))) as B2x.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail GB)))) as B3. pose proof (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail GB)))) as GRpost.
    cbv beta in B0, B1, B2x, B3. clear GB.
    pose proof (rw_cells_bound _ _ _ _ AR1) as BA1. rewrite ifs_cells_size in BA1 by (rewrite length_rev; lia). rewrite length_rev in BA1.
    assert (AGS35 : agrees_on (fun a => outside [(CUR, CUR + 16); (D, D + 4)]%Z a) m3 m5) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    unfold ai_FRAME in FR3. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_hd in *.
    assert (EBL3 : clocA FL ((q1, I', (40 * ng_ifaces_size sg)%Z) :: C1 ++ C2) EB 256) by (eapply clocA_incl; [exact EBL | apply incl_tl, incl_refl | apply incl_refl]).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G3 EBL3) as (EBLO & EBHI).
    transport HD3 m5 AGS35 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    transport FR3 m5 AGS35 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    transport NG3 m5 AGS35 ltac:(intros a Ha; unfold ng_cells in Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    transport AR1 m5 AGS35 ltac:(intros a Ha; rewrite ifs_cells_size in Ha by (rewrite length_rev; clear - LJS; lia); rewrite length_rev in Ha; cbn [outside fst snd]; clear - Ha IC1 IC2 Q1 Q4 LO BU CURS HDd APIB Lpre LBS; lia).
    transport SL3 m5 AGS35 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; clear - Ha HSA IC1 IC2 Q4 LO BU CURS HDd APIB Lpre LBS; lia).
    transport AR2 m5 AGS35 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; clear - Ha HSA IC1 IC2 Q4 LO BU CURS HDd APIB Lpre LBS; lia).
    transport HEB3 m5 AGS35 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    assert (G5 : GIOA L RNG3 stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB FL m5).
    { eapply (gl_client_frame _ _ _ GL); [exact G3 | exact MU | exact WM |].
      apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [| apply Forall_nil].
      right; left. unfold iv_in_block. apply Exists_cons_tl. apply Exists_exists. exists (pc_buffer p, B, pc_bufalloc p). split; [exact HinB|]. cbn [cb_addr cb_size fst snd]. lia. }
    assert (ST5 : stk asegs m5 lo (bv_unsigned sp + -144)) by (eapply agrees_stk; [exact AGS35 | exact ST3 | intros a Ha; cbn [outside fst snd]; lia]).
    assert (AG5 : AGP m5).
    { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS35|]. intros a (_ & _ & Hc & _ & Hb); cbn [outside fst snd]. split; [lia|]. split; [clear - Hb HDd Lpre LBS; lia| exact Logic.I]. }
    (* [comment removed for export] *)
    pose proof (rw_cells_recell _ _ _ [CB (length pre) (map b8 pre); CB 4 [b8 u0; b8 u1; b8 u2; b8 u3]; CB (length bsr) bsr] BUF3
                  ltac:(cbn; rewrite length_map; repeat split; reflexivity) ltac:(cbn [cells_bytes cbytes app]; rewrite !app_nil_r; reflexivity)) as BX.
    destruct (rw_cells_cut _ _ _ 1 BX) as [HB1 BX2]. destruct (rw_cells_cut _ _ _ 1 BX2) as [_ HB2]. clear BX BX2. cbn [firstn skipn cells_size csize Nat.add] in HB1, HB2.
    lazymatch type of HB2 with rw_cells _ _ ?A _ => replace A with (D + 4)%Z in HB2 by lia end.
    transport HB1 m5 AGS35 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    transport HB2 m5 AGS35 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    pose proof (rw_cells_uncut _ _ _ _ _ HB1 HOPT5 ltac:(cbn [cells_size csize Nat.add]; lia)) as J1.
    pose proof (rw_cells_uncut _ _ _ _ _ J1 HB2 ltac:(cbn [cells_size csize Nat.add app]; lia)) as J2. clear J1.
    assert (BUF5 : rw_cells asegs m5 B [CB (Z.to_nat (pc_bufalloc p)) bs5]).
    { eapply rw_cells_recell; [exact J2 | cbn; subst bs5; rewrite !length_app, !length_map; cbn [length]; lia |].
      subst bs5. cbn [cells_bytes cbytes app]. rewrite !le2_lit by lia. rewrite !app_nil_r. cbn [app]. reflexivity. }
    clear J2.
    assert (PFX5 : firstn (length buf5) bs5 = map b8 buf5) by (subst buf5 bs5; exact (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pfx_comp pre [c0; c1; l0; l1] post bsr PFXr)).
    assert (LB5 : length buf5 = length (pc_bufdata p)) by (rewrite <- LB3; subst buf5; rewrite !length_app; reflexivity).
    assert (GR5 : Forall (fun z => 0 <= z < 256)%Z buf5) by (subst buf5; apply Forall_app; split; [exact GRpre|]; repeat (constructor; [lia|]); exact GRpost).
    split; [exact ST5|]. split; [exact AG5|]. split; [exact HD3|]. split; [exact FR3|]. split; [exact NG3|]. split; [exact AR1|]. split; [exact SL3|]. split; [exact AR2|].
    split; [exact G5|]. split; [exact BUF5|]. split; [exact PFX5|]. split; [exact LB5|]. split; [exact GR5|]. split; [exact GRpost|]. split; [exact HEB3|]. split; [exact HB2|].
    eapply loop_restf; [exact G5 | exact NG3 | exact AR1 | exact SL3 | exact AR2 | exact BUF5 | exact PFX5 | exact LB5 | exact GR5 | exact CC5 | exact Hccs].
  Qed.
  End Sz5.
  #[using="rc tlsI FO fflagA GL LO BU GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 U1 U2 IC1 IC2 SZ LJS HSA OFG"] Lemma loop_facts : ltac:(let t := eval hnf in loop_facts__stmt in exact t).
  Proof. intros io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m5 c0 c1 l0 l1 D ccs. ltac2:(SecDiet.SzSec.closeP 'loop_facts__body "vvvvvvvvvvvvvvvvvv"). Qed.
  End AIX.
  End CANSEC1.
End F_aiEA_facts.

(* [comment removed for export] *)
Module F_aiEA_iter.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require Import UbGuardB AiAuxB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiBA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.


Ltac apA lem := eapply lem; try eassumption.
Ltac transport H m' AG tac :=
  lazymatch type of H with rw_cells ?sg _ ?A ?cs =>
    let X := fresh in
    assert (X : rw_cells sg m' A cs) by (eapply agrees_rw_cells; [exact AG | exact H | tac]);
    clear H; rename X into H end.

Ltac msg_ok := vm_compute; repeat first [apply Forall_nil | apply Forall_cons; [split; reflexivity|]].
(* [comment removed for export] *)
Ltac fmt_at_tac MI ADDR str :=
  split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs _ ADDR (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string str) ++ [Z_to_bv 8 0])
                   MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
  split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right]).

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AccFast.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= plia.
Local Ltac flia ::= first [ sassumption | plia | assumption ].
Local Ltac acc_hint ::= acc_hint_cheap.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section AIX.
  Context {H : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.CANSEC1.AIX.u0}} {hptr : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.CANSEC1.AIX.u1}} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (L : alayout) (RNG : footprint) (st : PS) (C1 C2 FB : list cblk) (FL : list fblock) (P B I CUR EB lo idb_off : Z).
  Variables (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte).
  Hypothesis G : GIOA L RNG st (C1 ++ IBLK i I s ++ C2) FB FL m.
  Hypothesis LO : (ATOP + 4096 <= lo)%Z.
  Hypothesis BU : (lo + 16528 <= bv_unsigned sp)%Z.
  Hypothesis SPT : (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RTLS : rng_atls RNG.
  Hypothesis TPE : tp = Z_to_bv 64 ATP.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.

  #[local] Abbreviation POSTQ := (add_interface_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st)).
  #[local] Abbreviation AGP := (ai_AGP FL sp C1 C2 P B CUR EB p m).
  #[local] Abbreviation FRAME := (ai_FRAME ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

  (* [comment removed for export] *)
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis HinP : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2).
  Hypothesis HinB : In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2).
  Hypothesis P14 : (0 < P /\ P + 680 <= ATOP)%Z.
  Hypothesis B14 : (0 < B /\ B + pc_bufalloc p <= ATOP)%Z.
  Hypothesis LENB : (Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32)%Z.
  Hypothesis CURS : (bv_unsigned sp <= CUR /\ CUR + 24 <= al_top L)%Z.
  (* [comment removed for export] *)
  Hypothesis EBL : clocA FL (C1 ++ C2) EB 256.
  Hypothesis EBP : (EB + 256 <= P + 648 \/ P + 680 <= EB)%Z.
  Hypothesis EBB : (EB + 256 <= B \/ B + pc_bufalloc p <= EB)%Z.

  #[local] Abbreviation AIREST_F := (ai_REST_F GIOA L).
  Hypothesis EBO : cobjA RNG m FL (C1 ++ C2) EB 256 \/ (P + 216 = EB)%Z.

  Hypothesis UTS : (0 < ng_user_tsresol s < 2^64)%Z.
  Hypothesis IFW : Forall if_wf (ng_ifaces s).
  Hypothesis P2 : (P mod 16 = 0)%Z.
  Hypothesis B2 : (B mod 16 = 0)%Z.
  Hypothesis IDB0 : (0 <= idb_off)%Z.
  Hypothesis IDB4 : (idb_off mod 4 = 0)%Z.
  Hypothesis COFF : (cur_off c = idb_off + 8)%Z.
  Hypothesis CREM : (0 <= cur_remaining c)%Z.
  Hypothesis CEND : (cur_off c + cur_remaining c <= Z.of_nat (length (pc_bufdata p)))%Z.
  Hypothesis CBT : (0 <= cur_block_type c < 2^32)%Z.
  Hypothesis CUR8 : (CUR mod 8 = 0)%Z.
  Hypothesis APB : (P + 680 <= B \/ B + pc_bufalloc p <= P)%Z.
  Hypothesis EBP2 : (EB + 256 <= P + 48 \/ P + 60 <= EB)%Z.
  Hypothesis HPV : rw_cells asegs m (P + 48) [C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))].

  #[local] Abbreviation ai_snap := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_snap idb_off p).
  #[local] Abbreviation ai_slot0 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot0 idb_off p).
  #[local] Abbreviation ai_result := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result idb_off p s c).

  (* [comment removed for export] *)
  Variables (RNG3 : footprint) (stG : PS) (sg : pcap_ng_sf) (q1 : hptr) (I' SA : Z) (js : list if_junk) (pad1 sj tail3 : list byte).
  Hypothesis FP3 : fp_le RNG RNG3.
  Hypothesis U1 : ng_user_tsresol sg = ng_user_tsresol s.
  Hypothesis U2 : ng_max_blocksize sg = ng_max_blocksize s.
  Hypothesis U5 : ng_ifaces sg = ng_ifaces s.
  Hypothesis IC1 : (ng_ifcount sg = Z.of_nat (length (ng_ifaces s)) + 1)%Z.
  Hypothesis IC2 : (ng_ifcount sg <= ng_ifaces_size sg)%Z.
  Hypothesis SZ : (1 <= ng_ifaces_size sg < 2^26)%Z.
  Hypothesis LJS : length js = length (ng_ifaces s).
  Hypothesis HSA : (SA = I' + 40 * (ng_ifcount sg - 1))%Z.
  Hypothesis SNR : (0 <= ai_snap < 2^32)%Z.
  Hypothesis OFG : ps_outfile stG = ps_outfile st.

  (* [comment removed for export] *)
  Variable hj0 : list byte.
  (* [comment removed for export] *)
  #[local] Abbreviation ai_hd := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_hd P EB hj0).
  #[local] Abbreviation sgF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.sgF hptr idb_off p sg).
  #[local] Abbreviation pF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.pF hptr idb_off p sg q1).
  #[local] Abbreviation ai_result_inl := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_result_inl hptr idb_off p s c sg q1).
  #[local] Abbreviation AIM := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.AIM H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation LREGS := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.LREGS sp gp tp P CUR).
  #[local] Abbreviation LOOPK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.LOOPK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ITERK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ITERK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_loop0 := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_loop0 H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_loop_step__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_loop_step__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_loop_step := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_loop_step rc tlsI H hptr FO GIOA fflagA GL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej LO BU SPT RSTK GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB UTS IFW IDB0 COFF CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG hj0).
  #[local] Abbreviation loop_restf__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.loop_restf__stmt H hptr GIOA L st C1 C2 FB FL P B CUR idb_off p s c RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation loop_restf := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.loop_restf rc H hptr GIOA sp L st C1 C2 FB FL P B CUR EB lo idb_off p s c LO BU P14 B14 LENB CURS EBP EBB IDB0 COFF CREM CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 U1 U2 IC1 IC2 SZ LJS HSA OFG).
  #[local] Abbreviation loop_facts__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.loop_facts__stmt H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L st C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_disp__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_disp__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_body__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_body__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_iter__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_iter__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation swap_hdrA := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.swap_hdrA rc hptr sp L P B CUR EB lo idb_off p s c LO BU ALN P14 B14 LENB CURS EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 js LJS).

  #[local] Abbreviation pio_body := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_body.
  #[local] Abbreviation pio_value := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_value.
  #[local] Abbreviation le8val := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val.

  Section Sz9.
  Variables fuel t0' x8 a0' a3' a4' a5' x25 x26 io c' buf' m3 bs3 cpad3 : ltac2:(SecDiet.SzSec.tyM 'ai_iter__stmt "vhvvvvvvvvvvvvvv" @fuel).
  Lemma ai_iter__gen : ai_body__stmt -> ltac2:(SecDiet.SzSec.bodyP 'ai_iter__stmt "vhvvvvvvvvvvvvvv").
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 HPV RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG hj0 fuel t0' x8 a0' a3' a4' a5' x25 x26 io c' buf' m3 bs3 cpad3.
    intros ai_body LK.
 intros IV FUEL RPOS.
    pose proof IV as IV'. destruct IV' as (TSR & MI3 & ST3 & AG3 & HD3 & FR3 & NG3 & AR1 & SL3 & AR2 & G3 & BUF3 & PFX3 & LB3 & GR3 & CC3 & CR1 & CR2 & CR3 & CR4 & HEB3 & OFF4).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as AR.
    assert (HPV3 : rw_cells asegs m3 (P + 48) [C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))]).
    { eapply agrees_rw_cells; [exact AG3 | exact HPV |]. cbn [cells_size csize Nat.add]. intros a Ha.
      split; [right; left; apply in_block_In; exists (pc_self p, P, PCAP_NG_SF_TOTAL); split; [exact HinP| cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia]|].
      unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL. repeat split; lia. }
    assert (LBS : length bs3 = Z.to_nat (pc_bufalloc p)) by (destruct BUF3 as [[WF _] _]; cbn in WF; lia).
    unfold cursor_cells in CC3.
    rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_unfold. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_iter. rewrite (proj2 (Z.eqb_neq (cur_remaining c') 0)) by lia.
    unfold get_opthdr_from_block_data, get_from_block_data.
    (* [comment removed for export] *)
    assert (HinB3 : In (pc_buffer p, B, pc_bufalloc p) (((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) ++ FB)) by (apply in_or_app; left; right; exact HinB).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G3 HinB3) as ((BBAND & B3x & BTOP & _) & B1 & BUNP & BRNG & BRSH & BAR).
    cbn [cb_addr cb_size fst snd] in BBAND, B3x, BTOP, B1, BUNP, BRNG, BRSH.
    band_ind BBAND bB.
    assert (HinP3 : In (pc_self p, P, PCAP_NG_SF_TOTAL) (((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) ++ FB)) by (apply in_or_app; left; right; exact HinP).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G3 HinP3) as ((PBAND & P3x & PTOP & _) & P1 & PUNP & PRNG & PRSH & PAR).
    cbn [cb_addr cb_size fst snd] in PBAND, P3x, PTOP, P1, PUNP, PRNG, PRSH. unfold PCAP_NG_SF_TOTAL in PBAND, P3x, PTOP, P1, PUNP, PRNG, PRSH.
    band_ind PBAND bP.
    pose proof (rng_fp_le _ _ _ _ FP3 RSTK) as RSTK3.
    destruct (gia_stack_sobjA FO GIOA fflagA GL _ _ _ _ _ _ _ lo (bv_unsigned sp) CUR 24 G3 LO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RSTK3) as (_ & _ & CUNP & CRNG & CRSH).
    replace (CUR - CUR mod 8)%Z with CUR in CRSH by lia. replace (24 + CUR mod 8)%Z with 24%Z in CRSH by lia.
    assert (RSPW : rng RNG3 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK3| lia]).
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_hd in HD3. unfold ai_FRAME in FR3.
    hide HD3. hide FR3. hide NG3. hide AR1. hide SL3. hide AR2. hide BUF3. hide HEB3. hide HPV3.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU0. pose proof (wmono_refl asegs m3) as WM0.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.LREGS. zstep.
  destruct (Z.lt_ge_cases (cur_remaining c') 4) as [LT4|GE4].
  { (* [comment removed for export] *)
    replace (bv_ltu (Z_to_bv 64 (cur_remaining c')) (Z_to_bv 64 4)) with true by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [negb].     (* [comment removed for export] *)
    rewrite (proj2 (Z.ltb_lt (cur_remaining c') 4) LT4). rewrite ai_result_inl.
    zstep. ck0 CUNP; ck_go.
    zstep.
    rewrite (sx32_s32 (cur_block_type c')) by lia.
    do 3 zstep.
    unhide HD3. unhide FR3. unhide NG3. unhide AR1. unhide SL3. unhide AR2. unhide BUF3. unhide HEB3.
    assert (MSG : fmt_at m3 0x22520 "block of type %u in pcapng dump file is too short"%string) by (fmt_at_tac MI3 0x22520%Z "block of type %u in pcapng dump file is too short"%string).
    eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB.ai_snp_b with (m3 := m3) (args := [AInt (s32 (cur_block_type c'))]) (h0 := C8 (Z_to_bv 64 3)) (h2 := C8 (Z_to_bv 64 65280)); try eassumption;
      [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia
      | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil]
      | unfold Msg.block_too_short, PCAP_ERRBUF_SIZE; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.snprintf_pargs;
        replace (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.convs (fmt "block of type %u in pcapng dump file is too short")) with [Cu] by (vm_compute; reflexivity);
        apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_cons; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.aeq_s32; reflexivity| apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_nil]
      | vm_compute; reflexivity | apply args_ok_ints1
      | eapply loop_restf; [exact G3 | exact NG3 | exact AR1 | exact SL3 | exact AR2 | exact BUF3 | exact PFX3 | exact LB3 | exact GR3 | exact CC3 | reflexivity] ]. }
  (* [comment removed for export] *)
  replace (bv_ltu (Z_to_bv 64 (cur_remaining c')) (Z_to_bv 64 4)) with false by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [negb].
  rewrite (proj2 (Z.ltb_ge (cur_remaining c') 4) GE4). cbv beta iota.
  assert (OFF0 : (8 <= cur_off c')%Z) by lia.
  assert (LEN4 : (cur_off c' + cur_remaining c' <= Z.of_nat (length buf'))%Z) by lia.
  destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.split_at4 buf' (Z.to_nat (cur_off c')) ltac:(lia)) as (pre & u0 & u1 & u2 & u3 & post & Ebuf & Lpre).
  assert (LpreZ : Z.of_nat (length pre) = cur_off c') by lia. clear Lpre.
  subst buf'.
  destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pfx_decomp pre [u0; u1; u2; u3] post bs3 PFX3) as (bsr & Ebs & PFXr). cbn [map] in Ebs. subst bs3.
  assert (GRh : (0 <= u0 < 256 /\ 0 <= u1 < 256 /\ 0 <= u2 < 256 /\ 0 <= u3 < 256)%Z).
  { apply Forall_app in GR3 as [GA GB].
    pose proof (Forall_inv GB) as B0. pose proof (Forall_inv (Forall_inv_tail GB)) as B1x. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail GB))) as B2x.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail GB)))) as B3. cbv beta in B0, B1x, B2x, B3. lia. }
  destruct GRh as (B0 & B1x & B2x & B3).
  (* [comment removed for export] *)
  unhide BUF3.
  pose proof (rw_cells_recell _ _ _ [CB (length pre) (map b8 pre); Cells.C2 (Z_to_bv 64 (u0 + 256 * u1)); Cells.C2 (Z_to_bv 64 (u2 + 256 * u3)); CB (length bsr) bsr] BUF3
                ltac:(cbn; rewrite length_map; repeat split; reflexivity) ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit by lia; rewrite !app_nil_r; cbn [app]; reflexivity)) as BX.
  destruct (rw_cells_cut _ _ _ 1 BX) as [_ BX2]. destruct (rw_cells_cut _ _ _ 2 BX2) as [HOPT _]. clear BX BX2. cbn [firstn skipn cells_size csize Nat.add app] in HOPT.
  remember (B + cur_off c')%Z as D eqn:HDd.
  lazymatch type of HOPT with rw_cells _ _ ?A _ => replace A with D in HOPT by lia end.
  hide BUF3.
  assert (DM4 : (D mod 4 = 0)%Z) by (subst D; clear - B2 OFF4; Z.div_mod_to_equations; lia).
  clear MU0 WM0.
  pose proof (munch_refl [(CUR, CUR + 16); (D, D + 4)]%Z m3) as MU. pose proof (wmono_refl asegs m3) as WM.
  unhide HPV3.
  ck0_at CUNP CUR; ck_go.
  zstep. zstep.
  zstep. ub_ltu.                             (* [comment removed for export] *)
  ck0_at CUNP CUR; ck_go.                    (* [comment removed for export] *)
  zstep.
  ck0_at CUNP (CUR + 8)%Z; ck_go.
  zstep. replace (cur_remaining c' + -4)%Z with (cur_remaining c' - 4)%Z by lia.
  zstep.
  ck0_at PUNP (P + 56)%Z; ck_go.
  zstep.
  rewrite (sx32_s32 (Z.b2z (pc_swapped p))) by (destruct (pc_swapped p); cbn; lia).
  rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.s32_small (Z.b2z (pc_swapped p))) by (destruct (pc_swapped p); cbn; lia).
  clear HPV3.
  zstep. zstep. zstep.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4a end.
  destruct (pc_swapped p) eqn:SW.
  - (* [comment removed for export] *)
    cbn [Z.b2z]. rewrite (eqb_lits_false 1 0) by lia. cbv iota.
    zstep. ub_al 1%Z ltac:(clear - DM4; Z.div_mod_to_equations; lia). zstep. if_false.       (* [comment removed for export] *)
    hide CC3.
    eapply evtF_cut.
    { eapply (swap_hdrA RNG3) with (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3) (Bq := B) (alloc := pc_bufalloc p) (bB := bB);
        [exact B0 | exact B1x | exact B2x | exact B3 | exact HOPT | exact MI3 | exact BUNP | lia | lia | exact DM4 | lia | exact B2 | lia
        | exact bBr | exact bBhi | exact bBlo | exact bBimg | exact BRNG | exact BRSH]. }
    cbv beta. intros ms' (a3v & a5v & s9v & m4 & -> & MU4 & WM4 & MI4 & HOPT4 & BUNP4).
    unhide CC3.
    assert (AGSd : agrees_on (fun a => outside [(D, D + 4)]%Z a) m4a m4) by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    apply (agrees_rw_cells _ _ _ _ _ AGSd) in CC3; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia].
    assert (MU34 : munch [(CUR, CUR + 16); (D, D + 4)]%Z m3 m4).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU4]. intros x Hx. cbn [outside fst snd] in Hx |- *. clear - Hx. tauto. }
    assert (WM34 : wmono asegs m3 m4) by (eapply wmono_trans; [exact WM | exact WM4]).
    assert (SWB : swap_field 2 (cur_off c' + 2) (swap_field 2 (cur_off c') (pre ++ u0 :: u1 :: u2 :: u3 :: post)) = pre ++ u1 :: u0 :: u3 :: u2 :: post)
      by (rewrite <- LpreZ, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.swap2_at, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.swap2_at2; reflexivity).
    assert (GL1 : get_le16 (pre ++ u1 :: u0 :: u3 :: u2 :: post) (cur_off c') = (u1 + 256 * u0)%Z) by (rewrite <- LpreZ; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.get_le16_at).
    assert (GL2 : get_le16 (pre ++ u1 :: u0 :: u3 :: u2 :: post) (cur_off c' + 2) = (u3 + 256 * u2)%Z) by (rewrite <- LpreZ; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.get_le16_at2).
    rewrite SWB, GL1, GL2. subst D.
    eapply (ai_body fuel LK _ _ _ io c' (pre ++ u0 :: u1 :: u2 :: u3 :: post) m3 (map b8 pre ++ [b8 u0; b8 u1; b8 u2; b8 u3] ++ bsr) cpad3 true pre post u0 u1 u2 u3 bsr m4);
      [exact IV | exact FUEL | exact GE4 | exact SW | reflexivity | exact LpreZ | reflexivity | exact PFXr | exact MI4 | exact MU34 | exact WM34 | exact CC3 | exact HOPT4].
  - (* [comment removed for export] *)
    cbn [Z.b2z]. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq 0 0 eq_refl). cbv iota.
    zstep. rewrite (eqb_lits_false D 0) by lia. cbv iota.        (* [comment removed for export] *)
    zstep. ub_al 1%Z ltac:(clear - DM4; Z.div_mod_to_equations; lia). zstep. if_false.       (* [comment removed for export] *)
    assert (GL1 : get_le16 (pre ++ u0 :: u1 :: u2 :: u3 :: post) (cur_off c') = (u0 + 256 * u1)%Z) by (rewrite <- LpreZ; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.get_le16_at).
    assert (GL2 : get_le16 (pre ++ u0 :: u1 :: u2 :: u3 :: post) (cur_off c' + 2) = (u2 + 256 * u3)%Z) by (rewrite <- LpreZ; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.get_le16_at2).
    rewrite GL1, GL2. subst D.
    eapply (ai_body fuel LK _ _ _ io c' (pre ++ u0 :: u1 :: u2 :: u3 :: post) m3 (map b8 pre ++ [b8 u0; b8 u1; b8 u2; b8 u3] ++ bsr) cpad3 false pre post u0 u1 u2 u3 bsr m4a);
      [exact IV | exact FUEL | exact GE4 | exact SW | reflexivity | exact LpreZ | reflexivity | exact PFXr | exact MI3 | exact MU | exact WM | exact CC3 | exact HOPT].
  Qed.
  End Sz9.
  End AIX.
  End CANSEC1.
End F_aiEA_iter.

(* [comment removed for export] *)
Module F_ngnBA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require Import UbGuardB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnEA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnEA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac apA lem := eapply lem; try eassumption.
Ltac transport H m' AG tac :=
  lazymatch type of H with rw_cells ?sg _ ?A ?cs =>
    let X := fresh in
    assert (X : rw_cells sg m' A cs) by (eapply agrees_rw_cells; [exact AG | exact H | tac]);
    clear H; rename X into H end.
(* [comment removed for export] *)
Ltac exit_sides FIN :=
  lazymatch goal with
  | |- OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_finalC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => FIN
  | |- is_ng _ = true => reflexivity
  | |- cells_size _ = _ => reflexivity
  | |- length (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes _) = _ => rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes_length; reflexivity
  | |- In _ client_globals => unfold client_globals; repeat (first [left; reflexivity | right])
  | |- fmt_ok _ _ = true => reflexivity
  | |- (length _ <= _)%nat => cbn; lia
  | |- Forall2 _ _ _ => cbn [length firstn]; repeat (constructor; [reflexivity|]); constructor
  | |- _ => lia
  end.
Ltac name_field data off a b c d DRNG :=
  set (a := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0%Z) in *; set (b := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1%Z) in *; set (c := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 2%Z) in *; set (d := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 3%Z) in *;
  let Ra := fresh "R" a in let Rb := fresh "R" b in let Rc := fresh "R" c in let Rd := fresh "R" d in
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 0%Z DRNG ltac:(lia)) as Ra; pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 1%Z DRNG ltac:(lia)) as Rb;
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 2%Z DRNG ltac:(lia)) as Rc; pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 3%Z DRNG ltac:(lia)) as Rd;
  fold a in Ra; fold b in Rb; fold c in Rc; fold d in Rd.

(* [comment removed for export] *)
Definition firstn2_q8__stmt : Prop := forall data (bs : list byte) (k : nat) off,
  firstn (length data) bs = map b8 data -> Z.of_nat k = off -> (off + 2 <= Z.of_nat (length data))%Z ->
  firstn 2 (skipn k bs) = [b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0); b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)].
Section Sz1.
Variables data bs k off : ltac2:(SecDiet.SzSec.tyM 'firstn2_q8__stmt "vvvv" @data).
#[using="Type"] Lemma firstn2_q8__body : ltac2:(SecDiet.SzSec.bodyP 'firstn2_q8__stmt "vvvv").
Proof.
  intros PFX Hk H1.
 subst off.
  destruct (zslice_2 (Z.of_nat k) data ltac:(lia) H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 (Z.of_nat k) data x0 x1 ltac:(lia) H1 E) as [E0 E1].
  transitivity (map b8 (zslice (Z.of_nat k) 2 data)).
  - unfold zslice, zfirstn, zskipn. rewrite <- firstn_map, <- skipn_map, <- PFX. rewrite skipn_firstn_comm, firstn_firstn, Nat2Z.id. f_equal. lia.
  - rewrite E. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8. rewrite Z.add_0_r, E0, E1. reflexivity.
Qed.
End Sz1.
Lemma firstn2_q8 : ltac:(let t := eval cbv delta [firstn2_q8__stmt] in firstn2_q8__stmt in exact t).
Proof. intros data bs k off. ltac2:(SecDiet.SzSec.closeP 'firstn2_q8__body "vvvv"). Qed.

Lemma get_le16_q8' : forall data off, (0 <= off)%Z -> (off + 2 <= Z.of_nat (length data))%Z ->
  get_le16 data off = (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0 + 256 * OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)%Z.
Proof.
  intros data off H0 H1. destruct (zslice_2 off data H0 H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 off data x0 x1 H0 H1 E) as [E0 E1].
  rewrite (get_le16_of_slice off data x0 x1 E). unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8. rewrite Z.add_0_r, E0, E1. reflexivity.
Qed.

Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.
Lemma bytes_wr_rw_cellsA : forall {rc : runConstT} mx A l, bytes_at asegs mx A l -> wr_at asegs mx A (Z.of_nat (length l)) -> rw_cells asegs mx A [CB (length l) l].
Proof. intros rc mx A l HB HW. split; [split; [cbn; split; [reflexivity| exact Logic.I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB] | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r; exact HW]. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (L : alayout) (RNG : footprint) (CLc FB : list (@cblock hptr)) (FL : list fblock) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
  Hypothesis LO : (ATOP + 4096 <= lo)%Z.
  Hypothesis BU : (lo + 57344 <= bv_unsigned sp)%Z.
  Hypothesis SPT : (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RTLS : rng_atls RNG.
  Hypothesis TPE : tp = Z_to_bv 64 ATP.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis HALO : (0x604000 <= HA /\ HA + 24 <= ATOP)%Z.
  Hypothesis DALO : (0x604000 <= DA /\ DA + 8 <= ATOP)%Z.
  Hypothesis HAP : (HA + 24 <= P \/ P + 680 <= HA)%Z.
  Hypothesis DAP : (DA + 8 <= P \/ P + 680 <= DA)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis HLOC : clocA FL CLc HA 24.
  Hypothesis DLOC : clocA FL CLc DA 8.

  Let POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation ngn_frameA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_final GIOA sp L RNG CLc FB FL P HA DA m o).
  #[local] Abbreviation ngn_finalC := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_finalC GIOA sp L RNG CLc FB FL P HA DA m o).

  Hypothesis PP : post_process_stmt.
  Hypothesis OHA : cobjA RNG m FL CLc HA 24.
  Hypothesis ODA : cobjA RNG m FL CLc DA 8.
  Hypothesis HDA : (HA + 24 <= DA \/ DA + 8 <= HA)%Z.
  Hypothesis HA8 : (HA mod 8 = 0)%Z.
  Hypothesis DA8 : (DA mod 8 = 0)%Z.

  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation pv := (A3P.F_ngnEA.TwB.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).

  (* [comment removed for export] *)
  Definition ngn_pp__stmt : Prop := forall (ra' t0' t1' t2' x0 a0' a2' a3' a5' a6' a7' x2 x3 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' ws wu : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc doff rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (sec usec cap len : Z) (dw : cell) (ccs' : list cell),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA (C8 (Z_to_bv 64 (Bq + doff)) :: C8 (Z_to_bv 64 rem) :: ccs')) -> cells_size ccs' = 8%nat -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA [C8 ws; C8 wu; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      ws = Z_to_bv 64 sec -> wu = Z_to_bv 64 usec -> Forall (fun x => 0 <= x < 256)%Z data ->
      (0 <= doff <= Z.of_nat (length data))%Z -> (doff mod 4 = 0)%Z ->
      (0 <= cap <= Z.of_nat (length data) - doff)%Z -> (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> ps_outfile ps = o -> (0 < alloc)%Z -> (0 <= rem < 2^63)%Z ->
      implMG RNG5 (let '(hdr, d) := pcapint_post_process linktype swapped (mkHdr sec usec cap len) (zskipn doff data) in
                   mret (1%Z, hdr, set_bufdata (zfirstn doff data ++ d) (pv bq alloc data eb sx ix))) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' x0 x3 a0' (Z_to_bv 64 cap) a2' a3' (Z_to_bv 64 rem) a5' a6' a7'
                 (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x2 (Z_to_bv 64 2147450880) x6 x7 x8 x9 x10 x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8dbdc) fc None m5 (seg_rom asegs)).
  Section Sz4.
  Variables ra' t0' t1' t2' x0 a0' a2' a3' a5' a6' a7' x2 x3 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' ws wu m5 RNG5 ps bq Bq Ix alloc doff rem data eb sx ix sec usec cap len dw ccs' : ltac2:(SecDiet.SzSec.tyM 'ngn_pp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  #[using="rc tlsI FO fflagA GL LO BU SPT RSTK RIMG RISH HALO DALO HAP DAP HLOC DLOC PP OHA ODA HDA HA8 DA8"] Lemma ngn_pp__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_pp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros FP5 ST5 FR5 Hccs MI5 G5 PC5 AG5 HH HD Hd -> -> DRNG Hdoff Hd4 Hcap Hl31 Hlen OF5 ALLOC0 REM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5. pose proof (rng_fp_le _ _ _ _ FP5 RIMG) as RIMG5. pose proof (rng_fp_le _ _ _ _ FP5 RISH) as RISH5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof atop_range as AR.
    (* [comment removed for export] *)
    pose proof (cobj_now FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G5 HLOC DLOC AG5 ODA ltac:(lia)) as (_ & (DA0 & DA47 & DUNP & DRNGf & DRSH & DAR & DBLK)).
    replace (DA - DA mod 8)%Z with DA in DRSH by lia. replace (8 + DA mod 8)%Z with 8%Z in DRSH by lia.
    band_ind DBLK bD.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ((BBAND & B3 & BTOP & B2) & B1 & BUNP & BRNG & BRSH & BAR).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof WF as (W1' & W2' & W3 & W4 & _ & _ & _ & _ & W9' & _).
    unfold A3P.F_ngnEA.TwB.pv, pcap_blocks, psize, is_ng in EPB, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB. unfold PCAP_NG_SF_TOTAL in APB.
    unfold A3P.F_ngnEA.TwB.pv in W3, W4, W9'. cbn [pc_bufalloc pc_bufdata pc_linktype] in W3, W4, W9'.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    band_ind PBAND bP. band_ind BBAND bB.
    (* [comment removed for export] *)
    assert (HinP2 : In (self, P, 680%Z) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) by (left; reflexivity).
    assert (HinB2 : In (bq, Bq, alloc) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) by (right; left; reflexivity).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G5 DLOC HinP2 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kDP & kDPr & kDP1 & kDP2).
    cbn [cb_addr cb_size fst snd] in kDP1, kDP2.
    assert (KHD : exists k, (0 <= k <= 1 /\ HA + 24 <= DA + k * 18446744073709551616 /\ DA + 8 <= HA + (1 - k) * 18446744073709551616)%Z)
      by (destruct HDA; [exists 0%Z | exists 1%Z]; lia).
    destruct KHD as (kHD & kHDr & kHD1 & kHD2).
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, A3P.F_ngnEA.TwB.pv in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    unfold A3P.F_ngnEA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA in FRJ. cbn [app] in FRJ.
    hide BUF. hide PRIV. hide HH. hide FR5.
    pose proof (munch_refl [(bv_unsigned sp + -240 + 112, bv_unsigned sp + -240 + 128); (DA, DA + 8)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG.
    (* [comment removed for export] *)
    zstep.
    do 2 zstep. ub_ltu.
    do 4 zstep. ub_xnull.
    do 3 zstep.
    (* [comment removed for export] *)
    zstep. ub_null.
    do 2 zstep. ub_al 7%Z ltac:(al8 DA8). zstep. if_false.
    zstep. ck0 DUNP; ck_go.
    zstep.
    zstep. if_cases BRZ; zify_cond BRZ. { exfalso. rewrite ?unsigned_lit in BRZ by lia. lia. }
    ck0_at PUNP (P + 100)%Z; ck_go.
    ck0_at PUNP (P + 56)%Z; ck_go.
    rewrite (sx32_small linktype) by lia.
    zstep. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
    zstep.
    unhide BUF. unhide PRIV. unhide HH. clear FR5.
    (* [comment removed for export] *)
    assert (FR5 : rw_cells asegs m0 (bv_unsigned sp + -240) (ngn_frameA (C8 (Z_to_bv 64 (Bq + doff + cap)) :: C8 (Z_to_bv 64 (rem - cap)) :: ccs'))) by exact FRJ.
    clear FRJ.
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G5 DLOC HinB2 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kDB & kDBr & kDB1 & kDB2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G5 HLOC HinB2 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kHB & kHBr & kHB1 & kHB2).
    cbn [cb_addr cb_size fst snd] in kDB1, kDB2, kHB1, kHB2.
    assert (AGD : agrees_on (fun a => outside [(bv_unsigned sp + -240 + 112, bv_unsigned sp + -240 + 128); (DA, DA + 8)]%Z a) m5 m0) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    assert (T0 : forall A cs, rw_cells asegs m5 A cs -> (A + Z.of_nat (cells_size cs) <= DA \/ DA + 8 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= ATOP)%Z -> rw_cells asegs m0 A cs).
    { intros A cs HC HA' HT. eapply agrees_rw_cells; [exact AGD | exact HC | intros a Ha; cbn [outside fst snd]; lia]. }
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs m5 _ [] (Z.to_nat alloc) _ [] [Z.to_nat doff; length data - Z.to_nat doff; Z.to_nat alloc - length data]%nat) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF.
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.pfx_split data bsx' (Z.to_nat doff) PFX ltac:(lia)) as [E0 E1]. rewrite E0, E1 in BUF.
    destruct (rw_cells_cut _ _ _ 1 BUF) as [BD0 BUF']. cbn [firstn skipn cells_size csize Nat.add] in BD0, BUF'.
    destruct (rw_cells_cut _ _ _ 1 BUF') as [BD BT]. clear BUF BUF'. cbn [firstn skipn cells_size csize Nat.add] in BD, BT.
    replace (Bq + Z.of_nat (Z.to_nat doff + 0))%Z with (Bq + doff)%Z in BD, BT by lia.
    replace (Bq + doff + Z.of_nat (length data - Z.to_nat doff + 0))%Z with (Bq + Z.of_nat (length data))%Z in BT by lia.
    apply T0 in BD0; [| cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
    apply T0 in BD; [| cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
    apply T0 in BT; [| cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
    apply T0 in HH; [| cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
    clear T0.
    assert (DL' : clocA FL (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) DA 8) by (eapply clocA_incl; [exact DLOC | apply incl_appl, incl_refl | apply incl_refl]).
    assert (G5' : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m0).
    { eapply (gl_client_frame _ _ _ GL); [exact G5 | exact MU | exact WM |]. apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [exact (clocA_iv _ _ _ _ DL')| apply Forall_nil]. }
    assert (PC5' : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m0).
    { eapply PCAPR_agree; [exact AGD | | exact PC5]. intros a Ha. cbn [outside fst snd].
      pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)) as AB.
      split; [lia|]. split; [| exact Logic.I]. intros Hr.
      exact (clocA_not_PB FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ a G5 DLOC Hr Ha). }
    assert (AG5' : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m0).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGD|]. intros a [K [_ Hn]]; cbn [outside fst snd].
      destruct (keeps_facts FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ a G5 K) as [Ks|[Kb _]]; (split; [lia|]; split; [lia| exact Logic.I]). }
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G5') as (RT5 & _).
    pose proof (cobj_now FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G5' HLOC DLOC AG5' OHA ltac:(lia)) as (_ & OHA5).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5' HinB) as BBLK.
    clear MU WM AGD G5 AG5 PC5.
    assert (ZA : zarr m0 (Bq + doff) (zskipn doff data)).
    { unfold zskipn. split; [| split; [| apply Forall_range_skipn; exact DRNG]].
      - pose proof (rw_cells_bytes_at _ _ _ _ BD) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X.
      - eapply rw_cells_wr_at; [exact BD|]. cbn [cells_size csize Nat.add]. rewrite length_skipn. lia. }
    change (rw_cells asegs m0 HA (pkthdr_cells (Z_to_bv 64 sec) (Z_to_bv 64 usec) (mkHdr sec usec cap len))) in HH.
    assert (LD : Z.of_nat (length (zskipn doff data)) = (Z.of_nat (length data) - doff)%Z) by (unfold zskipn; rewrite length_skipn; lia).
    name_sp sp (-240)%Z.
    eapply evtF_cut.
    { eapply PP with (lo := lo) (HA := HA) (DA := (Bq + doff)%Z) (hdr := mkHdr sec usec cap len) (d := zskipn doff data) (linktype := linktype) (swapped := swapped)
                     (ws := Z_to_bv 64 sec) (wu := Z_to_bv 64 usec);
        [ rewrite Hsp; assumption | unfold PP_FRAME; rewrite Hsp; lia | exact LO | exact HH | exact ZA | assumption | exact RT5
        | reflexivity | reflexivity | reflexivity | reflexivity
        | lia | cbn [h_caplen]; lia | lia | cbn [h_len]; lia
        | exact OHA5
        | eapply blockA_aobj; [exact BBLK | cbn [cb_addr cb_size fst snd]; lia | cbn [cb_addr cb_size fst snd]; lia | lia]
        | lia | lia | lia | exact HA8 | clear - B2 Hd4; Z.div_mod_to_equations; lia
        | eapply rng_sub'; [exact RSTK5| rewrite Hsp; lia] | exact RIMG5 | exact RISH5 ]. }
    cbv beta. intros ms' PO. unfold post_process_post in PO. destruct_exs PO. destruct PO as (-> & MU6 & WM6 & MI6 & ST6 & HH6 & ZA6).
    rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 580700)) with (Z_to_bv 64 580700) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    cbn [h_caplen] in MU6. unfold PP_FRAME in MU6.
    lazymatch type of MU6 with munch _ _ ?mb => rename mb into m6 end.
    set (hdr' := fst (pcapint_post_process linktype swapped (mkHdr sec usec cap len) (zskipn doff data))) in *.
    set (d' := snd (pcapint_post_process linktype swapped (mkHdr sec usec cap len) (zskipn doff data))) in *.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts.pp_length linktype swapped (mkHdr sec usec cap len) (zskipn doff data)) as LEN'. fold d' in LEN'.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts.pp_sec linktype swapped (mkHdr sec usec cap len) (zskipn doff data)) as [SEC' USEC']. fold hdr' in SEC', USEC'. cbn [h_sec h_usec] in SEC', USEC'.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts.pp_range linktype swapped (mkHdr sec usec cap len) (zskipn doff data) ltac:(cbn [h_caplen]; lia) ltac:(cbn [h_len]; lia) ltac:(lia)) as [RC' RL']. fold hdr' in RC', RL'.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -240 - 64, bv_unsigned sp + -240); (HA + 20, HA + 24); (Bq + doff, Bq + doff + cap)]%Z a) m0 m6)
      by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    apply (agrees_rw_cells _ _ _ _ _ AGS) in FR5; [| intros a Ha; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA in Ha; rewrite !cells_size_app in Ha; cbn [outside fst snd cells_size csize Nat.add] in *; rewrite Hccs in Ha; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HD'; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in *; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in BT; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in *; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in BD0; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in *; lia].
    (* [comment removed for export] *)
    destruct ZA6 as (ZB & ZW & ZR).
    pose proof (bytes_wr_rw_cellsA _ _ _ ZB ltac:(rewrite zbytes_length; exact ZW)) as BD6. rewrite zbytes_length in BD6.
    pose proof (rw_cells_uncut _ _ _ _ _ BD6 BT ltac:(cbn [cells_size csize Nat.add]; rewrite LEN'; unfold zskipn; rewrite length_skipn; lia)) as BDT. cbn [app] in BDT.
    pose proof (rw_cells_uncut _ _ _ _ _ BD0 BDT ltac:(cbn [cells_size csize Nat.add]; lia)) as BUF6. cbn [app] in BUF6.
    merge_all BUF6.
    replace (Z.to_nat doff + (length d' + (Z.to_nat alloc - length data + 0)))%nat with (Z.to_nat alloc) in BUF6 by (rewrite LEN'; unfold zskipn; rewrite length_skipn; lia).
    rewrite app_nil_r in BUF6.
    rewrite (surjective_pairing (pcapint_post_process linktype swapped _ _)). fold hdr' d'.
    change (set_bufdata (zfirstn doff data ++ d') (pv bq alloc data eb sx ix)) with (pv bq alloc (zfirstn doff data ++ d') eb sx ix).
    assert (HL' : clocA FL (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (HA + 20) 4).
    { eapply clocA_sub; [eapply clocA_incl; [exact HLOC | apply incl_appl, incl_refl | apply incl_refl] | lia | lia]. }
    pose proof (clocA_iv _ _ _ _ HL') as HIV. replace (HA + 20 + 4)%Z with (HA + 24)%Z in HIV by lia.
    assert (G6 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m6).
    { eapply (gl_client_frame _ _ _ GL); [exact G5' | exact MU6 | exact WM6 |].
      apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [exact HIV|]. apply Forall_cons; [| apply Forall_nil].
      right; left. unfold iv_in_block. apply Exists_exists. exists (bq, Bq, alloc). split; [apply in_or_app; right; exact HinB2| cbn [cb_addr cb_size fst snd]; lia]. }
    assert (LENX : length (zfirstn doff data ++ d') = length data).
    { unfold zfirstn. rewrite length_app, length_firstn, LEN'. unfold zskipn. rewrite length_skipn. lia. }
    assert (PFX6 : firstn (length (zfirstn doff data ++ d')) (map PcapRep.b8 (firstn (Z.to_nat doff) data) ++ zbytes d' ++ firstn (Z.to_nat alloc - length data) (skipn (length data - Z.to_nat doff) (skipn (Z.to_nat doff) bsx')))
                   = map b8 (zfirstn doff data ++ d')).
    { unfold zfirstn. rewrite length_app, length_firstn, map_app.
      replace (Nat.min (Z.to_nat doff) (length data) + length d')%nat with (length (map PcapRep.b8 (firstn (Z.to_nat doff) data) ++ zbytes d')) by (rewrite length_app, length_map, length_firstn, zbytes_length; lia).
      rewrite app_assoc, firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. reflexivity. }
    assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc (zfirstn doff data ++ d') eb sx ix) (pcap_blocks (pv bq alloc (zfirstn doff data ++ d') eb sx ix) P Bq Ix) FB m6).
    { eapply (@PCAPR_bufdata2 rc tlsI H hptr FO GIOA fflagA GL) with (m5 := m0) (data := data)
               (Q := fun a => outside [(bv_unsigned sp + -240 - 64, bv_unsigned sp + -240); (HA + 20, HA + 24); (Bq + doff, Bq + doff + cap)]%Z a);
        [exact G5' | exact PC5' | exact AGS | | exact BUF6 | exact PFX6 | exact LENX].
      intros a Hina Hnb. cbn [outside fst snd].
      pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5' ltac:(apply in_block_app; left; apply in_block_app; right; exact Hina)) as AB.
      split; [lia|]. split; [| split; [lia| exact Logic.I]].
      intros Hr. exact (clocA_not_PB FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ a G5' HLOC ltac:(lia) Hina). }
    assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AGS|]. intros a [K [Hn1 Hn2]]. cbn [outside fst snd].
      destruct (keeps_facts FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ a G5' K) as [Ks|[Kb Kn]].
      - split; [lia|]. split; [lia|]. split; [lia| exact Logic.I].
      - split; [lia|]. split; [lia|]. split; [| exact Logic.I]. intros Hr. apply Kn.
        unfold pcap_blocks, in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc A3P.F_ngnEA.TwB.pv]. lia. }
    apply evtF_done.
    eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_ret_1 rc H hptr GIOA) with (PB' := pcap_blocks (pv bq alloc (zfirstn doff data ++ d') eb sx ix) P Bq Ix) (ccs := C8 (Z_to_bv 64 (Bq + doff + cap)) :: C8 (Z_to_bv 64 (rem - cap)) :: ccs');
      try eassumption; [cbn [cells_size csize]; rewrite Hccs; reflexivity | ].
    split; [exact FP5|]. split; [exact G6|]. split; [exact PC6|]. split; [exact AG6|].
    split. { unfold hdr_cells. rewrite SEC', USEC'. exact HH6. }
    split; [reflexivity|]. split; [exact HD'|]. split; [reflexivity| exact OF5].
  Qed.
  End Sz4.
  #[using="rc tlsI FO fflagA GL LO BU SPT RSTK RIMG RISH HALO DALO HAP DAP HLOC DLOC PP OHA ODA HDA HA8 DA8"] Lemma ngn_pp : ltac:(let t := eval cbv delta [ngn_pp__stmt] in ngn_pp__stmt in exact t).
  Proof. intros ra' t0' t1' t2' x0 a0' a2' a3' a5' a6' a7' x2 x3 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' ws wu m5 RNG5 ps bq Bq Ix alloc doff rem data eb sx ix sec usec cap len dw ccs'. ltac2:(SecDiet.SzSec.closeP 'ngn_pp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgnCtx.
End CANSEC1.
End F_ngnBA.
