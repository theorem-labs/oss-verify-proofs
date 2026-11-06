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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require AccFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_aiBA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.
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

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
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
  Hypothesis BU : (lo + 16512 <= bv_unsigned sp)%Z.
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
    /\ (exists bI, (0 <= bI <= 1 /\ I' + N <= 2147446784 + bI * 140737479966720 /\ 17594333495296 * bI <= I' /\ 6303744 <= I')%Z)
    /\ (P + 680 <= I' \/ I' + N <= P)%Z /\ (B + pc_bufalloc p <= I' \/ I' + N <= B)%Z /\ (EB + 256 <= I' \/ I' + N <= EB)%Z.
  Section Sz1.
  Variables RNG3 st3 q1 I' N m3 : ltac2:(SecDiet.SzSec.tyM 'ai_head__stmt "vvvvvv" @RNG3).
  #[using="tlsI FO fflagA GL sp lo LO BU GPL HinP HinB EBL"] Lemma ai_head__body : ltac2:(SecDiet.SzSec.bodyP 'ai_head__stmt "vvvvvv").
  Proof.
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
  #[using="tlsI FO fflagA GL sp lo LO BU GPL HinP HinB EBL"] Lemma ai_head : ltac:(let t := eval cbv delta [ai_head__stmt] in ai_head__stmt in exact t).
  Proof. intros RNG3 st3 q1 I' N m3. ltac2:(SecDiet.SzSec.closeP 'ai_head__body "vvvvvv"). Qed.

  #[using="Type"] Lemma ifs_cells_app : forall (l1 l2 : list ng_if) (j1 j2 : list if_junk),
    length j1 = length l1 -> ifs_cells l1 j1 ++ ifs_cells l2 j2 = ifs_cells (l1 ++ l2) (j1 ++ j2).
  Proof.
    clear. induction l1 as [|i0 l1 IH]; intros l2 [|j j1] j2 HL; cbn [length] in HL; try discriminate HL; [reflexivity|].
    cbn [ifs_cells app]. rewrite <- app_assoc. f_equal. apply IH. lia.
  Qed.

  (* [comment removed for export] *)
  Definition ai_tail__stmt : Prop := forall (ra' a0' a1' a2' a3' a4' a5' a6' a7' t3' t5' y0 y3 y4 y7 y8 y9 y10 y11 : word)
      (m3 : mem) (RNG3 : footprint) (stG : PS) (sg : pcap_ng_sf) (q1 : hptr) (I' SA : Z) (js : list if_junk) (pad1 sj tail3 bs3 cpad3 : list byte)
      (opts : idbopts) (c' : cursor) (buf' : list Z) (hd : list cell),
    ng_user_tsresol sg = ng_user_tsresol s -> ng_max_blocksize sg = ng_max_blocksize s -> ng_ifaces sg = ng_ifaces s ->
    (ng_ifcount sg = Z.of_nat (length (ng_ifaces s)) + 1)%Z -> (ng_ifcount sg <= ng_ifaces_size sg)%Z -> (1 <= ng_ifaces_size sg < 2^26)%Z ->
    length js = length (ng_ifaces s) ->
    (SA = I' + 40 * (ng_ifcount sg - 1))%Z ->
    (0 <= ai_snap < 2^32)%Z -> (0 < io_tsresol opts < 2^64)%Z ->
    fp_le RNG RNG3 ->
    mem_inv asegs m3 -> stk asegs m3 lo (bv_unsigned sp + -128) -> AGP m3 ->
    rw_cells asegs m3 (bv_unsigned sp + -128) hd -> cells_size hd = 24%nat -> FRAME m3 ->
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
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 (Z.shiftr (P + 672) 3 + 2147450880)) (Z_to_bv 64 (io_tsresol opts)) (Z_to_bv 64 (Z.b2z (io_is_binary opts)))
               y0 (Z_to_bv 64 (P + 648)) a0' a1' a2' a3' a4' a5' a6' a7'
               (Z_to_bv 64 (P + 660)) y3 y4 (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 660) 3 + 2147450880)) y7 y8 y9 y10 y11
               t3' (Z_to_bv 64 (io_tsoffset opts)) t5' (Z_to_bv 64 (P + 672)))
          F (Z_to_bv 64 0x8c6cc) fc None m3 (seg_rom asegs)).
  Section Sz3.
  Variables ra' a0' a1' a2' a3' a4' a5' a6' a7' t3' t5' y0 y3 y4 y7 y8 y9 y10 y11 m3 RNG3 stG sg q1 I' SA js pad1 sj tail3 bs3 cpad3 opts c' buf' hd : ltac2:(SecDiet.SzSec.tyM 'ai_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  #[using="rc tlsI FO fflagA GL LO BU SPT RSTK GPL HinP HinB P14 LENB CURS EBL EBP EBB UTS IFW"] Lemma ai_tail__body : ltac2:(SecDiet.SzSec.bodyP 'ai_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros U1 U2 U5 IC1 IC2 SZ LJS HSA SNR TSR FP3 MI3 ST3 AG3 HD3 Hhd FR3 NG3 AR1 SL3 AR2 G3 BUF3 PFX3 LB3 GR3 CC3 CR1 CR2 CR3 CR4 HEB3 OFG.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as AR.
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
    ck0_at PUNP (P + 672)%Z; ck_go.
    ck0_at PUNP (P + 660)%Z; ck_go.
    zstep. rewrite (sx32_small (ng_ifcount sg)) by lia.
    do 7 zstep.
  replace (Z.shiftr ((Z.shiftl (ng_ifcount sg + -1) 32) mod 18446744073709551616 * 171798691840) 64) with ((ng_ifcount sg - 1) * 40)%Z
    by (rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mod_small by lia; change (2^32)%Z with 4294967296%Z; rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.mulhu40 (ng_ifcount sg + -1)) by lia; lia).
  replace (I' + (ng_ifcount sg - 1) * 40 + 8)%Z with (SA + 8)%Z by lia.
  ck0 IUNP; ck_go.
  do 6 zstep.
  rewrite (Z.mod_small (ng_ifcount sg + -1) 4294967296) by lia.
  replace (I' + (ng_ifcount sg + -1) * 40 + 32)%Z with (SA + 32)%Z by lia.
  ck0 IUNP; ck_go.
  zstep.
  ck0_at PUNP (P + 648)%Z; ck_go.
  zstep. zstep.
    (* [comment removed for export] *)
    assert (LEAF : forall (ra'' t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 : word) (m5 : mem) (jn : if_junk),
      mem_inv asegs m5 -> stk asegs m5 lo (bv_unsigned sp + -128) ->
      munch [(SA, SA + 40)]%Z m3 m5 -> wmono asegs m3 m5 ->
      rw_cells asegs m5 SA (if_cells (ai_slot opts) jn) ->
      evtF asegs RNG3 (POSTQ (ai_result sg (Some q1) (buf', inr (opts, c'))) stG RNG3)
        (MS (mkR ra'' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0'' t1'' t2'' z0 z1 (Z_to_bv 64 1) a1'' a2'' a3'' a4'' a5'' a6'' a7''
                 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 t3'' t4'' t5'' t6'') F (Z_to_bv 64 0x8c970) fc None m5 (seg_rom asegs))).
    { intros until jn. intros MI5 ST5 MU5 WM5 SL5.
      assert (AGS : agrees_on (fun a => outside [(SA, SA + 40)]%Z a) m3 m5) by (eapply agrees_on_of_munch; [exact MU5 | exact WM5 | intros a _ Ho; exact Ho]).
      unhide HD3. unhide FR3.
      transport HD3 m5 AGS ltac:(intros a Ha; rewrite Hhd in Ha; cbn [outside fst snd]; lia).
      transport FR3 m5 AGS ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
      unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result.
      eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.ai_exit with (ok := true) (hd := hd); try eassumption.
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
      do 4 zstep.
  replace (I' + (ng_ifcount sg + -1) * 40 + 16)%Z with (SA + 16)%Z by lia.
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
      do 3 zstep.
      destruct (Z.lt_ge_cases (ng_user_tsresol sg) (io_tsresol opts)) as [LT|GE].
      + (* [comment removed for export] *)
        replace (bv_ltu (Z_to_bv 64 (ng_user_tsresol sg)) (Z_to_bv 64 (io_tsresol opts))) with true
          by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
        destruct (io_is_binary opts) eqn:BIN; cbn [Z.b2z].
        * (* [comment removed for export] *)
          zstep. zstep. if_false. zstep.
          replace (I' + (ng_ifcount sg + -1) * 40 + 16)%Z with (SA + 16)%Z by lia.
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
          zstep. zstep. if_true. zstep.
          replace (I' + (ng_ifcount sg + -1) * 40 + 24)%Z with (SA + 24)%Z by lia.
          ck0 IUNP; ck_go.
          zstep.
          rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.m_divu (Z_to_bv 64 (io_tsresol opts)) (Z_to_bv 64 (ng_user_tsresol sg))) by (rewrite unsigned_lit by lia; lia).
          rewrite !(unsigned_lit (io_tsresol opts)), !(unsigned_lit (ng_user_tsresol sg)) by lia.
          zstep. zstep.
          replace (I' + (ng_ifcount sg + -1) * 40 + 16)%Z with (SA + 16)%Z by lia.
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
          zstep. if_false. zstep. zstep.
          replace (I' + (ng_ifcount sg + -1) * 40 + 16)%Z with (SA + 16)%Z by lia.
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
          zstep. if_true. zstep. zstep.
          replace (I' + (ng_ifcount sg + -1) * 40 + 24)%Z with (SA + 24)%Z by lia.
          ck0 IUNP; ck_go.
          zstep.
          rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.m_divu (Z_to_bv 64 (ng_user_tsresol sg)) (Z_to_bv 64 (io_tsresol opts))) by (rewrite unsigned_lit by lia; lia).
          rewrite !(unsigned_lit (io_tsresol opts)), !(unsigned_lit (ng_user_tsresol sg)) by lia.
          zstep. zstep.
          replace (I' + (ng_ifcount sg + -1) * 40 + 16)%Z with (SA + 16)%Z by lia.
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
  #[using="rc tlsI FO fflagA GL LO BU SPT RSTK GPL HinP HinB P14 LENB CURS EBL EBP EBB UTS IFW"] Lemma ai_tail : ltac:(let t := eval cbv delta [ai_tail__stmt] in ai_tail__stmt in exact t).
  Proof. intros ra' a0' a1' a2' a3' a4' a5' a6' a7' t3' t5' y0 y3 y4 y7 y8 y9 y10 y11 m3 RNG3 stG sg q1 I' SA js pad1 sj tail3 bs3 cpad3 opts c' buf' hd. ltac2:(SecDiet.SzSec.closeP 'ai_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End AIX.
End CANSEC1.
End F_aiBA.

(* [comment removed for export] *)
Module F_aiEA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiBA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.
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

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
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
  Definition swap_hdrA__stmt : Prop := forall (RNGx : footprint) (ra_ sp_ gp_ tp_ t0 t1 t2 s1_ a1 a2 a4 a5 a6 a7 s2_ s3_ s4_ s6_ s7_ s8_ s9_ s10_ s11_ t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc_ : bv 32)
           (mx : mem) (u0 u1 u2 u3 : Z) (Bq alloc bB D : Z),
      (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> (0 <= u2 < 256)%Z -> (0 <= u3 < 256)%Z ->
      rw_cells asegs mx D [Cells.C2 (Z_to_bv 64 (u0 + 256 * u1)); Cells.C2 (Z_to_bv 64 (u2 + 256 * u3))] ->
      mem_inv asegs mx ->
      unpoisoned mx Bq (Bq + alloc) -> (Bq <= D)%Z -> (D + 4 <= Bq + alloc)%Z -> (D mod 4 = 0)%Z ->
      (Bq + alloc <= ATOP)%Z -> (Bq mod 16 = 0)%Z -> (0 < Bq)%Z ->
      (0 <= bB <= 1)%Z -> (Bq + alloc <= 2147446784 + bB * 140737479966720)%Z -> (17594333495296 * bB <= Bq)%Z -> (6303744 <= Bq)%Z ->
      rng RNGx Bq alloc -> rng RNGx (shad Bq) (nshad alloc) ->
      evtF asegs RNGx (fun ms' => exists (rav a5v s9v : word) (m' : mem),
          ms' = MS (mkR rav sp_ gp_ tp_ t0 t1 t2 (Z_to_bv 64 (Z.shiftr D 3)) s1_ (Z_to_bv 64 D) a1 a2 (Z_to_bv 64 (D + 2)) a4 a5v a6 a7
                       s2_ s3_ s4_ (Z_to_bv 64 2147450880) s6_ s7_ s8_ s9v s10_ s11_ t3 t4 t5 t6) F_ (Z_to_bv 64 0x8c45c) fc_ None m' (seg_rom asegs)
          /\ munch [(D, D + 4)]%Z mx m' /\ wmono asegs mx m' /\ mem_inv asegs m'
          /\ rw_cells asegs m' D [Cells.C2 (Z_to_bv 64 (u1 + 256 * u0)); Cells.C2 (Z_to_bv 64 (u3 + 256 * u2))]
          /\ unpoisoned m' Bq (Bq + alloc))
        (MS (mkR ra_ sp_ gp_ tp_ t0 t1 t2 (Z_to_bv 64 (Z.shiftr D 3)) s1_ (Z_to_bv 64 D) a1 a2 (Z_to_bv 64 (D + 2)) a4 a5 a6 a7
                 s2_ s3_ s4_ (Z_to_bv 64 2147450880) s6_ s7_ s8_ s9_ s10_ s11_ t3 t4 t5 t6) F_ (Z_to_bv 64 0x8c408) fc_ None mx (seg_rom asegs)).
  Section Sz8.
  Variables RNGx ra_ sp_ gp_ tp_ t0 t1 t2 s1_ a1 a2 a4 a5 a6 a7 s2_ s3_ s4_ s6_ s7_ s8_ s9_ s10_ s11_ t3 t4 t5 t6 F_ fc_ mx u0 u1 u2 u3 Bq alloc bB D : ltac2:(SecDiet.SzSec.tyM 'swap_hdrA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  #[using="Type"] Lemma swap_hdrA__core : ltac2:(SecDiet.SzSec.bodyP 'swap_hdrA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros B0 B1x B2x B3 HOPT MIx BUNP INB1 INB2 DM4 BTOP BM16 BPOS bBr bBhi bBlo bBimg BRNG BRSH.
    pose proof atop_range as AR.
    pose proof (munch_refl [(D, D + 4)]%Z mx) as MU. pose proof (wmono_refl asegs mx) as WM.
    ckp_at BUNP D 2%Z.
  do 2 zstep.
  ck_cut 0x8c414%Z [15%Z].
  do 2 zstep.
  ck_cut 0x8c420%Z [15%Z].
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
  ck_cut 0x8c440%Z [15%Z].
  do 2 zstep.
  ck_cut 0x8c44c%Z [15%Z].
  rewrite (zx16_lit (u2 + 256 * u3)) by lia.
  do 3 zstep.
  match goal with |- context [Z_to_bv 64 (Z.lor ?a ?b)] =>
    replace (Z.lor a b) with (u3 + 256 * u2 + 65536 * u3)%Z
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia;
          replace ((u2 + 256 * u3) / 2 ^ 8)%Z with u3 by (Z.div_mod_to_equations; lia);
          rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.lor_high_low (u2 + 256 * u3) u3 8) by lia; lia) end.
  zstep.
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
  Hypothesis BU : (lo + 16512 <= bv_unsigned sp)%Z.
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
  Definition ai_hd : list cell := [C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 EB); C8 (Z_to_bv 64 65280)].

  (* [comment removed for export] *)
  Definition sgF : pcap_ng_sf := mkNg (ng_user_tsresol sg) (ng_max_blocksize sg) (ng_ifcount sg) (ng_ifaces_size sg) (ai_slot0 :: ng_ifaces sg).
  Definition pF (buf' : list Z) : pcapT := set_bufdata buf' (set_ng sgF (Some q1) (set_ng sg (Some q1) p)).
  #[using="Type"] Lemma ai_result_inl : forall buf' msg, ai_result sg (Some q1) (buf', inl msg) = (false, c, pF buf', msg).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition AIM (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte) : Prop :=
    (0 < io_tsresol io < 2^64)%Z /\
    mem_inv asegs m3 /\ stk asegs m3 lo (bv_unsigned sp + -128) /\ AGP m3 /\
    rw_cells asegs m3 (bv_unsigned sp + -128) ai_hd /\ FRAME m3 /\
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
  Definition LREGS (ra' x8 a0' a3' a4' a5' x19 x25 : word) (io : idbopts) (c' : cursor) :=
    mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 (Z.shiftr (P + 672) 3 + 2147450880)) (Z_to_bv 64 (io_tsresol io)) (Z_to_bv 64 (Z.b2z (io_is_binary io)))
        x8 (Z_to_bv 64 (P + 648)) a0' (Z_to_bv 64 (CUR + 8)) (Z_to_bv 64 CUR) a3' a4' a5' (Z_to_bv 64 (cur_remaining c')) (Z_to_bv 64 (P + 56))
        (Z_to_bv 64 (P + 660)) x19 (Z_to_bv 64 (Z.b2z (io_saw_tsoffset io))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 660) 3 + 2147450880))
        (Z_to_bv 64 10) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x25 (Z_to_bv 64 (Z.b2z (io_saw_tsresol io))) (Z_to_bv 64 (Z.shiftr CUR 3 + 2147450880))
        (Z_to_bv 64 (Z.shiftr (CUR + 8) 3 + 2147450880)) (Z_to_bv 64 (io_tsoffset io)) (Z_to_bv 64 3) (Z_to_bv 64 (P + 672)).

  Definition LOOPK (fuel : nat) : Prop :=
    forall (ra' x8 a0' a3' a4' a5' x19 x25 : word) (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte),
      AIM io c' buf' m3 bs3 cpad3 -> (cur_remaining c' / 4 < Z.of_nat fuel)%Z ->
      evtF asegs RNG3 (POSTQ (ai_result sg (Some q1) (process_idb_options_loop fuel (pc_swapped p) io c' buf')) stG RNG3)
        (MS (LREGS ra' x8 a0' a3' a4' a5' x19 x25 io c') F (Z_to_bv 64 0x8c3c0) fc None m3 (seg_rom asegs)).
  Definition ITERK (fuel : nat) : Prop :=
    forall (ra' x8 a0' a3' a4' a5' x19 x25 : word) (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte),
      AIM io c' buf' m3 bs3 cpad3 -> (cur_remaining c' / 4 < Z.of_nat (S fuel))%Z -> (0 < cur_remaining c')%Z ->
      evtF asegs RNG3 (POSTQ (ai_result sg (Some q1) (process_idb_options_loop (S fuel) (pc_swapped p) io c' buf')) stG RNG3)
        (MS (LREGS ra' x8 a0' a3' a4' a5' x19 x25 io c') F (Z_to_bv 64 0x8c3c4) fc None m3 (seg_rom asegs)).

  #[using="Type"] Lemma ai_loop0 : LOOPK O.
  Proof. red. intros until cpad3. intros IV FUEL. destruct IV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR1 & _). exfalso. clear - FUEL CR1. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Definition ai_loop_step__stmt : Prop := forall fuel, ITERK fuel -> LOOPK (S fuel).
  Section Sz3.
  Variables fuel : ltac2:(SecDiet.SzSec.tyM 'ai_loop_step__stmt "v" @fuel).
  Lemma ai_loop_step__body : ltac2:(SecDiet.SzSec.bodyP 'ai_loop_step__stmt "v").
  Proof using rc tlsI H hptr FO GIOA fflagA GL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej LO BU SPT RSTK GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB UTS IFW IDB0 COFF CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG fuel.
    intros IT.
 red. intros until cpad3. intros IV FUEL.
    pose proof IV as IV'. destruct IV' as (TSR & MI3 & ST3 & AG3 & HD3 & FR3 & NG3 & AR1 & SL3 & AR2 & G3 & BUF3 & PFX3 & LB3 & GR3 & CC3 & CR1 & CR2 & CR3 & CR4 & HEB3 & OFF4).
    hide HD3. hide FR3. hide NG3. hide AR1. hide SL3. hide AR2. hide BUF3. hide CC3. hide HEB3.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    unfold LREGS. zstep.
    destruct (Z.eq_dec (cur_remaining c') 0) as [R0|R0].
    - rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ R0). cbv iota. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_unfold. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_iter. rewrite (proj2 (Z.eqb_eq _ _) R0).
      unhide HD3. unhide FR3. unhide NG3. unhide AR1. unhide SL3. unhide AR2. unhide BUF3. unhide CC3. unhide HEB3.
      eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiBA.ai_tail with (hd := ai_hd) (SA := SA) (js := js); eassumption || (try exact IC1; try exact HSA; try reflexivity; try lia).
    - rewrite (eqb_lits_false (cur_remaining c') 0) by lia. cbv iota.
      unhide HD3. unhide FR3. unhide NG3. unhide AR1. unhide SL3. unhide AR2. unhide BUF3. unhide CC3. unhide HEB3.
      apply (IT _ _ _ _ _ _ _ _ io c' buf' m3 bs3 cpad3 IV FUEL ltac:(lia)).
  Qed.
  End Sz3.
  #[using="rc tlsI FO fflagA GL LO BU SPT RSTK GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB UTS IFW IDB0 COFF CEND APB EBP2 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG"] Lemma ai_loop_step : ltac:(let t := eval cbv delta [ai_loop_step__stmt] in ai_loop_step__stmt in exact t).
  Proof. intros fuel. ltac2:(SecDiet.SzSec.closeP 'ai_loop_step__body "v"). Qed.

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
      stk asegs m5 lo (bv_unsigned sp + -128) /\ AGP m5 /\
      rw_cells asegs m5 (bv_unsigned sp + -128) ai_hd /\ FRAME m5 /\
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
    forall (ra' x8 x25 : word) (io : idbopts) (c' : cursor) (sw : bool) (pre post : list Z) (c0 c1 l0 l1 : Z) (bsr cpad3 : list byte) (m5 : mem) (D : Z),
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
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 (Z.shiftr (P + 672) 3 + 2147450880)) (Z_to_bv 64 (io_tsresol io)) (Z_to_bv 64 (Z.b2z (io_is_binary io)))
                 x8 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 D) (Z_to_bv 64 (CUR + 8)) (Z_to_bv 64 CUR) (Z_to_bv 64 olen) (Z_to_bv 64 (D + 4)) (Z_to_bv 64 code)
                 (Z_to_bv 64 (cur_remaining c' - 4 - padded)) (Z_to_bv 64 (P + 56))
                 (Z_to_bv 64 (P + 660)) (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 (Z.b2z (io_saw_tsoffset io))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 660) 3 + 2147450880))
                 (Z_to_bv 64 10) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x25 (Z_to_bv 64 (Z.b2z (io_saw_tsresol io))) (Z_to_bv 64 (Z.shiftr CUR 3 + 2147450880))
                 (Z_to_bv 64 (Z.shiftr (CUR + 8) 3 + 2147450880)) (Z_to_bv 64 (io_tsoffset io)) (Z_to_bv 64 3) (Z_to_bv 64 (P + 672)))
            F (Z_to_bv 64 0x8c4ac) fc None m5 (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition ai_body__stmt : Prop := forall fuel, LOOPK fuel ->
    forall (ra' a5' x25 : word) (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte)
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
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 (Z.shiftr (P + 672) 3 + 2147450880)) (Z_to_bv 64 (io_tsresol io)) (Z_to_bv 64 (Z.b2z (io_is_binary io)))
                 (Z_to_bv 64 (Z.shiftr (B + cur_off c') 3)) (Z_to_bv 64 (P + 648)) (Z_to_bv 64 (B + cur_off c')) (Z_to_bv 64 (CUR + 8)) (Z_to_bv 64 CUR)
                 (Z_to_bv 64 (B + cur_off c' + 2)) (Z_to_bv 64 (B + cur_off c' + 4)) a5'
                 (Z_to_bv 64 (cur_remaining c' - 4)) (Z_to_bv 64 (P + 56))
                 (Z_to_bv 64 (P + 660)) (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 (Z.b2z (io_saw_tsoffset io))) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 660) 3 + 2147450880))
                 (Z_to_bv 64 10) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x25 (Z_to_bv 64 (Z.b2z (io_saw_tsresol io))) (Z_to_bv 64 (Z.shiftr CUR 3 + 2147450880))
                 (Z_to_bv 64 (Z.shiftr (CUR + 8) 3 + 2147450880)) (Z_to_bv 64 (io_tsoffset io)) (Z_to_bv 64 3) (Z_to_bv 64 (P + 672)))
            F (Z_to_bv 64 0x8c45c) fc None m4 (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition ai_iter__stmt : Prop := forall fuel, LOOPK fuel -> ITERK fuel.

  Section Sz8.
  Variables RNGx ra_ sp_ gp_ tp_ t0 t1 t2 s1_ a1 a2 a4 a5 a6 a7 s2_ s3_ s4_ s6_ s7_ s8_ s9_ s10_ s11_ t3 t4 t5 t6 F_ fc_ mx u0 u1 u2 u3 Bq alloc bB D : ltac2:(SecDiet.SzSec.tyM 'swap_hdrA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNGx).
  Lemma swap_hdrA__body : ltac2:(SecDiet.SzSec.bodyP 'swap_hdrA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using rc hptr sp L P B CUR EB lo idb_off p s c LO BU ALN P14 B14 LENB CURS EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 js LJS RNGx ra_ sp_ gp_ tp_ t0 t1 t2 s1_ a1 a2 a4 a5 a6 a7 s2_ s3_ s4_ s6_ s7_ s8_ s9_ s10_ s11_ t3 t4 t5 t6 F_ fc_ mx u0 u1 u2 u3 Bq alloc bB D. exact (swap_hdrA__core RNGx ra_ sp_ gp_ tp_ t0 t1 t2 s1_ a1 a2 a4 a5 a6 a7 s2_ s3_ s4_ s6_ s7_ s8_ s9_ s10_ s11_ t3 t4 t5 t6 F_ fc_ mx u0 u1 u2 u3 Bq alloc bB D). Qed.
  End Sz8.
  #[using="hptr sp L P B CUR EB lo idb_off p s c LO BU ALN P14 B14 LENB CURS EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 js LJS"] Lemma swap_hdrA : ltac:(let t := eval cbv delta [swap_hdrA__stmt] in swap_hdrA__stmt in exact t).
  Proof. intros RNGx ra_ sp_ gp_ tp_ t0 t1 t2 s1_ a1 a2 a4 a5 a6 a7 s2_ s3_ s4_ s6_ s7_ s8_ s9_ s10_ s11_ t3 t4 t5 t6 F_ fc_ mx u0 u1 u2 u3 Bq alloc bB D. ltac2:(SecDiet.SzSec.closeP 'swap_hdrA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  End AIX.
  End CANSEC1.
End F_aiEA.

(* [comment removed for export] *)
Module F_aiEA_body.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiBA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.
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
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section AIX.
  Context {H : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.CANSEC1.AIX.u0}} {hptr : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.CANSEC1.AIX.u1}} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
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
  Hypothesis BU : (lo + 16512 <= bv_unsigned sp)%Z.
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
  (* [comment removed for export] *)
  #[local] Abbreviation ai_hd := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_hd EB).
  #[local] Abbreviation sgF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.sgF hptr idb_off p sg).
  #[local] Abbreviation pF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.pF hptr idb_off p sg q1).
  #[local] Abbreviation ai_result_inl := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_result_inl hptr idb_off p s c sg q1).
  #[local] Abbreviation AIM := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.AIM H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation LREGS := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.LREGS sp gp tp P CUR).
  #[local] Abbreviation LOOPK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.LOOPK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ITERK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ITERK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_loop0 := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_loop0 H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_loop_step__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_loop_step__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_loop_step := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_loop_step rc tlsI H hptr FO GIOA fflagA GL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej LO BU SPT RSTK GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB UTS IFW IDB0 COFF CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG).
  #[local] Abbreviation loop_restf__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.loop_restf__stmt H hptr GIOA L st C1 C2 FB FL P B CUR idb_off p s c RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation loop_restf := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.loop_restf rc H hptr GIOA sp L st C1 C2 FB FL P B CUR EB lo idb_off p s c LO BU P14 B14 LENB CURS EBP EBB IDB0 COFF CREM CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 U1 U2 IC1 IC2 SZ LJS HSA OFG).
  #[local] Abbreviation loop_facts__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.loop_facts__stmt H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L st C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_disp__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_disp__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_body__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_body__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_iter__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_iter__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation swap_hdrA := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.swap_hdrA rc hptr sp L P B CUR EB lo idb_off p s c LO BU ALN P14 B14 LENB CURS EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 js LJS).

  #[local] Abbreviation pio_body := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_body.
  #[local] Abbreviation pio_value := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_value.
  #[local] Abbreviation le8val := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val.

  Section Sz7.
  Variables fuel : ltac2:(SecDiet.SzSec.tyM 'ai_body__stmt "v" @fuel).
  Lemma ai_body__gen : loop_facts__stmt -> ai_disp__stmt -> ltac2:(SecDiet.SzSec.bodyP 'ai_body__stmt "v").
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG fuel.
    intros loop_facts ai_disp LK.
 intros until m4. intros IV FUEL GE4 SW Ebuf Lpre Ebs PFXr c0 c1 l0 l1 code olen MI4 MU WM CC4 HOPT4.
    pose proof IV as IV'. destruct IV' as (TSR & MI3 & ST3 & AG3 & HD3 & FR3 & NG3 & AR1 & SL3 & AR2 & G3 & BUF3 & PFX3 & LB3 & GR3 & CC3 & CR1 & CR2 & CR3 & CR4 & HEB3 & OFF4).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as AR.
    set (padded := ((olen + 3) / 4 * 4)%Z).
    assert (LBS : length bs3 = Z.to_nat (pc_bufalloc p)) by (destruct BUF3 as [[WF _] _]; cbn in WF; lia).
    assert (OFF0 : (8 <= cur_off c')%Z) by lia.
    assert (LEN4 : (cur_off c' + cur_remaining c' <= Z.of_nat (length buf'))%Z) by lia.
    assert (Lpost : (Z.of_nat (length post) = Z.of_nat (length buf') - cur_off c' - 4)%Z) by (subst buf'; rewrite length_app in *; cbn [length] in *; lia).
    assert (GRh : (0 <= u0 < 256 /\ 0 <= u1 < 256 /\ 0 <= u2 < 256 /\ 0 <= u3 < 256)%Z /\ Forall (fun z => 0 <= z < 256)%Z pre /\ Forall (fun z => 0 <= z < 256)%Z post).
    { subst buf'. apply Forall_app in GR3 as [GA GB]. inversion GB as [|x0 l0' B0 GB1]; subst. inversion GB1 as [|x1 l1' B1x GB2]; subst.
      inversion GB2 as [|x2 l2' B2x GB3]; subst. inversion GB3 as [|x3 l3' B3 GB4]; subst. repeat split; try assumption; lia. }
    destruct GRh as ((B0 & B1x & B2x & B3) & GRpre & GRpost).
    assert (HC : (0 <= c0 < 256 /\ 0 <= c1 < 256 /\ 0 <= l0 < 256 /\ 0 <= l1 < 256)%Z) by (subst c0 c1 l0 l1; destruct sw; lia).
    destruct HC as (HC0 & HC1 & HL0 & HL1).
    assert (HCODE : (0 <= code < 65536)%Z) by (subst code; lia). assert (HOLEN : (0 <= olen < 65536)%Z) by (subst olen; lia).
    assert (HPAD : (olen <= padded <= olen + 3 /\ padded mod 4 = 0)%Z) by (subst padded; Z.div_mod_to_equations; lia).
    set (buf5 := pre ++ c0 :: c1 :: l0 :: l1 :: post) in *.
    assert (LB5 : length buf5 = length buf') by (subst buf5 buf'; rewrite !length_app; reflexivity).
    remember (B + cur_off c')%Z as D eqn:HDd.
    (* [comment removed for export] *)
    assert (G4 : GIOA L RNG3 stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB FL m4).
    { eapply (gl_client_frame _ _ _ GL); [exact G3 | exact MU | exact WM |].
      apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [| apply Forall_nil].
      right; left. unfold iv_in_block. apply Exists_cons_tl. apply Exists_exists. exists (pc_buffer p, B, pc_bufalloc p). split; [exact HinB|]. cbn [cb_addr cb_size fst snd]. lia. }
    assert (HinB4 : In (pc_buffer p, B, pc_bufalloc p) (((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) ++ FB)) by (apply in_or_app; left; right; exact HinB).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G4 HinB4) as ((BBAND & B3x & BTOP & _) & B1 & BUNP & BRNG & BRSH & BAR).
    cbn [cb_addr cb_size fst snd] in BBAND, B3x, BTOP, B1, BUNP, BRNG, BRSH.
    band_ind BBAND bB.
    pose proof (rng_fp_le _ _ _ _ FP3 RSTK) as RSTK3.
    destruct (gia_stack_sobjA FO GIOA fflagA GL _ _ _ _ _ _ _ lo (bv_unsigned sp) CUR 24 G4 LO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RSTK3) as (_ & _ & CUNP & CRNG & CRSH).
    replace (CUR - CUR mod 8)%Z with CUR in CRSH by lia. replace (24 + CUR mod 8)%Z with 24%Z in CRSH by lia.
    assert (RSPW : rng RNG3 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK3| lia]).
    assert (DM4 : (D mod 4 = 0)%Z) by (subst D; clear - B2 OFF4; Z.div_mod_to_equations; lia).
    assert (INB : (B <= D /\ D + 4 <= B + pc_bufalloc p)%Z) by lia.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_hd in HD3. unfold ai_FRAME in FR3.
    hide HD3. hide FR3. hide NG3. hide AR1. hide SL3. hide AR2. hide BUF3. hide CC3. hide HEB3.
    pose proof (munch_refl [(CUR, CUR + 16)]%Z m4) as MU45. pose proof (wmono_refl asegs m4) as WM45.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.LREGS.
    eapply evtF_cut.
    { eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.opt_lenA RNG3) with (code := code) (olen := olen) (Bq := B) (alloc := pc_bufalloc p) (bB := bB) (D := D);
        [exact HCODE | exact HOLEN | exact HOPT4 | exact MI4 | exact BUNP | lia | lia | exact DM4 | lia | exact B2 | lia | exact bBr | exact bBhi | exact bBlo | exact bBimg | exact BRNG | exact BRSH]. }
    cbv beta. intros ms' ->.
    fold padded.
    zstep.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_value, get_optvalue_from_block_data, get_from_block_data. cbn [cur_remaining cur_off cur_block_type]. fold padded.
    destruct (Z.le_gt_cases padded (cur_remaining c' - 4)) as [FIT|NOFIT].
    2:{ (* [comment removed for export] *)
      replace (bv_ltu (Z_to_bv 64 (cur_remaining c' - 4)) (Z_to_bv 64 padded)) with true by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_lt; lia). cbv beta iota.
      rewrite (proj2 (Z.ltb_lt (cur_remaining c' - 4) padded)) by lia. cbv beta iota. rewrite ai_result_inl.
      zstep. ck0 CUNP; ck_go.
      zstep.
      rewrite (sx32_s32 (cur_block_type c')) by lia.
      do 3 zstep.
      destruct (loop_facts io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m4 c0 c1 l0 l1 D _ ltac:(subst buf' bs3; exact IV) GE4 Lpre HDd PFXr HC0 HC1 HL0 HL1 MI4 MU WM ltac:(subst code olen; exact HOPT4) CC4 eq_refl)
        as (ST4 & AG4 & HD4 & FR4 & NG4 & AR14 & SL4 & AR24 & _ & BUF4 & PFX4 & LB4 & GR4 & _ & HEB4 & _ & RESTF4).
      assert (MSG : fmt_at m4 0x22520 "block of type %u in pcapng dump file is too short"%string) by (fmt_at_tac MI4 0x22520%Z "block of type %u in pcapng dump file is too short"%string).
      unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_hd in HD4.
      eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.ai_snp_b with (m3 := m4) (args := [AInt (s32 (cur_block_type c'))]) (h0 := C8 (Z_to_bv 64 3)) (h2 := C8 (Z_to_bv 64 65280)); try eassumption;
        [ reflexivity | reflexivity | reflexivity | cbn; lia
        | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil]
        | unfold Msg.block_too_short, PCAP_ERRBUF_SIZE; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.snprintf_pargs;
          replace (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.convs (fmt "block of type %u in pcapng dump file is too short")) with [Cu] by (vm_compute; reflexivity);
          apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_cons; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.aeq_s32; reflexivity| apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_nil]
        | vm_compute; reflexivity | apply args_ok_ints1 ]. }
    replace (bv_ltu (Z_to_bv 64 (cur_remaining c' - 4)) (Z_to_bv 64 padded)) with false by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_ge; lia). cbv beta iota.
    rewrite (proj2 (Z.ltb_ge (cur_remaining c' - 4) padded)) by lia. cbv beta iota.
    ck0_at CUNP CUR; ck_go.
    zstep. zstep.
    ck0_at CUNP (CUR + 8)%Z; ck_go.
    zstep. zstep.
  eapply evtF_cut.
  { eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.opt_codeA RNG3) with (code := code) (olen := olen) (Bq := B) (alloc := pc_bufalloc p) (bB := bB) (D := D);
      [exact HCODE | exact HOLEN | exact HOPT4 | exact MI4 | exact BUNP | lia | lia | exact DM4 | lia | exact B2 | lia | exact bBr | exact bBhi | exact bBlo | exact bBimg | exact BRNG | exact BRSH]. }
  cbv beta. intros ms' (s0v & ->).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end.
    (* [comment removed for export] *)
    subst bs3. subst buf'.
    destruct (loop_facts io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m5 c0 c1 l0 l1 D _ IV GE4 Lpre HDd PFXr HC0 HC1 HL0 HL1 MI4 MU WM ltac:(subst code olen; exact HOPT4) CC4 eq_refl)
      as (ST5 & AG5 & HD5 & FR5 & NG5 & AR15 & SL5 & AR25 & G5 & BUF5 & PFX5 & LB5' & GR5' & _ & HEB5 & HB2 & RESTF5).
    set (bs5 := map b8 pre ++ [b8 c0; b8 c1; b8 l0; b8 l1] ++ bsr) in *.
    set (c2 := mkCursor (cur_off c' + 4 + padded) (cur_remaining c' - 4 - padded) (cur_block_type c')).
    assert (AIM5 : forall io', (0 < io_tsresol io' < 2^64)%Z -> AIM io' c2 buf5 m5 bs5 cpad3).
    { intros io' TS'. split; [exact TS'|]. split; [exact MI4|]. split; [exact ST5|]. split; [exact AG5|]. split; [exact HD5|]. split; [exact FR5|].
      split; [exact NG5|]. split; [exact AR15|]. split; [exact SL5|]. split; [exact AR25|]. split; [exact G5|]. split; [exact BUF5|]. split; [exact PFX5|].
      split; [exact LB5'|]. split; [exact GR5'|]. split; [unfold cursor_cells; subst c2 D; cbn [cur_off cur_remaining cur_block_type]; replace (B + cur_off c' + 4 + padded)%Z with (B + (cur_off c' + 4 + padded))%Z in CC4 by lia; exact CC4|].
      subst c2; cbn [cur_off cur_remaining cur_block_type]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact CR4|]. split; [exact HEB5|]. clear - OFF4 HPAD. Z.div_mod_to_equations. lia. }
    fold c2.
    assert (LEN5 : (cur_off c' + cur_remaining c' <= Z.of_nat (length buf5))%Z) by (rewrite LB5; exact LEN4).
    eapply (ai_disp fuel LK _ _ _ io c' sw pre post c0 c1 l0 l1 bsr cpad3 m5 D AIM5 TSR SW FUEL GE4 FIT OFF0 OFF4 LEN5 HDd Lpre PFXr HC0 HC1 HL0 HL1 GRpost HB2).
  Qed.
  End Sz7.
  End AIX.
  End CANSEC1.
End F_aiEA_body.

(* [comment removed for export] *)
Module F_aiEA_disp.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiBA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.
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

(* [comment removed for export] *)
Lemma msg_ok_b : forall l : list Z, forallb (fun z => (0 <? z)%Z && (z <? 256)%Z) l = true -> Forall (fun z => 0 < z < 256)%Z l.
Proof. intros l H. apply Forall_forall. intros x Hx. rewrite forallb_forall in H. specialize (H x Hx). apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia. Qed.
Ltac msg_ok := first [ apply msg_ok_b; vm_compute; reflexivity
                     | vm_compute; repeat first [apply Forall_nil | apply Forall_cons; [split; reflexivity|]] ].
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
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (Z.sub _ (Z.mul (256)%Z (Z.div _ (128)%Z))) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- inr64 (Z.sub _ (256)%Z) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zsimp ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange_gz_g
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_gz_i
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section AIX.
  Context {H : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.CANSEC1.AIX.u0}} {hptr : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.CANSEC1.AIX.u1}} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
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
  Hypothesis BU : (lo + 16512 <= bv_unsigned sp)%Z.
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
  (* [comment removed for export] *)
  #[local] Abbreviation ai_hd := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_hd EB).
  #[local] Abbreviation sgF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.sgF hptr idb_off p sg).
  #[local] Abbreviation pF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.pF hptr idb_off p sg q1).
  #[local] Abbreviation ai_result_inl := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_result_inl hptr idb_off p s c sg q1).
  #[local] Abbreviation AIM := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.AIM H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation LREGS := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.LREGS sp gp tp P CUR).
  #[local] Abbreviation LOOPK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.LOOPK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ITERK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ITERK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_loop0 := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_loop0 H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_loop_step__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_loop_step__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_loop_step := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_loop_step rc tlsI H hptr FO GIOA fflagA GL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej LO BU SPT RSTK GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB UTS IFW IDB0 COFF CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG).
  #[local] Abbreviation loop_restf__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.loop_restf__stmt H hptr GIOA L st C1 C2 FB FL P B CUR idb_off p s c RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation loop_restf := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.loop_restf rc H hptr GIOA sp L st C1 C2 FB FL P B CUR EB lo idb_off p s c LO BU P14 B14 LENB CURS EBP EBB IDB0 COFF CREM CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 U1 U2 IC1 IC2 SZ LJS HSA OFG).
  #[local] Abbreviation loop_facts__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.loop_facts__stmt H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L st C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_disp__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_disp__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_body__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_body__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_iter__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_iter__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation swap_hdrA := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.swap_hdrA rc hptr sp L P B CUR EB lo idb_off p s c LO BU ALN P14 B14 LENB CURS EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 js LJS).

  #[local] Abbreviation pio_body := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_body.
  #[local] Abbreviation pio_value := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_value.
  #[local] Abbreviation le8val := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val.

  Section Sz6.
  Variables fuel : ltac2:(SecDiet.SzSec.tyM 'ai_disp__stmt "v" @fuel).
  Lemma ai_disp__body : ltac2:(SecDiet.SzSec.bodyP 'ai_disp__stmt "v").
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG fuel.
    intros LK.
 intros until D. intros code olen padded buf5 bs5 c2 AIM5 TSR SW FUEL GE4 FIT OFF0 OFF4 LEN4 HDd Lpre PFXr HC0 HC1 HL0 HL1 GRpost HB2.
    red in LK. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.LREGS in LK.
    assert (R2 : cur_remaining c2 = (cur_remaining c' - 4 - padded)%Z) by reflexivity.
    assert (FUEL2 : (cur_remaining c2 / 4 < Z.of_nat fuel)%Z) by (rewrite R2; clear - FUEL FIT HL0 HL1; subst padded olen; Z.div_mod_to_equations; lia).
    pose proof (AIM5 io TSR) as IV5.
    destruct IV5 as (_ & MI5 & ST5 & AG5 & HD5 & FR5 & NG5 & AR15 & SL5 & AR25 & G5 & BUF5 & PFX5 & LB5 & GR5 & CC5 & CR1 & CR2 & CR3 & CR4 & HEB5 & OFF5).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as AR.
    assert (HCODE : (0 <= code < 65536)%Z) by (subst code; lia). assert (HOLEN : (0 <= olen < 65536)%Z) by (subst olen; lia).
    assert (HPAD : (olen <= padded <= olen + 3 /\ padded mod 4 = 0)%Z) by (subst padded; Z.div_mod_to_equations; lia).
    assert (Lpost : (cur_remaining c' - 4 <= Z.of_nat (length post))%Z) by (subst buf5; rewrite length_app in LEN4; cbn [length] in LEN4; lia).
    assert (RESTF5 : AIREST_F RNG3 FL C1 C2 FB P B CUR p s (ps_outfile st) m5 stG c (pF buf5)).
    { eapply loop_restf; [exact G5 | exact NG5 | exact AR15 | exact SL5 | exact AR25 | exact BUF5 | exact PFX5 | exact LB5 | exact GR5 | exact CC5 | reflexivity]. }
    (* [comment removed for export] *)
    assert (HinB5 : In (pc_buffer p, B, pc_bufalloc p) (((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) ++ FB)) by (apply in_or_app; left; right; exact HinB).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB5) as ((BBAND & B3 & BTOP & _) & B1 & BUNP & BRNG & BRSH & BAR).
    cbn [cb_addr cb_size fst snd] in BBAND, B3, BTOP, B1, BUNP, BRNG, BRSH.
    band_ind BBAND bB.
    assert (RSPW : rng RNG3 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact (rng_fp_le _ _ _ _ FP3 RSTK)| lia]).
    assert (LBS : length bs5 = Z.to_nat (pc_bufalloc p)) by (destruct BUF5 as [[WF _] _]; cbn in WF; lia).
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_body.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_hd in HD5.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    hide FR5. hide NG5. hide AR15. hide SL5. hide AR25. hide BUF5. hide CC5. hide HEB5.
    (* [comment removed for export] *)
    zstep. zstep.
    destruct (Z.eq_dec code 9) as [E9|NE9].
    { (* [comment removed for export] *)
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ E9). cbv iota.
      replace (code =? OPT_ENDOFOPT)%Z with false by (rewrite E9; reflexivity). replace (code =? IF_TSRESOL)%Z with true by (rewrite E9; reflexivity). cbv iota.
      zstep. zstep.
      destruct (Z.eq_dec olen 1) as [L1|L1].
      2:{ (* [comment removed for export] *)
        rewrite (eqb_lits_false olen 1) by lia. cbv beta iota delta [negb]. rewrite (proj2 (Z.eqb_neq olen 1) L1). cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 3 zstep.
        assert (MSG : fmt_at m5 0x226c0 "Interface Description Block has if_tsresol option with length %u != 1"%string) by (fmt_at_tac MI5 0x226c0%Z "Interface Description Block has if_tsresol option with length %u != 1"%string).
        unhide FR5. unhide HEB5.
        eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.ai_snp_b with (m3 := m5) (args := [AInt olen]) (h0 := C8 (Z_to_bv 64 3)) (h2 := C8 (Z_to_bv 64 65280)); try eassumption;
          [ reflexivity | reflexivity | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.tsresol_len, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 ]. }
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ L1). cbn [negb]. cbv iota. rewrite (proj2 (Z.eqb_eq olen 1) L1). cbv beta iota delta [negb].
      (* [comment removed for export] *)
      zstep.
      destruct (io_saw_tsresol io) eqn:SAWR.
      { cbn [Z.b2z]. rewrite (eqb_lits_false 1 0) by lia. cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 3 zstep.
        assert (MSG : fmt_at m5 0x22740 "Interface Description Block has more than one if_tsresol option"%string) by (fmt_at_tac MI5 0x22740%Z "Interface Description Block has more than one if_tsresol option"%string).
        unhide FR5. unhide HEB5.
        eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.ai_mcp with (m3 := m5) (str := "Interface Description Block has more than one if_tsresol option"%string) (h0 := C8 (Z_to_bv 64 3)) (h2 := C8 (Z_to_bv 64 65280)); try eassumption;
          [ reflexivity | reflexivity | cbn; lia | lia | vm_compute; reflexivity | msg_ok ]. }
      cbn [Z.b2z]. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq 0 0 eq_refl). cbv beta iota delta [negb].
      (* [comment removed for export] *)
      destruct post as [|v post']; [exfalso; cbn [length] in Lpost; clear - Lpost FIT HPAD L1; lia|].
      destruct bsr as [|bv0 bsr']; [cbn in PFXr; discriminate|]. cbn [firstn length map] in PFXr. injection PFXr as Ebv0 PFXr'. subst bv0.
      pose proof (Forall_inv GRpost) as Bv. cbv beta in Bv.
      assert (GU : get_u8 buf5 (cur_off c' + 4) = v).
      { subst buf5. replace (pre ++ c0 :: c1 :: l0 :: l1 :: v :: post') with ((pre ++ [c0; c1; l0; l1]) ++ v :: post') by (rewrite <- app_assoc; reflexivity).
        replace (cur_off c' + 4)%Z with (Z.of_nat (length (pre ++ [c0; c1; l0; l1]))) by (rewrite length_app; cbn [length]; lia). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.get_u8_at. }
      rewrite GU.
      pose proof (rw_cells_recell _ _ _ [CB 1 [b8 v]; CB (length bsr') bsr'] HB2 ltac:(cbn; auto) ltac:(reflexivity)) as HV.
      destruct (rw_cells_cut _ _ _ 1 HV) as [HV1 _]. clear HV. cbn [firstn] in HV1.
      assert (INB : (B <= D + 4 /\ D + 4 + 1 <= B + pc_bufalloc p)%Z) by (cbn [length] in Lpost; lia).
      eapply evtF_cut.
      { eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.tsres_ldA RNG3) with (v := v) (Bq := B) (alloc := pc_bufalloc p) (bB := bB) (A := (D + 4)%Z);
          [exact Bv | exact HV1 | exact MI5 | exact BUNP | lia | lia | lia | exact B2 | lia | exact bBr | exact bBhi | exact bBlo | exact bBimg | exact BRNG | exact BRSH]. }
      cbv beta. intros ms' (a3x & ->).
  rewrite (sxb_lit v) by lia.
  zstep. zstep.
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.land_128 v) by lia.
      destruct (Z.lt_ge_cases v 128) as [VLO|VHI].
      + (* [comment removed for export] *)
        rewrite (Z.div_small v 128) by lia. replace (128 * 0 =? 0)%Z with true by reflexivity. cbv beta iota delta [negb]. replace (v - 256 * 0)%Z with v by lia.
        rewrite (Z.mod_small v 18446744073709551616), OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.land_255_mod, (Z.mod_small v 256) by lia.
        if_cases BRv; zify_cond BRv. { exfalso. plia_seed1 BRv. }
        zstep. zstep.
        destruct (Z.lt_ge_cases v 20) as [V20|V20].
        2:{ (* [comment removed for export] *)
          if_cases BR20; zify_cond BR20; rewrite ?unsigned_lit in BR20 by lia; [| exfalso; plia_seed1 BR20].
          rewrite (proj2 (Z.ltb_lt 19 v)) by lia. cbv iota. rewrite ai_result_inl.
          do 3 zstep.
          assert (MSG : fmt_at m5 0x22820 "Interface Description Block if_tsresol option resolution 10^-%u is too high"%string) by (fmt_at_tac MI5 0x22820%Z "Interface Description Block if_tsresol option resolution 10^-%u is too high"%string).
          unhide FR5. unhide HEB5.
          eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.ai_snp_b with (m3 := m5) (args := [AInt v]) (h0 := C8 (Z_to_bv 64 3)) (h2 := C8 (Z_to_bv 64 65280)); try eassumption;
            [ reflexivity | reflexivity | reflexivity | cbn; lia
            | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.tsresol_dec_high, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 ]. }
        if_cases BR20; zify_cond BR20; rewrite ?unsigned_lit in BR20 by lia; [exfalso; plia_seed1 BR20|].
        rewrite (proj2 (Z.ltb_ge 19 v)) by lia. cbv iota.
        assert (P19 : (0 < 10 ^ v <= 10 ^ 19)%Z) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
        change (10 ^ 19)%Z with 10000000000000000000%Z in P19.
        zstep.
        destruct (Z.eq_dec v 0) as [V0|V0].
        * (* [comment removed for export] *)
          rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ V0). cbv iota. rewrite V0. change (10 ^ 0)%Z with 1%Z.
          do 4 zstep.
          unhide FR5. unhide NG5. unhide AR15. unhide SL5. unhide AR25. unhide BUF5. unhide CC5. unhide HEB5.
          rewrite <- SW; eapply (LK _ _ _ _ _ _ _ _ (mkIdbOpts 1 (io_tsoffset io) false true (io_saw_tsoffset io)) c2 buf5 m5 bs5 cpad3); [apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
        * rewrite (eqb_lits_false v 0) by lia. cbv iota. zstep. zstep.
          eapply evtF_cut; [eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA.pow10A (Z.to_nat v - 1) v 1); lia |].
          cbv beta. intros ms' ->. rewrite Z.mul_1_l.
          do 2 zstep.
          unhide FR5. unhide NG5. unhide AR15. unhide SL5. unhide AR25. unhide BUF5. unhide CC5. unhide HEB5.
          rewrite <- SW; eapply (LK _ _ _ _ _ _ _ _ (mkIdbOpts (10 ^ v) (io_tsoffset io) false true (io_saw_tsoffset io)) c2 buf5 m5 bs5 cpad3); [apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
      + (* [comment removed for export] *)
        replace (v / 128)%Z with 1%Z by (Z.div_mod_to_equations; lia). replace (128 * 1 =? 0)%Z with false by reflexivity. cbv beta iota delta [negb].
        rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.land_127_hi v) by lia. replace (v - 256 * 1)%Z with (v - 256)%Z by lia.
        rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.land_255_mod. replace (((v - 256) mod 18446744073709551616) mod 256)%Z with v by (Z.div_mod_to_equations; lia).
        if_cases BRv; zify_cond BRv; [| exfalso; plia_seed1 BRv].
        zstep. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.land_127_hi v) by lia.
        zstep. zstep.
        destruct (Z.lt_ge_cases 63 (v - 128)) as [V63|V63].
        { (* [comment removed for export] *)
          if_cases BR63; zify_cond BR63; rewrite ?unsigned_lit in BR63 by lia; [| exfalso; plia_seed1 BR63].
          rewrite (proj2 (Z.ltb_lt 63 (v - 128))) by lia. cbv iota. rewrite ai_result_inl.
          do 2 zstep.
          assert (MSG : fmt_at m5 0x227a0 "Interface Description Block if_tsresol option resolution 2^-%u is too high"%string) by (fmt_at_tac MI5 0x227a0%Z "Interface Description Block if_tsresol option resolution 2^-%u is too high"%string).
          unhide FR5. unhide HEB5.
          eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.ai_snp_b with (m3 := m5) (args := [AInt (v - 128)]) (h0 := C8 (Z_to_bv 64 3)) (h2 := C8 (Z_to_bv 64 65280)); try eassumption;
            [ reflexivity | reflexivity | reflexivity | cbn; lia
            | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.tsresol_bin_high, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 ]. }
        if_cases BR63; zify_cond BR63; rewrite ?unsigned_lit in BR63 by lia; [exfalso; plia_seed1 BR63|].
        rewrite (proj2 (Z.ltb_ge 63 (v - 128))) by lia. cbv iota.
        assert (P63 : (0 < 2 ^ (v - 128) <= 2 ^ 63)%Z) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
        change (2 ^ 63)%Z with 9223372036854775808%Z in P63.
        zstep. zstep.
        rewrite (Z.mod_small (v - 128) 64), Z.shiftl_1_l by lia.
        zstep. zstep.
        unhide FR5. unhide NG5. unhide AR15. unhide SL5. unhide AR25. unhide BUF5. unhide CC5. unhide HEB5.
        rewrite <- SW; eapply (LK _ _ _ _ _ _ _ _ (mkIdbOpts (2 ^ (v - 128)) (io_tsoffset io) true true (io_saw_tsoffset io)) c2 buf5 m5 bs5 cpad3); [apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
    }
    (* [comment removed for export] *)
    rewrite (eqb_lits_false code 9) by lia. cbv iota.
    replace (code =? IF_TSRESOL)%Z with false by (symmetry; apply Z.eqb_neq; exact NE9).
    zstep. zstep.
    destruct (Z.eq_dec code 14) as [E14|NE14].
    { (* [comment removed for export] *)
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ E14). cbv beta iota delta [negb].
      replace (code =? OPT_ENDOFOPT)%Z with false by (rewrite E14; reflexivity). replace (code =? IF_TSOFFSET)%Z with true by (rewrite E14; reflexivity). cbv iota.
      zstep. zstep.
      destruct (Z.eq_dec olen 8) as [L8|L8].
      2:{ (* [comment removed for export] *)
        rewrite (eqb_lits_false olen 8) by lia. cbv beta iota delta [negb]. rewrite (proj2 (Z.eqb_neq olen 8) L8). cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 3 zstep.
        assert (MSG : fmt_at m5 0x228a0 "Interface Description Block has if_tsoffset option with length %u != 8"%string) by (fmt_at_tac MI5 0x228a0%Z "Interface Description Block has if_tsoffset option with length %u != 8"%string).
        unhide FR5. unhide HEB5.
        eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.ai_snp_b with (m3 := m5) (args := [AInt olen]) (h0 := C8 (Z_to_bv 64 3)) (h2 := C8 (Z_to_bv 64 65280)); try eassumption;
          [ reflexivity | reflexivity | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.tsoffset_len, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 ]. }
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ L8). cbv beta iota delta [negb]. rewrite (proj2 (Z.eqb_eq olen 8) L8). cbv beta iota delta [negb].
      (* [comment removed for export] *)
      zstep.
      destruct (io_saw_tsoffset io) eqn:SAWO.
      { cbn [Z.b2z]. rewrite (eqb_lits_false 1 0) by lia. cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 4 zstep.
        assert (MSG : fmt_at m5 0x22920 "Interface Description Block has more than one if_tsoffset option"%string) by (fmt_at_tac MI5 0x22920%Z "Interface Description Block has more than one if_tsoffset option"%string).
        unhide FR5. unhide HEB5.
        eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.ai_mcp with (m3 := m5) (str := "Interface Description Block has more than one if_tsoffset option"%string) (h0 := C8 (Z_to_bv 64 3)) (h2 := C8 (Z_to_bv 64 65280)); try eassumption;
          [ reflexivity | reflexivity | cbn; lia | lia | vm_compute; reflexivity | msg_ok ]. }
      cbn [Z.b2z]. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq 0 0 eq_refl). cbv beta iota delta [negb].
      (* [comment removed for export] *)
      destruct post as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 [|v6 [|v7 post']]]]]]]]; [ exfalso; cbn [length] in Lpost; clear - Lpost FIT HPAD L8; lia .. | ].
      destruct bsr as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 bsr']]]]]]]]; try (cbn in PFXr; discriminate).
      cbn [firstn length map] in PFXr. injection PFXr as E0 E1 E2 E3 E4 E5 E6 E7 PFXr'. subst b0 b1 b2 b3 b4 b5 b6 b7.
      assert (Bv : forall x, In x [v0; v1; v2; v3; v4; v5; v6; v7] -> (0 <= x < 256)%Z).
      { intros x Hx. apply (proj1 (Forall_forall _ _) GRpost). cbn in Hx |- *. clear - Hx. tauto. }
      pose proof (Bv v0 ltac:(cbn; clear; tauto)) as Bv0. pose proof (Bv v1 ltac:(cbn; clear; tauto)) as Bv1. pose proof (Bv v2 ltac:(cbn; clear; tauto)) as Bv2. pose proof (Bv v3 ltac:(cbn; clear; tauto)) as Bv3.
      pose proof (Bv v4 ltac:(cbn; clear; tauto)) as Bv4. pose proof (Bv v5 ltac:(cbn; clear; tauto)) as Bv5. pose proof (Bv v6 ltac:(cbn; clear; tauto)) as Bv6. pose proof (Bv v7 ltac:(cbn; clear; tauto)) as Bv7. clear Bv.
      assert (GU : get_le64 buf5 (cur_off c' + 4) = le8val v0 v1 v2 v3 v4 v5 v6 v7).
      { subst buf5. replace (pre ++ c0 :: c1 :: l0 :: l1 :: v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: post') with ((pre ++ [c0; c1; l0; l1]) ++ v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: post') by (rewrite <- app_assoc; reflexivity).
        replace (cur_off c' + 4)%Z with (Z.of_nat (length (pre ++ [c0; c1; l0; l1]))) by (rewrite length_app; cbn [length]; lia). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.get_le64_at. }
      rewrite GU.
      pose proof (rw_cells_recell _ _ _ [CB 8 (map b8 [v0; v1; v2; v3; v4; v5; v6; v7]); CB (length bsr') bsr'] HB2 ltac:(cbn; auto) ltac:(reflexivity)) as HV.
      destruct (rw_cells_cut _ _ _ 1 HV) as [HV8 _]. clear HV. cbn [firstn] in HV8.
      assert (INB : (B <= D + 4 /\ D + 4 + 8 <= B + pc_bufalloc p)%Z) by (cbn [length] in Lpost; lia).
      eapply evtF_cut.
      { eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.ldu64ckA RNG3) with (A := (D + 4)%Z) (u0 := v0) (u1 := v1) (u2 := v2) (u3 := v3) (u4 := v4) (u5 := v5) (u6 := v6) (u7 := v7) (Bq := B) (alloc := pc_bufalloc p) (bB := bB);
          [exact Bv0 | exact Bv1 | exact Bv2 | exact Bv3 | exact Bv4 | exact Bv5 | exact Bv6 | exact Bv7 | exact HV8 | exact MI5 | exact BUNP | lia | lia | lia | exact B2 | lia
          | exact bBr | exact bBhi | exact bBlo | exact bBimg | exact BRNG | exact BRSH]. }
      cbv beta. intros ms' (a0x & a3x & a4x & a5x & s0x & ->).
      (* [comment removed for export] *)
      zstep.
      destruct sw.
      + cbn [Z.b2z]. rewrite (eqb_lits_false 1 0) by lia. cbv beta iota delta [negb].
        destruct (rw_cells_cut _ _ _ 2 HD5) as [_ HD16]. cbn [firstn skipn cells_size csize Nat.add] in HD16.
        replace (bv_unsigned sp + -128 + Z.of_nat 16)%Z with (bv_unsigned sp + -128 + 16)%Z in HD16 by lia.
        eapply evtF_cut.
        { eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA.bswap64A with (SPF := (bv_unsigned sp + -128)%Z) (u0 := v0) (u1 := v1) (u2 := v2) (u3 := v3) (u4 := v4) (u5 := v5) (u6 := v6) (u7 := v7);
            [exact MI5 | reflexivity | lia | lia | eapply rng_sub'; [exact RSPW | lia] | exact HD16 | exact Bv0 | exact Bv1 | exact Bv2 | exact Bv3 | exact Bv4 | exact Bv5 | exact Bv6 | exact Bv7]. }
        cbv beta. intros ms' (a0y & a3y & a4y & a5y & s0y & s3y & ->).
        rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.bswap64_bytes v0 v1 v2 v3 v4 v5 v6 v7) by lia. rewrite <- (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.Z_to_bv64_s64 (le8val v7 v6 v5 v4 v3 v2 v1 v0)).
        replace (process_idb_options_loop fuel true) with (process_idb_options_loop fuel (pc_swapped p)) by (rewrite SW; reflexivity).
        unhide FR5. unhide NG5. unhide AR15. unhide SL5. unhide AR25. unhide BUF5. unhide CC5. unhide HEB5.
        eapply (LK _ _ _ _ _ _ _ _ (mkIdbOpts (io_tsresol io) (s64 (le8val v7 v6 v5 v4 v3 v2 v1 v0)) (io_is_binary io) (io_saw_tsresol io) true) c2 buf5 m5 bs5 cpad3); [apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
      + cbn [Z.b2z]. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq 0 0 eq_refl). cbv beta iota delta [negb].
        rewrite <- (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.Z_to_bv64_s64 (le8val v0 v1 v2 v3 v4 v5 v6 v7)).
        replace (process_idb_options_loop fuel false) with (process_idb_options_loop fuel (pc_swapped p)) by (rewrite SW; reflexivity).
        unhide FR5. unhide NG5. unhide AR15. unhide SL5. unhide AR25. unhide BUF5. unhide CC5. unhide HEB5.
        eapply (LK _ _ _ _ _ _ _ _ (mkIdbOpts (io_tsresol io) (s64 (le8val v0 v1 v2 v3 v4 v5 v6 v7)) (io_is_binary io) (io_saw_tsresol io) true) c2 buf5 m5 bs5 cpad3); [apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
    }
    (* [comment removed for export] *)
    rewrite (eqb_lits_false code 14) by lia. cbv beta iota delta [negb].
    replace (code =? IF_TSOFFSET)%Z with false by (symmetry; apply Z.eqb_neq; exact NE14).
    zstep.
    destruct (Z.eq_dec code 0) as [E0|NE0].
    + rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ E0). cbv iota. replace (code =? OPT_ENDOFOPT)%Z with true by (rewrite E0; reflexivity). cbv iota.
      (* [comment removed for export] *)
      zstep.
      destruct (Z.eq_dec olen 0) as [L0|L0].
      * rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ L0). cbv iota. rewrite (proj2 (Z.eqb_eq olen 0) L0). cbv beta iota delta [negb].
        unhide FR5. unhide NG5. unhide AR15. unhide SL5. unhide AR25. unhide BUF5. unhide CC5. unhide HEB5.
        eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiBA.ai_tail with (hd := ai_hd) (SA := SA) (js := js) (c' := c2) (opts := io); eassumption || (try exact IC1; try exact HSA; try reflexivity; try lia).
      * rewrite (eqb_lits_false olen 0) by lia. cbv iota. rewrite (proj2 (Z.eqb_neq olen 0) L0). cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 3 zstep.
        assert (MSG : fmt_at m5 0x22640 "Interface Description Block has opt_endofopt option with length %u != 0"%string) by (fmt_at_tac MI5 0x22640%Z "Interface Description Block has opt_endofopt option with length %u != 0"%string).
        unhide FR5. unhide HEB5.
        eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.ai_snp_b with (m3 := m5) (args := [AInt olen]) (h0 := C8 (Z_to_bv 64 3)) (h2 := C8 (Z_to_bv 64 65280)); try eassumption;
          [ reflexivity | reflexivity | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.endofopt_len, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 ].
    + (* [comment removed for export] *)
      rewrite (eqb_lits_false code 0) by lia. cbv iota. replace (code =? OPT_ENDOFOPT)%Z with false by (symmetry; apply Z.eqb_neq; exact NE0). cbv iota.
      replace (process_idb_options_loop fuel sw) with (process_idb_options_loop fuel (pc_swapped p)) by (rewrite SW; reflexivity).
      unhide FR5. unhide NG5. unhide AR15. unhide SL5. unhide AR25. unhide BUF5. unhide CC5. unhide HEB5.
      eapply (LK _ _ _ _ _ _ _ _ io c2 buf5 m5 bs5 cpad3); [apply AIM5; exact TSR | exact FUEL2].
  Qed.
  End Sz6.
  #[using="rc tlsI FO fflagA GL SNPRINTF I i G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG"] Lemma ai_disp : ltac:(let t := eval hnf in ai_disp__stmt in exact t).
  Proof. intros fuel. ltac2:(SecDiet.SzSec.closeP 'ai_disp__body "v"). Qed.
  End AIX.
  End CANSEC1.
End F_aiEA_disp.

(* [comment removed for export] *)
Module F_aiEA_facts.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiBA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.
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
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section AIX.
  Context {H : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.CANSEC1.AIX.u0}} {hptr : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.CANSEC1.AIX.u1}} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
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
  Hypothesis BU : (lo + 16512 <= bv_unsigned sp)%Z.
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
  (* [comment removed for export] *)
  #[local] Abbreviation ai_hd := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_hd EB).
  #[local] Abbreviation sgF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.sgF hptr idb_off p sg).
  #[local] Abbreviation pF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.pF hptr idb_off p sg q1).
  #[local] Abbreviation ai_result_inl := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_result_inl hptr idb_off p s c sg q1).
  #[local] Abbreviation AIM := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.AIM H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation LREGS := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.LREGS sp gp tp P CUR).
  #[local] Abbreviation LOOPK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.LOOPK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ITERK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ITERK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_loop0 := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_loop0 H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_loop_step__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_loop_step__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_loop_step := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_loop_step rc tlsI H hptr FO GIOA fflagA GL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej LO BU SPT RSTK GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB UTS IFW IDB0 COFF CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG).
  #[local] Abbreviation loop_restf__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.loop_restf__stmt H hptr GIOA L st C1 C2 FB FL P B CUR idb_off p s c RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation loop_restf := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.loop_restf rc H hptr GIOA sp L st C1 C2 FB FL P B CUR EB lo idb_off p s c LO BU P14 B14 LENB CURS EBP EBB IDB0 COFF CREM CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 U1 U2 IC1 IC2 SZ LJS HSA OFG).
  #[local] Abbreviation loop_facts__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.loop_facts__stmt H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L st C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_disp__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_disp__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_body__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_body__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_iter__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_iter__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation swap_hdrA := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.swap_hdrA rc hptr sp L P B CUR EB lo idb_off p s c LO BU ALN P14 B14 LENB CURS EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 js LJS).

  Section Sz5.
  Variables io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m5 c0 c1 l0 l1 D ccs : ltac2:(SecDiet.SzSec.tyM 'loop_facts__stmt "vvvvvvvvvvvvvvvvvv" @io).
  Lemma loop_facts__body : ltac2:(SecDiet.SzSec.bodyP 'loop_facts__stmt "vvvvvvvvvvvvvvvvvv").
  Proof using rc tlsI H hptr FO GIOA fflagA GL ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L st C1 C2 FB FL P B CUR EB lo idb_off p s c ej LO BU GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 U1 U2 IC1 IC2 SZ LJS HSA OFG io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m5 c0 c1 l0 l1 D ccs.
 intros IV GE4 Lpre HDd PFXr HC0 HC1 HL0 HL1 MI5 MU WM HOPT5 CC5 Hccs buf5 bs5.
    destruct IV as (TSR & MI3 & ST3 & AG3 & HD3 & FR3 & NG3 & AR1 & SL3 & AR2 & G3 & BUF3 & PFX3 & LB3 & GR3 & CC3 & CR1 & CR2 & CR3 & CR4 & HEB3 & OFF4).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as AR.
    assert (LBS : (length pre + (4 + length bsr))%nat = Z.to_nat (pc_bufalloc p)).
    { destruct BUF3 as [[WF _] _]. cbn [cells_wf cell_wf] in WF. rewrite !length_app, !length_map in WF. cbn [length] in WF. lia. }
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiBA.ai_head FO GIOA fflagA GL sp L C1 C2 FB FL P B EB lo p LO BU GPL HinP HinB EBL _ _ _ _ _ _ G3 ltac:(lia)) as ((Q1 & Q4 & Q2) & _ & _ & _ & _ & API & APIB & APIE).
    assert (LEN4 : (cur_off c' + cur_remaining c' <= Z.of_nat (length (pre ++ u0 :: u1 :: u2 :: u3 :: post)))%Z) by lia.
    rewrite length_app in LEN4. cbn [length] in LEN4.
    apply Forall_app in GR3 as [GRpre GB].
    pose proof (Forall_inv GB) as B0. pose proof (Forall_inv (Forall_inv_tail GB)) as B1. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail GB))) as B2x.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail GB)))) as B3. pose proof (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail GB)))) as GRpost.
    cbv beta in B0, B1, B2x, B3. clear GB.
    pose proof (rw_cells_bound _ _ _ _ AR1) as BA1. rewrite ifs_cells_size in BA1 by (rewrite length_rev; lia). rewrite length_rev in BA1.
    assert (AGS35 : agrees_on (fun a => outside [(CUR, CUR + 16); (D, D + 4)]%Z a) m3 m5) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    unfold ai_FRAME in FR3. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_hd in *.
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
    assert (ST5 : stk asegs m5 lo (bv_unsigned sp + -128)) by (eapply agrees_stk; [exact AGS35 | exact ST3 | intros a Ha; cbn [outside fst snd]; lia]).
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
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiBA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.
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
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section AIX.
  Context {H : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.CANSEC1.AIX.u0}} {hptr : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.CANSEC1.AIX.u1}} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
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
  Hypothesis BU : (lo + 16512 <= bv_unsigned sp)%Z.
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
  (* [comment removed for export] *)
  #[local] Abbreviation ai_hd := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_hd EB).
  #[local] Abbreviation sgF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.sgF hptr idb_off p sg).
  #[local] Abbreviation pF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.pF hptr idb_off p sg q1).
  #[local] Abbreviation ai_result_inl := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_result_inl hptr idb_off p s c sg q1).
  #[local] Abbreviation AIM := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.AIM H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation LREGS := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.LREGS sp gp tp P CUR).
  #[local] Abbreviation LOOPK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.LOOPK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ITERK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ITERK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_loop0 := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_loop0 H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_loop_step__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_loop_step__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_loop_step := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_loop_step rc tlsI H hptr FO GIOA fflagA GL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej LO BU SPT RSTK GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB UTS IFW IDB0 COFF CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG).
  #[local] Abbreviation loop_restf__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.loop_restf__stmt H hptr GIOA L st C1 C2 FB FL P B CUR idb_off p s c RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation loop_restf := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.loop_restf rc H hptr GIOA sp L st C1 C2 FB FL P B CUR EB lo idb_off p s c LO BU P14 B14 LENB CURS EBP EBB IDB0 COFF CREM CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 U1 U2 IC1 IC2 SZ LJS HSA OFG).
  #[local] Abbreviation loop_facts__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.loop_facts__stmt H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L st C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_disp__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_disp__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_body__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_body__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_iter__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_iter__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation swap_hdrA := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.swap_hdrA rc hptr sp L P B CUR EB lo idb_off p s c LO BU ALN P14 B14 LENB CURS EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 js LJS).

  #[local] Abbreviation pio_body := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_body.
  #[local] Abbreviation pio_value := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_value.
  #[local] Abbreviation le8val := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val.

  Section Sz9.
  Variables fuel : ltac2:(SecDiet.SzSec.tyM 'ai_iter__stmt "v" @fuel).
  Lemma ai_iter__gen : ai_body__stmt -> ltac2:(SecDiet.SzSec.bodyP 'ai_iter__stmt "v").
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 HPV RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG fuel.
    intros ai_body LK.
 red. intros until cpad3. intros IV FUEL RPOS.
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
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_hd in HD3. unfold ai_FRAME in FR3.
    hide HD3. hide FR3. hide NG3. hide AR1. hide SL3. hide AR2. hide BUF3. hide HEB3. hide HPV3.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU0. pose proof (wmono_refl asegs m3) as WM0.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.LREGS. zstep.
  destruct (Z.lt_ge_cases (cur_remaining c') 4) as [LT4|GE4].
  { (* [comment removed for export] *)
    replace (bv_ltu (Z_to_bv 64 3) (Z_to_bv 64 (cur_remaining c'))) with false by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [negb].
    rewrite (proj2 (Z.ltb_lt (cur_remaining c') 4) LT4). rewrite ai_result_inl.
    zstep. ck0 CUNP; ck_go.
    zstep.
    rewrite (sx32_s32 (cur_block_type c')) by lia.
    do 3 zstep.
    unhide HD3. unhide FR3. unhide NG3. unhide AR1. unhide SL3. unhide AR2. unhide BUF3. unhide HEB3.
    assert (MSG : fmt_at m3 0x22520 "block of type %u in pcapng dump file is too short"%string) by (fmt_at_tac MI3 0x22520%Z "block of type %u in pcapng dump file is too short"%string).
    eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.ai_snp_b with (m3 := m3) (args := [AInt (s32 (cur_block_type c'))]) (h0 := C8 (Z_to_bv 64 3)) (h2 := C8 (Z_to_bv 64 65280)); try eassumption;
      [ reflexivity | reflexivity | reflexivity | cbn; lia
      | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil]
      | unfold Msg.block_too_short, PCAP_ERRBUF_SIZE; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.snprintf_pargs;
        replace (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.convs (fmt "block of type %u in pcapng dump file is too short")) with [Cu] by (vm_compute; reflexivity);
        apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_cons; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.aeq_s32; reflexivity| apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_nil]
      | vm_compute; reflexivity | apply args_ok_ints1
      | eapply loop_restf; [exact G3 | exact NG3 | exact AR1 | exact SL3 | exact AR2 | exact BUF3 | exact PFX3 | exact LB3 | exact GR3 | exact CC3 | reflexivity] ]. }
  (* [comment removed for export] *)
  replace (bv_ltu (Z_to_bv 64 3) (Z_to_bv 64 (cur_remaining c'))) with true by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [negb].
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
  zstep.
  ck0_at CUNP (CUR + 8)%Z; ck_go.
  zstep. replace (cur_remaining c' + -4)%Z with (cur_remaining c' - 4)%Z by lia.
  zstep.
  zstep. rewrite (eqb_lits_false D 0) by lia. cbv iota.
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
    hide CC3.
    eapply evtF_cut.
    { eapply (swap_hdrA RNG3) with (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3) (Bq := B) (alloc := pc_bufalloc p) (bB := bB);
        [exact B0 | exact B1x | exact B2x | exact B3 | exact HOPT | exact MI3 | exact BUNP | lia | lia | exact DM4 | lia | exact B2 | lia
        | exact bBr | exact bBhi | exact bBlo | exact bBimg | exact BRNG | exact BRSH]. }
    cbv beta. intros ms' (rav & a5v & s9v & m4 & -> & MU4 & WM4 & MI4 & HOPT4 & BUNP4).
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
Module F_aiEA_loop.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiBA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.
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


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section AIX.
  Context {H : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.CANSEC1.AIX.u0}} {hptr : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.CANSEC1.AIX.u1}} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
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
  Hypothesis BU : (lo + 16512 <= bv_unsigned sp)%Z.
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
  (* [comment removed for export] *)
  #[local] Abbreviation ai_hd := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_hd EB).
  #[local] Abbreviation sgF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.sgF hptr idb_off p sg).
  #[local] Abbreviation pF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.pF hptr idb_off p sg q1).
  #[local] Abbreviation ai_result_inl := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_result_inl hptr idb_off p s c sg q1).
  #[local] Abbreviation AIM := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.AIM H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation LREGS := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.LREGS sp gp tp P CUR).
  #[local] Abbreviation LOOPK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.LOOPK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ITERK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ITERK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_loop0 := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_loop0 H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_loop_step__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_loop_step__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_loop_step := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_loop_step rc tlsI H hptr FO GIOA fflagA GL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej LO BU SPT RSTK GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB UTS IFW IDB0 COFF CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG).
  #[local] Abbreviation loop_restf__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.loop_restf__stmt H hptr GIOA L st C1 C2 FB FL P B CUR idb_off p s c RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation loop_restf := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.loop_restf rc H hptr GIOA sp L st C1 C2 FB FL P B CUR EB lo idb_off p s c LO BU P14 B14 LENB CURS EBP EBB IDB0 COFF CREM CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 U1 U2 IC1 IC2 SZ LJS HSA OFG).
  #[local] Abbreviation loop_facts__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.loop_facts__stmt H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L st C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_disp__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_disp__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_body__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_body__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation ai_iter__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.ai_iter__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation swap_hdrA := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA.swap_hdrA rc hptr sp L P B CUR EB lo idb_off p s c LO BU ALN P14 B14 LENB CURS EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 js LJS).

  Section Sz7.
  Variables fuel : ltac2:(SecDiet.SzSec.tyM 'ai_body__stmt "v" @fuel).
  Lemma ai_body__body : ltac2:(SecDiet.SzSec.bodyP 'ai_body__stmt "v").
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG fuel. exact (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA_body.ai_body__gen rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG fuel (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA_facts.loop_facts rc tlsI H hptr FO GIOA fflagA GL ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L st C1 C2 FB FL P B CUR EB lo idb_off p s c ej LO BU GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 U1 U2 IC1 IC2 SZ LJS HSA OFG) (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA_disp.ai_disp rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG)). Qed.
  End Sz7.
  #[using="rc tlsI FO fflagA GL SNPRINTF I i G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG"] Lemma ai_body : ltac:(let t := eval hnf in ai_body__stmt in exact t).
  Proof. intros fuel. ltac2:(SecDiet.SzSec.closeP 'ai_body__body "v"). Qed.

  Section Sz9.
  Variables fuel : ltac2:(SecDiet.SzSec.tyM 'ai_iter__stmt "v" @fuel).
  Lemma ai_iter__body : ltac2:(SecDiet.SzSec.bodyP 'ai_iter__stmt "v").
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 HPV RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG fuel. exact (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA_iter.ai_iter__gen rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 HPV RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG fuel ai_body). Qed.
  End Sz9.
  #[using="rc tlsI FO fflagA GL SNPRINTF I i G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 HPV FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG"] Lemma ai_iter : ltac:(let t := eval hnf in ai_iter__stmt in exact t).
  Proof. intros fuel. ltac2:(SecDiet.SzSec.closeP 'ai_iter__body "v"). Qed.

  (* [comment removed for export] *)
  Theorem ai_loop : forall fuel, LOOPK fuel.
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 HPV RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG. induction fuel as [|fuel IH]; [apply ai_loop0 | apply ai_loop_step, ai_iter, IH]. Qed.
  End AIX.
  End CANSEC1.
End F_aiEA_loop.
