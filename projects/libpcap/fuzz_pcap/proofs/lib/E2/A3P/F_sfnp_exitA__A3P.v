(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P.
From Stdlib Require String.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_iface_ppA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_sfnp_exitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
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

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NpExit.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.

  Definition np_exit__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 : word)
      (scs : list cell) (st : Z) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA scs -> cells_size scs = 120%nat ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (st = 1 \/ st = 0 \/ st = -1)%Z ->
    (st = 1%Z -> hcs' = hdr_cells h /\ (0 <= h_caplen h < 2^32)%Z /\ (0 <= h_len h < 2^32)%Z) ->
    implMG RNGx (fo_ret FO _ FF_NEXT_PACKET (st, h, p')) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp r9 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 st) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r20 (Z_to_bv 64 Fb) r22 r23 r24 (Z_to_bv 64 Fb) r26 r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88aec) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 scs st h p' hcs' dw : ltac2:(SecDiet.SzSec.tyM 'np_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_exit__body : ltac2:(SecDiet.SzSec.bodyP 'np_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7.
    intros CTX INV PC FRA Hscs HH Hh HD Hd STC ST1.
    destruct CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & OHA & ODA & DHD & HA8 & DA8 & SPAB & SPA32).
    destruct INV as (FP & G & OF & MI & ST & STG & FR & AG & (k0 & k1 & k2 & fj & FRC) & SHC & SHD).
    unfold PCAP_L2_STACK in BU. unfold np_shadow in SHC.
    destruct (rw_cells_forget _ _ _ _ FRA) as [jS FRA']. rewrite Hscs in FRA'. clear FRA.
    destruct (rw_cells_cut _ _ _ 1 FRC) as [FRC0 FRC1]. clear FRC. cbn [firstn skipn cells_size csize Nat.add] in FRC0, FRC1.
    destruct (rw_cells_cut _ _ _ 3 FRC1) as [_ FRL]. clear FRC1. cbn [firstn skipn cells_size csize Nat.add] in FRL.
    lazymatch type of FRL with rw_cells _ _ ?A _ => replace A with (Fb + 8184)%Z in FRL by lia end.
    apply (rng_fp_le _ _ _ _ FP) in RSTK. apply (rng_fp_le _ _ _ _ FP) in RIMG. apply (rng_fp_le _ _ _ _ FP) in RISH. apply (rng_fp_le _ _ _ _ FP) in RTLS.
    eapply implMG_mono.
    { eapply (np_epi FO GIOA fflagA GL FFREE7 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNGx sx CL PB FB FL lo SPA Fb mm);
        [exact SPAB| exact SPA32| exact LO| unfold FAKE_STACK; lia| exact SPT| exact TOP47| exact TPE| exact G| exact MI| exact ST| exact STG| exact FRA'| exact FR
        | exact FRC0| exact FRL| exact SHC| exact RSTK| exact RIMG| exact RISH| exact RTLS]. }
    intros r' s3' RNG3 ms3 (-> & -> & PO). destruct_exs PO. destruct PO as (-> & MI7 & ST7 & AG7 & AGP7 & G7 & OF7).
    unfold next_packet_post. split; [exact FP|].
    lazymatch goal with |- context [MS _ _ _ _ _ ?m7 _] => exists (Z_to_bv 64 st), m7, PB, dw end.
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [congruence|]. split; [exact MI7|]. split; [exact ST7|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG|]; intros a (K & N1 & N2); split; [exact K|]; cbn [outside fst snd]; lia|].
             eapply agrees_on_weaken; [exact AG7|]. intros a (K & _); exact K. }
    split; [exact G7|].
    assert (PC7 : PCAPR (hptr:=hptr) P p' PB FB x13).
    { eapply PCAPR_agree; [exact AGP7| intros a Ha; apply in_block_app; right; exact Ha| exact PC]. }
    split; [intros _; exact PC7|]. split; [intros _; apply PCAPR_closable_of; exact PC7|].
    split; [reflexivity|]. split; [exact STC|].
    assert (KHA : forall cs, rw_cells asegs mm HA cs -> cells_size cs = 24%nat -> rw_cells asegs x13 HA cs).
    { intros cs HC HS. eapply agrees_rw_cells; [exact AG7| exact HC|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OHA)| rewrite HS in Ha; lia]. }
    split. { intros E1. destruct (ST1 E1) as (EH & C1 & C2). subst hcs'. split; [apply KHA; [exact HH| reflexivity]|]. split; assumption. }
    split. { intros _. exists hcs'. split; [exact Hh| apply KHA; [exact HH| exact Hh]]. }
    split; [| exact Hd].
    eapply agrees_rw_cells; [exact AG7| exact HD|]. intros a Ha. eapply clocA_keeps; [exact (proj1 ODA)| cbn [cells_size] in Ha; rewrite Hd in Ha; lia].
  Qed.
  End Sz1.
  Lemma np_exit : ltac:(let t := eval cbv delta [np_exit__stmt] in np_exit__stmt in exact t).
  Proof using GL FFREE7. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 scs st h p' hcs' dw. ltac2:(SecDiet.SzSec.closeP 'np_exit__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_exit_m1__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 : word)
      (scs : list cell) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA scs -> cells_size scs = 120%nat ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    implMG RNGx (fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, h, p')) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp r9 a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r20 (Z_to_bv 64 Fb) r22 r23 r24 (Z_to_bv 64 Fb) r26 r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88ae8) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 scs h p' hcs' dw : ltac2:(SecDiet.SzSec.tyM 'np_exit_m1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_exit_m1__body : ltac2:(SecDiet.SzSec.bodyP 'np_exit_m1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7.
    intros CTX INV PC FRA Hscs HH Hh HD Hd.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep.
    apply evtF_done. subst POSTQ.
    eapply np_exit with (st := (-1)%Z); [exact CTX| exact INV| exact PC| exact FRA| exact Hscs| exact HH| exact Hh| exact HD| exact Hd| lia| intros X; discriminate X].
  Qed.
  End Sz2.
  Lemma np_exit_m1 : ltac:(let t := eval cbv delta [np_exit_m1__stmt] in np_exit_m1__stmt in exact t).
  Proof using GL FFREE7. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 scs h p' hcs' dw. ltac2:(SecDiet.SzSec.closeP 'np_exit_m1__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_exit_n__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r21 r22 r24 r26 r27 t3 t4 t5 t6 : word)
      (scs : list cell) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA scs -> cells_size scs = 120%nat ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    implMG RNGx (fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, h, p')) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp r9 a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r20 r21 r22 (Z_to_bv 64 Fb) r24 (Z_to_bv 64 Fb) r26 r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88a5c) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r21 r22 r24 r26 r27 t3 t4 t5 t6 scs h p' hcs' dw : ltac2:(SecDiet.SzSec.tyM 'np_exit_n__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_exit_n__body : ltac2:(SecDiet.SzSec.bodyP 'np_exit_n__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7.
    intros CTX INV PC FRA Hscs HH Hh HD Hd.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    do 3 zstep.
    apply evtF_done. subst POSTQ.
    eapply np_exit with (st := (-1)%Z); [exact CTX| exact INV| exact PC| exact FRA| exact Hscs| exact HH| exact Hh| exact HD| exact Hd| lia| intros X; discriminate X].
  Qed.
  End Sz3.
  Lemma np_exit_n : ltac:(let t := eval cbv delta [np_exit_n__stmt] in np_exit_n__stmt in exact t).
  Proof using GL FFREE7. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r21 r22 r24 r26 r27 t3 t4 t5 t6 scs h p' hcs' dw. ltac2:(SecDiet.SzSec.closeP 'np_exit_n__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpExit.

Section NpExitSh.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.

  (* [comment removed for export] *)
  Definition np_exit_sh__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 : word) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9;
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 c11; C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    implMG RNGx (fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, h, p')) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r20 (Z_to_bv 64 Fb) r22 r23 r24 (Z_to_bv 64 Fb) r26 r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88adc) fc None mm (seg_rom asegs)).
  Section Sz4.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 h p' hcs' dw : ltac2:(SecDiet.SzSec.tyM 'np_exit_sh__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_exit_sh__body : ltac2:(SecDiet.SzSec.bodyP 'np_exit_sh__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8.
    intros CTX INV PC FRA HH Hh HD Hd.
    np_setup GL CTX INV.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HH']. rewrite Hh in HH'. clear HH.
    destruct (rw_cells_forget _ _ _ _ HD) as [dj HD']. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'. clear HD.
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z mm) as MU.
    pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    do 2 zstep.
    zstep.
    (* [comment removed for export] *)
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (SETF8 _ spa) with (lo := lo) (SA := (Z.shiftr Fb 3 + 2147450892)%Z) (n := 512%Z) (old := dsh);
        [ assumption | rewrite Hspa; exact ST | rewrite Hspa; unfold FAKE_STACK; lia | lia
        | exact (proj1 (gl_rt _ _ _ GL _ _ _ _ _ _ _ G)) | exact (gl_got_memset _ _ _ GL _ _ _ _ _ _ _ G)
        | reflexivity | reflexivity | lia | lia | exact SHD
        | eapply rng_sub'; [exact FSRNG| lia] | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] | exact RIMG ]
      | ].
    cbv beta. intros ms' PO. destruct PO as (a0v & m2 & E & MUc & WMc & MIc & STc & SHD2).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. unfold FAKE_STACK in MUc.
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end.
    replace (ret_pc (Z_to_bv 64 559848)) with (Z_to_bv 64 559848) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(SPA - 4096, SPA); (Z.shiftr Fb 3 + 2147450892, Z.shiftr Fb 3 + 2147450892 + 512)]%Z) by own_ivs.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ m2 _ [] _ (Forall_impl _ (own_ivA_PB _ PB _) FW) (Forall_nil _) G MUc WMc ltac:(lia)) as [G2 AG2].
    assert (PC2 : PCAPR (hptr:=hptr) P p' PB FB m2).
    { eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MUc| exact WMc|]; intros a _ Ha; exact Ha| | exact PC].
      intros a Ha. exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ PB) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a (proj2 (in_block_app _ _ _) (or_intror Ha))). }
    subst spa.
    apply evtF_done. subst POSTQ.
    eapply (np_exit_m1 FO GIOA TP fflagA GL FFREE7) with (PB := PB) (dsh := repeat (Z_to_bv 8 248) (Z.to_nat 512)) (hcs' := [CB 24 hj]) (dw := CB 8 dj);
      [ exact CTX | | exact PC2 | eassumption | reflexivity | eassumption | reflexivity | eassumption | reflexivity ].
    unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G2|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|].
    split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG2|]. intros a (K & _). split; [exact K| exact I]. }
    split; [exists k0, k1, k2, fj; assumption|]. split; [assumption|]. exact SHD2.
  Qed.
  End Sz4.
  Lemma np_exit_sh : ltac:(let t := eval cbv delta [np_exit_sh__stmt] in np_exit_sh__stmt in exact t).
  Proof using GL FFREE7 SETF8. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 h p' hcs' dw. ltac2:(SecDiet.SzSec.closeP 'np_exit_sh__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_ret_ok (pc : Z) (r21 r23 : word) (Fb : Z) : Prop :=
    ((pc = 0x88498 \/ pc = 0x884bc \/ pc = 0x8881c \/ pc = 0x88aa8 \/ pc = 0x88adc)%Z /\ r21 = Z_to_bv 64 Fb)
    \/ ((pc = 0x889e8 \/ pc = 0x88a5c)%Z /\ r23 = Z_to_bv 64 Fb).
  #[using="Type"] Lemma np_ret_pc : forall pc r21 r23 Fb, np_ret_ok pc r21 r23 Fb -> ret_pc (Z_to_bv 64 pc) = Z_to_bv 64 pc.
  Proof. intros pc r21 r23 Fb [[X _]|[X _]]; apply ret_pc_even; lia. Qed.

  Definition np_fail_ret__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 : word) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell) (pc : Z),
    np_ret_ok pc r21 r23 Fb ->
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9;
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 c11; C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    implMG RNGx (fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, h, p')) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r20 r21 r22 r23 r24 (Z_to_bv 64 Fb) r26 r27 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Section Sz6.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 h p' hcs' dw pc : ltac2:(SecDiet.SzSec.tyM 'np_fail_ret__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_fail_ret__body : ltac2:(SecDiet.SzSec.bodyP 'np_fail_ret__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8.
    intros ROK CTX INV PC FRA HH Hh HD Hd.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    destruct ROK as [[[-> |[-> |[-> |[-> | ->]]]] ->]|[[-> | ->] ->]].
    - lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF. zstep. apply evtF_done. subst POSTQ.
      eapply (np_exit_m1 FO GIOA TP fflagA GL FFREE7); [exact CTX| exact INV| exact PC| exact FRA| reflexivity| exact HH| exact Hh| exact HD| exact Hd].
    - lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF. zstep. apply evtF_done. subst POSTQ.
      eapply (np_exit_m1 FO GIOA TP fflagA GL FFREE7); [exact CTX| exact INV| exact PC| exact FRA| reflexivity| exact HH| exact Hh| exact HD| exact Hd].
    - lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF. zstep. apply evtF_done. subst POSTQ.
      eapply (np_exit_m1 FO GIOA TP fflagA GL FFREE7); [exact CTX| exact INV| exact PC| exact FRA| reflexivity| exact HH| exact Hh| exact HD| exact Hd].
    - lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF. zstep. apply evtF_done. subst POSTQ.
      eapply np_exit_sh; [exact CTX| exact INV| exact PC| exact FRA| exact HH| exact Hh| exact HD| exact Hd].
    - eapply np_exit_sh; [exact CTX| exact INV| exact PC| exact FRA| exact HH| exact Hh| exact HD| exact Hd].
    - lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF. zstep. apply evtF_done. subst POSTQ.
      eapply (np_exit_n FO GIOA TP fflagA GL FFREE7); [exact CTX| exact INV| exact PC| exact FRA| reflexivity| exact HH| exact Hh| exact HD| exact Hd].
    - eapply (np_exit_n FO GIOA TP fflagA GL FFREE7); [exact CTX| exact INV| exact PC| exact FRA| reflexivity| exact HH| exact Hh| exact HD| exact Hd].
  Qed.
  End Sz6.
  Lemma np_fail_ret : ltac:(let t := eval cbv delta [np_fail_ret__stmt] in np_fail_ret__stmt in exact t).
  Proof using GL FFREE7 SETF8. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 h p' hcs' dw pc. ltac2:(SecDiet.SzSec.closeP 'np_fail_ret__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpExitSh.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NpExit.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.

  Definition np_exit__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 : word)
      (scs : list cell) (st : Z) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA scs -> cells_size scs = 120%nat ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (st = 1 \/ st = 0 \/ st = -1)%Z ->
    (st = 1%Z -> hcs' = hdr_cells h /\ (0 <= h_caplen h < 2^32)%Z /\ (0 <= h_len h < 2^32)%Z) ->
    implMG RNGx (fo_ret FO _ FF_NEXT_PACKET (st, h, p')) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp r9 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 st) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r20 (Z_to_bv 64 Fb) r22 r23 r24 r26 (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88d28) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 scs st h p' hcs' dw : ltac2:(SecDiet.SzSec.tyM 'np_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_exit__body : ltac2:(SecDiet.SzSec.bodyP 'np_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7.
 intros CTX INV PC FRA Hscs HH Hh HD Hd STC ST1.
    destruct CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & OHA & ODA & DHD & HA8 & DA8 & SPAB & SPA32).
    destruct INV as (FP & G & OF & MI & ST & STG & FR & AG & (k0 & k1 & k2 & fj & FRC) & SHC & SHD).
    unfold PCAP_L2_STACK in BU. unfold np_shadow in SHC.
    destruct (rw_cells_forget _ _ _ _ FRA) as [jS FRA']. rewrite Hscs in FRA'. clear FRA.
    destruct (rw_cells_cut _ _ _ 1 FRC) as [FRC0 FRC1]. clear FRC. cbn [firstn skipn cells_size csize Nat.add] in FRC0, FRC1.
    destruct (rw_cells_cut _ _ _ 3 FRC1) as [_ FRL]. clear FRC1. cbn [firstn skipn cells_size csize Nat.add] in FRL.
    lazymatch type of FRL with rw_cells _ _ ?A _ => replace A with (Fb + 8184)%Z in FRL by lia end.
    apply (rng_fp_le _ _ _ _ FP) in RSTK. apply (rng_fp_le _ _ _ _ FP) in RIMG. apply (rng_fp_le _ _ _ _ FP) in RISH. apply (rng_fp_le _ _ _ _ FP) in RTLS.
    eapply implMG_mono.
    { eapply (np_epi FO GIOA fflagA GL FFREE7 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNGx sx CL PB FB FL lo SPA Fb mm);
        [exact SPAB| exact SPA32| exact LO| unfold FAKE_STACK; lia| exact SPT| exact TOP47| exact TPE| exact G| exact MI| exact ST| exact STG| exact FRA'| exact FR
        | exact FRC0| exact FRL| exact SHC| exact RSTK| exact RIMG| exact RISH| exact RTLS]. }
    intros r' s3' RNG3 ms3 (-> & -> & PO). destruct_exs PO. destruct PO as (-> & MI7 & ST7 & AG7 & AGP7 & G7 & OF7).
    unfold next_packet_post. split; [exact FP|].
    lazymatch goal with |- context [MS _ _ _ _ _ ?m7 _] => exists (Z_to_bv 64 st), m7, PB, dw end.
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [congruence|]. split; [exact MI7|]. split; [exact ST7|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG|]; intros a (K & N1 & N2); split; [exact K|]; cbn [outside fst snd]; lia|].
             eapply agrees_on_weaken; [exact AG7|]. intros a (K & _); exact K. }
    split; [exact G7|].
    assert (PC7 : PCAPR (hptr:=hptr) P p' PB FB x13).
    { eapply PCAPR_agree; [exact AGP7| intros a Ha; apply in_block_app; right; exact Ha| exact PC]. }
    split; [intros _; exact PC7|]. split; [intros _; apply PCAPR_closable_of; exact PC7|].
    split; [reflexivity|]. split; [exact STC|].
    assert (KHA : forall cs, rw_cells asegs mm HA cs -> cells_size cs = 24%nat -> rw_cells asegs x13 HA cs).
    { intros cs HC HS. eapply agrees_rw_cells; [exact AG7| exact HC|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OHA)| rewrite HS in Ha; lia]. }
    split. { intros E1. destruct (ST1 E1) as (EH & C1 & C2). subst hcs'. split; [apply KHA; [exact HH| reflexivity]|]. split; assumption. }
    split. { intros _. exists hcs'. split; [exact Hh| apply KHA; [exact HH| exact Hh]]. }
    split; [| exact Hd].
    eapply agrees_rw_cells; [exact AG7| exact HD|]. intros a Ha. eapply clocA_keeps; [exact (proj1 ODA)| cbn [cells_size] in Ha; rewrite Hd in Ha; lia].
  Qed.
  End Sz1.
  Lemma np_exit : ltac:(let t := eval cbv delta [np_exit__stmt] in np_exit__stmt in exact t).
  Proof using GL FFREE7. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 scs st h p' hcs' dw. ltac2:(SecDiet.SzSec.closeP 'np_exit__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_exit_m1__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 : word)
      (scs : list cell) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA scs -> cells_size scs = 120%nat ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    implMG RNGx (fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, h, p')) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp r9 a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r20 (Z_to_bv 64 Fb) r22 r23 r24 r26 (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88d24) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 scs h p' hcs' dw : ltac2:(SecDiet.SzSec.tyM 'np_exit_m1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_exit_m1__body : ltac2:(SecDiet.SzSec.bodyP 'np_exit_m1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7.
 intros CTX INV PC FRA Hscs HH Hh HD Hd.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep.
    apply evtF_done. subst POSTQ.
    eapply np_exit with (st := (-1)%Z); [exact CTX| exact INV| exact PC| exact FRA| exact Hscs| exact HH| exact Hh| exact HD| exact Hd| lia| intros X; discriminate X].
  Qed.
  End Sz2.
  Lemma np_exit_m1 : ltac:(let t := eval cbv delta [np_exit_m1__stmt] in np_exit_m1__stmt in exact t).
  Proof using GL FFREE7. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 scs h p' hcs' dw. ltac2:(SecDiet.SzSec.closeP 'np_exit_m1__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_exit_n__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 : word)
      (c0 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 : word)
      (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c8; C8 c7; C8 c10; C8 c9; C8 c11; C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    implMG RNGx (fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, h, p')) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r20 r21 r22 r23 r24 r26 (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x89000) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 c0 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 h p' hcs' dw : ltac2:(SecDiet.SzSec.tyM 'np_exit_n__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_exit_n__body : ltac2:(SecDiet.SzSec.bodyP 'np_exit_n__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7.
 intros CTX INV PC FRA HH Hh HD Hd.
    np_setup GL CTX INV.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    do 3 zstep.
    apply evtF_done. subst POSTQ.
    eapply np_exit with (st := (-1)%Z); [exact CTX| exact INV| exact PC| exact FRA| reflexivity| exact HH| exact Hh| exact HD| exact Hd| lia| intros X; discriminate X].
  Qed.
  End Sz3.
  Lemma np_exit_n : ltac:(let t := eval cbv delta [np_exit_n__stmt] in np_exit_n__stmt in exact t).
  Proof using GL FFREE7. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 c0 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 h p' hcs' dw. ltac2:(SecDiet.SzSec.closeP 'np_exit_n__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpExit.

Section NpExitSh.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.

  (* [comment removed for export] *)
  Definition np_exit_sh__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 : word) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c8; C8 c7; C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 c9; C8 c11; C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    implMG RNGx (fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, h, p')) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r20 (Z_to_bv 64 Fb) r22 r23 r24 r26 (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x89088) fc None mm (seg_rom asegs)).
  Section Sz4.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 h p' hcs' dw : ltac2:(SecDiet.SzSec.tyM 'np_exit_sh__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_exit_sh__body : ltac2:(SecDiet.SzSec.bodyP 'np_exit_sh__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8.
 intros CTX INV PC FRA HH Hh HD Hd.
    np_setup GL CTX INV.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HH']. rewrite Hh in HH'. clear HH.
    destruct (rw_cells_forget _ _ _ _ HD) as [dj HD']. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'. clear HD.
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z mm) as MU.
    pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    do 2 zstep.
    zstep.
    (* [comment removed for export] *)
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (SETF8 _ spa) with (lo := lo) (SA := (Z.shiftr Fb 3 + 2147450892)%Z) (n := 512%Z) (old := dsh);
        [ assumption | rewrite Hspa; exact ST | rewrite Hspa; unfold FAKE_STACK; lia | lia
        | exact (proj1 (gl_rt _ _ _ GL _ _ _ _ _ _ _ G)) | exact (gl_got_memset _ _ _ GL _ _ _ _ _ _ _ G)
        | reflexivity | reflexivity | lia | lia | exact SHD
        | eapply rng_sub'; [exact FSRNG| lia] | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] | exact RIMG ]
      | ].
    cbv beta. intros ms' PO. destruct PO as (a0v & m2 & E & MUc & WMc & MIc & STc & SHD2).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. unfold FAKE_STACK in MUc.
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end.
    replace (ret_pc (Z_to_bv 64 561300)) with (Z_to_bv 64 561300) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(SPA - 4096, SPA); (Z.shiftr Fb 3 + 2147450892, Z.shiftr Fb 3 + 2147450892 + 512)]%Z) by own_ivs.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ m2 _ [] _ (Forall_impl _ (own_ivA_PB _ PB _) FW) (Forall_nil _) G MUc WMc ltac:(lia)) as [G2 AG2].
    assert (PC2 : PCAPR (hptr:=hptr) P p' PB FB m2).
    { eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MUc| exact WMc|]; intros a _ Ha; exact Ha| | exact PC].
      intros a Ha. exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ PB) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a (proj2 (in_block_app _ _ _) (or_intror Ha))). }
    subst spa.
    zstep. (* [comment removed for export] *)
    apply evtF_done. subst POSTQ.
    eapply (np_exit_m1 FO GIOA TP fflagA GL FFREE7) with (PB := PB) (dsh := repeat (Z_to_bv 8 248) (Z.to_nat 512)) (hcs' := [CB 24 hj]) (dw := CB 8 dj);
      [ exact CTX | | exact PC2 | eassumption | reflexivity | eassumption | reflexivity | eassumption | reflexivity ].
    unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G2|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|].
    split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG2|]. intros a (K & _). split; [exact K| exact I]. }
    split; [exists k0, k1, k2, fj; assumption|]. split; [assumption|]. exact SHD2.
  Qed.
  End Sz4.
  Lemma np_exit_sh : ltac:(let t := eval cbv delta [np_exit_sh__stmt] in np_exit_sh__stmt in exact t).
  Proof using GL FFREE7 SETF8. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 h p' hcs' dw. ltac2:(SecDiet.SzSec.closeP 'np_exit_sh__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_ret_ok (pc : Z) (r21 c1 : word) (Fb : Z) : Prop :=
    ((pc = 0x88954 \/ pc = 0x88d24 \/ pc = 0x89054 \/ pc = 0x89088)%Z /\ r21 = Z_to_bv 64 Fb)
    \/ (pc = 0x89000%Z /\ c1 = Z_to_bv 64 Fb).
  #[using="Type"] Lemma np_ret_pc : forall pc r21 c1 Fb, np_ret_ok pc r21 c1 Fb -> ret_pc (Z_to_bv 64 pc) = Z_to_bv 64 pc.
  Proof. intros pc r21 c1 Fb [[X _]|[X _]]; apply ret_pc_even; lia. Qed.

  Definition np_fail_ret__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c10 c11 c12 c13 c14 : word) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell) (pc : Z),
    np_ret_ok pc r21 c1 Fb ->
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8;
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 c10; C8 c11; C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    implMG RNGx (fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, h, p')) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r20 r21 r22 r23 r24 r26 (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Section Sz6.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c10 c11 c12 c13 c14 h p' hcs' dw pc : ltac2:(SecDiet.SzSec.tyM 'np_fail_ret__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_fail_ret__body : ltac2:(SecDiet.SzSec.bodyP 'np_fail_ret__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8.
 intros ROK CTX INV PC FRA HH Hh HD Hd.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    destruct ROK as [[[-> |[-> |[-> | ->]]] ->]|[-> ->]].
    - lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF. zstep. apply evtF_done. subst POSTQ.
      eapply (np_exit_m1 FO GIOA TP fflagA GL FFREE7); [exact CTX| exact INV| exact PC| exact FRA| reflexivity| exact HH| exact Hh| exact HD| exact Hd].
    - eapply (np_exit_m1 FO GIOA TP fflagA GL FFREE7); [exact CTX| exact INV| exact PC| exact FRA| reflexivity| exact HH| exact Hh| exact HD| exact Hd].
    - lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF. zstep. apply evtF_done. subst POSTQ.
      eapply np_exit_sh; [exact CTX| exact INV| exact PC| exact FRA| exact HH| exact Hh| exact HD| exact Hd].
    - eapply np_exit_sh; [exact CTX| exact INV| exact PC| exact FRA| exact HH| exact Hh| exact HD| exact Hd].
    - eapply (np_exit_n FO GIOA TP fflagA GL FFREE7); [exact CTX| exact INV| exact PC| exact FRA| exact HH| exact Hh| exact HD| exact Hd].
  Qed.
  End Sz6.
  Lemma np_fail_ret : ltac:(let t := eval cbv delta [np_fail_ret__stmt] in np_fail_ret__stmt in exact t).
  Proof using GL FFREE7 SETF8. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c10 c11 c12 c13 c14 h p' hcs' dw pc. ltac2:(SecDiet.SzSec.closeP 'np_fail_ret__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpExitSh.
End CANSEC1.
End TwB.
End F_sfnp_exitA.

(* [comment removed for export] *)
Module F_sfnp_kitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Lemma np_fmt_errmsg_length : forall f args e, (length (fmt_errmsg f args e) <= 255)%nat.
Proof.
  intros f args e. unfold fmt_errmsg, snprintf, snprintf_out, PCAP_ERRBUF_SIZE, zlength.
  set (mm := firstn (Z.to_nat (256 - 1)) (fmt_output (fmt f) args)).
  assert (Hm : (length mm <= 255)%nat) by (subst mm; rewrite length_firstn; apply Nat.le_min_l).
  destruct (256 <? Z.of_nat (length mm) + 3)%Z eqn:E; [exact Hm|].
  apply Z.ltb_ge in E. rewrite !length_app, length_firstn. cbn [length str String.list_ascii_of_string map].
  unfold str. cbn [String.list_ascii_of_string map length]. lia.
Qed.
Lemma np_snprintf_length : forall n f a, (length (Fmt.snprintf n f a) <= Z.to_nat (n - 1))%nat.
Proof. intros. unfold Fmt.snprintf, snprintf_out. apply firstn_le_length. Qed.

(* [comment removed for export] *)
Lemma np_sx32_small : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold sx32. f_equal. rewrite unsigned_lit by lia. rewrite bv_swrap32_eq.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma np_zx32_small : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx32. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NpKit.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL"] Lemma PCAPR_errbuf : forall L RNGx sx (CLx : list (@cblock hptr)) Px (p : PcapTypes.pcap hptr hptr) PB FBx FLx (mx mx' : mem) (Q : Z -> Prop) cs e,
    GIOA L RNGx sx (CLx ++ PB) FBx FLx mx -> PCAPR (hptr:=hptr) Px p PB FBx mx -> agrees_on Q mx mx' ->
    (forall a, in_block PB a -> ~ (Px + 216 <= a < Px + 472)%Z -> Q a) ->
    rw_cells asegs mx' (Px + 216) cs -> cells_size cs = 256%nat ->
    PCAPR (hptr:=hptr) Px (set_errbuf e p) PB FBx mx'.
  Proof.
    intros L RNGx sx CLx Px p PB FBx FLx mx mx' Q cs e G PC AG HQ HCS Hsz.
    destruct PC as (Afx & Hin & (Bx & I & jx & padx & bsx & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (psize_pos p) as PS. pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G EPB) as [APB API].
    assert (Q1 : forall a, (Px <= a < Px + psize p)%Z -> ~ (Px + 216 <= a < Px + 472)%Z -> Q a).
    { intros a Ha Hn. apply HQ; [|exact Hn]. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    apply (rw_cells_split_CB asegs mx _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [_ CE2]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE2.
    replace (Px + 216 + Z.of_nat 256)%Z with (Px + 472)%Z in CE2 by lia.
    apply (agrees_rw_cells _ _ _ _ _ AG) in CA; [| intros a Ha; rewrite (pc_pre_size p Px Bx (C8 (Z_to_bv 64 Afx)) jx eq_refl) in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CH; [| intros a Ha; cbn [cells_size csize hdr_cells Nat.add] in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CO; [| intros a Ha; cbn [cells_size csize pc_ops Nat.add] in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CE2; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply Q1; lia].
    pose proof (rw_cells_uncut _ _ _ _ _ HCS CE2 ltac:(rewrite Hsz; lia)) as CE'.
    pose proof WF as (_ & _ & W3 & _).
    destruct (pcap_aux_agree p Px Bx I padx bsx mx mx' Q AG) as (BUF' & PRIV' & IFS');
      [ intros a Ha; apply HQ; [rewrite EPB; unfold pcap_blocks, in_block; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; exact Ha| lia]
      | intros a Ha; apply Q1; unfold PCAP_PRIV_OFF in Ha; lia
      | intros sg q Hq a Ha; destruct (API sg q Hq) as [X1 X2]; apply HQ;
          [rewrite EPB; unfold pcap_blocks, in_block; rewrite Hq; do 2 apply Exists_cons_tl; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; exact Ha| lia]
      | lia | exact BUF | exact PRIV | exact IFS |].
    exists Afx. split; [destruct p; exact Hin|].
    exists Bx, I, (set_pj_g (cells_bytes (cs ++ [CB 48 (firstn 48 (skipn 256 (pj_g jx)))])) jx), padx, bsx.
    split; [rewrite EPB; destruct p; reflexivity|].
    split. { pose proof (pcap_cells_join4 mx' Px p Bx (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jx _ (pc_header p)
                           eq_refl CA CE' ltac:(rewrite cells_size_app, Hsz; reflexivity) CH CO) as J.
             unfold pcap_cells. replace (set_header (pc_header p) p) with p in J by (destruct p; reflexivity).
             destruct p; cbn. exact J. }
    split; [destruct p; exact PRIV'|]. split; [destruct p; exact BUF'|]. split; [destruct p; exact PFX|].
    split; [destruct p; exact IFS'|]. destruct p; exact WF.
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO GL"] Lemma np_inv0_callee : forall (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock)
      (lo HA DA SPA Fb : Z) (o : option hptr) (m : mem) (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (RNGy : footprint) (sy : PState H hptr) (my : mem) (Pn : Z -> Prop),
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    (ATOP <= SPA)%Z -> (SPA <= bv_unsigned sp - 224)%Z ->
    fp_le RNGx RNGy -> GIOA L RNGy sy (CL ++ PB) FB ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) my -> ps_outfile sy = ps_outfile sx ->
    mem_inv asegs my -> stk asegs my lo SPA ->
    agrees_on (fun a => client_keeps ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (CL ++ PB) SPA a /\ Pn a) mm my ->
    (forall a, (SPA <= a)%Z -> Pn a) ->
    (forall a, (Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 1024)%Z -> Pn a) ->
    (forall a, client_keeps FL CL (bv_unsigned sp) a -> ~ (Fb <= a < Fb + 8192)%Z -> Pn a) ->
    (exists (k0 k1 k2 : word) (fj : list byte),
        rw_cells asegs my Fb [C8 k0; C8 k1; C8 k2; CB (Z.to_nat 8160) fj; C8 (Z_to_bv 64 (fflagA L FF_NEXT_PACKET Fb))]) ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGy sy PB dsh my.
  Proof.
    intros until Pn. intros INV HSPA HSP FPy Gy OFy MIy STy AGy PST PSH PCL FRy.
    destruct INV as (FP & G & OF & MI & ST & STG & FR & AG & _ & SHC & SHD).
    unfold np_inv0. split; [eapply fp_le_trans; [exact FP| exact FPy]|]. split; [exact Gy|]. split; [congruence|]. split; [exact MIy|]. split; [exact STy|].
    assert (INSH : forall a, (Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 1024)%Z -> in_frame_sh ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) a).
    { intros a Ha. apply in_frame_sh_In. exists (FF_NEXT_PACKET, Fb, 8192%Z). split; [left; reflexivity|].
      cbn [fb_addr fb_size fst snd]. change (Z.shiftr 8192 3) with 1024%Z. exact Ha. }
    split. { eapply agrees_stk; [exact AGy| exact STG|]. intros a Ha. split; [left; lia| apply PST; lia]. }
    split. { eapply agrees_rw_cells; [exact AGy| exact FR|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. split; [left; lia| apply PST; lia]. }
    split. { eapply agrees_on_trans; [exact AG|]. eapply (keeps_callee FO GIOA fflagA GL); [exact G| apply incl_appl, incl_refl| exact HSPA| lia| exact AGy|].
             intros a K _ NF. apply PCL; [exact K| exact NF]. }
    split; [exact FRy|].
    split. { eapply agrees_rw_cells; [exact AGy| exact SHC|]. intros a Ha. unfold np_shadow in Ha. cbn [cells_size csize Nat.add] in Ha.
             split; [right; right; right; apply INSH; lia| apply PSH; lia]. }
    eapply agrees_rw_cells; [exact AGy| exact SHD|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    split; [right; right; right; apply INSH; lia| apply PSH; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma np_inv0_callee0 : forall (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (L : alayout) (RNG : footprint) (CL CLx FB : list (@cblock hptr)) (FL : list fblock)
      (lo HA DA SPA Fb : Z) (o : option hptr) (m : mem) (RNGx : footprint) (sx : PState H hptr) (PB PB' : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (RNGy : footprint) (sy : PState H hptr) (my : mem),
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    (SPA <= bv_unsigned sp - 224)%Z ->
    fp_le RNGx RNGy -> GIOA L RNGy sy (CL ++ PB') FB ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) my -> ps_outfile sy = ps_outfile sx ->
    mem_inv asegs my -> stk asegs my lo SPA -> incl CL CLx ->
    agrees_on (client_keeps ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) CLx SPA) mm my ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGy sy PB' dsh my.
  Proof.
    intros until my. intros INV HSP FPy Gy OFy MIy STy ICx AGy.
    destruct INV as (FP & G & OF & MI & ST & STG & FR & AG & (k0 & k1 & k2 & fj & FRC) & SHC & SHD).
    unfold np_inv0. split; [eapply fp_le_trans; [exact FP| exact FPy]|]. split; [exact Gy|]. split; [congruence|]. split; [exact MIy|]. split; [exact STy|].
    assert (INSH : forall a, (Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 1024)%Z -> in_frame_sh ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) a).
    { intros a Ha. apply in_frame_sh_In. exists (FF_NEXT_PACKET, Fb, 8192%Z). split; [left; reflexivity|].
      cbn [fb_addr fb_size fst snd]. change (Z.shiftr 8192 3) with 1024%Z. exact Ha. }
    split. { eapply agrees_stk; [exact AGy| exact STG|]. intros a Ha. left; lia. }
    split. { eapply agrees_rw_cells; [exact AGy| exact FR|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. left; lia. }
    split. { eapply agrees_on_trans; [exact AG|]. eapply (keeps_callee0 CLx (FF_NEXT_PACKET, Fb, 8192%Z) FL _ _ CL (bv_unsigned sp) SPA); [exact ICx| lia| exact AGy]. }
    split. { exists k0, k1, k2, fj. eapply agrees_rw_cells; [exact AGy| exact FRC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
             right; right; left. apply in_frames_In. exists (FF_NEXT_PACKET, Fb, 8192%Z). split; [left; reflexivity|]. cbn [fb_addr fb_size fst snd]. lia. }
    split. { eapply agrees_rw_cells; [exact AGy| exact SHC|]. intros a Ha. unfold np_shadow in Ha. cbn [cells_size csize Nat.add] in Ha.
             right; right; right; apply INSH; lia. }
    eapply agrees_rw_cells; [exact AGy| exact SHD|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    right; right; right; apply INSH; lia.
  Qed.

  #[using="Type"] Lemma np_frame_keep : forall (L : alayout) (CLx : list (@cblock hptr)) (FL : list fblock) (SPA Fb : Z) (mm my : mem) (Pn : Z -> Prop),
    agrees_on (fun a => client_keeps ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) CLx SPA a /\ Pn a) mm my ->
    (forall a, (Fb <= a < Fb + 8192)%Z -> Pn a) ->
    (exists (k0 k1 k2 : word) (fj : list byte),
        rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB (Z.to_nat 8160) fj; C8 (Z_to_bv 64 (fflagA L FF_NEXT_PACKET Fb))]) ->
    (exists (k0 k1 k2 : word) (fj : list byte),
        rw_cells asegs my Fb [C8 k0; C8 k1; C8 k2; CB (Z.to_nat 8160) fj; C8 (Z_to_bv 64 (fflagA L FF_NEXT_PACKET Fb))]).
  Proof.
    intros L CLx FL SPA Fb mm my Pn AGy PFR (k0 & k1 & k2 & fj & FRC). exists k0, k1, k2, fj.
    eapply agrees_rw_cells; [exact AGy| exact FRC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    split; [| apply PFR; lia]. right; right; left. apply in_frames_In. exists (FF_NEXT_PACKET, Fb, 8192%Z). split; [left; reflexivity|].
    cbn [fb_addr fb_size fst snd]. lia.
  Qed.
End NpKit.

#[using="Type"] Lemma np_bytes_wr_rw_cells : forall mx A l, bytes_at asegs mx A l -> wr_at asegs mx A (Z.of_nat (length l)) -> rw_cells asegs mx A [CB (length l) l].
Proof. intros mx A l HB HW. split; [split; [cbn; split; [reflexivity| exact Logic.I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB] | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r; exact HW]. Qed.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition np_fmt_errmsg_length__stmt : Prop := forall f args e, (length (fmt_errmsg f args e) <= 255)%nat.
Section Sz1.
Variables f args e : ltac2:(SecDiet.SzSec.tyM 'np_fmt_errmsg_length__stmt "vvv" @f).
#[using="Type"] Lemma np_fmt_errmsg_length__body : ltac2:(SecDiet.SzSec.bodyP 'np_fmt_errmsg_length__stmt "vvv").
Proof.
 unfold fmt_errmsg, snprintf, snprintf_out, PCAP_ERRBUF_SIZE, zlength.
  set (mm := firstn (Z.to_nat (256 - 1)) (fmt_output (fmt f) args)).
  assert (Hm : (length mm <= 255)%nat) by (subst mm; rewrite length_firstn; apply Nat.le_min_l).
  destruct (256 <? Z.of_nat (length mm) + 3)%Z eqn:E; [exact Hm|].
  apply Z.ltb_ge in E. rewrite !length_app, length_firstn. cbn [length str String.list_ascii_of_string map].
  unfold str. cbn [String.list_ascii_of_string map length]. lia.
Qed.
End Sz1.
Lemma np_fmt_errmsg_length : ltac:(let t := eval cbv delta [np_fmt_errmsg_length__stmt] in np_fmt_errmsg_length__stmt in exact t).
Proof. intros f args e. ltac2:(SecDiet.SzSec.closeP 'np_fmt_errmsg_length__body "vvv"). Qed.
Lemma np_snprintf_length : forall n f a, (length (Fmt.snprintf n f a) <= Z.to_nat (n - 1))%nat.
Proof. intros. unfold Fmt.snprintf, snprintf_out. apply firstn_le_length. Qed.

(* [comment removed for export] *)
Lemma np_sx32_small : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold sx32. f_equal. rewrite unsigned_lit by lia. rewrite bv_swrap32_eq.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma np_zx32_small : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx32. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NpKit.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  (* [comment removed for export] *)
  Definition PCAPR_errbuf__stmt : Prop := forall L RNGx sx (CLx : list (@cblock hptr)) Px (p : PcapTypes.pcap hptr hptr) PB FBx FLx (mx mx' : mem) (Q : Z -> Prop) cs e,
    GIOA L RNGx sx (CLx ++ PB) FBx FLx mx -> PCAPR (hptr:=hptr) Px p PB FBx mx -> agrees_on Q mx mx' ->
    (forall a, in_block PB a -> ~ (Px + 216 <= a < Px + 472)%Z -> Q a) ->
    rw_cells asegs mx' (Px + 216) cs -> cells_size cs = 256%nat ->
    PCAPR (hptr:=hptr) Px (set_errbuf e p) PB FBx mx'.
  Section Sz5.
  Variables L RNGx sx CLx Px p PB FBx FLx mx mx' Q cs e : ltac2:(SecDiet.SzSec.tyM 'PCAPR_errbuf__stmt "vvvvvvvvvvvvvv" @L).
  #[using="rc tlsI FO fflagA GL"] Lemma PCAPR_errbuf__body : ltac2:(SecDiet.SzSec.bodyP 'PCAPR_errbuf__stmt "vvvvvvvvvvvvvv").
  Proof.
    intros G PC AG HQ HCS Hsz.
    destruct PC as (Afx & Hin & (Bx & I & jx & padx & bsx & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (psize_pos p) as PS. pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G EPB) as [APB API].
    assert (Q1 : forall a, (Px <= a < Px + psize p)%Z -> ~ (Px + 216 <= a < Px + 472)%Z -> Q a).
    { intros a Ha Hn. apply HQ; [|exact Hn]. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    apply (rw_cells_split_CB asegs mx _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [_ CE2]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE2.
    replace (Px + 216 + Z.of_nat 256)%Z with (Px + 472)%Z in CE2 by lia.
    apply (agrees_rw_cells _ _ _ _ _ AG) in CA; [| intros a Ha; rewrite (pc_pre_size p Px Bx (C8 (Z_to_bv 64 Afx)) jx eq_refl) in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CH; [| intros a Ha; cbn [cells_size csize hdr_cells Nat.add] in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CO; [| intros a Ha; cbn [cells_size csize pc_ops Nat.add] in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CE2; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply Q1; lia].
    pose proof (rw_cells_uncut _ _ _ _ _ HCS CE2 ltac:(rewrite Hsz; lia)) as CE'.
    pose proof WF as (_ & _ & W3 & _).
    destruct (pcap_aux_agree p Px Bx I padx bsx mx mx' Q AG) as (BUF' & PRIV' & IFS');
      [ intros a Ha; apply HQ; [rewrite EPB; unfold pcap_blocks, in_block; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; exact Ha| lia]
      | intros a Ha; apply Q1; unfold PCAP_PRIV_OFF in Ha; lia
      | intros sg q Hq a Ha; destruct (API sg q Hq) as [X1 X2]; apply HQ;
          [rewrite EPB; unfold pcap_blocks, in_block; rewrite Hq; do 2 apply Exists_cons_tl; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; exact Ha| lia]
      | lia | exact BUF | exact PRIV | exact IFS |].
    exists Afx. split; [destruct p; exact Hin|].
    exists Bx, I, (set_pj_g (cells_bytes (cs ++ [CB 48 (firstn 48 (skipn 256 (pj_g jx)))])) jx), padx, bsx.
    split; [rewrite EPB; destruct p; reflexivity|].
    split. { pose proof (pcap_cells_join4 mx' Px p Bx (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jx _ (pc_header p)
                           eq_refl CA CE' ltac:(rewrite cells_size_app, Hsz; reflexivity) CH CO) as J.
             unfold pcap_cells. replace (set_header (pc_header p) p) with p in J by (destruct p; reflexivity).
             destruct p; cbn. exact J. }
    split; [destruct p; exact PRIV'|]. split; [destruct p; exact BUF'|]. split; [destruct p; exact PFX|].
    split; [destruct p; exact IFS'|]. destruct p; exact WF.
  Qed.
  End Sz5.
  #[using="rc tlsI FO fflagA GL"] Lemma PCAPR_errbuf : ltac:(let t := eval cbv delta [PCAPR_errbuf__stmt] in PCAPR_errbuf__stmt in exact t).
  Proof. intros L RNGx sx CLx Px p PB FBx FLx mx mx' Q cs e. ltac2:(SecDiet.SzSec.closeP 'PCAPR_errbuf__body "vvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_inv0_callee__stmt : Prop := forall (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock)
      (lo HA DA SPA Fb : Z) (o : option hptr) (m : mem) (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (RNGy : footprint) (sy : PState H hptr) (my : mem) (Pn : Z -> Prop),
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    (ATOP <= SPA)%Z -> (SPA <= bv_unsigned sp - 224)%Z ->
    fp_le RNGx RNGy -> GIOA L RNGy sy (CL ++ PB) FB ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) my -> ps_outfile sy = ps_outfile sx ->
    mem_inv asegs my -> stk asegs my lo SPA ->
    agrees_on (fun a => client_keeps ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (CL ++ PB) SPA a /\ Pn a) mm my ->
    (forall a, (SPA <= a)%Z -> Pn a) ->
    (forall a, (Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 1024)%Z -> Pn a) ->
    (forall a, client_keeps FL CL (bv_unsigned sp) a -> ~ (Fb <= a < Fb + 8192)%Z -> Pn a) ->
    (exists (k0 k1 k2 : word) (fj : list byte),
        rw_cells asegs my Fb [C8 k0; C8 k1; C8 k2; CB (Z.to_nat 8160) fj; C8 (Z_to_bv 64 (fflagA L FF_NEXT_PACKET Fb))]) ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGy sy PB dsh my.
  Section Sz6.
  Variables ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm RNGy sy my Pn : ltac2:(SecDiet.SzSec.tyM 'np_inv0_callee__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="tlsI FO GL"] Lemma np_inv0_callee__body : ltac2:(SecDiet.SzSec.bodyP 'np_inv0_callee__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros INV HSPA HSP FPy Gy OFy MIy STy AGy PST PSH PCL FRy.
    destruct INV as (FP & G & OF & MI & ST & STG & FR & AG & _ & SHC & SHD).
    unfold np_inv0. split; [eapply fp_le_trans; [exact FP| exact FPy]|]. split; [exact Gy|]. split; [congruence|]. split; [exact MIy|]. split; [exact STy|].
    assert (INSH : forall a, (Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 1024)%Z -> in_frame_sh ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) a).
    { intros a Ha. apply in_frame_sh_In. exists (FF_NEXT_PACKET, Fb, 8192%Z). split; [left; reflexivity|].
      cbn [fb_addr fb_size fst snd]. change (Z.shiftr 8192 3) with 1024%Z. exact Ha. }
    split. { eapply agrees_stk; [exact AGy| exact STG|]. intros a Ha. split; [left; lia| apply PST; lia]. }
    split. { eapply agrees_rw_cells; [exact AGy| exact FR|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. split; [left; lia| apply PST; lia]. }
    split. { eapply agrees_on_trans; [exact AG|]. eapply (keeps_callee FO GIOA fflagA GL); [exact G| apply incl_appl, incl_refl| exact HSPA| lia| exact AGy|].
             intros a K _ NF. apply PCL; [exact K| exact NF]. }
    split; [exact FRy|].
    split. { eapply agrees_rw_cells; [exact AGy| exact SHC|]. intros a Ha. unfold np_shadow in Ha. cbn [cells_size csize Nat.add] in Ha.
             split; [right; right; right; apply INSH; lia| apply PSH; lia]. }
    eapply agrees_rw_cells; [exact AGy| exact SHD|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    split; [right; right; right; apply INSH; lia| apply PSH; lia].
  Qed.
  End Sz6.
  #[using="tlsI FO GL"] Lemma np_inv0_callee : ltac:(let t := eval cbv delta [np_inv0_callee__stmt] in np_inv0_callee__stmt in exact t).
  Proof. intros ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm RNGy sy my Pn. ltac2:(SecDiet.SzSec.closeP 'np_inv0_callee__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_inv0_callee0__stmt : Prop := forall (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (L : alayout) (RNG : footprint) (CL CLx FB : list (@cblock hptr)) (FL : list fblock)
      (lo HA DA SPA Fb : Z) (o : option hptr) (m : mem) (RNGx : footprint) (sx : PState H hptr) (PB PB' : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (RNGy : footprint) (sy : PState H hptr) (my : mem),
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    (SPA <= bv_unsigned sp - 224)%Z ->
    fp_le RNGx RNGy -> GIOA L RNGy sy (CL ++ PB') FB ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) my -> ps_outfile sy = ps_outfile sx ->
    mem_inv asegs my -> stk asegs my lo SPA -> incl CL CLx ->
    agrees_on (client_keeps ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) CLx SPA) mm my ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGy sy PB' dsh my.
  Section Sz7.
  Variables ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL CLx FB FL lo HA DA SPA Fb o m RNGx sx PB PB' dsh mm RNGy sy my : ltac2:(SecDiet.SzSec.tyM 'np_inv0_callee0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="Type"] Lemma np_inv0_callee0__body : ltac2:(SecDiet.SzSec.bodyP 'np_inv0_callee0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros INV HSP FPy Gy OFy MIy STy ICx AGy.
    destruct INV as (FP & G & OF & MI & ST & STG & FR & AG & (k0 & k1 & k2 & fj & FRC) & SHC & SHD).
    unfold np_inv0. split; [eapply fp_le_trans; [exact FP| exact FPy]|]. split; [exact Gy|]. split; [congruence|]. split; [exact MIy|]. split; [exact STy|].
    assert (INSH : forall a, (Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 1024)%Z -> in_frame_sh ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) a).
    { intros a Ha. apply in_frame_sh_In. exists (FF_NEXT_PACKET, Fb, 8192%Z). split; [left; reflexivity|].
      cbn [fb_addr fb_size fst snd]. change (Z.shiftr 8192 3) with 1024%Z. exact Ha. }
    split. { eapply agrees_stk; [exact AGy| exact STG|]. intros a Ha. left; lia. }
    split. { eapply agrees_rw_cells; [exact AGy| exact FR|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. left; lia. }
    split. { eapply agrees_on_trans; [exact AG|]. eapply (keeps_callee0 CLx (FF_NEXT_PACKET, Fb, 8192%Z) FL _ _ CL (bv_unsigned sp) SPA); [exact ICx| lia| exact AGy]. }
    split. { exists k0, k1, k2, fj. eapply agrees_rw_cells; [exact AGy| exact FRC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
             right; right; left. apply in_frames_In. exists (FF_NEXT_PACKET, Fb, 8192%Z). split; [left; reflexivity|]. cbn [fb_addr fb_size fst snd]. lia. }
    split. { eapply agrees_rw_cells; [exact AGy| exact SHC|]. intros a Ha. unfold np_shadow in Ha. cbn [cells_size csize Nat.add] in Ha.
             right; right; right; apply INSH; lia. }
    eapply agrees_rw_cells; [exact AGy| exact SHD|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    right; right; right; apply INSH; lia.
  Qed.
  End Sz7.
  #[using="Type"] Lemma np_inv0_callee0 : ltac:(let t := eval cbv delta [np_inv0_callee0__stmt] in np_inv0_callee0__stmt in exact t).
  Proof. intros ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL CLx FB FL lo HA DA SPA Fb o m RNGx sx PB PB' dsh mm RNGy sy my. ltac2:(SecDiet.SzSec.closeP 'np_inv0_callee0__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  #[using="Type"] Lemma np_frame_keep : forall (L : alayout) (CLx : list (@cblock hptr)) (FL : list fblock) (SPA Fb : Z) (mm my : mem) (Pn : Z -> Prop),
    agrees_on (fun a => client_keeps ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) CLx SPA a /\ Pn a) mm my ->
    (forall a, (Fb <= a < Fb + 8192)%Z -> Pn a) ->
    (exists (k0 k1 k2 : word) (fj : list byte),
        rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB (Z.to_nat 8160) fj; C8 (Z_to_bv 64 (fflagA L FF_NEXT_PACKET Fb))]) ->
    (exists (k0 k1 k2 : word) (fj : list byte),
        rw_cells asegs my Fb [C8 k0; C8 k1; C8 k2; CB (Z.to_nat 8160) fj; C8 (Z_to_bv 64 (fflagA L FF_NEXT_PACKET Fb))]).
  Proof.
    intros L CLx FL SPA Fb mm my Pn AGy PFR (k0 & k1 & k2 & fj & FRC). exists k0, k1, k2, fj.
    eapply agrees_rw_cells; [exact AGy| exact FRC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    split; [| apply PFR; lia]. right; right; left. apply in_frames_In. exists (FF_NEXT_PACKET, Fb, 8192%Z). split; [left; reflexivity|].
    cbn [fb_addr fb_size fst snd]. lia.
  Qed.
End NpKit.

#[using="Type"] Lemma np_bytes_wr_rw_cells : forall mx A l, bytes_at asegs mx A l -> wr_at asegs mx A (Z.of_nat (length l)) -> rw_cells asegs mx A [CB (length l) l].
Proof. intros mx A l HB HW. split; [split; [cbn; split; [reflexivity| exact Logic.I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB] | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r; exact HW]. Qed.
End CANSEC1.
End TwB.
End F_sfnp_kitA.

(* [comment removed for export] *)
Module F_sfnp_failA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA.
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

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NpFail.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.

  (* [comment removed for export] *)
  Definition np_snp__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (t0 t1 t2 a3 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 : word) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell)
      (pc FMTA : Z) (fs : string) (args : list farg),
    np_ret_ok pc r21 r23 Fb ->
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9;
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 c11; C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    fmt_at mm FMTA fs -> fmt_ok fs args = true -> (length args <= 2)%nat ->
    Forall2 (farg_word true L RNGx ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (CL ++ PB) SPA (P + 216) 256 mm) args (firstn (length args) [a3; a4]) ->
    implMG RNGx (fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, h, set_errbuf (Fmt.snprintf 256 fs args) p')) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR (Z_to_bv 64 pc) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (P + 216)) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r20 r21 r22 r23 r24 (Z_to_bv 64 Fb) r26 r27 t3 t4 t5 t6)
          F (Z_to_bv 64 SNPRINTF_ENTRY) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm t0 t1 t2 a3 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 h p' hcs' dw pc FMTA fs args : ltac2:(SecDiet.SzSec.tyM 'np_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_snp__body : ltac2:(SecDiet.SzSec.bodyP 'np_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 SNPRINTF.
    intros ROK CTX INV PC FRA HH Hh HD Hd FMT5 FOK LA FWA.
    np_setup GL CTX INV.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HH']. rewrite Hh in HH'. clear HH.
    destruct (rw_cells_forget _ _ _ _ HD) as [dj HD']. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'. clear HD.
    pose proof PC as (Afx & _ & (Bx & Ix & jx & padx & bsx & EPB & CELLS & _ & _ & _ & _ & WF)).
    pose proof (psize_pos p') as PS.
    assert (HinP : In (pc_self p', P, psize p') ((CL ++ PB) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; rewrite EPB; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP) as PBLK. pose proof PBLK as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    cbn [cb_addr cb_size fst snd] in PBAND, P3, PTOP, P2, P1, PUNP, PRNG, PRSH. band_ind PBAND bP.
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ G HinP (or_introl eq_refl) ltac:(cbn [cb_size snd]; lia)) as (kPF & kPFr & kPF1 & kPF2).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2.
    assert (HinPB : In (pc_self p', P, psize p') PB) by (rewrite EPB; left; reflexivity).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OHA) (incl_refl _) IFL) HinPB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kHP & kHPr & kHP1 & kHP2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 ODA) (incl_refl _) IFL) HinPB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kDP & kDPr & kDP1 & kDP2).
    cbn [cb_addr cb_size fst snd] in kHP1, kHP2, kDP1, kDP2.
    apply pcap_cells_split4 in CELLS as (_ & CE & _ & _); [|reflexivity].
    apply (rw_cells_split_CB asegs mm _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 _]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1.
    assert (OEB : cobjA RNGx mm ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (CL ++ PB) (P + 216) 256).
    { split; [left; exists (pc_self p', P, psize p'); split; [apply in_or_app; right; exact HinPB| cbn [cb_addr cb_size fst snd]; lia]|].
      eapply blockA_aobj; [exact PBLK| cbn [cb_addr cb_size fst snd]; lia| cbn [cb_addr cb_size fst snd]; lia| lia]. }
    pose proof (munch_refl [(bv_unsigned sp - 57344, bv_unsigned sp); (P, P + 664)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply SNPRINTF with (L := L) (s := sx) (CL := CL ++ PB) (FB := FB) (FL := (FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (lo := lo) (DST := (P + 216)%Z) (n := 256%Z)
                             (FMTA := FMTA) (fs := fs) (args := args) (junk := firstn 256 (pj_g jx));
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | reflexivity | reflexivity | reflexivity | lia | exact FMT5 | exact FOK | lia
        | rewrite Hspa; replace (firstn (length args) [a3; a4; a5]) with (firstn (length args) [a3; a4])
            by (clear - LA; destruct args as [|? [|? [|? ?]]]; cbn in LA |- *; first [reflexivity | lia]); exact FWA
        | exact CE1 | exact OEB ]
      | ].
    cbv beta; intros ms' PO; destruct PO as (vav5 & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
    unfold hpost_regs in E; destruct_exs E; subst ms'; rewrite Hspa in *; clear Hspa; subst spa.
    unfold STDIO_STACK in MU6.
    assert (AGS : agrees_on (fun a => outside [(SPA - 16384, SPA); (P + 216, P + 216 + 256)]%Z a) mm m6)
      by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] PB (bv_unsigned sp)) [(SPA - 16384, SPA); (P + 216, P + 216 + 256)]%Z).
    { apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
      right; left. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ m6 _ [] _ FW (Forall_nil _) G MU6 WM6 ltac:(lia)) as [G6 AG6].
    assert (PC6 : PCAPR (hptr:=hptr) P (set_errbuf (Fmt.snprintf 256 fs args) p') PB FB m6).
    { pose proof (np_snprintf_length 256 fs args) as LEN. change (Z.to_nat (256 - 1)) with 255%nat in LEN.
      eapply (PCAPR_errbuf FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ G PC AGS); [| exact HEB6 | cbn [cells_size csize Nat.add]; change (Z.to_nat 256) with 256%nat; lia].
      intros a Ha Hn. cbn [outside].
      pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G (proj2 (in_block_app _ _ _) (or_introl (proj2 (in_block_app _ _ _) (or_intror Ha))))). lia. }
    lazymatch type of MU6 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU6 WM6 end; clear MU6 WM6.
    rewrite (np_ret_pc _ _ _ _ ROK).
    apply evtF_done. subst POSTQ.
    eapply (np_fail_ret FO GIOA TP fflagA GL FFREE7 SETF8) with (PB := PB) (dsh := dsh) (hcs' := [CB 24 hj]) (dw := CB 8 dj);
      [ exact ROK | exact CTX | | exact PC6 | eassumption | eassumption | reflexivity | eassumption | reflexivity ].
    unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G6|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|].
    split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG6|]. intros a (K & _). split; [exact K| exact I]. }
    split; [exists k0, k1, k2, fj; assumption|]. split; assumption.
  Qed.
  End Sz1.
  Lemma np_snp : ltac:(let t := eval cbv delta [np_snp__stmt] in np_snp__stmt in exact t).
  Proof using GL FFREE7 SETF8 SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm t0 t1 t2 a3 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 h p' hcs' dw pc FMTA fs args. ltac2:(SecDiet.SzSec.closeP 'np_snp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_fmt__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (t0 t1 t2 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 : word) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell)
      (pc e : Z) (g : list Z -> Monad.M (PState H hptr) (Z * pkthdr * PcapTypes.pcap hptr hptr)),
    np_ret_ok pc r21 r23 Fb ->
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9;
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 c11; C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (-2^31 <= e < 2^31)%Z -> fmt_at mm 0x21b80 "error reading dump file"%string ->
    (forall msg, g msg = fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, h, set_errbuf msg p')) ->
    implMG RNGx (mbind (fo_enter FO _ FF_FMT_ERRMSG (fo_ret FO _ FF_FMT_ERRMSG (fmt_errmsg "error reading dump file"%string [] e))) g) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR (Z_to_bv 64 pc) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (P + 216)) (Z_to_bv 64 256) (Z_to_bv 64 (s32 e)) (Z_to_bv 64 0x21b80) a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r20 r21 r22 r23 r24 (Z_to_bv 64 Fb) r26 r27 t3 t4 t5 t6)
          F (Z_to_bv 64 PCAP_FMT_ERRMSG_ENTRY) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm t0 t1 t2 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 h p' hcs' dw pc e g : ltac2:(SecDiet.SzSec.tyM 'np_fmt__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_fmt__body : ltac2:(SecDiet.SzSec.bodyP 'np_fmt__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 FMT.
    intros ROK CTX INV PC FRA HH Hh HD Hd HE MSG Hg.
    np_setup GL CTX INV.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HH']. rewrite Hh in HH'. clear HH.
    destruct (rw_cells_forget _ _ _ _ HD) as [dj HD']. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'. clear HD.
    pose proof PC as (Afx & _ & (Bx & Ix & jx & padx & bsx & EPB & CELLS & _ & _ & _ & _ & WF)).
    pose proof (psize_pos p') as PS.
    assert (HinP : In (pc_self p', P, psize p') ((CL ++ PB) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; rewrite EPB; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP) as PBLK. pose proof PBLK as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    cbn [cb_addr cb_size fst snd] in PBAND, P3, PTOP, P2, P1, PUNP, PRNG, PRSH. band_ind PBAND bP.
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ G HinP (or_introl eq_refl) ltac:(cbn [cb_size snd]; lia)) as (kPF & kPFr & kPF1 & kPF2).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2.
    assert (HinPB : In (pc_self p', P, psize p') PB) by (rewrite EPB; left; reflexivity).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OHA) (incl_refl _) IFL) HinPB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kHP & kHPr & kHP1 & kHP2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 ODA) (incl_refl _) IFL) HinPB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kDP & kDPr & kDP1 & kDP2).
    cbn [cb_addr cb_size fst snd] in kHP1, kHP2, kDP1, kDP2.
    apply pcap_cells_split4 in CELLS as (_ & CE & _ & _); [|reflexivity].
    apply (rw_cells_split_CB asegs mm _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 _]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1.
    assert (OEB : cobjA RNGx mm ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (CL ++ PB) (P + 216) 256).
    { split; [left; exists (pc_self p', P, psize p'); split; [apply in_or_app; right; exact HinPB| cbn [cb_addr cb_size fst snd]; lia]|].
      eapply blockA_aobj; [exact PBLK| cbn [cb_addr cb_size fst snd]; lia| cbn [cb_addr cb_size fst snd]; lia| lia]. }
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply implMG_bind.
    { eapply (FMT _ spa) with (L := L) (s := sx) (CL := CL ++ PB) (FB := FB) (FL := (FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (lo := lo) (EB := (P + 216)%Z)
                             (FMTA := 0x21b80%Z) (e := e) (fs := "error reading dump file"%string) (args := []) (junk := firstn 256 (pj_g jx));
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold PCAP_L1_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | cbn [map fb_fn fst]; intros [X|X]; [discriminate X|];
          exact (NF FF_FMT_ERRMSG ltac:(unfold frames_next_packet_op, frames_pcap_next_packet; right; left; reflexivity) X)
        | reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor
        | exact CE1 | exact OEB | Z.div_mod_to_equations; lia ]. }
    intros r4 s4' RNG4 ms4 PO. cbv beta in PO. destruct PO as (FP4 & -> & PO). destruct_exs PO.
    destruct PO as (-> & OF4 & LC4 & TL4 & MI4 & ST4 & AG4 & G4 & HEB4).
    rewrite Hspa in *. clear Hspa. subst spa.
    rewrite (np_ret_pc _ _ _ _ ROK). rewrite Hg.
    lazymatch type of AG4 with agrees_on _ _ ?m4 =>
      assert (KST : forall A cs, rw_cells asegs mm A cs -> (SPA <= A)%Z -> rw_cells asegs m4 A cs)
        by (intros A cs HC HA'; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [left; lia| lia]);
      assert (KFR : forall A cs, rw_cells asegs mm A cs -> (Fb <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fb + 8192)%Z -> rw_cells asegs m4 A cs)
        by (intros A cs HC H1 H3; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [|lia];
            right; right; left; apply in_frames_In; exists (FF_NEXT_PACKET, Fb, 8192%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]);
      assert (KSH : forall A cs, rw_cells asegs mm A cs -> (Z.shiftr Fb 3 + 2147450880 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Z.shiftr Fb 3 + 2147450880 + 1024)%Z -> rw_cells asegs m4 A cs)
        by (intros A cs HC H1 H3; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [|lia];
            right; right; right; apply in_frame_sh_In; exists (FF_NEXT_PACKET, Fb, 8192%Z);
            split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 8192 3) with 1024%Z; lia]);
      assert (KOB : forall A k cs, rw_cells asegs mm A cs -> clocA FL CL A k -> Z.of_nat (cells_size cs) = k ->
                     (A + k <= P + 216 \/ P + 216 + 256 <= A)%Z -> rw_cells asegs m4 A cs)
        by (intros A k cs HC LOC HSz HD; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [|lia];
            eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ LOC ICL IFL)| lia]);
      assert (AGm4 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(HA, HA + 24); (DA, DA + 8)]%Z a) m m4)
        by (eapply agrees_on_trans; [exact AG|]; eapply (keeps_callee FO GIOA fflagA GL); [exact G| exact ICL| | | exact AG4|];
            [lia| lia| intros a K _ _ Hin; eapply (keeps_not_PB FO GIOA fflagA GL); [exact G| exact IFL| | exact K|];
                       [lia| rewrite EPB; unfold pcap_blocks, in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia]])
    end.
    apply KST in FR; [|lia]. apply KST in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG4) in STG; [|intros a Ha; split; [left; lia| lia]].
    apply KFR in FRC; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply KSH in SHC; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KSH in SHD; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KOB _ 24%Z) in HH'; [|exact (proj1 OHA)|reflexivity|lia].
    apply (KOB _ 8%Z) in HD'; [|exact (proj1 ODA)|reflexivity|lia].
    pose proof (np_fmt_errmsg_length "error reading dump file" [] e) as LEN.
    assert (PC4 : PCAPR (hptr:=hptr) P (set_errbuf (fmt_errmsg "error reading dump file" [] e) p') PB FB x14).
    { eapply (PCAPR_errbuf FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ G PC AG4); [| exact HEB4 | cbn [cells_size csize Nat.add]; lia].
      intros a Ha Hn. split; [right; left; apply in_block_app; right; exact Ha| lia]. }
    eapply (np_fail_ret FO GIOA TP fflagA GL FFREE7 SETF8) with (PB := PB) (dsh := dsh) (hcs' := [CB 24 hj]) (dw := CB 8 dj);
      [ exact ROK | exact CTX | | exact PC4 | exact FRA | exact HH' | reflexivity | exact HD' | reflexivity ].
    unfold np_inv0, np_shadow. split; [eapply fp_le_trans; [exact FP| exact FP4]|]. split; [exact G4|]. split; [congruence|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [assumption|]. split; [exact AGm4|].
    split; [exists k0, k1, k2, fj; assumption|]. split; assumption.
  Qed.
  End Sz2.
  Lemma np_fmt : ltac:(let t := eval cbv delta [np_fmt__stmt] in np_fmt__stmt in exact t).
  Proof using GL FFREE7 SETF8 FMT. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm t0 t1 t2 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 h p' hcs' dw pc e g. ltac2:(SecDiet.SzSec.closeP 'np_fmt__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpFail.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NpFail.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.

  (* [comment removed for export] *)
  Definition np_snp__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (t0 t1 t2 a3 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 : word) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell)
      (pc FMTA : Z) (fs : string) (args : list farg),
    np_ret_ok pc r21 c1 Fb ->
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c8; C8 c7; C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 c9; C8 c11; C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    fmt_at mm FMTA fs -> fmt_ok fs args = true -> (length args <= 2)%nat ->
    Forall2 (farg_word true L RNGx ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (CL ++ PB) SPA (P + 216) 256 mm) args (firstn (length args) [a3; a4]) ->
    implMG RNGx (fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, h, set_errbuf (Fmt.snprintf 256 fs args) p')) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR (Z_to_bv 64 pc) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (P + 216)) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r20 r21 r22 r23 r24 r26 (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 SNPRINTF_ENTRY) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm t0 t1 t2 a3 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 h p' hcs' dw pc FMTA fs args : ltac2:(SecDiet.SzSec.tyM 'np_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_snp__body : ltac2:(SecDiet.SzSec.bodyP 'np_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 SNPRINTF.
 intros ROK CTX INV PC FRA HH Hh HD Hd FMT5 FOK LA FWA.
    np_setup GL CTX INV.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HH']. rewrite Hh in HH'. clear HH.
    destruct (rw_cells_forget _ _ _ _ HD) as [dj HD']. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'. clear HD.
    pose proof PC as (Afx & _ & (Bx & Ix & jx & padx & bsx & EPB & CELLS & _ & _ & _ & _ & WF)).
    pose proof (psize_pos p') as PS.
    assert (HinP : In (pc_self p', P, psize p') ((CL ++ PB) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; rewrite EPB; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP) as PBLK. pose proof PBLK as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    cbn [cb_addr cb_size fst snd] in PBAND, P3, PTOP, P2, P1, PUNP, PRNG, PRSH. band_ind PBAND bP.
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ G HinP (or_introl eq_refl) ltac:(cbn [cb_size snd]; lia)) as (kPF & kPFr & kPF1 & kPF2).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2.
    assert (HinPB : In (pc_self p', P, psize p') PB) by (rewrite EPB; left; reflexivity).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OHA) (incl_refl _) IFL) HinPB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kHP & kHPr & kHP1 & kHP2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 ODA) (incl_refl _) IFL) HinPB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kDP & kDPr & kDP1 & kDP2).
    cbn [cb_addr cb_size fst snd] in kHP1, kHP2, kDP1, kDP2.
    apply pcap_cells_split4 in CELLS as (_ & CE & _ & _); [|reflexivity].
    apply (rw_cells_split_CB asegs mm _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 _]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1.
    assert (OEB : cobjA RNGx mm ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (CL ++ PB) (P + 216) 256).
    { split; [left; exists (pc_self p', P, psize p'); split; [apply in_or_app; right; exact HinPB| cbn [cb_addr cb_size fst snd]; lia]|].
      eapply blockA_aobj; [exact PBLK| cbn [cb_addr cb_size fst snd]; lia| cbn [cb_addr cb_size fst snd]; lia| lia]. }
    pose proof (munch_refl [(bv_unsigned sp - 57344, bv_unsigned sp); (P, P + 664)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply SNPRINTF with (L := L) (s := sx) (CL := CL ++ PB) (FB := FB) (FL := (FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (lo := lo) (DST := (P + 216)%Z) (n := 256%Z)
                             (FMTA := FMTA) (fs := fs) (args := args) (junk := firstn 256 (pj_g jx));
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | reflexivity | reflexivity | reflexivity | lia | exact FMT5 | exact FOK | lia
        | rewrite Hspa; replace (firstn (length args) [a3; a4; a5]) with (firstn (length args) [a3; a4])
            by (clear - LA; destruct args as [|? [|? [|? ?]]]; cbn in LA |- *; first [reflexivity | lia]); exact FWA
        | exact CE1 | exact OEB ]
      | ].
    cbv beta; intros ms' PO; destruct PO as (vav5 & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
    unfold hpost_regs in E; destruct_exs E; subst ms'; rewrite Hspa in *; clear Hspa; subst spa.
    unfold STDIO_STACK in MU6.
    assert (AGS : agrees_on (fun a => outside [(SPA - 16384, SPA); (P + 216, P + 216 + 256)]%Z a) mm m6)
      by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] PB (bv_unsigned sp)) [(SPA - 16384, SPA); (P + 216, P + 216 + 256)]%Z).
    { apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
      right; left. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ m6 _ [] _ FW (Forall_nil _) G MU6 WM6 ltac:(lia)) as [G6 AG6].
    assert (PC6 : PCAPR (hptr:=hptr) P (set_errbuf (Fmt.snprintf 256 fs args) p') PB FB m6).
    { pose proof (np_snprintf_length 256 fs args) as LEN. change (Z.to_nat (256 - 1)) with 255%nat in LEN.
      eapply (PCAPR_errbuf FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ G PC AGS); [| exact HEB6 | cbn [cells_size csize Nat.add]; change (Z.to_nat 256) with 256%nat; lia].
      intros a Ha Hn. cbn [outside].
      pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G (proj2 (in_block_app _ _ _) (or_introl (proj2 (in_block_app _ _ _) (or_intror Ha))))). lia. }
    lazymatch type of MU6 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU6 WM6 end; clear MU6 WM6.
    rewrite (np_ret_pc _ _ _ _ ROK).
    apply evtF_done. subst POSTQ.
    eapply (np_fail_ret FO GIOA TP fflagA GL FFREE7 SETF8) with (PB := PB) (dsh := dsh) (hcs' := [CB 24 hj]) (dw := CB 8 dj);
      [ exact ROK | exact CTX | | exact PC6 | eassumption | eassumption | reflexivity | eassumption | reflexivity ].
    unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G6|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|].
    split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG6|]. intros a (K & _). split; [exact K| exact I]. }
    split; [exists k0, k1, k2, fj; assumption|]. split; assumption.
  Qed.
  End Sz1.
  Lemma np_snp : ltac:(let t := eval cbv delta [np_snp__stmt] in np_snp__stmt in exact t).
  Proof using GL FFREE7 SETF8 SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm t0 t1 t2 a3 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 h p' hcs' dw pc FMTA fs args. ltac2:(SecDiet.SzSec.closeP 'np_snp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_fmt__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (t0 t1 t2 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 : word) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell)
      (pc e : Z) (g : list Z -> Monad.M (PState H hptr) (Z * pkthdr * PcapTypes.pcap hptr hptr)),
    np_ret_ok pc r21 c1 Fb ->
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c8; C8 c7; C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 c9; C8 c11; C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (-2^31 <= e < 2^31)%Z -> fmt_at mm 0x21b80 "error reading dump file"%string ->
    (forall msg, g msg = fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, h, set_errbuf msg p')) ->
    implMG RNGx (mbind (fo_enter FO _ FF_FMT_ERRMSG (fo_ret FO _ FF_FMT_ERRMSG (fmt_errmsg "error reading dump file"%string [] e))) g) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR (Z_to_bv 64 pc) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (P + 216)) (Z_to_bv 64 256) (Z_to_bv 64 (s32 e)) (Z_to_bv 64 0x21b80) a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r20 r21 r22 r23 r24 r26 (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 PCAP_FMT_ERRMSG_ENTRY) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm t0 t1 t2 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 h p' hcs' dw pc e g : ltac2:(SecDiet.SzSec.tyM 'np_fmt__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_fmt__body : ltac2:(SecDiet.SzSec.bodyP 'np_fmt__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 FMT.
 intros ROK CTX INV PC FRA HH Hh HD Hd HE MSG Hg.
    np_setup GL CTX INV.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HH']. rewrite Hh in HH'. clear HH.
    destruct (rw_cells_forget _ _ _ _ HD) as [dj HD']. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'. clear HD.
    pose proof PC as (Afx & _ & (Bx & Ix & jx & padx & bsx & EPB & CELLS & _ & _ & _ & _ & WF)).
    pose proof (psize_pos p') as PS.
    assert (HinP : In (pc_self p', P, psize p') ((CL ++ PB) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; rewrite EPB; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP) as PBLK. pose proof PBLK as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    cbn [cb_addr cb_size fst snd] in PBAND, P3, PTOP, P2, P1, PUNP, PRNG, PRSH. band_ind PBAND bP.
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ G HinP (or_introl eq_refl) ltac:(cbn [cb_size snd]; lia)) as (kPF & kPFr & kPF1 & kPF2).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2.
    assert (HinPB : In (pc_self p', P, psize p') PB) by (rewrite EPB; left; reflexivity).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OHA) (incl_refl _) IFL) HinPB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kHP & kHPr & kHP1 & kHP2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 ODA) (incl_refl _) IFL) HinPB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kDP & kDPr & kDP1 & kDP2).
    cbn [cb_addr cb_size fst snd] in kHP1, kHP2, kDP1, kDP2.
    apply pcap_cells_split4 in CELLS as (_ & CE & _ & _); [|reflexivity].
    apply (rw_cells_split_CB asegs mm _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 _]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1.
    assert (OEB : cobjA RNGx mm ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (CL ++ PB) (P + 216) 256).
    { split; [left; exists (pc_self p', P, psize p'); split; [apply in_or_app; right; exact HinPB| cbn [cb_addr cb_size fst snd]; lia]|].
      eapply blockA_aobj; [exact PBLK| cbn [cb_addr cb_size fst snd]; lia| cbn [cb_addr cb_size fst snd]; lia| lia]. }
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply implMG_bind.
    { eapply (FMT _ spa) with (L := L) (s := sx) (CL := CL ++ PB) (FB := FB) (FL := (FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (lo := lo) (EB := (P + 216)%Z)
                             (FMTA := 0x21b80%Z) (e := e) (fs := "error reading dump file"%string) (args := []) (junk := firstn 256 (pj_g jx));
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold PCAP_L1_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | cbn [map fb_fn fst]; intros [X|X]; [discriminate X|];
          exact (NF FF_FMT_ERRMSG ltac:(unfold frames_next_packet_op, frames_pcap_next_packet; right; left; reflexivity) X)
        | reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor
        | exact CE1 | exact OEB | Z.div_mod_to_equations; lia ]. }
    intros r4 s4' RNG4 ms4 PO. cbv beta in PO. destruct PO as (FP4 & -> & PO). destruct_exs PO.
    destruct PO as (-> & OF4 & LC4 & TL4 & MI4 & ST4 & AG4 & G4 & HEB4).
    rewrite Hspa in *. clear Hspa. subst spa.
    rewrite (np_ret_pc _ _ _ _ ROK). rewrite Hg.
    lazymatch type of AG4 with agrees_on _ _ ?m4 =>
      assert (KST : forall A cs, rw_cells asegs mm A cs -> (SPA <= A)%Z -> rw_cells asegs m4 A cs)
        by (intros A cs HC HA'; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [left; lia| lia]);
      assert (KFR : forall A cs, rw_cells asegs mm A cs -> (Fb <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fb + 8192)%Z -> rw_cells asegs m4 A cs)
        by (intros A cs HC H1 H3; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [|lia];
            right; right; left; apply in_frames_In; exists (FF_NEXT_PACKET, Fb, 8192%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]);
      assert (KSH : forall A cs, rw_cells asegs mm A cs -> (Z.shiftr Fb 3 + 2147450880 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Z.shiftr Fb 3 + 2147450880 + 1024)%Z -> rw_cells asegs m4 A cs)
        by (intros A cs HC H1 H3; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [|lia];
            right; right; right; apply in_frame_sh_In; exists (FF_NEXT_PACKET, Fb, 8192%Z);
            split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 8192 3) with 1024%Z; lia]);
      assert (KOB : forall A k cs, rw_cells asegs mm A cs -> clocA FL CL A k -> Z.of_nat (cells_size cs) = k ->
                     (A + k <= P + 216 \/ P + 216 + 256 <= A)%Z -> rw_cells asegs m4 A cs)
        by (intros A k cs HC LOC HSz HD; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [|lia];
            eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ LOC ICL IFL)| lia]);
      assert (AGm4 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(HA, HA + 24); (DA, DA + 8)]%Z a) m m4)
        by (eapply agrees_on_trans; [exact AG|]; eapply (keeps_callee FO GIOA fflagA GL); [exact G| exact ICL| | | exact AG4|];
            [lia| lia| intros a K _ _ Hin; eapply (keeps_not_PB FO GIOA fflagA GL); [exact G| exact IFL| | exact K|];
                       [lia| rewrite EPB; unfold pcap_blocks, in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia]])
    end.
    apply KST in FR; [|lia]. apply KST in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG4) in STG; [|intros a Ha; split; [left; lia| lia]].
    apply KFR in FRC; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply KSH in SHC; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KSH in SHD; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KOB _ 24%Z) in HH'; [|exact (proj1 OHA)|reflexivity|lia].
    apply (KOB _ 8%Z) in HD'; [|exact (proj1 ODA)|reflexivity|lia].
    pose proof (np_fmt_errmsg_length "error reading dump file" [] e) as LEN.
    assert (PC4 : PCAPR (hptr:=hptr) P (set_errbuf (fmt_errmsg "error reading dump file" [] e) p') PB FB x14).
    { eapply (PCAPR_errbuf FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ G PC AG4); [| exact HEB4 | cbn [cells_size csize Nat.add]; lia].
      intros a Ha Hn. split; [right; left; apply in_block_app; right; exact Ha| lia]. }
    eapply (np_fail_ret FO GIOA TP fflagA GL FFREE7 SETF8) with (PB := PB) (dsh := dsh) (hcs' := [CB 24 hj]) (dw := CB 8 dj);
      [ exact ROK | exact CTX | | exact PC4 | exact FRA | exact HH' | reflexivity | exact HD' | reflexivity ].
    unfold np_inv0, np_shadow. split; [eapply fp_le_trans; [exact FP| exact FP4]|]. split; [exact G4|]. split; [congruence|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [assumption|]. split; [exact AGm4|].
    split; [exists k0, k1, k2, fj; assumption|]. split; assumption.
  Qed.
  End Sz2.
  Lemma np_fmt : ltac:(let t := eval cbv delta [np_fmt__stmt] in np_fmt__stmt in exact t).
  Proof using GL FFREE7 SETF8 FMT. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm t0 t1 t2 a4 a5 a6 a7 r18 r20 r21 r22 r23 r24 r26 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 h p' hcs' dw pc e g. ltac2:(SecDiet.SzSec.closeP 'np_fmt__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpFail.
End CANSEC1.
End TwB.
End F_sfnp_failA.

(* [comment removed for export] *)
Module F_sfnp_finA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA.
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
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NpFin.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis PP : post_process_stmt.

  Definition np_finish__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 r22 r23 r24 r27 t3 t4 t5 t6 : word)
      (c0 c1 c4 c5 c7 c8 c11 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (ws wu : word) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 c4; C8 c5;
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 c7; C8 c8; C8 (Z_to_bv 64 DA);
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 c11; C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 ws; C8 wu; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    ws = Z_to_bv 64 sec -> wu = Z_to_bv 64 usec -> Forall (fun x => 0 <= x < 256)%Z data ->
    (0 <= cap <= Z.of_nat (length data))%Z -> (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (let '(hdr, d) := pcapint_post_process (k_lt k) (k_sw k) (mkHdr sec usec cap len) data in
                 fo_ret FO _ FF_NEXT_PACKET (1%Z, hdr, set_bufdata d (pv k bq bsz alloc data eb))) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 (Z_to_bv 64 (P + 100)) a5 a6 a7
               (Z_to_bv 64 HA) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) r22 r23 r24 (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88904) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 r22 r23 r24 r27 t3 t4 t5 t6 c0 c1 c4 c5 c7 c8 c11 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len ws wu dw : ltac2:(SecDiet.SzSec.tyM 'np_finish__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_finish__body : ltac2:(SecDiet.SzSec.bodyP 'np_finish__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 PP.
    intros CTX INV PC FRA HH HD Hd -> -> DRNG Hcap Hlen Hl32 AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs mm _ [] (Z.to_nat alloc) _ [] [length data; (Z.to_nat alloc - length data)%nat]) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF. rewrite PFX in BUF.
    destruct (rw_cells_cut _ _ _ 1 BUF) as [BD BT]. clear BUF. cbn [firstn skipn cells_size csize Nat.add] in BD, BT.
    hide BD. hide BT. hide PRIV.
    pose proof (munch_refl [(DA, DA + 8)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep.
    ck0 PUNP; ck_go.
    zstep.
    ck0 DAUNP; ck_go.
    do 3 zstep.
    ck0_at PUNP (P + 100)%Z; ck_go.
    ck0_at PUNP (P + 56)%Z; ck_go.
    rewrite (np_sx32_small (k_lt k)) by lia.
    do 2 zstep. rewrite (np_sx32_small (Z.b2z (k_sw k))) by (destruct (k_sw k); cbn; lia).
    zstep.
    zstep.
    (* [comment removed for export] *)
    unhide BD. unhide BT. unhide PRIV.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m5 _) =>
      assert (AGD : agrees_on (fun a => outside [(DA, DA + 8)]%Z a) mm m5) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]) end.
    apply (agrees_rw_cells _ _ _ _ _ AGD) in BD; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGD) in BT; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGD) in PRIV; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    assert (FX : Forall (cobj_iv FL CL) [(DA, DA + 8)]%Z) by cobj_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m5 _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m5 [] _ (bv_unsigned sp) (Forall_nil _) FX G MU WM ltac:(lia)) as [G5 AG5];
      assert (AGm5 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(HA, HA + 24); (DA, DA + 8)]%Z a) m m5)
        by (eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG5|]; intros a (K & (_ & QN & _)); split; [exact K|]; split; [exact QN| exact I])
    end.
    pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G IFL AGm5 FXB) as AGsh5.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OHA G5 ICL IFL AGsh5 ltac:(lia)) as OHA5.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as BBLK5.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G5) as (RT5 & _).
    assert (ZA : zarr m0 Bx data).
    { split; [| split; [| exact DRNG]].
      - pose proof (rw_cells_bytes_at _ _ _ _ BD) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X.
      - eapply rw_cells_wr_at; [exact BD|]. cbn [cells_size csize Nat.add]. lia. }
    change (rw_cells asegs m0 HA (pkthdr_cells (Z_to_bv 64 sec) (Z_to_bv 64 usec) (mkHdr sec usec cap len))) in HH.
    clear MU WM AGD.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (PP _ spa) with (lo := lo) (HA := HA) (DA := Bx) (linktype := k_lt k) (swapped := k_sw k) (d := data);
        [ rewrite Hspa; eassumption | rewrite Hspa; unfold PP_FRAME; lia | lia | exact HH | exact ZA | assumption | exact RT5
        | reflexivity | reflexivity | reflexivity | reflexivity | lia | cbn [h_caplen]; lia | lia | cbn [h_len]; lia
        | exact (proj2 OHA5)
        | eapply blockA_aobj; [exact BBLK5 | cbn [cb_addr cb_size fst snd]; lia | cbn [cb_addr cb_size fst snd]; lia | lia]
        | lia | lia | lia | exact HA8 | Z.div_mod_to_equations; lia
        | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] | exact RIMG | exact RISH ]
      | ].
    cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & -> & MU6 & WM6 & MI6 & ST6 & HH6 & ZA6).
    rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 559456)) with (Z_to_bv 64 559456) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    cbn [h_caplen] in MU6. unfold PP_FRAME in MU6.
    set (hdr' := fst (pcapint_post_process (k_lt k) (k_sw k) (mkHdr sec usec cap len) data)) in *.
    set (d' := snd (pcapint_post_process (k_lt k) (k_sw k) (mkHdr sec usec cap len) data)) in *.
    pose proof (pp_length (k_lt k) (k_sw k) (mkHdr sec usec cap len) data) as LEN'. fold d' in LEN'.
    pose proof (pp_sec (k_lt k) (k_sw k) (mkHdr sec usec cap len) data) as [SEC' USEC']. fold hdr' in SEC', USEC'. cbn [h_sec h_usec] in SEC', USEC'.
    pose proof (pp_range (k_lt k) (k_sw k) (mkHdr sec usec cap len) data ltac:(cbn [h_caplen]; lia) ltac:(cbn [h_len]; lia) Hlen) as [RC' RL']. fold hdr' in RC', RL'.
    (* [comment removed for export] *)
    assert (MU6' : munch ([(SPA - 48, SPA); (Bx, Bx + cap)] ++ [(HA, HA + 24)])%Z m0 m6).
    { eapply munch_weaken; [|exact MU6]. intros x Hx. cbn [outside app] in *. destruct Hx as (H1 & H2 & H3 & _).
      split; [exact H1|]. split; [lia|]. split; [exact H2| exact I]. }
    assert (FW6 : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] [(k_self k, P, 664%Z); (bq, Bx, alloc)] (bv_unsigned sp)) [(SPA - 48, SPA); (Bx, Bx + cap)]%Z)
      by (apply Forall_cons; [left; cbn [fst snd]; lia|]; apply Forall_cons; [|apply Forall_nil];
          right; left; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia).
    assert (FX6 : Forall (cobj_iv FL CL) [(HA, HA + 24)]%Z) by cobj_ivs.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m6 _ _ (bv_unsigned sp) FW6 FX6 G5 MU6' WM6 ltac:(lia)) as [G6 AG6].
    assert (AGm6 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(HA, HA + 24); (DA, DA + 8)]%Z a) m m6)
      by (eapply agrees_on_trans; [exact AGm5|]; eapply agrees_on_weaken; [exact AG6|]; intros a (K & (QN & _)); split; [exact K|]; split; [exact QN| exact I]).
    lazymatch type of MU6 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU6 WM6 end. clear MU6 WM6 MU6'.
    (* [comment removed for export] *)
    destruct ZA6 as (ZB & ZW & ZR).
    pose proof (np_bytes_wr_rw_cells _ _ _ ZB ltac:(unfold zbytes; rewrite length_map; exact ZW)) as BD6. unfold zbytes in BD6. rewrite length_map in BD6.
    pose proof (rw_cells_uncut _ _ _ _ _ BD6 BT ltac:(cbn [cells_size csize Nat.add]; rewrite LEN'; lia)) as BUF6.
    cbn [app] in BUF6. merge_all BUF6.
    replace (length d' + (Z.to_nat alloc - length data + 0))%nat with (Z.to_nat alloc) in BUF6 by lia. rewrite app_nil_r in BUF6.
    assert (PC6 : PCAPR (hptr:=hptr) P (set_bufdata d' (pv k bq bsz alloc data eb)) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m6).
    { exists Afx. split; [exact HinFx|]. exists Bx, 0%Z, jx, padx, (map (Z_to_bv 8) d' ++ firstn (Z.to_nat alloc - length data) (skipn (length data) bsx)).
      split; [reflexivity|]. split; [exact CELLS|]. split; [exact PRIV|]. split; [exact BUF6|].
      split; [unfold pv, b8; cbn [pc_bufdata set_bufdata]; replace (length d') with (length (map (Z_to_bv 8) d')) by (apply length_map);
              rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; rewrite app_nil_r; reflexivity|].
      split; [reflexivity|].
      unfold pcap_wf, pv in *. cbn [set_bufdata pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                 pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in *. rewrite LEN'. exact WF. }
    rewrite (surjective_pairing (pcapint_post_process (k_lt k) (k_sw k) _ data)). fold hdr' d'.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    do 2 zstep.
    apply evtF_done. subst POSTQ.
    eapply (np_exit FO GIOA TP fflagA GL FFREE7) with (st := 1%Z) (hcs' := hdr_cells hdr') (dw := C8 (Z_to_bv 64 Bx)) (dsh := dsh)
                                                        (PB := pcap_blocks (pv k bq bsz alloc data eb) P Bx 0);
      [ exact CTX | | exact PC6 | exact FRA | reflexivity | unfold hdr_cells; rewrite SEC', USEC'; exact HH6 | reflexivity | exact HD' | reflexivity
      | lia | intros _; split; [reflexivity| split; assumption] ].
    unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G6|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [exact AGm6|].
    split; [exists k0, k1, k2, fj; assumption|]. split; assumption.
  Qed.
  End Sz1.
  Lemma np_finish : ltac:(let t := eval cbv delta [np_finish__stmt] in np_finish__stmt in exact t).
  Proof using GL FFREE7 PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 r22 r23 r24 r27 t3 t4 t5 t6 c0 c1 c4 c5 c7 c8 c11 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len ws wu dw. ltac2:(SecDiet.SzSec.closeP 'np_finish__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpFin.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NpFin.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis PP : post_process_stmt.

  Definition np_finish__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 r27 t3 t4 t5 t6 : word)
      (c0 c4 c5 c8 c11 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (ws wu : word) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 c4; C8 c5;
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 100)); C8 c8; C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 c11; C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 ws; C8 wu; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    ws = Z_to_bv 64 sec -> wu = Z_to_bv 64 usec -> Forall (fun x => 0 <= x < 256)%Z data ->
    (0 <= cap <= Z.of_nat (length data))%Z -> (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (let '(hdr, d) := pcapint_post_process (k_lt k) (k_sw k) (mkHdr sec usec cap len) data in
                 fo_ret FO _ FF_NEXT_PACKET (1%Z, hdr, set_bufdata d (pv k bq bsz alloc data eb))) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 HA) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) r21 r22 r23 r24 (Z_to_bv 64 2147450880)
               (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88e88) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 r27 t3 t4 t5 t6 c0 c4 c5 c8 c11 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len ws wu dw : ltac2:(SecDiet.SzSec.tyM 'np_finish__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_finish__body : ltac2:(SecDiet.SzSec.bodyP 'np_finish__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 PP.
 intros CTX INV PC FRA HH HD Hd -> -> DRNG Hcap Hlen Hl32 AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs mm _ [] (Z.to_nat alloc) _ [] [length data; (Z.to_nat alloc - length data)%nat]) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF. rewrite PFX in BUF.
    destruct (rw_cells_cut _ _ _ 1 BUF) as [BD BT]. clear BUF. cbn [firstn skipn cells_size csize Nat.add] in BD, BT.
    hide BD. hide BT. hide PRIV.
    pose proof (munch_refl [(DA, DA + 8)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    (* [comment removed for export] *)
    zstep.
    zstep. ub_null.
    zstep. zstep. ub_al 7%Z ltac:(al8 DA8).
    zstep. if_false.
    zstep.
    ck0 PUNP; ck_go.
    zstep.
    ck0 DAUNP; ck_go.
    do 3 zstep.
    ck0_at PUNP (P + 100)%Z; ck_go.
    ck0_at PUNP (P + 56)%Z; ck_go.
    rewrite (np_sx32_small (k_lt k)) by lia.
    do 2 zstep. rewrite (np_sx32_small (Z.b2z (k_sw k))) by (destruct (k_sw k); cbn; lia).
    zstep.
    zstep.
    (* [comment removed for export] *)
    unhide BD. unhide BT. unhide PRIV.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m5 _) =>
      assert (AGD : agrees_on (fun a => outside [(DA, DA + 8)]%Z a) mm m5) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]) end.
    apply (agrees_rw_cells _ _ _ _ _ AGD) in BD; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGD) in BT; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGD) in PRIV; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    assert (FX : Forall (cobj_iv FL CL) [(DA, DA + 8)]%Z) by cobj_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m5 _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m5 [] _ (bv_unsigned sp) (Forall_nil _) FX G MU WM ltac:(lia)) as [G5 AG5];
      assert (AGm5 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(HA, HA + 24); (DA, DA + 8)]%Z a) m m5)
        by (eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG5|]; intros a (K & (_ & QN & _)); split; [exact K|]; split; [exact QN| exact I])
    end.
    pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G IFL AGm5 FXB) as AGsh5.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OHA G5 ICL IFL AGsh5 ltac:(lia)) as OHA5.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as BBLK5.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G5) as (RT5 & _).
    assert (ZA : zarr m0 Bx data).
    { split; [| split; [| exact DRNG]].
      - pose proof (rw_cells_bytes_at _ _ _ _ BD) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X.
      - eapply rw_cells_wr_at; [exact BD|]. cbn [cells_size csize Nat.add]. lia. }
    change (rw_cells asegs m0 HA (pkthdr_cells (Z_to_bv 64 sec) (Z_to_bv 64 usec) (mkHdr sec usec cap len))) in HH.
    clear MU WM AGD.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (PP _ spa) with (lo := lo) (HA := HA) (DA := Bx) (linktype := k_lt k) (swapped := k_sw k) (d := data);
        [ rewrite Hspa; eassumption | rewrite Hspa; unfold PP_FRAME; lia | lia | exact HH | exact ZA | assumption | exact RT5
        | reflexivity | reflexivity | reflexivity | reflexivity | lia | cbn [h_caplen]; lia | lia | cbn [h_len]; lia
        | exact (proj2 OHA5)
        | eapply blockA_aobj; [exact BBLK5 | cbn [cb_addr cb_size fst snd]; lia | cbn [cb_addr cb_size fst snd]; lia | lia]
        | lia | lia | lia | exact HA8 | Z.div_mod_to_equations; lia
        | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] | exact RIMG | exact RISH ]
      | ].
    cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & -> & MU6 & WM6 & MI6 & ST6 & HH6 & ZA6).
    rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 560896)) with (Z_to_bv 64 560896) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    cbn [h_caplen] in MU6. unfold PP_FRAME in MU6.
    set (hdr' := fst (pcapint_post_process (k_lt k) (k_sw k) (mkHdr sec usec cap len) data)) in *.
    set (d' := snd (pcapint_post_process (k_lt k) (k_sw k) (mkHdr sec usec cap len) data)) in *.
    pose proof (pp_length (k_lt k) (k_sw k) (mkHdr sec usec cap len) data) as LEN'. fold d' in LEN'.
    pose proof (pp_sec (k_lt k) (k_sw k) (mkHdr sec usec cap len) data) as [SEC' USEC']. fold hdr' in SEC', USEC'. cbn [h_sec h_usec] in SEC', USEC'.
    pose proof (pp_range (k_lt k) (k_sw k) (mkHdr sec usec cap len) data ltac:(cbn [h_caplen]; lia) ltac:(cbn [h_len]; lia) Hlen) as [RC' RL']. fold hdr' in RC', RL'.
    (* [comment removed for export] *)
    assert (MU6' : munch ([(SPA - 64, SPA); (Bx, Bx + cap)] ++ [(HA, HA + 24)])%Z m0 m6).
    { eapply munch_weaken; [|exact MU6]. intros x Hx. cbn [outside app] in *. destruct Hx as (H1 & H2 & H3 & _).
      split; [exact H1|]. split; [lia|]. split; [exact H2| exact I]. }
    assert (FW6 : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] [(k_self k, P, 664%Z); (bq, Bx, alloc)] (bv_unsigned sp)) [(SPA - 64, SPA); (Bx, Bx + cap)]%Z)
      by (apply Forall_cons; [left; cbn [fst snd]; lia|]; apply Forall_cons; [|apply Forall_nil];
          right; left; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia).
    assert (FX6 : Forall (cobj_iv FL CL) [(HA, HA + 24)]%Z) by cobj_ivs.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m6 _ _ (bv_unsigned sp) FW6 FX6 G5 MU6' WM6 ltac:(lia)) as [G6 AG6].
    assert (AGm6 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(HA, HA + 24); (DA, DA + 8)]%Z a) m m6)
      by (eapply agrees_on_trans; [exact AGm5|]; eapply agrees_on_weaken; [exact AG6|]; intros a (K & (QN & _)); split; [exact K|]; split; [exact QN| exact I]).
    lazymatch type of MU6 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU6 WM6 end. clear MU6 WM6 MU6'.
    (* [comment removed for export] *)
    destruct ZA6 as (ZB & ZW & ZR).
    pose proof (np_bytes_wr_rw_cells _ _ _ ZB ltac:(unfold zbytes; rewrite length_map; exact ZW)) as BD6. unfold zbytes in BD6. rewrite length_map in BD6.
    pose proof (rw_cells_uncut _ _ _ _ _ BD6 BT ltac:(cbn [cells_size csize Nat.add]; rewrite LEN'; lia)) as BUF6.
    cbn [app] in BUF6. merge_all BUF6.
    replace (length d' + (Z.to_nat alloc - length data + 0))%nat with (Z.to_nat alloc) in BUF6 by lia. rewrite app_nil_r in BUF6.
    assert (PC6 : PCAPR (hptr:=hptr) P (set_bufdata d' (pv k bq bsz alloc data eb)) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m6).
    { exists Afx. split; [exact HinFx|]. exists Bx, 0%Z, jx, padx, (map (Z_to_bv 8) d' ++ firstn (Z.to_nat alloc - length data) (skipn (length data) bsx)).
      split; [reflexivity|]. split; [exact CELLS|]. split; [exact PRIV|]. split; [exact BUF6|].
      split; [unfold pv, b8; cbn [pc_bufdata set_bufdata]; replace (length d') with (length (map (Z_to_bv 8) d')) by (apply length_map);
              rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; rewrite app_nil_r; reflexivity|].
      split; [reflexivity|].
      unfold pcap_wf, pv in *. cbn [set_bufdata pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                 pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in *. rewrite LEN'. exact WF. }
    rewrite (surjective_pairing (pcapint_post_process (k_lt k) (k_sw k) _ data)). fold hdr' d'.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    do 2 zstep.
    apply evtF_done. subst POSTQ.
    eapply (np_exit FO GIOA TP fflagA GL FFREE7) with (st := 1%Z) (hcs' := hdr_cells hdr') (dw := C8 (Z_to_bv 64 Bx)) (dsh := dsh)
                                                        (PB := pcap_blocks (pv k bq bsz alloc data eb) P Bx 0);
      [ exact CTX | | exact PC6 | exact FRA | reflexivity | unfold hdr_cells; rewrite SEC', USEC'; exact HH6 | reflexivity | exact HD' | reflexivity
      | lia | intros _; split; [reflexivity| split; assumption] ].
    unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G6|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [exact AGm6|].
    split; [exists k0, k1, k2, fj; assumption|]. split; assumption.
  Qed.
  End Sz1.
  Lemma np_finish : ltac:(let t := eval cbv delta [np_finish__stmt] in np_finish__stmt in exact t).
  Proof using GL FFREE7 PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 r27 t3 t4 t5 t6 c0 c4 c5 c8 c11 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len ws wu dw. ltac2:(SecDiet.SzSec.closeP 'np_finish__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpFin.
End CANSEC1.
End TwB.
End F_sfnp_finA.

(* [comment removed for export] *)
Module F_sfnp_discA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
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

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NpDisc.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis PP : post_process_stmt.

  (* [comment removed for export] *)
  Definition np_otail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r23 r24 t3 t4 t5 t6 : word)
      (c0 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 DA);
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    Forall (fun x => 0 <= x < 256)%Z data -> Z.of_nat (length data) = k_snap k -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (let '(hdr, d) := pcapint_post_process (k_lt k) (k_sw k) (mkHdr sec usec (k_snap k) len) data in
                 fo_ret FO _ FF_NEXT_PACKET (1%Z, hdr, set_bufdata d (pv k bq bsz alloc data eb))) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) r21 (Z_to_bv 64 (P + 96)) r23 r24 (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x887ac) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r23 r24 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_otail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_otail__body : ltac2:(SecDiet.SzSec.bodyP 'np_otail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 PP.
    intros CTX INV PC FRA HH HD Hd DRNG DLEN Hl32 AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    clear PRIV BUF.
    pose proof (munch_refl [(HA, HA + 24)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    ck0_at PUNP (P + 96)%Z; ck_go.
    ck0_at HAUNP (HA + 16)%Z; ck_go.
    rewrite (np_sx32_small (k_snap k)) by lia.
    zstep.
    do 2 zstep. zstep.
    (* [comment removed for export] *)
    clear CELLS.
    assert (FX : Forall (cobj_iv FL CL) [(HA, HA + 24)]%Z) by cobj_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m5 _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m5 [] _ (bv_unsigned sp) (Forall_nil _) FX G MU WM ltac:(lia)) as [G5 AG5];
      assert (AGm5 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(HA, HA + 24); (DA, DA + 8)]%Z a) m m5)
        by (eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG5|]; intros a (K & (QN & _)); split; [exact K|]; split; [exact QN| exact I]);
      assert (PC5 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m5)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ [] _ (bv_unsigned sp) (Forall_nil _) FX G a Ha))
    end.
    clear MU WM.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (SETF8 _ spa) with (lo := lo) (SA := (Z.shiftr Fb 3 + 2147450892)%Z) (n := 512%Z) (old := dsh);
        [ assumption | rewrite Hspa; eassumption | rewrite Hspa; unfold FAKE_STACK; lia | lia
        | exact (proj1 (gl_rt _ _ _ GL _ _ _ _ _ _ _ G5)) | exact (gl_got_memset _ _ _ GL _ _ _ _ _ _ _ G5)
        | reflexivity | reflexivity | lia | lia | eassumption
        | eapply rng_sub'; [exact FSRNG| lia] | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] | exact RIMG ]
      | ].
    cbv beta. intros ms' PO. (nd_pre PO 8%nat; intros a0v m6 E MUc WMc MIc STc SHD6; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. unfold FAKE_STACK in MUc.
    replace (ret_pc (Z_to_bv 64 559072)) with (Z_to_bv 64 559072) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(SPA - 4096, SPA); (Z.shiftr Fb 3 + 2147450892, Z.shiftr Fb 3 + 2147450892 + 512)]%Z) by own_ivs.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m6 _ [] (bv_unsigned sp)
                (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FW) (Forall_nil _) G5 MUc WMc ltac:(lia)) as [G6 AG6].
    assert (PC6 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m6).
    { eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MUc| exact WMc|]; intros a _ Ha; exact Ha| | exact PC5].
      intros a Ha. exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G5 a
                            (proj2 (in_block_app _ _ _) (or_intror Ha))). }
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end. clear MUc WMc.
    subst spa.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    do 2 zstep.
    apply evtF_done. subst POSTQ.
    eapply (np_finish FO GIOA TP fflagA GL FFREE7 PP) with (dsh := repeat (Z_to_bv 8 248) (Z.to_nat 512)) (sec := sec) (usec := usec) (cap := k_snap k);
      [ exact CTX | | exact PC6 | eassumption | eassumption | eassumption | reflexivity | reflexivity | reflexivity | exact DRNG
      | lia | lia | exact Hl32 | exact AL0 ].
    unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G6|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|].
    split. { eapply agrees_on_trans; [exact AGm5|]. eapply agrees_on_weaken; [exact AG6|]. intros a (K & _). split; [exact K| exact I]. }
    split; [exists k0, k1, k2, fj; assumption|]. split; [assumption|]. exact SHD6.
  Qed.
  End Sz1.
  Lemma np_otail : ltac:(let t := eval cbv delta [np_otail__stmt] in np_otail__stmt in exact t).
  Proof using GL FFREE7 SETF8 PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r23 r24 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_otail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  #[using="Type"] Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M (PState H hptr) B) (g : B -> Monad.M (PState H hptr) C) (s : PState H hptr) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof. intros B C f g s RNG Q ms HH. exact HH. Qed.

  (* [comment removed for export] *)
  Definition np_dshort__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r23 r27 t3 t4 t5 t6 : word)
      (c0 c2 c3 c4 c6 c8 c9 c12 c13 c14 : word) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (ws wu : word) (dw : cell) (cap len n : Z),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 c2; C8 c3; C8 c4; C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880)); C8 c6;
                           C8 (Z_to_bv 64 (HA + 16)); C8 c8; C8 c9;
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 ws; C8 wu; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= n <= cap)%Z -> (0 <= cap < 2^31)%Z ->
    implMG RNGx (mbind (read_fail_msg MOps (prims HO FO sites) f (Msg.trunc_captured_u cap n))
                       (fun m0 => fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, h, set_errbuf m0 p'))) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) r21 r22 r23 (Z_to_bv 64 n) (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88a68) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r23 r27 t3 t4 t5 t6 c0 c2 c3 c4 c6 c8 c9 c12 c13 c14 h p' ws wu dw cap len n : ltac2:(SecDiet.SzSec.tyM 'np_dshort__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_dshort__body : ltac2:(SecDiet.SzSec.bodyP 'np_dshort__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF.
    intros CTX INV PC FRA HH HD Hd NR C31.
    np_setup GL CTX INV.
    rename HH into HH'.
    destruct (rw_cells_forget _ _ _ _ HD) as [dj HD']. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'. clear HD.
    set (POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o).
    unfold read_fail_msg. cbn [mo_bind mo_ret MOps e_ferror e_fret prims].
    apply implMG_bind_assoc.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF. zstep. zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { eapply (FERROR _ spa) with (L := L) (s := sx) (CL := CL ++ PB) (FB := FB) (FL := (FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (lo := lo) (f := f) (Af := Af);
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity ]. }
    intros r s3' RNG3 ms' PO. cbv beta in PO. (nd_pre PO 9%nat; intros FP3 av m3 E MI3' ST3 AG3 G3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); rename ndR3__ into ERRNO).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 559728)) with (Z_to_bv 64 559728) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (AG3' : agrees_on (fun a => client_keeps ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (CL ++ PB) SPA a /\ True) mm m3)
      by (eapply agrees_on_weaken; [exact AG3|]; intros a (K & _); exact K).
    assert (INV3 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNG3 sx PB dsh m3).
    { eapply (np_inv0_callee FO GIOA fflagA GL) with (Pn := fun _ => True);
        [ exact INV | lia | lia | exact FP3 | exact G3 | reflexivity | exact MI3' | exact ST3 | exact AG3'
        | intros; exact I | intros; exact I | intros; exact I
        | eapply np_frame_keep with (Pn := fun _ => True); [exact AG3'| intros; exact I| exists k0, k1, k2, fj; exact FRC] ]. }
    assert (PC3 : PCAPR (hptr:=hptr) P p' PB FB m3)
      by (eapply PCAPR_agree; [exact AG3| intros a Ha; right; left; apply in_block_app; right; exact Ha| exact PC]).
    apply (agrees_rw_cells _ _ _ _ _ AG3) in FRA; [|intros a Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HH'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HD'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
    apply (rng_fp_le _ _ _ _ FP3) in RTLS.
    repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    destruct r.
    - (* [comment removed for export] *)
      destruct (ERRNO eq_refl) as [EN2 ER]. clear ERRNO.
      unfold errmsg_for_errno. cbn [mo_bind mo_ret MOps e_last_errno e_fenter e_fret prims].
      apply implMG_errno_ll. set (e := lc_errno (ps_libc sx)) in *.
      (nd_pre (gl_tls _ _ _ GL _ _ _ _ _ _ _ G3 RTLS) 6%nat; intros T0 T47 TUNP TRNG (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) _; nd_post).
      assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
      assert (MSG : fmt_at m3 0x21b80 "error reading dump file"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x21b80 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      apply implMG_from_evtF. zstep. zstep. if_false.
      zstep. do 3 zstep. rewrite ETP.
      ck TUNP 4%Z 0x88a90%Z [11%Z; 12%Z].
      zstep.
      do 4 zstep. zstep.
      replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      apply evtF_done. subst POSTQ.
      eapply (np_fmt FO GIOA TP fflagA GL FFREE7 SETF8 FMT) with (pc := 0x88aa8%Z) (PB := PB) (dsh := dsh) (hcs' := [C8 ws; C8 wu; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)]) (dw := CB 8 dj) (e := e);
        [ left; split; [right; right; right; left; reflexivity| reflexivity] | exact CTX | exact INV3 | exact PC3 | exact FRA | exact HH' | reflexivity | exact HD' | reflexivity
        | lia | exact MSG | intros msg; reflexivity ].
    - (* [comment removed for export] *)
      apply implMG_retb.
      assert (MSG : fmt_at m3 0x21f40 "truncated dump file; tried to read %u captured bytes, only got %zu"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x21f40 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "truncated dump file; tried to read %u captured bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      (* [comment removed for export] *)
      (pose proof INV3 as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ _ _ _ _ AGm3 _; nd_post).
      pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G3 IFL AGm3 FXB) as AGsh3.
      (pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OHA G3 ICL IFL AGsh3 ltac:(lia)) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ HAUNP3 HARNG3 HARSH3 _; nd_post).
      apply implMG_from_evtF. zstep. zstep. if_true.
      ck0_at HAUNP3 (HA + 16)%Z; ck_go.
      zstep. zstep. rewrite (np_sx32_small cap) by lia.
      do 4 zstep. zstep. zstep.
      apply evtF_done. subst POSTQ. unfold Msg.trunc_captured_u, PCAP_ERRBUF_SIZE.
      eapply (np_snp FO GIOA TP fflagA GL FFREE7 SETF8 SNPRINTF) with (pc := 0x88adc%Z) (PB := PB) (dsh := dsh) (hcs' := [C8 ws; C8 wu; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)]) (dw := CB 8 dj)
                                                                               (args := [AInt cap; AInt n]);
        [ left; split; [right; right; right; right; reflexivity| reflexivity] | exact CTX | exact INV3 | exact PC3 | exact FRA | exact HH' | reflexivity | exact HD' | reflexivity
        | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor] ].
  Qed.
  End Sz3.
  Lemma np_dshort : ltac:(let t := eval cbv delta [np_dshort__stmt] in np_dshort__stmt in exact t).
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r23 r27 t3 t4 t5 t6 c0 c2 c3 c4 c6 c8 c9 c12 c13 c14 h p' ws wu dw cap len n. ltac2:(SecDiet.SzSec.closeP 'np_dshort__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.


  (* [comment removed for export] *)
  #[using="Type"] Lemma discard_loop_S : forall fuel fp cap btd br,
    discard_loop MOps (prims HO FO sites) (S fuel) fp cap btd br =
    (if (btd =? 0)%Z then mret (inr tt) else
     mbind (e_fread (prims HO FO sites) fp (DStack SiteDiscardBuf 0) (if 4096 <? btd then 4096 else btd)%Z) (fun got =>
     (if negb (zlength got =? (if 4096 <? btd then 4096 else btd))%Z
      then mbind (read_fail_msg MOps (prims HO FO sites) fp (Msg.trunc_captured_u cap (br + zlength got))) (fun m0 => mret (inl m0))
      else discard_loop MOps (prims HO FO sites) fuel fp cap (btd - zlength got) (br + zlength got)))).
  Proof. intros. reflexivity. Qed.
  #[using="Type"] Lemma discard_loop_0 : forall fuel fp cap br, discard_loop MOps (prims HO FO sites) fuel fp cap 0 br = mret (inr tt).
  Proof. intros. destruct fuel; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma np_discard : forall (fuel : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 t3 t4 t5 t6 : word)
      (c0 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len btd bread : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) (repeat (Z_to_bv 8 0) (Z.to_nat 512)) mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 DA);
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    Forall (fun x => 0 <= x < 256)%Z data -> Z.of_nat (length data) = k_snap k -> (0 <= len < 2^32)%Z -> (0 <= cap < 2^31)%Z -> (0 < alloc)%Z ->
    (0 < btd)%Z -> (btd <= 4096 * (Z.of_nat fuel - 1))%Z -> (0 <= bread)%Z -> (bread + btd <= cap)%Z ->
    implMG RNGx (mbind (discard_loop MOps (prims HO FO sites) fuel (k_f k) cap btd bread)
                       (fun r => match r with
                                 | inl m0 => fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, mkHdr sec usec cap len, set_errbuf m0 (pv k bq bsz alloc data eb))
                                 | inr _ => (let '(hdr, d) := pcapint_post_process (k_lt k) (k_sw k) (mkHdr sec usec (k_snap k) len) data in
                                             fo_ret FO _ FF_NEXT_PACKET (1%Z, hdr, set_bufdata d (pv k bq bsz alloc data eb)))
                                 end)) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 btd) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) r21 (Z_to_bv 64 (P + 96)) (Z_to_bv 64 (Fb + 96))
               (Z_to_bv 64 bread) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x88778) fc None mm (seg_rom asegs)).
  Proof using GL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP.
    induction fuel as [|fuel IH]; intros until dw; intros CTX INV PC FRA HH HD Hd DRNG DLEN Hl32 Hc31 AL0 Bpos Bfuel Br0 Brc.
    { exfalso. cbn [Z.of_nat] in Bfuel. lia. }
    rewrite Nat2Z.inj_succ in Bfuel.
    np_setup GL CTX INV.
    np_blocks GL G OHA ODA IFL.
    rewrite discard_loop_S. replace (btd =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    set (n := (if 4096 <? btd then 4096 else btd)%Z).
    assert (Hn : (0 < n <= 4096)%Z /\ (n <= btd)%Z /\ (n = btd \/ (n = 4096 /\ 4096 < btd))%Z) by (subst n; destruct (Z.ltb_spec 4096 btd); lia).
    clearbody n. (nd_pre Hn 3%nat; intros Hn1 Hn2 Hn3; nd_post).
    cbn [e_fread prims].
    set (POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o).
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF.
    (* [comment removed for export] *)
    do 2 zstep. zstep.
    lazymatch goal with |- evtF _ _ ?Q _ =>
      assert (K54 : forall s5v : word, s5v = Z_to_bv 64 n ->
        evtF asegs RNGx Q
          (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 4096) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 btd) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) s5v (Z_to_bv 64 (P + 96)) (Z_to_bv 64 (Fb + 96))
                   (Z_to_bv 64 bread) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) t3 t4 t5 t6)
              F (Z_to_bv 64 0x88788) fc None mm (seg_rom asegs))) end.
    2:{ if_cases Kc; zify_cond Kc.
        - apply K54. f_equal; lia.
        - zstep. apply K54. f_equal; lia. }
    intros s5v ->.
    do 4 zstep. zstep.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs _ _ [_; _; _] (Z.to_nat 8160) _ [_] [72%nat; Z.to_nat n; (Z.to_nat 8160 - 72 - Z.to_nat n)%nat]) in FRC; [| cbn [sum_nat]; lia].
    cbn [mk_CB_cells app] in FRC.
    lazymatch type of FRC with rw_cells _ _ _ [_; _; _; CB _ ?l0; CB _ ?l1; CB _ ?l2; _] =>
      set (j0 := l0) in FRC; set (j1 := l1) in FRC; set (j2 := l2) in FRC; clearbody j0 j1 j2 end.
    destruct (rw_cells_cut _ _ _ 4 FRC) as [F0 F12]. clear FRC. cbn [firstn skipn cells_size csize Nat.add] in F0, F12.
    destruct (rw_cells_cut _ _ _ 1 F12) as [F1 F2]. clear F12. cbn [firstn skipn cells_size csize Nat.add] in F1, F2.
    lazymatch type of F1 with rw_cells _ _ ?A _ => replace A with (Fb + 96)%Z in F1, F2 by lia end.
    lazymatch type of F2 with rw_cells _ _ ?A _ => replace A with (Fb + 96 + n)%Z in F2 by lia end.
    assert (SHD' : rw_cells asegs mm (Z.shiftr (Fb + 96) 3 + 2147450880) [CB 512 (repeat (Z_to_bv 8 0) (Z.to_nat 512))]).
    { replace (Z.shiftr (Fb + 96) 3 + 2147450880)%Z with (Z.shiftr Fb 3 + 2147450892)%Z; [exact SHD|].
      change (Fb + 96)%Z with (Fb + 8 * 12)%Z. rewrite shiftr3_add by (Z.div_mod_to_equations; lia). lia. }
    pose proof (unp_of_zero_cells _ (Fb + 96)%Z 512%nat _ SHD' ltac:(cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity)
                  ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)) as UNPD.
    change (8 * Z.of_nat 512)%Z with 4096%Z in UNPD. clear SHD'.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. apply implMG_bind_assoc. eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest].
      rewrite (gl_site _ _ _ GL _ _ _ _ _ _ _ _ _ _ SiteDiscardBuf 96%Z G (or_introl eq_refl) eq_refl).
      replace (Fb + 96 + 0)%Z with (Fb + 96)%Z by lia.
      eapply (FREAD _ spa) with (Af := Af);
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact F1
        | split; [right; exists (FF_NEXT_PACKET, Fb, 8192%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia|
                               eapply unpoisoned_sub; [exact UNPD| lia| lia]] ]. }
    intros got s6' RNG6 ms' PO. cbv beta in PO.
    (nd_pre PO 11%nat; intros FP6 av m6 junk6 E OF6 MI6 ST6 AG6 G6 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 3%nat; intros GOTL GOTR HD6; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 559004)) with (Z_to_bv 64 559004) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (KFR : forall A cs, rw_cells asegs mm A cs -> (Fb <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fb + 8192)%Z ->
                   (A + Z.of_nat (cells_size cs) <= Fb + 96 \/ Fb + 96 + n <= A)%Z -> rw_cells asegs m6 A cs)
      by (intros A cs HC H1 H3 H4; eapply agrees_rw_cells; [exact AG6| exact HC|]; intros a Ha; split; [|lia];
          right; right; left; apply in_frames_In; exists (FF_NEXT_PACKET, Fb, 8192%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]).
    apply KFR in F0; [|lia|cbn [cells_size csize Nat.add]; lia|cbn [cells_size csize Nat.add]; lia].
    apply KFR in F2; [|lia|cbn [cells_size csize]; lia|cbn [cells_size csize]; lia]. clear KFR.
    assert (LG : (length got <= Z.to_nat n)%nat) by (unfold zlength in GOTL; lia).
    pose proof (rw_cells_uncut _ _ _ _ _ F0 HD6 ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
    pose proof (rw_cells_uncut _ _ _ _ _ J1 F2 ltac:(cbn [cells_size csize]; lia)) as J2. cbn [app] in J2. clear J1 F0 F2 HD6.
    apply (rw_cells_merge asegs m6 Fb [C8 k0; C8 k1; C8 k2] [_; _; _; _] [_]) in J2.
    replace (cells_size [CB 72 j0; CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk6; CB (Z.to_nat 8160 - 72 - Z.to_nat n) j2])
      with (Z.to_nat 8160) in J2 by (cbn [cells_size csize]; lia).
    cbn [app] in J2.
    assert (INV6 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNG6 s6'
                           (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) (repeat (Z_to_bv 8 0) (Z.to_nat 512)) m6).
    { eapply (np_inv0_callee FO GIOA fflagA GL) with (Pn := fun a => ~ (Fb + 96 <= a < Fb + 96 + n)%Z);
        [ exact INV | lia | lia | exact FP6 | exact G6 | exact OF6 | exact MI6 | exact ST6 | exact AG6
        | intros a Ha; lia | intros a Ha; lia | intros a _ Ha; lia
        | eexists k0, k1, k2, _; exact J2 ]. }
    assert (PC6 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m6).
    { eapply PCAPR_agree; [exact AG6| | exact PC]. intros a Ha. split; [right; left; apply in_block_app; right; exact Ha|].
      intros Hin. eapply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G);
        [ apply in_frames_In; exists (FF_NEXT_PACKET, Fb, 8192%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]
        | apply in_block_app; left; apply in_block_app; right; exact Ha ]. }
    apply (agrees_rw_cells _ _ _ _ _ AG6) in FRA; [|intros a Ha; split; [left; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG6) in HH; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL IFL)| lia]| lia]].
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    apply (agrees_rw_cells _ _ _ _ _ AG6) in HD'; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL IFL)| lia]| lia]].
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    destruct (Z.eq_dec (zlength got) n) as [LEQ|LNE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb]. rewrite LEQ.
      apply implMG_from_evtF.
      zstep. zstep. if_cases Kq; [zify_cond Kq; exfalso; lia|].
      zstep. zstep.
      destruct (Z.eq_dec (btd - n) 0) as [BZ|BNZ].
      + if_cases Kz; [zify_cond Kz; exfalso; lia|].
        apply evtF_done. replace (btd - n)%Z with 0%Z by lia. rewrite discard_loop_0. apply implMG_retb. subst POSTQ.
        eapply np_otail with (sec := sec) (usec := usec) (cap := cap) (dw := CB 8 dwj);
          [ exact CTX | exact INV6 | exact PC6 | exact FRA | exact HH | exact HD' | reflexivity | exact DRNG | exact DLEN | exact Hl32 | exact AL0 ].
      + if_cases Kz; [|zify_cond Kz; exfalso; lia].
        apply evtF_done. subst POSTQ.
        replace (n + bread)%Z with (bread + n)%Z by lia.
        eapply IH with (dw := CB 8 dwj);
          [ exact CTX | exact INV6 | exact PC6 | exact FRA | exact HH | exact HD' | reflexivity | exact DRNG | exact DLEN | exact Hl32 | exact Hc31 | exact AL0
          | lia | lia | lia | lia ].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      apply implMG_bind_assoc.
      apply implMG_from_evtF.
      zstep. zstep. if_cases Kq; [|zify_cond Kq; exfalso; lia].
      apply evtF_done. subst POSTQ.
      replace (zlength got + bread)%Z with (bread + zlength got)%Z by lia.
      eapply np_dshort with (n := (bread + zlength got)%Z) (cap := cap) (len := len) (dsh := repeat (Z_to_bv 8 0) (Z.to_nat 512)) (dw := CB 8 dwj)
                            (p' := pv k bq bsz alloc data eb) (PB := pcap_blocks (pv k bq bsz alloc data eb) P Bx 0);
        [ exact CTX | exact INV6 | exact PC6 | exact FRA | exact HH | exact HD' | reflexivity | lia | lia ].
  Qed.
End NpDisc.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NpDisc.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis PP : post_process_stmt.

  (* [comment removed for export] *)
  Definition np_otail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r23 r24 t3 t4 t5 t6 : word)
      (c0 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    Forall (fun x => 0 <= x < 256)%Z data -> Z.of_nat (length data) = k_snap k -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (let '(hdr, d) := pcapint_post_process (k_lt k) (k_sw k) (mkHdr sec usec (k_snap k) len) data in
                 fo_ret FO _ FF_NEXT_PACKET (1%Z, hdr, set_bufdata d (pv k bq bsz alloc data eb))) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) r21 (Z_to_bv 64 (P + 96)) r23 r24 (Z_to_bv 64 2147450880)
               (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x88cbc) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r23 r24 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_otail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_otail__body : ltac2:(SecDiet.SzSec.bodyP 'np_otail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 PP.
 intros CTX INV PC FRA HH HD Hd DRNG DLEN Hl32 AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    clear PRIV BUF.
    pose proof (munch_refl [(HA, HA + 24)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    ck0_at PUNP (P + 96)%Z; ck_go.
    ck0_at HAUNP (HA + 16)%Z; ck_go.
    rewrite (np_sx32_small (k_snap k)) by lia.
    zstep.
    do 2 zstep. zstep.
    (* [comment removed for export] *)
    clear CELLS.
    assert (FX : Forall (cobj_iv FL CL) [(HA, HA + 24)]%Z) by cobj_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m5 _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m5 [] _ (bv_unsigned sp) (Forall_nil _) FX G MU WM ltac:(lia)) as [G5 AG5];
      assert (AGm5 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(HA, HA + 24); (DA, DA + 8)]%Z a) m m5)
        by (eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG5|]; intros a (K & (QN & _)); split; [exact K|]; split; [exact QN| exact I]);
      assert (PC5 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m5)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ [] _ (bv_unsigned sp) (Forall_nil _) FX G a Ha))
    end.
    clear MU WM.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (SETF8 _ spa) with (lo := lo) (SA := (Z.shiftr Fb 3 + 2147450892)%Z) (n := 512%Z) (old := dsh);
        [ assumption | rewrite Hspa; eassumption | rewrite Hspa; unfold FAKE_STACK; lia | lia
        | exact (proj1 (gl_rt _ _ _ GL _ _ _ _ _ _ _ G5)) | exact (gl_got_memset _ _ _ GL _ _ _ _ _ _ _ G5)
        | reflexivity | reflexivity | lia | lia | eassumption
        | eapply rng_sub'; [exact FSRNG| lia] | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] | exact RIMG ]
      | ].
    cbv beta. intros ms' PO. (nd_pre PO 8%nat; intros a0v m6 E MUc WMc MIc STc SHD6; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. unfold FAKE_STACK in MUc.
    replace (ret_pc (Z_to_bv 64 560364)) with (Z_to_bv 64 560364) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(SPA - 4096, SPA); (Z.shiftr Fb 3 + 2147450892, Z.shiftr Fb 3 + 2147450892 + 512)]%Z) by own_ivs.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m6 _ [] (bv_unsigned sp)
                (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FW) (Forall_nil _) G5 MUc WMc ltac:(lia)) as [G6 AG6].
    assert (PC6 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m6).
    { eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MUc| exact WMc|]; intros a _ Ha; exact Ha| | exact PC5].
      intros a Ha. exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G5 a
                            (proj2 (in_block_app _ _ _) (or_intror Ha))). }
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end. clear MUc WMc.
    subst spa.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    zstep.   (* [comment removed for export] *)
    apply evtF_done. subst POSTQ.
    eapply (np_finish FO GIOA TP fflagA GL FFREE7 PP) with (dsh := repeat (Z_to_bv 8 248) (Z.to_nat 512)) (sec := sec) (usec := usec) (cap := k_snap k);
      [ exact CTX | | exact PC6 | eassumption | eassumption | eassumption | reflexivity | reflexivity | reflexivity | exact DRNG
      | lia | lia | exact Hl32 | exact AL0 ].
    unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G6|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|].
    split. { eapply agrees_on_trans; [exact AGm5|]. eapply agrees_on_weaken; [exact AG6|]. intros a (K & _). split; [exact K| exact I]. }
    split; [exists k0, k1, k2, fj; assumption|]. split; [assumption|]. exact SHD6.
  Qed.
  End Sz1.
  Lemma np_otail : ltac:(let t := eval cbv delta [np_otail__stmt] in np_otail__stmt in exact t).
  Proof using GL FFREE7 SETF8 PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r23 r24 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_otail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  #[using="Type"] Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M (PState H hptr) B) (g : B -> Monad.M (PState H hptr) C) (s : PState H hptr) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof. intros B C f g s RNG Q ms HH. exact HH. Qed.

  (* [comment removed for export] *)
  Definition np_dshort__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r23 r27 t3 t4 t5 t6 : word)
      (c0 c2 c3 c4 c6 c8 c9 c12 c13 c14 : word) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (ws wu : word) (dw : cell) (cap len n : Z),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 c2; C8 c3; C8 c4; C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880)); C8 c6;
                           C8 c8; C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 c9; C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 ws; C8 wu; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= n <= cap)%Z -> (0 <= cap < 2^31)%Z ->
    implMG RNGx (mbind (read_fail_msg MOps (prims HO FO sites) f (Msg.trunc_captured_u cap n))
                       (fun m0 => fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, h, set_errbuf m0 p'))) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) r21 r22 r23 (Z_to_bv 64 n) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8900c) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r23 r27 t3 t4 t5 t6 c0 c2 c3 c4 c6 c8 c9 c12 c13 c14 h p' ws wu dw cap len n : ltac2:(SecDiet.SzSec.tyM 'np_dshort__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_dshort__body : ltac2:(SecDiet.SzSec.bodyP 'np_dshort__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF.
 intros CTX INV PC FRA HH HD Hd NR C31.
    np_setup GL CTX INV.
    rename HH into HH'.
    destruct (rw_cells_forget _ _ _ _ HD) as [dj HD']. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'. clear HD.
    set (POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o).
    unfold read_fail_msg. cbn [mo_bind mo_ret MOps e_ferror e_fret prims].
    apply implMG_bind_assoc.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF. zstep. zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { eapply (FERROR _ spa) with (L := L) (s := sx) (CL := CL ++ PB) (FB := FB) (FL := (FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (lo := lo) (f := f) (Af := Af);
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity ]. }
    intros r s3' RNG3 ms' PO. cbv beta in PO. (nd_pre PO 9%nat; intros FP3 av m3 E MI3' ST3 AG3 G3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); rename ndR3__ into ERRNO).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 561172)) with (Z_to_bv 64 561172) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (AG3' : agrees_on (fun a => client_keeps ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (CL ++ PB) SPA a /\ True) mm m3)
      by (eapply agrees_on_weaken; [exact AG3|]; intros a (K & _); exact K).
    assert (INV3 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNG3 sx PB dsh m3).
    { eapply (np_inv0_callee FO GIOA fflagA GL) with (Pn := fun _ => True);
        [ exact INV | lia | lia | exact FP3 | exact G3 | reflexivity | exact MI3' | exact ST3 | exact AG3'
        | intros; exact I | intros; exact I | intros; exact I
        | eapply np_frame_keep with (Pn := fun _ => True); [exact AG3'| intros; exact I| exists k0, k1, k2, fj; exact FRC] ]. }
    assert (PC3 : PCAPR (hptr:=hptr) P p' PB FB m3)
      by (eapply PCAPR_agree; [exact AG3| intros a Ha; right; left; apply in_block_app; right; exact Ha| exact PC]).
    apply (agrees_rw_cells _ _ _ _ _ AG3) in FRA; [|intros a Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HH'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HD'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
    apply (rng_fp_le _ _ _ _ FP3) in RTLS.
    repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    destruct r.
    - (* [comment removed for export] *)
      destruct (ERRNO eq_refl) as [EN2 ER]. clear ERRNO.
      unfold errmsg_for_errno. cbn [mo_bind mo_ret MOps e_last_errno e_fenter e_fret prims].
      apply implMG_errno_ll. set (e := lc_errno (ps_libc sx)) in *.
      (nd_pre (gl_tls _ _ _ GL _ _ _ _ _ _ _ G3 RTLS) 6%nat; intros T0 T47 TUNP TRNG (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) _; nd_post).
      assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
      assert (MSG : fmt_at m3 0x21b80 "error reading dump file"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x21b80 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      apply implMG_from_evtF. zstep. if_false.
      zstep. do 3 zstep. rewrite ETP.
      zstep.   (* [comment removed for export] *)
      (* [comment removed for export] *)
      pose proof ATPv_pg as TPG. pose proof atp_lin as ((TPLO & _) & _).
      assert (XX : (0 < ATP + -164 < 2 ^ 64)%Z) by (unfold ATP; atop_facts; lia).
      zstep. if_false_by (eqz_false (ATP + -164) XX).
      zstep. replace (Z.land (ATP + -164) 3) with 0%Z by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; unfold ATP; Z.div_mod_to_equations; lia).
      zstep. if_false.
      ck TUNP 4%Z 0x8903c%Z [11%Z; 12%Z].
      zstep.
      do 4 zstep. zstep.
      replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      apply evtF_done. subst POSTQ.
      eapply (np_fmt FO GIOA TP fflagA GL FFREE7 SETF8 FMT) with (pc := 0x89054%Z) (PB := PB) (dsh := dsh) (hcs' := [C8 ws; C8 wu; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)]) (dw := CB 8 dj) (e := e);
        [ left; split; [right; right; left; reflexivity| reflexivity] | exact CTX | exact INV3 | exact PC3 | exact FRA | exact HH' | reflexivity | exact HD' | reflexivity
        | lia | exact MSG | intros msg; reflexivity ].
    - (* [comment removed for export] *)
      apply implMG_retb.
      assert (MSG : fmt_at m3 0x21f40 "truncated dump file; tried to read %u captured bytes, only got %zu"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x21f40 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "truncated dump file; tried to read %u captured bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      (* [comment removed for export] *)
      (pose proof INV3 as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ _ _ _ _ AGm3 _; nd_post).
      pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G3 IFL AGm3 FXB) as AGsh3.
      (pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OHA G3 ICL IFL AGsh3 ltac:(lia)) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ HAUNP3 HARNG3 HARSH3 _; nd_post).
      apply implMG_from_evtF. zstep. if_true.
      ck0_at HAUNP3 (HA + 16)%Z; ck_go.
      zstep. zstep. rewrite (np_sx32_small cap) by lia.
      do 4 zstep. zstep. zstep.
      apply evtF_done. subst POSTQ. unfold Msg.trunc_captured_u, PCAP_ERRBUF_SIZE.
      eapply (np_snp FO GIOA TP fflagA GL FFREE7 SETF8 SNPRINTF) with (pc := 0x89088%Z) (PB := PB) (dsh := dsh) (hcs' := [C8 ws; C8 wu; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)]) (dw := CB 8 dj)
                                                                               (args := [AInt cap; AInt n]);
        [ left; split; [right; right; right; reflexivity| reflexivity] | exact CTX | exact INV3 | exact PC3 | exact FRA | exact HH' | reflexivity | exact HD' | reflexivity
        | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor] ].
  Qed.
  End Sz3.
  Lemma np_dshort : ltac:(let t := eval cbv delta [np_dshort__stmt] in np_dshort__stmt in exact t).
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r23 r27 t3 t4 t5 t6 c0 c2 c3 c4 c6 c8 c9 c12 c13 c14 h p' ws wu dw cap len n. ltac2:(SecDiet.SzSec.closeP 'np_dshort__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.


  (* [comment removed for export] *)
  #[using="Type"] Lemma discard_loop_S : forall fuel fp cap btd br,
    discard_loop MOps (prims HO FO sites) (S fuel) fp cap btd br =
    (if (btd =? 0)%Z then mret (inr tt) else
     mbind (e_fread (prims HO FO sites) fp (DStack SiteDiscardBuf 0) (if 4096 <? btd then 4096 else btd)%Z) (fun got =>
     (if negb (zlength got =? (if 4096 <? btd then 4096 else btd))%Z
      then mbind (read_fail_msg MOps (prims HO FO sites) fp (Msg.trunc_captured_u cap (br + zlength got))) (fun m0 => mret (inl m0))
      else discard_loop MOps (prims HO FO sites) fuel fp cap (btd - zlength got) (br + zlength got)))).
  Proof. intros. reflexivity. Qed.
  #[using="Type"] Lemma discard_loop_0 : forall fuel fp cap br, discard_loop MOps (prims HO FO sites) fuel fp cap 0 br = mret (inr tt).
  Proof. intros. destruct fuel; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma np_discard : forall (fuel : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 t3 t4 t5 t6 : word)
      (c0 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len btd bread : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) (repeat (Z_to_bv 8 0) (Z.to_nat 512)) mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    Forall (fun x => 0 <= x < 256)%Z data -> Z.of_nat (length data) = k_snap k -> (0 <= len < 2^32)%Z -> (0 <= cap < 2^31)%Z -> (0 < alloc)%Z ->
    (0 < btd)%Z -> (btd <= 4096 * (Z.of_nat fuel - 1))%Z -> (0 <= bread)%Z -> (bread + btd <= cap)%Z ->
    implMG RNGx (mbind (discard_loop MOps (prims HO FO sites) fuel (k_f k) cap btd bread)
                       (fun r => match r with
                                 | inl m0 => fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, mkHdr sec usec cap len, set_errbuf m0 (pv k bq bsz alloc data eb))
                                 | inr _ => (let '(hdr, d) := pcapint_post_process (k_lt k) (k_sw k) (mkHdr sec usec (k_snap k) len) data in
                                             fo_ret FO _ FF_NEXT_PACKET (1%Z, hdr, set_bufdata d (pv k bq bsz alloc data eb)))
                                 end)) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 btd) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) r21 (Z_to_bv 64 (P + 96)) (Z_to_bv 64 (Fb + 96))
               (Z_to_bv 64 bread) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x88c88) fc None mm (seg_rom asegs)).
  Proof using GL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP.
    induction fuel as [|fuel IH]; intros until dw; intros CTX INV PC FRA HH HD Hd DRNG DLEN Hl32 Hc31 AL0 Bpos Bfuel Br0 Brc.
    { exfalso. cbn [Z.of_nat] in Bfuel. lia. }
    rewrite Nat2Z.inj_succ in Bfuel.
    np_setup GL CTX INV.
    np_blocks GL G OHA ODA IFL.
    rewrite discard_loop_S. replace (btd =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    set (n := (if 4096 <? btd then 4096 else btd)%Z).
    assert (Hn : (0 < n <= 4096)%Z /\ (n <= btd)%Z /\ (n = btd \/ (n = 4096 /\ 4096 < btd))%Z) by (subst n; destruct (Z.ltb_spec 4096 btd); lia).
    clearbody n. (nd_pre Hn 3%nat; intros Hn1 Hn2 Hn3; nd_post).
    cbn [e_fread prims].
    set (POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o).
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF.
    (* [comment removed for export] *)
    do 2 zstep. zstep.
    lazymatch goal with |- evtF _ _ ?Q _ =>
      assert (K54 : forall s5v : word, s5v = Z_to_bv 64 n ->
        evtF asegs RNGx Q
          (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 4096) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 btd) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) s5v (Z_to_bv 64 (P + 96)) (Z_to_bv 64 (Fb + 96))
                   (Z_to_bv 64 bread) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) t3 t4 t5 t6)
              F (Z_to_bv 64 0x88c98) fc None mm (seg_rom asegs))) end.
    2:{ if_cases Kc; zify_cond Kc.
        - apply K54. f_equal; lia.
        - zstep. apply K54. f_equal; lia. }
    intros s5v ->.
    do 4 zstep. zstep.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs _ _ [_; _; _] (Z.to_nat 8160) _ [_] [72%nat; Z.to_nat n; (Z.to_nat 8160 - 72 - Z.to_nat n)%nat]) in FRC; [| cbn [sum_nat]; lia].
    cbn [mk_CB_cells app] in FRC.
    lazymatch type of FRC with rw_cells _ _ _ [_; _; _; CB _ ?l0; CB _ ?l1; CB _ ?l2; _] =>
      set (j0 := l0) in FRC; set (j1 := l1) in FRC; set (j2 := l2) in FRC; clearbody j0 j1 j2 end.
    destruct (rw_cells_cut _ _ _ 4 FRC) as [F0 F12]. clear FRC. cbn [firstn skipn cells_size csize Nat.add] in F0, F12.
    destruct (rw_cells_cut _ _ _ 1 F12) as [F1 F2]. clear F12. cbn [firstn skipn cells_size csize Nat.add] in F1, F2.
    lazymatch type of F1 with rw_cells _ _ ?A _ => replace A with (Fb + 96)%Z in F1, F2 by lia end.
    lazymatch type of F2 with rw_cells _ _ ?A _ => replace A with (Fb + 96 + n)%Z in F2 by lia end.
    assert (SHD' : rw_cells asegs mm (Z.shiftr (Fb + 96) 3 + 2147450880) [CB 512 (repeat (Z_to_bv 8 0) (Z.to_nat 512))]).
    { replace (Z.shiftr (Fb + 96) 3 + 2147450880)%Z with (Z.shiftr Fb 3 + 2147450892)%Z; [exact SHD|].
      change (Fb + 96)%Z with (Fb + 8 * 12)%Z. rewrite shiftr3_add by (Z.div_mod_to_equations; lia). lia. }
    pose proof (unp_of_zero_cells _ (Fb + 96)%Z 512%nat _ SHD' ltac:(cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity)
                  ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)) as UNPD.
    change (8 * Z.of_nat 512)%Z with 4096%Z in UNPD. clear SHD'.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. apply implMG_bind_assoc. eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest].
      rewrite (gl_site _ _ _ GL _ _ _ _ _ _ _ _ _ _ SiteDiscardBuf 96%Z G (or_introl eq_refl) eq_refl).
      replace (Fb + 96 + 0)%Z with (Fb + 96)%Z by lia.
      eapply (FREAD _ spa) with (Af := Af);
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact F1
        | split; [right; exists (FF_NEXT_PACKET, Fb, 8192%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia|
                               eapply unpoisoned_sub; [exact UNPD| lia| lia]] ]. }
    intros got s6' RNG6 ms' PO. cbv beta in PO.
    (nd_pre PO 11%nat; intros FP6 av m6 junk6 E OF6 MI6 ST6 AG6 G6 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 3%nat; intros GOTL GOTR HD6; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 560300)) with (Z_to_bv 64 560300) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (KFR : forall A cs, rw_cells asegs mm A cs -> (Fb <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fb + 8192)%Z ->
                   (A + Z.of_nat (cells_size cs) <= Fb + 96 \/ Fb + 96 + n <= A)%Z -> rw_cells asegs m6 A cs)
      by (intros A cs HC H1 H3 H4; eapply agrees_rw_cells; [exact AG6| exact HC|]; intros a Ha; split; [|lia];
          right; right; left; apply in_frames_In; exists (FF_NEXT_PACKET, Fb, 8192%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]).
    apply KFR in F0; [|lia|cbn [cells_size csize Nat.add]; lia|cbn [cells_size csize Nat.add]; lia].
    apply KFR in F2; [|lia|cbn [cells_size csize]; lia|cbn [cells_size csize]; lia]. clear KFR.
    assert (LG : (length got <= Z.to_nat n)%nat) by (unfold zlength in GOTL; lia).
    pose proof (rw_cells_uncut _ _ _ _ _ F0 HD6 ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
    pose proof (rw_cells_uncut _ _ _ _ _ J1 F2 ltac:(cbn [cells_size csize]; lia)) as J2. cbn [app] in J2. clear J1 F0 F2 HD6.
    apply (rw_cells_merge asegs m6 Fb [C8 k0; C8 k1; C8 k2] [_; _; _; _] [_]) in J2.
    replace (cells_size [CB 72 j0; CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk6; CB (Z.to_nat 8160 - 72 - Z.to_nat n) j2])
      with (Z.to_nat 8160) in J2 by (cbn [cells_size csize]; lia).
    cbn [app] in J2.
    assert (INV6 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNG6 s6'
                           (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) (repeat (Z_to_bv 8 0) (Z.to_nat 512)) m6).
    { eapply (np_inv0_callee FO GIOA fflagA GL) with (Pn := fun a => ~ (Fb + 96 <= a < Fb + 96 + n)%Z);
        [ exact INV | lia | lia | exact FP6 | exact G6 | exact OF6 | exact MI6 | exact ST6 | exact AG6
        | intros a Ha; lia | intros a Ha; lia | intros a _ Ha; lia
        | eexists k0, k1, k2, _; exact J2 ]. }
    assert (PC6 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m6).
    { eapply PCAPR_agree; [exact AG6| | exact PC]. intros a Ha. split; [right; left; apply in_block_app; right; exact Ha|].
      intros Hin. eapply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G);
        [ apply in_frames_In; exists (FF_NEXT_PACKET, Fb, 8192%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]
        | apply in_block_app; left; apply in_block_app; right; exact Ha ]. }
    apply (agrees_rw_cells _ _ _ _ _ AG6) in FRA; [|intros a Ha; split; [left; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG6) in HH; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL IFL)| lia]| lia]].
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    apply (agrees_rw_cells _ _ _ _ _ AG6) in HD'; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL IFL)| lia]| lia]].
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    destruct (Z.eq_dec (zlength got) n) as [LEQ|LNE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb]. rewrite LEQ.
      apply implMG_from_evtF.
      zstep. zstep. if_cases Kq; [zify_cond Kq; exfalso; lia|].
      zstep. zstep.
      destruct (Z.eq_dec (btd - n) 0) as [BZ|BNZ].
      + if_cases Kz; [zify_cond Kz; exfalso; lia|].
        apply evtF_done. replace (btd - n)%Z with 0%Z by lia. rewrite discard_loop_0. apply implMG_retb. subst POSTQ.
        eapply np_otail with (sec := sec) (usec := usec) (cap := cap) (dw := CB 8 dwj);
          [ exact CTX | exact INV6 | exact PC6 | exact FRA | exact HH | exact HD' | reflexivity | exact DRNG | exact DLEN | exact Hl32 | exact AL0 ].
      + if_cases Kz; [|zify_cond Kz; exfalso; lia].
        apply evtF_done. subst POSTQ.
        replace (n + bread)%Z with (bread + n)%Z by lia.
        eapply IH with (dw := CB 8 dwj);
          [ exact CTX | exact INV6 | exact PC6 | exact FRA | exact HH | exact HD' | reflexivity | exact DRNG | exact DLEN | exact Hl32 | exact Hc31 | exact AL0
          | lia | lia | lia | lia ].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      apply implMG_bind_assoc.
      apply implMG_from_evtF.
      zstep. zstep. if_cases Kq; [|zify_cond Kq; exfalso; lia].
      apply evtF_done. subst POSTQ.
      replace (zlength got + bread)%Z with (bread + zlength got)%Z by lia.
      eapply np_dshort with (n := (bread + zlength got)%Z) (cap := cap) (len := len) (dsh := repeat (Z_to_bv 8 0) (Z.to_nat 512)) (dw := CB 8 dwj)
                            (p' := pv k bq bsz alloc data eb) (PB := pcap_blocks (pv k bq bsz alloc data eb) P Bx 0);
        [ exact CTX | exact INV6 | exact PC6 | exact FRA | exact HH | exact HD' | reflexivity | lia | lia ].
  Qed.
End NpDisc.
End CANSEC1.
End TwB.
End F_sfnp_discA.

(* [comment removed for export] *)
Module F_sfnp_growA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA.
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

(* [comment removed for export] *)
Lemma srliw_orA : forall x s, (0 <= x < 2^31)%Z -> (0 <= s)%Z ->
  Z.lor (bv_swrap 32 (Z.shiftr (bv_wrap 32 x) s) mod 18446744073709551616) x = Z.lor x (Z.shiftr x s).
Proof.
  intros x s Hx Hs. rewrite bv_wrap32_eq, (Z.mod_small x) by lia.
  assert (R : (0 <= Z.shiftr x s <= x)%Z).
  { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 s). split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  rewrite bv_swrap32_small by lia. rewrite Z.mod_small by lia. apply Z.lor_comm.
Qed.

(* [comment removed for export] *)
Lemma pfx_realloc : forall (bsx junk : list byte) (d : list Z) (M n : nat),
  firstn (length d) bsx = map (Z_to_bv 8) d -> (Nat.min n (length d) <= M)%nat -> (M <= length bsx)%nat ->
  firstn (length (firstn n d)) (firstn M bsx ++ junk) = map (Z_to_bv 8) (firstn n d).
Proof.
  intros bsx junk d M n PFXd HM HL.
  rewrite length_firstn. rewrite firstn_app. rewrite firstn_firstn by lia.
  replace (Nat.min n (length d) - length (firstn M bsx))%nat with 0%nat by (rewrite length_firstn; lia). cbn [firstn]. rewrite app_nil_r.
  rewrite (Nat.min_l (Nat.min n (length d)) M) by lia.
  rewrite <- firstn_map, <- PFXd, firstn_firstn. reflexivity.
Qed.

Definition lor_ge_l__stmt : Prop := forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (a <= Z.lor a b)%Z.
Section Sz3.
Variables a b : ltac2:(SecDiet.SzSec.tyM 'lor_ge_l__stmt "vv" @a).
#[using="Type"] Lemma lor_ge_l__body : ltac2:(SecDiet.SzSec.bodyP 'lor_ge_l__stmt "vv").
Proof.
  intros Ha Hb.
  set (c := Z.land b (Z.lnot a)).
  assert (Hc : (0 <= c)%Z) by (subst c; apply Z.land_nonneg; left; lia).
  assert (D : Z.land a c = 0%Z).
  { subst c. rewrite Z.land_comm, <- Z.land_assoc. rewrite (Z.land_comm (Z.lnot a) a), Z.land_lnot_diag, Z.land_0_r. reflexivity. }
  assert (E : Z.lor a b = Z.lor a c).
  { apply Z.bits_inj'. intros n Hn. subst c. rewrite !Z.lor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
  rewrite E, <- Z.lxor_lor, <- Z.add_nocarry_lxor by exact D. lia.
Qed.
End Sz3.
Lemma lor_ge_l : ltac:(let t := eval cbv delta [lor_ge_l__stmt] in lor_ge_l__stmt in exact t).
Proof. intros a b. ltac2:(SecDiet.SzSec.closeP 'lor_ge_l__body "vv"). Qed.

(* [comment removed for export] *)
Definition roundup_bounds__stmt : Prop := forall cap, (1 <= cap <= 2^27)%Z -> (cap <= roundup_pow2_u32 cap <= 2^27)%Z.
Section Sz4.
Variables cap : ltac2:(SecDiet.SzSec.tyM 'roundup_bounds__stmt "v" @cap).
#[using="Type"] Lemma roundup_bounds__body : ltac2:(SecDiet.SzSec.bodyP 'roundup_bounds__stmt "v").
Proof.
  intros CAP.
 unfold roundup_pow2_u32, u32. rewrite (Z.mod_small (cap - 1)) by lia.
  assert (R0 : (0 <= cap - 1 < 2^27)%Z) by lia.
  pose proof (lor_shr_lt (cap - 1) 1 27 ltac:(lia) ltac:(lia) R0) as R1. set (n1 := Z.lor (cap - 1) (Z.shiftr (cap - 1) 1)) in *.
  pose proof (lor_shr_lt n1 2 27 ltac:(lia) ltac:(lia) R1) as R2. set (n2 := Z.lor n1 (Z.shiftr n1 2)) in *.
  pose proof (lor_shr_lt n2 4 27 ltac:(lia) ltac:(lia) R2) as R3. set (n3 := Z.lor n2 (Z.shiftr n2 4)) in *.
  pose proof (lor_shr_lt n3 8 27 ltac:(lia) ltac:(lia) R3) as R4. set (n4 := Z.lor n3 (Z.shiftr n3 8)) in *.
  pose proof (lor_shr_lt n4 16 27 ltac:(lia) ltac:(lia) R4) as R5. set (n5 := Z.lor n4 (Z.shiftr n4 16)) in *.
  pose proof (lor_ge_l (cap - 1) (Z.shiftr (cap - 1) 1) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G1. fold n1 in G1.
  pose proof (lor_ge_l n1 (Z.shiftr n1 2) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G2. fold n2 in G2.
  pose proof (lor_ge_l n2 (Z.shiftr n2 4) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G3. fold n3 in G3.
  pose proof (lor_ge_l n3 (Z.shiftr n3 8) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G4. fold n4 in G4.
  pose proof (lor_ge_l n4 (Z.shiftr n4 16) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G5. fold n5 in G5.
  rewrite Z.mod_small by lia. lia.
Qed.
End Sz4.
Lemma roundup_bounds : ltac:(let t := eval cbv delta [roundup_bounds__stmt] in roundup_bounds__stmt in exact t).
Proof. intros cap. ltac2:(SecDiet.SzSec.closeP 'roundup_bounds__body "v"). Qed.
Lemma max_snaplen_le : forall d, (max_snaplen_for_dlt d <= 134217728)%Z.
Proof. intros d. unfold max_snaplen_for_dlt, MAXIMUM_SNAPLEN. repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) end; lia. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NpRoundup.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (RNG : footprint) (cap snap : Z).
  Hypothesis CAP : (1 <= cap <= 2^27)%Z.
  Hypothesis SNAP : (1 <= snap < 2^31)%Z.

  (* [comment removed for export] *)
  Lemma np_roundup_seq :
    evtF asegs RNG (fun ms' => exists a1v a2v : word,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 snap) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                      (Z_to_bv 64 (if (snap <? roundup_pow2_u32 cap)%Z then snap else roundup_pow2_u32 cap)) s8 s9 s10 s5 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x88878) fc None m (seg_rom asegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 snap) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 cap) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8883c) fc None m (seg_rom asegs)).
  Proof using CAP SNAP.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. zstep.
    assert (R0 : (0 <= cap + -1 < 2^27)%Z) by lia.
    do 2 zstep. rewrite (srliw_orA (cap + -1) 1) by lia. pose proof (lor_shr_lt (cap + -1) 1 27 ltac:(lia) ltac:(lia) ltac:(lia)) as R1'.
    set (n1 := Z.lor (cap + -1) (Z.shiftr (cap + -1) 1)) in *.
    do 2 zstep. rewrite (srliw_orA n1 2) by lia. pose proof (lor_shr_lt n1 2 27 ltac:(lia) ltac:(lia) R1') as R2'.
    set (n2 := Z.lor n1 (Z.shiftr n1 2)) in *.
    do 2 zstep. rewrite (srliw_orA n2 4) by lia. pose proof (lor_shr_lt n2 4 27 ltac:(lia) ltac:(lia) R2') as R3'.
    set (n3 := Z.lor n2 (Z.shiftr n2 4)) in *.
    do 2 zstep. rewrite (srliw_orA n3 8) by lia. pose proof (lor_shr_lt n3 8 27 ltac:(lia) ltac:(lia) R3') as R4'.
    set (n4 := Z.lor n3 (Z.shiftr n3 8)) in *.
    do 2 zstep. rewrite (srliw_orA n4 16) by lia. pose proof (lor_shr_lt n4 16 27 ltac:(lia) ltac:(lia) R4') as R5'.
    set (n5 := Z.lor n4 (Z.shiftr n4 16)) in *.
    zstep. rewrite (bv_swrap32_small (n5 + 1)) by lia.
    assert (RU : roundup_pow2_u32 cap = (n5 + 1)%Z).
    { unfold roundup_pow2_u32, u32. rewrite (Z.mod_small (cap - 1)) by lia. replace (cap - 1)%Z with (cap + -1)%Z by lia.
      subst n1 n2 n3 n4 n5. rewrite Z.mod_small; [reflexivity| lia]. }
    rewrite RU. clearbody n1 n2 n3 n4 n5.
    zstep. if_cases Kc; zify_cond Kc.
    - replace (if (snap <? n5 + 1)%Z then snap else (n5 + 1)%Z) with (n5 + 1)%Z by (destruct (Z.ltb_spec snap (n5 + 1)); lia).
      apply evtF_done. do 2 eexists. reflexivity.
    - replace (if (snap <? n5 + 1)%Z then snap else (n5 + 1)%Z) with snap by (destruct (Z.ltb_spec snap (n5 + 1)); lia).
      zstep. apply evtF_done. do 2 eexists. reflexivity.
  Qed.
End NpRoundup.

Section NpRealloc.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.

  Definition np_realloc__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (t0 t1 t2 a2 a3 a4 a5 a6 a7 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 t3 t4 t5 t6 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (nb pc : Z)
      (A : Type) (kont : option hptr -> Monad.M (PState H hptr) A) (Q : A -> PState H hptr -> footprint -> machine_state -> Prop),
    (pc = 0x886e4 \/ pc = 0x88898)%Z ->
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    (1 <= nb < 2^29 - 2^16)%Z -> (0 < alloc)%Z ->
    (forall (q' : hptr) (A' : Z) (RNG6 : footprint) (s6' : PState H hptr) (m6 : mem) (junk6 bsx : list byte)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        fp_le RNGx RNG6 ->
        np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNG6 s6'
                (pcap_blocks (pv k q' nb nb (zfirstn nb data) eb) P A' 0) dsh m6 ->
        agrees_on (client_keeps ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (CL ++ [(k_self k, P, 664%Z)]) SPA) mm m6 ->
        firstn (length data) bsx = map b8 data -> length bsx = Z.to_nat alloc ->
        rw_cells asegs m6 A' [CB (Z.to_nat (Z.min alloc nb)) (firstn (Z.to_nat (Z.min alloc nb)) bsx); CB (Z.to_nat (nb - Z.min alloc nb)) junk6] ->
        implMG RNG6 (kont (Some q')) s6' Q
          (MS (mkR (Z_to_bv 64 pc) (Z_to_bv 64 SPA) gp tp t0' t1' t2' sp (Z_to_bv 64 SPA) (Z_to_bv 64 A') a1' a2' a3' a4' a5' a6' a7'
                   r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 t3' t4' t5' t6') F (Z_to_bv 64 pc) fc None m6 (seg_rom asegs))) ->
    implMG RNGx (mbind (prealloc HO bq nb) kont) sx Q
      (MS (mkR (Z_to_bv 64 pc) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 Bx) (Z_to_bv 64 nb) a2 a3 a4 a5 a6 a7
               r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 t3 t4 t5 t6) F (Z_to_bv 64 REALLOC_ENTRY) fc None mm (seg_rom asegs)).
  Section Sz7.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm t0 t1 t2 a2 a3 a4 a5 a6 a7 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 t3 t4 t5 t6 k bq Bx bsz alloc data eb nb pc A kont Q : ltac2:(SecDiet.SzSec.tyM 'np_realloc__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_realloc__body : ltac2:(SecDiet.SzSec.bodyP 'np_realloc__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL REALLOC RPC.
    intros HPC CTX INV PC NB AL0 KONT.
    np_setup GL CTX INV.
    np_open PC.
    assert (LBS : length bsx = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; exact (proj1 WFB)).
    (* [comment removed for export] *)
    assert (UC5 : ucallerA (depth_next_packet_op false) L mm sp s0 ra trC)
      by (eapply ucaller_keep; [exact UC| lia|]; intros a Ha;
          destruct (AG a ltac:(lia) ltac:(split; [left; lia| cbn [outside fst snd]; lia])) as [E1 _]; congruence).
    pose proof (rw_cells_nth_C8 _ _ _ 11%nat _ FR eq_refl) as BS0. pose proof (rw_cells_nth_C8 _ _ _ 12%nat _ FR eq_refl) as BRA.
    cbn [firstn cells_size csize Nat.add] in BS0, BRA.
    replace (bv_unsigned sp + -104 + Z.of_nat 88)%Z with (bv_unsigned sp - 16)%Z in BS0 by lia.
    replace (bv_unsigned sp + -104 + Z.of_nat 96)%Z with (bv_unsigned sp - 8)%Z in BRA by lia.
    assert (G' : GIOA L RNGx sx ((CL ++ [(k_self k, P, 664%Z)]) ++ (bq, Bx, alloc) :: []) FB ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) mm)
      by (rewrite <- app_assoc; exact G).
    assert (TRX : In (tp_rpc TP :: pc :: bv_unsigned ra :: trC) (al_U L)).
    { unfold traces_next_packet_op, traces_pcap_next_packet in TR. destruct TR as (_ & _ & T3 & _ & T5 & _). destruct HPC as [-> | ->]; [exact T3| exact T5]. }
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply implMG_bind.
    { eapply (REALLOC _ spa) with (L := L) (s := sx) (C1 := CL ++ [(k_self k, P, 664%Z)]) (C2 := []) (FB := FB) (FL := (FF_NEXT_PACKET, Fb, 8192%Z) :: FL)
                                 (lo := lo) (q := bq) (A := Bx) (sz := alloc) (n := nb) (bs := bsx);
        [ split; [exact G'|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold REALLOC_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | reflexivity | reflexivity | lia | exact BUF
        | eapply (unw_of_ucaller (pred (depth_next_packet_op false)));
            [ eapply (ucaller_frame _ _ _ _ _ _ _ _ _ _ pc UC5); [rewrite Hspa; lia| lia| Z.div_mod_to_equations; lia| exact BS0| exact BRA
                | reflexivity| unfold ACLIENT_LO, ACLIENT_HI; destruct HPC as [-> | ->]; lia| unfold depth_next_packet_op, depth_pcap_next_packet; cbn; lia]
            | exact RPC
            | rewrite Hspa; lia
            | rewrite unsigned_lit by (destruct HPC as [-> | ->]; lia); exact TRX
            | exact RSTK ] ]. }
    intros r s6' RNG6 ms' PO. cbv beta in PO. destruct PO as (FP6 & av & m6 & E & OF6 & MI6 & ST6 & AG6 & PO).
    destruct r as [q'|]; [|destruct PO]. destruct PO as (A' & junk6 & -> & G6 & NEW).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 pc)) with (Z_to_bv 64 pc) by (symmetry; destruct HPC as [E0|E0]; rewrite E0; apply ret_pc_even; [lia|reflexivity|lia|reflexivity]).
    rewrite app_nil_r in AG6, G6.
    assert (G6' : GIOA L RNG6 s6' (CL ++ pcap_blocks (pv k q' nb nb (zfirstn nb data) eb) P A' 0) FB ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) m6).
    { eapply GPL; [exact G6|]. change (pcap_blocks (pv k q' nb nb (zfirstn nb data) eb) P A' 0) with ([(k_self k, P, 664%Z)] ++ [(q', A', nb)]).
      rewrite app_assoc. apply Permutation.Permutation_cons_append. }
    eapply KONT; [ exact FP6 | | exact AG6 | exact PFX | exact LBS | exact NEW ].
    eapply np_inv0_callee0 with (CLx := CL ++ [(k_self k, P, 664%Z)]);
      [ exact INV | lia | exact FP6 | exact G6' | exact OF6 | exact MI6 | exact ST6 | apply incl_appl, incl_refl | exact AG6 ].
  Qed.
  End Sz7.
  Lemma np_realloc : ltac:(let t := eval cbv delta [np_realloc__stmt] in np_realloc__stmt in exact t).
  Proof using GL GPL REALLOC RPC. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm t0 t1 t2 a2 a3 a4 a5 a6 a7 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 t3 t4 t5 t6 k bq Bx bsz alloc data eb nb pc A kont Q. ltac2:(SecDiet.SzSec.closeP 'np_realloc__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpRealloc.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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

(* [comment removed for export] *)
Lemma srliw_orA : forall x s, (0 <= x < 2^31)%Z -> (0 <= s)%Z ->
  Z.lor (bv_swrap 32 (Z.shiftr (bv_wrap 32 x) s) mod 18446744073709551616) x = Z.lor x (Z.shiftr x s).
Proof.
  intros x s Hx Hs. rewrite bv_wrap32_eq, (Z.mod_small x) by lia.
  assert (R : (0 <= Z.shiftr x s <= x)%Z).
  { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 s). split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  rewrite bv_swrap32_small by lia. rewrite Z.mod_small by lia. apply Z.lor_comm.
Qed.

(* [comment removed for export] *)
Lemma pfx_realloc : forall (bsx junk : list byte) (d : list Z) (M n : nat),
  firstn (length d) bsx = map (Z_to_bv 8) d -> (Nat.min n (length d) <= M)%nat -> (M <= length bsx)%nat ->
  firstn (length (firstn n d)) (firstn M bsx ++ junk) = map (Z_to_bv 8) (firstn n d).
Proof.
  intros bsx junk d M n PFXd HM HL.
  rewrite length_firstn. rewrite firstn_app. rewrite firstn_firstn by lia.
  replace (Nat.min n (length d) - length (firstn M bsx))%nat with 0%nat by (rewrite length_firstn; lia). cbn [firstn]. rewrite app_nil_r.
  rewrite (Nat.min_l (Nat.min n (length d)) M) by lia.
  rewrite <- firstn_map, <- PFXd, firstn_firstn. reflexivity.
Qed.

Definition lor_ge_l__stmt : Prop := forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (a <= Z.lor a b)%Z.
Section Sz3.
Variables a b : ltac2:(SecDiet.SzSec.tyM 'lor_ge_l__stmt "vv" @a).
#[using="Type"] Lemma lor_ge_l__body : ltac2:(SecDiet.SzSec.bodyP 'lor_ge_l__stmt "vv").
Proof.
  intros Ha Hb.
  set (c := Z.land b (Z.lnot a)).
  assert (Hc : (0 <= c)%Z) by (subst c; apply Z.land_nonneg; left; lia).
  assert (D : Z.land a c = 0%Z).
  { subst c. rewrite Z.land_comm, <- Z.land_assoc. rewrite (Z.land_comm (Z.lnot a) a), Z.land_lnot_diag, Z.land_0_r. reflexivity. }
  assert (E : Z.lor a b = Z.lor a c).
  { apply Z.bits_inj'. intros n Hn. subst c. rewrite !Z.lor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
  rewrite E, <- Z.lxor_lor, <- Z.add_nocarry_lxor by exact D. lia.
Qed.
End Sz3.
Lemma lor_ge_l : ltac:(let t := eval cbv delta [lor_ge_l__stmt] in lor_ge_l__stmt in exact t).
Proof. intros a b. ltac2:(SecDiet.SzSec.closeP 'lor_ge_l__body "vv"). Qed.

(* [comment removed for export] *)
Definition roundup_bounds__stmt : Prop := forall cap, (1 <= cap <= 2^27)%Z -> (cap <= roundup_pow2_u32 cap <= 2^27)%Z.
Section Sz4.
Variables cap : ltac2:(SecDiet.SzSec.tyM 'roundup_bounds__stmt "v" @cap).
#[using="Type"] Lemma roundup_bounds__body : ltac2:(SecDiet.SzSec.bodyP 'roundup_bounds__stmt "v").
Proof.
  intros CAP.
 unfold roundup_pow2_u32, u32. rewrite (Z.mod_small (cap - 1)) by lia.
  assert (R0 : (0 <= cap - 1 < 2^27)%Z) by lia.
  pose proof (lor_shr_lt (cap - 1) 1 27 ltac:(lia) ltac:(lia) R0) as R1. set (n1 := Z.lor (cap - 1) (Z.shiftr (cap - 1) 1)) in *.
  pose proof (lor_shr_lt n1 2 27 ltac:(lia) ltac:(lia) R1) as R2. set (n2 := Z.lor n1 (Z.shiftr n1 2)) in *.
  pose proof (lor_shr_lt n2 4 27 ltac:(lia) ltac:(lia) R2) as R3. set (n3 := Z.lor n2 (Z.shiftr n2 4)) in *.
  pose proof (lor_shr_lt n3 8 27 ltac:(lia) ltac:(lia) R3) as R4. set (n4 := Z.lor n3 (Z.shiftr n3 8)) in *.
  pose proof (lor_shr_lt n4 16 27 ltac:(lia) ltac:(lia) R4) as R5. set (n5 := Z.lor n4 (Z.shiftr n4 16)) in *.
  pose proof (lor_ge_l (cap - 1) (Z.shiftr (cap - 1) 1) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G1. fold n1 in G1.
  pose proof (lor_ge_l n1 (Z.shiftr n1 2) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G2. fold n2 in G2.
  pose proof (lor_ge_l n2 (Z.shiftr n2 4) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G3. fold n3 in G3.
  pose proof (lor_ge_l n3 (Z.shiftr n3 8) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G4. fold n4 in G4.
  pose proof (lor_ge_l n4 (Z.shiftr n4 16) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G5. fold n5 in G5.
  rewrite Z.mod_small by lia. lia.
Qed.
End Sz4.
Lemma roundup_bounds : ltac:(let t := eval cbv delta [roundup_bounds__stmt] in roundup_bounds__stmt in exact t).
Proof. intros cap. ltac2:(SecDiet.SzSec.closeP 'roundup_bounds__body "v"). Qed.
Lemma max_snaplen_le : forall d, (max_snaplen_for_dlt d <= 134217728)%Z.
Proof. intros d. unfold max_snaplen_for_dlt, MAXIMUM_SNAPLEN. repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) end; lia. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NpRoundup.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (RNG : footprint) (cap snap : Z).
  Hypothesis CAP : (1 <= cap <= 2^27)%Z.
  Hypothesis SNAP : (1 <= snap < 2^31)%Z.

  (* [comment removed for export] *)
  Lemma np_roundup_seq :
    evtF asegs RNG (fun ms' => exists a1v a2v : word,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 snap) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                      (Z_to_bv 64 (if (snap <? roundup_pow2_u32 cap)%Z then snap else roundup_pow2_u32 cap)) s8 s10 s9 s5 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x88e04) fc None m (seg_rom asegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 snap) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 cap) s8 s10 s9 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88dc8) fc None m (seg_rom asegs)).
  Proof using CAP SNAP.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. zstep.
    assert (R0 : (0 <= cap + -1 < 2^27)%Z) by lia.
    do 2 zstep. rewrite (srliw_orA (cap + -1) 1) by lia. pose proof (lor_shr_lt (cap + -1) 1 27 ltac:(lia) ltac:(lia) ltac:(lia)) as R1'.
    set (n1 := Z.lor (cap + -1) (Z.shiftr (cap + -1) 1)) in *.
    do 2 zstep. rewrite (srliw_orA n1 2) by lia. pose proof (lor_shr_lt n1 2 27 ltac:(lia) ltac:(lia) R1') as R2'.
    set (n2 := Z.lor n1 (Z.shiftr n1 2)) in *.
    do 2 zstep. rewrite (srliw_orA n2 4) by lia. pose proof (lor_shr_lt n2 4 27 ltac:(lia) ltac:(lia) R2') as R3'.
    set (n3 := Z.lor n2 (Z.shiftr n2 4)) in *.
    do 2 zstep. rewrite (srliw_orA n3 8) by lia. pose proof (lor_shr_lt n3 8 27 ltac:(lia) ltac:(lia) R3') as R4'.
    set (n4 := Z.lor n3 (Z.shiftr n3 8)) in *.
    do 2 zstep. rewrite (srliw_orA n4 16) by lia. pose proof (lor_shr_lt n4 16 27 ltac:(lia) ltac:(lia) R4') as R5'.
    set (n5 := Z.lor n4 (Z.shiftr n4 16)) in *.
    zstep. rewrite (bv_swrap32_small (n5 + 1)) by lia.
    assert (RU : roundup_pow2_u32 cap = (n5 + 1)%Z).
    { unfold roundup_pow2_u32, u32. rewrite (Z.mod_small (cap - 1)) by lia. replace (cap - 1)%Z with (cap + -1)%Z by lia.
      subst n1 n2 n3 n4 n5. rewrite Z.mod_small; [reflexivity| lia]. }
    rewrite RU. clearbody n1 n2 n3 n4 n5.
    zstep. if_cases Kc; zify_cond Kc.
    - replace (if (snap <? n5 + 1)%Z then snap else (n5 + 1)%Z) with (n5 + 1)%Z by (destruct (Z.ltb_spec snap (n5 + 1)); lia).
      apply evtF_done. do 2 eexists. reflexivity.
    - replace (if (snap <? n5 + 1)%Z then snap else (n5 + 1)%Z) with snap by (destruct (Z.ltb_spec snap (n5 + 1)); lia).
      zstep. apply evtF_done. do 2 eexists. reflexivity.
  Qed.
End NpRoundup.

Section NpRealloc.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.

  Definition np_realloc__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (t0 t1 t2 a2 a3 a4 a5 a6 a7 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 t3 t4 t5 t6 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (nb pc : Z)
      (A : Type) (kont : option hptr -> Monad.M (PState H hptr) A) (Q : A -> PState H hptr -> footprint -> machine_state -> Prop),
    (pc = 0x88bf4 \/ pc = 0x88e24)%Z ->
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    (1 <= nb < 2^29 - 2^16)%Z -> (0 < alloc)%Z ->
    (forall (q' : hptr) (A' : Z) (RNG6 : footprint) (s6' : PState H hptr) (m6 : mem) (junk6 bsx : list byte)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        fp_le RNGx RNG6 ->
        np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNG6 s6'
                (pcap_blocks (pv k q' nb nb (zfirstn nb data) eb) P A' 0) dsh m6 ->
        agrees_on (client_keeps ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (CL ++ [(k_self k, P, 664%Z)]) SPA) mm m6 ->
        firstn (length data) bsx = map b8 data -> length bsx = Z.to_nat alloc ->
        rw_cells asegs m6 A' [CB (Z.to_nat (Z.min alloc nb)) (firstn (Z.to_nat (Z.min alloc nb)) bsx); CB (Z.to_nat (nb - Z.min alloc nb)) junk6] ->
        implMG RNG6 (kont (Some q')) s6' Q
          (MS (mkR (Z_to_bv 64 pc) (Z_to_bv 64 SPA) gp tp t0' t1' t2' sp (Z_to_bv 64 SPA) (Z_to_bv 64 A') a1' a2' a3' a4' a5' a6' a7'
                   r18 r19 r20 r21 r22 r23 r24 r26 r25 r27 t3' t4' t5' t6') F (Z_to_bv 64 pc) fc None m6 (seg_rom asegs))) ->
    implMG RNGx (mbind (prealloc HO bq nb) kont) sx Q
      (MS (mkR (Z_to_bv 64 pc) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 Bx) (Z_to_bv 64 nb) a2 a3 a4 a5 a6 a7
               r18 r19 r20 r21 r22 r23 r24 r26 r25 r27 t3 t4 t5 t6) F (Z_to_bv 64 REALLOC_ENTRY) fc None mm (seg_rom asegs)).
  Section Sz7.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm t0 t1 t2 a2 a3 a4 a5 a6 a7 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 t3 t4 t5 t6 k bq Bx bsz alloc data eb nb pc A kont Q : ltac2:(SecDiet.SzSec.tyM 'np_realloc__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_realloc__body : ltac2:(SecDiet.SzSec.bodyP 'np_realloc__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL REALLOC RPC.
 intros HPC CTX INV PC NB AL0 KONT.
    np_setup GL CTX INV.
    np_open PC.
    assert (LBS : length bsx = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; exact (proj1 WFB)).
    (* [comment removed for export] *)
    assert (UC5 : ucallerA (depth_next_packet_op false) L mm sp s0 ra trC)
      by (eapply ucaller_keep; [exact UC| lia|]; intros a Ha;
          destruct (AG a ltac:(lia) ltac:(split; [left; lia| cbn [outside fst snd]; lia])) as [E1 _]; congruence).
    pose proof (rw_cells_nth_C8 _ _ _ 11%nat _ FR eq_refl) as BS0. pose proof (rw_cells_nth_C8 _ _ _ 12%nat _ FR eq_refl) as BRA.
    cbn [firstn cells_size csize Nat.add] in BS0, BRA.
    replace (bv_unsigned sp + -104 + Z.of_nat 88)%Z with (bv_unsigned sp - 16)%Z in BS0 by lia.
    replace (bv_unsigned sp + -104 + Z.of_nat 96)%Z with (bv_unsigned sp - 8)%Z in BRA by lia.
    assert (G' : GIOA L RNGx sx ((CL ++ [(k_self k, P, 664%Z)]) ++ (bq, Bx, alloc) :: []) FB ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) mm)
      by (rewrite <- app_assoc; exact G).
    assert (TRX : In (tp_rpc TP :: pc :: bv_unsigned ra :: trC) (al_U L)).
    { unfold traces_next_packet_op, traces_pcap_next_packet in TR. destruct TR as (_ & _ & T3 & _ & T5 & _). destruct HPC as [-> | ->]; [exact T3| exact T5]. }
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply implMG_bind.
    { eapply (REALLOC _ spa) with (L := L) (s := sx) (C1 := CL ++ [(k_self k, P, 664%Z)]) (C2 := []) (FB := FB) (FL := (FF_NEXT_PACKET, Fb, 8192%Z) :: FL)
                                 (lo := lo) (q := bq) (A := Bx) (sz := alloc) (n := nb) (bs := bsx);
        [ split; [exact G'|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold REALLOC_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | reflexivity | reflexivity | lia | exact BUF
        | eapply (unw_of_ucaller (pred (depth_next_packet_op false)));
            [ eapply (ucaller_frame _ _ _ _ _ _ _ _ _ _ pc UC5); [rewrite Hspa; lia| lia| Z.div_mod_to_equations; lia| exact BS0| exact BRA
                | reflexivity| unfold ACLIENT_LO, ACLIENT_HI; destruct HPC as [-> | ->]; lia| unfold depth_next_packet_op, depth_pcap_next_packet; cbn; lia]
            | exact RPC
            | rewrite Hspa; lia
            | rewrite unsigned_lit by (destruct HPC as [-> | ->]; lia); exact TRX
            | exact RSTK ] ]. }
    intros r s6' RNG6 ms' PO. cbv beta in PO. destruct PO as (FP6 & av & m6 & E & OF6 & MI6 & ST6 & AG6 & PO).
    destruct r as [q'|]; [|destruct PO]. destruct PO as (A' & junk6 & -> & G6 & NEW).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 pc)) with (Z_to_bv 64 pc) by (symmetry; destruct HPC as [E0|E0]; rewrite E0; apply ret_pc_even; [lia|reflexivity|lia|reflexivity]).
    rewrite app_nil_r in AG6, G6.
    assert (G6' : GIOA L RNG6 s6' (CL ++ pcap_blocks (pv k q' nb nb (zfirstn nb data) eb) P A' 0) FB ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) m6).
    { eapply GPL; [exact G6|]. change (pcap_blocks (pv k q' nb nb (zfirstn nb data) eb) P A' 0) with ([(k_self k, P, 664%Z)] ++ [(q', A', nb)]).
      rewrite app_assoc. apply Permutation.Permutation_cons_append. }
    eapply KONT; [ exact FP6 | | exact AG6 | exact PFX | exact LBS | exact NEW ].
    eapply np_inv0_callee0 with (CLx := CL ++ [(k_self k, P, 664%Z)]);
      [ exact INV | lia | exact FP6 | exact G6' | exact OF6 | exact MI6 | exact ST6 | apply incl_appl, incl_refl | exact AG6 ].
  Qed.
  End Sz7.
  Lemma np_realloc : ltac:(let t := eval cbv delta [np_realloc__stmt] in np_realloc__stmt in exact t).
  Proof using GL GPL REALLOC RPC. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm t0 t1 t2 a2 a3 a4 a5 a6 a7 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 t3 t4 t5 t6 k bq Bx bsz alloc data eb nb pc A kont Q. ltac2:(SecDiet.SzSec.closeP 'np_realloc__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpRealloc.
End CANSEC1.
End TwB.
End F_sfnp_growA.

(* [comment removed for export] *)
Module F_sfnp_overA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_growA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_discA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
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
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NpOver.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.
  Hypothesis SET00 : set_shadow_stmt SET_SHADOW_00 0.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.
  Hypothesis PP : post_process_stmt.

  #[using="Type"] Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M (PState H hptr) B) (g : B -> Monad.M (PState H hptr) C) (s : PState H hptr) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof. intros B C f g s RNG Q ms HH. exact HH. Qed.

  (* [comment removed for export] *)
  Definition np_oshort__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 r27 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c12 c13 c14 : word) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell) (cap n : Z),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9;
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= n <= cap)%Z -> (0 <= cap < 2^31)%Z ->
    implMG RNGx (mbind (read_fail_msg MOps (prims HO FO sites) f (Msg.trunc_captured_d cap n))
                       (fun m0 => fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, h, set_errbuf m0 p'))) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 cap) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) r22 r23 (Z_to_bv 64 n) (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88968) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c12 c13 c14 h p' hcs' dw cap n : ltac2:(SecDiet.SzSec.tyM 'np_oshort__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_oshort__body : ltac2:(SecDiet.SzSec.bodyP 'np_oshort__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF.
    intros CTX INV PC FRA HH Hh HD Hd NR C31.
    np_setup GL CTX INV.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HH']. rewrite Hh in HH'. clear HH.
    destruct (rw_cells_forget _ _ _ _ HD) as [dj HD']. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'. clear HD.
    set (POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o).
    unfold read_fail_msg. cbn [mo_bind mo_ret MOps e_ferror e_fret prims].
    apply implMG_bind_assoc.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF. zstep. zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { eapply (FERROR _ spa) with (L := L) (s := sx) (CL := CL ++ PB) (FB := FB) (FL := (FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (lo := lo) (f := f) (Af := Af);
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity ]. }
    intros r s3' RNG3 ms' PO. cbv beta in PO. destruct PO as (FP3 & av & m3 & E & MI3' & ST3 & AG3 & G3 & -> & -> & ERRNO).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 559472)) with (Z_to_bv 64 559472) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (AG3' : agrees_on (fun a => client_keeps ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (CL ++ PB) SPA a /\ True) mm m3)
      by (eapply agrees_on_weaken; [exact AG3|]; intros a (K & _); exact K).
    assert (INV3 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNG3 sx PB dsh m3).
    { eapply (np_inv0_callee FO GIOA fflagA GL) with (Pn := fun _ => True);
        [ exact INV | lia | lia | exact FP3 | exact G3 | reflexivity | exact MI3' | exact ST3 | exact AG3'
        | intros; exact I | intros; exact I | intros; exact I
        | eapply np_frame_keep with (Pn := fun _ => True); [exact AG3'| intros; exact I| exists k0, k1, k2, fj; exact FRC] ]. }
    assert (PC3 : PCAPR (hptr:=hptr) P p' PB FB m3)
      by (eapply PCAPR_agree; [exact AG3| intros a Ha; right; left; apply in_block_app; right; exact Ha| exact PC]).
    apply (agrees_rw_cells _ _ _ _ _ AG3) in FRA; [|intros a Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HH'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HD'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
    apply (rng_fp_le _ _ _ _ FP3) in RTLS.
    repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    destruct r.
    - (* [comment removed for export] *)
      destruct (ERRNO eq_refl) as [EN2 ER]. clear ERRNO.
      unfold errmsg_for_errno. cbn [mo_bind mo_ret MOps e_last_errno e_fenter e_fret prims].
      apply implMG_errno_ll. set (e := lc_errno (ps_libc sx)) in *.
      destruct (gl_tls _ _ _ GL _ _ _ _ _ _ _ G3 RTLS) as (T0 & T47 & TUNP & TRNG & (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) & _).
      assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
      assert (MSG : fmt_at m3 0x21b80 "error reading dump file"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x21b80 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      apply implMG_from_evtF. zstep. zstep. if_false.
      zstep. do 3 zstep. rewrite ETP.
      ck TUNP 4%Z 0x8898c%Z [11%Z; 12%Z].
      zstep.
      do 4 zstep. zstep. zstep.
      replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      apply evtF_done. subst POSTQ.
      eapply (np_fmt FO GIOA TP fflagA GL FFREE7 SETF8 FMT) with (pc := 0x88aa8%Z) (PB := PB) (dsh := dsh) (hcs' := [CB 24 hj]) (dw := CB 8 dj) (e := e);
        [ left; split; [right; right; right; left; reflexivity| reflexivity] | exact CTX | exact INV3 | exact PC3 | exact FRA | exact HH' | reflexivity | exact HD' | reflexivity
        | lia | exact MSG | intros msg; reflexivity ].
    - (* [comment removed for export] *)
      apply implMG_retb.
      assert (MSG : fmt_at m3 0x21ec0 "truncated dump file; tried to read %d captured bytes, only got %zu"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x21ec0 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "truncated dump file; tried to read %d captured bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      apply implMG_from_evtF. zstep. zstep. if_true.
      do 7 zstep. zstep.
      apply evtF_done. subst POSTQ. unfold Msg.trunc_captured_d, PCAP_ERRBUF_SIZE.
      eapply (np_snp FO GIOA TP fflagA GL FFREE7 SETF8 SNPRINTF) with (pc := 0x88adc%Z) (PB := PB) (dsh := dsh) (hcs' := [CB 24 hj]) (dw := CB 8 dj)
                                                                               (args := [AInt cap; AInt n]);
        [ left; split; [right; right; right; right; reflexivity| reflexivity] | exact CTX | exact INV3 | exact PC3 | exact FRA | exact HH' | reflexivity | exact HD' | reflexivity
        | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor] ].
  Qed.
  End Sz2.
  Lemma np_oshort : ltac:(let t := eval cbv delta [np_oshort__stmt] in np_oshort__stmt in exact t).
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c12 c13 c14 h p' hcs' dw cap n. ltac2:(SecDiet.SzSec.closeP 'np_oshort__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.


  (* [comment removed for export] *)
  Definition np_oread_post__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r24 t3 t4 t5 t6 : word)
      (c0 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (got eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc got eb) P Bx 0) (repeat (Z_to_bv 8 0) (Z.to_nat 512)) mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc got eb) (pcap_blocks (pv k bq bsz alloc got eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 DA);
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    Forall (fun x => 0 <= x < 256)%Z got -> (0 <= zlength got <= k_snap k)%Z -> (k_snap k < cap)%Z -> (cap < 2^31)%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (if negb (zlength got =? k_snap k)%Z
                 then mbind (read_fail_msg MOps (prims HO FO sites) (k_f k) (Msg.trunc_captured_d (k_snap k) (zlength got)))
                            (fun m0 => fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, mkHdr sec usec cap len, set_errbuf m0 (pv k bq bsz alloc got eb)))
                 else mbind (discard_loop MOps (prims HO FO sites) (Z.to_nat ((cap - k_snap k) / 4096 + 2)) (k_f k) cap (cap - k_snap k) (k_snap k))
                            (fun r => match r with
                                      | inl m0 => fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, mkHdr sec usec cap len, set_errbuf m0 (pv k bq bsz alloc got eb))
                                      | inr _ => (let '(hdr, d) := pcapint_post_process (k_lt k) (k_sw k) (mkHdr sec usec (k_snap k) len) got in
                                                  fo_ret FO _ FF_NEXT_PACKET (1%Z, hdr, set_bufdata d (pv k bq bsz alloc got eb)))
                                      end)) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (zlength got)) a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 96)) (Z_to_bv 64 (HA + 16)) r24 (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8873c) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r24 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc got eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_oread_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_oread_post__body : ltac2:(SecDiet.SzSec.bodyP 'np_oread_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP.
    intros CTX INV PC FRA HH HD Hd GOTR GOTL SC C31 Hl32 AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    clear PRIV BUF.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    destruct (Z.eq_dec (zlength got) (k_snap k)) as [LEQ|LNE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb].
      apply implMG_from_evtF.
      ck0_at PUNP (P + 96)%Z; ck_go.
      zstep. rewrite (np_zx32_small (k_snap k)) by lia.
      zstep. replace (bv_swrap 32 (k_snap k + 0)) with (k_snap k) by (rewrite bv_swrap32_eq, Z.add_0_r, Z.mod_small by lia; lia).
      zstep. if_cases Kq; [zify_cond Kq; exfalso; first [ revert Kq; plia_cheap | lia ]|].
      ck0_at HAUNP (HA + 16)%Z; ck_go.
      zstep. rewrite (np_sx32_small cap) by lia.
      zstep. if_cases Kc; [zify_cond Kc; exfalso; first [ revert Kc; plia_cheap | lia ]|].
      do 4 zstep.
      replace ((bv_swrap 32 (cap - k_snap k) mod 18446744073709551616) mod 4294967296)%Z with (cap - k_snap k)%Z
        by (rewrite bv_swrap32_small by lia; rewrite !Z.mod_small by lia; reflexivity).
      rewrite LEQ.
      apply evtF_done. subst POSTQ.
      eapply (np_discard HO FO sites GIOA TP fflagA GL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP) with (sec := sec) (usec := usec) (len := len);
        [ exact CTX | exact INV | exact PC | exact FRA | exact HH | exact HD | exact Hd | exact GOTR | unfold zlength in LEQ; exact LEQ | exact Hl32 | lia | exact AL0
        | lia | | lia | lia ].
      rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      apply implMG_from_evtF.
      ck0_at PUNP (P + 96)%Z; ck_go.
      zstep. rewrite (np_zx32_small (k_snap k)) by lia.
      zstep. replace (bv_swrap 32 (k_snap k + 0)) with (k_snap k) by (rewrite bv_swrap32_eq, Z.add_0_r, Z.mod_small by lia; lia).
      zstep. if_cases Kq; [|zify_cond Kq; exfalso; first [ revert Kq; plia_cheap | lia ]].
      apply evtF_done. subst POSTQ.
      eapply np_oshort with (dsh := repeat (Z_to_bv 8 0) (Z.to_nat 512)) (PB := pcap_blocks (pv k bq bsz alloc got eb) P Bx 0)
                            (hcs' := [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)]);
        [ exact CTX | exact INV | exact PC | exact FRA | exact HH | reflexivity | exact HD | exact Hd | exact GOTL | lia ].
  Qed.
  End Sz3.
  Lemma np_oread_post : ltac:(let t := eval cbv delta [np_oread_post__stmt] in np_oread_post__stmt in exact t).
  Proof using GL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r24 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc got eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_oread_post__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_oread__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r23 r24 t3 t4 t5 t6 : word)
      (c0 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) (repeat (Z_to_bv 8 0) (Z.to_nat 512)) mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 DA);
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (k_snap k <= bsz)%Z -> (k_snap k < cap)%Z -> (cap < 2^31)%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (np_oread_model MOps (prims HO FO sites) (k_f k) (k_snap k) (pv k bq bsz alloc data eb) (mkHdr sec usec cap len) cap len sec usec) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 96)) r23 r24 (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x88708) fc None mm (seg_rom asegs)).
  Section Sz4.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r23 r24 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_oread__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_oread__body : ltac2:(SecDiet.SzSec.bodyP 'np_oread__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP.
    intros CTX INV PC FRA HH HD Hd Hsb Hsc C31 Hl32 AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs mm _ [] (Z.to_nat alloc) _ [] [Z.to_nat (k_snap k); (Z.to_nat alloc - Z.to_nat (k_snap k))%nat]) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF.
    destruct (rw_cells_cut _ _ _ 1 BUF) as [BD BT]. clear BUF. cbn [firstn skipn cells_size csize Nat.add] in BD, BT.
    unfold np_oread_model.
    cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_fread e_ferror e_last_errno pc_buffer pc_linktype pc_swapped pc_bufdata set_bufdata set_errbuf
         pc_self pc_rfile pc_bufsize pc_bufalloc pc_version_major pc_version_minor pc_snapshot pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv pv].
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep.
    ck0 PUNP; ck_go.
    ck0_at PUNP (P + 96)%Z; ck_go.
    zstep. rewrite (np_sx32_small (k_snap k)) by lia.
    do 2 zstep.
    zstep.
    (* [comment removed for export] *)
    pose proof (HAL _ _ _ _ _ _ _ (bq, Bx, alloc) G HinB) as EA. cbn [cb_tok cb_addr fst snd] in EA.
    assert (INP : forall a, (P <= a < P + 664)%Z -> in_block (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) a)
      by (intros a Ha; apply in_block_In; exists (k_self k, P, 664%Z); split; [apply in_or_app; right; exact HinPB| cbn [cb_addr cb_size fst snd]; lia]).
    assert (INB : forall a, (Bx <= a < Bx + alloc)%Z -> in_block (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) a)
      by (intros a Ha; apply in_block_In; exists (bq, Bx, alloc); split; [apply in_or_app; right; exact HinBB| cbn [cb_addr cb_size fst snd]; lia]).
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest]. rewrite EA. rewrite Z.add_0_r.
      eapply (FREAD _ spa) with (Af := Af);
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact BD
        | split; [left; exists (bq, Bx, alloc); split; [apply in_or_app; right; exact HinBB| cbn [cb_addr cb_size fst snd]; lia]|];
          eapply blockA_aobj; [exact BBLK| cbn [cb_addr cb_size fst snd]; lia| cbn [cb_addr cb_size fst snd]; lia| lia] ]. }
    intros got s6' RNG6 ms' PO. cbv beta in PO.
    destruct PO as (FP6 & av & m6 & junk6 & E & OF6 & MI6 & ST6 & AG6 & G6 & -> & GOTL & GOTR & HD6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 558908)) with (Z_to_bv 64 558908) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (INV6 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNG6 s6'
                           (pcap_blocks (pv k bq bsz alloc got eb) P Bx 0) (repeat (Z_to_bv 8 0) (Z.to_nat 512)) m6).
    { eapply (np_inv0_callee FO GIOA fflagA GL) with (Pn := fun a => ~ (Bx <= a < Bx + k_snap k)%Z);
        [ exact INV | lia | lia | exact FP6 | exact G6 | exact OF6 | exact MI6 | exact ST6 | exact AG6
        | intros a Ha; lia | intros a Ha; lia
        | intros a K _ Hin; eapply (keeps_not_PB FO GIOA fflagA GL); [exact G| exact IFL| | exact K|];
            [lia| apply in_block_In; exists (bq, Bx, alloc); split; [exact HinBB| cbn [cb_addr cb_size fst snd]; lia]]
        | eapply np_frame_keep; [exact AG6| intros a Ha; cbv beta; lia| exists k0, k1, k2, fj; exact FRC] ]. }
    assert (KEEP : forall A cs, rw_cells asegs mm A cs ->
              ((SPA <= A) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664) \/ (Bx + k_snap k <= A /\ A + Z.of_nat (cells_size cs) <= Bx + alloc))%Z ->
              rw_cells asegs m6 A cs).
    { intros A cs HC HX. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HX as [HX|[HX|HX]].
      - split; [left; lia| lia].
      - split; [right; left; apply INP; lia| lia].
      - split; [right; left; apply INB; lia| lia]. }
    assert (KOB : forall A n cs, rw_cells asegs mm A cs -> clocA FL CL A n -> Z.of_nat (cells_size cs) = n ->
                   (A + n <= Bx \/ Bx + k_snap k <= A)%Z -> rw_cells asegs m6 A cs)
      by (intros A n0 cs HC LOC HSz HDj; eapply agrees_rw_cells; [exact AG6| exact HC|]; intros a Ha; split; [|lia];
          eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ LOC ICL IFL)| lia]).
    apply KEEP in FRA; [| left; lia].
    apply KEEP in CELLS; [| right; left; cbn [cells_size csize Nat.add]; lia]. apply KEEP in PRIV; [| right; left; cbn [cells_size csize Nat.add]; lia].
    apply KEEP in BT; [| right; right; cbn [cells_size csize Nat.add]; lia].
    apply (KOB _ 24%Z) in HH; [|exact (proj1 OHA)|reflexivity|lia].
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    apply (KOB _ 8%Z) in HD'; [|exact (proj1 ODA)|reflexivity|lia].
    clear KEEP KOB.
    pose proof (rw_cells_uncut _ _ _ _ _ HD6 BT ltac:(cbn [cells_size csize Nat.add]; unfold zlength in GOTL; lia)) as BUF6. cbn [app] in BUF6. merge_all BUF6.
    replace (length got + (Z.to_nat (k_snap k) - length got + (Z.to_nat alloc - Z.to_nat (k_snap k) + 0)))%nat with (Z.to_nat alloc) in BUF6 by (unfold zlength in GOTL; lia).
    rewrite app_nil_r in BUF6.
    assert (PC6 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc got eb) (pcap_blocks (pv k bq bsz alloc got eb) P Bx 0) FB m6).
    { exists Afx. split; [exact HinFx|]. exists Bx, 0%Z, jx, padx, (map b8 got ++ junk6 ++ firstn (Z.to_nat alloc - Z.to_nat (k_snap k)) (skipn (Z.to_nat (k_snap k)) bsx)).
      split; [reflexivity|]. split; [exact CELLS|]. split; [exact PRIV|]. split; [unfold pv; cbn [pc_bufalloc]; exact BUF6|].
      split; [unfold pv; cbn [pc_bufdata]; replace (length got) with (length (map b8 got)) by (apply length_map);
              rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; rewrite app_nil_r; reflexivity|].
      split; [reflexivity|].
      unfold pcap_wf, pv in *. cbn [set_bufdata pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                 pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in *. unfold zlength in GOTL. repeat split; try lia; try tauto. }
    subst POSTQ.
    cbn [pc_linktype pc_swapped pc_bufdata set_bufdata set_errbuf pv].
    eapply (np_oread_post) with (sec := sec) (usec := usec) (cap := cap) (len := len) (got := got) (dw := CB 8 dwj);
      [ exact CTX | exact INV6 | exact PC6 | exact FRA | exact HH | exact HD' | reflexivity | exact GOTR | exact GOTL | exact Hsc | exact C31 | exact Hl32 | exact AL0 ].
  Qed.
  End Sz4.
  Lemma np_oread : ltac:(let t := eval cbv delta [np_oread__stmt] in np_oread__stmt in exact t).
  Proof using GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r23 r24 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_oread__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpOver.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_growA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_discA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NpOver.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.
  Hypothesis SET00 : set_shadow_stmt SET_SHADOW_00 0.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.
  Hypothesis PP : post_process_stmt.

  #[using="Type"] Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M (PState H hptr) B) (g : B -> Monad.M (PState H hptr) C) (s : PState H hptr) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof. intros B C f g s RNG Q ms HH. exact HH. Qed.

  (* [comment removed for export] *)
  Definition np_oshort__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 r27 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c12 c13 c14 : word) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell) (cap n : Z),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c8; C8 c7; C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 c9; C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= n <= cap)%Z -> (0 <= cap < 2^31)%Z ->
    implMG RNGx (mbind (read_fail_msg MOps (prims HO FO sites) f (Msg.trunc_captured_d cap n))
                       (fun m0 => fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, h, set_errbuf m0 p'))) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 cap) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) r22 r23 (Z_to_bv 64 n) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88f08) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c12 c13 c14 h p' hcs' dw cap n : ltac2:(SecDiet.SzSec.tyM 'np_oshort__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_oshort__body : ltac2:(SecDiet.SzSec.bodyP 'np_oshort__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF.
 intros CTX INV PC FRA HH Hh HD Hd NR C31.
    np_setup GL CTX INV.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HH']. rewrite Hh in HH'. clear HH.
    destruct (rw_cells_forget _ _ _ _ HD) as [dj HD']. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'. clear HD.
    set (POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o).
    unfold read_fail_msg. cbn [mo_bind mo_ret MOps e_ferror e_fret prims].
    apply implMG_bind_assoc.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF. zstep. zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { eapply (FERROR _ spa) with (L := L) (s := sx) (CL := CL ++ PB) (FB := FB) (FL := (FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (lo := lo) (f := f) (Af := Af);
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity ]. }
    intros r s3' RNG3 ms' PO. cbv beta in PO. destruct PO as (FP3 & av & m3 & E & MI3' & ST3 & AG3 & G3 & -> & -> & ERRNO).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 560912)) with (Z_to_bv 64 560912) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (AG3' : agrees_on (fun a => client_keeps ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (CL ++ PB) SPA a /\ True) mm m3)
      by (eapply agrees_on_weaken; [exact AG3|]; intros a (K & _); exact K).
    assert (INV3 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNG3 sx PB dsh m3).
    { eapply (np_inv0_callee FO GIOA fflagA GL) with (Pn := fun _ => True);
        [ exact INV | lia | lia | exact FP3 | exact G3 | reflexivity | exact MI3' | exact ST3 | exact AG3'
        | intros; exact I | intros; exact I | intros; exact I
        | eapply np_frame_keep with (Pn := fun _ => True); [exact AG3'| intros; exact I| exists k0, k1, k2, fj; exact FRC] ]. }
    assert (PC3 : PCAPR (hptr:=hptr) P p' PB FB m3)
      by (eapply PCAPR_agree; [exact AG3| intros a Ha; right; left; apply in_block_app; right; exact Ha| exact PC]).
    apply (agrees_rw_cells _ _ _ _ _ AG3) in FRA; [|intros a Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HH'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HD'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
    apply (rng_fp_le _ _ _ _ FP3) in RTLS.
    repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    destruct r.
    - (* [comment removed for export] *)
      destruct (ERRNO eq_refl) as [EN2 ER]. clear ERRNO.
      unfold errmsg_for_errno. cbn [mo_bind mo_ret MOps e_last_errno e_fenter e_fret prims].
      apply implMG_errno_ll. set (e := lc_errno (ps_libc sx)) in *.
      destruct (gl_tls _ _ _ GL _ _ _ _ _ _ _ G3 RTLS) as (T0 & T47 & TUNP & TRNG & (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) & _).
      assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
      assert (MSG : fmt_at m3 0x21b80 "error reading dump file"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x21b80 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      apply implMG_from_evtF. zstep. if_false.
      zstep. do 3 zstep. rewrite ETP.
      (* [comment removed for export] *)
      pose proof ATPv_pg as TPG. pose proof atp_lin as ((TPLO & _) & _).
      assert (XX : (0 < ATP + -164 < 2 ^ 64)%Z) by (unfold ATP; atop_facts; lia).
      zstep. if_false_by (eqz_false (ATP + -164) XX).
      zstep. replace (Z.land (ATP + -164) 3) with 0%Z by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; unfold ATP; Z.div_mod_to_equations; lia).
      zstep. if_false.
      ck TUNP 4%Z 0x88f34%Z [11%Z; 12%Z].
      zstep.
      do 4 zstep. zstep. zstep.
      replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      apply evtF_done. subst POSTQ.
      eapply (np_fmt FO GIOA TP fflagA GL FFREE7 SETF8 FMT) with (pc := 0x89054%Z) (PB := PB) (dsh := dsh) (hcs' := [CB 24 hj]) (dw := CB 8 dj) (e := e);
        [ left; split; [right; right; left; reflexivity| reflexivity] | exact CTX | exact INV3 | exact PC3 | exact FRA | exact HH' | reflexivity | exact HD' | reflexivity
        | lia | exact MSG | intros msg; reflexivity ].
    - (* [comment removed for export] *)
      apply implMG_retb.
      assert (MSG : fmt_at m3 0x21ec0 "truncated dump file; tried to read %d captured bytes, only got %zu"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x21ec0 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "truncated dump file; tried to read %d captured bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      apply implMG_from_evtF. zstep. if_true.
      do 7 zstep. zstep.
      apply evtF_done. subst POSTQ. unfold Msg.trunc_captured_d, PCAP_ERRBUF_SIZE.
      eapply (np_snp FO GIOA TP fflagA GL FFREE7 SETF8 SNPRINTF) with (pc := 0x89088%Z) (PB := PB) (dsh := dsh) (hcs' := [CB 24 hj]) (dw := CB 8 dj)
                                                                               (args := [AInt cap; AInt n]);
        [ left; split; [right; right; right; reflexivity| reflexivity] | exact CTX | exact INV3 | exact PC3 | exact FRA | exact HH' | reflexivity | exact HD' | reflexivity
        | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor] ].
  Qed.
  End Sz2.
  Lemma np_oshort : ltac:(let t := eval cbv delta [np_oshort__stmt] in np_oshort__stmt in exact t).
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c12 c13 c14 h p' hcs' dw cap n. ltac2:(SecDiet.SzSec.closeP 'np_oshort__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.


  (* [comment removed for export] *)
  Definition np_oread_post__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r24 t3 t4 t5 t6 : word)
      (c0 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (got eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc got eb) P Bx 0) (repeat (Z_to_bv 8 0) (Z.to_nat 512)) mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc got eb) (pcap_blocks (pv k bq bsz alloc got eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    Forall (fun x => 0 <= x < 256)%Z got -> (0 <= zlength got <= k_snap k)%Z -> (k_snap k < cap)%Z -> (cap < 2^31)%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (if negb (zlength got =? k_snap k)%Z
                 then mbind (read_fail_msg MOps (prims HO FO sites) (k_f k) (Msg.trunc_captured_d (k_snap k) (zlength got)))
                            (fun m0 => fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, mkHdr sec usec cap len, set_errbuf m0 (pv k bq bsz alloc got eb)))
                 else mbind (discard_loop MOps (prims HO FO sites) (Z.to_nat ((cap - k_snap k) / 4096 + 2)) (k_f k) cap (cap - k_snap k) (k_snap k))
                            (fun r => match r with
                                      | inl m0 => fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, mkHdr sec usec cap len, set_errbuf m0 (pv k bq bsz alloc got eb))
                                      | inr _ => (let '(hdr, d) := pcapint_post_process (k_lt k) (k_sw k) (mkHdr sec usec (k_snap k) len) got in
                                                  fo_ret FO _ FF_NEXT_PACKET (1%Z, hdr, set_bufdata d (pv k bq bsz alloc got eb)))
                                      end)) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (zlength got)) a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 96)) (Z_to_bv 64 (HA + 16)) r24 (Z_to_bv 64 2147450880)
               (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x88c4c) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r24 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc got eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_oread_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_oread_post__body : ltac2:(SecDiet.SzSec.bodyP 'np_oread_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP.
 intros CTX INV PC FRA HH HD Hd GOTR GOTL SC C31 Hl32 AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    clear PRIV BUF.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    destruct (Z.eq_dec (zlength got) (k_snap k)) as [LEQ|LNE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb].
      apply implMG_from_evtF.
      ck0_at PUNP (P + 96)%Z; ck_go.
      zstep. rewrite (np_zx32_small (k_snap k)) by lia.
      zstep. replace (bv_swrap 32 (k_snap k + 0)) with (k_snap k) by (rewrite bv_swrap32_eq, Z.add_0_r, Z.mod_small by lia; lia).
      zstep. if_cases Kq; [zify_cond Kq; exfalso; first [ revert Kq; plia_cheap | lia ]|].
      ck0_at HAUNP (HA + 16)%Z; ck_go.
      zstep. rewrite (np_sx32_small cap) by lia.
      zstep. if_cases Kc; [zify_cond Kc; exfalso; first [ revert Kc; plia_cheap | lia ]|].
      do 4 zstep.
      replace ((bv_swrap 32 (cap - k_snap k) mod 18446744073709551616) mod 4294967296)%Z with (cap - k_snap k)%Z
        by (rewrite bv_swrap32_small by lia; rewrite !Z.mod_small by lia; reflexivity).
      rewrite LEQ.
      apply evtF_done. subst POSTQ.
      eapply (np_discard HO FO sites GIOA TP fflagA GL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP) with (sec := sec) (usec := usec) (len := len);
        [ exact CTX | exact INV | exact PC | exact FRA | exact HH | exact HD | exact Hd | exact GOTR | unfold zlength in LEQ; exact LEQ | exact Hl32 | lia | exact AL0
        | lia | | lia | lia ].
      rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      apply implMG_from_evtF.
      ck0_at PUNP (P + 96)%Z; ck_go.
      zstep. rewrite (np_zx32_small (k_snap k)) by lia.
      zstep. replace (bv_swrap 32 (k_snap k + 0)) with (k_snap k) by (rewrite bv_swrap32_eq, Z.add_0_r, Z.mod_small by lia; lia).
      zstep. if_cases Kq; [|zify_cond Kq; exfalso; first [ revert Kq; plia_cheap | lia ]].
      apply evtF_done. subst POSTQ.
      eapply np_oshort with (dsh := repeat (Z_to_bv 8 0) (Z.to_nat 512)) (PB := pcap_blocks (pv k bq bsz alloc got eb) P Bx 0)
                            (hcs' := [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)]);
        [ exact CTX | exact INV | exact PC | exact FRA | exact HH | reflexivity | exact HD | exact Hd | exact GOTL | lia ].
  Qed.
  End Sz3.
  Lemma np_oread_post : ltac:(let t := eval cbv delta [np_oread_post__stmt] in np_oread_post__stmt in exact t).
  Proof using GL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r24 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc got eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_oread_post__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_oread__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r23 r24 t3 t4 t5 t6 : word)
      (c0 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) (repeat (Z_to_bv 8 0) (Z.to_nat 512)) mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (k_snap k <= bsz)%Z -> (k_snap k < cap)%Z -> (cap < 2^31)%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (np_oread_model MOps (prims HO FO sites) (k_f k) (k_snap k) (pv k bq bsz alloc data eb) (mkHdr sec usec cap len) cap len sec usec) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 96)) r23 r24 (Z_to_bv 64 2147450880)
               (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x88c18) fc None mm (seg_rom asegs)).
  Section Sz4.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r23 r24 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_oread__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_oread__body : ltac2:(SecDiet.SzSec.bodyP 'np_oread__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP.
 intros CTX INV PC FRA HH HD Hd Hsb Hsc C31 Hl32 AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs mm _ [] (Z.to_nat alloc) _ [] [Z.to_nat (k_snap k); (Z.to_nat alloc - Z.to_nat (k_snap k))%nat]) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF.
    destruct (rw_cells_cut _ _ _ 1 BUF) as [BD BT]. clear BUF. cbn [firstn skipn cells_size csize Nat.add] in BD, BT.
    unfold np_oread_model.
    cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_fread e_ferror e_last_errno pc_buffer pc_linktype pc_swapped pc_bufdata set_bufdata set_errbuf
         pc_self pc_rfile pc_bufsize pc_bufalloc pc_version_major pc_version_minor pc_snapshot pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv pv].
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep.
    ck0 PUNP; ck_go.
    ck0_at PUNP (P + 96)%Z; ck_go.
    zstep. rewrite (np_sx32_small (k_snap k)) by lia.
    do 2 zstep.
    zstep.
    (* [comment removed for export] *)
    pose proof (HAL _ _ _ _ _ _ _ (bq, Bx, alloc) G HinB) as EA. cbn [cb_tok cb_addr fst snd] in EA.
    assert (INP : forall a, (P <= a < P + 664)%Z -> in_block (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) a)
      by (intros a Ha; apply in_block_In; exists (k_self k, P, 664%Z); split; [apply in_or_app; right; exact HinPB| cbn [cb_addr cb_size fst snd]; lia]).
    assert (INB : forall a, (Bx <= a < Bx + alloc)%Z -> in_block (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) a)
      by (intros a Ha; apply in_block_In; exists (bq, Bx, alloc); split; [apply in_or_app; right; exact HinBB| cbn [cb_addr cb_size fst snd]; lia]).
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest]. rewrite EA. rewrite Z.add_0_r.
      eapply (FREAD _ spa) with (Af := Af);
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact BD
        | split; [left; exists (bq, Bx, alloc); split; [apply in_or_app; right; exact HinBB| cbn [cb_addr cb_size fst snd]; lia]|];
          eapply blockA_aobj; [exact BBLK| cbn [cb_addr cb_size fst snd]; lia| cbn [cb_addr cb_size fst snd]; lia| lia] ]. }
    intros got s6' RNG6 ms' PO. cbv beta in PO.
    destruct PO as (FP6 & av & m6 & junk6 & E & OF6 & MI6 & ST6 & AG6 & G6 & -> & GOTL & GOTR & HD6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 560204)) with (Z_to_bv 64 560204) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (INV6 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNG6 s6'
                           (pcap_blocks (pv k bq bsz alloc got eb) P Bx 0) (repeat (Z_to_bv 8 0) (Z.to_nat 512)) m6).
    { eapply (np_inv0_callee FO GIOA fflagA GL) with (Pn := fun a => ~ (Bx <= a < Bx + k_snap k)%Z);
        [ exact INV | lia | lia | exact FP6 | exact G6 | exact OF6 | exact MI6 | exact ST6 | exact AG6
        | intros a Ha; lia | intros a Ha; lia
        | intros a K _ Hin; eapply (keeps_not_PB FO GIOA fflagA GL); [exact G| exact IFL| | exact K|];
            [lia| apply in_block_In; exists (bq, Bx, alloc); split; [exact HinBB| cbn [cb_addr cb_size fst snd]; lia]]
        | eapply np_frame_keep; [exact AG6| intros a Ha; cbv beta; lia| exists k0, k1, k2, fj; exact FRC] ]. }
    assert (KEEP : forall A cs, rw_cells asegs mm A cs ->
              ((SPA <= A) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664) \/ (Bx + k_snap k <= A /\ A + Z.of_nat (cells_size cs) <= Bx + alloc))%Z ->
              rw_cells asegs m6 A cs).
    { intros A cs HC HX. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HX as [HX|[HX|HX]].
      - split; [left; lia| lia].
      - split; [right; left; apply INP; lia| lia].
      - split; [right; left; apply INB; lia| lia]. }
    assert (KOB : forall A n cs, rw_cells asegs mm A cs -> clocA FL CL A n -> Z.of_nat (cells_size cs) = n ->
                   (A + n <= Bx \/ Bx + k_snap k <= A)%Z -> rw_cells asegs m6 A cs)
      by (intros A n0 cs HC LOC HSz HDj; eapply agrees_rw_cells; [exact AG6| exact HC|]; intros a Ha; split; [|lia];
          eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ LOC ICL IFL)| lia]).
    apply KEEP in FRA; [| left; lia].
    apply KEEP in CELLS; [| right; left; cbn [cells_size csize Nat.add]; lia]. apply KEEP in PRIV; [| right; left; cbn [cells_size csize Nat.add]; lia].
    apply KEEP in BT; [| right; right; cbn [cells_size csize Nat.add]; lia].
    apply (KOB _ 24%Z) in HH; [|exact (proj1 OHA)|reflexivity|lia].
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    apply (KOB _ 8%Z) in HD'; [|exact (proj1 ODA)|reflexivity|lia].
    clear KEEP KOB.
    pose proof (rw_cells_uncut _ _ _ _ _ HD6 BT ltac:(cbn [cells_size csize Nat.add]; unfold zlength in GOTL; lia)) as BUF6. cbn [app] in BUF6. merge_all BUF6.
    replace (length got + (Z.to_nat (k_snap k) - length got + (Z.to_nat alloc - Z.to_nat (k_snap k) + 0)))%nat with (Z.to_nat alloc) in BUF6 by (unfold zlength in GOTL; lia).
    rewrite app_nil_r in BUF6.
    assert (PC6 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc got eb) (pcap_blocks (pv k bq bsz alloc got eb) P Bx 0) FB m6).
    { exists Afx. split; [exact HinFx|]. exists Bx, 0%Z, jx, padx, (map b8 got ++ junk6 ++ firstn (Z.to_nat alloc - Z.to_nat (k_snap k)) (skipn (Z.to_nat (k_snap k)) bsx)).
      split; [reflexivity|]. split; [exact CELLS|]. split; [exact PRIV|]. split; [unfold pv; cbn [pc_bufalloc]; exact BUF6|].
      split; [unfold pv; cbn [pc_bufdata]; replace (length got) with (length (map b8 got)) by (apply length_map);
              rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; rewrite app_nil_r; reflexivity|].
      split; [reflexivity|].
      unfold pcap_wf, pv in *. cbn [set_bufdata pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                 pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in *. unfold zlength in GOTL. repeat split; try lia; try tauto. }
    subst POSTQ.
    cbn [pc_linktype pc_swapped pc_bufdata set_bufdata set_errbuf pv].
    eapply (np_oread_post) with (sec := sec) (usec := usec) (cap := cap) (len := len) (got := got) (dw := CB 8 dwj);
      [ exact CTX | exact INV6 | exact PC6 | exact FRA | exact HH | exact HD' | reflexivity | exact GOTR | exact GOTL | exact Hsc | exact C31 | exact Hl32 | exact AL0 ].
  Qed.
  End Sz4.
  Lemma np_oread : ltac:(let t := eval cbv delta [np_oread__stmt] in np_oread__stmt in exact t).
  Proof using GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r23 r24 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_oread__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpOver.
End CANSEC1.
End TwB.
End F_sfnp_overA.

(* [comment removed for export] *)
Module F_sfnp_over2A.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_growA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_discA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_overA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NpOver2.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.
  Hypothesis SET00 : set_shadow_stmt SET_SHADOW_00 0.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.
  Hypothesis PP : post_process_stmt.

  (* [comment removed for export] *)
  Definition np_ogrow_post__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (c12 c13 c14 : word)
      (k : npk hptr) (bq q' : hptr) (Bx A' bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell)
      (Afx : Z) (jx : pcap_junk) (padx bsx junk6 : list byte),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k q' (k_snap k) (k_snap k) (zfirstn (k_snap k) data) eb) P A' 0) (repeat (Z_to_bv 8 0) (Z.to_nat 512)) mm ->
    In (k_f k, Afx, FILE_BLOCK) FB ->
    rw_cells asegs mm P (pcap_cells_gen (pv k bq bsz alloc data eb) P Bx (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jx) ->
    rw_cells asegs mm (P + PCAP_PRIV_OFF) (priv_cells (pv k bq bsz alloc data eb) 0 padx) ->
    pcap_wf (pv k bq bsz alloc data eb) ->
    firstn (length data) bsx = map b8 data -> length bsx = Z.to_nat alloc ->
    rw_cells asegs mm A' [CB (Z.to_nat (Z.min alloc (k_snap k))) (firstn (Z.to_nat (Z.min alloc (k_snap k))) bsx); CB (Z.to_nat (k_snap k - Z.min alloc (k_snap k))) junk6] ->
    rw_cells asegs mm SPA [C8 (Z_to_bv 64 (Z.shiftr (P + 20) 3 + 2147450880)); C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 DA);
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (k_snap k < cap)%Z -> (cap <= 2^27)%Z -> (0 <= len < 2^32)%Z ->
    implMG RNGx (np_oread_model MOps (prims HO FO sites) (k_f k) (k_snap k) (pv k q' (k_snap k) (k_snap k) (zfirstn (k_snap k) data) eb)
                                (mkHdr sec usec cap len) cap len sec usec) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (k_snap k)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P)
               (Z_to_bv 64 (Z.shiftr (P + 24) 3 + 2147450880)) (Z_to_bv 64 (P + 96)) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 (P + 20)) (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x886e4) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c12 c13 c14 k bq q' Bx A' bsz alloc data eb sec usec cap len dw Afx jx padx bsx junk6 : ltac2:(SecDiet.SzSec.tyM 'np_ogrow_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_ogrow_post__body : ltac2:(SecDiet.SzSec.bodyP 'np_ogrow_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP.
    intros CTX INV HinFx CELLS PRIV WF PFX LBS NEW FRA HH HD Hd Hsc C27 Hl32.
    set (nb := k_snap k) in *.
    assert (AL0 : (0 < nb)%Z) by (subst nb; pose proof WF as (W1' & _); unfold pv in W1'; cbn [pc_snapshot] in W1'; lia).
    np_setup GL CTX INV.
    np_blocks GL G OHA ODA IFL.
    unfold pv, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision
         pc_header pc_priv pk_next_pcap pk_cleanup_sf PK] in CELLS.
    unfold pv, priv_cells, sf_cells, PCAP_PRIV_OFF in PRIV. cbn [pc_priv sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    pose proof WF as WF'. unfold pcap_wf, pv in WF'.
    cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
         pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in WF'.
    destruct WF' as (W1 & W2 & W3 & W4 & _ & _ & W7 & W8 & W9 & W10 & W11 & W12 & WHS & WBB). unfold INT_MAX in W1.
    merge_all NEW. replace (Z.to_nat (Z.min alloc nb) + (Z.to_nat (nb - Z.min alloc nb) + 0))%nat with (Z.to_nat nb) in NEW by lia. rewrite app_nil_r in NEW.
    pose proof (munch_refl [(P + 20, P + 32)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep. if_false_by (eqz_false A' ltac:(lia)).
    ck0_at PUNP (P + 24)%Z; ck_go.
    zstep.
    ck0_at PUNP (P + 20)%Z; ck_go.
    zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with HH1 : rw_cells asegs _ SPA _ |- _ => rename HH1 into FRA1 end.
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] [(k_self k, P, 664%Z); (q', A', nb)] (bv_unsigned sp)) [(P + 20, P + 32)]%Z)
      by (apply Forall_cons; [|apply Forall_nil]; right; left; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m7 _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m7 _ [] (bv_unsigned sp) FW (Forall_nil _) G MU WM ltac:(lia)) as [G7 AG7];
      assert (AGm7 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(HA, HA + 24); (DA, DA + 8)]%Z a) m m7)
        by (eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG7|]; intros a (K & _); split; [exact K| exact I])
    end.
    assert (PC7 : PCAPR (hptr:=hptr) P (pv k q' nb nb (zfirstn nb data) eb) (pcap_blocks (pv k q' nb nb (zfirstn nb data) eb) P A' 0) FB m1).
    { exists Afx. split; [exact HinFx|]. exists A', 0%Z, jx, padx, (firstn (Z.to_nat (Z.min alloc nb)) bsx ++ junk6).
      split; [reflexivity|]. split; [exact CELLS|]. split; [exact PRIV|]. split; [unfold pv; cbn [pc_bufalloc]; exact NEW|].
      split; [unfold pv, zfirstn, b8; cbn [pc_bufdata]; apply pfx_realloc; [exact PFX | lia | lia]|].
      split; [reflexivity|].
      unfold pcap_wf, pv in *. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                 pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in *.
      unfold zfirstn. rewrite length_firstn. unfold INT_MAX. subst nb. repeat split; try lia; try tauto. }
    apply evtF_done. subst POSTQ.
    eapply (np_oread HO FO sites GIOA TP fflagA GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP) with (sec := sec) (usec := usec);
      [ exact CTX | | exact PC7 | exact FRA1 | exact HH | exact HD | exact Hd | lia | exact Hsc | lia | exact Hl32 | exact AL0 ].
    unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G7|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [exact AGm7|].
    split; [exists k0, k1, k2, fj; assumption|]. split; assumption.
  Qed.
  End Sz1.
  Lemma np_ogrow_post : ltac:(let t := eval cbv delta [np_ogrow_post__stmt] in np_ogrow_post__stmt in exact t).
  Proof using GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c12 c13 c14 k bq q' Bx A' bsz alloc data eb sec usec cap len dw Afx jx padx bsx junk6. ltac2:(SecDiet.SzSec.closeP 'np_ogrow_post__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.


  (* [comment removed for export] *)
  Definition np_over2__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (c0 c1 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) (repeat (Z_to_bv 8 0) (Z.to_nat 512)) mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 DA);
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (k_snap k < cap)%Z -> (cap <= 2^27)%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (np_over_model MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (mkHdr sec usec cap len) cap len sec usec) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (k_snap k)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 96)) (Z_to_bv 64 cap)
               (Z_to_bv 64 (P + 20)) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x886a4) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c0 c1 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_over2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_over2__body : ltac2:(SecDiet.SzSec.bodyP 'np_over2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF REALLOC RPC PP.
    intros CTX INV PC FRA HH HD Hd Hsc C27 Hl32 AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    unfold np_over_model, grow_buffer.
    cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_realloc pc_bufsize pc_snapshot pc_rfile pc_buffer pc_bufdata
         pc_self pc_bufalloc pc_swapped pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv pv].
    pose proof (munch_refl [(SPA, SPA + 120)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    ck0 PUNP; ck_go.
    zstep. rewrite (np_sx32_small bsz) by lia.
    zstep.
    zstep.
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(SPA, SPA + 120)]%Z) by own_ivs.
    destruct (Z.ltb_spec bsz cap) as [GROW|NOGROW].
    - (* [comment removed for export] *)
      replace (bsz <? cap)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      if_cases Kb; try (zify_cond Kb; exfalso; lia).
      zstep. zstep.
      ck0 PUNP; ck_go.
      zstep. zstep.
      zstep.
      lazymatch goal with HH1 : rw_cells asegs _ SPA _ |- _ => rename HH1 into FRA1 end.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m5 _) =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m5 _ [] (bv_unsigned sp)
                    (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FW) (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
        assert (PC5 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m5)
          by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC];
              intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a
                                    (proj2 (in_block_app _ _ _) (or_intror Ha))));
        assert (INV5 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
                               (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) (repeat (Z_to_bv 8 0) (Z.to_nat 512)) m5)
          by (unfold np_inv0, np_shadow; split; [exact FP|]; split; [exact G5|]; split; [exact OF|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
              split; [assumption|];
              split; [eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG5|]; intros a (K & _); split; [exact K| exact I]|];
              split; [exists k0, k1, k2, fj; assumption|]; split; assumption)
      end.
      apply evtF_done. apply implMG_bind_assoc.
      eapply np_realloc with (pc := 0x886e4%Z) (k := k) (bsz := bsz) (alloc := alloc) (data := data) (eb := eb) (dsh := repeat (Z_to_bv 8 0) (Z.to_nat 512));
        [ exact GL | exact GPL | exact REALLOC | exact RPC | left; reflexivity | exact CTX | exact INV5 | exact PC5 | lia | exact AL0 | ].
      intros q' A' RNG6 s6' m6 junk6 bsx' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' FP6 INV6 AG6 PFX6 LBS6 NEW6.
      apply implMG_retb. cbv beta iota.
      cbn [negb set_buffer pc_self pc_rfile pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
           pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
      assert (ICL1 : incl CL (CL ++ [(k_self k, P, 664%Z)])) by (apply incl_appl, incl_refl).
      lazymatch type of AG6 with agrees_on _ ?m5 _ =>
        assert (KP : forall A cs, rw_cells asegs m5 A cs -> (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664)%Z -> rw_cells asegs m6 A cs)
          by (intros A cs HC HX; eapply agrees_rw_cells; [exact AG6 | exact HC |]; intros a Ha; right; left; apply in_block_In;
              exists (k_self k, P, 664%Z); split; [apply in_or_app; right; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]) end.
      apply KP in CELLS; [| cbn [cells_size csize Nat.add]; lia]. apply KP in PRIV; [| cbn [cells_size csize Nat.add]; lia]. clear KP.
      apply (agrees_rw_cells _ _ _ _ _ AG6) in FRA1; [|intros a Ha; left; lia].
      apply (agrees_rw_cells _ _ _ _ _ AG6) in HH; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL1 IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
      destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
      apply (agrees_rw_cells _ _ _ _ _ AG6) in HD'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL1 IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
      subst POSTQ.
      eapply np_ogrow_post with (bq := bq) (Bx := Bx) (bsz := bsz) (alloc := alloc) (data := data) (Afx := Afx) (jx := jx) (padx := padx)
                                (bsx := bsx') (junk6 := junk6) (dw := CB 8 dwj);
        [ exact CTX | exact INV6 | exact HinFx | exact CELLS | exact PRIV | exact WF | exact PFX6 | exact LBS6 | exact NEW6 | exact FRA1 | exact HH | exact HD'
        | reflexivity | exact Hsc | exact C27 | exact Hl32 ].
    - (* [comment removed for export] *)
      replace (bsz <? cap)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      if_cases Kb; try (zify_cond Kb; exfalso; lia).
      lazymatch goal with HH1 : rw_cells asegs _ SPA _ |- _ => rename HH1 into FRA1 end.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m5 _) =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m5 _ [] (bv_unsigned sp)
                    (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FW) (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
        assert (PC5 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m5)
          by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC];
              intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a
                                    (proj2 (in_block_app _ _ _) (or_intror Ha))));
        assert (INV5 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
                               (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) (repeat (Z_to_bv 8 0) (Z.to_nat 512)) m5)
          by (unfold np_inv0, np_shadow; split; [exact FP|]; split; [exact G5|]; split; [exact OF|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
              split; [assumption|];
              split; [eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG5|]; intros a (K & _); split; [exact K| exact I]|];
              split; [exists k0, k1, k2, fj; assumption|]; split; assumption)
      end.
      apply evtF_done. apply implMG_retb. cbv beta iota. cbn [negb]. subst POSTQ.
      eapply (np_oread HO FO sites GIOA TP fflagA GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP) with (sec := sec) (usec := usec);
        [ exact CTX | exact INV5 | exact PC5 | exact FRA1 | eassumption | eassumption | exact Hd | lia | exact Hsc | lia | exact Hl32 | exact AL0 ].
  Qed.
  End Sz2.
  Lemma np_over2 : ltac:(let t := eval cbv delta [np_over2__stmt] in np_over2__stmt in exact t).
  Proof using GL HAL GPL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF REALLOC RPC PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c0 c1 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_over2__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_over__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (c0 c1 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 DA);
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (k_snap k < cap)%Z -> (cap <= 2^27)%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (np_over_model MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (mkHdr sec usec cap len) cap len sec usec) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (k_snap k)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 96)) (Z_to_bv 64 cap)
               (Z_to_bv 64 (P + 20)) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x88698) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c0 c1 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_over__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_over__body : ltac2:(SecDiet.SzSec.bodyP 'np_over__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP.
    intros CTX INV PC FRA HH HD Hd Hsc C27 Hl32 AL0.
    np_setup GL CTX INV.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    do 2 zstep. zstep.
    clear MU WM.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (SET00 _ spa) with (lo := lo) (SA := (Z.shiftr Fb 3 + 2147450892)%Z) (n := 512%Z) (old := dsh);
        [ assumption | rewrite Hspa; exact ST | rewrite Hspa; unfold FAKE_STACK; lia | lia
        | exact (proj1 (gl_rt _ _ _ GL _ _ _ _ _ _ _ G)) | exact (gl_got_memset _ _ _ GL _ _ _ _ _ _ _ G)
        | reflexivity | reflexivity | lia | lia | exact SHD
        | eapply rng_sub'; [exact FSRNG| lia] | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] | exact RIMG ]
      | ].
    cbv beta. intros ms' PO. destruct PO as (a0v & m6 & E & MUc & WMc & MIc & STc & SHD6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. unfold FAKE_STACK in MUc.
    replace (ret_pc (Z_to_bv 64 558756)) with (Z_to_bv 64 558756) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(SPA - 4096, SPA); (Z.shiftr Fb 3 + 2147450892, Z.shiftr Fb 3 + 2147450892 + 512)]%Z) by own_ivs.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m6 _ [] (bv_unsigned sp)
                (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FW) (Forall_nil _) G MUc WMc ltac:(lia)) as [G6 AG6].
    assert (PC6 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m6).
    { eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MUc| exact WMc|]; intros a _ Ha; exact Ha| | exact PC].
      intros a Ha. exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a
                            (proj2 (in_block_app _ _ _) (or_intror Ha))). }
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end. clear MUc WMc.
    subst spa. apply evtF_done. subst POSTQ.
    eapply np_over2 with (sec := sec) (usec := usec) (dw := CB 8 dwj);
      [ exact CTX | | exact PC6 | eassumption | eassumption | eassumption | reflexivity | exact Hsc | exact C27 | exact Hl32 | exact AL0 ].
    unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G6|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|].
    split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG6|]. intros a (K & _). split; [exact K| exact I]. }
    split; [exists k0, k1, k2, fj; assumption|]. split; [assumption|]. exact SHD6.
  Qed.
  End Sz3.
  Lemma np_over : ltac:(let t := eval cbv delta [np_over__stmt] in np_over__stmt in exact t).
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c0 c1 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_over__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpOver2.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_growA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_discA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_overA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NpOver2.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.
  Hypothesis SET00 : set_shadow_stmt SET_SHADOW_00 0.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.
  Hypothesis PP : post_process_stmt.

  (* [comment removed for export] *)
  Definition np_ogrow_post__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (c12 c13 c14 : word)
      (k : npk hptr) (bq q' : hptr) (Bx A' bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell)
      (Afx : Z) (jx : pcap_junk) (padx bsx junk6 : list byte),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k q' (k_snap k) (k_snap k) (zfirstn (k_snap k) data) eb) P A' 0) (repeat (Z_to_bv 8 0) (Z.to_nat 512)) mm ->
    In (k_f k, Afx, FILE_BLOCK) FB ->
    rw_cells asegs mm P (pcap_cells_gen (pv k bq bsz alloc data eb) P Bx (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jx) ->
    rw_cells asegs mm (P + PCAP_PRIV_OFF) (priv_cells (pv k bq bsz alloc data eb) 0 padx) ->
    pcap_wf (pv k bq bsz alloc data eb) ->
    firstn (length data) bsx = map b8 data -> length bsx = Z.to_nat alloc ->
    rw_cells asegs mm A' [CB (Z.to_nat (Z.min alloc (k_snap k))) (firstn (Z.to_nat (Z.min alloc (k_snap k))) bsx); CB (Z.to_nat (k_snap k - Z.min alloc (k_snap k))) junk6] ->
    rw_cells asegs mm SPA [C8 (Z_to_bv 64 (Z.shiftr (P + 20) 3 + 2147450880)); C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (k_snap k < cap)%Z -> (cap <= 2^27)%Z -> (0 <= len < 2^32)%Z ->
    implMG RNGx (np_oread_model MOps (prims HO FO sites) (k_f k) (k_snap k) (pv k q' (k_snap k) (k_snap k) (zfirstn (k_snap k) data) eb)
                                (mkHdr sec usec cap len) cap len sec usec) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (k_snap k)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P)
               (Z_to_bv 64 (Z.shiftr (P + 24) 3 + 2147450880)) (Z_to_bv 64 (P + 96)) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 (P + 20)) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x88bf4) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c12 c13 c14 k bq q' Bx A' bsz alloc data eb sec usec cap len dw Afx jx padx bsx junk6 : ltac2:(SecDiet.SzSec.tyM 'np_ogrow_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_ogrow_post__body : ltac2:(SecDiet.SzSec.bodyP 'np_ogrow_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP.
 intros CTX INV HinFx CELLS PRIV WF PFX LBS NEW FRA HH HD Hd Hsc C27 Hl32.
    set (nb := k_snap k) in *.
    assert (AL0 : (0 < nb)%Z) by (subst nb; pose proof WF as (W1' & _); unfold pv in W1'; cbn [pc_snapshot] in W1'; lia).
    np_setup GL CTX INV.
    np_blocks GL G OHA ODA IFL.
    unfold pv, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision
         pc_header pc_priv pk_next_pcap pk_cleanup_sf PK] in CELLS.
    unfold pv, priv_cells, sf_cells, PCAP_PRIV_OFF in PRIV. cbn [pc_priv sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    pose proof WF as WF'. unfold pcap_wf, pv in WF'.
    cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
         pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in WF'.
    destruct WF' as (W1 & W2 & W3 & W4 & _ & _ & W7 & W8 & W9 & W10 & W11 & W12 & WHS & WBB). unfold INT_MAX in W1.
    merge_all NEW. replace (Z.to_nat (Z.min alloc nb) + (Z.to_nat (nb - Z.min alloc nb) + 0))%nat with (Z.to_nat nb) in NEW by lia. rewrite app_nil_r in NEW.
    pose proof (munch_refl [(P + 20, P + 32)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep. if_false_by (eqz_false A' ltac:(lia)).
    ck0_at PUNP (P + 24)%Z; ck_go.
    zstep.
    ck0_at PUNP (P + 20)%Z; ck_go.
    zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with HH1 : rw_cells asegs _ SPA _ |- _ => rename HH1 into FRA1 end.
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] [(k_self k, P, 664%Z); (q', A', nb)] (bv_unsigned sp)) [(P + 20, P + 32)]%Z)
      by (apply Forall_cons; [|apply Forall_nil]; right; left; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m7 _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m7 _ [] (bv_unsigned sp) FW (Forall_nil _) G MU WM ltac:(lia)) as [G7 AG7];
      assert (AGm7 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(HA, HA + 24); (DA, DA + 8)]%Z a) m m7)
        by (eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG7|]; intros a (K & _); split; [exact K| exact I])
    end.
    assert (PC7 : PCAPR (hptr:=hptr) P (pv k q' nb nb (zfirstn nb data) eb) (pcap_blocks (pv k q' nb nb (zfirstn nb data) eb) P A' 0) FB m1).
    { exists Afx. split; [exact HinFx|]. exists A', 0%Z, jx, padx, (firstn (Z.to_nat (Z.min alloc nb)) bsx ++ junk6).
      split; [reflexivity|]. split; [exact CELLS|]. split; [exact PRIV|]. split; [unfold pv; cbn [pc_bufalloc]; exact NEW|].
      split; [unfold pv, zfirstn, b8; cbn [pc_bufdata]; apply pfx_realloc; [exact PFX | lia | lia]|].
      split; [reflexivity|].
      unfold pcap_wf, pv in *. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                 pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in *.
      unfold zfirstn. rewrite length_firstn. unfold INT_MAX. subst nb. repeat split; try lia; try tauto. }
    apply evtF_done. subst POSTQ.
    eapply (np_oread HO FO sites GIOA TP fflagA GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP) with (sec := sec) (usec := usec);
      [ exact CTX | | exact PC7 | exact FRA1 | exact HH | exact HD | exact Hd | lia | exact Hsc | lia | exact Hl32 | exact AL0 ].
    unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G7|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [exact AGm7|].
    split; [exists k0, k1, k2, fj; assumption|]. split; assumption.
  Qed.
  End Sz1.
  Lemma np_ogrow_post : ltac:(let t := eval cbv delta [np_ogrow_post__stmt] in np_ogrow_post__stmt in exact t).
  Proof using GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c12 c13 c14 k bq q' Bx A' bsz alloc data eb sec usec cap len dw Afx jx padx bsx junk6. ltac2:(SecDiet.SzSec.closeP 'np_ogrow_post__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.


  (* [comment removed for export] *)
  Definition np_over2__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (c0 c12 c13 c14 : word)   (* [comment removed for export] *)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) (repeat (Z_to_bv 8 0) (Z.to_nat 512)) mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (k_snap k < cap)%Z -> (cap <= 2^27)%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (np_over_model MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (mkHdr sec usec cap len) cap len sec usec) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (k_snap k)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 96)) (Z_to_bv 64 cap)
               (Z_to_bv 64 (P + 20)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x88bb8) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_over2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_over2__body : ltac2:(SecDiet.SzSec.bodyP 'np_over2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF REALLOC RPC PP.
 intros CTX INV PC FRA HH HD Hd Hsc C27 Hl32 AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    unfold np_over_model, grow_buffer.
    cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_realloc pc_bufsize pc_snapshot pc_rfile pc_buffer pc_bufdata
         pc_self pc_bufalloc pc_swapped pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv pv].
    pose proof (munch_refl [(SPA, SPA + 120)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    ck0 PUNP; ck_go.
    zstep. rewrite (np_sx32_small bsz) by lia.
    zstep.   (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(SPA, SPA + 120)]%Z) by own_ivs.
    destruct (Z.ltb_spec bsz cap) as [GROW|NOGROW].
    - (* [comment removed for export] *)
      replace (bsz <? cap)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      if_cases Kb; try (zify_cond Kb; exfalso; lia).
      zstep. zstep.
      ck0 PUNP; ck_go.
      zstep. zstep.
      zstep.
      lazymatch goal with HH1 : rw_cells asegs _ SPA _ |- _ => rename HH1 into FRA1 end.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m5 _) =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m5 _ [] (bv_unsigned sp)
                    (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FW) (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
        assert (PC5 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m5)
          by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC];
              intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a
                                    (proj2 (in_block_app _ _ _) (or_intror Ha))));
        assert (INV5 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
                               (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) (repeat (Z_to_bv 8 0) (Z.to_nat 512)) m5)
          by (unfold np_inv0, np_shadow; split; [exact FP|]; split; [exact G5|]; split; [exact OF|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
              split; [assumption|];
              split; [eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG5|]; intros a (K & _); split; [exact K| exact I]|];
              split; [exists k0, k1, k2, fj; assumption|]; split; assumption)
      end.
      apply evtF_done. apply implMG_bind_assoc.
      eapply np_realloc with (pc := 0x88bf4%Z) (k := k) (bsz := bsz) (alloc := alloc) (data := data) (eb := eb) (dsh := repeat (Z_to_bv 8 0) (Z.to_nat 512));
        [ exact GL | exact GPL | exact REALLOC | exact RPC | left; reflexivity | exact CTX | exact INV5 | exact PC5 | lia | exact AL0 | ].
      intros q' A' RNG6 s6' m6 junk6 bsx' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' FP6 INV6 AG6 PFX6 LBS6 NEW6.
      apply implMG_retb. cbv beta iota.
      cbn [negb set_buffer pc_self pc_rfile pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
           pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
      assert (ICL1 : incl CL (CL ++ [(k_self k, P, 664%Z)])) by (apply incl_appl, incl_refl).
      lazymatch type of AG6 with agrees_on _ ?m5 _ =>
        assert (KP : forall A cs, rw_cells asegs m5 A cs -> (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664)%Z -> rw_cells asegs m6 A cs)
          by (intros A cs HC HX; eapply agrees_rw_cells; [exact AG6 | exact HC |]; intros a Ha; right; left; apply in_block_In;
              exists (k_self k, P, 664%Z); split; [apply in_or_app; right; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]) end.
      apply KP in CELLS; [| cbn [cells_size csize Nat.add]; lia]. apply KP in PRIV; [| cbn [cells_size csize Nat.add]; lia]. clear KP.
      apply (agrees_rw_cells _ _ _ _ _ AG6) in FRA1; [|intros a Ha; left; lia].
      apply (agrees_rw_cells _ _ _ _ _ AG6) in HH; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL1 IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
      destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
      apply (agrees_rw_cells _ _ _ _ _ AG6) in HD'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL1 IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
      subst POSTQ.
      eapply np_ogrow_post with (bq := bq) (Bx := Bx) (bsz := bsz) (alloc := alloc) (data := data) (Afx := Afx) (jx := jx) (padx := padx)
                                (bsx := bsx') (junk6 := junk6) (dw := CB 8 dwj);
        [ exact CTX | exact INV6 | exact HinFx | exact CELLS | exact PRIV | exact WF | exact PFX6 | exact LBS6 | exact NEW6 | exact FRA1 | exact HH | exact HD'
        | reflexivity | exact Hsc | exact C27 | exact Hl32 ].
    - (* [comment removed for export] *)
      replace (bsz <? cap)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      if_cases Kb; try (zify_cond Kb; exfalso; lia).
      lazymatch goal with HH1 : rw_cells asegs _ SPA _ |- _ => rename HH1 into FRA1 end.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m5 _) =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m5 _ [] (bv_unsigned sp)
                    (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FW) (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
        assert (PC5 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m5)
          by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC];
              intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a
                                    (proj2 (in_block_app _ _ _) (or_intror Ha))));
        assert (INV5 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
                               (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) (repeat (Z_to_bv 8 0) (Z.to_nat 512)) m5)
          by (unfold np_inv0, np_shadow; split; [exact FP|]; split; [exact G5|]; split; [exact OF|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
              split; [assumption|];
              split; [eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG5|]; intros a (K & _); split; [exact K| exact I]|];
              split; [exists k0, k1, k2, fj; assumption|]; split; assumption)
      end.
      apply evtF_done. apply implMG_retb. cbv beta iota. cbn [negb]. subst POSTQ.
      eapply (np_oread HO FO sites GIOA TP fflagA GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP) with (sec := sec) (usec := usec);
        [ exact CTX | exact INV5 | exact PC5 | exact FRA1 | eassumption | eassumption | exact Hd | lia | exact Hsc | lia | exact Hl32 | exact AL0 ].
  Qed.
  End Sz2.
  Lemma np_over2 : ltac:(let t := eval cbv delta [np_over2__stmt] in np_over2__stmt in exact t).
  Proof using GL HAL GPL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF REALLOC RPC PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_over2__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_over__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (c0 c12 c13 c14 : word)   (* [comment removed for export] *)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (k_snap k < cap)%Z -> (cap <= 2^27)%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (np_over_model MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (mkHdr sec usec cap len) cap len sec usec) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (k_snap k)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 96)) (Z_to_bv 64 cap)
               (Z_to_bv 64 (P + 20)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x88bac) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_over__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_over__body : ltac2:(SecDiet.SzSec.bodyP 'np_over__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP.
 intros CTX INV PC FRA HH HD Hd Hsc C27 Hl32 AL0.
    np_setup GL CTX INV.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    do 2 zstep. zstep.
    clear MU WM.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (SET00 _ spa) with (lo := lo) (SA := (Z.shiftr Fb 3 + 2147450892)%Z) (n := 512%Z) (old := dsh);
        [ assumption | rewrite Hspa; exact ST | rewrite Hspa; unfold FAKE_STACK; lia | lia
        | exact (proj1 (gl_rt _ _ _ GL _ _ _ _ _ _ _ G)) | exact (gl_got_memset _ _ _ GL _ _ _ _ _ _ _ G)
        | reflexivity | reflexivity | lia | lia | exact SHD
        | eapply rng_sub'; [exact FSRNG| lia] | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] | exact RIMG ]
      | ].
    cbv beta. intros ms' PO. destruct PO as (a0v & m6 & E & MUc & WMc & MIc & STc & SHD6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. unfold FAKE_STACK in MUc.
    replace (ret_pc (Z_to_bv 64 560056)) with (Z_to_bv 64 560056) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(SPA - 4096, SPA); (Z.shiftr Fb 3 + 2147450892, Z.shiftr Fb 3 + 2147450892 + 512)]%Z) by own_ivs.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m6 _ [] (bv_unsigned sp)
                (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FW) (Forall_nil _) G MUc WMc ltac:(lia)) as [G6 AG6].
    assert (PC6 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m6).
    { eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MUc| exact WMc|]; intros a _ Ha; exact Ha| | exact PC].
      intros a Ha. exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a
                            (proj2 (in_block_app _ _ _) (or_intror Ha))). }
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end. clear MUc WMc.
    subst spa. apply evtF_done. subst POSTQ.
    eapply np_over2 with (sec := sec) (usec := usec) (dw := CB 8 dwj);
      [ exact CTX | | exact PC6 | eassumption | eassumption | eassumption | reflexivity | exact Hsc | exact C27 | exact Hl32 | exact AL0 ].
    unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G6|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|].
    split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG6|]. intros a (K & _). split; [exact K| exact I]. }
    split; [exists k0, k1, k2, fj; assumption|]. split; [assumption|]. exact SHD6.
  Qed.
  End Sz3.
  Lemma np_over : ltac:(let t := eval cbv delta [np_over__stmt] in np_over__stmt in exact t).
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_over__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpOver2.
End CANSEC1.
End TwB.
End F_sfnp_over2A.
