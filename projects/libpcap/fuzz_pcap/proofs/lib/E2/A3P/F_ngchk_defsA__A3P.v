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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_modelA.
From Stdlib Require String.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_iface_ngA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_ngchk_defsA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition ngc_shadow : list cell :=
  [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
   C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 18446744073709551603)].

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcDefs.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.

  (* [comment removed for export] *)
  Definition ngc_ctx (ra sp tp s0 : word) (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) : Prop :=
    (ATOP + 4096 <= lo)%Z /\ (lo + PCAP_L2_STACK <= bv_unsigned sp)%Z /\ (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z
    /\ tp = Z_to_bv 64 ATP /\ (bv_unsigned sp mod 16 = 0)%Z
    /\ (rng RNG lo (al_top L - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG)
    /\ ucallerA (depth_check_header true) L m sp s0 ra trC /\ traces_check_header TP true L (bv_unsigned ra) trC
    /\ nofr (frames_check_header true) FL /\ In (f, FA, FILE_BLOCK) FB
    /\ Forall (fun z => 0 <= z < 256)%Z magic /\ length magic = 4%nat
    /\ cobjA RNG m FL CL MG 4 /\ cobjA RNG m FL CL ERR 4 /\ (MG + 4 <= ERR \/ ERR + 4 <= MG)%Z
    /\ cobjA RNG m FL CL EB 256 /\ (EB + 256 <= ERR \/ ERR + 4 <= EB)%Z /\ (EB + 256 <= MG \/ MG + 4 <= EB)%Z
    /\ (ERR mod 4 = 0)%Z /\ (EB mod 8 = 0)%Z
    /\ (bv_unsigned sp - 287 <= SPA <= bv_unsigned sp - 256)%Z /\ (SPA mod 32 = 0)%Z.

  (* [comment removed for export] *)
  Definition ngc_inv (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock)
      (lo MG EB ERR SPA Fb : Z) (magic : list Z) (o : option hptr) (m : mem)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (mm : mem) : Prop :=
    fp_le RNG RNGx /\ GIOA L RNGx sx (CL ++ PB) FB ((FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL) mm /\ ps_outfile sx = o /\ mem_inv asegs mm
    /\ stk asegs mm lo SPA /\ stk asegs mm (SPA + 152) (bv_unsigned sp + -104)
    /\ rw_cells asegs mm (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m mm
    /\ rw_cells asegs mm MG (map (fun z => C1 (b8 z)) magic)
    /\ rw_cells asegs mm (Z.shiftr Fb 3 + 2147450880) ngc_shadow.

  (* [comment removed for export] *)
  Definition ngc_result (r : check_result) (av ew : word) (PB : list (@cblock hptr)) (EB : Z) (f : hptr) (mm : mem) : Prop :=
    match r with
    | CH_NotMe => av = Z_to_bv 64 0 /\ ew = Z_to_bv 64 0 /\ PB = [] /\ exists e, rw_cells asegs mm EB [CB 256 e]
    | CH_Err msg => av = Z_to_bv 64 0 /\ ew = Z_to_bv 64 1 /\ PB = []
        /\ (exists junk', rw_cells asegs mm EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'])
        /\ (Z.of_nat (length msg) < 256)%Z /\ Forall (fun z => 0 < z < 256)%Z msg
    | CH_Ok p => exists P, av = Z_to_bv 64 P /\ pre_PCAPR (hptr:=hptr) P p PB mm /\ pc_rfile p = f /\ exists e, rw_cells asegs mm EB [CB 256 e]
    end.

End NgcDefs.

(* [comment removed for export] *)
Section NgcKeepsCallee.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  #[using="Type"] Lemma ngc_keeps_up : forall (FL FL' : list fblock) (CL CL' : list (@cblock hptr)) SP SP' a,
    client_keeps FL CL SP a -> (SP' <= SP)%Z -> incl CL CL' -> incl FL FL' -> client_keeps FL' CL' SP' a.
  Proof.
    intros FL FL' CL CL' SP SP' a [K|[K|[K|K]]] HS IC IF.
    - left. lia.
    - right; left. apply in_block_In in K as (b & Hb & Hr). apply in_block_In. exists b. split; [apply IC; exact Hb| exact Hr].
    - right; right; left. eapply in_frames_incl; eassumption.
    - right; right; right. eapply in_frame_sh_incl; eassumption.
  Qed.

  #[using="tlsI FO fflagA GL"] Lemma ngc_keeps_callee : forall L RNGx sx (CLx FB : list (@cblock hptr)) fr FL m0 m1 m2 (CL : list (@cblock hptr)) SP SPA WX (Pn : Z -> Prop),
    GIOA L RNGx sx CLx FB (fr :: FL) m0 -> incl CL CLx -> (ATOP <= SPA)%Z -> (SPA <= SP)%Z ->
    agrees_on (fun a => client_keeps (fr :: FL) CLx SPA a /\ Pn a) m1 m2 ->
    (forall a, client_keeps FL CL SP a -> outside WX a -> ~ (fb_addr fr <= a < fb_addr fr + fb_size fr)%Z -> Pn a) ->
    agrees_on (fun a => client_keeps FL CL SP a /\ outside WX a) m1 m2.
  Proof.
    intros L RNGx sx CLx FB fr FL m0 m1 m2 CL SP SPA WX Pn G IC HA HS AG HP.
    eapply agrees_on_weaken; [exact AG|]. intros a (K & O). split.
    - eapply ngc_keeps_up; [exact K| exact HS| exact IC| apply incl_tl, incl_refl].
    - apply HP; [exact K| exact O|]. assert (HSP : (ATOP <= SP)%Z) by lia. exact (proj1 (keeps_not_own_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ a G IC HSP K)).
  Qed.

  #[using="Type"] Lemma ngc_ngc_keeps_callee0 : forall (CLx : list (@cblock hptr)) fr FL m1 m2 (CL : list (@cblock hptr)) SP SPA WX,
    incl CL CLx -> (SPA <= SP)%Z ->
    agrees_on (client_keeps (fr :: FL) CLx SPA) m1 m2 ->
    agrees_on (fun a => client_keeps FL CL SP a /\ outside WX a) m1 m2.
  Proof.
    intros CLx fr FL m1 m2 CL SP SPA WX IC HS AG.
    eapply agrees_on_weaken; [exact AG|]. intros a (K & O).
    eapply ngc_keeps_up; [exact K| exact HS| exact IC| apply incl_tl, incl_refl].
  Qed.
End NgcKeepsCallee.
End CANSEC1.

(* [comment removed for export] *)
Ltac ngc_setup GL CTX INV :=
  pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32);
  pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC);
  unfold PCAP_L2_STACK in BU; unfold ngc_shadow in SHC;
  lazymatch type of MGL with length ?magic = _ =>
    destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL; cbn [map] in MGc end;
  lazymatch type of ALN with (bv_unsigned ?sp mod 16 = 0)%Z => pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP end;
  destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll FND]; pose proof (Forall_inv FAll) as FRM; pose proof FRM as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR);
  cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR; clear FAll; change (Z.shiftr 64 3) with 8%Z in FSRNG, FSWR;
  pose proof (ablk_lin _ _ FBAND') as (_ & Fb0 & _ & _); (let bF := fresh "bF" in band_ind FBAND' bF);
  lazymatch type of G with ?GG _ _ _ (?CL ++ ?PB) _ ((FF_NG_CHECK_HEADER, ?Fb, _) :: ?FL) _ =>
    assert (ICL : incl CL (CL ++ PB)) by (apply incl_appl, incl_refl);
    assert (IFL : incl FL ((FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL)) by (apply incl_tl, incl_refl);
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL)) as (MGLO & MGHI);
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)) as (ERLO & ERHI);
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)) as (EBLO & EBHI);
  pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL) ltac:(lia)) as MGBAND;
  pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL) ltac:(lia)) as ERBAND;
  pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL) ltac:(lia)) as EBBAND;
  pose proof MGBAND as MGBAND'; pose proof ERBAND as ERBAND'; pose proof EBBAND as EBBAND';
  (let bM := fresh "bM" in band_ind MGBAND bM); (let bE := fresh "bE" in band_ind ERBAND bE); (let bB := fresh "bB" in band_ind EBBAND bB);
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL (incl_refl _)) ltac:(lia)) as (kM & kMr & kM1 & kM2);
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL (incl_refl _)) ltac:(lia)) as (kE & kEr & kE1 & kE2);
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL (incl_refl _)) ltac:(lia)) as (kB & kBr & kB1 & kB2);
  cbn [fb_addr fb_size fst snd] in kM1, kM2, kE1, kE2, kB1, kB2;
  lazymatch type of FRNG with rng _ ?Fb _ =>
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000
                   /\ (Fb + 64 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 8 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia) end;
  apply (rng_fp_le _ _ _ _ FP) in RSTK; apply (rng_fp_le _ _ _ _ FP) in RIMG; apply (rng_fp_le _ _ _ _ FP) in RISH; apply (rng_fp_le _ _ _ _ FP) in RTLS;
  lazymatch type of RSTK with rng ?RNGx ?lo _ => lazymatch type of SPAB with (_ <= ?SPA <= bv_unsigned ?sp - _)%Z =>
    assert (RSPW : rng RNGx lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]);
    assert (RSPA : rng RNGx SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]) end end
  end.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition ngc_shadow : list cell :=
  [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
   C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 18446744073709551603)].

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcDefs.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.

  (* [comment removed for export] *)
  Definition ngc_ctx (ra sp tp s0 : word) (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) : Prop :=
    (ATOP + 4096 <= lo)%Z /\ (lo + PCAP_L2_STACK <= bv_unsigned sp)%Z /\ (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z
    /\ tp = Z_to_bv 64 ATP /\ (bv_unsigned sp mod 16 = 0)%Z
    /\ (rng RNG lo (al_top L - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG)
    /\ ucallerA (depth_check_header true) L m sp s0 ra trC /\ traces_check_header TP true L (bv_unsigned ra) trC
    /\ nofr (frames_check_header true) FL /\ In (f, FA, FILE_BLOCK) FB
    /\ Forall (fun z => 0 <= z < 256)%Z magic /\ length magic = 4%nat
    /\ cobjA RNG m FL CL MG 4 /\ cobjA RNG m FL CL ERR 4 /\ (MG + 4 <= ERR \/ ERR + 4 <= MG)%Z
    /\ cobjA RNG m FL CL EB 256 /\ (EB + 256 <= ERR \/ ERR + 4 <= EB)%Z /\ (EB + 256 <= MG \/ MG + 4 <= EB)%Z
    /\ (ERR mod 4 = 0)%Z /\ (EB mod 8 = 0)%Z
    /\ (bv_unsigned sp - 287 <= SPA <= bv_unsigned sp - 256)%Z /\ (SPA mod 32 = 0)%Z.

  (* [comment removed for export] *)
  Definition ngc_inv (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock)
      (lo MG EB ERR SPA Fb : Z) (magic : list Z) (o : option hptr) (m : mem)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (mm : mem) : Prop :=
    fp_le RNG RNGx /\ GIOA L RNGx sx (CL ++ PB) FB ((FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL) mm /\ ps_outfile sx = o /\ mem_inv asegs mm
    /\ stk asegs mm lo SPA /\ stk asegs mm (SPA + 152) (bv_unsigned sp + -104)
    /\ rw_cells asegs mm (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m mm
    /\ rw_cells asegs mm MG (map (fun z => C1 (b8 z)) magic)
    /\ rw_cells asegs mm (Z.shiftr Fb 3 + 2147450880) ngc_shadow.

  (* [comment removed for export] *)
  Definition ngc_result (r : check_result) (av ew : word) (PB : list (@cblock hptr)) (EB : Z) (f : hptr) (mm : mem) : Prop :=
    match r with
    | CH_NotMe => av = Z_to_bv 64 0 /\ ew = Z_to_bv 64 0 /\ PB = [] /\ exists e, rw_cells asegs mm EB [CB 256 e]
    | CH_Err msg => av = Z_to_bv 64 0 /\ ew = Z_to_bv 64 1 /\ PB = []
        /\ (exists junk', rw_cells asegs mm EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'])
        /\ (Z.of_nat (length msg) < 256)%Z /\ Forall (fun z => 0 < z < 256)%Z msg
    | CH_Ok p => exists P, av = Z_to_bv 64 P /\ pre_PCAPR (hptr:=hptr) P p PB mm /\ pc_rfile p = f /\ exists e, rw_cells asegs mm EB [CB 256 e]
    end.

End NgcDefs.

(* [comment removed for export] *)
Section NgcKeepsCallee.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  #[using="Type"] Lemma ngc_keeps_up : forall (FL FL' : list fblock) (CL CL' : list (@cblock hptr)) SP SP' a,
    client_keeps FL CL SP a -> (SP' <= SP)%Z -> incl CL CL' -> incl FL FL' -> client_keeps FL' CL' SP' a.
  Proof.
    intros FL FL' CL CL' SP SP' a [K|[K|[K|K]]] HS IC IF.
    - left. lia.
    - right; left. apply in_block_In in K as (b & Hb & Hr). apply in_block_In. exists b. split; [apply IC; exact Hb| exact Hr].
    - right; right; left. eapply in_frames_incl; eassumption.
    - right; right; right. eapply in_frame_sh_incl; eassumption.
  Qed.

  #[using="tlsI FO fflagA GL"] Lemma ngc_keeps_callee : forall L RNGx sx (CLx FB : list (@cblock hptr)) fr FL m0 m1 m2 (CL : list (@cblock hptr)) SP SPA WX (Pn : Z -> Prop),
    GIOA L RNGx sx CLx FB (fr :: FL) m0 -> incl CL CLx -> (ATOP <= SPA)%Z -> (SPA <= SP)%Z ->
    agrees_on (fun a => client_keeps (fr :: FL) CLx SPA a /\ Pn a) m1 m2 ->
    (forall a, client_keeps FL CL SP a -> outside WX a -> ~ (fb_addr fr <= a < fb_addr fr + fb_size fr)%Z -> Pn a) ->
    agrees_on (fun a => client_keeps FL CL SP a /\ outside WX a) m1 m2.
  Proof.
    intros L RNGx sx CLx FB fr FL m0 m1 m2 CL SP SPA WX Pn G IC HA HS AG HP.
    eapply agrees_on_weaken; [exact AG|]. intros a (K & O). split.
    - eapply ngc_keeps_up; [exact K| exact HS| exact IC| apply incl_tl, incl_refl].
    - apply HP; [exact K| exact O|]. assert (HSP : (ATOP <= SP)%Z) by lia. exact (proj1 (keeps_not_own_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ a G IC HSP K)).
  Qed.

  #[using="Type"] Lemma ngc_ngc_keeps_callee0 : forall (CLx : list (@cblock hptr)) fr FL m1 m2 (CL : list (@cblock hptr)) SP SPA WX,
    incl CL CLx -> (SPA <= SP)%Z ->
    agrees_on (client_keeps (fr :: FL) CLx SPA) m1 m2 ->
    agrees_on (fun a => client_keeps FL CL SP a /\ outside WX a) m1 m2.
  Proof.
    intros CLx fr FL m1 m2 CL SP SPA WX IC HS AG.
    eapply agrees_on_weaken; [exact AG|]. intros a (K & O).
    eapply ngc_keeps_up; [exact K| exact HS| exact IC| apply incl_tl, incl_refl].
  Qed.
End NgcKeepsCallee.
End CANSEC1.

(* [comment removed for export] *)
Ltac ngc_setup GL CTX INV :=
  pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32);
  pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC);
  unfold PCAP_L2_STACK in BU; unfold ngc_shadow in SHC;
  lazymatch type of MGL with length ?magic = _ =>
    destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL; cbn [map] in MGc end;
  lazymatch type of ALN with (bv_unsigned ?sp mod 16 = 0)%Z => pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP end;
  destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll FND]; pose proof (Forall_inv FAll) as FRM; pose proof FRM as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR);
  cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR; clear FAll; change (Z.shiftr 64 3) with 8%Z in FSRNG, FSWR;
  pose proof (ablk_lin _ _ FBAND') as (_ & Fb0 & _ & _); (let bF := fresh "bF" in band_ind FBAND' bF);
  lazymatch type of G with ?GG _ _ _ (?CL ++ ?PB) _ ((FF_NG_CHECK_HEADER, ?Fb, _) :: ?FL) _ =>
    assert (ICL : incl CL (CL ++ PB)) by (apply incl_appl, incl_refl);
    assert (IFL : incl FL ((FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL)) by (apply incl_tl, incl_refl);
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL)) as (MGLO & MGHI);
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)) as (ERLO & ERHI);
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)) as (EBLO & EBHI);
  pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL) ltac:(lia)) as MGBAND;
  pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL) ltac:(lia)) as ERBAND;
  pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL) ltac:(lia)) as EBBAND;
  pose proof MGBAND as MGBAND'; pose proof ERBAND as ERBAND'; pose proof EBBAND as EBBAND';
  (let bM := fresh "bM" in band_ind MGBAND bM); (let bE := fresh "bE" in band_ind ERBAND bE); (let bB := fresh "bB" in band_ind EBBAND bB);
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL (incl_refl _)) ltac:(lia)) as (kM & kMr & kM1 & kM2);
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL (incl_refl _)) ltac:(lia)) as (kE & kEr & kE1 & kE2);
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL (incl_refl _)) ltac:(lia)) as (kB & kBr & kB1 & kB2);
  cbn [fb_addr fb_size fst snd] in kM1, kM2, kE1, kE2, kB1, kB2;
  lazymatch type of FRNG with rng _ ?Fb _ =>
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000
                   /\ (Fb + 64 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 8 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia) end;
  apply (rng_fp_le _ _ _ _ FP) in RSTK; apply (rng_fp_le _ _ _ _ FP) in RIMG; apply (rng_fp_le _ _ _ _ FP) in RISH; apply (rng_fp_le _ _ _ _ FP) in RTLS;
  lazymatch type of RSTK with rng ?RNGx ?lo _ => lazymatch type of SPAB with (_ <= ?SPA <= bv_unsigned ?sp - _)%Z =>
    assert (RSPW : rng RNGx lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]);
    assert (RSPA : rng RNGx SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]) end end
  end.

(* [comment removed for export] *)
Local Open Scope list_scope. Local Open Scope Z_scope.
Lemma ngc_tr_a3 : forall (TP : tparams) (L : alayout) (ra : Z) (trC : list Z), traces_pcap_ng_check_header TP L ra trC ->
    traces_fmt_errmsg TP L 0x8ae18 (ra :: trC) /\
    traces_fmt_errmsg TP L 0x8ae94 (ra :: trC) /\
    traces_open_offline_common TP L 0x8afac (ra :: trC) /\
    In (AMALLOC_PC :: 0x8b0c4 :: (ra :: trC)) (al_U L) /\
    traces_read_bytes TP L 0x8b1b0 (ra :: trC) /\
    traces_read_block TP L 0x8b2d8 (ra :: trC) /\
    In (AFREE_PC :: 0x8b51c :: (ra :: trC)) (al_U L) /\
    In (AFREE_PC :: 0x8b554 :: (ra :: trC)) (al_U L) /\
    In (AFREE_PC :: 0x8b5e0 :: (ra :: trC)) (al_U L) /\
    In (AFREE_PC :: 0x8b5f8 :: (ra :: trC)) (al_U L) /\
    In (AFREE_PC :: 0x8b600 :: (ra :: trC)) (al_U L) /\
    traces_add_interface TP L 0x8b3c0 (ra :: trC) /\
    traces_linktype_to_dlt TP L 0x8b3dc (ra :: trC) /\
    traces_adjust_snapshot TP L 0x8b414 (ra :: trC) /\
    traces_max_snaplen TP L 0x8b460 (ra :: trC) /\
    traces_max_snaplen TP L 0x8b498 (ra :: trC).
Proof.
  intros TP L ra trC (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16).
  repeat (split; [assumption|]). assumption.
Qed.
End TwB.
End F_ngchk_defsA.

(* [comment removed for export] *)
Module F_ngchk_epiA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.
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
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Lemma land_m32N : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcEpi.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.

  Definition ngc_epi__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CLc PB FB : list (@cblock hptr)) (FL : list fblock) (lo SPA Fb : Z) (m : mem)
      (ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 r24 r26 t3 t4 t5 t6 : word)
      (jS : list byte) (k0 k1 k2 : word) (fj : list byte) (b0 b1 b2 b3 b4 b5 b6 b7 : byte)
      (A : Type) (x : A),
    (bv_unsigned sp - 287 <= SPA <= bv_unsigned sp - 256)%Z -> (SPA mod 32 = 0)%Z -> (ATOP + 4096 <= lo)%Z -> (lo <= SPA)%Z ->
    (bv_unsigned sp + 16 < al_top L)%Z -> (al_top L <= 2^47)%Z ->
    GIOA L RNG s (CLc ++ PB) FB ((FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL) m -> mem_inv asegs m ->
    stk asegs m lo SPA -> stk asegs m (SPA + 152) (bv_unsigned sp + -104) ->
    rw_cells asegs m SPA [CB 152 jS] ->
    rw_cells asegs m (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m Fb [C8 k0; C8 k1; C8 k2; CB 32 fj; C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7] ->
    rng RNG lo (al_top L - lo) ->
    implMG RNG (fo_ret FO _ FF_NG_CHECK_HEADER x) s
      (fun r s' RNG' ms' => r = x /\ RNG' = RNG /\ exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 av a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m' /\ agrees_on (fun a => in_block (CLc ++ PB) a) m m'
           /\ GIOA L RNG s' (CLc ++ PB) FB FL m' /\ ps_outfile s' = ps_outfile s)
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 sp r9 av a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 r20 r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r26 (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b490) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CLc PB FB FL lo SPA Fb m ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 r24 r26 t3 t4 t5 t6 jS k0 k1 k2 fj b0 b1 b2 b3 b4 b5 b6 b7 A x : ltac2:(SecDiet.SzSec.tyM 'ngc_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="tlsI GL FRET"] Lemma ngc_epi__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros SPAB SPA32 LO LOS SPT TOP47 G MI ST STG FRA FR FRC SHC RSTK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. pose proof (Forall_inv FAll) as (FBAND & FTOP & F64 & _ & FRNG & FSRNG & _ & _).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64, FRNG, FSRNG. clear FAll. change (Z.shiftr 64 3) with 8%Z in FSRNG.
    pose proof (ablk_lin _ _ FBAND) as (_ & Fb0 & _ & _). band_ind FBAND bF.
    destruct (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G) as (_ & FLR & FLB & FLT & _ & (kF & kFr & kF1 & kF2)). band_ind FLB bG.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000
                   /\ (Fb + 64 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 8 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    assert (FW : Forall (own_ivA [(FF_NG_CHECK_HEADER, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z) by own_ivs.
    pose proof (munch_refl [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    zstep. neg_lits.
    do 2 zstep.
    do 3 zstep.
    zstep. if_false_by (eqz_false Fb ltac:(lia)).
    zstep. neg_lits.
    do 4 zstep. zstep_sh0. do 3 zstep.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ (Forall_impl _ (own_ivA_PB _ PB _) FW) (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
      assert (AGP5 : agrees_on (fun a => in_block (CLc ++ PB) a) m mm)
        by (eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha;
            exact (pb_outside _ _ _ GL _ _ _ [] (CLc ++ PB) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a Ha));
      pose proof (munch_refl [(fflagA L FF_NG_CHECK_HEADER Fb, fflagA L FF_NG_CHECK_HEADER Fb + 1)]%Z mm) as MU2; pose proof (wmono_refl asegs mm) as WM2
    end.
    destruct (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G5) as (FLC & _).
    clear MU WM.
    zstep.
    apply evtF_done. eapply FRET; [exact G5 | unfold ff_class; lia | exact MU2 | exact WM2 | exact FLC |].
    intros s3' G6 OF3 LC3 TL3.
    clear FRNG FSRNG FLR kF kFr kF1 kF2 bF bFr bFhi bFlo bFimg bG bGr bGhi bGlo bGimg SHLO.
    zstep.
    do 16 zstep.
    release_frame FRA ST (SPA + 152)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST STG ltac:(lia)) as ST3. clear ST STG.
    release_frame FR ST3 (bv_unsigned sp).
    destruct (flag_keeps _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ CLc (bv_unsigned sp) G5 MU2 WM2 (incl_appl _ (incl_refl _)) ltac:(lia)) as [AG6 AGP6].
    apply evtF_done. subst POSTQ. cbv beta iota.
    split; [reflexivity|]. split; [reflexivity|].
    do 14 eexists. lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end.
    split; [reflexivity|]. split; [assumption|]. split; [exact ST3|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a K; split; [exact K| exact I] | exact AG6]. }
    split. { eapply agrees_on_trans; [exact AGP5| exact AGP6]. }
    split; [exact G6| exact OF3].
  Qed.
  End Sz2.
  #[using="tlsI GL FRET"] Lemma ngc_epi : ltac:(let t := eval cbv delta [ngc_epi__stmt] in ngc_epi__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CLc PB FB FL lo SPA Fb m ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 r24 r26 t3 t4 t5 t6 jS k0 k1 k2 fj b0 b1 b2 b3 b4 b5 b6 b7 A x. ltac2:(SecDiet.SzSec.closeP 'ngc_epi__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcEpi.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB.
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
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Lemma land_m32N : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcEpi.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.

  Definition ngc_epi__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CLc PB FB : list (@cblock hptr)) (FL : list fblock) (lo SPA Fb : Z) (m : mem)
      (ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 r24 r26 t3 t4 t5 t6 : word)
      (jS : list byte) (k0 k1 k2 : word) (fj : list byte) (b0 b1 b2 b3 b4 b5 b6 b7 : byte)
      (A : Type) (x : A),
    (bv_unsigned sp - 287 <= SPA <= bv_unsigned sp - 256)%Z -> (SPA mod 32 = 0)%Z -> (ATOP + 4096 <= lo)%Z -> (lo <= SPA)%Z ->
    (bv_unsigned sp + 16 < al_top L)%Z -> (al_top L <= 2^47)%Z ->
    GIOA L RNG s (CLc ++ PB) FB ((FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL) m -> mem_inv asegs m ->
    stk asegs m lo SPA -> stk asegs m (SPA + 152) (bv_unsigned sp + -104) ->
    rw_cells asegs m SPA [CB 152 jS] ->
    rw_cells asegs m (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m Fb [C8 k0; C8 k1; C8 k2; CB 32 fj; C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7] ->
    rng RNG lo (al_top L - lo) ->
    implMG RNG (fo_ret FO _ FF_NG_CHECK_HEADER x) s
      (fun r s' RNG' ms' => r = x /\ RNG' = RNG /\ exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 av a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m' /\ agrees_on (fun a => in_block (CLc ++ PB) a) m m'
           /\ GIOA L RNG s' (CLc ++ PB) FB FL m' /\ ps_outfile s' = ps_outfile s)
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 sp r9 av a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 r20 r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r26 (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b614) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CLc PB FB FL lo SPA Fb m ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 r24 r26 t3 t4 t5 t6 jS k0 k1 k2 fj b0 b1 b2 b3 b4 b5 b6 b7 A x : ltac2:(SecDiet.SzSec.tyM 'ngc_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="tlsI GL FRET"] Lemma ngc_epi__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros SPAB SPA32 LO LOS SPT TOP47 G MI ST STG FRA FR FRC SHC RSTK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. pose proof (Forall_inv FAll) as (FBAND & FTOP & F64 & _ & FRNG & FSRNG & _ & _).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64, FRNG, FSRNG. clear FAll. change (Z.shiftr 64 3) with 8%Z in FSRNG.
    pose proof (ablk_lin _ _ FBAND) as (_ & Fb0 & _ & _). band_ind FBAND bF.
    destruct (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G) as (_ & FLR & FLB & FLT & _ & (kF & kFr & kF1 & kF2)). band_ind FLB bG.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000
                   /\ (Fb + 64 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 8 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    assert (FW : Forall (own_ivA [(FF_NG_CHECK_HEADER, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z) by own_ivs.
    pose proof (munch_refl [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    zstep. neg_lits.
    do 2 zstep.
    do 3 zstep.
    zstep. if_false_by (eqz_false Fb ltac:(lia)).
    zstep. neg_lits.
    do 4 zstep. zstep_sh0. do 3 zstep.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ (Forall_impl _ (own_ivA_PB _ PB _) FW) (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
      assert (AGP5 : agrees_on (fun a => in_block (CLc ++ PB) a) m mm)
        by (eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha;
            exact (pb_outside _ _ _ GL _ _ _ [] (CLc ++ PB) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a Ha));
      pose proof (munch_refl [(fflagA L FF_NG_CHECK_HEADER Fb, fflagA L FF_NG_CHECK_HEADER Fb + 1)]%Z mm) as MU2; pose proof (wmono_refl asegs mm) as WM2
    end.
    destruct (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G5) as (FLC & _).
    clear MU WM.
    zstep.
    apply evtF_done. eapply FRET; [exact G5 | unfold ff_class; lia | exact MU2 | exact WM2 | exact FLC |].
    intros s3' G6 OF3 LC3 TL3.
    clear FRNG FSRNG FLR kF kFr kF1 kF2 bF bFr bFhi bFlo bFimg bG bGr bGhi bGlo bGimg SHLO.
    zstep.
    do 16 zstep.
    release_frame FRA ST (SPA + 152)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST STG ltac:(lia)) as ST3. clear ST STG.
    release_frame FR ST3 (bv_unsigned sp).
    destruct (flag_keeps _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ CLc (bv_unsigned sp) G5 MU2 WM2 (incl_appl _ (incl_refl _)) ltac:(lia)) as [AG6 AGP6].
    apply evtF_done. subst POSTQ. cbv beta iota.
    split; [reflexivity|]. split; [reflexivity|].
    do 14 eexists. lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end.
    split; [reflexivity|]. split; [assumption|]. split; [exact ST3|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a K; split; [exact K| exact I] | exact AG6]. }
    split. { eapply agrees_on_trans; [exact AGP5| exact AGP6]. }
    split; [exact G6| exact OF3].
  Qed.
  End Sz2.
  #[using="tlsI GL FRET"] Lemma ngc_epi : ltac:(let t := eval cbv delta [ngc_epi__stmt] in ngc_epi__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CLc PB FB FL lo SPA Fb m ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 r24 r26 t3 t4 t5 t6 jS k0 k1 k2 fj b0 b1 b2 b3 b4 b5 b6 b7 A x. ltac2:(SecDiet.SzSec.closeP 'ngc_epi__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcEpi.
End CANSEC1.
End TwB.
End F_ngchk_epiA.

(* [comment removed for export] *)
Module F_ngchk_exitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcExit.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.

  Definition ngc_exit__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (mm : mem)
      (ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 r24 r26 t3 t4 t5 t6 : word)
      (scs fcs : list cell) (k0 k1 k2 ew : word) (r : check_result),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB mm ->
    rw_cells asegs mm SPA scs -> cells_size scs = 152%nat ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 ew] ->
    ngc_result r av ew PB EB f mm ->
    implMG RNGx (fo_ret FO _ FF_NG_CHECK_HEADER r) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 sp r9 av a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 r20 r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r26 (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b490) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx PB mm ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 r24 r26 t3 t4 t5 t6 scs fcs k0 k1 k2 ew r : ltac2:(SecDiet.SzSec.tyM 'ngc_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_exit__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET.
 intros CTX INV FRA Hscs FRC Hfcs ERRc RES.
    destruct CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    destruct INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU.
    destruct (rw_cells_forget _ _ _ _ FRA) as [jS FRA']. rewrite Hscs in FRA'. clear FRA.
    pose proof (rw_cells_merge asegs _ _ [C8 k0; C8 k1; C8 k2] fcs [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))] FRC) as FRCm.
    rewrite Hfcs in FRCm. cbn [app] in FRCm. clear FRC.
    unfold ngc_shadow in SHC.
    apply (rng_fp_le _ _ _ _ FP) in RSTK.
    eapply implMG_mono.
    { eapply (ngc_epi FO GIOA fflagA GL FRET ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNGx sx CL PB FB FL lo SPA Fb mm);
        [exact SPAB| exact SPA32| exact LO| lia| exact SPT| exact TOP47| exact G| exact MI| exact ST| exact STG| exact FRA'| exact FR| exact FRCm| exact SHC| exact RSTK]. }
    intros r' s3' RNG3 ms3 (-> & -> & PO). destruct_exs PO. destruct PO as (-> & MI7 & ST7 & AG7 & AGP7 & G7 & OF7).
    unfold check_header_post. split; [exact FP|].
    lazymatch goal with |- context [MS _ _ _ _ _ ?m7 _] => exists av, m7, ew end.
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [congruence|]. split; [exact MI7|]. split; [exact ST7|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG|]; intros a (K & N1 & N2); split; [exact K|]; cbn [outside fst snd]; lia|].
             eapply agrees_on_weaken; [exact AG7|]. intros a (K & _); exact K. }
    destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. cbn [map] in MGc |- *.
    split. { eapply rw_cells_recell; [eapply agrees_rw_cells; [exact AG7| exact MGc|]; intros a Ha; eapply clocA_keeps; [exact (proj1 OMG)| cbn [cells_size csize Nat.add] in Ha; lia]
                                    | cbn; repeat split; exact Logic.I | reflexivity]. }
    split. { eapply agrees_rw_cells; [exact AG7| exact ERRc|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OERR)| cbn [cells_size csize Nat.add] in Ha; lia]. }
    assert (KEB : forall cs, rw_cells asegs mm EB cs -> cells_size cs = 256%nat -> rw_cells asegs x13 EB cs).
    { intros cs HC HS. eapply agrees_rw_cells; [exact AG7| exact HC|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OEB)| rewrite HS in Ha; lia]. }
    destruct r as [| msg | p]; cbn [ngc_result] in RES.
    - destruct RES as (-> & -> & -> & e & HEB). rewrite app_nil_r in G7.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact G7|]. exists e. apply KEB; [exact HEB| reflexivity].
    - destruct RES as (-> & -> & -> & (junk' & HEB) & LEN & MSG). rewrite app_nil_r in G7.
      exists junk'. split; [reflexivity|]. split; [reflexivity|]. split; [exact G7|].
      split; [apply KEB; [exact HEB| cbn [cells_size csize Nat.add]; lia]|]. split; [exact LEN| exact MSG].
    - destruct RES as (P & -> & (rf & st & os & Lrf & Lst & Los & PG) & RF & e & HEB).
      exists P, PB. split; [reflexivity|]. split; [exact G7|].
      split. { exists rf, st, os. split; [exact Lrf|]. split; [exact Lst|]. split; [exact Los|].
               eapply PCAPRg_agree; [exact AGP7| intros a Ha; apply in_block_app; right; exact Ha| reflexivity| reflexivity| reflexivity| exact PG]. }
      split; [exact RF|]. exists e. apply KEB; [exact HEB| reflexivity].
  Qed.
  End Sz1.
  Lemma ngc_exit : ltac:(let t := eval cbv delta [ngc_exit__stmt] in ngc_exit__stmt in exact t).
  Proof using GL FRET. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx PB mm ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 r24 r26 t3 t4 t5 t6 scs fcs k0 k1 k2 ew r. ltac2:(SecDiet.SzSec.closeP 'ngc_exit__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcExit.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcExit.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.

  Definition ngc_exit__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (mm : mem)
      (ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 r24 r26 t3 t4 t5 t6 : word)
      (scs fcs : list cell) (k0 k1 k2 ew : word) (r : check_result),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB mm ->
    rw_cells asegs mm SPA scs -> cells_size scs = 152%nat ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 ew] ->
    ngc_result r av ew PB EB f mm ->
    implMG RNGx (fo_ret FO _ FF_NG_CHECK_HEADER r) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 sp r9 av a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 r20 r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r26 (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b614) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx PB mm ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 r24 r26 t3 t4 t5 t6 scs fcs k0 k1 k2 ew r : ltac2:(SecDiet.SzSec.tyM 'ngc_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_exit__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET.
 intros CTX INV FRA Hscs FRC Hfcs ERRc RES.
    destruct CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    destruct INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU.
    destruct (rw_cells_forget _ _ _ _ FRA) as [jS FRA']. rewrite Hscs in FRA'. clear FRA.
    pose proof (rw_cells_merge asegs _ _ [C8 k0; C8 k1; C8 k2] fcs [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))] FRC) as FRCm.
    rewrite Hfcs in FRCm. cbn [app] in FRCm. clear FRC.
    unfold ngc_shadow in SHC.
    apply (rng_fp_le _ _ _ _ FP) in RSTK.
    eapply implMG_mono.
    { eapply (ngc_epi FO GIOA fflagA GL FRET ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNGx sx CL PB FB FL lo SPA Fb mm);
        [exact SPAB| exact SPA32| exact LO| lia| exact SPT| exact TOP47| exact G| exact MI| exact ST| exact STG| exact FRA'| exact FR| exact FRCm| exact SHC| exact RSTK]. }
    intros r' s3' RNG3 ms3 (-> & -> & PO). destruct_exs PO. destruct PO as (-> & MI7 & ST7 & AG7 & AGP7 & G7 & OF7).
    unfold check_header_post. split; [exact FP|].
    lazymatch goal with |- context [MS _ _ _ _ _ ?m7 _] => exists av, m7, ew end.
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [congruence|]. split; [exact MI7|]. split; [exact ST7|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG|]; intros a (K & N1 & N2); split; [exact K|]; cbn [outside fst snd]; lia|].
             eapply agrees_on_weaken; [exact AG7|]. intros a (K & _); exact K. }
    destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. cbn [map] in MGc |- *.
    split. { eapply rw_cells_recell; [eapply agrees_rw_cells; [exact AG7| exact MGc|]; intros a Ha; eapply clocA_keeps; [exact (proj1 OMG)| cbn [cells_size csize Nat.add] in Ha; lia]
                                    | cbn; repeat split; exact Logic.I | reflexivity]. }
    split. { eapply agrees_rw_cells; [exact AG7| exact ERRc|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OERR)| cbn [cells_size csize Nat.add] in Ha; lia]. }
    assert (KEB : forall cs, rw_cells asegs mm EB cs -> cells_size cs = 256%nat -> rw_cells asegs x13 EB cs).
    { intros cs HC HS. eapply agrees_rw_cells; [exact AG7| exact HC|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OEB)| rewrite HS in Ha; lia]. }
    destruct r as [| msg | p]; cbn [ngc_result] in RES.
    - destruct RES as (-> & -> & -> & e & HEB). rewrite app_nil_r in G7.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact G7|]. exists e. apply KEB; [exact HEB| reflexivity].
    - destruct RES as (-> & -> & -> & (junk' & HEB) & LEN & MSG). rewrite app_nil_r in G7.
      exists junk'. split; [reflexivity|]. split; [reflexivity|]. split; [exact G7|].
      split; [apply KEB; [exact HEB| cbn [cells_size csize Nat.add]; lia]|]. split; [exact LEN| exact MSG].
    - destruct RES as (P & -> & (rf & st & os & Lrf & Lst & Los & PG) & RF & e & HEB).
      exists P, PB. split; [reflexivity|]. split; [exact G7|].
      split. { exists rf, st, os. split; [exact Lrf|]. split; [exact Lst|]. split; [exact Los|].
               eapply PCAPRg_agree; [exact AGP7| intros a Ha; apply in_block_app; right; exact Ha| reflexivity| reflexivity| reflexivity| exact PG]. }
      split; [exact RF|]. exists e. apply KEB; [exact HEB| reflexivity].
  Qed.
  End Sz1.
  Lemma ngc_exit : ltac:(let t := eval cbv delta [ngc_exit__stmt] in ngc_exit__stmt in exact t).
  Proof using GL FRET. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx PB mm ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 r24 r26 t3 t4 t5 t6 scs fcs k0 k1 k2 ew r. ltac2:(SecDiet.SzSec.closeP 'ngc_exit__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcExit.
End CANSEC1.
End TwB.
End F_ngchk_exitA.

(* [comment removed for export] *)
Module F_ngchk_fstmtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_modelA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcFillStmt.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.

  Definition ngc_fill_stmt : Prop :=
    forall (fuel : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (sw : bool) (TL : Z)
      (j0 j : list byte) (ccs : list cell) (fpre fmid fpost : list byte) (k0 k1 k2 tlw : word) (e : list byte),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [] mm ->
    (28 <= TL <= 1048576)%Z ->
    rw_cells asegs mm SPA [CB 80 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb)] ->
    rw_cells asegs mm (SPA + 128) ccs -> cells_size ccs = 24%nat ->
    rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; C4 tlw; CB 12 fmid; C4 (Z_to_bv 64 BYTE_ORDER_MAGIC); CB 4 fpost;
                          C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))] ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    implMG RNGx (ngc_open MOps (prims HO FO sites) fuel f 0 BT_SHB sw TL) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 (Fb + 48)) (Z_to_bv 64 FA) (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 TL)
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b044) fc None mm (seg_rom asegs)).
End NgcFillStmt.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcFillStmt.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.

  Definition ngc_fill_stmt : Prop :=
    forall (fuel : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (sw : bool) (TL : Z)
      (j0 j : list byte) (ccs : list cell) (fpre fmid fpost : list byte) (k0 k1 k2 tlw : word) (e : list byte),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [] mm ->
    (28 <= TL <= 1048576)%Z ->
    rw_cells asegs mm SPA [CB 80 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb)] ->
    rw_cells asegs mm (SPA + 128) ccs -> cells_size ccs = 24%nat ->
    rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; C4 tlw; CB 12 fmid; C4 (Z_to_bv 64 BYTE_ORDER_MAGIC); CB 4 fpost;
                          C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))] ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    implMG RNGx (ngc_open MOps (prims HO FO sites) fuel f 0 BT_SHB sw TL) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 FA) (Z_to_bv 64 (Fb + 48)) (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 TL)
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8af9c) fc None mm (seg_rom asegs)).
End NgcFillStmt.
End CANSEC1.
End TwB.
End F_ngchk_fstmtA.

(* [comment removed for export] *)
Module F_ngchk_hstmt2A.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_modelA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcBomStmt.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.

  (* [comment removed for export] *)
  Definition ngc_bomk (fuel : nat) (f : hptr) (tlb bomb : list Z) : Monad.M (PState H hptr) (@check_result hptr hptr) :=
    let total_length := get_le32 tlb 0 in
    let byte_order_magic := get_le32 bomb 0 in
    let '(ok, swapped, total_length) :=
      if byte_order_magic =? BYTE_ORDER_MAGIC then (true, false, total_length)
      else if bswap32 byte_order_magic =? BYTE_ORDER_MAGIC then (true, true, bswap32 total_length)
      else (false, false, total_length) in
    if negb ok then e_fret (prims HO FO sites) FF_NG_CHECK_HEADER CH_NotMe else
    if (total_length <? 28) || (BT_SHB_INSANE_MAX <? total_length)
    then e_fret (prims HO FO sites) FF_NG_CHECK_HEADER (CH_Err (Msg.shb_invalid_length total_length))
    else ngc_open MOps (prims HO FO sites) fuel f 0 BT_SHB swapped total_length.

  Definition ngc_bom_stmt : Prop :=
    forall (fuel : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6 : word) (tlb bomb : list Z)
      (j0 j j2 : list byte) (fpre fmid fpost : list byte) (k0 k1 k2 : word) (e : list byte),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [] mm ->
    Forall (fun z => 0 <= z < 256)%Z tlb -> length tlb = 4%nat -> Forall (fun z => 0 <= z < 256)%Z bomb -> length bomb = 4%nat ->
    rw_cells asegs mm SPA [CB 80 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb); CB 24 j2] ->
    rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; CB 4 (map b8 tlb); CB 12 fmid; CB 4 (map b8 bomb); CB 4 fpost;
                          C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))] ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    implMG RNGx (ngc_bomk fuel f tlb bomb) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 (Fb + 48)) (Z_to_bv 64 FA) r23 (Z_to_bv 64 (Fb + 32))
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8af58) fc None mm (seg_rom asegs)).
End NgcBomStmt.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcBomStmt.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.

  (* [comment removed for export] *)
  Definition ngc_bomk (fuel : nat) (f : hptr) (tlb bomb : list Z) : Monad.M (PState H hptr) (@check_result hptr hptr) :=
    let total_length := get_le32 tlb 0 in
    let byte_order_magic := get_le32 bomb 0 in
    let '(ok, swapped, total_length) :=
      if byte_order_magic =? BYTE_ORDER_MAGIC then (true, false, total_length)
      else if bswap32 byte_order_magic =? BYTE_ORDER_MAGIC then (true, true, bswap32 total_length)
      else (false, false, total_length) in
    if negb ok then e_fret (prims HO FO sites) FF_NG_CHECK_HEADER CH_NotMe else
    if (total_length <? 28) || (BT_SHB_INSANE_MAX <? total_length)
    then e_fret (prims HO FO sites) FF_NG_CHECK_HEADER (CH_Err (Msg.shb_invalid_length total_length))
    else ngc_open MOps (prims HO FO sites) fuel f 0 BT_SHB swapped total_length.

  Definition ngc_bom_stmt : Prop :=
    forall (fuel : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6 : word) (tlb bomb : list Z)
      (j0 j j2 : list byte) (fpre fmid fpost : list byte) (k0 k1 k2 : word) (e : list byte),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [] mm ->
    Forall (fun z => 0 <= z < 256)%Z tlb -> length tlb = 4%nat -> Forall (fun z => 0 <= z < 256)%Z bomb -> length bomb = 4%nat ->
    rw_cells asegs mm SPA [CB 80 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb); CB 24 j2] ->
    rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; CB 4 (map b8 tlb); CB 12 fmid; CB 4 (map b8 bomb); CB 4 fpost;
                          C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))] ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    implMG RNGx (ngc_bomk fuel f tlb bomb) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 FA) (Z_to_bv 64 (Fb + 48)) r23 (Z_to_bv 64 (Fb + 32))
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8aeb0) fc None mm (seg_rom asegs)).
End NgcBomStmt.
End CANSEC1.
End TwB.
End F_ngchk_hstmt2A.

(* [comment removed for export] *)
Module F_ngchk_hstmtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_modelA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcHeadStmts.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.

  Definition ngc_short_stmt : Prop :=
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r23 r24 t3 t4 t5 t6 : word) (pcx : Z)
      (j0 j j2 : list byte) (fcs : list cell) (k0 k1 k2 : word) (e : list byte),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [] mm ->
    (pcx = 0x8ae94 \/ pcx = 0x8af04)%Z ->
    rw_cells asegs mm SPA [CB 80 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb); CB 24 j2] ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    implMG RNGx (mbind (e_ferror (prims HO FO sites) f) (fun er : bool =>
                   if er then mbind (errmsg_for_errno MOps (prims HO FO sites) "error reading dump file"%string [])
                                    (fun msg => e_fret (prims HO FO sites) FF_NG_CHECK_HEADER (CH_Err msg))
                   else e_fret (prims HO FO sites) FF_NG_CHECK_HEADER CH_NotMe)) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 (Z_to_bv 64 FA) r23 r24
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 pcx) fc None mm (seg_rom asegs)).

  Definition ngc_lenfail_stmt : Prop :=
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 w24 t3 t4 t5 t6 : word) (TL hi : Z)
      (j0 j j2 : list byte) (fcs : list cell) (k0 k1 k2 : word) (e : list byte),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [] mm ->
    (bv_unsigned w24 = TL + 4294967296 * hi)%Z -> (0 <= TL < 2^32)%Z -> (0 <= hi < 2^32)%Z ->
    rw_cells asegs mm SPA [CB 80 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb); CB 24 j2] ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    implMG RNGx (e_fret (prims HO FO sites) FF_NG_CHECK_HEADER (CH_Err (Msg.shb_invalid_length TL))) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 w24
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8af84) fc None mm (seg_rom asegs)).
End NgcHeadStmts.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcHeadStmts.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.

  Definition ngc_short_stmt : Prop :=
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 r24 t3 t4 t5 t6 : word) (pcx : Z)
      (j0 j j2 : list byte) (fcs : list cell) (k0 k1 k2 : word) (e : list byte),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [] mm ->
    (pcx = 0x8add4 \/ pcx = 0x8ae50)%Z ->
    rw_cells asegs mm SPA [CB 80 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb); CB 24 j2] ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    implMG RNGx (mbind (e_ferror (prims HO FO sites) f) (fun er : bool =>
                   if er then mbind (errmsg_for_errno MOps (prims HO FO sites) "error reading dump file"%string [])
                                    (fun msg => e_fret (prims HO FO sites) FF_NG_CHECK_HEADER (CH_Err msg))
                   else e_fret (prims HO FO sites) FF_NG_CHECK_HEADER CH_NotMe)) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 FA) r22 r23 r24
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 pcx) fc None mm (seg_rom asegs)).

  Definition ngc_lenfail_stmt : Prop :=
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 w24 t3 t4 t5 t6 : word) (TL hi : Z)
      (j0 j j2 : list byte) (fcs : list cell) (k0 k1 k2 : word) (e : list byte),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [] mm ->
    (bv_unsigned w24 = TL + 4294967296 * hi)%Z -> (0 <= TL < 2^32)%Z -> (0 <= hi < 2^32)%Z ->
    rw_cells asegs mm SPA [CB 80 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb); CB 24 j2] ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    implMG RNGx (e_fret (prims HO FO sites) FF_NG_CHECK_HEADER (CH_Err (Msg.shb_invalid_length TL))) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 w24
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8aedc) fc None mm (seg_rom asegs)).
End NgcHeadStmts.
End CANSEC1.
End TwB.
End F_ngchk_hstmtA.

(* [comment removed for export] *)
Module F_pcap_statsA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase RtCells AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.
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

Definition stats_msg : list byte := [83; 116; 97; 116; 105; 115; 116; 105; 99; 115; 32; 97; 114; 101; 110; 39; 116; 32; 97; 118; 97; 105; 108; 97; 98; 108; 101; 32; 102; 114; 111; 109; 32; 115; 97; 118; 101; 102; 105; 108; 101; 115; 0].

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Stats.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  (* [comment removed for export] *)
  #[using="Type"] Lemma pcap_aux_closable_agree : forall (p : PcapTypes.pcap hptr hptr) P B I pad bs m m' (Q : Z -> Prop),
    agrees_on Q m m' ->
    (forall a, B <= a < B + pc_bufalloc p -> Q a)%Z ->
    (forall a, P + PCAP_PRIV_OFF <= a < P + psize p -> Q a)%Z ->
    (forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a)%Z ->
    (0 <= pc_bufalloc p)%Z ->
    rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] -> rw_cells asegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad) -> ifaces_closable p I m ->
    rw_cells asegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs] /\ rw_cells asegs m' (P + PCAP_PRIV_OFF) (priv_cells p I pad) /\ ifaces_closable p I m'.
  Proof.
    intros p P B I pad bs m m' Q AG HB HP HI Hba BUF PRIV IFS. split; [|split].
    - eapply agrees_rw_cells; [exact AG|exact BUF|]. intros a Ha. apply HB. cbn [cells_size csize] in Ha. lia.
    - eapply agrees_rw_cells; [exact AG|exact PRIV|]. intros a Ha. apply HP. pose proof (priv_cells_psize _ _ _ _ _ PRIV). lia.
    - eapply ifaces_closable_agree; eassumption.
  Qed.

  Definition pcap_stats_proofA__stmt : Prop := pcap_stats_stmt GIOA TP.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P p : ltac2:(SecDiet.SzSec.tyM 'pcap_stats_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="FO fflagA GL"] Lemma pcap_stats_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_stats_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros PRE UC TR NF PC ->.
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    destruct PC as (Af & HinF & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    assert (HinP : In (pc_self p, P, psize p) ((CLc ++ PB) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; rewrite EPB; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & _) & _).
    pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G EPB) as [APB API].
    pose proof (psize_pos p) as PS. unfold PCAP_L1_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    band_ind PBAND bP.
    (* [comment removed for export] *)
    set (AUXB := rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs]) in BUF.
    set (AUXP := rw_cells asegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad)) in PRIV.
    set (AUXI := ifaces_closable p I m) in IFS.
    (* [comment removed for export] *)
    unfold Pcap.pcap_stats. cbn [mo_ret MOps]. apply implMG_ret.
    unfold PCAP_STATS_ENTRY.
    (* [comment removed for export] *)
    assert (MSG : ro_cells asegs m 0x215a0 [CB 43 stats_msg]).
    { apply (ro_cells_image asegs m); [exact MI | vm_compute; reflexivity | lia | cbn; lia]. }
    (* [comment removed for export] *)
    apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    unfold pc_ops, PK, pk_stats, pk_oneshot in CO. unfold pc_pre in CA. unfold hdr_cells in CH. unfold PCAP_PRIV_OFF in CA.
    apply (rw_cells_split_CB asegs m _ [] 304 _ [] [43; 261]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CB1 CB2]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CB1, CB2.
    replace (P + 216 + Z.of_nat 43)%Z with (P + 259)%Z in CB2 by lia.
    pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (P + 216, P + 216 + 43)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 6 zstep.
    ck0 PUNP; ck_go.
    do 4 zstep.
    release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 7 zstep.
    assert (FW : Forall (pcap_iv FL PB) [(bv_unsigned sp - 2240, bv_unsigned sp); (P + 216, P + 216 + 43)]%Z).
    { apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
      right; left. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G1 : GIOA L RNG s (CLc ++ PB) FB FL mm) by (eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FW])
    end.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G1) as (RT1 & _).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G1 HinP) as PBLK1.
    call_sp (asan_memcpy_specZ RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (P + 216)%Z 0x215a0%Z 43%Z stats_msg (firstn 43 (pj_g j)));
      [ reflexivity | reflexivity | reflexivity | assumption | exact ST | lia | lia
      | exact RT1 | exact (ro_cells_bytes_at _ _ _ _ MSG) | reflexivity | lia | exact CB1 | lia
      | eapply (gia_global_mobjA _ _ _ GL); [exact G1 | unfold client_globals; repeat (first [left; reflexivity | right]) | exact RIMG | exact RISH]
      | apply aobjA_mobjA; [eapply blockA_aobj; [exact PBLK1 | cbn [cb_addr cb_size fst snd]; lia | cbn [cb_addr cb_size fst snd]; lia | lia] | lia]
      | lia | lia | ].
    do 4 zstep.
    release_frame FR PC (bv_unsigned sp).
    (* [comment removed for export] *)
    assert (HinB : In (pc_buffer p, B, pc_bufalloc p) ((CLc ++ PB) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; rewrite EPB; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinB) as ((_ & _ & BTOP & _) & B1 & _). cbn [cb_addr cb_size fst snd] in BTOP, B1.
    set (W := [(bv_unsigned sp - 2240, bv_unsigned sp); (P + 216, P + 216 + 43)]%Z) in *.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AG : agrees_on (fun a => outside W a) m mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      destruct (pcap_aux_closable_agree p P B I pad bs m mm _ AG) as (BUF' & PRIV' & IFS');
        [ | | | lia | exact BUF | exact PRIV | exact IFS |]
    end.
    { intros a Ha. subst W. cbn [outside]. lia. }
    { intros a Ha. subst W. cbn [outside]. unfold PCAP_PRIV_OFF in Ha. lia. }
    { intros sg q Hq a Ha. subst W. cbn [outside]. destruct (API sg q Hq) as [X1 X2].
      assert (HinI : In (q, I, (40 * ng_ifaces_size sg)%Z) ((CLc ++ PB) ++ FB))
        by (apply in_or_app; left; apply in_or_app; right; rewrite EPB; unfold pcap_blocks; rewrite Hq; right; right; left; reflexivity).
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinI) as ((_ & _ & ITOP & _) & I1 & _). cbn [cb_addr cb_size fst snd] in ITOP, I1. lia. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      apply evtF_done; unfold pcap_post; split; [apply fp_le_refl|]; exists (Z_to_bv 64 (-1)), mm, PB, FB end.
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [assumption|]. split; [assumption|].
    split. { eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G | exact MU | exact WM | | lia].
             subst W. apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
             right; left. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    split. { eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FW]. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    (* [comment removed for export] *)
    cbn [fst snd]. exists Af. split; [exact HinF|].
    exists B, I. eexists. exists pad, bs.
    split; [exact EPB|]. split.
    { lazymatch goal with HPC : rw_cells _ ?mm (P + 216)%Z _ |- rw_cells _ _ _ _ =>
        pose proof (rw_cells_uncut _ _ _ _ _ HPC CB2 ltac:(cbn; lia)) as CE';
        pose proof (pcap_cells_join4 mm P p B (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) j _ (pc_header p)
                      eq_refl CA CE' eq_refl CH CO) as J end.
      replace (set_header (pc_header p) p) with p in J by (destruct p; reflexivity). exact J. }
    split; [exact PRIV'|]. split; [exact BUF'|]. split; [exact PFX|]. split; [exact IFS'|]. exact WF.
  Qed.
  End Sz2.
  #[using="FO fflagA GL"] Theorem pcap_stats_proofA : ltac:(let t := eval cbv delta [pcap_stats_proofA__stmt] in pcap_stats_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P p. ltac2:(SecDiet.SzSec.closeP 'pcap_stats_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Stats.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
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

Definition stats_msg : list byte := [83; 116; 97; 116; 105; 115; 116; 105; 99; 115; 32; 97; 114; 101; 110; 39; 116; 32; 97; 118; 97; 105; 108; 97; 98; 108; 101; 32; 102; 114; 111; 109; 32; 115; 97; 118; 101; 102; 105; 108; 101; 115; 0].

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Stats.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  (* [comment removed for export] *)
  #[using="Type"] Lemma pcap_aux_closable_agree : forall (p : PcapTypes.pcap hptr hptr) P B I pad bs m m' (Q : Z -> Prop),
    agrees_on Q m m' ->
    (forall a, B <= a < B + pc_bufalloc p -> Q a)%Z ->
    (forall a, P + PCAP_PRIV_OFF <= a < P + psize p -> Q a)%Z ->
    (forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a)%Z ->
    (0 <= pc_bufalloc p)%Z ->
    rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] -> rw_cells asegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad) -> ifaces_closable p I m ->
    rw_cells asegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs] /\ rw_cells asegs m' (P + PCAP_PRIV_OFF) (priv_cells p I pad) /\ ifaces_closable p I m'.
  Proof.
    intros p P B I pad bs m m' Q AG HB HP HI Hba BUF PRIV IFS. split; [|split].
    - eapply agrees_rw_cells; [exact AG|exact BUF|]. intros a Ha. apply HB. cbn [cells_size csize] in Ha. lia.
    - eapply agrees_rw_cells; [exact AG|exact PRIV|]. intros a Ha. apply HP. pose proof (priv_cells_psize _ _ _ _ _ PRIV). lia.
    - eapply ifaces_closable_agree; eassumption.
  Qed.

  Definition pcap_stats_proofA__stmt : Prop := pcap_stats_stmt GIOA TP.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P p : ltac2:(SecDiet.SzSec.tyM 'pcap_stats_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="FO fflagA GL"] Lemma pcap_stats_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_stats_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros PRE UC TR NF PC ->.
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    destruct PC as (Af & HinF & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    assert (HinP : In (pc_self p, P, psize p) ((CLc ++ PB) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; rewrite EPB; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & _) & _).
    pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G EPB) as [APB API].
    pose proof (psize_pos p) as PS. unfold PCAP_L1_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    band_ind PBAND bP.
    (* [comment removed for export] *)
    set (AUXB := rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs]) in BUF.
    set (AUXP := rw_cells asegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad)) in PRIV.
    set (AUXI := ifaces_closable p I m) in IFS.
    (* [comment removed for export] *)
    unfold Pcap.pcap_stats. cbn [mo_ret MOps]. apply implMG_ret.
    unfold PCAP_STATS_ENTRY.
    (* [comment removed for export] *)
    assert (MSG : ro_cells asegs m 0x215a0 [CB 43 stats_msg]).
    { apply (ro_cells_image asegs m); [exact MI | vm_compute; reflexivity | lia | cbn; lia]. }
    (* [comment removed for export] *)
    apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    unfold pc_ops, PK, pk_stats, pk_oneshot in CO. unfold pc_pre in CA. unfold hdr_cells in CH. unfold PCAP_PRIV_OFF in CA.
    apply (rw_cells_split_CB asegs m _ [] 304 _ [] [43; 261]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CB1 CB2]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CB1, CB2.
    replace (P + 216 + Z.of_nat 43)%Z with (P + 259)%Z in CB2 by lia.
    pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (P + 216, P + 216 + 43)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 2 zstep. ub_null.                  (* [comment removed for export] *)
    zstep. ub_al 7%Z ltac:(al16 P2). zstep. if_false.
    do 4 zstep.
    ck0 PUNP; ck_go.
    do 4 zstep.
    release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 2 zstep. ub_null.                  (* [comment removed for export] *)
    zstep. ub_al 7%Z ltac:(al16 P2). zstep. if_false.
    do 5 zstep.
    assert (FW : Forall (pcap_iv FL PB) [(bv_unsigned sp - 2240, bv_unsigned sp); (P + 216, P + 216 + 43)]%Z).
    { apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
      right; left. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G1 : GIOA L RNG s (CLc ++ PB) FB FL mm) by (eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FW])
    end.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G1) as (RT1 & _).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G1 HinP) as PBLK1.
    call_sp (asan_memcpy_specZ RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (P + 216)%Z 0x215a0%Z 43%Z stats_msg (firstn 43 (pj_g j)));
      [ reflexivity | reflexivity | reflexivity | assumption | exact ST | lia | lia
      | exact RT1 | exact (ro_cells_bytes_at _ _ _ _ MSG) | reflexivity | lia | exact CB1 | lia
      | eapply (gia_global_mobjA _ _ _ GL); [exact G1 | unfold client_globals; repeat (first [left; reflexivity | right]) | exact RIMG | exact RISH]
      | apply aobjA_mobjA; [eapply blockA_aobj; [exact PBLK1 | cbn [cb_addr cb_size fst snd]; lia | cbn [cb_addr cb_size fst snd]; lia | lia] | lia]
      | lia | lia | ].
    do 4 zstep.
    release_frame FR PC (bv_unsigned sp).
    (* [comment removed for export] *)
    assert (HinB : In (pc_buffer p, B, pc_bufalloc p) ((CLc ++ PB) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; rewrite EPB; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinB) as ((_ & _ & BTOP & _) & B1 & _). cbn [cb_addr cb_size fst snd] in BTOP, B1.
    set (W := [(bv_unsigned sp - 2240, bv_unsigned sp); (P + 216, P + 216 + 43)]%Z) in *.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AG : agrees_on (fun a => outside W a) m mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      destruct (pcap_aux_closable_agree p P B I pad bs m mm _ AG) as (BUF' & PRIV' & IFS');
        [ | | | lia | exact BUF | exact PRIV | exact IFS |]
    end.
    { intros a Ha. subst W. cbn [outside]. lia. }
    { intros a Ha. subst W. cbn [outside]. unfold PCAP_PRIV_OFF in Ha. lia. }
    { intros sg q Hq a Ha. subst W. cbn [outside]. destruct (API sg q Hq) as [X1 X2].
      assert (HinI : In (q, I, (40 * ng_ifaces_size sg)%Z) ((CLc ++ PB) ++ FB))
        by (apply in_or_app; left; apply in_or_app; right; rewrite EPB; unfold pcap_blocks; rewrite Hq; right; right; left; reflexivity).
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinI) as ((_ & _ & ITOP & _) & I1 & _). cbn [cb_addr cb_size fst snd] in ITOP, I1. lia. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      apply evtF_done; unfold pcap_post; split; [apply fp_le_refl|]; exists (Z_to_bv 64 (-1)), mm, PB, FB end.
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [assumption|]. split; [assumption|].
    split. { eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G | exact MU | exact WM | | lia].
             subst W. apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
             right; left. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    split. { eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FW]. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    (* [comment removed for export] *)
    cbn [fst snd]. exists Af. split; [exact HinF|].
    exists B, I. eexists. exists pad, bs.
    split; [exact EPB|]. split.
    { lazymatch goal with HPC : rw_cells _ ?mm (P + 216)%Z _ |- rw_cells _ _ _ _ =>
        pose proof (rw_cells_uncut _ _ _ _ _ HPC CB2 ltac:(cbn; lia)) as CE';
        pose proof (pcap_cells_join4 mm P p B (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) j _ (pc_header p)
                      eq_refl CA CE' eq_refl CH CO) as J end.
      replace (set_header (pc_header p) p) with p in J by (destruct p; reflexivity). exact J. }
    split; [exact PRIV'|]. split; [exact BUF'|]. split; [exact PFX|]. split; [exact IFS'|]. exact WF.
  Qed.
  End Sz2.
  #[using="FO fflagA GL"] Theorem pcap_stats_proofA : ltac:(let t := eval cbv delta [pcap_stats_proofA__stmt] in pcap_stats_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P p. ltac2:(SecDiet.SzSec.closeP 'pcap_stats_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Stats.
End CANSEC1.
End TwB.
End F_pcap_statsA.

(* [comment removed for export] *)
Module F_sfchk_epiA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.
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
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Lemma land_m32A : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section ChkEpi.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.

  Definition chk_epi__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CLc PB FB : list (@cblock hptr)) (FL : list fblock) (lo SPA Fb : Z) (m : mem)
      (ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a6 a7 r18 r19 r20 r21 r22 r23 r26 r27 t3 t4 t5 t6 : word)
      (jS : list byte) (k0 k1 k2 : word) (fj : list byte) (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : byte)
      (A : Type) (x : A),
    (bv_unsigned sp - 208 <= SPA <= bv_unsigned sp - 192)%Z -> (SPA mod 32 = 0)%Z -> (ATOP + 4096 <= lo)%Z -> (lo <= SPA)%Z ->
    (bv_unsigned sp + 16 < al_top L)%Z -> (al_top L <= 2^47)%Z ->
    GIOA L RNG s (CLc ++ PB) FB ((FF_CHECK_HEADER, Fb, 128%Z) :: FL) m -> mem_inv asegs m ->
    stk asegs m lo SPA -> stk asegs m (SPA + 88) (bv_unsigned sp + -104) ->
    rw_cells asegs m SPA [CB 88 jS] ->
    rw_cells asegs m (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m Fb [C8 k0; C8 k1; C8 k2; CB 96 fj; C8 (Z_to_bv 64 (fflagA L FF_CHECK_HEADER Fb))] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9; C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15] ->
    rng RNG lo (al_top L - lo) ->
    implMG RNG (fo_ret FO _ FF_CHECK_HEADER x) s
      (fun r s' RNG' ms' => r = x /\ RNG' = RNG /\ exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 av a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m' /\ agrees_on (fun a => in_block (CLc ++ PB) a) m m'
           /\ GIOA L RNG s' (CLc ++ PB) FB FL m' /\ ps_outfile s' = ps_outfile s)
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 sp r9 av a1 a2 a3 a4 (Z_to_bv 64 Fb) a6 a7
               r18 r19 r20 r21 r22 r23 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb) r26 r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x87a50) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CLc PB FB FL lo SPA Fb m ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a6 a7 r18 r19 r20 r21 r22 r23 r26 r27 t3 t4 t5 t6 jS k0 k1 k2 fj b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 A x : ltac2:(SecDiet.SzSec.tyM 'chk_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="tlsI GL FRET"] Lemma chk_epi__body : ltac2:(SecDiet.SzSec.bodyP 'chk_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros SPAB SPA32 LO LOS SPT TOP47 G MI ST STG FRA FR FRC SHC RSTK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. pose proof (Forall_inv FAll) as (FBAND & FTOP & F64 & _ & FRNG & FSRNG & _ & _).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64, FRNG, FSRNG. clear FAll. change (Z.shiftr 128 3) with 16%Z in FSRNG.
    pose proof (ablk_lin _ _ FBAND) as (_ & Fb0 & _ & _). band_ind FBAND bF.
    destruct (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G) as (_ & FLR & FLB & FLT & _ & (kF & kFr & kF1 & kF2)). band_ind FLB bG.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 16 <= 0x10007fff8000
                   /\ (Fb + 128 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 16 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    assert (FW : Forall (own_ivA [(FF_CHECK_HEADER, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z) by own_ivs.
    pose proof (munch_refl [(Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    zstep. neg_lits.
    do 3 zstep.
    do 3 zstep.
    zstep. if_false_by (eqz_false Fb ltac:(lia)).
    zstep. neg_lits.
    do 4 zstep. zstep_sh0. do 11 zstep.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ (Forall_impl _ (own_ivA_PB _ PB _) FW) (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
      assert (AGP5 : agrees_on (fun a => in_block (CLc ++ PB) a) m mm)
        by (eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha;
            exact (pb_outside _ _ _ GL _ _ _ [] (CLc ++ PB) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a Ha));
      pose proof (munch_refl [(fflagA L FF_CHECK_HEADER Fb, fflagA L FF_CHECK_HEADER Fb + 1)]%Z mm) as MU2; pose proof (wmono_refl asegs mm) as WM2
    end.
    destruct (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G5) as (FLC & _).
    clear MU WM.
    zstep.
    apply evtF_done. eapply FRET; [exact G5 | unfold ff_class; lia | exact MU2 | exact WM2 | exact FLC |].
    intros s3' G6 OF3 LC3 TL3.
    clear FRNG FSRNG FLR kF kFr kF1 kF2 bF bFr bFhi bFlo bFimg bG bGr bGhi bGlo bGimg SHLO.
    zstep.
    do 16 zstep.
    release_frame FRA ST (SPA + 88)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST STG ltac:(lia)) as ST3. clear ST STG.
    release_frame FR ST3 (bv_unsigned sp).
    destruct (flag_keeps _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ CLc (bv_unsigned sp) G5 MU2 WM2 (incl_appl _ (incl_refl _)) ltac:(lia)) as [AG6 AGP6].
    apply evtF_done. subst POSTQ. cbv beta iota.
    split; [reflexivity|]. split; [reflexivity|].
    do 14 eexists. lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end.
    split; [reflexivity|]. split; [assumption|]. split; [exact ST3|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a K; split; [exact K| exact I] | exact AG6]. }
    split. { eapply agrees_on_trans; [exact AGP5| exact AGP6]. }
    split; [exact G6| exact OF3].
  Qed.
  End Sz2.
  #[using="tlsI GL FRET"] Lemma chk_epi : ltac:(let t := eval cbv delta [chk_epi__stmt] in chk_epi__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CLc PB FB FL lo SPA Fb m ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a6 a7 r18 r19 r20 r21 r22 r23 r26 r27 t3 t4 t5 t6 jS k0 k1 k2 fj b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 A x. ltac2:(SecDiet.SzSec.closeP 'chk_epi__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkEpi.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB.
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
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Lemma land_m32A : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section ChkEpi.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.

  Definition chk_epi__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CLc PB FB : list (@cblock hptr)) (FL : list fblock) (lo SPA Fb : Z) (m : mem)
      (ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r18 r19 r20 r21 r22 r23 r27 t3 t4 t5 t6 : word)
      (jS : list byte) (k0 k1 k2 : word) (fj : list byte) (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : byte)
      (A : Type) (x : A),
    (bv_unsigned sp - 208 <= SPA <= bv_unsigned sp - 192)%Z -> (SPA mod 32 = 0)%Z -> (ATOP + 4096 <= lo)%Z -> (lo <= SPA)%Z ->
    (bv_unsigned sp + 16 < al_top L)%Z -> (al_top L <= 2^47)%Z ->
    GIOA L RNG s (CLc ++ PB) FB ((FF_CHECK_HEADER, Fb, 128%Z) :: FL) m -> mem_inv asegs m ->
    stk asegs m lo SPA -> stk asegs m (SPA + 88) (bv_unsigned sp + -104) ->
    rw_cells asegs m SPA [CB 88 jS] ->
    rw_cells asegs m (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m Fb [C8 k0; C8 k1; C8 k2; CB 96 fj; C8 (Z_to_bv 64 (fflagA L FF_CHECK_HEADER Fb))] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9; C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15] ->
    rng RNG lo (al_top L - lo) ->
    implMG RNG (fo_ret FO _ FF_CHECK_HEADER x) s
      (fun r s' RNG' ms' => r = x /\ RNG' = RNG /\ exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 av a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m' /\ agrees_on (fun a => in_block (CLc ++ PB) a) m m'
           /\ GIOA L RNG s' (CLc ++ PB) FB FL m' /\ ps_outfile s' = ps_outfile s)
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 sp r9 av a1 a2 a3 a4 a5 a6 a7
               r18 r19 r20 r21 r22 r23 (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x87f24) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CLc PB FB FL lo SPA Fb m ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r18 r19 r20 r21 r22 r23 r27 t3 t4 t5 t6 jS k0 k1 k2 fj b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 A x : ltac2:(SecDiet.SzSec.tyM 'chk_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="tlsI GL FRET"] Lemma chk_epi__body : ltac2:(SecDiet.SzSec.bodyP 'chk_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros SPAB SPA32 LO LOS SPT TOP47 G MI ST STG FRA FR FRC SHC RSTK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. pose proof (Forall_inv FAll) as (FBAND & FTOP & F64 & _ & FRNG & FSRNG & _ & _).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64, FRNG, FSRNG. clear FAll. change (Z.shiftr 128 3) with 16%Z in FSRNG.
    pose proof (ablk_lin _ _ FBAND) as (_ & Fb0 & _ & _). band_ind FBAND bF.
    destruct (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G) as (_ & FLR & FLB & FLT & _ & (kF & kFr & kF1 & kF2)). band_ind FLB bG.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 16 <= 0x10007fff8000
                   /\ (Fb + 128 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 16 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    assert (FW : Forall (own_ivA [(FF_CHECK_HEADER, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z) by own_ivs.
    pose proof (munch_refl [(Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    zstep. neg_lits.
    do 3 zstep.
    do 3 zstep.
    zstep. if_false_by (eqz_false Fb ltac:(lia)).
    zstep. neg_lits.
    do 4 zstep. zstep_sh0. do 11 zstep.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ (Forall_impl _ (own_ivA_PB _ PB _) FW) (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
      assert (AGP5 : agrees_on (fun a => in_block (CLc ++ PB) a) m mm)
        by (eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha;
            exact (pb_outside _ _ _ GL _ _ _ [] (CLc ++ PB) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a Ha));
      pose proof (munch_refl [(fflagA L FF_CHECK_HEADER Fb, fflagA L FF_CHECK_HEADER Fb + 1)]%Z mm) as MU2; pose proof (wmono_refl asegs mm) as WM2
    end.
    destruct (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G5) as (FLC & _).
    clear MU WM.
    zstep.
    apply evtF_done. eapply FRET; [exact G5 | unfold ff_class; lia | exact MU2 | exact WM2 | exact FLC |].
    intros s3' G6 OF3 LC3 TL3.
    clear FRNG FSRNG FLR kF kFr kF1 kF2 bF bFr bFhi bFlo bFimg bG bGr bGhi bGlo bGimg SHLO.
    zstep.
    do 16 zstep.
    release_frame FRA ST (SPA + 88)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST STG ltac:(lia)) as ST3. clear ST STG.
    release_frame FR ST3 (bv_unsigned sp).
    destruct (flag_keeps _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ CLc (bv_unsigned sp) G5 MU2 WM2 (incl_appl _ (incl_refl _)) ltac:(lia)) as [AG6 AGP6].
    apply evtF_done. subst POSTQ. cbv beta iota.
    split; [reflexivity|]. split; [reflexivity|].
    do 14 eexists. lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end.
    split; [reflexivity|]. split; [assumption|]. split; [exact ST3|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a K; split; [exact K| exact I] | exact AG6]. }
    split. { eapply agrees_on_trans; [exact AGP5| exact AGP6]. }
    split; [exact G6| exact OF3].
  Qed.
  End Sz2.
  #[using="tlsI GL FRET"] Lemma chk_epi : ltac:(let t := eval cbv delta [chk_epi__stmt] in chk_epi__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CLc PB FB FL lo SPA Fb m ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r18 r19 r20 r21 r22 r23 r27 t3 t4 t5 t6 jS k0 k1 k2 fj b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 A x. ltac2:(SecDiet.SzSec.closeP 'chk_epi__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkEpi.
End CANSEC1.
End TwB.
End F_sfchk_epiA.

(* [comment removed for export] *)
Module F_ngblk_kitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_defsA.
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


Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section RbKit2.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  (* [comment removed for export] *)
  Definition rb_keeps_sh__stmt : Prop := forall (ra sp tp s0 : word) L RNG (C1 C2 FB : list (@cblock hptr)) FL trC lo P CUR EB Af SPA self f m
      RNGx sx (CLx : list (@cblock hptr)) FLx mm,
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    GIOA L RNGx sx CLx FB FLx mm -> incl (C1 ++ C2) CLx -> incl FL FLx ->
    agrees_on (fun a => client_keeps FL (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m mm ->
    agrees_on (in_frame_sh FL) m mm.
  Section Sz1.
  Variables ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m RNGx sx CLx FLx mm : ltac2:(SecDiet.SzSec.tyM 'rb_keeps_sh__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="FO fflagA GL"] Lemma rb_keeps_sh__body : ltac2:(SecDiet.SzSec.bodyP 'rb_keeps_sh__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros CTX G ICL IFL AG.
    destruct CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & RR & UC & TR & NF & HinF & HinP & (CUR1 & CUR2) & CUR8 & EBM & EB8 & SPAB & SPA32).
    unfold READ_BLOCK_STACK, PCAP_L1_STACK in BU.
    eapply agrees_on_weaken; [exact AG|]. intros a Ha.
    pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G (in_frame_sh_incl _ _ _ IFL Ha)) as BD.
    assert (HinP' : In (self, P, PCAP_NG_SF_TOTAL) (CLx ++ FB)) by (apply in_or_app; left; apply ICL; exact HinP).
    destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP') as ((PBAND & _) & _). cbn [cb_addr cb_size fst snd] in PBAND. unfold PCAP_NG_SF_TOTAL in PBAND.
    pose proof (ablk_clear_band _ _ a PBAND ltac:(unfold KLS; lia)) as NP.
    split; [right; right; right; exact Ha|]. split; [lia|]. split; [lia|].
    destruct EBM as [((LOC & (_ & _ & _ & _ & _ & _ & EBAND)) & _)| <-]; [| lia].
    exact (ablk_clear_band _ _ a EBAND ltac:(unfold KLS; lia)).
  Qed.
  End Sz1.
  #[using="FO fflagA GL"] Lemma rb_keeps_sh : ltac:(let t := eval cbv delta [rb_keeps_sh__stmt] in rb_keeps_sh__stmt in exact t).
  Proof. intros ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m RNGx sx CLx FLx mm. ltac2:(SecDiet.SzSec.closeP 'rb_keeps_sh__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition rb_eb_facts__stmt : Prop := forall (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 tp : word) L RNG (C1 C2 FB : list (@cblock hptr)) FL trC lo P CUR EB Af SPA Fb self f o m
      RNGx sx bq B alloc mm,
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx bq B alloc mm ->
    (0 < alloc)%Z ->
    cobjA RNGx mm ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(bq, B, alloc)]) EB 256
    /\ clocA FL (C1 ++ C2) EB 256
    /\ (0x603000 <= EB /\ EB + 256 <= ATOP)%Z
    /\ exists k1 k2 k3 kB kF : Z,
         (0 <= k1 <= 1 /\ EB + 256 <= P + 20 + k1 * 18446744073709551616 /\ P + 32 <= EB + (1 - k1) * 18446744073709551616)%Z
      /\ (0 <= k2 <= 1 /\ EB + 256 <= P + 48 + k2 * 18446744073709551616 /\ P + 60 <= EB + (1 - k2) * 18446744073709551616)%Z
      /\ (0 <= k3 <= 1 /\ EB + 256 <= P + 656 + k3 * 18446744073709551616 /\ P + 660 <= EB + (1 - k3) * 18446744073709551616)%Z
      /\ (0 <= kB <= 1 /\ EB + 256 <= B + kB * 18446744073709551616 /\ B + alloc <= EB + (1 - kB) * 18446744073709551616)%Z
      /\ (0 <= kF <= 1 /\ EB + 256 <= Fb + kF * 18446744073709551616 /\ Fb + 64 <= EB + (1 - kF) * 18446744073709551616)%Z.
  Section Sz2.
  Variables ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 tp L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f o m RNGx sx bq B alloc mm : ltac2:(SecDiet.SzSec.tyM 'rb_eb_facts__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="FO GL"] Lemma rb_eb_facts__body : ltac2:(SecDiet.SzSec.bodyP 'rb_eb_facts__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros CTX INV AL0.
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & _ & _ & _).
    assert (ICL : incl (C1 ++ C2) ((C1 ++ C2) ++ [(bq, B, alloc)])) by (apply incl_appl, incl_refl).
    assert (IFL : incl FL ((FF_READ_BLOCK, Fb, 64%Z) :: FL)) by (apply incl_tl, incl_refl).
    pose proof (rb_keeps_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX G ICL IFL AG) as AGsh.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & RR & UC & TR & NF & HinF & HinP & (CUR1 & CUR2) & CUR8 & EBM & EB8 & SPAB & SPA32).
    assert (HinP' : In (self, P, PCAP_NG_SF_TOTAL) (((C1 ++ C2) ++ [(bq, B, alloc)]) ++ FB)) by (apply in_or_app; left; apply ICL; exact HinP).
    assert (HinB : In (bq, B, alloc) [(bq, B, alloc)]) by (left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP') as PBLK.
    assert (LOC : clocA FL (C1 ++ C2) EB 256).
    { destruct EBM as [((LOC & _) & _)| <-]; [exact LOC|]. left. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    pose proof (clocA_incl _ _ _ _ _ _ LOC ICL IFL) as LOC'.
    split.
    { split; [exact LOC'|]. destruct EBM as [(OEB & _)| <-].
      - exact (proj2 (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G ICL IFL AGsh ltac:(lia))).
      - eapply blockA_aobj; [exact PBLK| cbn [cb_addr cb_size fst snd]; lia| cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia| lia]. }
    split; [exact LOC|].
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G LOC') as (EBLO & EBHI).
    pose proof PBLK as ((_ & _ & PTOP & _) & P1 & _). cbn [cb_addr cb_size fst snd] in PTOP, P1. unfold PCAP_NG_SF_TOTAL in PTOP.
    split; [split; [exact EBLO| exact EBHI]|].
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ LOC (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kB & kBr & kB1 & kB2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ LOC ICL (incl_refl _)) ltac:(lia)) as (kF & kFr & kF1 & kF2).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kB1, kB2, kF1, kF2.
    destruct EBM as [(_ & _ & [EP|EP])| <-].
    - exists 0%Z, 0%Z, 0%Z, kB, kF. unfold PCAP_NG_SF_TOTAL in EP. repeat split; lia.
    - exists 1%Z, 1%Z, 1%Z, kB, kF. unfold PCAP_NG_SF_TOTAL in EP. repeat split; lia.
    - exists 1%Z, 1%Z, 0%Z, kB, kF. repeat split; lia.
  Qed.
  End Sz2.
  #[using="FO GL"] Lemma rb_eb_facts : ltac:(let t := eval cbv delta [rb_eb_facts__stmt] in rb_eb_facts__stmt in exact t).
  Proof. intros ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 tp L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f o m RNGx sx bq B alloc mm. ltac2:(SecDiet.SzSec.closeP 'rb_eb_facts__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition rb_keeps_not_PB__stmt : Prop := forall L RNG s (CLc PB FB : list (@cblock hptr)) FL FLc m SP a,
    GIOA L RNG s (CLc ++ PB) FB FL m -> incl FLc FL -> (ATOP <= SP)%Z -> client_keeps FLc CLc SP a -> ~ in_block PB a.
  Section Sz3.
  Variables L RNG s CLc PB FB FL FLc m SP a : ltac2:(SecDiet.SzSec.tyM 'rb_keeps_not_PB__stmt "vvvvvvvvvvv" @L).
  #[using="tlsI FO fflagA GL"] Lemma rb_keeps_not_PB__body : ltac2:(SecDiet.SzSec.bodyP 'rb_keeps_not_PB__stmt "vvvvvvvvvvv").
  Proof.
    intros G IFL HSP K Hin.
    assert (HaB : in_block ((CLc ++ PB) ++ FB) a) by (apply in_block_app; left; apply in_block_app; right; exact Hin).
    destruct K as [K|[K|[K|K]]].
    - pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G HaB). lia.
    - apply in_block_In in K as (b & Hb & Hr). apply in_block_In in Hin as (b' & Hb' & Hr').
      pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _).
      apply blocks_apart_app_inv in BA as (_ & _ & BX). specialize (BX b b' Hb Hb'). unfold apart in BX. lia.
    - exact (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G (in_frames_incl _ _ _ IFL K) HaB).
    - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G (in_frame_sh_incl _ _ _ IFL K)) as BD.
      apply in_block_In in HaB as (b & Hb & Hr). destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G Hb) as ((BB & _) & _).
      exact (ablk_clear_band _ _ a BB ltac:(unfold KLS; lia) Hr).
  Qed.
  End Sz3.
  #[using="tlsI FO fflagA GL"] Lemma rb_keeps_not_PB : ltac:(let t := eval cbv delta [rb_keeps_not_PB__stmt] in rb_keeps_not_PB__stmt in exact t).
  Proof. intros L RNG s CLc PB FB FL FLc m SP a. ltac2:(SecDiet.SzSec.closeP 'rb_keeps_not_PB__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition rb_inv_callee__stmt : Prop := forall (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock)
      (lo P CUR EB SPA Fb : Z) (o : option hptr) (m : mem) (RNGx : footprint) (sx : PState H hptr) (bq : hptr) (B alloc : Z) (mm : mem)
      (RNGy : footprint) (sy : PState H hptr) (my : mem) (Pn : Z -> Prop),
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx bq B alloc mm ->
    (ATOP <= SPA)%Z -> (SPA <= bv_unsigned sp - 192)%Z ->
    fp_le RNGx RNGy -> GIOA L RNGy sy ((C1 ++ C2) ++ [(bq, B, alloc)]) FB ((FF_READ_BLOCK, Fb, 64%Z) :: FL) my -> ps_outfile sy = ps_outfile sx ->
    mem_inv asegs my -> stk asegs my lo SPA ->
    agrees_on (fun a => client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(bq, B, alloc)]) SPA a /\ Pn a) mm my ->
    (forall a, (SPA <= a)%Z -> Pn a) ->
    (forall a, (Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 8)%Z -> Pn a) ->
    (forall a, (Fb <= a < Fb + 32 \/ Fb + 40 <= a < Fb + 64)%Z -> Pn a) ->
    (forall a, client_keeps FL (C1 ++ C2) (bv_unsigned sp) a -> ~ in_block [(bq, B, alloc)] a -> ~ (Fb <= a < Fb + 64)%Z -> Pn a) ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGy sy bq B alloc my.
  Section Sz4.
  Variables ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx bq B alloc mm RNGy sy my Pn : ltac2:(SecDiet.SzSec.tyM 'rb_inv_callee__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="tlsI FO GL"] Lemma rb_inv_callee__body : ltac2:(SecDiet.SzSec.bodyP 'rb_inv_callee__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros INV HSPA HSP FPy Gy OFy MIy STy AGy PST PSH PFR PCL.
    destruct INV as (FP & G & OF & MI & ST & STG & FR & AG & (k0 & k1 & k2 & pre & FRC1) & (post & FRC3) & SHC).
    unfold rb_inv. split; [eapply fp_le_trans; [exact FP| exact FPy]|]. split; [exact Gy|]. split; [congruence|]. split; [exact MIy|]. split; [exact STy|].
    assert (INFR : forall a, (Fb <= a < Fb + 64)%Z -> in_frames ((FF_READ_BLOCK, Fb, 64%Z) :: FL) a).
    { intros a Ha. apply in_frames_In. exists (FF_READ_BLOCK, Fb, 64%Z). split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]. }
    assert (INSH : forall a, (Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 8)%Z -> in_frame_sh ((FF_READ_BLOCK, Fb, 64%Z) :: FL) a).
    { intros a Ha. apply in_frame_sh_In. exists (FF_READ_BLOCK, Fb, 64%Z). split; [left; reflexivity|].
      cbn [fb_addr fb_size fst snd]. change (Z.shiftr 64 3) with 8%Z. exact Ha. }
    split. { eapply agrees_stk; [exact AGy| exact STG|]. intros a Ha. split; [left; lia| apply PST; lia]. }
    split. { eapply agrees_rw_cells; [exact AGy| exact FR|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. split; [left; lia| apply PST; lia]. }
    split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AGy|]. intros a (K & N1 & N2 & N3).
             assert (NB : ~ in_block [(bq, B, alloc)] a) by (assert (HSPX : (ATOP <= bv_unsigned sp)%Z) by lia; exact (rb_keeps_not_PB _ _ _ _ _ _ _ _ _ _ a G (incl_tl _ (incl_refl _)) HSPX K)).
             assert (NF : ~ (Fb <= a < Fb + 64)%Z).
             { intros Hf. destruct K as [K|[K|[K|K]]].
               - pose proof (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (Forall_inv FA) as (_ & FT & _). cbn [fb_addr fb_size fst snd] in FT. lia.
               - exact (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G (INFR a Hf) (proj2 (in_block_app _ _ _) (or_introl (proj2 (in_block_app _ _ _) (or_introl K))))).
               - apply in_frames_In in K as (fr & Hfr & Hr).
                 destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [_ ND]. cbn [map] in ND. apply NoDup_cons_iff in ND as [NI _].
                 assert (NE : fb_fn (FF_READ_BLOCK, Fb, 64%Z) <> fb_fn fr) by (intros E; apply NI; rewrite E; apply in_map; exact Hfr).
                 pose proof (gl_fr_disj _ _ _ GL _ _ _ _ _ _ _ (FF_READ_BLOCK, Fb, 64%Z) fr G (or_introl eq_refl) (or_intror Hfr) NE) as D.
                 cbn [fb_addr fb_size fst snd] in D. lia.
               - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G (in_frame_sh_cons _ _ _ K)) as BD.
                 pose proof (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (Forall_inv FA) as (FBD & _). cbn [fb_addr fb_size fst snd] in FBD.
                 exact (ablk_clear_band _ _ a FBD ltac:(unfold KLS; lia) Hf). }
             split; [| exact (PCL a K NB NF)].
             destruct K as [K|[K|[K|K]]]; [left; lia| right; left; apply in_block_app; left; exact K
                                          | right; right; left; apply in_frames_cons; exact K| right; right; right; apply in_frame_sh_cons; exact K]. }
    split. { exists k0, k1, k2, pre. eapply agrees_rw_cells; [exact AGy| exact FRC1|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
             split; [right; right; left; apply INFR; lia| apply PFR; lia]. }
    split. { exists post. eapply agrees_rw_cells; [exact AGy| exact FRC3|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
             split; [right; right; left; apply INFR; lia| apply PFR; lia]. }
    eapply agrees_rw_cells; [exact AGy| exact SHC|]. intros a Ha. unfold rb_shadow in Ha. cbn [cells_size csize Nat.add] in Ha.
    split; [right; right; right; apply INSH; lia| apply PSH; lia].
  Qed.
  End Sz4.
  #[using="tlsI FO GL"] Lemma rb_inv_callee : ltac:(let t := eval cbv delta [rb_inv_callee__stmt] in rb_inv_callee__stmt in exact t).
  Proof. intros ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx bq B alloc mm RNGy sy my Pn. ltac2:(SecDiet.SzSec.closeP 'rb_inv_callee__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbKit2.
End CANSEC1.

(* [comment removed for export] *)
Ltac rb_setup GL CTX INV AL0 :=
  pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & HinP & (CUR1 & CUR2) & CUR8 & EBM & EB8 & SPAB & SPA32);
  pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & (k0 & k1 & k2 & pre & FRC1) & (post & FRC3) & SHC);
  unfold READ_BLOCK_STACK, PCAP_L1_STACK in BU; unfold rb_shadow in SHC;
  lazymatch type of ALN with (bv_unsigned ?sp mod 16 = 0)%Z => pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP end;
  destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll FND]; pose proof (Forall_inv FAll) as FRM; pose proof FRM as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR);
  cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR; clear FAll; change (Z.shiftr 64 3) with 8%Z in FSRNG, FSWR;
  pose proof (ablk_lin _ _ FBAND') as (_ & Fb0 & _ & _); (let bF := fresh "bF" in band_ind FBAND' bF);
  destruct (rb_eb_facts _ _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX INV AL0)
    as (OEB & EBLOC & (EBLO & EBHI) & (kE1 & kE2 & kE3 & kEB & kEF & (kE1r & kE1a & kE1b) & (kE2r & kE2a & kE2b) & (kE3r & kE3a & kE3b) & (kEBr & kEBa & kEBb) & (kEFr & kEFa & kEFb)));
  pose proof OEB as (_ & _ & _ & EBUNP & EBRNG & EBRSH & _ & EBBAND); rewrite EB8, Z.sub_0_r, Z.add_0_r in EBRSH; (let bE := fresh "bE" in band_ind EBBAND bE);
  lazymatch type of G with ?GG _ _ _ (?CL ++ [(?bq, ?B, ?alloc)]) ?FB ((FF_READ_BLOCK, ?Fb, _) :: ?FL) _ =>
    assert (ICL : incl CL (CL ++ [(bq, B, alloc)])) by (apply incl_appl, incl_refl);
    assert (IFL : incl FL ((FF_READ_BLOCK, Fb, 64%Z) :: FL)) by (apply incl_tl, incl_refl);
    assert (SHQ : (Fb = 8 * Z.shiftr Fb 3)%Z) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia);
    assert (SLO : (2147450880 <= Z.shiftr Fb 3 + 2147450880)%Z) by lia;
    assert (SHI : (Z.shiftr Fb 3 + 2147450880 + 8 <= 17594333495296)%Z) by lia;
    assert (HinP' : In (_, _, PCAP_NG_SF_TOTAL) ((CL ++ [(bq, B, alloc)]) ++ FB)) by (apply in_or_app; left; apply ICL; exact HinP);
    assert (HinB' : In (bq, B, alloc) ((CL ++ [(bq, B, alloc)]) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity);
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP') as PBLK; pose proof PBLK as ((PBAND & _ & PTOP & P2) & P1 & PUNP & PRNG & PRSH & _);
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinB') as BBLK; pose proof BBLK as ((BBAND & _ & BTOP & B2) & B1 & BUNP & BRNG & BRSH & _);
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P2, P1, PUNP, PRNG, PRSH, BBAND, BTOP, B2, B1, BUNP, BRNG, BRSH;
    unfold PCAP_NG_SF_TOTAL in PBAND, PTOP, PUNP, PRNG, PRSH;
    (let bP := fresh "bP" in band_ind PBAND bP); (let bB := fresh "bB" in band_ind BBAND bB);
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ G HinP' (or_introl eq_refl) ltac:(cbn [cb_size snd]; unfold PCAP_NG_SF_TOTAL; lia)) as (kPF & kPFr & kPF1 & kPF2);
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ G HinB' (or_introl eq_refl) ltac:(cbn [cb_size snd]; lia)) as (kBF & kBFr & kBF1 & kBF2);
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2, kBF1, kBF2; unfold PCAP_NG_SF_TOTAL in kPF1, kPF2;
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA; apply blocks_apart_app_inv in BA as (BA & _ & _); apply blocks_apart_app_inv in BA as (_ & _ & BX);
    pose proof (BX _ _ HinP (or_introl eq_refl)) as APB; clear BX; try clear BA; unfold apart in APB; cbn [cb_addr cb_size fst snd] in APB; unfold PCAP_NG_SF_TOTAL in APB;
    (let kPB := fresh "kPB" in disj_ind APB kPB); clear APB; clear EBM;
    apply (rng_fp_le _ _ _ _ FP) in RSTK; apply (rng_fp_le _ _ _ _ FP) in RIMG; apply (rng_fp_le _ _ _ _ FP) in RISH; apply (rng_fp_le _ _ _ _ FP) in RTLS;
    lazymatch type of RSTK with rng ?RNGx ?lo _ => lazymatch type of SPAB with (_ <= ?SPA <= bv_unsigned ?sp - _)%Z =>
      assert (RSPW : rng RNGx lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]);
      assert (RSPA : rng RNGx SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]) end end;
    lazymatch type of CUR8 with (?CUR mod 8 = 0)%Z =>
      destruct (gl_stack _ _ _ GL _ _ _ _ _ _ _ CUR 24%Z G ltac:(lia) ltac:(lia) CUR2) as (CURUNP & CURAR);
      pose proof (arenaA_sh_rng _ _ _ _ CURAR ltac:(lia) ltac:(lia)) as CURSH; rewrite CUR8, Z.sub_0_r, Z.add_0_r in CURSH;
      lazymatch type of RSTK with rng ?RNGx _ _ => assert (CURRNG : rng RNGx CUR 24) by (eapply rng_sub'; [exact RSTK| lia]) end
    end
  end.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_defsA.TwB.
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


Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section RbKit2.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  (* [comment removed for export] *)
  Definition rb_keeps_sh__stmt : Prop := forall (ra sp tp s0 : word) L RNG (C1 C2 FB : list (@cblock hptr)) FL trC lo P CUR EB Af SPA self f m
      RNGx sx (CLx : list (@cblock hptr)) FLx mm,
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    GIOA L RNGx sx CLx FB FLx mm -> incl (C1 ++ C2) CLx -> incl FL FLx ->
    agrees_on (fun a => client_keeps FL (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m mm ->
    agrees_on (in_frame_sh FL) m mm.
  Section Sz1.
  Variables ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m RNGx sx CLx FLx mm : ltac2:(SecDiet.SzSec.tyM 'rb_keeps_sh__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="FO fflagA GL"] Lemma rb_keeps_sh__body : ltac2:(SecDiet.SzSec.bodyP 'rb_keeps_sh__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros CTX G ICL IFL AG.
    destruct CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & RR & UC & TR & NF & HinF & HinP & (CUR1 & CUR2) & CUR8 & EBM & EB8 & SPAB & SPA32).
    unfold READ_BLOCK_STACK, PCAP_L1_STACK in BU.
    eapply agrees_on_weaken; [exact AG|]. intros a Ha.
    pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G (in_frame_sh_incl _ _ _ IFL Ha)) as BD.
    assert (HinP' : In (self, P, PCAP_NG_SF_TOTAL) (CLx ++ FB)) by (apply in_or_app; left; apply ICL; exact HinP).
    destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP') as ((PBAND & _) & _). cbn [cb_addr cb_size fst snd] in PBAND. unfold PCAP_NG_SF_TOTAL in PBAND.
    pose proof (ablk_clear_band _ _ a PBAND ltac:(unfold KLS; lia)) as NP.
    split; [right; right; right; exact Ha|]. split; [lia|]. split; [lia|].
    destruct EBM as [((LOC & (_ & _ & _ & _ & _ & _ & EBAND)) & _)| <-]; [| lia].
    exact (ablk_clear_band _ _ a EBAND ltac:(unfold KLS; lia)).
  Qed.
  End Sz1.
  #[using="FO fflagA GL"] Lemma rb_keeps_sh : ltac:(let t := eval cbv delta [rb_keeps_sh__stmt] in rb_keeps_sh__stmt in exact t).
  Proof. intros ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m RNGx sx CLx FLx mm. ltac2:(SecDiet.SzSec.closeP 'rb_keeps_sh__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition rb_eb_facts__stmt : Prop := forall (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 tp : word) L RNG (C1 C2 FB : list (@cblock hptr)) FL trC lo P CUR EB Af SPA Fb self f o m
      RNGx sx bq B alloc mm,
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx bq B alloc mm ->
    (0 < alloc)%Z ->
    cobjA RNGx mm ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(bq, B, alloc)]) EB 256
    /\ clocA FL (C1 ++ C2) EB 256
    /\ (0x604000 <= EB /\ EB + 256 <= ATOP)%Z
    /\ exists k1 k2 k3 kB kF : Z,
         (0 <= k1 <= 1 /\ EB + 256 <= P + 20 + k1 * 18446744073709551616 /\ P + 32 <= EB + (1 - k1) * 18446744073709551616)%Z
      /\ (0 <= k2 <= 1 /\ EB + 256 <= P + 48 + k2 * 18446744073709551616 /\ P + 60 <= EB + (1 - k2) * 18446744073709551616)%Z
      /\ (0 <= k3 <= 1 /\ EB + 256 <= P + 656 + k3 * 18446744073709551616 /\ P + 660 <= EB + (1 - k3) * 18446744073709551616)%Z
      /\ (0 <= kB <= 1 /\ EB + 256 <= B + kB * 18446744073709551616 /\ B + alloc <= EB + (1 - kB) * 18446744073709551616)%Z
      /\ (0 <= kF <= 1 /\ EB + 256 <= Fb + kF * 18446744073709551616 /\ Fb + 64 <= EB + (1 - kF) * 18446744073709551616)%Z.
  Section Sz2.
  Variables ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 tp L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f o m RNGx sx bq B alloc mm : ltac2:(SecDiet.SzSec.tyM 'rb_eb_facts__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="FO GL"] Lemma rb_eb_facts__body : ltac2:(SecDiet.SzSec.bodyP 'rb_eb_facts__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros CTX INV AL0.
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & _ & _ & _).
    assert (ICL : incl (C1 ++ C2) ((C1 ++ C2) ++ [(bq, B, alloc)])) by (apply incl_appl, incl_refl).
    assert (IFL : incl FL ((FF_READ_BLOCK, Fb, 64%Z) :: FL)) by (apply incl_tl, incl_refl).
    pose proof (rb_keeps_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX G ICL IFL AG) as AGsh.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & RR & UC & TR & NF & HinF & HinP & (CUR1 & CUR2) & CUR8 & EBM & EB8 & SPAB & SPA32).
    assert (HinP' : In (self, P, PCAP_NG_SF_TOTAL) (((C1 ++ C2) ++ [(bq, B, alloc)]) ++ FB)) by (apply in_or_app; left; apply ICL; exact HinP).
    assert (HinB : In (bq, B, alloc) [(bq, B, alloc)]) by (left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP') as PBLK.
    assert (LOC : clocA FL (C1 ++ C2) EB 256).
    { destruct EBM as [((LOC & _) & _)| <-]; [exact LOC|]. left. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    pose proof (clocA_incl _ _ _ _ _ _ LOC ICL IFL) as LOC'.
    split.
    { split; [exact LOC'|]. destruct EBM as [(OEB & _)| <-].
      - exact (proj2 (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G ICL IFL AGsh ltac:(lia))).
      - eapply blockA_aobj; [exact PBLK| cbn [cb_addr cb_size fst snd]; lia| cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia| lia]. }
    split; [exact LOC|].
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G LOC') as (EBLO & EBHI).
    pose proof PBLK as ((_ & _ & PTOP & _) & P1 & _). cbn [cb_addr cb_size fst snd] in PTOP, P1. unfold PCAP_NG_SF_TOTAL in PTOP.
    split; [split; [exact EBLO| exact EBHI]|].
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ LOC (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kB & kBr & kB1 & kB2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ LOC ICL (incl_refl _)) ltac:(lia)) as (kF & kFr & kF1 & kF2).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kB1, kB2, kF1, kF2.
    destruct EBM as [(_ & _ & [EP|EP])| <-].
    - exists 0%Z, 0%Z, 0%Z, kB, kF. unfold PCAP_NG_SF_TOTAL in EP. repeat split; lia.
    - exists 1%Z, 1%Z, 1%Z, kB, kF. unfold PCAP_NG_SF_TOTAL in EP. repeat split; lia.
    - exists 1%Z, 1%Z, 0%Z, kB, kF. repeat split; lia.
  Qed.
  End Sz2.
  #[using="FO GL"] Lemma rb_eb_facts : ltac:(let t := eval cbv delta [rb_eb_facts__stmt] in rb_eb_facts__stmt in exact t).
  Proof. intros ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 tp L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f o m RNGx sx bq B alloc mm. ltac2:(SecDiet.SzSec.closeP 'rb_eb_facts__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition rb_keeps_not_PB__stmt : Prop := forall L RNG s (CLc PB FB : list (@cblock hptr)) FL FLc m SP a,
    GIOA L RNG s (CLc ++ PB) FB FL m -> incl FLc FL -> (ATOP <= SP)%Z -> client_keeps FLc CLc SP a -> ~ in_block PB a.
  Section Sz3.
  Variables L RNG s CLc PB FB FL FLc m SP a : ltac2:(SecDiet.SzSec.tyM 'rb_keeps_not_PB__stmt "vvvvvvvvvvv" @L).
  #[using="tlsI FO fflagA GL"] Lemma rb_keeps_not_PB__body : ltac2:(SecDiet.SzSec.bodyP 'rb_keeps_not_PB__stmt "vvvvvvvvvvv").
  Proof.
    intros G IFL HSP K Hin.
    assert (HaB : in_block ((CLc ++ PB) ++ FB) a) by (apply in_block_app; left; apply in_block_app; right; exact Hin).
    destruct K as [K|[K|[K|K]]].
    - pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G HaB). lia.
    - apply in_block_In in K as (b & Hb & Hr). apply in_block_In in Hin as (b' & Hb' & Hr').
      pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _).
      apply blocks_apart_app_inv in BA as (_ & _ & BX). specialize (BX b b' Hb Hb'). unfold apart in BX. lia.
    - exact (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G (in_frames_incl _ _ _ IFL K) HaB).
    - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G (in_frame_sh_incl _ _ _ IFL K)) as BD.
      apply in_block_In in HaB as (b & Hb & Hr). destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G Hb) as ((BB & _) & _).
      exact (ablk_clear_band _ _ a BB ltac:(unfold KLS; lia) Hr).
  Qed.
  End Sz3.
  #[using="tlsI FO fflagA GL"] Lemma rb_keeps_not_PB : ltac:(let t := eval cbv delta [rb_keeps_not_PB__stmt] in rb_keeps_not_PB__stmt in exact t).
  Proof. intros L RNG s CLc PB FB FL FLc m SP a. ltac2:(SecDiet.SzSec.closeP 'rb_keeps_not_PB__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition rb_inv_callee__stmt : Prop := forall (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock)
      (lo P CUR EB SPA Fb : Z) (o : option hptr) (m : mem) (RNGx : footprint) (sx : PState H hptr) (bq : hptr) (B alloc : Z) (mm : mem)
      (RNGy : footprint) (sy : PState H hptr) (my : mem) (Pn : Z -> Prop),
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx bq B alloc mm ->
    (ATOP <= SPA)%Z -> (SPA <= bv_unsigned sp - 192)%Z ->
    fp_le RNGx RNGy -> GIOA L RNGy sy ((C1 ++ C2) ++ [(bq, B, alloc)]) FB ((FF_READ_BLOCK, Fb, 64%Z) :: FL) my -> ps_outfile sy = ps_outfile sx ->
    mem_inv asegs my -> stk asegs my lo SPA ->
    agrees_on (fun a => client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(bq, B, alloc)]) SPA a /\ Pn a) mm my ->
    (forall a, (SPA <= a)%Z -> Pn a) ->
    (forall a, (Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 8)%Z -> Pn a) ->
    (forall a, (Fb <= a < Fb + 32 \/ Fb + 40 <= a < Fb + 64)%Z -> Pn a) ->
    (forall a, client_keeps FL (C1 ++ C2) (bv_unsigned sp) a -> ~ in_block [(bq, B, alloc)] a -> ~ (Fb <= a < Fb + 64)%Z -> Pn a) ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGy sy bq B alloc my.
  Section Sz4.
  Variables ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx bq B alloc mm RNGy sy my Pn : ltac2:(SecDiet.SzSec.tyM 'rb_inv_callee__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="tlsI FO GL"] Lemma rb_inv_callee__body : ltac2:(SecDiet.SzSec.bodyP 'rb_inv_callee__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros INV HSPA HSP FPy Gy OFy MIy STy AGy PST PSH PFR PCL.
    destruct INV as (FP & G & OF & MI & ST & STG & FR & AG & (k0 & k1 & k2 & pre & FRC1) & (post & FRC3) & SHC).
    unfold rb_inv. split; [eapply fp_le_trans; [exact FP| exact FPy]|]. split; [exact Gy|]. split; [congruence|]. split; [exact MIy|]. split; [exact STy|].
    assert (INFR : forall a, (Fb <= a < Fb + 64)%Z -> in_frames ((FF_READ_BLOCK, Fb, 64%Z) :: FL) a).
    { intros a Ha. apply in_frames_In. exists (FF_READ_BLOCK, Fb, 64%Z). split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]. }
    assert (INSH : forall a, (Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 8)%Z -> in_frame_sh ((FF_READ_BLOCK, Fb, 64%Z) :: FL) a).
    { intros a Ha. apply in_frame_sh_In. exists (FF_READ_BLOCK, Fb, 64%Z). split; [left; reflexivity|].
      cbn [fb_addr fb_size fst snd]. change (Z.shiftr 64 3) with 8%Z. exact Ha. }
    split. { eapply agrees_stk; [exact AGy| exact STG|]. intros a Ha. split; [left; lia| apply PST; lia]. }
    split. { eapply agrees_rw_cells; [exact AGy| exact FR|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. split; [left; lia| apply PST; lia]. }
    split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AGy|]. intros a (K & N1 & N2 & N3).
             assert (NB : ~ in_block [(bq, B, alloc)] a) by (assert (HSPX : (ATOP <= bv_unsigned sp)%Z) by lia; exact (rb_keeps_not_PB _ _ _ _ _ _ _ _ _ _ a G (incl_tl _ (incl_refl _)) HSPX K)).
             assert (NF : ~ (Fb <= a < Fb + 64)%Z).
             { intros Hf. destruct K as [K|[K|[K|K]]].
               - pose proof (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (Forall_inv FA) as (_ & FT & _). cbn [fb_addr fb_size fst snd] in FT. lia.
               - exact (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G (INFR a Hf) (proj2 (in_block_app _ _ _) (or_introl (proj2 (in_block_app _ _ _) (or_introl K))))).
               - apply in_frames_In in K as (fr & Hfr & Hr).
                 destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [_ ND]. cbn [map] in ND. apply NoDup_cons_iff in ND as [NI _].
                 assert (NE : fb_fn (FF_READ_BLOCK, Fb, 64%Z) <> fb_fn fr) by (intros E; apply NI; rewrite E; apply in_map; exact Hfr).
                 pose proof (gl_fr_disj _ _ _ GL _ _ _ _ _ _ _ (FF_READ_BLOCK, Fb, 64%Z) fr G (or_introl eq_refl) (or_intror Hfr) NE) as D.
                 cbn [fb_addr fb_size fst snd] in D. lia.
               - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G (in_frame_sh_cons _ _ _ K)) as BD.
                 pose proof (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (Forall_inv FA) as (FBD & _). cbn [fb_addr fb_size fst snd] in FBD.
                 exact (ablk_clear_band _ _ a FBD ltac:(unfold KLS; lia) Hf). }
             split; [| exact (PCL a K NB NF)].
             destruct K as [K|[K|[K|K]]]; [left; lia| right; left; apply in_block_app; left; exact K
                                          | right; right; left; apply in_frames_cons; exact K| right; right; right; apply in_frame_sh_cons; exact K]. }
    split. { exists k0, k1, k2, pre. eapply agrees_rw_cells; [exact AGy| exact FRC1|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
             split; [right; right; left; apply INFR; lia| apply PFR; lia]. }
    split. { exists post. eapply agrees_rw_cells; [exact AGy| exact FRC3|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
             split; [right; right; left; apply INFR; lia| apply PFR; lia]. }
    eapply agrees_rw_cells; [exact AGy| exact SHC|]. intros a Ha. unfold rb_shadow in Ha. cbn [cells_size csize Nat.add] in Ha.
    split; [right; right; right; apply INSH; lia| apply PSH; lia].
  Qed.
  End Sz4.
  #[using="tlsI FO GL"] Lemma rb_inv_callee : ltac:(let t := eval cbv delta [rb_inv_callee__stmt] in rb_inv_callee__stmt in exact t).
  Proof. intros ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx bq B alloc mm RNGy sy my Pn. ltac2:(SecDiet.SzSec.closeP 'rb_inv_callee__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbKit2.
End CANSEC1.

(* [comment removed for export] *)
Ltac rb_setup GL CTX INV AL0 :=
  pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & HinP & (CUR1 & CUR2) & CUR8 & EBM & EB8 & SPAB & SPA32);
  pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & (k0 & k1 & k2 & pre & FRC1) & (post & FRC3) & SHC);
  unfold READ_BLOCK_STACK, PCAP_L1_STACK in BU; unfold rb_shadow in SHC;
  lazymatch type of ALN with (bv_unsigned ?sp mod 16 = 0)%Z => pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP end;
  destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll FND]; pose proof (Forall_inv FAll) as FRM; pose proof FRM as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR);
  cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR; clear FAll; change (Z.shiftr 64 3) with 8%Z in FSRNG, FSWR;
  pose proof (ablk_lin _ _ FBAND') as (_ & Fb0 & _ & _); (let bF := fresh "bF" in band_ind FBAND' bF);
  destruct (rb_eb_facts _ _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX INV AL0)
    as (OEB & EBLOC & (EBLO & EBHI) & (kE1 & kE2 & kE3 & kEB & kEF & (kE1r & kE1a & kE1b) & (kE2r & kE2a & kE2b) & (kE3r & kE3a & kE3b) & (kEBr & kEBa & kEBb) & (kEFr & kEFa & kEFb)));
  pose proof OEB as (_ & _ & _ & EBUNP & EBRNG & EBRSH & _ & EBBAND); rewrite EB8, Z.sub_0_r, Z.add_0_r in EBRSH; (let bE := fresh "bE" in band_ind EBBAND bE);
  lazymatch type of G with ?GG _ _ _ (?CL ++ [(?bq, ?B, ?alloc)]) ?FB ((FF_READ_BLOCK, ?Fb, _) :: ?FL) _ =>
    assert (ICL : incl CL (CL ++ [(bq, B, alloc)])) by (apply incl_appl, incl_refl);
    assert (IFL : incl FL ((FF_READ_BLOCK, Fb, 64%Z) :: FL)) by (apply incl_tl, incl_refl);
    assert (SHQ : (Fb = 8 * Z.shiftr Fb 3)%Z) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia);
    assert (SLO : (2147450880 <= Z.shiftr Fb 3 + 2147450880)%Z) by lia;
    assert (SHI : (Z.shiftr Fb 3 + 2147450880 + 8 <= 17594333495296)%Z) by lia;
    assert (HinP' : In (_, _, PCAP_NG_SF_TOTAL) ((CL ++ [(bq, B, alloc)]) ++ FB)) by (apply in_or_app; left; apply ICL; exact HinP);
    assert (HinB' : In (bq, B, alloc) ((CL ++ [(bq, B, alloc)]) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity);
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP') as PBLK; pose proof PBLK as ((PBAND & _ & PTOP & P2) & P1 & PUNP & PRNG & PRSH & _);
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinB') as BBLK; pose proof BBLK as ((BBAND & _ & BTOP & B2) & B1 & BUNP & BRNG & BRSH & _);
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P2, P1, PUNP, PRNG, PRSH, BBAND, BTOP, B2, B1, BUNP, BRNG, BRSH;
    unfold PCAP_NG_SF_TOTAL in PBAND, PTOP, PUNP, PRNG, PRSH;
    (let bP := fresh "bP" in band_ind PBAND bP); (let bB := fresh "bB" in band_ind BBAND bB);
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ G HinP' (or_introl eq_refl) ltac:(cbn [cb_size snd]; unfold PCAP_NG_SF_TOTAL; lia)) as (kPF & kPFr & kPF1 & kPF2);
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ G HinB' (or_introl eq_refl) ltac:(cbn [cb_size snd]; lia)) as (kBF & kBFr & kBF1 & kBF2);
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2, kBF1, kBF2; unfold PCAP_NG_SF_TOTAL in kPF1, kPF2;
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA; apply blocks_apart_app_inv in BA as (BA & _ & _); apply blocks_apart_app_inv in BA as (_ & _ & BX);
    pose proof (BX _ _ HinP (or_introl eq_refl)) as APB; clear BX; try clear BA; unfold apart in APB; cbn [cb_addr cb_size fst snd] in APB; unfold PCAP_NG_SF_TOTAL in APB;
    (let kPB := fresh "kPB" in disj_ind APB kPB); clear APB; clear EBM;
    apply (rng_fp_le _ _ _ _ FP) in RSTK; apply (rng_fp_le _ _ _ _ FP) in RIMG; apply (rng_fp_le _ _ _ _ FP) in RISH; apply (rng_fp_le _ _ _ _ FP) in RTLS;
    lazymatch type of RSTK with rng ?RNGx ?lo _ => lazymatch type of SPAB with (_ <= ?SPA <= bv_unsigned ?sp - _)%Z =>
      assert (RSPW : rng RNGx lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]);
      assert (RSPA : rng RNGx SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]) end end;
    lazymatch type of CUR8 with (?CUR mod 8 = 0)%Z =>
      destruct (gl_stack _ _ _ GL _ _ _ _ _ _ _ CUR 24%Z G ltac:(lia) ltac:(lia) CUR2) as (CURUNP & CURAR);
      pose proof (arenaA_sh_rng _ _ _ _ CURAR ltac:(lia) ltac:(lia)) as CURSH; rewrite CUR8, Z.sub_0_r, Z.add_0_r in CURSH;
      lazymatch type of RSTK with rng ?RNGx _ _ => assert (CURRNG : rng RNGx CUR 24) by (eapply rng_sub'; [exact RSTK| lia]) end
    end
  end.
End TwB.
End F_ngblk_kitA.
