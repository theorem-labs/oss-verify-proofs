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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA LibcKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA F_ngchk_modelA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_iface_ngA Pcap_iface_ppA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_pcap_open2A__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_sfchk_fsegA__B3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_ngchk_hlenA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA F_ngchk_modelA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_fail3A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_msgA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_hstmtA.
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
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Definition shb_len_fmt : string := "Section Header Block in pcapng dump file has invalid length %zu < _%u_ < %u (BT_SHB_INSANE_MAX)"%string.

(* [comment removed for export] *)
Definition shb_len_msg__stmt : Prop := forall TL hi, Fmt.snprintf 256 shb_len_fmt [AInt 28; AInt (TL + 4294967296 * hi); AInt 1048576] = Msg.shb_invalid_length TL.
Section Sz1.
Variables TL hi : ltac2:(SecDiet.SzSec.tyM 'shb_len_msg__stmt "vv" @TL).
#[using="Type"] Lemma shb_len_msg__body : ltac2:(SecDiet.SzSec.bodyP 'shb_len_msg__stmt "vv").
Proof.
  assert (CV : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.convs (fmt shb_len_fmt) = [Czu; Cu; Cu]) by (vm_compute; reflexivity).
  assert (S32E : s32 (TL + 4294967296 * hi) = s32 TL) by (unfold s32; Z.div_mod_to_equations; lia).
  transitivity (Fmt.snprintf 256 shb_len_fmt [AInt 28; AInt (s32 (TL + 4294967296 * hi)); AInt 1048576]).
  - symmetry. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.snprintf_pargs. rewrite CV.
    apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_cons; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.aeq_same|]. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_cons; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.aeq_s32; reflexivity|].
    apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_cons; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.aeq_same| apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_nil].
  - rewrite S32E. unfold Msg.shb_invalid_length, PCAP_ERRBUF_SIZE. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.snprintf_pargs. fold shb_len_fmt. rewrite CV.
    apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_cons; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.aeq_same|]. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_cons; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.aeq_s32; reflexivity|].
    apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_cons; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.aeq_same| apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_nil].
Qed.
End Sz1.
Lemma shb_len_msg : ltac:(let t := eval cbv delta [shb_len_msg__stmt] in shb_len_msg__stmt in exact t).
Proof. intros TL hi. ltac2:(SecDiet.SzSec.closeP 'shb_len_msg__body "vv"). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcLenfail.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).

  Definition ngc_lenfail__stmt : Prop := ngc_lenfail_stmt HO FO sites GIOA TP fflagA.
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 w24 t3 t4 t5 t6 TL hi j0 j j2 fcs k0 k1 k2 e : ltac2:(SecDiet.SzSec.tyM 'ngc_lenfail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_lenfail__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_lenfail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET SNPRINTF.
 intros CTX INV W24 TLR HIR FRA FRC Hfcs HE HEB.
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    edestruct (ngc_cobj_now FO GIOA TP fflagA GL) as (_ & _ & OEB'); [exact CTX| exact INV|].
    assert (OEBx : cobjA RNGx mm (NGFR Fb :: FL) (CL ++ []) EB 256)
      by (split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB') ICL IFL)| exact (proj2 OEB')]).
    assert (MSG : fmt_at mm 0x220c0 shb_len_fmt)
      by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm 0x220c0 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string shb_len_fmt) ++ [Z_to_bv 8 0])
                               MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
          split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
    cbn [e_fret prims].
    pose proof (munch_refl [(SPA - 16384, SPA); (EB, EB + 256)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    do 7 zstep. zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut.
    { eapply SNPRINTF with (L := L) (s := sx) (CL := (CL ++ [])%list) (FB := FB) (FL := NGFR Fb :: FL) (lo := lo) (DST := EB) (n := 256%Z) (FMTA := 0x220c0%Z)
                           (fs := shb_len_fmt) (args := [AInt 28; AInt (TL + 4294967296 * hi); AInt 1048576]) (junk := e);
        [ rewrite Espa; eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G| exact ST| exact MI| unfold STDIO_STACK, PCAP_L2_STACK; lia]
        | reflexivity | reflexivity | reflexivity | lia | exact MSG | vm_compute; reflexivity | cbn; lia
        | cbn [length firstn]; constructor; [reflexivity|]; constructor; [rewrite <- W24; symmetry; apply Z_to_bv_bv_unsigned|]; constructor; [reflexivity| constructor]
        | exact HEB | exact OEBx ]. }
    cbv beta. intros ms' PO. destruct PO as (av6 & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    unfold STDIO_STACK in MU6.
    assert (INV6 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx [] m6)
      by (eapply (ngc_inv_munch FO GIOA TP fflagA GL) with (n := 256%Z); [exact CTX| exact INV| exact MU6| exact WM6| exact MI6| exact ST6| lia| lia]).
    assert (AGS : agrees_on (fun a => outside [(SPA - 16384, SPA); (EB, EB + 256)]%Z a) mm m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    assert (FRA6 : rw_cells asegs m6 SPA [CB 80 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb); CB 24 j2])
      by (eapply agrees_rw_cells; [exact AGS| exact FRA|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
    assert (FRC6 : rw_cells asegs m6 Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]))
      by (eapply agrees_rw_cells; [exact AGS| exact FRC|]; intros a Ha; rewrite !cells_size_app, Hfcs in Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
    assert (HE6 : rw_cells asegs m6 ERR [C4 z64])
      by (eapply agrees_rw_cells; [exact AGS| exact HE|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
    rewrite shb_len_msg in HEB6.
    pose proof (snprintf_length_le 256 shb_len_fmt [AInt 28; AInt (TL + 4294967296 * hi); AInt 1048576] ltac:(lia)) as LS. rewrite shb_len_msg in LS.
    change (Z.to_nat 256) with 256%nat in HEB6.
    replace (256 - length (Msg.shb_invalid_length TL) - 1)%nat with (255 - length (Msg.shb_invalid_length TL))%nat in HEB6 by lia.
    assert (MOK : Forall (fun z => 0 < z < 256)%Z (Msg.shb_invalid_length TL))
      by (rewrite <- (shb_len_msg TL hi); apply snprintf_ok; [vm_compute; reflexivity| repeat constructor]).
    replace (ret_pc (Z_to_bv 64 0x8afa4)) with (Z_to_bv 64 0x8afa4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply evtF_done. subst POSTQ.
    eapply (ngc_failx FO GIOA TP fflagA GL FRET) with (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (pcX := 0x8afa4%Z) (msg := Msg.shb_invalid_length TL);
      [ exact CTX | exact INV6 | right; right; left; reflexivity | exact FRA6 | reflexivity | exact FRC6 | exact Hfcs | exact HE6 | exact HEB6 | lia | exact MOK ].
  Qed.
  End Sz2.
  Theorem ngc_lenfail : ltac:(let t := eval cbv delta [ngc_lenfail__stmt] in ngc_lenfail__stmt in exact t).
  Proof using GL FRET SNPRINTF. red. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 w24 t3 t4 t5 t6 TL hi j0 j j2 fcs k0 k1 k2 e. ltac2:(SecDiet.SzSec.closeP 'ngc_lenfail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcLenfail.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_fail3A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_msgA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_hstmtA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Definition shb_len_fmt : string := "Section Header Block in pcapng dump file has invalid length %zu < _%u_ < %u (BT_SHB_INSANE_MAX)"%string.

(* [comment removed for export] *)
Definition shb_len_msg__stmt : Prop := forall TL hi, Fmt.snprintf 256 shb_len_fmt [AInt 28; AInt (TL + 4294967296 * hi); AInt 1048576] = Msg.shb_invalid_length TL.
Section Sz1.
Variables TL hi : ltac2:(SecDiet.SzSec.tyM 'shb_len_msg__stmt "vv" @TL).
#[using="Type"] Lemma shb_len_msg__body : ltac2:(SecDiet.SzSec.bodyP 'shb_len_msg__stmt "vv").
Proof.
  assert (CV : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.convs (fmt shb_len_fmt) = [Czu; Cu; Cu]) by (vm_compute; reflexivity).
  assert (S32E : s32 (TL + 4294967296 * hi) = s32 TL) by (unfold s32; Z.div_mod_to_equations; lia).
  transitivity (Fmt.snprintf 256 shb_len_fmt [AInt 28; AInt (s32 (TL + 4294967296 * hi)); AInt 1048576]).
  - symmetry. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.snprintf_pargs. rewrite CV.
    apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_cons; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.aeq_same|]. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_cons; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.aeq_s32; reflexivity|].
    apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_cons; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.aeq_same| apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_nil].
  - rewrite S32E. unfold Msg.shb_invalid_length, PCAP_ERRBUF_SIZE. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.snprintf_pargs. fold shb_len_fmt. rewrite CV.
    apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_cons; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.aeq_same|]. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_cons; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.aeq_s32; reflexivity|].
    apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_cons; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.aeq_same| apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.pargs_nil].
Qed.
End Sz1.
Lemma shb_len_msg : ltac:(let t := eval cbv delta [shb_len_msg__stmt] in shb_len_msg__stmt in exact t).
Proof. intros TL hi. ltac2:(SecDiet.SzSec.closeP 'shb_len_msg__body "vv"). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcLenfail.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).

  Definition ngc_lenfail__stmt : Prop := ngc_lenfail_stmt HO FO sites GIOA TP fflagA.
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 w24 t3 t4 t5 t6 TL hi j0 j j2 fcs k0 k1 k2 e : ltac2:(SecDiet.SzSec.tyM 'ngc_lenfail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_lenfail__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_lenfail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET SNPRINTF.
 intros CTX INV W24 TLR HIR FRA FRC Hfcs HE HEB.
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    edestruct (ngc_cobj_now FO GIOA TP fflagA GL) as (_ & _ & OEB'); [exact CTX| exact INV|].
    assert (OEBx : cobjA RNGx mm (NGFR Fb :: FL) (CL ++ []) EB 256)
      by (split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB') ICL IFL)| exact (proj2 OEB')]).
    assert (MSG : fmt_at mm 0x220c0 shb_len_fmt)
      by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm 0x220c0 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string shb_len_fmt) ++ [Z_to_bv 8 0])
                               MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
          split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
    cbn [e_fret prims].
    pose proof (munch_refl [(SPA - 16384, SPA); (EB, EB + 256)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    do 7 zstep. zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut.
    { eapply SNPRINTF with (L := L) (s := sx) (CL := (CL ++ [])%list) (FB := FB) (FL := NGFR Fb :: FL) (lo := lo) (DST := EB) (n := 256%Z) (FMTA := 0x220c0%Z)
                           (fs := shb_len_fmt) (args := [AInt 28; AInt (TL + 4294967296 * hi); AInt 1048576]) (junk := e);
        [ rewrite Espa; eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G| exact ST| exact MI| unfold STDIO_STACK, PCAP_L2_STACK; lia]
        | reflexivity | reflexivity | reflexivity | lia | exact MSG | vm_compute; reflexivity | cbn; lia
        | cbn [length firstn]; constructor; [reflexivity|]; constructor; [rewrite <- W24; symmetry; apply Z_to_bv_bv_unsigned|]; constructor; [reflexivity| constructor]
        | exact HEB | exact OEBx ]. }
    cbv beta. intros ms' PO. destruct PO as (av6 & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    unfold STDIO_STACK in MU6.
    assert (INV6 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx [] m6)
      by (eapply (ngc_inv_munch FO GIOA TP fflagA GL) with (n := 256%Z); [exact CTX| exact INV| exact MU6| exact WM6| exact MI6| exact ST6| lia| lia]).
    assert (AGS : agrees_on (fun a => outside [(SPA - 16384, SPA); (EB, EB + 256)]%Z a) mm m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    assert (FRA6 : rw_cells asegs m6 SPA [CB 80 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb); CB 24 j2])
      by (eapply agrees_rw_cells; [exact AGS| exact FRA|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
    assert (FRC6 : rw_cells asegs m6 Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]))
      by (eapply agrees_rw_cells; [exact AGS| exact FRC|]; intros a Ha; rewrite !cells_size_app, Hfcs in Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
    assert (HE6 : rw_cells asegs m6 ERR [C4 z64])
      by (eapply agrees_rw_cells; [exact AGS| exact HE|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
    rewrite shb_len_msg in HEB6.
    pose proof (snprintf_length_le 256 shb_len_fmt [AInt 28; AInt (TL + 4294967296 * hi); AInt 1048576] ltac:(lia)) as LS. rewrite shb_len_msg in LS.
    change (Z.to_nat 256) with 256%nat in HEB6.
    replace (256 - length (Msg.shb_invalid_length TL) - 1)%nat with (255 - length (Msg.shb_invalid_length TL))%nat in HEB6 by lia.
    assert (MOK : Forall (fun z => 0 < z < 256)%Z (Msg.shb_invalid_length TL))
      by (rewrite <- (shb_len_msg TL hi); apply snprintf_ok; [vm_compute; reflexivity| repeat constructor]).
    replace (ret_pc (Z_to_bv 64 569084)) with (Z_to_bv 64 569084) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply evtF_done. subst POSTQ.
    eapply (ngc_failx FO GIOA TP fflagA GL FRET) with (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (pcX := 569084%Z) (msg := Msg.shb_invalid_length TL);
      [ exact CTX | exact INV6 | right; right; left; reflexivity | exact FRA6 | reflexivity | exact FRC6 | exact Hfcs | exact HE6 | exact HEB6 | lia | exact MOK ].
  Qed.
  End Sz2.
  Theorem ngc_lenfail : ltac:(let t := eval cbv delta [ngc_lenfail__stmt] in ngc_lenfail__stmt in exact t).
  Proof using GL FRET SNPRINTF. red. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 w24 t3 t4 t5 t6 TL hi j0 j j2 fcs k0 k1 k2 e. ltac2:(SecDiet.SzSec.closeP 'ngc_lenfail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcLenfail.
End CANSEC1.
End TwB.
End F_ngchk_hlenA.

(* [comment removed for export] *)
Module F_aiDA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.


Section AID.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  #[local] Abbreviation SPOA := (std_pre_o GIOA).

  (* [comment removed for export] *)
  Definition add_interface_stmt9 : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (st : PS) (C1 C2 FB : list cblk) (FL : list fblock) (trC : list Z) (P B I CUR EB lo idb_off : Z)
           (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte),
      SPOA L RNG sp tp st (C1 ++ IBLK i I s ++ C2) FB FL lo ADD_INTERFACE_STACK m ->
      ucallerA depth_add_interface L m sp s0 ra trC -> traces_add_interface TP L (bv_unsigned ra) trC -> nofr frames_add_interface FL ->
      pc_priv p = PrivNg s i ->
      In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2) -> In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2) ->
      P + PCAP_NG_SF_TOTAL <= B \/ B + pc_bufalloc p <= P ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 (B + idb_off) -> a2 = Z_to_bv 64 CUR -> a3 = Z_to_bv 64 EB ->
      rw_cells asegs m (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
      rw_cells asegs m (P + PCAP_PRIV_OFF) (ng_cells s I pad) -> ifaces_ok p I m ->
      0 < ng_user_tsresol s < 2^64 -> 0 <= ng_max_blocksize s < 2^32 ->
      rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] -> firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p) ->
      Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32 -> Forall (fun z => 0 <= z < 256) (pc_bufdata p) ->
      rw_cells asegs m CUR (cursor_cells B c cpad) -> (bv_unsigned sp <= CUR /\ CUR + 24 <= al_top L) -> CUR mod 8 = 0 ->
      0 <= idb_off -> idb_off mod 4 = 0 -> cur_off c = idb_off + 8 -> 0 <= cur_remaining c -> cur_off c + cur_remaining c <= Z.of_nat (length (pc_bufdata p)) ->
      0 <= cur_block_type c < 2^32 ->
      rw_cells asegs m EB [CB 256 ej] ->
      ((cobjA RNG m FL (C1 ++ C2) EB 256 /\ (EB + 256 <= CUR \/ CUR + 24 <= EB) /\ (EB + 256 <= P \/ P + PCAP_NG_SF_TOTAL <= EB) /\ (EB + 256 <= B \/ B + pc_bufalloc p <= EB)) \/ (P + 216 = EB)) ->
      implMG RNG (add_interface MOps (prims HO FO sites) p idb_off c) st
        (add_interface_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADD_INTERFACE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition ai_AGP (FL : list fblock) (sp : word) (C1 C2 : list cblk) (P B CUR EB : Z) (p : pcapT) (m m' : mem) : Prop :=
    agrees_on (fun a => client_keeps FL (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + PCAP_PRIV_OFF <= a < P + PCAP_NG_SF_TOTAL)
                        /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256) /\ ~ (B <= a < B + pc_bufalloc p)) m m'.
  (* [comment removed for export] *)
  Definition ai_FRAME (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m' : mem) : Prop :=
    rw_cells asegs m' (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition ai_REST (L : alayout) (RNG' : footprint) (FL : list fblock) (C1 C2 FB : list cblk) (P B CUR EB : Z) (p : pcapT) (s : pcap_ng_sf) (c : cursor) (ej : list byte) (o : option hptr)
      (m' : mem) (st' : PS) (r : bool * cursor * pcapT * list Z) : Prop :=
    let '(ok, c', p', msg) := r in
    exists (s' : pcap_ng_sf) (i' : option hptr) (I' : Z) (pad' bs' : list byte),
      ps_outfile st' = o /\ p' = set_ng s' i' (set_bufdata (pc_bufdata p') p)
      /\ GIOA L RNG' st' (IBLK i' I' s' ++ C1 ++ C2) FB FL m'
      /\ rw_cells asegs m' (P + PCAP_PRIV_OFF) (ng_cells s' I' pad')
      /\ ng_user_tsresol s' = ng_user_tsresol s /\ ng_max_blocksize s' = ng_max_blocksize s /\ 0 <= ng_ifcount s' < 2^32 /\ 0 <= ng_ifaces_size s' < 2^32
      /\ rw_cells asegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
      /\ length (pc_bufdata p') = length (pc_bufdata p) /\ Forall (fun z => 0 <= z < 256) (pc_bufdata p')
      /\ if ok then
           ifaces_ok p' I' m'
           /\ (exists cpad', rw_cells asegs m' CUR (cursor_cells B c' cpad'))
           /\ 0 <= cur_remaining c' /\ cur_off c <= cur_off c' /\ cur_off c' + cur_remaining c' <= cur_off c + cur_remaining c
           /\ cur_block_type c' = cur_block_type c
           /\ rw_cells asegs m' EB [CB 256 ej] /\ msg = []
         else
           ng_ifaces_closable s' i' I' m'
           /\ (exists ccs', rw_cells asegs m' CUR ccs' /\ cells_size ccs' = 24%nat)
           /\ (exists junk'', rw_cells asegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''])
           /\ Z.of_nat (length msg) < 256 /\ Forall (fun z => 0 < z < 256) msg.
  (* [comment removed for export] *)
  Definition ai_REST_F (L : alayout) (RNG' : footprint) (FL : list fblock) (C1 C2 FB : list cblk) (P B CUR : Z) (p : pcapT) (s : pcap_ng_sf) (o : option hptr)
      (m' : mem) (st' : PS) (c' : cursor) (p' : pcapT) : Prop :=
    exists (s' : pcap_ng_sf) (i' : option hptr) (I' : Z) (pad' bs' : list byte),
      ps_outfile st' = o /\ p' = set_ng s' i' (set_bufdata (pc_bufdata p') p)
      /\ GIOA L RNG' st' (IBLK i' I' s' ++ C1 ++ C2) FB FL m'
      /\ rw_cells asegs m' (P + PCAP_PRIV_OFF) (ng_cells s' I' pad')
      /\ ng_user_tsresol s' = ng_user_tsresol s /\ ng_max_blocksize s' = ng_max_blocksize s /\ 0 <= ng_ifcount s' < 2^32 /\ 0 <= ng_ifaces_size s' < 2^32
      /\ rw_cells asegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
      /\ length (pc_bufdata p') = length (pc_bufdata p) /\ Forall (fun z => 0 <= z < 256)%Z (pc_bufdata p')
      /\ ng_ifaces_closable s' i' I' m'
      /\ (exists ccs', rw_cells asegs m' CUR ccs' /\ cells_size ccs' = 24%nat).
End AID.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.


Section AID.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  #[local] Abbreviation SPOA := (std_pre_o GIOA).

  (* [comment removed for export] *)
  Definition add_interface_stmt9 : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (st : PS) (C1 C2 FB : list cblk) (FL : list fblock) (trC : list Z) (P B I CUR EB lo idb_off : Z)
           (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte),
      SPOA L RNG sp tp st (C1 ++ IBLK i I s ++ C2) FB FL lo ADD_INTERFACE_STACK m ->
      ucallerA depth_add_interface L m sp s0 ra trC -> traces_add_interface TP L (bv_unsigned ra) trC -> nofr frames_add_interface FL ->
      pc_priv p = PrivNg s i ->
      In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2) -> In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2) ->
      P + PCAP_NG_SF_TOTAL <= B \/ B + pc_bufalloc p <= P ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 (B + idb_off) -> a2 = Z_to_bv 64 CUR -> a3 = Z_to_bv 64 EB ->
      rw_cells asegs m (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
      rw_cells asegs m (P + PCAP_PRIV_OFF) (ng_cells s I pad) -> ifaces_ok p I m ->
      0 < ng_user_tsresol s < 2^64 -> 0 <= ng_max_blocksize s < 2^32 ->
      rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] -> firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p) ->
      Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32 -> Forall (fun z => 0 <= z < 256) (pc_bufdata p) ->
      rw_cells asegs m CUR (cursor_cells B c cpad) -> (bv_unsigned sp <= CUR /\ CUR + 24 <= al_top L) -> CUR mod 8 = 0 ->
      0 <= idb_off -> idb_off mod 4 = 0 -> cur_off c = idb_off + 8 -> 0 <= cur_remaining c -> cur_off c + cur_remaining c <= Z.of_nat (length (pc_bufdata p)) ->
      0 <= cur_block_type c < 2^32 ->
      rw_cells asegs m EB [CB 256 ej] ->
      ((cobjA RNG m FL (C1 ++ C2) EB 256 /\ (EB + 256 <= CUR \/ CUR + 24 <= EB) /\ (EB + 256 <= P \/ P + PCAP_NG_SF_TOTAL <= EB) /\ (EB + 256 <= B \/ B + pc_bufalloc p <= EB)) \/ (P + 216 = EB)) ->
      implMG RNG (add_interface MOps (prims HO FO sites) p idb_off c) st
        (add_interface_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADD_INTERFACE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition ai_AGP (FL : list fblock) (sp : word) (C1 C2 : list cblk) (P B CUR EB : Z) (p : pcapT) (m m' : mem) : Prop :=
    agrees_on (fun a => client_keeps FL (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + PCAP_PRIV_OFF <= a < P + PCAP_NG_SF_TOTAL)
                        /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256) /\ ~ (B <= a < B + pc_bufalloc p)) m m'.
  (* [comment removed for export] *)
  Definition ai_FRAME (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m' : mem) : Prop :=
    rw_cells asegs m' (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition ai_REST (L : alayout) (RNG' : footprint) (FL : list fblock) (C1 C2 FB : list cblk) (P B CUR EB : Z) (p : pcapT) (s : pcap_ng_sf) (c : cursor) (ej : list byte) (o : option hptr)
      (m' : mem) (st' : PS) (r : bool * cursor * pcapT * list Z) : Prop :=
    let '(ok, c', p', msg) := r in
    exists (s' : pcap_ng_sf) (i' : option hptr) (I' : Z) (pad' bs' : list byte),
      ps_outfile st' = o /\ p' = set_ng s' i' (set_bufdata (pc_bufdata p') p)
      /\ GIOA L RNG' st' (IBLK i' I' s' ++ C1 ++ C2) FB FL m'
      /\ rw_cells asegs m' (P + PCAP_PRIV_OFF) (ng_cells s' I' pad')
      /\ ng_user_tsresol s' = ng_user_tsresol s /\ ng_max_blocksize s' = ng_max_blocksize s /\ 0 <= ng_ifcount s' < 2^32 /\ 0 <= ng_ifaces_size s' < 2^32
      /\ rw_cells asegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
      /\ length (pc_bufdata p') = length (pc_bufdata p) /\ Forall (fun z => 0 <= z < 256) (pc_bufdata p')
      /\ if ok then
           ifaces_ok p' I' m'
           /\ (exists cpad', rw_cells asegs m' CUR (cursor_cells B c' cpad'))
           /\ 0 <= cur_remaining c' /\ cur_off c <= cur_off c' /\ cur_off c' + cur_remaining c' <= cur_off c + cur_remaining c
           /\ cur_block_type c' = cur_block_type c
           /\ rw_cells asegs m' EB [CB 256 ej] /\ msg = []
         else
           ng_ifaces_closable s' i' I' m'
           /\ (exists ccs', rw_cells asegs m' CUR ccs' /\ cells_size ccs' = 24%nat)
           /\ (exists junk'', rw_cells asegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''])
           /\ Z.of_nat (length msg) < 256 /\ Forall (fun z => 0 < z < 256) msg.
  (* [comment removed for export] *)
  Definition ai_REST_F (L : alayout) (RNG' : footprint) (FL : list fblock) (C1 C2 FB : list cblk) (P B CUR : Z) (p : pcapT) (s : pcap_ng_sf) (o : option hptr)
      (m' : mem) (st' : PS) (c' : cursor) (p' : pcapT) : Prop :=
    exists (s' : pcap_ng_sf) (i' : option hptr) (I' : Z) (pad' bs' : list byte),
      ps_outfile st' = o /\ p' = set_ng s' i' (set_bufdata (pc_bufdata p') p)
      /\ GIOA L RNG' st' (IBLK i' I' s' ++ C1 ++ C2) FB FL m'
      /\ rw_cells asegs m' (P + PCAP_PRIV_OFF) (ng_cells s' I' pad')
      /\ ng_user_tsresol s' = ng_user_tsresol s /\ ng_max_blocksize s' = ng_max_blocksize s /\ 0 <= ng_ifcount s' < 2^32 /\ 0 <= ng_ifaces_size s' < 2^32
      /\ rw_cells asegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
      /\ length (pc_bufdata p') = length (pc_bufdata p) /\ Forall (fun z => 0 <= z < 256)%Z (pc_bufdata p')
      /\ ng_ifaces_closable s' i' I' m'
      /\ (exists ccs', rw_cells asegs m' CUR ccs' /\ cells_size ccs' = 24%nat).
End AID.
End TwB.
End F_aiDA.

(* [comment removed for export] *)
Module F_ngblk_tailA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_pcap_open2A__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_pcap_open2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngblk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_ngblk_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_ngblk_shortA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngblk_segA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.
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




(* [comment removed for export] *)
Tactic Notation "callp" uconstr(SPEC) :=
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ ?m _) => eapply evtF_cut; [ eapply SPEC; [ try eassumption .. ]; lia | post_call segs m ]
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section RbTail.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.

  (* [comment removed for export] *)
  Definition rb_fin__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a5 a6 a7 r19 r22 r23 r25 t3 t4 t5 t6 : word)
      (c0 c1 c2 c4 c5 c8 c9 c10 : word) (cj : list byte) (p p3 : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (B' : Z) (ej : list byte) (bt tl tr : Z),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p3) B' (pc_bufalloc p3) mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 (Z_to_bv 64 (B' + 8)); C8 c4; C8 c5; C8 (Z_to_bv 64 CUR); C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10] ->
    rb_handle p p3 s P B' mm ->
    rw_cells asegs mm (Fb + 32) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)] ->
    rw_cells asegs mm EB [CB 256 ej] -> rw_cells asegs mm CUR [CB 24 cj] ->
    (0 <= bt < 2^32)%Z -> (12 <= tl <= 2^30)%Z -> (0 <= tr < 2^32)%Z ->
    Z.of_nat (length (pc_bufdata p3)) = tl -> Forall (fun z => 0 <= z < 256)%Z (pc_bufdata p3) ->
    implMG RNGx (if negb (tl =? tr)%Z
                 then e_fret (prims HO FO sites) FF_READ_BLOCK (RB_Err (Msg.header_trailer_mismatch tl tr) p3)
                 else e_fret (prims HO FO sites) FF_READ_BLOCK (RB_Ok (mkCursor 8 (tl - 12) bt) p3)) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 (Z_to_bv 64 (s32 tl)) (sx32 (Z_to_bv 64 tr)) a5 a6 a7
               (Z_to_bv 64 Fb) r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Fb + 32)) r22 r23 (Z_to_bv 64 tl) r25
               (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8c000) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a5 a6 a7 r19 r22 r23 r25 t3 t4 t5 t6 c0 c1 c2 c4 c5 c8 c9 c10 cj p p3 s B' ej bt tl tr : ltac2:(SecDiet.SzSec.tyM 'rb_fin__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_fin__body : ltac2:(SecDiet.SzSec.bodyP 'rb_fin__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET SNPRINTF.
 intros CTX INV FRA HDL HBH HEB HCUR BT TL TRR LD3 DR3.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p3)%Z) by lia.
    rb_setup GL CTX INV AL0.
    pose proof (munch_refl [(CUR, CUR + 24)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    cbn [e_fret prims].
    replace (sx32 (Z_to_bv 64 tr)) with (Z_to_bv 64 (s32 tr)) by (symmetry; apply sx32_s32; lia).
    destruct (Z.eq_dec tl tr) as [TE|TNE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) TE). cbn [negb].
      apply implMG_from_evtF.
      zstep. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.eqb_s32 tl tr) by lia. rewrite (proj2 (Z.eqb_eq _ _) TE). cbn [negb]. cbv iota.
      assert (RSP88 : rng RNGx SPA 88) by (eapply rng_sub'; [exact RSPA| lia]).
      assert (RHB : rng RNGx (Fb + 32) 8) by (eapply rng_sub'; [exact FRNG| lia]).
      callp rb_cur_seq.
      lazymatch goal with HH : rw_cells asegs ?mx CUR [_; _; _; CB 4 ?cp] |- _ => rename HH into HCUR2; rename mx into mX; rename cp into cpX end.
      assert (FS : Forall (fun iv : Z * Z => (bv_unsigned sp <= fst iv)%Z) [(CUR, CUR + 24)]%Z) by (apply Forall_cons; [cbn [fst]; lia| apply Forall_nil]).
      destruct (own_writes_s FO GIOA fflagA GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ mX [] [] _ (bv_unsigned sp) (Forall_nil _) (Forall_nil _) FS G MU WM ltac:(lia)) as [G2 AG2].
      cbn [app] in G2, AG2.
      assert (INV2 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p3) B' (pc_bufalloc p3) mX).
      { unfold rb_inv, rb_shadow. split; [exact FP|]. split; [exact G2|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
        split; [assumption|].
        split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG2|]. intros a (K & N1 & N2 & N3). split; [exact K|]. cbn [outside fst snd]. split; [lia| exact I]. }
        split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
      assert (HDL2 : rb_handle p p3 s P B' mX).
      { unfold rb_handle, blk_handle. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
        repeat (split; [assumption|]). assumption. }
      apply evtF_done. subst POSTQ.
      eapply (rb_exit FO GIOA TP fflagA GL GPL FRET) with (p := p) (p' := p3) (B' := B');
        [ exact CTX | exact INV2 | eassumption | reflexivity | exact HDL2 |].
      cbn [rb_result cur_remaining cur_block_type cur_off]. split; [reflexivity|]. split; [reflexivity|]. split; [assumption|].
      split; [exists cpX; exact HCUR2|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact DR3].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) TNE). cbn [negb].
      assert (MSG : fmt_at mm 0x224c0 "block total length in header %u and trailer %u don't match"%string)
        by (fmt_at_solve MI 0x224c0%Z "block total length in header %u and trailer %u don't match"%string).
      replace (Msg.header_trailer_mismatch tl tr) with (Fmt.snprintf 256 "block total length in header %u and trailer %u don't match"%string [AInt (s32 tl); AInt (s32 tr)])
        by (unfold Msg.header_trailer_mismatch, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
            replace (convs (fmt "block total length in header %u and trailer %u don't match")) with [Cu; Cu] by (vm_compute; reflexivity);
            apply pargs_cons; [apply aeq_s32; reflexivity|]; apply pargs_cons; [apply aeq_s32; reflexivity| apply pargs_nil]).
      apply implMG_from_evtF.
      zstep. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.eqb_s32 tl tr) by lia. rewrite (proj2 (Z.eqb_neq _ _) TNE). cbn [negb]. cbv iota.
      do 2 zstep. do 2 zstep. do 2 zstep. zstep.
      apply evtF_done. subst POSTQ.
      eapply (rb_snp FO GIOA TP fflagA GL GPL FRET SNPRINTF) with (pc := 0x8bdac%Z) (p := p) (p' := p3) (B' := B') (ccs' := [CB 24 cj]) (ej' := ej)
               (scs := [C8 c0; C8 c1; C8 c2; C8 (Z_to_bv 64 (B' + 8)); C8 c4; C8 c5; C8 (Z_to_bv 64 CUR); C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10])
               (args := [AInt (s32 tl); AInt (s32 tr)]);
        [ left; reflexivity | exact CTX | exact INV | exact FRA | reflexivity | exact HDL | exact HEB | exact HCUR | reflexivity
        | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
        | apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2] ].
  Qed.
  End Sz1.
  Lemma rb_fin : ltac:(let t := eval cbv delta [rb_fin__stmt] in rb_fin__stmt in exact t).
  Proof using GL GPL FRET SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a5 a6 a7 r19 r22 r23 r25 t3 t4 t5 t6 c0 c1 c2 c4 c5 c8 c9 c10 cj p p3 s B' ej bt tl tr. ltac2:(SecDiet.SzSec.closeP 'rb_fin__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition rb_tail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 t3 t4 t5 t6 : word)
      (c0 c1 c2 c8 c9 c10 : word) (ccs : list cell) (p p2 : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (B' : Z) (ej : list byte) (bt tl : Z),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p2) B' (pc_bufalloc p2) mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 (Z_to_bv 64 (B' + 8)); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (s32 tl));
                           C8 (Z_to_bv 64 CUR); C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10] ->
    rb_handle p p2 s P B' mm ->
    rw_cells asegs mm (Fb + 32) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)] ->
    rw_cells asegs mm EB [CB 256 ej] -> rw_cells asegs mm CUR ccs -> cells_size ccs = 24%nat ->
    (0 <= bt < 2^32)%Z -> (12 <= tl <= 2^30)%Z -> (tl mod 4 = 0)%Z ->
    Z.of_nat (length (pc_bufdata p2)) = tl -> Forall (fun z => 0 <= z < 256)%Z (pc_bufdata p2) ->
    implMG RNGx (let p3 := if pc_swapped p2 then set_bufdata (swap_field 4 (tl - 4) (pc_bufdata p2)) p2 else p2 in
                 let trailer_length := get_le32 (pc_bufdata p3) (tl - 4) in
                 if negb (tl =? trailer_length)%Z
                 then e_fret (prims HO FO sites) FF_READ_BLOCK (RB_Err (Msg.header_trailer_mismatch tl trailer_length) p3)
                 else e_fret (prims HO FO sites) FF_READ_BLOCK (RB_Ok (mkCursor 8 (tl - 12) bt) p3)) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 B') (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Fb + 32)) r22 r23 (Z_to_bv 64 tl) (Z_to_bv 64 (P + 56))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bf84) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 t3 t4 t5 t6 c0 c1 c2 c8 c9 c10 ccs p p2 s B' ej bt tl : ltac2:(SecDiet.SzSec.tyM 'rb_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_tail__body : ltac2:(SecDiet.SzSec.bodyP 'rb_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET SNPRINTF.
 intros CTX INV FRA HDL HBH HEB HCUR Hccs BT TL TL4 LD2 DR2.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p2)%Z) by lia.
    rb_setup GL CTX INV AL0.
    destruct (rw_cells_forget _ _ _ _ HCUR) as [cj HCUR']. rewrite Hccs in HCUR'. clear HCUR.
    (* [comment removed for export] *)
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.lastn4 (pc_bufdata p2) ltac:(lia)) as (dpre & u0 & u1 & u2 & u3 & ED & LPRE).
    pose proof DR2 as DR2'. rewrite ED in DR2'. apply Forall_app in DR2' as [DRP DRU].
    do 4 (apply Forall_cons_iff in DRU; destruct DRU as [? DRU]). clear DRU.
    (* [comment removed for export] *)
    assert (EBS : bs' = map b8 dpre ++ [b8 u0; b8 u1; b8 u2; b8 u3] ++ skipn (length (pc_bufdata p2)) bs').
    { rewrite <- (firstn_skipn (length (pc_bufdata p2)) bs') at 1. rewrite PFX, ED, map_app. cbn [map]. rewrite <- app_assoc. reflexivity. }
    set (rest := skipn (length (pc_bufdata p2)) bs') in *.
    assert (LBS : length bs' = Z.to_nat (pc_bufalloc p2)) by (destruct HBUF as [[WFb _] _]; cbn in WFb; tauto).
    assert (LREST : length rest = (Z.to_nat (pc_bufalloc p2) - Z.to_nat tl)%nat) by (subst rest; rewrite length_skipn; lia).
    assert (HB3 : rw_cells asegs mm B' [CB (length dpre) (map b8 dpre); C4 (Z_to_bv 64 (le4val u0 u1 u2 u3)); CB (length rest) rest]).
    { eapply rw_cells_recell; [exact HBUF | cbn; rewrite length_map; repeat split; exact Logic.I |].
      cbn [cells_bytes cbytes app]. rewrite (le4_lit u0 u1 u2 u3) by lia. rewrite EBS at 1. rewrite ?app_nil_r. reflexivity. }
    clear HBUF.
    assert (LDP : Z.of_nat (length dpre) = (tl - 4)%Z) by lia.
    set (TA := (B' + (tl - 4))%Z).
    destruct (rw_cells_cut _ _ _ 1 HB3) as [HB3a HB3bc]. cbn [firstn skipn cells_size csize Nat.add] in HB3a, HB3bc.
    destruct (rw_cells_cut _ _ _ 1 HB3bc) as [HTR HB3c]. cbn [firstn skipn cells_size csize Nat.add] in HTR, HB3c. clear HB3 HB3bc.
    lazymatch type of HTR with rw_cells _ _ ?A _ => replace A with TA in HTR, HB3c by (subst TA; lia) end.
    lazymatch type of HB3c with rw_cells _ _ ?A _ => replace A with (TA + 4)%Z in HB3c by lia end.
    pose proof (munch_refl [(B', B' + pc_bufalloc p2); (CUR, CUR + 24)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    apply implMG_from_evtF.
    ck0_at PUNP (P + 56)%Z; ck_go.
    zstep. do 3 zstep. zstep.
    replace (B' + tl + -4)%Z with TA by (subst TA; lia).
    assert (ETA : TA = (B' + (tl - 4))%Z) by reflexivity.
    assert (TA4 : (TA mod 4 = 0)%Z) by (subst TA; Z.div_mod_to_equations; lia).
    clearbody TA.
    (* [comment removed for export] *)
    assert (KBUF : forall mx v0 v1 v2 v3, (0 <= v0 < 256)%Z -> (0 <= v1 < 256)%Z -> (0 <= v2 < 256)%Z -> (0 <= v3 < 256)%Z ->
              rw_cells asegs mx B' [CB (length dpre) (map b8 dpre)] -> rw_cells asegs mx TA [C4 (Z_to_bv 64 (le4val v0 v1 v2 v3))] ->
              rw_cells asegs mx (TA + 4) [CB (length rest) rest] ->
              exists bs3, rw_cells asegs mx B' [CB (Z.to_nat (pc_bufalloc p2)) bs3]
                          /\ firstn (length (dpre ++ [v0; v1; v2; v3])) bs3 = map b8 (dpre ++ [v0; v1; v2; v3])).
    { intros mx v0 v1 v2 v3 V0 V1 V2 V3 X1 X2 X3.
      pose proof (rw_cells_uncut _ _ _ _ _ X1 X2 ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
      pose proof (rw_cells_uncut _ _ _ _ _ J1 X3 ltac:(cbn [cells_size csize Nat.add]; lia)) as J2. cbn [app] in J2. clear J1.
      apply (rw_cells_merge asegs mx B' [] [_; _; _] []) in J2. cbn [app] in J2.
      replace (cells_size [CB (length dpre) (map b8 dpre); C4 (Z_to_bv 64 (le4val v0 v1 v2 v3)); CB (length rest) rest]) with (Z.to_nat (pc_bufalloc p2)) in J2
        by (cbn [cells_size csize Nat.add]; lia).
      eexists. split; [exact J2|].
      cbn [cells_bytes cbytes app]. rewrite (le4_lit v0 v1 v2 v3) by lia. rewrite app_nil_r.
      rewrite map_app. cbn [map]. rewrite length_app. cbn [length].
      rewrite (app_assoc (map b8 dpre)). rewrite firstn_app.
      replace (length dpre + 4 - length (map b8 dpre ++ [Z_to_bv 8 v0; Z_to_bv 8 v1; Z_to_bv 8 v2; Z_to_bv 8 v3]))%nat with 0%nat by (rewrite length_app, length_map; cbn [length]; lia).
      rewrite firstn_all2 by (rewrite length_app, length_map; cbn [length]; lia). cbn [firstn]. rewrite app_nil_r. reflexivity. }
    assert (LD2' : Z.of_nat (length dpre) = (tl - 4)%Z) by lia.
    destruct (pc_swapped p2) eqn:ESW.
    - (* [comment removed for export] *)
      cbn [Z.b2z]. replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
      zstep. if_false.
      eapply evtF_cut; [ eapply rb_trl_swap_seq with (B := B') (alloc := pc_bufalloc p2) (bB := bB); [try eassumption ..]; lia | post_call asegs mm ].
      rename POST into HTR2.
      eapply evtF_cut; [ eapply rb_trl_ck_seq with (B := B') (alloc := pc_bufalloc p2) (bB := bB) (v0 := u3) (v1 := u2) (v2 := u1) (v3 := u0); [try eassumption ..]; first [lia | reflexivity] | ].
      cbv beta. intros ms' PO. destruct_exs PO. subst ms'.
      assert (FW : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] [(pc_buffer p2, B', pc_bufalloc p2)] (bv_unsigned sp)) [(B', B' + pc_bufalloc p2)]%Z).
      { apply Forall_cons; [| apply Forall_nil]. right; left. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      assert (FS : Forall (fun iv : Z * Z => (bv_unsigned sp <= fst iv)%Z) [(CUR, CUR + 24)]%Z) by (apply Forall_cons; [cbn [fst]; lia| apply Forall_nil]).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
        destruct (own_writes_s FO GIOA fflagA GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ mx _ [] _ (bv_unsigned sp) FW (Forall_nil _) FS G MU WM ltac:(lia)) as [G2 AG2];
        assert (INV2 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p2) B' (pc_bufalloc p2) mx)
      end.
      { cbn [app] in G2, AG2. unfold rb_inv, rb_shadow. split; [exact FP|]. split; [exact G2|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
        split; [assumption|].
        split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG2|]. intros a (K & N1 & N2 & N3). split; [exact K|]. cbn [outside fst snd]. split; [lia| exact I]. }
        split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
      destruct (KBUF _ u3 u2 u1 u0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HB3a HTR2 HB3c) as (bs3 & HBUF3 & PFX3).
      apply evtF_done. subst POSTQ. cbv zeta. cbv iota.
      cbn [pc_bufdata set_bufdata]. rewrite ED. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.swap_field_last4 dpre u0 u1 u2 u3 tl LD2').
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.get_le32_last4 dpre u3 u2 u1 u0 tl LD2').
      eapply (rb_fin ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx _)
        with (p := p) (p3 := set_bufdata (dpre ++ [u3; u2; u1; u0]) p2) (B' := B') (cj := cj) (tr := le4val u3 u2 u1 u0);
        [ exact CTX | exact INV2 | eassumption | | eassumption | eassumption | eassumption | lia | lia | unfold le4val; lia
        | cbn [pc_bufdata set_bufdata]; rewrite length_app; cbn [length]; lia
        | cbn [pc_bufdata set_bufdata]; apply Forall_app; split; [exact DRP|]; repeat (apply Forall_cons; [lia|]); apply Forall_nil ].
      unfold rb_handle, blk_handle. cbn [pc_bufsize pc_swapped pc_bufalloc pc_bufdata pc_priv pc_rfile pc_self set_bufdata]. rewrite ESW.
      split; [repeat (split; [assumption|]); assumption|]. split; [exists bs3; split; [exact HBUF3| exact PFX3]|].
      split; [rewrite length_app; cbn [length]; lia|].
      repeat (split; [assumption|]). exact E6.
    - (* [comment removed for export] *)
      cbn [Z.b2z]. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
      zstep. if_true.
      eapply evtF_cut; [ eapply rb_trl_ck_seq with (B := B') (alloc := pc_bufalloc p2) (bB := bB) (v0 := u0) (v1 := u1) (v2 := u2) (v3 := u3); [try eassumption ..]; first [lia | reflexivity] | ].
      cbv beta. intros ms' PO. destruct_exs PO. subst ms'.
      apply evtF_done. subst POSTQ. cbv zeta. cbv iota.
      rewrite ED. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.get_le32_last4 dpre u0 u1 u2 u3 tl LD2').
      eapply (rb_fin ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm)
        with (p := p) (p3 := p2) (B' := B') (cj := cj) (tr := le4val u0 u1 u2 u3);
        [ exact CTX | exact INV | eassumption | exact HDL | eassumption | eassumption | eassumption | lia | lia | unfold le4val; lia | exact LD2 | exact DR2 ].
  Qed.
  End Sz2.
  Lemma rb_tail : ltac:(let t := eval cbv delta [rb_tail__stmt] in rb_tail__stmt in exact t).
  Proof using GL GPL FRET SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 t3 t4 t5 t6 c0 c1 c2 c8 c9 c10 ccs p p2 s B' ej bt tl. ltac2:(SecDiet.SzSec.closeP 'rb_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbTail.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_sfchk_fsegA__B3P.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_sfchk_fsegA__B3P.SfAuxB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngblk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_ngblk_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_ngblk_shortA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngblk_segA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB.
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




(* [comment removed for export] *)
Tactic Notation "callp" uconstr(SPEC) :=
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ ?m _) => eapply evtF_cut; [ eapply SPEC; [ try eassumption .. ]; lia | post_call segs m ]
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section RbTail.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.

  (* [comment removed for export] *)
  Definition rb_fin__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a5 a6 a7 r22 r23 r25 t3 t4 t5 t6 : word)
      (c0 c1 c2 c4 c5 c8 c9 c10 : word) (cj : list byte) (p p3 : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (B' : Z) (ej : list byte) (bt tl tr : Z),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p3) B' (pc_bufalloc p3) mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 (Z_to_bv 64 B'); C8 c4; C8 c5; C8 (Z_to_bv 64 CUR); C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10] ->
    rb_handle p p3 s P B' mm ->
    rw_cells asegs mm (Fb + 32) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)] ->
    rw_cells asegs mm EB [CB 256 ej] -> rw_cells asegs mm CUR [CB 24 cj] ->
    (0 <= bt < 2^32)%Z -> (12 <= tl <= 2^30)%Z -> (0 <= tr < 2^32)%Z ->
    Z.of_nat (length (pc_bufdata p3)) = tl -> Forall (fun z => 0 <= z < 256)%Z (pc_bufdata p3) ->
    implMG RNGx (if negb (tl =? tr)%Z
                 then e_fret (prims HO FO sites) FF_READ_BLOCK (RB_Err (Msg.header_trailer_mismatch tl tr) p3)
                 else e_fret (prims HO FO sites) FF_READ_BLOCK (RB_Ok (mkCursor 8 (tl - 12) bt) p3)) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 (Z_to_bv 64 (s32 tl)) (sx32 (Z_to_bv 64 tr)) a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) (Z_to_bv 64 (Fb + 32)) r22 (Z_to_bv 64 tl) r23 r25
               (Z_to_bv 64 (B' + 8)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8c058) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a5 a6 a7 r22 r23 r25 t3 t4 t5 t6 c0 c1 c2 c4 c5 c8 c9 c10 cj p p3 s B' ej bt tl tr : ltac2:(SecDiet.SzSec.tyM 'rb_fin__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_fin__body : ltac2:(SecDiet.SzSec.bodyP 'rb_fin__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET SNPRINTF.
 intros CTX INV FRA HDL HBH HEB HCUR BT TL TRR LD3 DR3.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p3)%Z) by lia.
    rb_setup GL CTX INV AL0.
    pose proof (munch_refl [(CUR, CUR + 24)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    cbn [e_fret prims].
    replace (sx32 (Z_to_bv 64 tr)) with (Z_to_bv 64 (s32 tr)) by (symmetry; apply sx32_s32; lia).
    destruct (Z.eq_dec tl tr) as [TE|TNE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) TE). cbn [negb].
      apply implMG_from_evtF.
      zstep. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.eqb_s32 tl tr) by lia. rewrite (proj2 (Z.eqb_eq _ _) TE). cbn [negb]. cbv iota.
      assert (RSP88 : rng RNGx SPA 88) by (eapply rng_sub'; [exact RSPA| lia]).
      assert (RHB : rng RNGx (Fb + 32) 8) by (eapply rng_sub'; [exact FRNG| lia]).
      callp rb_cur_seq.
      lazymatch goal with HH : rw_cells asegs ?mx CUR [_; _; _; CB 4 ?cp] |- _ => rename HH into HCUR2; rename mx into mX; rename cp into cpX end.
      assert (FS : Forall (fun iv : Z * Z => (bv_unsigned sp <= fst iv)%Z) [(CUR, CUR + 24)]%Z) by (apply Forall_cons; [cbn [fst]; lia| apply Forall_nil]).
      destruct (own_writes_s FO GIOA fflagA GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ mX [] [] _ (bv_unsigned sp) (Forall_nil _) (Forall_nil _) FS G MU WM ltac:(lia)) as [G2 AG2].
      cbn [app] in G2, AG2.
      assert (INV2 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p3) B' (pc_bufalloc p3) mX).
      { unfold rb_inv, rb_shadow. split; [exact FP|]. split; [exact G2|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
        split; [assumption|].
        split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG2|]. intros a (K & N1 & N2 & N3). split; [exact K|]. cbn [outside fst snd]. split; [lia| exact I]. }
        split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
      assert (HDL2 : rb_handle p p3 s P B' mX).
      { unfold rb_handle, blk_handle. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
        repeat (split; [assumption|]). assumption. }
      apply evtF_done. subst POSTQ.
      eapply (rb_exit FO GIOA TP fflagA GL GPL FRET) with (p := p) (p' := p3) (B' := B');
        [ exact CTX | exact INV2 | eassumption | reflexivity | exact HDL2 |].
      cbn [rb_result cur_remaining cur_block_type cur_off]. split; [reflexivity|]. split; [reflexivity|]. split; [assumption|].
      split; [exists cpX; exact HCUR2|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact DR3].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) TNE). cbn [negb].
      assert (MSG : fmt_at mm 0x224c0 "block total length in header %u and trailer %u don't match"%string)
        by (fmt_at_solve MI 0x224c0%Z "block total length in header %u and trailer %u don't match"%string).
      replace (Msg.header_trailer_mismatch tl tr) with (Fmt.snprintf 256 "block total length in header %u and trailer %u don't match"%string [AInt (s32 tl); AInt (s32 tr)])
        by (unfold Msg.header_trailer_mismatch, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
            replace (convs (fmt "block total length in header %u and trailer %u don't match")) with [Cu; Cu] by (vm_compute; reflexivity);
            apply pargs_cons; [apply aeq_s32; reflexivity|]; apply pargs_cons; [apply aeq_s32; reflexivity| apply pargs_nil]).
      apply implMG_from_evtF.
      zstep. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.eqb_s32 tl tr) by lia. rewrite (proj2 (Z.eqb_neq _ _) TNE). cbn [negb]. cbv iota.
      do 2 zstep. do 2 zstep. do 2 zstep. zstep.
      apply evtF_done. subst POSTQ.
      eapply (rb_snp FO GIOA TP fflagA GL GPL FRET SNPRINTF) with (pc := 0x8bd6c%Z) (p := p) (p' := p3) (B' := B') (ccs' := [CB 24 cj]) (ej' := ej)
               (scs := [C8 c0; C8 c1; C8 c2; C8 (Z_to_bv 64 B'); C8 c4; C8 c5; C8 (Z_to_bv 64 CUR); C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10])
               (args := [AInt (s32 tl); AInt (s32 tr)]);
        [ left; reflexivity | exact CTX | exact INV | exact FRA | reflexivity | exact HDL | exact HEB | exact HCUR | reflexivity
        | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
        | apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2] ].
  Qed.
  End Sz1.
  Lemma rb_fin : ltac:(let t := eval cbv delta [rb_fin__stmt] in rb_fin__stmt in exact t).
  Proof using GL GPL FRET SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a5 a6 a7 r22 r23 r25 t3 t4 t5 t6 c0 c1 c2 c4 c5 c8 c9 c10 cj p p3 s B' ej bt tl tr. ltac2:(SecDiet.SzSec.closeP 'rb_fin__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition rb_tail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 t3 t4 t5 t6 : word)
      (c0 c1 c2 c8 c9 c10 : word) (ccs : list cell) (p p2 : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (B' : Z) (ej : list byte) (bt tl : Z),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p2) B' (pc_bufalloc p2) mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 (Z_to_bv 64 B'); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (s32 tl));
                           C8 (Z_to_bv 64 CUR); C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10] ->
    rb_handle p p2 s P B' mm ->
    rw_cells asegs mm (Fb + 32) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)] ->
    rw_cells asegs mm EB [CB 256 ej] -> rw_cells asegs mm CUR ccs -> cells_size ccs = 24%nat ->
    (0 <= bt < 2^32)%Z -> (12 <= tl <= 2^30)%Z -> (tl mod 4 = 0)%Z ->
    Z.of_nat (length (pc_bufdata p2)) = tl -> Forall (fun z => 0 <= z < 256)%Z (pc_bufdata p2) ->
    implMG RNGx (let p3 := if pc_swapped p2 then set_bufdata (swap_field 4 (tl - 4) (pc_bufdata p2)) p2 else p2 in
                 let trailer_length := get_le32 (pc_bufdata p3) (tl - 4) in
                 if negb (tl =? trailer_length)%Z
                 then e_fret (prims HO FO sites) FF_READ_BLOCK (RB_Err (Msg.header_trailer_mismatch tl trailer_length) p3)
                 else e_fret (prims HO FO sites) FF_READ_BLOCK (RB_Ok (mkCursor 8 (tl - 12) bt) p3)) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) (Z_to_bv 64 (Fb + 32)) r22 (Z_to_bv 64 tl) (Z_to_bv 64 (tl + -8)) (Z_to_bv 64 (P + 56))
               (Z_to_bv 64 (B' + 8)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bf5c) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 t3 t4 t5 t6 c0 c1 c2 c8 c9 c10 ccs p p2 s B' ej bt tl : ltac2:(SecDiet.SzSec.tyM 'rb_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_tail__body : ltac2:(SecDiet.SzSec.bodyP 'rb_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET SNPRINTF.
 intros CTX INV FRA HDL HBH HEB HCUR Hccs BT TL TL4 LD2 DR2.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p2)%Z) by lia.
    rb_setup GL CTX INV AL0.
    destruct (rw_cells_forget _ _ _ _ HCUR) as [cj HCUR']. rewrite Hccs in HCUR'. clear HCUR.
    (* [comment removed for export] *)
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.lastn4 (pc_bufdata p2) ltac:(lia)) as (dpre & u0 & u1 & u2 & u3 & ED & LPRE).
    pose proof DR2 as DR2'. rewrite ED in DR2'. apply Forall_app in DR2' as [DRP DRU].
    do 4 (apply Forall_cons_iff in DRU; destruct DRU as [? DRU]). clear DRU.
    (* [comment removed for export] *)
    assert (EBS : bs' = map b8 dpre ++ [b8 u0; b8 u1; b8 u2; b8 u3] ++ skipn (length (pc_bufdata p2)) bs').
    { rewrite <- (firstn_skipn (length (pc_bufdata p2)) bs') at 1. rewrite PFX, ED, map_app. cbn [map]. rewrite <- app_assoc. reflexivity. }
    set (rest := skipn (length (pc_bufdata p2)) bs') in *.
    assert (LBS : length bs' = Z.to_nat (pc_bufalloc p2)) by (destruct HBUF as [[WFb _] _]; cbn in WFb; tauto).
    assert (LREST : length rest = (Z.to_nat (pc_bufalloc p2) - Z.to_nat tl)%nat) by (subst rest; rewrite length_skipn; lia).
    assert (HB3 : rw_cells asegs mm B' [CB (length dpre) (map b8 dpre); C4 (Z_to_bv 64 (le4val u0 u1 u2 u3)); CB (length rest) rest]).
    { eapply rw_cells_recell; [exact HBUF | cbn; rewrite length_map; repeat split; exact Logic.I |].
      cbn [cells_bytes cbytes app]. rewrite (le4_lit u0 u1 u2 u3) by lia. rewrite EBS at 1. rewrite ?app_nil_r. reflexivity. }
    clear HBUF.
    assert (LDP : Z.of_nat (length dpre) = (tl - 4)%Z) by lia.
    set (TA := (B' + (tl - 4))%Z).
    destruct (rw_cells_cut _ _ _ 1 HB3) as [HB3a HB3bc]. cbn [firstn skipn cells_size csize Nat.add] in HB3a, HB3bc.
    destruct (rw_cells_cut _ _ _ 1 HB3bc) as [HTR HB3c]. cbn [firstn skipn cells_size csize Nat.add] in HTR, HB3c. clear HB3 HB3bc.
    lazymatch type of HTR with rw_cells _ _ ?A _ => replace A with TA in HTR, HB3c by (subst TA; lia) end.
    lazymatch type of HB3c with rw_cells _ _ ?A _ => replace A with (TA + 4)%Z in HB3c by lia end.
    pose proof (munch_refl [(B', B' + pc_bufalloc p2); (CUR, CUR + 24)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    apply implMG_from_evtF.
    (* [comment removed for export] *)
    zstep. rewrite (zb_lxor_ones (B' + 8)) by lia.
    zstep. if_cases KG1; [zify_cond KG1; exfalso; lia|].
    do 3 zstep.
    zstep. if_cases KG2; [zify_cond KG2; exfalso; lia|].
    clear KG1 KG2.
    ck0_at PUNP (P + 56)%Z; ck_go.
    zstep. zstep. zstep. zstep.
    replace (Z.land (B' + tl + -4) 3) with 0%Z by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    replace (B' + tl + -4)%Z with TA by (subst TA; lia).
    assert (ETA : TA = (B' + (tl - 4))%Z) by reflexivity.
    assert (TA4 : (TA mod 4 = 0)%Z) by (subst TA; Z.div_mod_to_equations; lia).
    clearbody TA.
    (* [comment removed for export] *)
    assert (KBUF : forall mx v0 v1 v2 v3, (0 <= v0 < 256)%Z -> (0 <= v1 < 256)%Z -> (0 <= v2 < 256)%Z -> (0 <= v3 < 256)%Z ->
              rw_cells asegs mx B' [CB (length dpre) (map b8 dpre)] -> rw_cells asegs mx TA [C4 (Z_to_bv 64 (le4val v0 v1 v2 v3))] ->
              rw_cells asegs mx (TA + 4) [CB (length rest) rest] ->
              exists bs3, rw_cells asegs mx B' [CB (Z.to_nat (pc_bufalloc p2)) bs3]
                          /\ firstn (length (dpre ++ [v0; v1; v2; v3])) bs3 = map b8 (dpre ++ [v0; v1; v2; v3])).
    { intros mx v0 v1 v2 v3 V0 V1 V2 V3 X1 X2 X3.
      pose proof (rw_cells_uncut _ _ _ _ _ X1 X2 ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
      pose proof (rw_cells_uncut _ _ _ _ _ J1 X3 ltac:(cbn [cells_size csize Nat.add]; lia)) as J2. cbn [app] in J2. clear J1.
      apply (rw_cells_merge asegs mx B' [] [_; _; _] []) in J2. cbn [app] in J2.
      replace (cells_size [CB (length dpre) (map b8 dpre); C4 (Z_to_bv 64 (le4val v0 v1 v2 v3)); CB (length rest) rest]) with (Z.to_nat (pc_bufalloc p2)) in J2
        by (cbn [cells_size csize Nat.add]; lia).
      eexists. split; [exact J2|].
      cbn [cells_bytes cbytes app]. rewrite (le4_lit v0 v1 v2 v3) by lia. rewrite app_nil_r.
      rewrite map_app. cbn [map]. rewrite length_app. cbn [length].
      rewrite (app_assoc (map b8 dpre)). rewrite firstn_app.
      replace (length dpre + 4 - length (map b8 dpre ++ [Z_to_bv 8 v0; Z_to_bv 8 v1; Z_to_bv 8 v2; Z_to_bv 8 v3]))%nat with 0%nat by (rewrite length_app, length_map; cbn [length]; lia).
      rewrite firstn_all2 by (rewrite length_app, length_map; cbn [length]; lia). cbn [firstn]. rewrite app_nil_r. reflexivity. }
    assert (LD2' : Z.of_nat (length dpre) = (tl - 4)%Z) by lia.
    destruct (pc_swapped p2) eqn:ESW.
    - (* [comment removed for export] *)
      cbn [Z.b2z]. replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
      zstep. if_false.
      zstep. if_false.   (* [comment removed for export] *)
      eapply evtF_cut; [ eapply rb_trl_swap_seq with (B := B') (alloc := pc_bufalloc p2) (bB := bB); [try eassumption ..]; lia | post_call asegs mm ].
      rename POST into HTR2.
      eapply evtF_cut; [ eapply rb_trl_ck_seq with (B := B') (alloc := pc_bufalloc p2) (bB := bB) (v0 := u3) (v1 := u2) (v2 := u1) (v3 := u0); [try eassumption ..]; first [lia | reflexivity] | ].
      cbv beta. intros ms' PO. destruct_exs PO. subst ms'.
      assert (FW : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] [(pc_buffer p2, B', pc_bufalloc p2)] (bv_unsigned sp)) [(B', B' + pc_bufalloc p2)]%Z).
      { apply Forall_cons; [| apply Forall_nil]. right; left. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      assert (FS : Forall (fun iv : Z * Z => (bv_unsigned sp <= fst iv)%Z) [(CUR, CUR + 24)]%Z) by (apply Forall_cons; [cbn [fst]; lia| apply Forall_nil]).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
        destruct (own_writes_s FO GIOA fflagA GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ mx _ [] _ (bv_unsigned sp) FW (Forall_nil _) FS G MU WM ltac:(lia)) as [G2 AG2];
        assert (INV2 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p2) B' (pc_bufalloc p2) mx)
      end.
      { cbn [app] in G2, AG2. unfold rb_inv, rb_shadow. split; [exact FP|]. split; [exact G2|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
        split; [assumption|].
        split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG2|]. intros a (K & N1 & N2 & N3). split; [exact K|]. cbn [outside fst snd]. split; [lia| exact I]. }
        split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
      destruct (KBUF _ u3 u2 u1 u0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HB3a HTR2 HB3c) as (bs3 & HBUF3 & PFX3).
      apply evtF_done. subst POSTQ. cbv zeta. cbv iota.
      cbn [pc_bufdata set_bufdata]. rewrite ED. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.swap_field_last4 dpre u0 u1 u2 u3 tl LD2').
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.get_le32_last4 dpre u3 u2 u1 u0 tl LD2').
      eapply (rb_fin ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx _)
        with (p := p) (p3 := set_bufdata (dpre ++ [u3; u2; u1; u0]) p2) (B' := B') (cj := cj) (tr := le4val u3 u2 u1 u0);
        [ exact CTX | exact INV2 | eassumption | | eassumption | eassumption | eassumption | lia | lia | unfold le4val; lia
        | cbn [pc_bufdata set_bufdata]; rewrite length_app; cbn [length]; lia
        | cbn [pc_bufdata set_bufdata]; apply Forall_app; split; [exact DRP|]; repeat (apply Forall_cons; [lia|]); apply Forall_nil ].
      unfold rb_handle, blk_handle. cbn [pc_bufsize pc_swapped pc_bufalloc pc_bufdata pc_priv pc_rfile pc_self set_bufdata]. rewrite ESW.
      split; [repeat (split; [assumption|]); assumption|]. split; [exists bs3; split; [exact HBUF3| exact PFX3]|].
      split; [rewrite length_app; cbn [length]; lia|].
      repeat (split; [assumption|]). exact E6.
    - (* [comment removed for export] *)
      cbn [Z.b2z]. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
      zstep. if_true.
      zstep. if_false.   (* [comment removed for export] *)
      eapply evtF_cut; [ eapply rb_trl_ck_seq with (B := B') (alloc := pc_bufalloc p2) (bB := bB) (v0 := u0) (v1 := u1) (v2 := u2) (v3 := u3); [try eassumption ..]; first [lia | reflexivity] | ].
      cbv beta. intros ms' PO. destruct_exs PO. subst ms'.
      apply evtF_done. subst POSTQ. cbv zeta. cbv iota.
      rewrite ED. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.get_le32_last4 dpre u0 u1 u2 u3 tl LD2').
      eapply (rb_fin ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm)
        with (p := p) (p3 := p2) (B' := B') (cj := cj) (tr := le4val u0 u1 u2 u3);
        [ exact CTX | exact INV | eassumption | exact HDL | eassumption | eassumption | eassumption | lia | lia | unfold le4val; lia | exact LD2 | exact DR2 ].
  Qed.
  End Sz2.
  Lemma rb_tail : ltac:(let t := eval cbv delta [rb_tail__stmt] in rb_tail__stmt in exact t).
  Proof using GL GPL FRET SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 t3 t4 t5 t6 c0 c1 c2 c8 c9 c10 ccs p p2 s B' ej bt tl. ltac2:(SecDiet.SzSec.closeP 'rb_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbTail.
End CANSEC1.
End TwB.
End F_ngblk_tailA.

(* [comment removed for export] *)
Module F_ngblk_bodyA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_pcap_open2A__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_pcap_open2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngblk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_ngblk_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_ngblk_shortA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngblk_segA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_ngblk_tailA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
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




(* [comment removed for export] *)
Tactic Notation "callp" uconstr(SPEC) :=
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ ?m _) => eapply evtF_cut; [ eapply SPEC; [ try eassumption .. ]; lia | post_call segs m ]
  end.


(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (s32 _) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- inr64 (s32 _) => fail   (* [comment removed for export] *)
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
Section RbBody.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.

  (* [comment removed for export] *)
  Definition rb_rd2__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c8 c9 c10 : word) (ccs : list cell) (p p0 : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (B0 : Z) (ej : list byte) (bt tl : Z),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p0) B0 (pc_bufalloc p0) mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (s32 tl));
                           C8 (Z_to_bv 64 CUR); C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10] ->
    rb_handle p p0 s P B0 mm ->
    rw_cells asegs mm (Fb + 32) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)] ->
    rw_cells asegs mm EB [CB 256 ej] -> rw_cells asegs mm CUR ccs -> cells_size ccs = 24%nat ->
    pc_rfile p = f -> (0 <= bt < 2^32)%Z -> (12 <= tl <= 2^30)%Z -> (tl mod 4 = 0)%Z -> (tl <= pc_bufalloc p0)%Z ->
    implMG RNGx (rb_bodyA HO FO sites f bt tl p0) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 Af) (Z_to_bv 64 P) (Z_to_bv 64 tl) (Z_to_bv 64 (P + 56))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bee4) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 t3 t4 t5 t6 c0 c1 c2 c3 c8 c9 c10 ccs p p0 s B0 ej bt tl : ltac2:(SecDiet.SzSec.tyM 'rb_rd2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_rd2__body : ltac2:(SecDiet.SzSec.bodyP 'rb_rd2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT.
 intros CTX INV FRA HDL HBH HEB HCUR Hccs RF BT TL TL4 TLA.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p0)%Z) by lia.
    rb_setup GL CTX INV AL0.
    (* [comment removed for export] *)
    set (V := (bt + 4294967296 * tl)%Z).
    assert (HBV : rw_cells asegs mm (Fb + 32) [C8 (Z_to_bv 64 V)]).
    { eapply rw_cells_recell; [exact HBH | cbn; repeat split; exact Logic.I |]. cbn [cells_bytes cbytes app]. rewrite !app_nil_r.
      subst V. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le8_two bt tl) by lia. rewrite map_app, <- !OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le4_le_bytes by lia. reflexivity. }
    clear HBH.
    assert (LBS : length bs' = Z.to_nat (pc_bufalloc p0)) by (destruct HBUF as [[WFb _] _]; cbn in WFb; tauto).
    apply (rw_cells_split_CB asegs mm _ [] (Z.to_nat (pc_bufalloc p0)) _ [] [8%nat; (Z.to_nat tl - 8)%nat; (Z.to_nat (pc_bufalloc p0) - Z.to_nat tl)%nat]) in HBUF; [| cbn; lia].
    cbn [mk_CB_cells app] in HBUF.
    lazymatch type of HBUF with rw_cells _ _ _ [CB _ ?l0; CB _ ?l1; CB _ ?l2] => set (jk := l0) in HBUF; set (jd := l1) in HBUF; set (jr := l2) in HBUF; clearbody jk jd jr end.
    destruct (rw_cells_cut _ _ _ 1 HBUF) as [HB8 HBT]. clear HBUF. cbn [firstn skipn cells_size csize Nat.add] in HB8, HBT.
    destruct (rw_cells_cut _ _ _ 1 HBT) as [HBD HBR]. clear HBT. cbn [firstn skipn cells_size csize Nat.add] in HBD, HBR.
    lazymatch type of HBD with rw_cells _ _ ?A _ => replace A with (B0 + 8)%Z in HBD, HBR by lia end.
    lazymatch type of HBR with rw_cells _ _ ?A _ => replace A with (B0 + tl)%Z in HBR by lia end.
    pose proof (munch_refl [(SPA, SPA + 88); (B0, B0 + pc_bufalloc p0)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    unfold rb_bodyA, read_bytes. cbn [mo_bind mo_ret MOps e_fread e_ferror e_fret prims pc_buffer set_bufdata].
    apply implMG_from_evtF.
    zstep. ck0 PUNP; ck_go.
    eapply evtF_cut; [ eapply rb_memcpy_seq with (B := B0) (alloc := pc_bufalloc p0) (bB := bB) (kPB := kPB) (kBF := kBF) (V := V) (P := P) (Fb := Fb); [try eassumption ..]; subst V; lia | post_call asegs mm ].
    lazymatch goal with HH : rw_cells asegs _ B0 [CB 8 _] |- _ => rename HH into HB8 end.
    do 3 zstep. zstep. do 2 zstep. zstep.
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] [(pc_buffer p0, B0, pc_bufalloc p0)] (bv_unsigned sp)) [(SPA, SPA + 88); (B0, B0 + pc_bufalloc p0)]%Z).
    { apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [| apply Forall_nil]. right; left. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ mx _ [] (bv_unsigned sp) FW (Forall_nil _) G MU WM ltac:(lia)) as [G3 AG3];
      assert (INV3 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p0) B0 (pc_bufalloc p0) mx)
    end.
    { cbn [app] in G3. unfold rb_inv, rb_shadow. split; [exact FP|]. split; [exact G3|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG3|]. intros a (K & N1 & N2 & N3). split; [exact K| exact I]. }
      split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
    cbn [app] in G3.
    pose proof (HAL _ _ _ _ _ _ _ (pc_buffer p0, B0, pc_bufalloc p0) G3 HinB') as EA. cbn [cb_tok cb_addr fst snd] in EA.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G3 HinB') as BBLK3.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. apply implMG_bind_assoc. eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest]. rewrite EA.
      eapply (FREAD _ spa) with (Af := Af);
        [ split; [exact G3|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | rewrite <- RF in HinF; rewrite <- RF; exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia
        | replace (Z.to_nat (tl - 8)) with (Z.to_nat tl - 8)%nat by lia; exact HBD
        | split; [left; exists (pc_buffer p0, B0, pc_bufalloc p0); split; [apply in_or_app; right; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]|];
          eapply blockA_aobj; [exact BBLK3| cbn [cb_addr cb_size fst snd]; lia| cbn [cb_addr cb_size fst snd]; lia| lia] ]. }
    intros got s6' RNG6 ms' PO. cbv beta in PO.
    destruct PO as (FP6 & av & m6 & junk6 & E & OF6 & MI6 & ST6 & AG6 & G6 & -> & GOTL & GOTR & HD6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 573312)) with (Z_to_bv 64 573312) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (INV6 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNG6 s6' (pc_buffer p0) B0 (pc_bufalloc p0) m6).
    { eapply (rb_inv_callee FO GIOA fflagA GL) with (Pn := fun a => ~ (B0 + 8 <= a < B0 + 8 + (tl - 8))%Z);
        [ exact INV3 | lia | lia | exact FP6 | exact G6 | exact OF6 | exact MI6 | exact ST6 | exact AG6
        | intros a Ha; lia | intros a Ha; lia | intros a Ha; lia
        | intros a KK NB NFr Hx; apply NB; unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia ]. }
    assert (KK : forall A cs, rw_cells asegs m0 A cs ->
              (forall a, (A <= a < A + Z.of_nat (cells_size cs))%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p0, B0, pc_bufalloc p0)]) SPA a) ->
              (A + Z.of_nat (cells_size cs) <= B0 + 8 \/ B0 + tl <= A)%Z -> rw_cells asegs m6 A cs).
    { intros A cs HC HK HD. eapply agrees_rw_cells; [exact AG6| exact HC|]. intros a Ha. split; [apply HK; exact Ha| lia]. }
    assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p0, B0, pc_bufalloc p0)]) SPA a).
    { intros a Ha. right; left. apply in_block_app. left. apply in_block_In. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
      cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (INB : forall a, (B0 <= a < B0 + pc_bufalloc p0)%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p0, B0, pc_bufalloc p0)]) SPA a).
    { intros a Ha. right; left. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    assert (INF : forall a, (Fb <= a < Fb + 64)%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p0, B0, pc_bufalloc p0)]) SPA a).
    { intros a Ha. right; right; left. apply in_frames_In. exists (FF_READ_BLOCK, Fb, 64%Z). split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]. }
    apply KK in FRA; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; left; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HCUR; [| intros a Ha; rewrite Hccs in Ha; left; lia | rewrite Hccs; lia].
    apply KK in HEB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; eapply clocA_keeps; [exact (proj1 OEB)| lia] | cbn [cells_size csize Nat.add]; lia].
    apply KK in HBS; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HPV; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HMB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HBV; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INF; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HB8; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INB; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HBR; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INB; lia | cbn [cells_size csize Nat.add]; lia].
    (* [comment removed for export] *)
    set (d2 := ((le_bytes 4 bt ++ le_bytes 4 tl) ++ got)%list).
    assert (LG : (length got <= Z.to_nat tl - 8)%nat) by (unfold zlength in GOTL; lia).
    assert (LD2 : Z.of_nat (length d2) = (8 + zlength got)%Z) by (subst d2; rewrite !length_app, !OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.length_le_bytes; unfold zlength; lia).
    assert (DR2 : Forall (fun z => 0 <= z < 256)%Z d2).
    { subst d2. apply Forall_app. split; [apply Forall_app; split; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le_bytes_4_range| exact GOTR]. }
    assert (HDL6 : rb_handle p (set_bufdata d2 p0) s P B0 m6).
    { pose proof (rw_cells_uncut _ _ _ _ _ HB8 HD6 ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
      pose proof (rw_cells_uncut _ _ _ _ _ J1 HBR ltac:(cbn [cells_size csize Nat.add]; lia)) as J2. cbn [app] in J2. clear J1.
      apply (rw_cells_merge asegs m6 B0 [] [_; _; _; _] []) in J2. cbn [app] in J2.
      replace (cells_size [CB 8 (le8 (Z_to_bv 64 V)); CB (length got) (map b8 got); CB (Z.to_nat (tl - 8) - length got) junk6; CB (Z.to_nat (pc_bufalloc p0) - Z.to_nat tl) jr])
        with (Z.to_nat (pc_bufalloc p0)) in J2 by (cbn [cells_size csize Nat.add]; lia).
      unfold rb_handle, blk_handle. cbn [pc_bufsize pc_swapped pc_bufalloc pc_bufdata pc_priv pc_rfile pc_self set_bufdata].
      split; [repeat (split; [assumption|]); assumption|]. split; [eexists; split; [exact J2|]|].
      - cbn [cells_bytes cbytes app]. rewrite app_nil_r. subst V. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le8_two bt tl) by lia. change PcapRep.b8 with b8.
        subst d2. rewrite app_assoc, <- (map_app b8).
        rewrite firstn_app. rewrite length_map, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
        apply firstn_all2. rewrite length_map. lia.
      - split; [lia|]. repeat (split; [assumption|]). exact E6. }
    assert (HBH6 : rw_cells asegs m6 (Fb + 32) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)]).
    { eapply rw_cells_recell; [exact HBV | cbn; repeat split; exact Logic.I |]. cbn [cells_bytes cbytes app]. rewrite !app_nil_r.
      subst V. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le8_two bt tl) by lia. rewrite map_app, <- !OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le4_le_bytes by lia. reflexivity. }
    destruct (Z.eq_dec (zlength got) (tl - 8)) as [LEQ|LNE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb]. apply implMG_retb. cbv iota beta.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU6. pose proof (wmono_refl asegs m6) as WM6.
      apply implMG_from_evtF. zstep. if_cases Kq; [zify_cond Kq; exfalso; lia|].
      apply evtF_done. subst POSTQ.
      eapply (rb_tail HO FO sites GIOA TP fflagA GL GPL FRET SNPRINTF) with (p := p) (p2 := set_bufdata d2 p0) (B' := B0) (ccs := ccs);
        [ exact CTX | exact INV6 | exact FRA | exact HDL6 | exact HBH6 | exact HEB | exact HCUR | exact Hccs | exact BT | exact TL | exact TL4
        | cbn [pc_bufdata set_bufdata]; lia | cbn [pc_bufdata set_bufdata]; exact DR2 ].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU6. pose proof (wmono_refl asegs m6) as WM6.
      apply implMG_from_evtF. zstep. if_cases Kq; [|zify_cond Kq; exfalso; lia].
      apply evtF_done. subst POSTQ.
      eapply (rb_short2 HO FO sites GIOA TP fflagA GL GPL FRET FERROR SNPRINTF FMT) with (p := p) (p' := set_bufdata d2 p0) (B' := B0) (ccs := ccs) (n := (tl - 8)%Z);
        [ exact CTX | exact INV6 | exact FRA | exact HDL6 | exact HEB | exact HCUR | exact Hccs | lia | exact GOTL | exact LNE | ].
      intros msg. reflexivity.
  Qed.
  End Sz1.
  Lemma rb_rd2 : ltac:(let t := eval cbv delta [rb_rd2__stmt] in rb_rd2__stmt in exact t).
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 t3 t4 t5 t6 c0 c1 c2 c3 c8 c9 c10 ccs p p0 s B0 ej bt tl. ltac2:(SecDiet.SzSec.closeP 'rb_rd2__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.

  (* [comment removed for export] *)
  Definition rb_inv_callee0__stmt : Prop := forall (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock)
      (lo P CUR EB SPA Fb : Z) (o : option hptr) (m : mem) (RNGx : footprint) (sx : PState H hptr) (bq : hptr) (B alloc : Z) (mm : mem)
      (RNGy : footprint) (sy : PState H hptr) (bq' : hptr) (B1 alloc' : Z) (my : mem),
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx bq B alloc mm ->
    (SPA <= bv_unsigned sp - 192)%Z ->
    fp_le RNGx RNGy -> GIOA L RNGy sy ((C1 ++ C2) ++ [(bq', B1, alloc')]) FB ((FF_READ_BLOCK, Fb, 64%Z) :: FL) my -> ps_outfile sy = ps_outfile sx ->
    mem_inv asegs my -> stk asegs my lo SPA ->
    agrees_on (client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) (C1 ++ C2) SPA) mm my ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGy sy bq' B1 alloc' my.
  Section Sz2.
  Variables ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx bq B alloc mm RNGy sy bq' B1 alloc' my : ltac2:(SecDiet.SzSec.tyM 'rb_inv_callee0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_inv_callee0__body : ltac2:(SecDiet.SzSec.bodyP 'rb_inv_callee0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type.
 intros INV HSP FPy Gy OFy MIy STy AGy.
    destruct INV as (FP & G & OF & MI & ST & STG & FR & AG & (k0 & k1 & k2 & pre & FRC1) & (post & FRC3) & SHC).
    unfold rb_inv. split; [eapply fp_le_trans; [exact FP| exact FPy]|]. split; [exact Gy|]. split; [congruence|]. split; [exact MIy|]. split; [exact STy|].
    assert (INFR : forall a, (Fb <= a < Fb + 64)%Z -> in_frames ((FF_READ_BLOCK, Fb, 64%Z) :: FL) a).
    { intros a Ha. apply in_frames_In. exists (FF_READ_BLOCK, Fb, 64%Z). split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]. }
    assert (INSH : forall a, (Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 8)%Z -> in_frame_sh ((FF_READ_BLOCK, Fb, 64%Z) :: FL) a).
    { intros a Ha. apply in_frame_sh_In. exists (FF_READ_BLOCK, Fb, 64%Z). split; [left; reflexivity|].
      cbn [fb_addr fb_size fst snd]. change (Z.shiftr 64 3) with 8%Z. exact Ha. }
    split. { eapply agrees_stk; [exact AGy| exact STG|]. intros a Ha. left; lia. }
    split. { eapply agrees_rw_cells; [exact AGy| exact FR|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. left; lia. }
    split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AGy|]. intros a (K & _).
             destruct K as [K|[K|[K|K]]]; [left; lia| right; left; exact K| right; right; left; apply in_frames_cons; exact K| right; right; right; apply in_frame_sh_cons; exact K]. }
    split. { exists k0, k1, k2, pre. eapply agrees_rw_cells; [exact AGy| exact FRC1|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. right; right; left; apply INFR; lia. }
    split. { exists post. eapply agrees_rw_cells; [exact AGy| exact FRC3|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. right; right; left; apply INFR; lia. }
    eapply agrees_rw_cells; [exact AGy| exact SHC|]. intros a Ha. unfold rb_shadow in Ha. cbn [cells_size csize Nat.add] in Ha. right; right; right; apply INSH; lia.
  Qed.
  End Sz2.
  Lemma rb_inv_callee0 : ltac:(let t := eval cbv delta [rb_inv_callee0__stmt] in rb_inv_callee0__stmt in exact t).
  Proof using Type. intros ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx bq B alloc mm RNGy sy bq' B1 alloc' my. ltac2:(SecDiet.SzSec.closeP 'rb_inv_callee0__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition rb_grow_post__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (c0 c1 c2 c8 c9 c10 bold : word) (ccs : list cell) (p : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (q' : hptr) (A' : Z) (ej bsn : list byte) (bt tl : Z),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx q' A' tl mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 (Z_to_bv 64 (P + 24)); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (s32 tl));
                           C8 (Z_to_bv 64 CUR); C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10] ->
    rw_cells asegs mm (P + 20) [C4 (Z_to_bv 64 (pc_bufsize p)); C8 bold] ->
    rw_cells asegs mm (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
    rw_cells asegs mm (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize s))] ->
    rw_cells asegs mm A' [CB (Z.to_nat tl) bsn] -> firstn (length (zfirstn tl (pc_bufdata p))) bsn = map b8 (zfirstn tl (pc_bufdata p)) ->
    rw_cells asegs mm (Fb + 32) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)] ->
    rw_cells asegs mm EB [CB 256 ej] -> rw_cells asegs mm CUR ccs -> cells_size ccs = 24%nat ->
    pc_rfile p = f -> (0 <= pc_bufsize p <= 2^30)%Z -> (pc_bufsize p < tl)%Z -> (0 <= ng_max_blocksize s <= 2^28)%Z ->
    (0 <= bt < 2^32)%Z -> (12 <= tl <= 2^30)%Z -> (tl mod 4 = 0)%Z ->
    implMG RNGx (rb_bodyA HO FO sites f bt tl (set_buffer q' (pc_bufsize p) tl (zfirstn tl (pc_bufdata p)) p)) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr (P + 24) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 Af) (Z_to_bv 64 P) (Z_to_bv 64 tl) (Z_to_bv 64 (P + 56))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bed0) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c0 c1 c2 c8 c9 c10 bold ccs p s q' A' ej bsn bt tl : ltac2:(SecDiet.SzSec.tyM 'rb_grow_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_grow_post__body : ltac2:(SecDiet.SzSec.bodyP 'rb_grow_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT.
 intros CTX INV FRA HBS HPV HMB HBUF PFX HBH HEB HCUR Hccs RF WBS TLB WMB BT TL TL4.
    assert (AL0 : (0 < tl)%Z) by lia.
    rb_setup GL CTX INV AL0.
    pose proof (munch_refl [(P + 24, P + 32)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    apply implMG_from_evtF.
    zstep. if_false_by (eqz_false A' ltac:(lia)).
    ck0_at PUNP (P + 24)%Z; ck_go.
    zstep. zstep.
    assert (FX : Forall (cobj_iv FL (C1 ++ C2)) [(P + 24, P + 32)]%Z).
    { apply Forall_cons; [| apply Forall_nil]. split; [| cbn [fst snd]; lia]. cbn [fst snd]. left. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
      cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ mx [] _ (bv_unsigned sp) (Forall_nil _) FX G MU WM ltac:(lia)) as [G3 AG3];
      assert (INV3 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx q' A' tl mx)
    end.
    { cbn [app] in G3. unfold rb_inv, rb_shadow. split; [exact FP|]. split; [exact G3|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG3|]. intros a (K & N1 & N2 & N3). split; [exact K|]. cbn [outside fst snd]. split; [lia| exact I]. }
      split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
    apply evtF_done. subst POSTQ.
    eapply (rb_rd2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx)
      with (p := p) (p0 := set_buffer q' (pc_bufsize p) tl (zfirstn tl (pc_bufdata p)) p) (B0 := A') (ccs := ccs);
      [ exact CTX | exact INV3 | eassumption | | eassumption | eassumption | eassumption | exact Hccs | exact RF | exact BT | exact TL | exact TL4 | cbn [pc_bufalloc set_buffer]; lia ].
    unfold rb_handle, blk_handle. cbn [pc_bufsize pc_swapped pc_bufalloc pc_bufdata pc_priv pc_rfile pc_self set_buffer].
    split; [repeat (split; [first [assumption | lia]|]); lia|]. split; [exists bsn; split; assumption|].
    split; [unfold zfirstn; rewrite length_firstn; lia|].
    repeat (split; [reflexivity|]). unfold same_meta. cbn [pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header set_buffer].
    repeat (split; [reflexivity|]). reflexivity.
  Qed.
  End Sz3.
  Lemma rb_grow_post : ltac:(let t := eval cbv delta [rb_grow_post__stmt] in rb_grow_post__stmt in exact t).
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c0 c1 c2 c8 c9 c10 bold ccs p s q' A' ej bsn bt tl. ltac2:(SecDiet.SzSec.closeP 'rb_grow_post__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition rb_grow__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a4 a5 a7 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c8 c9 c10 : word) (ccs : list cell) (p : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (i : option hptr) (B : Z) (ej : list byte) (bt tl : Z),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p) B (pc_bufalloc p) mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 (Z_to_bv 64 CUR); C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10] ->
    rb_handle p p s P B mm ->
    rw_cells asegs mm (Fb + 32) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)] ->
    rw_cells asegs mm EB [CB 256 ej] -> rw_cells asegs mm CUR ccs -> cells_size ccs = 24%nat ->
    pc_rfile p = f -> pc_priv p = PrivNg s i -> pc_self p = self ->
    (0 <= bt < 2^32)%Z -> (12 <= tl < 2^32)%Z -> (tl mod 4 = 0)%Z -> (ng_max_blocksize s < 2^29 - 2^16)%Z ->
    agrees_on (fun a => (bv_unsigned sp <= a)%Z) m mm ->
    implMG RNGx (mo_bind MOps
                   (if (pc_bufsize p <? tl)%Z then
                      if (ng_max_blocksize (ng_of p) <? tl)%Z
                      then mo_ret MOps (Some (Msg.block_size_gt_max tl (ng_max_blocksize (ng_of p))), p)
                      else mo_bind MOps (e_realloc (prims HO FO sites) (pc_buffer p) tl) (fun r =>
                           match r with
                           | None => mo_ret MOps (Some Msg.out_of_memory, p)
                           | Some b => mo_ret MOps (@None (list Z), set_buffer b (pc_bufsize p) tl (zfirstn tl (pc_bufdata p)) p)
                           end)
                    else mo_ret MOps (@None (list Z), p))
                   (fun x => let '(gerr, p0) := x in
                    match gerr with
                    | Some m0 => e_fret (prims HO FO sites) FF_READ_BLOCK (RB_Err m0 p0)
                    | None => rb_bodyA HO FO sites f bt tl p0
                    end)) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 (Z_to_bv 64 (s32 tl)) a4 a5 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 648)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 Af) (Z_to_bv 64 P) (Z_to_bv 64 tl) (Z_to_bv 64 (P + 56))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8be58) fc None mm (seg_rom asegs)).
  Section Sz4.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a4 a5 a7 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c8 c9 c10 ccs p s i B ej bt tl : ltac2:(SecDiet.SzSec.tyM 'rb_grow__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_grow__body : ltac2:(SecDiet.SzSec.bodyP 'rb_grow__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT REALLOC RPC.
 intros CTX INV FRA HDL HBH HEB HCUR Hccs RF PRV SELF BT TL TL4 MBX AGS.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p)%Z) by lia.
    rb_setup GL CTX INV AL0.
    unfold ng_of. rewrite PRV.
    pose proof (munch_refl [(SPA, SPA + 88); (P + 24, P + 32)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    cbn [mo_bind mo_ret MOps e_realloc e_fret prims].
    apply implMG_from_evtF.
    zstep. ck0 PUNP; ck_go.
    zstep. do 2 zstep.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.unsigned_s32 tl ltac:(lia)) as UST.
    replace (sx32 (Z_to_bv 64 (pc_bufsize p))) with (Z_to_bv 64 (pc_bufsize p)) by (rewrite sx32_s32 by lia; rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.s32_small by lia; reflexivity).
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      rewrite unsigned_lit_wrap in UST.
      assert (TLB : (tl <= pc_bufsize p)%Z) by (Z.div_mod_to_equations; lia).
      replace (pc_bufsize p <? tl)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      assert (FW : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] [(pc_buffer p, B, pc_bufalloc p)] (bv_unsigned sp)) [(SPA, SPA + 88)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
      assert (FX : Forall (cobj_iv FL (C1 ++ C2)) [(P + 24, P + 32)]%Z).
      { apply Forall_cons; [| apply Forall_nil]. split; [| cbn [fst snd]; lia]. cbn [fst snd]. left. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
        cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ mx _ _ (bv_unsigned sp) FW FX G MU WM ltac:(lia)) as [G3 AG3];
        assert (INV3 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p) B (pc_bufalloc p) mx);
        [| assert (HDL3 : rb_handle p p s P B mx) ]
      end.
      { cbn [app] in G3. unfold rb_inv, rb_shadow. split; [exact FP|]. split; [exact G3|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
        split; [assumption|].
        split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG3|]. intros a (K & N1 & N2 & N3). split; [exact K|]. cbn [outside fst snd]. split; [lia| exact I]. }
        split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
      { unfold rb_handle, blk_handle. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
        repeat (split; [assumption|]). assumption. }
      apply evtF_done. apply implMG_retb. cbv iota beta. subst POSTQ.
      eapply (rb_rd2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx) with (p := p) (p0 := p) (B0 := B) (ccs := ccs);
        [ exact CTX | exact INV3 | eassumption | exact HDL3 | eassumption | eassumption | eassumption | exact Hccs | exact RF | exact BT | lia | exact TL4 | lia ].
    - (* [comment removed for export] *)
      rewrite unsigned_lit_wrap in UST.
      assert (TLB : (pc_bufsize p < tl)%Z) by (Z.div_mod_to_equations; lia).
      replace (pc_bufsize p <? tl)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      zstep. ck0 PUNP; ck_go.
      zstep.
      replace (sx32 (Z_to_bv 64 (ng_max_blocksize s))) with (Z_to_bv 64 (ng_max_blocksize s)) by (rewrite sx32_s32 by lia; rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.s32_small by lia; reflexivity).
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        assert (TLM : (tl <= ng_max_blocksize s)%Z) by (Z.div_mod_to_equations; lia).
        replace (ng_max_blocksize s <? tl)%Z with false by (symmetry; apply Z.ltb_ge; lia).
        zstep. ck0 PUNP; ck_go.
        do 3 zstep. zstep.
        assert (FW : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] [(pc_buffer p, B, pc_bufalloc p)] (bv_unsigned sp)) [(SPA, SPA + 88)]%Z)
          by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
        assert (FX : Forall (cobj_iv FL (C1 ++ C2)) [(P + 24, P + 32)]%Z).
        { apply Forall_cons; [| apply Forall_nil]. split; [| cbn [fst snd]; lia]. cbn [fst snd]. left. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
          cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
          destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ mx _ _ (bv_unsigned sp) FW FX G MU WM ltac:(lia)) as [G3 AG3];
          assert (INV3 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p) B (pc_bufalloc p) mx);
          [| assert (UC5 : ucallerA depth_read_block L mx sp s0 ra trC) ]
        end.
        { cbn [app] in G3. unfold rb_inv, rb_shadow. split; [exact FP|]. split; [exact G3|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
          split; [assumption|].
          split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG3|]. intros a (K & N1 & N2 & N3). split; [exact K|]. cbn [outside fst snd]. split; [lia| exact I]. }
          split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
        { eapply ucaller_keep; [exact UC| lia|]. intros a Ha.
          destruct (AGS a ltac:(lia) ltac:(lia)) as [EQa _]. rewrite <- EQa. apply MU. rewrite wa_unsigned by lia. cbn [outside fst snd]. split; [lia|]. split; [lia| exact I]. }
        cbn [app] in G3.
        pose proof (rw_cells_nth_C8 _ _ _ 11%nat _ FR eq_refl) as BS0. pose proof (rw_cells_nth_C8 _ _ _ 12%nat _ FR eq_refl) as BRA.
        cbn [firstn cells_size csize Nat.add] in BS0, BRA.
        replace (bv_unsigned sp + -104 + Z.of_nat 88)%Z with (bv_unsigned sp - 16)%Z in BS0 by lia.
        replace (bv_unsigned sp + -104 + Z.of_nat 96)%Z with (bv_unsigned sp - 8)%Z in BRA by lia.
        assert (TRX : In (tp_rpc TP :: 0x8bed0%Z :: bv_unsigned ra :: trC) (al_U L)) by (exact (proj2 TR)).
        remember (Z_to_bv 64 SPA) as spa eqn:Espa.
        assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
        apply evtF_done. apply implMG_bind_assoc. eapply implMG_bind.
        { eapply (REALLOC _ spa) with (L := L) (s := sx) (C1 := C1 ++ C2) (C2 := []) (FB := FB) (FL := (FF_READ_BLOCK, Fb, 64%Z) :: FL)
                                     (lo := lo) (q := pc_buffer p) (A := B) (sz := pc_bufalloc p) (n := tl) (bs := bs');
            [ split; [exact G3|]; rewrite Hspa; split; [assumption|]; split; [lia|]; split; [unfold REALLOC_STACK; lia|]; split; [lia|];
              split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
              split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
            | reflexivity | reflexivity | lia | eassumption
            | eapply (unw_of_ucaller (pred depth_read_block));
                [ eapply (ucaller_frame _ _ _ _ _ _ _ _ _ _ 0x8bed0%Z UC5); [rewrite Hspa; lia| lia| Z.div_mod_to_equations; lia| exact BS0| exact BRA
                    | reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_read_block; cbn; lia]
                | exact RPC
                | rewrite Hspa; lia
                | rewrite unsigned_lit by lia; exact TRX
                | exact RSTK ] ]. }
        intros r s6' RNG6 ms' PO. cbv beta in PO. destruct PO as (FP6 & av & m6 & E & OF6 & MI6 & ST6 & AG6 & PO).
        destruct r as [q'|]; [|destruct PO]. destruct PO as (A' & junk6 & -> & G6 & NEW).
        unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
        replace (ret_pc (Z_to_bv 64 573136)) with (Z_to_bv 64 573136) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        rewrite app_nil_r in AG6, G6.
        assert (G6' : GIOA L RNG6 s6' ((C1 ++ C2) ++ [(q', A', tl)]) FB ((FF_READ_BLOCK, Fb, 64%Z) :: FL) m6)
          by (eapply GPL; [exact G6|]; apply Permutation.Permutation_cons_append).
        assert (INV6 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNG6 s6' q' A' tl m6)
          by (eapply rb_inv_callee0; [exact INV3| lia| exact FP6| exact G6'| exact OF6| exact MI6| exact ST6| exact AG6]).
        assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) (C1 ++ C2) SPA a).
        { intros a Ha. right; left. apply in_block_In. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
        assert (INF : forall a, (Fb <= a < Fb + 64)%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) (C1 ++ C2) SPA a).
        { intros a Ha. right; right; left. apply in_frames_In. exists (FF_READ_BLOCK, Fb, 64%Z). split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]. }
        apply (agrees_rw_cells _ _ _ _ _ AG6) in FRA; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; left; lia].
        apply (agrees_rw_cells _ _ _ _ _ AG6) in HCUR; [| intros a Ha; rewrite Hccs in Ha; left; lia].
        apply (agrees_rw_cells _ _ _ _ _ AG6) in HEB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ EBLOC (incl_refl _) IFL)| lia]].
        apply (agrees_rw_cells _ _ _ _ _ AG6) in HBS; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
        apply (agrees_rw_cells _ _ _ _ _ AG6) in HPV; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
        apply (agrees_rw_cells _ _ _ _ _ AG6) in HMB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
        apply (agrees_rw_cells _ _ _ _ _ AG6) in HBH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INF; lia].
        assert (LBS : length bs' = Z.to_nat (pc_bufalloc p)) by (destruct HBUF as [[WFb _] _]; cbn in WFb; tauto).
        apply (rw_cells_merge asegs m6 A' [] [_; _] []) in NEW. cbn [app] in NEW.
        replace (cells_size [CB (Z.to_nat (Z.min (pc_bufalloc p) tl)) (firstn (Z.to_nat (Z.min (pc_bufalloc p) tl)) bs'); CB (Z.to_nat (tl - Z.min (pc_bufalloc p) tl)) junk6])
          with (Z.to_nat tl) in NEW by (cbn [cells_size csize Nat.add]; lia).
        cbn [cells_bytes cbytes app] in NEW. rewrite app_nil_r in NEW.
        pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.realloc_prefix (pc_bufdata p) bs' junk6 (pc_bufalloc p) tl PFX LENB LBS ltac:(lia)) as PFX6. change PcapRep.b8 with b8 in PFX6.
        cbv iota beta. apply implMG_retb. cbv iota beta. subst POSTQ.
        eapply (rb_grow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNG6 s6' m6)
          with (p := p) (s := s) (q' := q') (A' := A') (ccs := ccs);
          [ exact CTX | exact INV6 | eassumption | eassumption | eassumption | eassumption | exact NEW | exact PFX6 | eassumption | eassumption | eassumption | exact Hccs
          | exact RF | lia | lia | lia | exact BT | lia | exact TL4 ].
      + (* [comment removed for export] *)
        assert (TLM : (ng_max_blocksize s < tl)%Z) by (Z.div_mod_to_equations; lia).
        replace (ng_max_blocksize s <? tl)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        assert (FW : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] [(pc_buffer p, B, pc_bufalloc p)] (bv_unsigned sp)) [(SPA, SPA + 88)]%Z)
          by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
        assert (FX : Forall (cobj_iv FL (C1 ++ C2)) [(P + 24, P + 32)]%Z).
        { apply Forall_cons; [| apply Forall_nil]. split; [| cbn [fst snd]; lia]. cbn [fst snd]. left. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
          cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
        do 3 zstep. do 2 zstep. do 2 zstep. zstep.
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
          destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ mx _ _ (bv_unsigned sp) FW FX G MU WM ltac:(lia)) as [G3 AG3];
          assert (INV3 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p) B (pc_bufalloc p) mx);
          [| assert (HDL3 : rb_handle p p s P B mx); [| assert (MSG : fmt_at mx 0x22460 "pcapng block size %u > maximum %u"%string) by (fmt_at_solve MI 0x22460%Z "pcapng block size %u > maximum %u"%string) ] ]
        end.
        { cbn [app] in G3. unfold rb_inv, rb_shadow. split; [exact FP|]. split; [exact G3|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
          split; [assumption|].
          split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG3|]. intros a (K & N1 & N2 & N3). split; [exact K|]. cbn [outside fst snd]. split; [lia| exact I]. }
          split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
        { unfold rb_handle, blk_handle. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
          repeat (split; [assumption|]). assumption. }
        apply evtF_done. apply implMG_retb. cbv iota beta. subst POSTQ.
        replace (Msg.block_size_gt_max tl (ng_max_blocksize s)) with (Fmt.snprintf 256 "pcapng block size %u > maximum %u"%string [AInt (s32 tl); AInt (ng_max_blocksize s)])
          by (unfold Msg.block_size_gt_max, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
              replace (convs (fmt "pcapng block size %u > maximum %u")) with [Cu; Cu] by (vm_compute; reflexivity);
              apply pargs_cons; [apply aeq_s32; reflexivity|]; apply pargs_cons; [apply aeq_same| apply pargs_nil]).
        eapply (rb_snp FO GIOA TP fflagA GL GPL FRET SNPRINTF) with (pc := 0x8bdac%Z) (p := p) (p' := p) (B' := B) (ccs' := ccs) (ej' := ej) (args := [AInt (s32 tl); AInt (ng_max_blocksize s)]);
          [ left; reflexivity | exact CTX | exact INV3 | eassumption | reflexivity | exact HDL3 | eassumption | eassumption | exact Hccs
          | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
          | apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2] ].
  Qed.
  End Sz4.
  Lemma rb_grow : ltac:(let t := eval cbv delta [rb_grow__stmt] in rb_grow__stmt in exact t).
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT REALLOC RPC. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a4 a5 a7 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c8 c9 c10 ccs p s i B ej bt tl. ltac2:(SecDiet.SzSec.closeP 'rb_grow__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition rb_len__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 r24 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c8 c9 c10 : word) (ccs : list cell) (p : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (i : option hptr) (B : Z) (ej : list byte) (bt tl : Z),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p) B (pc_bufalloc p) mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 (Z_to_bv 64 CUR); C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10] ->
    rb_handle p p s P B mm ->
    rw_cells asegs mm (Fb + 32) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)] ->
    rw_cells asegs mm EB [CB 256 ej] -> rw_cells asegs mm CUR ccs -> cells_size ccs = 24%nat ->
    pc_rfile p = f -> pc_priv p = PrivNg s i -> pc_self p = self ->
    (0 <= bt < 2^32)%Z -> (0 <= tl < 2^32)%Z -> (ng_max_blocksize s < 2^29 - 2^16)%Z ->
    agrees_on (fun a => (bv_unsigned sp <= a)%Z) m mm ->
    implMG RNGx (rb_tailA HO FO sites f bt tl p) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 648)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 Af) (Z_to_bv 64 P) r24 (Z_to_bv 64 (P + 56))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bd04) fc None mm (seg_rom asegs)).
  Section Sz5.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 r24 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c8 c9 c10 ccs p s i B ej bt tl : ltac2:(SecDiet.SzSec.tyM 'rb_len__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_len__body : ltac2:(SecDiet.SzSec.bodyP 'rb_len__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT REALLOC RPC.
 intros CTX INV FRA HDL HBH HEB HCUR Hccs RF PRV SELF BT TL MBX AGS.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p)%Z) by lia.
    rb_setup GL CTX INV AL0.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    unfold rb_tailA. cbn [e_fret prims].
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.unsigned_s32 tl ltac:(lia)) as UST. rewrite unsigned_lit_wrap in UST. change (2 ^ 64)%Z with 18446744073709551616%Z in UST.
    apply implMG_from_evtF.
    zstep. rewrite (zx32_lit tl) by lia.
    do 2 zstep. rewrite ?unsigned_lit by lia. rewrite ?Z.add_0_r, ?swrap32_s32.
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      replace (tl <? 12)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      zstep. zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        assert (TL4 : (tl mod 4 = 0)%Z).
        { rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.land3_low _ tl (tl / 2^31 * (2^32 - 1))) in K2; [exact K2| lia| lia| Z.div_mod_to_equations; lia]. }
        replace (negb (tl mod 4 =? 0))%Z with false by (rewrite TL4; reflexivity).
        apply evtF_done. subst POSTQ.
        eapply (rb_grow ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm) with (p := p) (s := s) (i := i) (B := B) (ccs := ccs);
          [ exact CTX | exact INV | exact FRA | exact HDL | exact HBH | exact HEB | exact HCUR | exact Hccs | exact RF | exact PRV | exact SELF | exact BT | lia | exact TL4 | exact MBX | exact AGS ].
      + (* [comment removed for export] *)
        assert (TL4 : (tl mod 4 <> 0)%Z).
        { intros X. apply K2. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.land3_low _ tl (tl / 2^31 * (2^32 - 1))); [exact X| lia| lia| Z.div_mod_to_equations; lia]. }
        replace (negb (tl mod 4 =? 0))%Z with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact TL4).
        assert (MSG : fmt_at mm 0x223e0 "block in pcapng dump file has a length of %u that is not a multiple of 4"%string)
          by (fmt_at_solve MI 0x223e0%Z "block in pcapng dump file has a length of %u that is not a multiple of 4"%string).
        do 2 zstep. do 2 zstep. zstep.
        apply evtF_done. subst POSTQ.
        replace (Msg.block_length_not_mult4 tl) with (Fmt.snprintf 256 "block in pcapng dump file has a length of %u that is not a multiple of 4"%string [AInt (s32 tl)])
          by (unfold Msg.block_length_not_mult4, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
              replace (convs (fmt "block in pcapng dump file has a length of %u that is not a multiple of 4")) with [Cu] by (vm_compute; reflexivity);
              apply pargs_cons; [apply aeq_s32; reflexivity| apply pargs_nil]).
        eapply (rb_snp FO GIOA TP fflagA GL GPL FRET SNPRINTF) with (pc := 0x8bd88%Z) (p := p) (p' := p) (B' := B) (ccs' := ccs) (ej' := ej) (args := [AInt (s32 tl)]);
          [ right; left; reflexivity | exact CTX | exact INV | exact FRA | reflexivity | exact HDL | exact HEB | exact HCUR | exact Hccs
          | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor]
          | apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints1] ].
    - (* [comment removed for export] *)
      replace (tl <? 12)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      assert (MSG : fmt_at mm 0x22380 "block in pcapng dump file has a length of %u < %zu"%string)
        by (fmt_at_solve MI 0x22380%Z "block in pcapng dump file has a length of %u < %zu"%string).
      do 4 zstep. do 2 zstep. zstep.
      apply evtF_done. subst POSTQ.
      replace (Msg.block_length_lt tl) with (Fmt.snprintf 256 "block in pcapng dump file has a length of %u < %zu"%string [AInt (s32 tl); AInt 12])
        by (unfold Msg.block_length_lt, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
            lazymatch goal with |- pargs ?c _ _ => let c' := eval vm_compute in c in change c with c' end;
            apply pargs_cons; [apply aeq_s32; reflexivity|]; apply pargs_cons; [apply aeq_same| apply pargs_nil]).
      eapply (rb_snp FO GIOA TP fflagA GL GPL FRET SNPRINTF) with (pc := 0x8bdac%Z) (p := p) (p' := p) (B' := B) (ccs' := ccs) (ej' := ej) (args := [AInt (s32 tl); AInt 12]);
        [ left; reflexivity | exact CTX | exact INV | exact FRA | reflexivity | exact HDL | exact HEB | exact HCUR | exact Hccs
        | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
        | apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2] ].
  Qed.
  End Sz5.
  Lemma rb_len : ltac:(let t := eval cbv delta [rb_len__stmt] in rb_len__stmt in exact t).
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT REALLOC RPC. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 r24 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c8 c9 c10 ccs p s i B ej bt tl. ltac2:(SecDiet.SzSec.closeP 'rb_len__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbBody.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_sfchk_fsegA__B3P.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_sfchk_fsegA__B3P.SfAuxB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngblk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_ngblk_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_ngblk_shortA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngblk_segA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_ngblk_tailA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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




(* [comment removed for export] *)
Tactic Notation "callp" uconstr(SPEC) :=
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ ?m _) => eapply evtF_cut; [ eapply SPEC; [ try eassumption .. ]; lia | post_call segs m ]
  end.


(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (s32 _) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- inr64 (s32 _) => fail   (* [comment removed for export] *)
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
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section RbBody.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.

  (* [comment removed for export] *)
  Definition rb_rd2__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c8 c9 c10 : word) (ccs : list cell) (p p0 : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (B0 : Z) (ej : list byte) (bt tl : Z),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p0) B0 (pc_bufalloc p0) mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (s32 tl));
                           C8 (Z_to_bv 64 CUR); C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10] ->
    rb_handle p p0 s P B0 mm ->
    rw_cells asegs mm (Fb + 32) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)] ->
    rw_cells asegs mm EB [CB 256 ej] -> rw_cells asegs mm CUR ccs -> cells_size ccs = 24%nat ->
    pc_rfile p = f -> (0 <= bt < 2^32)%Z -> (12 <= tl <= 2^30)%Z -> (tl mod 4 = 0)%Z -> (tl <= pc_bufalloc p0)%Z ->
    implMG RNGx (rb_bodyA HO FO sites f bt tl p0) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 Af) (Z_to_bv 64 tl) (Z_to_bv 64 P) (Z_to_bv 64 (P + 56))
               r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8beb0) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 t3 t4 t5 t6 c0 c1 c2 c3 c8 c9 c10 ccs p p0 s B0 ej bt tl : ltac2:(SecDiet.SzSec.tyM 'rb_rd2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_rd2__body : ltac2:(SecDiet.SzSec.bodyP 'rb_rd2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT.
 intros CTX INV FRA HDL HBH HEB HCUR Hccs RF BT TL TL4 TLA.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p0)%Z) by lia.
    rb_setup GL CTX INV AL0.
    (* [comment removed for export] *)
    set (V := (bt + 4294967296 * tl)%Z).
    assert (HBV : rw_cells asegs mm (Fb + 32) [C8 (Z_to_bv 64 V)]).
    { eapply rw_cells_recell; [exact HBH | cbn; repeat split; exact Logic.I |]. cbn [cells_bytes cbytes app]. rewrite !app_nil_r.
      subst V. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le8_two bt tl) by lia. rewrite map_app, <- !OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le4_le_bytes by lia. reflexivity. }
    clear HBH.
    assert (LBS : length bs' = Z.to_nat (pc_bufalloc p0)) by (destruct HBUF as [[WFb _] _]; cbn in WFb; tauto).
    apply (rw_cells_split_CB asegs mm _ [] (Z.to_nat (pc_bufalloc p0)) _ [] [8%nat; (Z.to_nat tl - 8)%nat; (Z.to_nat (pc_bufalloc p0) - Z.to_nat tl)%nat]) in HBUF; [| cbn; lia].
    cbn [mk_CB_cells app] in HBUF.
    lazymatch type of HBUF with rw_cells _ _ _ [CB _ ?l0; CB _ ?l1; CB _ ?l2] => set (jk := l0) in HBUF; set (jd := l1) in HBUF; set (jr := l2) in HBUF; clearbody jk jd jr end.
    destruct (rw_cells_cut _ _ _ 1 HBUF) as [HB8 HBT]. clear HBUF. cbn [firstn skipn cells_size csize Nat.add] in HB8, HBT.
    destruct (rw_cells_cut _ _ _ 1 HBT) as [HBD HBR]. clear HBT. cbn [firstn skipn cells_size csize Nat.add] in HBD, HBR.
    lazymatch type of HBD with rw_cells _ _ ?A _ => replace A with (B0 + 8)%Z in HBD, HBR by lia end.
    lazymatch type of HBR with rw_cells _ _ ?A _ => replace A with (B0 + tl)%Z in HBR by lia end.
    pose proof (munch_refl [(SPA, SPA + 88); (B0, B0 + pc_bufalloc p0)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    unfold rb_bodyA, read_bytes. cbn [mo_bind mo_ret MOps e_fread e_ferror e_fret prims pc_buffer set_bufdata].
    apply implMG_from_evtF.
    zstep. ck0 PUNP; ck_go.
    eapply evtF_cut; [ eapply rb_memcpy_seq with (B := B0) (alloc := pc_bufalloc p0) (bB := bB) (kPB := kPB) (kBF := kBF) (V := V) (P := P) (Fb := Fb); [try eassumption ..]; subst V; lia | post_call asegs mm ].
    lazymatch goal with HH : rw_cells asegs _ B0 [CB 8 _] |- _ => rename HH into HB8 end.
    zstep. zstep. zstep.   (* [comment removed for export] *)
    zstep. if_cases KG; [zify_cond KG; exfalso; lia|]. clear KG.   (* [comment removed for export] *)
    do 5 zstep. zstep.
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] [(pc_buffer p0, B0, pc_bufalloc p0)] (bv_unsigned sp)) [(SPA, SPA + 88); (B0, B0 + pc_bufalloc p0)]%Z).
    { apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [| apply Forall_nil]. right; left. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ mx _ [] (bv_unsigned sp) FW (Forall_nil _) G MU WM ltac:(lia)) as [G3 AG3];
      assert (INV3 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p0) B0 (pc_bufalloc p0) mx)
    end.
    { cbn [app] in G3. unfold rb_inv, rb_shadow. split; [exact FP|]. split; [exact G3|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG3|]. intros a (K & N1 & N2 & N3). split; [exact K| exact I]. }
      split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
    cbn [app] in G3.
    pose proof (HAL _ _ _ _ _ _ _ (pc_buffer p0, B0, pc_bufalloc p0) G3 HinB') as EA. cbn [cb_tok cb_addr fst snd] in EA.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G3 HinB') as BBLK3.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. apply implMG_bind_assoc. eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest]. rewrite EA.
      eapply (FREAD _ spa) with (Af := Af);
        [ split; [exact G3|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | rewrite <- RF in HinF; rewrite <- RF; exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia
        | replace (Z.to_nat (tl - 8)) with (Z.to_nat tl - 8)%nat by lia; exact HBD
        | split; [left; exists (pc_buffer p0, B0, pc_bufalloc p0); split; [apply in_or_app; right; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]|];
          eapply blockA_aobj; [exact BBLK3| cbn [cb_addr cb_size fst snd]; lia| cbn [cb_addr cb_size fst snd]; lia| lia] ]. }
    intros got s6' RNG6 ms' PO. cbv beta in PO.
    destruct PO as (FP6 & av & m6 & junk6 & E & OF6 & MI6 & ST6 & AG6 & G6 & -> & GOTL & GOTR & HD6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 573272)) with (Z_to_bv 64 573272) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (INV6 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNG6 s6' (pc_buffer p0) B0 (pc_bufalloc p0) m6).
    { eapply (rb_inv_callee FO GIOA fflagA GL) with (Pn := fun a => ~ (B0 + 8 <= a < B0 + 8 + (tl - 8))%Z);
        [ exact INV3 | lia | lia | exact FP6 | exact G6 | exact OF6 | exact MI6 | exact ST6 | exact AG6
        | intros a Ha; lia | intros a Ha; lia | intros a Ha; lia
        | intros a KK NB NFr Hx; apply NB; unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia ]. }
    assert (KK : forall A cs, rw_cells asegs m0 A cs ->
              (forall a, (A <= a < A + Z.of_nat (cells_size cs))%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p0, B0, pc_bufalloc p0)]) SPA a) ->
              (A + Z.of_nat (cells_size cs) <= B0 + 8 \/ B0 + tl <= A)%Z -> rw_cells asegs m6 A cs).
    { intros A cs HC HK HD. eapply agrees_rw_cells; [exact AG6| exact HC|]. intros a Ha. split; [apply HK; exact Ha| lia]. }
    assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p0, B0, pc_bufalloc p0)]) SPA a).
    { intros a Ha. right; left. apply in_block_app. left. apply in_block_In. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
      cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (INB : forall a, (B0 <= a < B0 + pc_bufalloc p0)%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p0, B0, pc_bufalloc p0)]) SPA a).
    { intros a Ha. right; left. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    assert (INF : forall a, (Fb <= a < Fb + 64)%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p0, B0, pc_bufalloc p0)]) SPA a).
    { intros a Ha. right; right; left. apply in_frames_In. exists (FF_READ_BLOCK, Fb, 64%Z). split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]. }
    apply KK in FRA; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; left; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HCUR; [| intros a Ha; rewrite Hccs in Ha; left; lia | rewrite Hccs; lia].
    apply KK in HEB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; eapply clocA_keeps; [exact (proj1 OEB)| lia] | cbn [cells_size csize Nat.add]; lia].
    apply KK in HBS; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HPV; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HMB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HBV; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INF; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HB8; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INB; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HBR; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INB; lia | cbn [cells_size csize Nat.add]; lia].
    (* [comment removed for export] *)
    set (d2 := ((le_bytes 4 bt ++ le_bytes 4 tl) ++ got)%list).
    assert (LG : (length got <= Z.to_nat tl - 8)%nat) by (unfold zlength in GOTL; lia).
    assert (LD2 : Z.of_nat (length d2) = (8 + zlength got)%Z) by (subst d2; rewrite !length_app, !OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.length_le_bytes; unfold zlength; lia).
    assert (DR2 : Forall (fun z => 0 <= z < 256)%Z d2).
    { subst d2. apply Forall_app. split; [apply Forall_app; split; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le_bytes_4_range| exact GOTR]. }
    assert (HDL6 : rb_handle p (set_bufdata d2 p0) s P B0 m6).
    { pose proof (rw_cells_uncut _ _ _ _ _ HB8 HD6 ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
      pose proof (rw_cells_uncut _ _ _ _ _ J1 HBR ltac:(cbn [cells_size csize Nat.add]; lia)) as J2. cbn [app] in J2. clear J1.
      apply (rw_cells_merge asegs m6 B0 [] [_; _; _; _] []) in J2. cbn [app] in J2.
      replace (cells_size [CB 8 (le8 (Z_to_bv 64 V)); CB (length got) (map b8 got); CB (Z.to_nat (tl - 8) - length got) junk6; CB (Z.to_nat (pc_bufalloc p0) - Z.to_nat tl) jr])
        with (Z.to_nat (pc_bufalloc p0)) in J2 by (cbn [cells_size csize Nat.add]; lia).
      unfold rb_handle, blk_handle. cbn [pc_bufsize pc_swapped pc_bufalloc pc_bufdata pc_priv pc_rfile pc_self set_bufdata].
      split; [repeat (split; [assumption|]); assumption|]. split; [eexists; split; [exact J2|]|].
      - cbn [cells_bytes cbytes app]. rewrite app_nil_r. subst V. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le8_two bt tl) by lia. change PcapRep.b8 with b8.
        subst d2. rewrite app_assoc, <- (map_app b8).
        rewrite firstn_app. rewrite length_map, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
        apply firstn_all2. rewrite length_map. lia.
      - split; [lia|]. repeat (split; [assumption|]). exact E6. }
    assert (HBH6 : rw_cells asegs m6 (Fb + 32) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)]).
    { eapply rw_cells_recell; [exact HBV | cbn; repeat split; exact Logic.I |]. cbn [cells_bytes cbytes app]. rewrite !app_nil_r.
      subst V. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le8_two bt tl) by lia. rewrite map_app, <- !OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le4_le_bytes by lia. reflexivity. }
    destruct (Z.eq_dec (zlength got) (tl - 8)) as [LEQ|LNE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb]. apply implMG_retb. cbv iota beta.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU6. pose proof (wmono_refl asegs m6) as WM6.
      apply implMG_from_evtF. zstep. if_cases Kq; [zify_cond Kq; exfalso; lia|].
      apply evtF_done. subst POSTQ.
      eapply (rb_tail HO FO sites GIOA TP fflagA GL GPL FRET SNPRINTF) with (p := p) (p2 := set_bufdata d2 p0) (B' := B0) (ccs := ccs);
        [ exact CTX | exact INV6 | exact FRA | exact HDL6 | exact HBH6 | exact HEB | exact HCUR | exact Hccs | exact BT | exact TL | exact TL4
        | cbn [pc_bufdata set_bufdata]; lia | cbn [pc_bufdata set_bufdata]; exact DR2 ].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU6. pose proof (wmono_refl asegs m6) as WM6.
      apply implMG_from_evtF. zstep. if_cases Kq; [|zify_cond Kq; exfalso; lia].
      apply evtF_done. subst POSTQ.
      eapply (rb_short2 HO FO sites GIOA TP fflagA GL GPL FRET FERROR SNPRINTF FMT) with (p := p) (p' := set_bufdata d2 p0) (B' := B0) (ccs := ccs) (n := (tl - 8)%Z);
        [ exact CTX | exact INV6 | exact FRA | exact HDL6 | exact HEB | exact HCUR | exact Hccs | lia | exact GOTL | exact LNE | ].
      intros msg. reflexivity.
  Qed.
  End Sz1.
  Lemma rb_rd2 : ltac:(let t := eval cbv delta [rb_rd2__stmt] in rb_rd2__stmt in exact t).
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 t3 t4 t5 t6 c0 c1 c2 c3 c8 c9 c10 ccs p p0 s B0 ej bt tl. ltac2:(SecDiet.SzSec.closeP 'rb_rd2__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.

  (* [comment removed for export] *)
  Definition rb_inv_callee0__stmt : Prop := forall (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock)
      (lo P CUR EB SPA Fb : Z) (o : option hptr) (m : mem) (RNGx : footprint) (sx : PState H hptr) (bq : hptr) (B alloc : Z) (mm : mem)
      (RNGy : footprint) (sy : PState H hptr) (bq' : hptr) (B1 alloc' : Z) (my : mem),
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx bq B alloc mm ->
    (SPA <= bv_unsigned sp - 192)%Z ->
    fp_le RNGx RNGy -> GIOA L RNGy sy ((C1 ++ C2) ++ [(bq', B1, alloc')]) FB ((FF_READ_BLOCK, Fb, 64%Z) :: FL) my -> ps_outfile sy = ps_outfile sx ->
    mem_inv asegs my -> stk asegs my lo SPA ->
    agrees_on (client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) (C1 ++ C2) SPA) mm my ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGy sy bq' B1 alloc' my.
  Section Sz2.
  Variables ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx bq B alloc mm RNGy sy bq' B1 alloc' my : ltac2:(SecDiet.SzSec.tyM 'rb_inv_callee0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_inv_callee0__body : ltac2:(SecDiet.SzSec.bodyP 'rb_inv_callee0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type.
 intros INV HSP FPy Gy OFy MIy STy AGy.
    destruct INV as (FP & G & OF & MI & ST & STG & FR & AG & (k0 & k1 & k2 & pre & FRC1) & (post & FRC3) & SHC).
    unfold rb_inv. split; [eapply fp_le_trans; [exact FP| exact FPy]|]. split; [exact Gy|]. split; [congruence|]. split; [exact MIy|]. split; [exact STy|].
    assert (INFR : forall a, (Fb <= a < Fb + 64)%Z -> in_frames ((FF_READ_BLOCK, Fb, 64%Z) :: FL) a).
    { intros a Ha. apply in_frames_In. exists (FF_READ_BLOCK, Fb, 64%Z). split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]. }
    assert (INSH : forall a, (Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 8)%Z -> in_frame_sh ((FF_READ_BLOCK, Fb, 64%Z) :: FL) a).
    { intros a Ha. apply in_frame_sh_In. exists (FF_READ_BLOCK, Fb, 64%Z). split; [left; reflexivity|].
      cbn [fb_addr fb_size fst snd]. change (Z.shiftr 64 3) with 8%Z. exact Ha. }
    split. { eapply agrees_stk; [exact AGy| exact STG|]. intros a Ha. left; lia. }
    split. { eapply agrees_rw_cells; [exact AGy| exact FR|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. left; lia. }
    split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AGy|]. intros a (K & _).
             destruct K as [K|[K|[K|K]]]; [left; lia| right; left; exact K| right; right; left; apply in_frames_cons; exact K| right; right; right; apply in_frame_sh_cons; exact K]. }
    split. { exists k0, k1, k2, pre. eapply agrees_rw_cells; [exact AGy| exact FRC1|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. right; right; left; apply INFR; lia. }
    split. { exists post. eapply agrees_rw_cells; [exact AGy| exact FRC3|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. right; right; left; apply INFR; lia. }
    eapply agrees_rw_cells; [exact AGy| exact SHC|]. intros a Ha. unfold rb_shadow in Ha. cbn [cells_size csize Nat.add] in Ha. right; right; right; apply INSH; lia.
  Qed.
  End Sz2.
  Lemma rb_inv_callee0 : ltac:(let t := eval cbv delta [rb_inv_callee0__stmt] in rb_inv_callee0__stmt in exact t).
  Proof using Type. intros ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx bq B alloc mm RNGy sy bq' B1 alloc' my. ltac2:(SecDiet.SzSec.closeP 'rb_inv_callee0__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition rb_grow_post__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (c0 c1 c2 c8 c9 c10 bold : word) (ccs : list cell) (p : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (q' : hptr) (A' : Z) (ej bsn : list byte) (bt tl : Z),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx q' A' tl mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 (Z_to_bv 64 (P + 24)); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (s32 tl));
                           C8 (Z_to_bv 64 CUR); C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10] ->
    rw_cells asegs mm (P + 20) [C4 (Z_to_bv 64 (pc_bufsize p)); C8 bold] ->
    rw_cells asegs mm (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
    rw_cells asegs mm (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize s))] ->
    rw_cells asegs mm A' [CB (Z.to_nat tl) bsn] -> firstn (length (zfirstn tl (pc_bufdata p))) bsn = map b8 (zfirstn tl (pc_bufdata p)) ->
    rw_cells asegs mm (Fb + 32) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)] ->
    rw_cells asegs mm EB [CB 256 ej] -> rw_cells asegs mm CUR ccs -> cells_size ccs = 24%nat ->
    pc_rfile p = f -> (0 <= pc_bufsize p <= 2^30)%Z -> (pc_bufsize p < tl)%Z -> (0 <= ng_max_blocksize s <= 2^28)%Z ->
    (0 <= bt < 2^32)%Z -> (12 <= tl <= 2^30)%Z -> (tl mod 4 = 0)%Z ->
    implMG RNGx (rb_bodyA HO FO sites f bt tl (set_buffer q' (pc_bufsize p) tl (zfirstn tl (pc_bufdata p)) p)) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 Af) (Z_to_bv 64 tl) (Z_to_bv 64 P) (Z_to_bv 64 (P + 56))
               (Z_to_bv 64 (Z.shiftr (P + 24) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8be9c) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c0 c1 c2 c8 c9 c10 bold ccs p s q' A' ej bsn bt tl : ltac2:(SecDiet.SzSec.tyM 'rb_grow_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_grow_post__body : ltac2:(SecDiet.SzSec.bodyP 'rb_grow_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT.
 intros CTX INV FRA HBS HPV HMB HBUF PFX HBH HEB HCUR Hccs RF WBS TLB WMB BT TL TL4.
    assert (AL0 : (0 < tl)%Z) by lia.
    rb_setup GL CTX INV AL0.
    pose proof (munch_refl [(P + 24, P + 32)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    apply implMG_from_evtF.
    zstep. if_false_by (eqz_false A' ltac:(lia)).
    ck0_at PUNP (P + 24)%Z; ck_go.
    zstep. zstep.
    assert (FX : Forall (cobj_iv FL (C1 ++ C2)) [(P + 24, P + 32)]%Z).
    { apply Forall_cons; [| apply Forall_nil]. split; [| cbn [fst snd]; lia]. cbn [fst snd]. left. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
      cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ mx [] _ (bv_unsigned sp) (Forall_nil _) FX G MU WM ltac:(lia)) as [G3 AG3];
      assert (INV3 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx q' A' tl mx)
    end.
    { cbn [app] in G3. unfold rb_inv, rb_shadow. split; [exact FP|]. split; [exact G3|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG3|]. intros a (K & N1 & N2 & N3). split; [exact K|]. cbn [outside fst snd]. split; [lia| exact I]. }
      split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
    apply evtF_done. subst POSTQ.
    eapply (rb_rd2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx)
      with (p := p) (p0 := set_buffer q' (pc_bufsize p) tl (zfirstn tl (pc_bufdata p)) p) (B0 := A') (ccs := ccs);
      [ exact CTX | exact INV3 | eassumption | | eassumption | eassumption | eassumption | exact Hccs | exact RF | exact BT | exact TL | exact TL4 | cbn [pc_bufalloc set_buffer]; lia ].
    unfold rb_handle, blk_handle. cbn [pc_bufsize pc_swapped pc_bufalloc pc_bufdata pc_priv pc_rfile pc_self set_buffer].
    split; [repeat (split; [first [assumption | lia]|]); lia|]. split; [exists bsn; split; assumption|].
    split; [unfold zfirstn; rewrite length_firstn; lia|].
    repeat (split; [reflexivity|]). unfold same_meta. cbn [pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header set_buffer].
    repeat (split; [reflexivity|]). reflexivity.
  Qed.
  End Sz3.
  Lemma rb_grow_post : ltac:(let t := eval cbv delta [rb_grow_post__stmt] in rb_grow_post__stmt in exact t).
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c0 c1 c2 c8 c9 c10 bold ccs p s q' A' ej bsn bt tl. ltac2:(SecDiet.SzSec.closeP 'rb_grow_post__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition rb_grow__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a4 a5 a6 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c8 c9 c10 : word) (ccs : list cell) (p : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (i : option hptr) (B : Z) (ej : list byte) (bt tl : Z),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p) B (pc_bufalloc p) mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 (Z_to_bv 64 CUR); C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10] ->
    rb_handle p p s P B mm ->
    rw_cells asegs mm (Fb + 32) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)] ->
    rw_cells asegs mm EB [CB 256 ej] -> rw_cells asegs mm CUR ccs -> cells_size ccs = 24%nat ->
    pc_rfile p = f -> pc_priv p = PrivNg s i -> pc_self p = self ->
    (0 <= bt < 2^32)%Z -> (12 <= tl < 2^32)%Z -> (tl mod 4 = 0)%Z -> (ng_max_blocksize s < 2^29 - 2^16)%Z ->
    agrees_on (fun a => (bv_unsigned sp <= a)%Z) m mm ->
    implMG RNGx (mo_bind MOps
                   (if (pc_bufsize p <? tl)%Z then
                      if (ng_max_blocksize (ng_of p) <? tl)%Z
                      then mo_ret MOps (Some (Msg.block_size_gt_max tl (ng_max_blocksize (ng_of p))), p)
                      else mo_bind MOps (e_realloc (prims HO FO sites) (pc_buffer p) tl) (fun r =>
                           match r with
                           | None => mo_ret MOps (Some Msg.out_of_memory, p)
                           | Some b => mo_ret MOps (@None (list Z), set_buffer b (pc_bufsize p) tl (zfirstn tl (pc_bufdata p)) p)
                           end)
                    else mo_ret MOps (@None (list Z), p))
                   (fun x => let '(gerr, p0) := x in
                    match gerr with
                    | Some m0 => e_fret (prims HO FO sites) FF_READ_BLOCK (RB_Err m0 p0)
                    | None => rb_bodyA HO FO sites f bt tl p0
                    end)) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 (Z_to_bv 64 (s32 tl)) a4 a5 a6 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880))
               (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 Af) (Z_to_bv 64 tl) (Z_to_bv 64 P) (Z_to_bv 64 (P + 56))
               (Z_to_bv 64 (P + 648)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8be18) fc None mm (seg_rom asegs)).
  Section Sz4.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a4 a5 a6 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c8 c9 c10 ccs p s i B ej bt tl : ltac2:(SecDiet.SzSec.tyM 'rb_grow__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_grow__body : ltac2:(SecDiet.SzSec.bodyP 'rb_grow__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT REALLOC RPC.
 intros CTX INV FRA HDL HBH HEB HCUR Hccs RF PRV SELF BT TL TL4 MBX AGS.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p)%Z) by lia.
    rb_setup GL CTX INV AL0.
    unfold ng_of. rewrite PRV.
    pose proof (munch_refl [(SPA, SPA + 88); (P + 24, P + 32)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    cbn [mo_bind mo_ret MOps e_realloc e_fret prims].
    apply implMG_from_evtF.
    zstep. ck0 PUNP; ck_go.
    zstep. do 2 zstep.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.unsigned_s32 tl ltac:(lia)) as UST.
    replace (sx32 (Z_to_bv 64 (pc_bufsize p))) with (Z_to_bv 64 (pc_bufsize p)) by (rewrite sx32_s32 by lia; rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.s32_small by lia; reflexivity).
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      rewrite unsigned_lit_wrap in UST.
      assert (TLB : (tl <= pc_bufsize p)%Z) by (Z.div_mod_to_equations; lia).
      replace (pc_bufsize p <? tl)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      assert (FW : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] [(pc_buffer p, B, pc_bufalloc p)] (bv_unsigned sp)) [(SPA, SPA + 88)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
      assert (FX : Forall (cobj_iv FL (C1 ++ C2)) [(P + 24, P + 32)]%Z).
      { apply Forall_cons; [| apply Forall_nil]. split; [| cbn [fst snd]; lia]. cbn [fst snd]. left. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
        cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ mx _ _ (bv_unsigned sp) FW FX G MU WM ltac:(lia)) as [G3 AG3];
        assert (INV3 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p) B (pc_bufalloc p) mx);
        [| assert (HDL3 : rb_handle p p s P B mx) ]
      end.
      { cbn [app] in G3. unfold rb_inv, rb_shadow. split; [exact FP|]. split; [exact G3|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
        split; [assumption|].
        split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG3|]. intros a (K & N1 & N2 & N3). split; [exact K|]. cbn [outside fst snd]. split; [lia| exact I]. }
        split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
      { unfold rb_handle, blk_handle. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
        repeat (split; [assumption|]). assumption. }
      apply evtF_done. apply implMG_retb. cbv iota beta. subst POSTQ.
      eapply (rb_rd2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx) with (p := p) (p0 := p) (B0 := B) (ccs := ccs);
        [ exact CTX | exact INV3 | eassumption | exact HDL3 | eassumption | eassumption | eassumption | exact Hccs | exact RF | exact BT | lia | exact TL4 | lia ].
    - (* [comment removed for export] *)
      rewrite unsigned_lit_wrap in UST.
      assert (TLB : (pc_bufsize p < tl)%Z) by (Z.div_mod_to_equations; lia).
      replace (pc_bufsize p <? tl)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      (* [comment removed for export] *)
      assert (XX : (0 < P + 648 < 2 ^ 64)%Z) by (atop_facts; lia).
      zstep. if_false_by (eqz_false (P + 648) XX).
      zstep. replace (Z.land (P + 648) 7) with 0%Z by (rewrite land7_mod; Z.div_mod_to_equations; lia).
      zstep. if_false.
      zstep. ck0 PUNP; ck_go.
      zstep.
      replace (sx32 (Z_to_bv 64 (ng_max_blocksize s))) with (Z_to_bv 64 (ng_max_blocksize s)) by (rewrite sx32_s32 by lia; rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.s32_small by lia; reflexivity).
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        assert (TLM : (tl <= ng_max_blocksize s)%Z) by (Z.div_mod_to_equations; lia).
        replace (ng_max_blocksize s <? tl)%Z with false by (symmetry; apply Z.ltb_ge; lia).
        zstep. ck0 PUNP; ck_go.
        do 3 zstep. zstep.
        assert (FW : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] [(pc_buffer p, B, pc_bufalloc p)] (bv_unsigned sp)) [(SPA, SPA + 88)]%Z)
          by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
        assert (FX : Forall (cobj_iv FL (C1 ++ C2)) [(P + 24, P + 32)]%Z).
        { apply Forall_cons; [| apply Forall_nil]. split; [| cbn [fst snd]; lia]. cbn [fst snd]. left. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
          cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
          destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ mx _ _ (bv_unsigned sp) FW FX G MU WM ltac:(lia)) as [G3 AG3];
          assert (INV3 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p) B (pc_bufalloc p) mx);
          [| assert (UC5 : ucallerA depth_read_block L mx sp s0 ra trC) ]
        end.
        { cbn [app] in G3. unfold rb_inv, rb_shadow. split; [exact FP|]. split; [exact G3|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
          split; [assumption|].
          split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG3|]. intros a (K & N1 & N2 & N3). split; [exact K|]. cbn [outside fst snd]. split; [lia| exact I]. }
          split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
        { eapply ucaller_keep; [exact UC| lia|]. intros a Ha.
          destruct (AGS a ltac:(lia) ltac:(lia)) as [EQa _]. rewrite <- EQa. apply MU. rewrite wa_unsigned by lia. cbn [outside fst snd]. split; [lia|]. split; [lia| exact I]. }
        cbn [app] in G3.
        pose proof (rw_cells_nth_C8 _ _ _ 11%nat _ FR eq_refl) as BS0. pose proof (rw_cells_nth_C8 _ _ _ 12%nat _ FR eq_refl) as BRA.
        cbn [firstn cells_size csize Nat.add] in BS0, BRA.
        replace (bv_unsigned sp + -104 + Z.of_nat 88)%Z with (bv_unsigned sp - 16)%Z in BS0 by lia.
        replace (bv_unsigned sp + -104 + Z.of_nat 96)%Z with (bv_unsigned sp - 8)%Z in BRA by lia.
        assert (TRX : In (tp_rpc TP :: 0x8be9c%Z :: bv_unsigned ra :: trC) (al_U L)) by (exact (proj2 TR)).
        remember (Z_to_bv 64 SPA) as spa eqn:Espa.
        assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
        apply evtF_done. apply implMG_bind_assoc. eapply implMG_bind.
        { eapply (REALLOC _ spa) with (L := L) (s := sx) (C1 := C1 ++ C2) (C2 := []) (FB := FB) (FL := (FF_READ_BLOCK, Fb, 64%Z) :: FL)
                                     (lo := lo) (q := pc_buffer p) (A := B) (sz := pc_bufalloc p) (n := tl) (bs := bs');
            [ split; [exact G3|]; rewrite Hspa; split; [assumption|]; split; [lia|]; split; [unfold REALLOC_STACK; lia|]; split; [lia|];
              split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
              split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
            | reflexivity | reflexivity | lia | eassumption
            | eapply (unw_of_ucaller (pred depth_read_block));
                [ eapply (ucaller_frame _ _ _ _ _ _ _ _ _ _ 0x8be9c%Z UC5); [rewrite Hspa; lia| lia| Z.div_mod_to_equations; lia| exact BS0| exact BRA
                    | reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_read_block; cbn; lia]
                | exact RPC
                | rewrite Hspa; lia
                | rewrite unsigned_lit by lia; exact TRX
                | exact RSTK ] ]. }
        intros r s6' RNG6 ms' PO. cbv beta in PO. destruct PO as (FP6 & av & m6 & E & OF6 & MI6 & ST6 & AG6 & PO).
        destruct r as [q'|]; [|destruct PO]. destruct PO as (A' & junk6 & -> & G6 & NEW).
        unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
        replace (ret_pc (Z_to_bv 64 573084)) with (Z_to_bv 64 573084) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        rewrite app_nil_r in AG6, G6.
        assert (G6' : GIOA L RNG6 s6' ((C1 ++ C2) ++ [(q', A', tl)]) FB ((FF_READ_BLOCK, Fb, 64%Z) :: FL) m6)
          by (eapply GPL; [exact G6|]; apply Permutation.Permutation_cons_append).
        assert (INV6 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNG6 s6' q' A' tl m6)
          by (eapply rb_inv_callee0; [exact INV3| lia| exact FP6| exact G6'| exact OF6| exact MI6| exact ST6| exact AG6]).
        assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) (C1 ++ C2) SPA a).
        { intros a Ha. right; left. apply in_block_In. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
        assert (INF : forall a, (Fb <= a < Fb + 64)%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) (C1 ++ C2) SPA a).
        { intros a Ha. right; right; left. apply in_frames_In. exists (FF_READ_BLOCK, Fb, 64%Z). split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]. }
        apply (agrees_rw_cells _ _ _ _ _ AG6) in FRA; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; left; lia].
        apply (agrees_rw_cells _ _ _ _ _ AG6) in HCUR; [| intros a Ha; rewrite Hccs in Ha; left; lia].
        apply (agrees_rw_cells _ _ _ _ _ AG6) in HEB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ EBLOC (incl_refl _) IFL)| lia]].
        apply (agrees_rw_cells _ _ _ _ _ AG6) in HBS; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
        apply (agrees_rw_cells _ _ _ _ _ AG6) in HPV; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
        apply (agrees_rw_cells _ _ _ _ _ AG6) in HMB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
        apply (agrees_rw_cells _ _ _ _ _ AG6) in HBH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INF; lia].
        assert (LBS : length bs' = Z.to_nat (pc_bufalloc p)) by (destruct HBUF as [[WFb _] _]; cbn in WFb; tauto).
        apply (rw_cells_merge asegs m6 A' [] [_; _] []) in NEW. cbn [app] in NEW.
        replace (cells_size [CB (Z.to_nat (Z.min (pc_bufalloc p) tl)) (firstn (Z.to_nat (Z.min (pc_bufalloc p) tl)) bs'); CB (Z.to_nat (tl - Z.min (pc_bufalloc p) tl)) junk6])
          with (Z.to_nat tl) in NEW by (cbn [cells_size csize Nat.add]; lia).
        cbn [cells_bytes cbytes app] in NEW. rewrite app_nil_r in NEW.
        pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.realloc_prefix (pc_bufdata p) bs' junk6 (pc_bufalloc p) tl PFX LENB LBS ltac:(lia)) as PFX6. change PcapRep.b8 with b8 in PFX6.
        cbv iota beta. apply implMG_retb. cbv iota beta. subst POSTQ.
        eapply (rb_grow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNG6 s6' m6)
          with (p := p) (s := s) (q' := q') (A' := A') (ccs := ccs);
          [ exact CTX | exact INV6 | eassumption | eassumption | eassumption | eassumption | exact NEW | exact PFX6 | eassumption | eassumption | eassumption | exact Hccs
          | exact RF | lia | lia | lia | exact BT | lia | exact TL4 ].
      + (* [comment removed for export] *)
        assert (TLM : (ng_max_blocksize s < tl)%Z) by (Z.div_mod_to_equations; lia).
        replace (ng_max_blocksize s <? tl)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        assert (FW : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] [(pc_buffer p, B, pc_bufalloc p)] (bv_unsigned sp)) [(SPA, SPA + 88)]%Z)
          by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
        assert (FX : Forall (cobj_iv FL (C1 ++ C2)) [(P + 24, P + 32)]%Z).
        { apply Forall_cons; [| apply Forall_nil]. split; [| cbn [fst snd]; lia]. cbn [fst snd]. left. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
          cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
        do 3 zstep. do 2 zstep. do 2 zstep. zstep.
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
          destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ mx _ _ (bv_unsigned sp) FW FX G MU WM ltac:(lia)) as [G3 AG3];
          assert (INV3 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p) B (pc_bufalloc p) mx);
          [| assert (HDL3 : rb_handle p p s P B mx); [| assert (MSG : fmt_at mx 0x22460 "pcapng block size %u > maximum %u"%string) by (fmt_at_solve MI 0x22460%Z "pcapng block size %u > maximum %u"%string) ] ]
        end.
        { cbn [app] in G3. unfold rb_inv, rb_shadow. split; [exact FP|]. split; [exact G3|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
          split; [assumption|].
          split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG3|]. intros a (K & N1 & N2 & N3). split; [exact K|]. cbn [outside fst snd]. split; [lia| exact I]. }
          split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
        { unfold rb_handle, blk_handle. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
          repeat (split; [assumption|]). assumption. }
        apply evtF_done. apply implMG_retb. cbv iota beta. subst POSTQ.
        replace (Msg.block_size_gt_max tl (ng_max_blocksize s)) with (Fmt.snprintf 256 "pcapng block size %u > maximum %u"%string [AInt (s32 tl); AInt (ng_max_blocksize s)])
          by (unfold Msg.block_size_gt_max, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
              replace (convs (fmt "pcapng block size %u > maximum %u")) with [Cu; Cu] by (vm_compute; reflexivity);
              apply pargs_cons; [apply aeq_s32; reflexivity|]; apply pargs_cons; [apply aeq_same| apply pargs_nil]).
        eapply (rb_snp FO GIOA TP fflagA GL GPL FRET SNPRINTF) with (pc := 0x8bd6c%Z) (p := p) (p' := p) (B' := B) (ccs' := ccs) (ej' := ej) (args := [AInt (s32 tl); AInt (ng_max_blocksize s)]);
          [ left; reflexivity | exact CTX | exact INV3 | eassumption | reflexivity | exact HDL3 | eassumption | eassumption | exact Hccs
          | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
          | apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2] ].
  Qed.
  End Sz4.
  Lemma rb_grow : ltac:(let t := eval cbv delta [rb_grow__stmt] in rb_grow__stmt in exact t).
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT REALLOC RPC. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a4 a5 a6 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c8 c9 c10 ccs p s i B ej bt tl. ltac2:(SecDiet.SzSec.closeP 'rb_grow__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition rb_len__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 r24 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c8 c9 c10 : word) (ccs : list cell) (p : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (i : option hptr) (B : Z) (ej : list byte) (bt tl : Z),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p) B (pc_bufalloc p) mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 (Z_to_bv 64 CUR); C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10] ->
    rb_handle p p s P B mm ->
    rw_cells asegs mm (Fb + 32) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)] ->
    rw_cells asegs mm EB [CB 256 ej] -> rw_cells asegs mm CUR ccs -> cells_size ccs = 24%nat ->
    pc_rfile p = f -> pc_priv p = PrivNg s i -> pc_self p = self ->
    (0 <= bt < 2^32)%Z -> (0 <= tl < 2^32)%Z -> (ng_max_blocksize s < 2^29 - 2^16)%Z ->
    agrees_on (fun a => (bv_unsigned sp <= a)%Z) m mm ->
    implMG RNGx (rb_tailA HO FO sites f bt tl p) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880))
               (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 Af) r24 (Z_to_bv 64 P) (Z_to_bv 64 (P + 56))
               (Z_to_bv 64 (P + 648)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bcb8) fc None mm (seg_rom asegs)).
  Section Sz5.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 r24 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c8 c9 c10 ccs p s i B ej bt tl : ltac2:(SecDiet.SzSec.tyM 'rb_len__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_len__body : ltac2:(SecDiet.SzSec.bodyP 'rb_len__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT REALLOC RPC.
 intros CTX INV FRA HDL HBH HEB HCUR Hccs RF PRV SELF BT TL MBX AGS.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p)%Z) by lia.
    rb_setup GL CTX INV AL0.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    unfold rb_tailA. cbn [e_fret prims].
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.unsigned_s32 tl ltac:(lia)) as UST. rewrite unsigned_lit_wrap in UST. change (2 ^ 64)%Z with 18446744073709551616%Z in UST.
    apply implMG_from_evtF.
    zstep. rewrite (zx32_lit tl) by lia.
    do 2 zstep. rewrite ?unsigned_lit by lia. rewrite ?Z.add_0_r, ?swrap32_s32.
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      replace (tl <? 12)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      zstep. zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        assert (TL4 : (tl mod 4 = 0)%Z).
        { rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.land3_low _ tl (tl / 2^31 * (2^32 - 1))) in K2; [exact K2| lia| lia| Z.div_mod_to_equations; lia]. }
        replace (negb (tl mod 4 =? 0))%Z with false by (rewrite TL4; reflexivity).
        apply evtF_done. subst POSTQ.
        eapply (rb_grow ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm) with (p := p) (s := s) (i := i) (B := B) (ccs := ccs);
          [ exact CTX | exact INV | exact FRA | exact HDL | exact HBH | exact HEB | exact HCUR | exact Hccs | exact RF | exact PRV | exact SELF | exact BT | lia | exact TL4 | exact MBX | exact AGS ].
      + (* [comment removed for export] *)
        assert (TL4 : (tl mod 4 <> 0)%Z).
        { intros X. apply K2. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.land3_low _ tl (tl / 2^31 * (2^32 - 1))); [exact X| lia| lia| Z.div_mod_to_equations; lia]. }
        replace (negb (tl mod 4 =? 0))%Z with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact TL4).
        assert (MSG : fmt_at mm 0x223e0 "block in pcapng dump file has a length of %u that is not a multiple of 4"%string)
          by (fmt_at_solve MI 0x223e0%Z "block in pcapng dump file has a length of %u that is not a multiple of 4"%string).
        do 2 zstep. do 2 zstep. zstep.
        apply evtF_done. subst POSTQ.
        replace (Msg.block_length_not_mult4 tl) with (Fmt.snprintf 256 "block in pcapng dump file has a length of %u that is not a multiple of 4"%string [AInt (s32 tl)])
          by (unfold Msg.block_length_not_mult4, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
              replace (convs (fmt "block in pcapng dump file has a length of %u that is not a multiple of 4")) with [Cu] by (vm_compute; reflexivity);
              apply pargs_cons; [apply aeq_s32; reflexivity| apply pargs_nil]).
        eapply (rb_snp FO GIOA TP fflagA GL GPL FRET SNPRINTF) with (pc := 0x8bd48%Z) (p := p) (p' := p) (B' := B) (ccs' := ccs) (ej' := ej) (args := [AInt (s32 tl)]);
          [ right; left; reflexivity | exact CTX | exact INV | exact FRA | reflexivity | exact HDL | exact HEB | exact HCUR | exact Hccs
          | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor]
          | apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints1] ].
    - (* [comment removed for export] *)
      replace (tl <? 12)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      assert (MSG : fmt_at mm 0x22380 "block in pcapng dump file has a length of %u < %zu"%string)
        by (fmt_at_solve MI 0x22380%Z "block in pcapng dump file has a length of %u < %zu"%string).
      do 4 zstep. do 2 zstep. zstep.
      apply evtF_done. subst POSTQ.
      replace (Msg.block_length_lt tl) with (Fmt.snprintf 256 "block in pcapng dump file has a length of %u < %zu"%string [AInt (s32 tl); AInt 12])
        by (unfold Msg.block_length_lt, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
            lazymatch goal with |- pargs ?c _ _ => let c' := eval vm_compute in c in change c with c' end;
            apply pargs_cons; [apply aeq_s32; reflexivity|]; apply pargs_cons; [apply aeq_same| apply pargs_nil]).
      eapply (rb_snp FO GIOA TP fflagA GL GPL FRET SNPRINTF) with (pc := 0x8bd6c%Z) (p := p) (p' := p) (B' := B) (ccs' := ccs) (ej' := ej) (args := [AInt (s32 tl); AInt 12]);
        [ left; reflexivity | exact CTX | exact INV | exact FRA | reflexivity | exact HDL | exact HEB | exact HCUR | exact Hccs
        | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
        | apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2] ].
  Qed.
  End Sz5.
  Lemma rb_len : ltac:(let t := eval cbv delta [rb_len__stmt] in rb_len__stmt in exact t).
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT REALLOC RPC. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 r24 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c8 c9 c10 ccs p s i B ej bt tl. ltac2:(SecDiet.SzSec.closeP 'rb_len__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbBody.
End CANSEC1.
End TwB.
End F_ngblk_bodyA.

(* [comment removed for export] *)
Module F_ngblk_rdA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_pcap_open2A__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_pcap_open2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngblk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_ngblk_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_ngblk_shortA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngblk_segA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_ngblk_tailA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_ngblk_bodyA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_psegA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.
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
(* [comment removed for export] *)
Local Ltac oiv_lo_base k := lazymatch goal with |- (?lo0 <= ?lo)%Z /\ _ => d_split lo0 ltac:(fun X0 _ _ => d_split lo ltac:(fun X _ _ => constr_eq X0 X; k)) end.
Local Ltac oiv_orig :=
  first [ left; cbn [fst snd]; lia
        | right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; lia
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; lia ].
Local Ltac own_iv1 ::=
  unfold own_ivA, iv_in_block, iv_in_frames, iv_in_frame_shadow;
  first [ right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; oiv_lo_base ltac:(lia)
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; oiv_lo_base ltac:(lia)
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; oiv_lo_base ltac:(lia)
        | oiv_orig ].
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section RbRd.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.

  (* [comment removed for export] *)
  Definition rb_rdhdr__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r19 r21 r24 r25 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c8 c9 c10 : word) (ccs : list cell) (p : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (i : option hptr) (B : Z) (ej bj : list byte)
      (site : stack_site),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p) B (pc_bufalloc p) mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 (Z_to_bv 64 CUR); C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10] ->
    rb_handle p p s P B mm ->
    rw_cells asegs mm (Fb + 32) [CB 8 bj] ->
    rw_cells asegs mm EB [CB 256 ej] -> rw_cells asegs mm CUR ccs -> cells_size ccs = 24%nat ->
    pc_rfile p = f -> pc_priv p = PrivNg s i -> pc_self p = self ->
    site_frameA site = Some (FF_READ_BLOCK, 32%Z) ->
    (ng_max_blocksize s < 2^29 - 2^16)%Z ->
    agrees_on (fun a => (bv_unsigned sp <= a)%Z) m mm ->
    implMG RNGx (mo_bind MOps (read_bytes MOps (prims HO FO sites) f (DStack site 0) 8 false) (fun x => let '(st, bh) := x in
                   match st with
                   | RBS_Eof => e_fret (prims HO FO sites) FF_READ_BLOCK (RB_Eof p)
                   | RBS_Err m0 => e_fret (prims HO FO sites) FF_READ_BLOCK (RB_Err m0 p)
                   | RBS_Ok => rb_tailA HO FO sites f (if pc_swapped p then bswap32 (get_le32 bh 0) else get_le32 bh 0)
                                 (if pc_swapped p then bswap32 (get_le32 bh 4) else get_le32 bh 4) p
                   end)) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (P + 48)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r21 (Z_to_bv 64 Af) (Z_to_bv 64 P) r24 r25
               (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bc50) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r19 r21 r24 r25 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c8 c9 c10 ccs p s i B ej bj site : ltac2:(SecDiet.SzSec.tyM 'rb_rdhdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_rdhdr__body : ltac2:(SecDiet.SzSec.bodyP 'rb_rdhdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT REALLOC RPC.
 intros CTX INV FRA HDL HBJ HEB HCUR Hccs RF PRV SELF SITEQ MBX AGS.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p)%Z) by lia.
    rb_setup GL CTX INV AL0.
    pose proof (munch_refl [(SPA, SPA + 88); (Fb + 32, Fb + 40)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    unfold read_bytes. cbn [mo_bind mo_ret MOps e_fread e_ferror e_fret prims].
    apply implMG_from_evtF.
    destruct (rw_cells_cut _ _ _ 1 HPV) as [C48 _]. cbn [firstn skipn cells_size csize Nat.add] in C48. unfold PCAP_PRIV_OFF in C48.
    assert (RSP88 : rng RNGx SPA 88) by (eapply rng_sub'; [exact RSPA| lia]).
    assert (SPALO : (17594333495296 <= SPA)%Z) by (atop_facts; lia).
    eapply evtF_cut; [ eapply rb_s1_seq with (P := P) (Fb := Fb) (Af := Af) (bP := bP); [try eassumption ..]; lia | post_call asegs mm ].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    lazymatch goal with HH : rw_cells asegs m3 SPA _ |- _ => rename HH into FRA3 end.
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] [(pc_buffer p, B, pc_bufalloc p)] (bv_unsigned sp)) [(SPA, SPA + 88); (Fb + 32, Fb + 40)]%Z).
    { eapply Forall_impl; [apply own_ivA_PB|]. own_ivs. }
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ m3 _ [] (bv_unsigned sp) FW (Forall_nil _) G MU WM ltac:(lia)) as [G3 AG3].
    assert (INV3 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p) B (pc_bufalloc p) m3).
    { cbn [app] in G3. unfold rb_inv, rb_shadow. split; [exact FP|]. split; [exact G3|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG3|]. intros a (K & N1 & N2 & N3). split; [exact K| exact I]. }
      split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
    cbn [app] in G3.
    assert (AGS3 : agrees_on (fun a => (bv_unsigned sp <= a)%Z) m m3).
    { eapply agrees_on_trans; [exact AGS|]. eapply agrees_on_weaken; [exact AG3|]. intros a Ha. split; [left; exact Ha| exact I]. }
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G3) as [FAll3 _]. pose proof (Forall_inv FAll3) as FRM3. clear FAll3.
    pose proof (unp_of_sh_bytes _ _ _ 4%nat 1%nat SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia)) as UNPH.
    change (8 * Z.of_nat 4)%Z with 32%Z in UNPH. change (8 * Z.of_nat 1)%Z with 8%Z in UNPH.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. apply implMG_bind_assoc. eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest].
      rewrite (gl_site _ _ _ GL _ _ _ _ _ _ _ _ _ _ site 32%Z G3 (or_introl eq_refl) SITEQ).
      replace (Fb + 32 + 0)%Z with (Fb + 32)%Z by lia.
      eapply (FREAD _ spa) with (Af := Af);
        [ split; [exact G3|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact HBJ
        | split; [right; exists (FF_READ_BLOCK, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM3| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPH] ]. }
    intros got s6' RNG6 ms' PO. cbv beta in PO.
    destruct PO as (FP6 & av & m6 & junk6 & E & OF6 & MI6 & ST6 & AG6 & G6 & -> & GOTL & GOTR & HD6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 572548)) with (Z_to_bv 64 572548) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (INV6 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNG6 s6' (pc_buffer p) B (pc_bufalloc p) m6).
    { eapply (rb_inv_callee FO GIOA fflagA GL) with (Pn := fun a => ~ (Fb + 32 <= a < Fb + 32 + 8)%Z);
        [ exact INV3 | lia | lia | exact FP6 | exact G6 | exact OF6 | exact MI6 | exact ST6 | exact AG6
        | intros a Ha; lia | intros a Ha; lia | intros a Ha; lia
        | intros a KK NB NFr Hx; apply NFr; lia ]. }
    assert (KK : forall A cs, rw_cells asegs m3 A cs ->
              (forall a, (A <= a < A + Z.of_nat (cells_size cs))%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p, B, pc_bufalloc p)]) SPA a) ->
              (A + Z.of_nat (cells_size cs) <= Fb + 32 \/ Fb + 40 <= A)%Z -> rw_cells asegs m6 A cs).
    { intros A cs HC HK HD. eapply agrees_rw_cells; [exact AG6| exact HC|]. intros a Ha. split; [apply HK; exact Ha| lia]. }
    assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p, B, pc_bufalloc p)]) SPA a).
    { intros a Ha. right; left. apply in_block_app. left. apply in_block_In. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
      cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (INB : forall a, (B <= a < B + pc_bufalloc p)%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p, B, pc_bufalloc p)]) SPA a).
    { intros a Ha. right; left. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply KK in FRA3; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; left; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HCUR; [| intros a Ha; rewrite Hccs in Ha; left; lia | rewrite Hccs; lia].
    apply KK in HEB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; eapply clocA_keeps; [exact (proj1 OEB)| lia] | cbn [cells_size csize Nat.add]; lia].
    apply KK in HBS; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HPV; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HMB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HBUF; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INB; lia | cbn [cells_size csize Nat.add]; lia].
    assert (HDL6 : rb_handle p p s P B m6).
    { unfold rb_handle, blk_handle. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
      repeat (split; [assumption|]). exact E6. }
    assert (AGS6 : agrees_on (fun a => (bv_unsigned sp <= a)%Z) m m6).
    { eapply agrees_on_trans; [exact AGS3|]. eapply agrees_on_weaken; [exact AG6|]. intros a Ha. split; [left; lia| lia]. }
    (* [comment removed for export] *)
    repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP6) in HR end.
    clear PUNP. pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G6 HinP') as (_ & _ & PUNP & _). cbn [cb_addr cb_size fst snd] in PUNP. unfold PCAP_NG_SF_TOTAL in PUNP.
    destruct (Z.eq_dec (zlength got) 8) as [LEQ|LNE].
    2:{ (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU6. pose proof (wmono_refl asegs m6) as WM6.
      apply implMG_from_evtF. zstep. if_cases Kq; [|zify_cond Kq; exfalso; lia].
      apply evtF_done. subst POSTQ.
      eapply (rb_short1 HO FO sites GIOA TP fflagA GL GPL FRET FERROR SNPRINTF FMT) with (p := p) (p' := p) (B' := B) (ccs := ccs) (got := got);
        [ exact CTX | exact INV6 | exact FRA3 | exact HDL6 | exact HEB | exact HCUR | exact Hccs | lia | exact LNE | intros msg; reflexivity | reflexivity ]. }
    (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb]. apply implMG_retb. cbv iota beta. rewrite LEQ.
    assert (L8n : length got = 8%nat) by (unfold zlength in LEQ; lia).
    destruct got as [|g0 [|g1 [|g2 [|g3 [|g4 [|g5 [|g6 [|g7 [|gx gr]]]]]]]]]; try (exfalso; cbn in L8n; lia). clear L8n LEQ GOTL.
    pose proof GOTR as GR'. do 8 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    assert (LJ : length junk6 = 0%nat) by (destruct HD6 as [[WF _] _]; cbn in WF; lia). destruct junk6 as [|jx jr]; [|discriminate LJ]. clear LJ.
    assert (HD5 : rw_cells asegs m6 (Fb + 32) [C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C4 (Z_to_bv 64 (le4val g4 g5 g6 g7))]).
    { eapply rw_cells_recell; [exact HD6 | cbn; repeat split; try exact Logic.I |]. cbn [cells_bytes cbytes map app]. unfold b8.
      rewrite (le4_lit g0 g1 g2 g3), (le4_lit g4 g5 g6 g7) by lia. reflexivity. }
    clear HD6.
    assert (EG0 : get_le32 [g0; g1; g2; g3; g4; g5; g6; g7] 0 = le4val g0 g1 g2 g3)
      by (unfold get_le32, zslice, zfirstn, zskipn; change (Z.to_nat 0) with 0%nat; change (Z.to_nat 4) with 4%nat; cbn [firstn skipn]; rewrite le_of_bytes_4; reflexivity).
    assert (EG4 : get_le32 [g0; g1; g2; g3; g4; g5; g6; g7] 4 = le4val g4 g5 g6 g7)
      by (unfold get_le32, zslice, zfirstn, zskipn; change (Z.to_nat 0) with 0%nat; change (Z.to_nat 4) with 4%nat; cbn [firstn skipn]; rewrite le_of_bytes_4; reflexivity).
    rewrite EG0, EG4. clear EG0 EG4.
    pose proof INV6 as (_ & _ & _ & _ & ST6' & STG6 & FR6 & _ & (k0' & k1' & k2' & pre' & FRC1') & (post' & FRC3') & SHC6).
    unfold rb_shadow in SHC6.
    assert (RBH : rng RNG6 (Fb + 32) 8) by (eapply rng_sub'; [exact FRNG| lia]).
    pose proof (munch_refl [(Fb + 32, Fb + 40)]%Z m6) as MU6. pose proof (wmono_refl asegs m6) as WM6.
    apply implMG_from_evtF. zstep. if_false.
    zstep.
    ck0 PUNP; ck_go.
    zstep.
    destruct (pc_swapped p) eqn:ESW; cbn [Z.b2z].
    - (* [comment removed for export] *)
      replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
      zstep. if_false.
      eapply evtF_cut; [ eapply rb_hdr_swap_seq with (HB := (Fb + 32)%Z) (g0 := g0) (g1 := g1) (g2 := g2) (g3 := g3) (g4 := g4) (g5 := g5) (g6 := g6) (g7 := g7);
                         [try eassumption ..]; lia | post_call asegs m6 ].
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
      lazymatch goal with HH : rw_cells asegs m7 (Fb + 32)%Z _ |- _ => rename HH into HD7 end.
      assert (FW7 : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] [(pc_buffer p, B, pc_bufalloc p)] (bv_unsigned sp)) [(Fb + 32, Fb + 40)]%Z)
        by (eapply Forall_impl; [apply own_ivA_PB|]; own_ivs).
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ m7 _ [] (bv_unsigned sp) FW7 (Forall_nil _) G6 MU6 WM6 ltac:(lia)) as [G7 AG7].
      assert (INV7 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNG6 s6' (pc_buffer p) B (pc_bufalloc p) m7).
      { cbn [app] in G7. pose proof INV6 as (FP' & _ & OF' & _ & _ & _ & _ & AG' & _). unfold rb_inv, rb_shadow. split; [exact FP'|]. split; [exact G7|]. split; [exact OF'|].
        split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
        split. { eapply agrees_on_trans; [exact AG'|]. eapply agrees_on_weaken; [exact AG7|]. intros a (K & N1 & N2 & N3). split; [exact K| exact I]. }
        split; [exists k0', k1', k2', pre'; assumption|]. split; [exists post'; assumption| assumption]. }
      assert (HDL7 : rb_handle p p s P B m7).
      { unfold rb_handle, blk_handle. rewrite ESW. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
        repeat (split; [first [assumption | reflexivity]|]). first [exact E6 | reflexivity]. }
      assert (AGS7 : agrees_on (fun a => (bv_unsigned sp <= a)%Z) m m7).
      { eapply agrees_on_trans; [exact AGS6|]. eapply agrees_on_weaken; [exact AG7|]. intros a Ha. split; [left; exact Ha| exact I]. }
      apply evtF_done. subst POSTQ. cbv iota.
      rewrite (bswap32_le4val g0 g1 g2 g3), (bswap32_le4val g4 g5 g6 g7) by lia.
      eapply (rb_len HO FO sites GIOA TP fflagA GL HAL GPL FRET FREAD FERROR SNPRINTF FMT REALLOC RPC) with (p := p) (s := s) (i := i) (B := B) (ccs := ccs)
                (bt := le4val g3 g2 g1 g0) (tl := le4val g7 g6 g5 g4);
        [ exact CTX | exact INV7 | eassumption | exact HDL7 | exact HD7 | eassumption | eassumption | exact Hccs | exact RF | exact PRV | exact SELF
        | unfold le4val; lia | unfold le4val; lia | exact MBX | exact AGS7 ].
    - (* [comment removed for export] *)
      replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
      zstep. if_true.
      apply evtF_done. subst POSTQ. cbv iota.
      eapply (rb_len HO FO sites GIOA TP fflagA GL HAL GPL FRET FREAD FERROR SNPRINTF FMT REALLOC RPC) with (p := p) (s := s) (i := i) (B := B) (ccs := ccs)
                (bt := le4val g0 g1 g2 g3) (tl := le4val g4 g5 g6 g7);
        [ exact CTX | exact INV6 | exact FRA3 | | exact HD5 | exact HEB | exact HCUR | exact Hccs | exact RF | exact PRV | exact SELF
        | unfold le4val; lia | unfold le4val; lia | exact MBX | exact AGS6 ].
      unfold rb_handle, blk_handle. rewrite ESW. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
      repeat (split; [first [assumption | reflexivity]|]). first [exact E6 | reflexivity].
  Qed.
  End Sz1.
  Lemma rb_rdhdr : ltac:(let t := eval cbv delta [rb_rdhdr__stmt] in rb_rdhdr__stmt in exact t).
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT REALLOC RPC. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r19 r21 r24 r25 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c8 c9 c10 ccs p s i B ej bj site. ltac2:(SecDiet.SzSec.closeP 'rb_rdhdr__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbRd.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_sfchk_fsegA__B3P.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_sfchk_fsegA__B3P.SfAuxB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngblk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_ngblk_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_ngblk_shortA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngblk_segA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_ngblk_tailA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_ngblk_bodyA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_psegA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB.
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
(* [comment removed for export] *)
Local Ltac oiv_lo_base k := lazymatch goal with |- (?lo0 <= ?lo)%Z /\ _ => d_split lo0 ltac:(fun X0 _ _ => d_split lo ltac:(fun X _ _ => constr_eq X0 X; k)) end.
Local Ltac oiv_orig :=
  first [ left; cbn [fst snd]; lia
        | right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; lia
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; lia ].
Local Ltac own_iv1 ::=
  unfold own_ivA, iv_in_block, iv_in_frames, iv_in_frame_shadow;
  first [ right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; oiv_lo_base ltac:(lia)
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; oiv_lo_base ltac:(lia)
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; oiv_lo_base ltac:(lia)
        | oiv_orig ].
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section RbRd.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.

  (* [comment removed for export] *)
  Definition rb_rdhdr__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 r21 r24 r25 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c8 c9 c10 : word) (ccs : list cell) (p : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (i : option hptr) (B : Z) (ej bj : list byte)
      (site : stack_site),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p) B (pc_bufalloc p) mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 (Z_to_bv 64 CUR); C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10] ->
    rb_handle p p s P B mm ->
    rw_cells asegs mm (Fb + 32) [CB 8 bj] ->
    rw_cells asegs mm EB [CB 256 ej] -> rw_cells asegs mm CUR ccs -> cells_size ccs = 24%nat ->
    pc_rfile p = f -> pc_priv p = PrivNg s i -> pc_self p = self ->
    site_frameA site = Some (FF_READ_BLOCK, 32%Z) ->
    (ng_max_blocksize s < 2^29 - 2^16)%Z ->
    agrees_on (fun a => (bv_unsigned sp <= a)%Z) m mm ->
    implMG RNGx (mo_bind MOps (read_bytes MOps (prims HO FO sites) f (DStack site 0) 8 false) (fun x => let '(st, bh) := x in
                   match st with
                   | RBS_Eof => e_fret (prims HO FO sites) FF_READ_BLOCK (RB_Eof p)
                   | RBS_Err m0 => e_fret (prims HO FO sites) FF_READ_BLOCK (RB_Err m0 p)
                   | RBS_Ok => rb_tailA HO FO sites f (if pc_swapped p then bswap32 (get_le32 bh 0) else get_le32 bh 0)
                                 (if pc_swapped p then bswap32 (get_le32 bh 4) else get_le32 bh 4) p
                   end)) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) r21 (Z_to_bv 64 Af) r24 (Z_to_bv 64 P) r25
               r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bbf8) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 r21 r24 r25 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c8 c9 c10 ccs p s i B ej bj site : ltac2:(SecDiet.SzSec.tyM 'rb_rdhdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_rdhdr__body : ltac2:(SecDiet.SzSec.bodyP 'rb_rdhdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT REALLOC RPC.
 intros CTX INV FRA HDL HBJ HEB HCUR Hccs RF PRV SELF SITEQ MBX AGS.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p)%Z) by lia.
    rb_setup GL CTX INV AL0.
    pose proof (munch_refl [(SPA, SPA + 88); (Fb + 32, Fb + 40)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    unfold read_bytes. cbn [mo_bind mo_ret MOps e_fread e_ferror e_fret prims].
    apply implMG_from_evtF.
    destruct (rw_cells_cut _ _ _ 1 HPV) as [C48 _]. cbn [firstn skipn cells_size csize Nat.add] in C48. unfold PCAP_PRIV_OFF in C48.
    assert (RSP88 : rng RNGx SPA 88) by (eapply rng_sub'; [exact RSPA| lia]).
    assert (SPALO : (17594333495296 <= SPA)%Z) by (atop_facts; lia).
    eapply evtF_cut; [ eapply rb_s1_seq with (P := P) (Fb := Fb) (Af := Af) (bP := bP); [try eassumption ..]; lia | post_call asegs mm ].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    lazymatch goal with HH : rw_cells asegs m3 SPA _ |- _ => rename HH into FRA3 end.
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] [(pc_buffer p, B, pc_bufalloc p)] (bv_unsigned sp)) [(SPA, SPA + 88); (Fb + 32, Fb + 40)]%Z).
    { eapply Forall_impl; [apply own_ivA_PB|]. own_ivs. }
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ m3 _ [] (bv_unsigned sp) FW (Forall_nil _) G MU WM ltac:(lia)) as [G3 AG3].
    assert (INV3 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p) B (pc_bufalloc p) m3).
    { cbn [app] in G3. unfold rb_inv, rb_shadow. split; [exact FP|]. split; [exact G3|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG3|]. intros a (K & N1 & N2 & N3). split; [exact K| exact I]. }
      split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
    cbn [app] in G3.
    assert (AGS3 : agrees_on (fun a => (bv_unsigned sp <= a)%Z) m m3).
    { eapply agrees_on_trans; [exact AGS|]. eapply agrees_on_weaken; [exact AG3|]. intros a Ha. split; [left; exact Ha| exact I]. }
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G3) as [FAll3 _]. pose proof (Forall_inv FAll3) as FRM3. clear FAll3.
    pose proof (unp_of_sh_bytes _ _ _ 4%nat 1%nat SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia)) as UNPH.
    change (8 * Z.of_nat 4)%Z with 32%Z in UNPH. change (8 * Z.of_nat 1)%Z with 8%Z in UNPH.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. apply implMG_bind_assoc. eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest].
      rewrite (gl_site _ _ _ GL _ _ _ _ _ _ _ _ _ _ site 32%Z G3 (or_introl eq_refl) SITEQ).
      replace (Fb + 32 + 0)%Z with (Fb + 32)%Z by lia.
      eapply (FREAD _ spa) with (Af := Af);
        [ split; [exact G3|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact HBJ
        | split; [right; exists (FF_READ_BLOCK, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM3| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPH] ]. }
    intros got s6' RNG6 ms' PO. cbv beta in PO.
    destruct PO as (FP6 & av & m6 & junk6 & E & OF6 & MI6 & ST6 & AG6 & G6 & -> & GOTL & GOTR & HD6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 572472)) with (Z_to_bv 64 572472) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (INV6 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNG6 s6' (pc_buffer p) B (pc_bufalloc p) m6).
    { eapply (rb_inv_callee FO GIOA fflagA GL) with (Pn := fun a => ~ (Fb + 32 <= a < Fb + 32 + 8)%Z);
        [ exact INV3 | lia | lia | exact FP6 | exact G6 | exact OF6 | exact MI6 | exact ST6 | exact AG6
        | intros a Ha; lia | intros a Ha; lia | intros a Ha; lia
        | intros a KK NB NFr Hx; apply NFr; lia ]. }
    assert (KK : forall A cs, rw_cells asegs m3 A cs ->
              (forall a, (A <= a < A + Z.of_nat (cells_size cs))%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p, B, pc_bufalloc p)]) SPA a) ->
              (A + Z.of_nat (cells_size cs) <= Fb + 32 \/ Fb + 40 <= A)%Z -> rw_cells asegs m6 A cs).
    { intros A cs HC HK HD. eapply agrees_rw_cells; [exact AG6| exact HC|]. intros a Ha. split; [apply HK; exact Ha| lia]. }
    assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p, B, pc_bufalloc p)]) SPA a).
    { intros a Ha. right; left. apply in_block_app. left. apply in_block_In. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
      cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (INB : forall a, (B <= a < B + pc_bufalloc p)%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p, B, pc_bufalloc p)]) SPA a).
    { intros a Ha. right; left. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply KK in FRA3; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; left; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HCUR; [| intros a Ha; rewrite Hccs in Ha; left; lia | rewrite Hccs; lia].
    apply KK in HEB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; eapply clocA_keeps; [exact (proj1 OEB)| lia] | cbn [cells_size csize Nat.add]; lia].
    apply KK in HBS; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HPV; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HMB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia | cbn [cells_size csize Nat.add]; lia].
    apply KK in HBUF; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INB; lia | cbn [cells_size csize Nat.add]; lia].
    assert (HDL6 : rb_handle p p s P B m6).
    { unfold rb_handle, blk_handle. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
      repeat (split; [assumption|]). exact E6. }
    assert (AGS6 : agrees_on (fun a => (bv_unsigned sp <= a)%Z) m m6).
    { eapply agrees_on_trans; [exact AGS3|]. eapply agrees_on_weaken; [exact AG6|]. intros a Ha. split; [left; lia| lia]. }
    (* [comment removed for export] *)
    repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP6) in HR end.
    clear PUNP. pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G6 HinP') as (_ & _ & PUNP & _). cbn [cb_addr cb_size fst snd] in PUNP. unfold PCAP_NG_SF_TOTAL in PUNP.
    destruct (Z.eq_dec (zlength got) 8) as [LEQ|LNE].
    2:{ (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU6. pose proof (wmono_refl asegs m6) as WM6.
      apply implMG_from_evtF. zstep. if_cases Kq; [|zify_cond Kq; exfalso; lia].
      apply evtF_done. subst POSTQ.
      eapply (rb_short1 HO FO sites GIOA TP fflagA GL GPL FRET FERROR SNPRINTF FMT) with (p := p) (p' := p) (B' := B) (ccs := ccs) (got := got);
        [ exact CTX | exact INV6 | exact FRA3 | exact HDL6 | exact HEB | exact HCUR | exact Hccs | lia | exact LNE | intros msg; reflexivity | reflexivity ]. }
    (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb]. apply implMG_retb. cbv iota beta. rewrite LEQ.
    assert (L8n : length got = 8%nat) by (unfold zlength in LEQ; lia).
    destruct got as [|g0 [|g1 [|g2 [|g3 [|g4 [|g5 [|g6 [|g7 [|gx gr]]]]]]]]]; try (exfalso; cbn in L8n; lia). clear L8n LEQ GOTL.
    pose proof GOTR as GR'. do 8 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    assert (LJ : length junk6 = 0%nat) by (destruct HD6 as [[WF _] _]; cbn in WF; lia). destruct junk6 as [|jx jr]; [|discriminate LJ]. clear LJ.
    assert (HD5 : rw_cells asegs m6 (Fb + 32) [C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C4 (Z_to_bv 64 (le4val g4 g5 g6 g7))]).
    { eapply rw_cells_recell; [exact HD6 | cbn; repeat split; try exact Logic.I |]. cbn [cells_bytes cbytes map app]. unfold b8.
      rewrite (le4_lit g0 g1 g2 g3), (le4_lit g4 g5 g6 g7) by lia. reflexivity. }
    clear HD6.
    assert (EG0 : get_le32 [g0; g1; g2; g3; g4; g5; g6; g7] 0 = le4val g0 g1 g2 g3)
      by (unfold get_le32, zslice, zfirstn, zskipn; change (Z.to_nat 0) with 0%nat; change (Z.to_nat 4) with 4%nat; cbn [firstn skipn]; rewrite le_of_bytes_4; reflexivity).
    assert (EG4 : get_le32 [g0; g1; g2; g3; g4; g5; g6; g7] 4 = le4val g4 g5 g6 g7)
      by (unfold get_le32, zslice, zfirstn, zskipn; change (Z.to_nat 0) with 0%nat; change (Z.to_nat 4) with 4%nat; cbn [firstn skipn]; rewrite le_of_bytes_4; reflexivity).
    rewrite EG0, EG4. clear EG0 EG4.
    pose proof INV6 as (_ & _ & _ & _ & ST6' & STG6 & FR6 & _ & (k0' & k1' & k2' & pre' & FRC1') & (post' & FRC3') & SHC6).
    unfold rb_shadow in SHC6.
    assert (RBH : rng RNG6 (Fb + 32) 8) by (eapply rng_sub'; [exact FRNG| lia]).
    pose proof (munch_refl [(Fb + 32, Fb + 40)]%Z m6) as MU6. pose proof (wmono_refl asegs m6) as WM6.
    apply implMG_from_evtF. zstep. if_false.
    zstep.
    ck0 PUNP; ck_go.
    zstep.
    destruct (pc_swapped p) eqn:ESW; cbn [Z.b2z].
    - (* [comment removed for export] *)
      replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
      zstep. if_false.
      eapply evtF_cut; [ eapply rb_hdr_swap_seq with (HB := (Fb + 32)%Z) (g0 := g0) (g1 := g1) (g2 := g2) (g3 := g3) (g4 := g4) (g5 := g5) (g6 := g6) (g7 := g7);
                         [try eassumption ..]; lia | post_call asegs m6 ].
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
      lazymatch goal with HH : rw_cells asegs m7 (Fb + 32)%Z _ |- _ => rename HH into HD7 end.
      assert (FW7 : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] [(pc_buffer p, B, pc_bufalloc p)] (bv_unsigned sp)) [(Fb + 32, Fb + 40)]%Z)
        by (eapply Forall_impl; [apply own_ivA_PB|]; own_ivs).
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ m7 _ [] (bv_unsigned sp) FW7 (Forall_nil _) G6 MU6 WM6 ltac:(lia)) as [G7 AG7].
      assert (INV7 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNG6 s6' (pc_buffer p) B (pc_bufalloc p) m7).
      { cbn [app] in G7. pose proof INV6 as (FP' & _ & OF' & _ & _ & _ & _ & AG' & _). unfold rb_inv, rb_shadow. split; [exact FP'|]. split; [exact G7|]. split; [exact OF'|].
        split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
        split. { eapply agrees_on_trans; [exact AG'|]. eapply agrees_on_weaken; [exact AG7|]. intros a (K & N1 & N2 & N3). split; [exact K| exact I]. }
        split; [exists k0', k1', k2', pre'; assumption|]. split; [exists post'; assumption| assumption]. }
      assert (HDL7 : rb_handle p p s P B m7).
      { unfold rb_handle, blk_handle. rewrite ESW. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
        repeat (split; [first [assumption | reflexivity]|]). first [exact E6 | reflexivity]. }
      assert (AGS7 : agrees_on (fun a => (bv_unsigned sp <= a)%Z) m m7).
      { eapply agrees_on_trans; [exact AGS6|]. eapply agrees_on_weaken; [exact AG7|]. intros a Ha. split; [left; exact Ha| exact I]. }
      apply evtF_done. subst POSTQ. cbv iota.
      rewrite (bswap32_le4val g0 g1 g2 g3), (bswap32_le4val g4 g5 g6 g7) by lia.
      eapply (rb_len HO FO sites GIOA TP fflagA GL HAL GPL FRET FREAD FERROR SNPRINTF FMT REALLOC RPC) with (p := p) (s := s) (i := i) (B := B) (ccs := ccs)
                (bt := le4val g3 g2 g1 g0) (tl := le4val g7 g6 g5 g4);
        [ exact CTX | exact INV7 | eassumption | exact HDL7 | exact HD7 | eassumption | eassumption | exact Hccs | exact RF | exact PRV | exact SELF
        | unfold le4val; lia | unfold le4val; lia | exact MBX | exact AGS7 ].
    - (* [comment removed for export] *)
      replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
      zstep. if_true.
      apply evtF_done. subst POSTQ. cbv iota.
      eapply (rb_len HO FO sites GIOA TP fflagA GL HAL GPL FRET FREAD FERROR SNPRINTF FMT REALLOC RPC) with (p := p) (s := s) (i := i) (B := B) (ccs := ccs)
                (bt := le4val g0 g1 g2 g3) (tl := le4val g4 g5 g6 g7);
        [ exact CTX | exact INV6 | exact FRA3 | | exact HD5 | exact HEB | exact HCUR | exact Hccs | exact RF | exact PRV | exact SELF
        | unfold le4val; lia | unfold le4val; lia | exact MBX | exact AGS6 ].
      unfold rb_handle, blk_handle. rewrite ESW. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
      repeat (split; [first [assumption | reflexivity]|]). first [exact E6 | reflexivity].
  Qed.
  End Sz1.
  Lemma rb_rdhdr : ltac:(let t := eval cbv delta [rb_rdhdr__stmt] in rb_rdhdr__stmt in exact t).
  Proof using GL HAL GPL FRET FREAD FERROR SNPRINTF FMT REALLOC RPC. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 r21 r24 r25 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c8 c9 c10 ccs p s i B ej bj site. ltac2:(SecDiet.SzSec.closeP 'rb_rdhdr__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbRd.
End CANSEC1.
End TwB.
End F_ngblk_rdA.

(* [comment removed for export] *)
Module F_ngblk_mainA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngblk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_psegA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_ngblk_rdA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac plia_comp := first [ once ltac2:(LiaRel.lr_prune_sub ()); lia_tiers | once ltac2:(LiaRel.lr_prune_hub 5); lia_tiers
                              | once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); lia_tiers ].
Local Ltac own_iv1 ::=
  unfold own_ivA, iv_in_block, iv_in_frames, iv_in_frame_shadow;
  first [ left; cbn [fst snd]; atop_facts; plia_comp
        | right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; atop_facts; plia_comp
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; atop_facts; plia_comp
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; atop_facts; plia_comp
        | first [ left; cbn [fst snd]; lia
                | right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia
                | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; lia
                | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
                  cbn [cb_addr cb_size fst snd]; lia ] ].
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section RbMain.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FENTER0 : fenter_stmt_o FO GIOA fflagA 0 STACK_MALLOC_0.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.

  Definition read_block_proofA__stmt : Prop := read_block_stmt HO FO sites GIOA TP.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG st C1 C2 FB FL trC f Af P B CUR EB lo p s i a_bhdr bs ej ccs : ltac2:(SecDiet.SzSec.tyM 'read_block_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma read_block_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'read_block_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FENTER0 FRET FREAD FERROR SNPRINTF FMT REALLOC RPC.
 intros PRE UC TR NF HinF RF PRV HinP SITE -> -> -> -> BH HBUF PFX LENB HCUR Hccs CURS CUR8 HEB EBM EB8.
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    destruct SITE as (site & -> & SITEQ).
    subst f.
    assert (MBXs : (ng_max_blocksize s < 2^29 - 2^16)%Z) by (destruct BH as (_ & _ & _ & _ & WMBx & _); lia).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (HDLm : hidc (rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] /\ rw_cells asegs m CUR ccs /\ rw_cells asegs m EB [CB 256 ej]))
      by (split; [exact HBUF| split; [exact HCUR| exact HEB]]).
    clear HBUF HCUR HEB.
    (* [comment removed for export] *)
    set (bq := pc_buffer p) in *. set (alloc := pc_bufalloc p) in *.
    assert (PERM : Permutation.Permutation (C1 ++ (bq, B, alloc) :: C2) ((C1 ++ C2) ++ [(bq, B, alloc)])).
    { eapply Permutation.perm_trans; [apply Permutation.Permutation_sym, Permutation.Permutation_middle| apply Permutation.Permutation_cons_append]. }
    apply (GPL _ _ _ _ _ _ _ _ G) in PERM. clear G. rename PERM into G.
    set (CL := ((C1 ++ C2) ++ [(bq, B, alloc)])%list) in *.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & SUA & _) & GSU). unfold GOT_UAR in GSU.
    unfold READ_BLOCK_STACK, PCAP_L1_STACK in BU.
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    rewrite (read_block_eqA HO FO sites). cbn [e_fenter prims]. unfold READ_BLOCK_ENTRY.
    remember (bv_unsigned sp - 192 - (bv_unsigned sp - 192) mod 32)%Z as SPA eqn:ESPA.
    assert (SPAP : (bv_unsigned sp - 208 <= SPA <= bv_unsigned sp - 192 /\ SPA mod 32 = 0 /\ (bv_unsigned sp + -192) - (bv_unsigned sp + -192) mod 32 = SPA)%Z)
      by (rewrite ESPA; Z.div_mod_to_equations; lia).
    destruct SPAP as (SPAB & SPA32 & ESPA').
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    (* [comment removed for export] *)
    zstep.
    carve_frame 104%nat ST. carve_frame 88%nat ST.
    zstep.
    do 13 zstep.
    zstep.
    zstep.
    rewrite land_m32B by lia. rewrite ESPA'.
    release_frame FR0 ST (bv_unsigned sp + -104)%Z.
    destruct (stk_split asegs _ lo (SPA + 88) (bv_unsigned sp + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPA + 88) 88 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 88) with 88%Z in STL, FRA. replace (SPA + 88 - 88)%Z with SPA in STL, FRA by lia.
    destruct (spill_words11 _ _ _ FRA) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & FRW). clear FRA.
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    (* [comment removed for export] *)
    do 6 zstep.
    do 2 zstep.
    zstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    zstep.
    zstep.
    zstep. if_false.
    do 2 zstep.
    (* [comment removed for export] *)
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FWS : Forall (client_ivA FL CL) [(bv_unsigned sp - 208, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG st CL FB FL mm) by (eapply (gl_client_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FWS]);
      assert (AGa : agrees_on (client_keeps FL CL (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ CL [] _ FL []); [exact G' | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    rename MU into MU0. rename WM into WM0. clear FWS G'.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FENTER0 _ spa).
    { split; [exact G0|]. rewrite Hspa. split; [exact STL|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [Z.div_mod_to_equations; lia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { apply NF. left. reflexivity. }
    { reflexivity. }
    intros Fb s1' m2 j0 j1 j2 fjunk t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G1 OF1 LC1 TL1 MI1 ST1 AG1 Fb0 LJ FRC SHC.
    rewrite Hspa in *. clear Hspa. subst spa.
    change (ff_size FF_READ_BLOCK) with 64%Z in *.
    change (Z.to_nat (64 - 32)) with 32%nat in *. change (Z.to_nat (64 / 8)) with 8%nat in *.
    apply sh_zero_cells in SHC. cbn [repeat] in SHC.
    replace (ret_pc (Z_to_bv 64 572352)) with (Z_to_bv 64 572352) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G1) as [FAll FND]. pose proof (Forall_inv FAll) as FRM. pose proof FRM as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR).
    cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll.
    change (Z.shiftr 64 3) with 8%Z in FSRNG, FSWR.
    band_ind FBAND' bF.
    (* [comment removed for export] *)
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FRW; [|lia].
    apply (agrees_stk _ _ _ _ _ AG1) in STG; [|intros a Ha; left; lia].
    assert (AGb : agrees_on (client_keeps FL CL (bv_unsigned sp)) m m2).
    { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; exact Ha| apply incl_refl]. }
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000)%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    destruct SHLO as (SLO & SHI).
    assert (HinP' : In (pc_self p, P, PCAP_NG_SF_TOTAL) (CL ++ FB)) by (apply in_or_app; left; subst CL; apply in_or_app; left; exact HinP).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G1 HinP') as ((PBAND & _) & _). cbn [cb_addr cb_size fst snd] in PBAND. unfold PCAP_NG_SF_TOTAL in PBAND.
    pose proof (ablk_lin _ _ PBAND) as (_ & P0 & _ & PHI).
    clear AGa AG1 G0 MU0 WM0 MI STL GOT SHB SUA GSU.
    pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z m2) as MU.
    pose proof (wmono_refl asegs m2) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ1 := Q) end. apply implMG_from_evtF.
    (* [comment removed for export] *)
    pose proof PBAND as PBAND'. band_ind PBAND' bP.
    call rb_poison_seq; [try eassumption .. | ]; [lia .. | ].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
    lazymatch goal with HH : rw_cells asegs m3 Fb _ |- _ => rename HH into FRC end.
    lazymatch goal with HH : rw_cells asegs m3 (Z.shiftr Fb 3 + 2147450880)%Z _ |- _ => rename HH into SHC end.
    lazymatch goal with HH : rw_cells asegs m3 SPA _ |- _ => rename HH into FRW end.
    (* [comment removed for export] *)
    assert (G1n : GIOA L RNG s1' (CL ++ []) FB ([(FF_READ_BLOCK, Fb, 64%Z)] ++ FL) m2) by (rewrite app_nil_r; exact G1).
    assert (FW : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(bv_unsigned sp - 208, bv_unsigned sp); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z) by own_ivs.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ m3 _ [] _ FW (Forall_nil _) G1n MU WM ltac:(lia)) as [G2 AG2].
    rewrite app_nil_r in G2. cbn [app] in G2.
    assert (AGm : agrees_on (client_keeps FL CL (bv_unsigned sp)) m m3).
    { eapply agrees_on_trans; [exact AGb|]. eapply agrees_on_weaken; [exact AG2|]. intros a K. split; [exact K| exact I]. }
    unfold hidc in HDLm. destruct HDLm as (HBUF & HCUR & HEB).
    destruct BH as (HBS & HPV & HMB & WBS & WMB & WBA & BSA).
    assert (ICL : incl (C1 ++ C2) CL) by (subst CL; apply incl_appl, incl_refl).
    assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps FL CL (bv_unsigned sp) a).
    { intros a Ha. right; left. subst CL. apply in_block_app. left. apply in_block_In. exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
      cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (INB : forall a, (B <= a < B + alloc)%Z -> client_keeps FL CL (bv_unsigned sp) a).
    { intros a Ha. right; left. subst CL. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply (agrees_rw_cells _ _ _ _ _ AGm) in HBS; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGm) in HPV; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGm) in HMB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGm) in HBUF; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INB; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGm) in HCUR; [| intros a Ha; rewrite Hccs in Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGm) in HEB;
      [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; destruct EBM as [(OEB & _)|EBP];
         [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL (incl_refl _))| lia] | apply INP; lia]].
    assert (HDL : rb_handle p p s P B m3).
    { unfold rb_handle, blk_handle. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs; split; assumption|]. split; [exact LENB|].
      do 5 (split; [reflexivity|]). unfold same_meta. repeat split. }
    assert (CTX : rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA (pc_self p) (pc_rfile p) m).
    { unfold rb_ctx, READ_BLOCK_STACK, PCAP_L1_STACK. split; [exact LO|]. split; [exact BU|]. split; [exact SPT|]. split; [exact TPE|]. split; [exact ALN|].
      split; [split; [exact RSTK| split; [exact RIMG| split; [exact RISH| exact RTLS]]]|].
      split; [exact UC|]. split; [exact TR|]. split; [exact NF|]. split; [exact HinF|]. split; [exact HinP|]. split; [exact CURS|]. split; [exact CUR8|].
      split. { destruct EBM as [(OEB & D1 & D2 & _)|EBP]; [left; split; [exact OEB| split; [exact D1| exact D2]]| right; exact EBP]. }
      split; [exact EB8|]. split; [exact SPAB| exact SPA32]. }
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs _ _ [_; _; _] 32 _ [_] [8; 8; 16]%nat) in FRC; [|reflexivity]. cbn [mk_CB_cells app] in FRC.
    lazymatch type of FRC with rw_cells _ _ _ [_; _; _; CB _ ?l0; CB _ ?l1; CB _ ?l2; _] =>
      set (pre := l0) in FRC; set (bj := l1) in FRC; set (post := l2) in FRC; clearbody pre bj post end.
    destruct (rw_cells_cut _ _ _ 4 FRC) as [FRC1 T1]. clear FRC. cbn [firstn skipn cells_size csize Nat.add] in FRC1, T1.
    destruct (rw_cells_cut _ _ _ 1 T1) as [HBJ FRC3]. clear T1. cbn [firstn skipn cells_size csize Nat.add] in HBJ, FRC3.
    lazymatch type of HBJ with rw_cells _ _ ?A _ => replace A with (Fb + 32)%Z in HBJ, FRC3 by lia end.
    lazymatch type of FRC3 with rw_cells _ _ ?A _ => replace A with (Fb + 40)%Z in FRC3 by lia end.
    assert (INV : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb (ps_outfile st) m RNG s1' (pc_buffer p) B (pc_bufalloc p) m3).
    { unfold rb_inv. split; [apply fp_le_refl|]. split; [exact G2|]. split; [exact OF1|]. split; [assumption|]. split; [assumption|]. split; [exact STG|]. split; [exact FR|].
      split. { eapply agrees_on_weaken; [exact AGm|]. intros a (K & _).
               destruct K as [K|[K|[K|K]]]; [left; exact K| right; left; subst CL; apply in_block_app; left; exact K| right; right; left; exact K| right; right; right; exact K]. }
      split; [eexists _, _, _, pre; exact FRC1|]. split; [exists post; exact FRC3|]. exact SHC. }
    assert (AGS : agrees_on (fun a => (bv_unsigned sp <= a)%Z) m m3) by (eapply agrees_on_weaken; [exact AGm|]; intros a Ha; left; exact Ha).
    (* [comment removed for export] *)
    apply evtF_done. subst POSTQ1 POSTQ.
    eapply (rb_rdhdr HO FO sites GIOA TP fflagA GL HAL GPL FRET FREAD FERROR SNPRINTF FMT REALLOC RPC) with (p := p) (s := s) (i := i) (B := B) (ccs := ccs) (site := site) (bj := bj);
      [ exact CTX | exact INV | exact FRW | exact HDL | exact HBJ | exact HEB | exact HCUR | exact Hccs | reflexivity | exact PRV | reflexivity | exact SITEQ | exact MBXs | exact AGS ].
  Qed.
  End Sz1.
  Theorem read_block_proofA : ltac:(let t := eval cbv delta [read_block_proofA__stmt] in read_block_proofA__stmt in exact t).
  Proof using GL HAL GPL FENTER0 FRET FREAD FERROR SNPRINTF FMT REALLOC RPC. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG st C1 C2 FB FL trC f Af P B CUR EB lo p s i a_bhdr bs ej ccs. ltac2:(SecDiet.SzSec.closeP 'read_block_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbMain.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngblk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_psegA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_ngblk_rdA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac plia_comp := first [ once ltac2:(LiaRel.lr_prune_sub ()); lia_tiers | once ltac2:(LiaRel.lr_prune_hub 5); lia_tiers
                              | once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); lia_tiers ].
Local Ltac own_iv1 ::=
  unfold own_ivA, iv_in_block, iv_in_frames, iv_in_frame_shadow;
  first [ left; cbn [fst snd]; atop_facts; plia_comp
        | right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; atop_facts; plia_comp
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; atop_facts; plia_comp
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; atop_facts; plia_comp
        | first [ left; cbn [fst snd]; lia
                | right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia
                | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; lia
                | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
                  cbn [cb_addr cb_size fst snd]; lia ] ].
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section RbMain.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FENTER0 : fenter_stmt_o FO GIOA fflagA 0 STACK_MALLOC_0.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.

  Definition read_block_proofA__stmt : Prop := read_block_stmt HO FO sites GIOA TP.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG st C1 C2 FB FL trC f Af P B CUR EB lo p s i a_bhdr bs ej ccs : ltac2:(SecDiet.SzSec.tyM 'read_block_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma read_block_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'read_block_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FENTER0 FRET FREAD FERROR SNPRINTF FMT REALLOC RPC.
 intros PRE UC TR NF HinF RF PRV HinP SITE -> -> -> -> BH HBUF PFX LENB HCUR Hccs CURS CUR8 HEB EBM EB8.
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    destruct SITE as (site & -> & SITEQ).
    subst f.
    assert (MBXs : (ng_max_blocksize s < 2^29 - 2^16)%Z) by (destruct BH as (_ & _ & _ & _ & WMBx & _); lia).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (HDLm : hidc (rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] /\ rw_cells asegs m CUR ccs /\ rw_cells asegs m EB [CB 256 ej]))
      by (split; [exact HBUF| split; [exact HCUR| exact HEB]]).
    clear HBUF HCUR HEB.
    (* [comment removed for export] *)
    set (bq := pc_buffer p) in *. set (alloc := pc_bufalloc p) in *.
    assert (PERM : Permutation.Permutation (C1 ++ (bq, B, alloc) :: C2) ((C1 ++ C2) ++ [(bq, B, alloc)])).
    { eapply Permutation.perm_trans; [apply Permutation.Permutation_sym, Permutation.Permutation_middle| apply Permutation.Permutation_cons_append]. }
    apply (GPL _ _ _ _ _ _ _ _ G) in PERM. clear G. rename PERM into G.
    set (CL := ((C1 ++ C2) ++ [(bq, B, alloc)])%list) in *.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & SUA & _) & GSU). unfold GOT_UAR in GSU.
    unfold READ_BLOCK_STACK, PCAP_L1_STACK in BU.
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    rewrite (read_block_eqA HO FO sites). cbn [e_fenter prims]. unfold READ_BLOCK_ENTRY.
    remember (bv_unsigned sp - 192 - (bv_unsigned sp - 192) mod 32)%Z as SPA eqn:ESPA.
    assert (SPAP : (bv_unsigned sp - 208 <= SPA <= bv_unsigned sp - 192 /\ SPA mod 32 = 0 /\ (bv_unsigned sp + -192) - (bv_unsigned sp + -192) mod 32 = SPA)%Z)
      by (rewrite ESPA; Z.div_mod_to_equations; lia).
    destruct SPAP as (SPAB & SPA32 & ESPA').
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    (* [comment removed for export] *)
    zstep.
    carve_frame 104%nat ST. carve_frame 88%nat ST.
    zstep.
    do 13 zstep.
    zstep.
    zstep.
    rewrite land_m32B by lia. rewrite ESPA'.
    release_frame FR0 ST (bv_unsigned sp + -104)%Z.
    destruct (stk_split asegs _ lo (SPA + 88) (bv_unsigned sp + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPA + 88) 88 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 88) with 88%Z in STL, FRA. replace (SPA + 88 - 88)%Z with SPA in STL, FRA by lia.
    destruct (spill_words11 _ _ _ FRA) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & FRW). clear FRA.
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    (* [comment removed for export] *)
    do 6 zstep.
    do 2 zstep.
    zstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    zstep.
    zstep.
    zstep. if_false.
    do 2 zstep.
    (* [comment removed for export] *)
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FWS : Forall (client_ivA FL CL) [(bv_unsigned sp - 208, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG st CL FB FL mm) by (eapply (gl_client_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FWS]);
      assert (AGa : agrees_on (client_keeps FL CL (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ CL [] _ FL []); [exact G' | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    rename MU into MU0. rename WM into WM0. clear FWS G'.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FENTER0 _ spa).
    { split; [exact G0|]. rewrite Hspa. split; [exact STL|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [Z.div_mod_to_equations; lia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { apply NF. left. reflexivity. }
    { reflexivity. }
    intros Fb s1' m2 j0 j1 j2 fjunk t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G1 OF1 LC1 TL1 MI1 ST1 AG1 Fb0 LJ FRC SHC.
    rewrite Hspa in *. clear Hspa. subst spa.
    change (ff_size FF_READ_BLOCK) with 64%Z in *.
    change (Z.to_nat (64 - 32)) with 32%nat in *. change (Z.to_nat (64 / 8)) with 8%nat in *.
    apply sh_zero_cells in SHC. cbn [repeat] in SHC.
    replace (ret_pc (Z_to_bv 64 572268)) with (Z_to_bv 64 572268) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G1) as [FAll FND]. pose proof (Forall_inv FAll) as FRM. pose proof FRM as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR).
    cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll.
    change (Z.shiftr 64 3) with 8%Z in FSRNG, FSWR.
    band_ind FBAND' bF.
    (* [comment removed for export] *)
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FRW; [|lia].
    apply (agrees_stk _ _ _ _ _ AG1) in STG; [|intros a Ha; left; lia].
    assert (AGb : agrees_on (client_keeps FL CL (bv_unsigned sp)) m m2).
    { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; exact Ha| apply incl_refl]. }
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000)%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    destruct SHLO as (SLO & SHI).
    assert (HinP' : In (pc_self p, P, PCAP_NG_SF_TOTAL) (CL ++ FB)) by (apply in_or_app; left; subst CL; apply in_or_app; left; exact HinP).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G1 HinP') as ((PBAND & _) & _). cbn [cb_addr cb_size fst snd] in PBAND. unfold PCAP_NG_SF_TOTAL in PBAND.
    pose proof (ablk_lin _ _ PBAND) as (_ & P0 & _ & PHI).
    clear AGa AG1 G0 MU0 WM0 MI STL GOT SHB SUA GSU.
    pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z m2) as MU.
    pose proof (wmono_refl asegs m2) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ1 := Q) end. apply implMG_from_evtF.
    (* [comment removed for export] *)
    pose proof PBAND as PBAND'. band_ind PBAND' bP.
    call rb_poison_seq; [try eassumption .. | ]; [lia .. | ].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
    lazymatch goal with HH : rw_cells asegs m3 Fb _ |- _ => rename HH into FRC end.
    lazymatch goal with HH : rw_cells asegs m3 (Z.shiftr Fb 3 + 2147450880)%Z _ |- _ => rename HH into SHC end.
    lazymatch goal with HH : rw_cells asegs m3 SPA _ |- _ => rename HH into FRW end.
    (* [comment removed for export] *)
    assert (G1n : GIOA L RNG s1' (CL ++ []) FB ([(FF_READ_BLOCK, Fb, 64%Z)] ++ FL) m2) by (rewrite app_nil_r; exact G1).
    assert (FW : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(bv_unsigned sp - 208, bv_unsigned sp); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z) by own_ivs.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ m3 _ [] _ FW (Forall_nil _) G1n MU WM ltac:(lia)) as [G2 AG2].
    rewrite app_nil_r in G2. cbn [app] in G2.
    assert (AGm : agrees_on (client_keeps FL CL (bv_unsigned sp)) m m3).
    { eapply agrees_on_trans; [exact AGb|]. eapply agrees_on_weaken; [exact AG2|]. intros a K. split; [exact K| exact I]. }
    unfold hidc in HDLm. destruct HDLm as (HBUF & HCUR & HEB).
    destruct BH as (HBS & HPV & HMB & WBS & WMB & WBA & BSA).
    assert (ICL : incl (C1 ++ C2) CL) by (subst CL; apply incl_appl, incl_refl).
    assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps FL CL (bv_unsigned sp) a).
    { intros a Ha. right; left. subst CL. apply in_block_app. left. apply in_block_In. exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
      cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (INB : forall a, (B <= a < B + alloc)%Z -> client_keeps FL CL (bv_unsigned sp) a).
    { intros a Ha. right; left. subst CL. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply (agrees_rw_cells _ _ _ _ _ AGm) in HBS; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGm) in HPV; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGm) in HMB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGm) in HBUF; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INB; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGm) in HCUR; [| intros a Ha; rewrite Hccs in Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGm) in HEB;
      [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; destruct EBM as [(OEB & _)|EBP];
         [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL (incl_refl _))| lia] | apply INP; lia]].
    assert (HDL : rb_handle p p s P B m3).
    { unfold rb_handle, blk_handle. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs; split; assumption|]. split; [exact LENB|].
      do 5 (split; [reflexivity|]). unfold same_meta. repeat split. }
    assert (CTX : rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA (pc_self p) (pc_rfile p) m).
    { unfold rb_ctx, READ_BLOCK_STACK, PCAP_L1_STACK. split; [exact LO|]. split; [exact BU|]. split; [exact SPT|]. split; [exact TPE|]. split; [exact ALN|].
      split; [split; [exact RSTK| split; [exact RIMG| split; [exact RISH| exact RTLS]]]|].
      split; [exact UC|]. split; [exact TR|]. split; [exact NF|]. split; [exact HinF|]. split; [exact HinP|]. split; [exact CURS|]. split; [exact CUR8|].
      split. { destruct EBM as [(OEB & D1 & D2 & _)|EBP]; [left; split; [exact OEB| split; [exact D1| exact D2]]| right; exact EBP]. }
      split; [exact EB8|]. split; [exact SPAB| exact SPA32]. }
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs _ _ [_; _; _] 32 _ [_] [8; 8; 16]%nat) in FRC; [|reflexivity]. cbn [mk_CB_cells app] in FRC.
    lazymatch type of FRC with rw_cells _ _ _ [_; _; _; CB _ ?l0; CB _ ?l1; CB _ ?l2; _] =>
      set (pre := l0) in FRC; set (bj := l1) in FRC; set (post := l2) in FRC; clearbody pre bj post end.
    destruct (rw_cells_cut _ _ _ 4 FRC) as [FRC1 T1]. clear FRC. cbn [firstn skipn cells_size csize Nat.add] in FRC1, T1.
    destruct (rw_cells_cut _ _ _ 1 T1) as [HBJ FRC3]. clear T1. cbn [firstn skipn cells_size csize Nat.add] in HBJ, FRC3.
    lazymatch type of HBJ with rw_cells _ _ ?A _ => replace A with (Fb + 32)%Z in HBJ, FRC3 by lia end.
    lazymatch type of FRC3 with rw_cells _ _ ?A _ => replace A with (Fb + 40)%Z in FRC3 by lia end.
    assert (INV : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb (ps_outfile st) m RNG s1' (pc_buffer p) B (pc_bufalloc p) m3).
    { unfold rb_inv. split; [apply fp_le_refl|]. split; [exact G2|]. split; [exact OF1|]. split; [assumption|]. split; [assumption|]. split; [exact STG|]. split; [exact FR|].
      split. { eapply agrees_on_weaken; [exact AGm|]. intros a (K & _).
               destruct K as [K|[K|[K|K]]]; [left; exact K| right; left; subst CL; apply in_block_app; left; exact K| right; right; left; exact K| right; right; right; exact K]. }
      split; [eexists _, _, _, pre; exact FRC1|]. split; [exists post; exact FRC3|]. exact SHC. }
    assert (AGS : agrees_on (fun a => (bv_unsigned sp <= a)%Z) m m3) by (eapply agrees_on_weaken; [exact AGm|]; intros a Ha; left; exact Ha).
    (* [comment removed for export] *)
    apply evtF_done. subst POSTQ1 POSTQ.
    eapply (rb_rdhdr HO FO sites GIOA TP fflagA GL HAL GPL FRET FREAD FERROR SNPRINTF FMT REALLOC RPC) with (p := p) (s := s) (i := i) (B := B) (ccs := ccs) (site := site) (bj := bj);
      [ exact CTX | exact INV | exact FRW | exact HDL | exact HBJ | exact HEB | exact HCUR | exact Hccs | reflexivity | exact PRV | reflexivity | exact SITEQ | exact MBXs | exact AGS ].
  Qed.
  End Sz1.
  Theorem read_block_proofA : ltac:(let t := eval cbv delta [read_block_proofA__stmt] in read_block_proofA__stmt in exact t).
  Proof using GL HAL GPL FENTER0 FRET FREAD FERROR SNPRINTF FMT REALLOC RPC. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG st C1 C2 FB FL trC f Af P B CUR EB lo p s i a_bhdr bs ej ccs. ltac2:(SecDiet.SzSec.closeP 'read_block_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbMain.
End CANSEC1.
End TwB.
End F_ngblk_mainA.
