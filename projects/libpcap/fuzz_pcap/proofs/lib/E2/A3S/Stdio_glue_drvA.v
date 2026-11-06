(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw ExecF ITreeA Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABase AMalloc_iface RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PcapRepA Pcap_ifaceA Fuzz_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Import Drv_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_fwrite. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fread_top__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fopen__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_mkstemp__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fwrite_top Printf_fmtA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Vfprintf_leafA Stdio_repA Stdio_glueKitA StdioLawsA Stdio_glueA Stdio_glue_snA Stdio_glue_pfA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_fwrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.Printf_fsink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.F_vfprintf_file OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_words OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_mkstemp__A3S.I_snprintf_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.I_fprintf_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.I_printf_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fwrite_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_fmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.Printf_pitems OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Vfprintf_leafA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_snA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_pfA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sbl_is_big n := lazymatch n with S _ => let b := eval vm_compute in (Nat.leb 200 n) in lazymatch b with true => idtac end end.
Local Ltac sbl_pose_in H :=
  (let T := type of H in let T' := eval hnf in T in change T' in H);
  repeat match type of H with
  | context [repeat ?b ?n] => sbl_is_big n; let z := fresh "sblz" in pose (z := repeat b n); change (repeat b n) with z in H
  | context [CB ?n _] => sbl_is_big n; let x := fresh "sblv" in pose (x := n); change n with x in H
  end.
Local Ltac sbl_subst_all :=
  repeat match goal with
  | z := repeat _ ?n |- _ => sbl_is_big n; subst z
  | x := ?n |- _ => sbl_is_big n; subst x
  end.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithRc. Context {rc : runConstT}.
Definition fmt_call_okD (FMT : Z) (fs : string) (args : list farg) (pargs : list parg) (ps : list (list Z)) : Prop :=
  Forall (fun c => 0 <= c < 256) (str fs ++ [0]) /\ pass1_ok (str fs ++ [0]) = true
  /\ printf_pieces (str fs ++ [0]) pargs = Some (ps, zlength (fmt_output (fmt fs) args)) /\ pieces_small ps
  /\ (65536 <= FMT /\ FMT + zlength (str fs ++ [0]) <= 204800)
  /\ (forall m, mem_inv asegs m -> bytes_at asegs m FMT (zb (str fs ++ [0])))
  /\ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true.

#[using="Type"] Lemma fmt_call_okD_intro : forall fs FMT args,
  fmt_staticA fs FMT -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> (length args <= 2)%nat ->
  Forall (fun a => farg_len a <= 2^24) args -> zlength (str fs) < 4096 ->
  fmt_call_okD FMT fs args (to_pargs (fmt fs) args) (fmt_pieces (fmt fs) args).
Proof.
  intros fs FMT args FS OK L2 SM FL.
  destruct (fmt_facts fs args OK L2 SM FL) as (HF & P1 & PIECES & SMALL & RB).
  pose proof FS as (RO & LO & HI).
  split; [exact HF|]. split; [exact P1|]. split; [exact PIECES|]. split; [exact SMALL|].
  split; [split; [exact LO| exact HI]|]. split; [intros m MI; exact (fmt_bytesA m fs FMT MI FS) | exact OK].
Qed.
End WithRc.

Local Close Scope string_scope.

Local Ltac fmt_callD :=
  apply fmt_call_okD_intro;
    [ split; [vm_compute; reflexivity | vm_compute; split; intros HH; discriminate HH]
    | vm_compute; reflexivity
    | cbn [length]; Lia.lia
    | repeat constructor; cbn [farg_len]; try assumption; try Lia.lia
    | vm_compute; reflexivity ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Open Scope string_scope.
Definition FS_EMIT_D : string := "%d
".
Definition FS_USAGE : string := "usage: %s INPUT
".
Definition FS_CANNOT_OPEN : string := "cli: cannot open %s
".
Definition FS_READ_ERROR : string := "cli: read error on %s
".
Definition FS_TOO_BIG : string := "cli: input >= %u bytes, refused
".
Local Close Scope string_scope.

Section WithRc2. Context {rc : runConstT}.
#[using="Type"] Lemma call_emit_dD : forall v, fmt_call_okD FMT_D FS_EMIT_D [AInt v] [PA_i (s32 v)] (pieces_emit_d v).
Proof. intros v. fmt_callD. Qed.
#[using="Type"] Lemma call_usageD : forall s, zlength s <= 2^24 -> fmt_call_okD FMT_USAGE FS_USAGE [AStr s] [PA_s s] (pieces_usage s).
Proof. intros s Hs. fmt_callD. Qed.
#[using="Type"] Lemma call_cannot_openD : forall s, zlength s <= 2^24 -> fmt_call_okD FMT_CANNOT_OPEN FS_CANNOT_OPEN [AStr s] [PA_s s] (pieces_cannot_open s).
Proof. intros s Hs. fmt_callD. Qed.
#[using="Type"] Lemma call_read_errorD : forall s, zlength s <= 2^24 -> fmt_call_okD FMT_READ_ERROR FS_READ_ERROR [AStr s] [PA_s s] (pieces_read_error s).
Proof. intros s Hs. fmt_callD. Qed.
#[using="Type"] Lemma call_too_bigD : fmt_call_okD FMT_TOO_BIG FS_TOO_BIG [AInt 0x4000000] [PA_u (u32 0x4000000)] pieces_too_big.
Proof. fmt_callD. Qed.
End WithRc2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section GlueDrv.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vprintf_d_proofA__stmt : Prop := vprintf_d_stmt_o GIOA.
  Section Sz7.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo AP v rest : ltac2:(SecDiet.SzSec.tyM 'vprintf_d_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma vprintf_d_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'vprintf_d_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
 intros SPO -> -> HV MOF APC APLO APHI.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & _ & _ & (RSTKF & _ & RIMGSH & _)).
    pose proof (spo_factsA GIOA GSL _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK in *.
    sbl_pose_in SO. destruct SO as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    pose proof SOI as (CH1 & FD1 & BS1 & NRD1 & NWR1 & EOF1 & RB1 & LBF1).
    pose proof (call_emit_dD v) as (HF & P1 & PIECES & SMALL & HA & BYf & IOK).
    pose proof (s32_facts v) as [S32a S32b].
    rewrite BS1 in FC, BUF, WBL. unfold BUFSIZ in FC, BUF, WBL.
    pose proof (rw_cells_bound _ _ _ _ APC) as APB. cbn [cells_size csize Nat.add] in APB.
    apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in APC. destruct APC as [APC _].
    destruct (pitems_facts FS_EMIT_D [AInt v] [Z_to_bv 64 v] IOK eq_refl) as (FSTR & NOZ & EF & OKI).
    assert (RVA : rng RNG AP 8) by (eapply rng_sub'; [exact RSTKF | lia]).
    assert (PW : pargs_okL RNG lo sp m (pitems FS_EMIT_D [AInt v] [Z_to_bv 64 v]) (Z_to_bv 64 AP)).
    { apply (pargs_okL_of_words RNG lo sp m _ [Z_to_bv 64 v] AP); [| exact APC | exact APLO | cbn [length]; lia | exact RVA].
      apply pitems_words_fs; [exact IOK | apply Forall2_cons; [exact I | apply Forall2_nil]]. }
    destruct (gs_statics _ GSL _ _ _ _ _ _ _ G RIMG RIMGSH) as [SOS1 SOS2].
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL.
    assert (EZ : zlength (str FS_EMIT_D ++ [0]) = 4) by (vm_compute; reflexivity).
    assert (SOFMT : sobj RNG m FMT_D (FMT_D + zlength (str FS_EMIT_D ++ [0]))) by (rewrite EZ; apply mobjA_sobj; [exact MOF | lia]).
    unfold printf. apply implMG_rd_lc.
    eapply implMG_bind.
    { eapply implMG_leaf. apply implAM_implMG. unfold VPRINTF_ENTRY.
      eapply (vprintf_i_spec (St:=PS) RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail FMT_D AP lo
                (str FS_EMIT_D ++ [0]) [Z_to_bv 64 v] [PA_i (s32 v)] (pieces_emit_d v) _ canary (zb (str FS_EMIT_D)) (pitems FS_EMIT_D [AInt v] [Z_to_bv 64 v]) true true)
        with (rpos := rp) (rend := rp + zlength (f_rbuf (lc_stdout (ps_libc s)))) (flags := flags) (mode := mode) (bufbytes := bufbytes).
      all: match goal with |- ?g => first
             [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact KLO | exact RSTK | exact RIMG | exact FSTR | exact NOZ | exact EF | exact OKI
             | reflexivity | exact FC | exact FLG | exact BUF | exact BP | exact WB0
             | exact BS1 | exact WBL | exact NWR1 | exact RB1
             | (rewrite CH1; left; exact FD1) | exact CH1 | (intros _; reflexivity)
             | (apply BYf; exact MI)
             | (apply va_area_of_cells; exact APC)
             | (cbn [args_ok]; split; [split; [exact S32a | exact S32b] | exact I])
             | exact ST | exact SSP | exact MI | exact ENV | exact (gs_ckpf _ GSL _ _ _ _ _ _ _ G) | exact PW
             | (apply (gs_stack _ GSL _ _ _ _ _ _ _ lo (bv_unsigned sp) G); (keep_hyps rc lo AP v LOA sp LOB L SPT APLO APHI TOP47; lia))
             | exact SOFMT | exact RVA
             | (apply (gs_rodata _ GSL _ _ _ _ _ _ _ 68460 68469 G RIMG RIMGSH); [left; (keep_hyps rc AP v; lia) | (keep_hyps rc AP v; lia)])
             | (eapply sobj_sub; [exact SOS1 | unfold A_STDOUT; (keep_hyps rc lo AP v GLO; lia) | (keep_hyps rc AP v; lia) | unfold A_STDOUT; (keep_hyps rc AP v; lia)])
             | (eapply sobj_sub; [exact SOS2 | unfold A_STDOUT_BUF; (keep_hyps rc lo AP v GLO; lia) | (keep_hyps rc AP v; lia) | unfold A_STDOUT_BUF; (keep_hyps rc AP v; lia)])
             | (eapply rng_sub'; [exact RIMG | unfold A_STDOUT_BUF; lia])
             | (cbv [zlength Datatypes.length Z.of_nat Pos.of_succ_nat Pos.succ]; unfold VPRINTF_I_DEPTH, GLOBALS_TOP in *; (keep_hyps rc sp lo AP v LOB GLO L APLO APHI TOP47; lia))
             | idtac "VPD-LEFT:" g ] end. }
    cbv beta. intros f' st' RNG' ms' [(-> & PO) LF].
    sbl_pose_in PO. destruct PO as (-> & INV' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & flags' & mode' & bufbytes' & m' & rpos' & rend'
                     & -> & MU & WM & MI' & ST' & SSP' & FC' & RP' & FL' & BUF' & BP' & WBL'). sbl_subst_all.
    assert (BSnz : f_bufsize (lc_stdout (ps_libc s)) <> 0) by (rewrite BS1; unfold BUFSIZ; lia).
    pose proof (vfprintf_leaf_buffered _ _ _ _ _ BSnz LF) as [FX _].
    pose proof (vfprintf_leaf_buffered_wl _ _ _ _ _ BSnz LF) as WL.
    pose proof INV' as (WA' & RB' & BS' & NW' & FDC' & _ & CHN').
    rewrite RB1 in RP1. change (zlength (@nil Z)) with 0 in RP1.
    assert (FR' : FILE_R m' f' A_STDOUT A_STDOUT_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0).
    { exists flags', mode', rpos', tail, bufbytes'.
      rewrite WA', RB', BS'. change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
      assert (Erend : rend' = rpos') by (rewrite RB1 in RP'; change (zlength (@nil Z)) with 0 in RP'; lia).
      rewrite Erend in FC'.
      split; [exact FC'|]. split; [exact FL'|]. split; [exact BUF'|]. split; [exact BP'|]. split; [intros X; discriminate X|]. split; [exact WBL'|].
      split; [intros X; exfalso; exact (X eq_refl)|]. split; [lia|]. split; [lia| exact GLN]. }
    assert (SOI' : stdout_inv f').
    { pose proof FX as (E1 & E2 & E3 & E4 & E5 & E6 & _ & _ & SW' & LB').
      unfold stdout_inv. rewrite E1, E2, E4, E5, E6.
      split; [exact CH1|]. split; [exact FD1|]. split; [exact BS'|]. split; [exact NRD1|]. split; [exact NWR1|]. split; [exact EOF1|]. split; [exact RB'|].
      destruct WL as [[W1 W2]|[W1 W2]]; rewrite W1, ?W2; [exact LBF1| intros X; discriminate X]. }
    destruct (GIOA_stdout_step FO GIOA fflagA GL GSL L RNG s CL FB FL m m' f' lo (bv_unsigned sp) G LOA ltac:(lia) MU WM FR' SOI') as [G' AG].
    unfold upd_lc. apply implMG_upd. apply evtF_done. unfold out_post_o.
    split; [apply fp_le_refl|].
    exists a0', m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. exact G'.
  Qed.
  End Sz7.
  Theorem vprintf_d_proofA : ltac:(let t := eval cbv delta [vprintf_d_proofA__stmt] in vprintf_d_proofA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo AP v rest. ltac2:(SecDiet.SzSec.closeP 'vprintf_d_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition spd_factsA__stmt : Prop := forall L RNG sp tp (s : PS) CL FB FL lo budget m,
    std_pre_d GIOA L RNG sp tp s CL FB FL lo budget m ->
    GIOA L RNG s CL FB FL m /\ STDIOR (ps_libc s) FB m /\ stk asegs m lo (bv_unsigned sp) /\ mem_inv asegs m
    /\ (exists canary, ssp_cells m canary) /\ icptenv m
    /\ ATOP + 4096 <= lo /\ lo + budget <= bv_unsigned sp /\ bv_unsigned sp < 2^47 /\ al_top L <= 2^47
    /\ tp = Z_to_bv 64 ATP
    /\ rng RNG lo (bv_unsigned sp - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG /\ KHIGH <= lo /\ 0x603000 <= lo.
  Section Sz8.
  Variables L RNG sp tp s CL FB FL lo budget m : ltac2:(SecDiet.SzSec.tyM 'spd_factsA__stmt "vvvvvvvvvvv" @L).
  Lemma spd_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'spd_factsA__stmt "vvvvvvvvvvv").
  Proof using GSL. pin_using (fun (GSL : unit) => tt).
    intros (G & ST & LOA & LOB & (SPT & TOP47) & MI & Etp & SPAL & (RSTKT & RSTK & RIMG & RIMGSH & RTLS)).
    pose proof (@ATOP_lo rc) as AL. pose proof (@ATOP_hi rc) as AH.
    split; [exact G|]. split; [exact (gs_stdio _ GSL _ _ _ _ _ _ _ G)|]. split; [exact ST|]. split; [exact MI|].
    split; [destruct (gs_ssp _ GSL L) as [canL SSPL]; exists canL; exact (SSPL _ _ _ _ _ _ G)|]. split; [exact (gs_env _ GSL _ _ _ _ _ _ _ G)|].
    split; [exact LOA|]. split; [exact LOB|]. split; [exact SPT|]. split; [exact TOP47|]. split; [exact Etp|].
    split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RIMGSH|]. split; [exact RTLS|].
    unfold KHIGH. split; lia.
  Qed.
  End Sz8.
  Lemma spd_factsA : ltac:(let t := eval cbv delta [spd_factsA__stmt] in spd_factsA__stmt in exact t).
  Proof using GSL. intros L RNG sp tp s CL FB FL lo budget m. ltac2:(SecDiet.SzSec.closeP 'spd_factsA__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition keeps_lowD__stmt : Prop := forall L RNG (s : PS) CL FB FL m SP a,
    GIOA L RNG s CL FB FL m -> client_keeps FL CL SP a -> a < SP -> 0x603000 <= a < ATOP.
  Section Sz9.
  Variables L RNG s CL FB FL m SP a : ltac2:(SecDiet.SzSec.tyM 'keeps_lowD__stmt "vvvvvvvvv" @L).
  Lemma keeps_lowD__body : ltac2:(SecDiet.SzSec.bodyP 'keeps_lowD__stmt "vvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G KEEP LT.
    pose proof (@ATOP_lo rc) as ATL.
    destruct KEEP as [X|[X|[X|X]]]; [lia| | |].
    - pose proof (gia_in_block_below FO GIOA fflagA GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; exact X)) as [B0 B1].
      apply in_block_In in X as (b & Hb & Hr).
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; exact Hb)) as ((ABLK & _) & _).
      unfold ablk, AIMG_HI, KLS in ABLK. lia.
    - pose proof (gia_in_frames_below FO GIOA fflagA GL _ _ _ _ _ _ _ a G X) as [B0 B1].
      apply in_frames_In in X as (fr & Hf & Hr).
      destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr Hf) as (BAND & _).
      unfold ablk, AIMG_HI, KLS in BAND. lia.
    - pose proof (gia_in_frame_sh_band FO GIOA fflagA GL _ _ _ _ _ _ _ a G X) as [B0 B1]. lia.
  Qed.
  End Sz9.
  Lemma keeps_lowD : ltac:(let t := eval cbv delta [keeps_lowD__stmt] in keeps_lowD__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m SP a. ltac2:(SecDiet.SzSec.closeP 'keeps_lowD__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition GIOA_stderr_step__stmt : Prop := forall L RNG (s : PS) CL FB FL m m' (f' : file_st) lo SP,
    GIOA L RNG s CL FB FL m -> ATOP + 4096 <= lo -> lo <= SP ->
    munch [(lo, SP); (A_STDERR, A_STDERR + 232); (A_STDERR_BUF, A_STDERR_BUF + 0)] m m' -> wmono asegs m m' ->
    FILE_R m' f' A_STDERR A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 -> stderr_inv f' ->
    GIOA L RNG (set_libc (set_stderr f' (ps_libc s)) s) CL FB FL m' /\ agrees_on (client_keeps FL CL SP) m m'.
  Section Sz10.
  Variables L RNG s CL FB FL m m' f' lo SP : ltac2:(SecDiet.SzSec.tyM 'GIOA_stderr_step__stmt "vvvvvvvvvvv" @L).
  Lemma GIOA_stderr_step__body : ltac2:(SecDiet.SzSec.bodyP 'GIOA_stderr_step__stmt "vvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros G LOA LOSP MU WM FR' INV'.
    pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G) as SR.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof (@ATOP_lo rc) as ATL.
    unfold A_STDERR, A_STDERR_BUF in MU.
    assert (HW : Forall (stdio_ivA FB SP) [(lo, SP); (694960, 694960 + 232); (6298816, 6298816 + 0)]).
    { unfold stdio_ivA. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd];
        [left; lia | right; right; left; lia | right; right; right; left; lia]. }
    rewrite <- (app_nil_r [(lo, SP); (694960, 694960 + 232); (6298816, 6298816 + 0)]) in MU.
    split.
    2:{ eapply agrees_on_weaken; [eapply (gs_keeps _ GSL L RNG s CL FB FL m m' _ [] SP); [exact G| exact MU| exact WM| exact HW| lia]|].
        intros a Ha. split; [exact Ha | exact I]. }
    eapply (gs_step _ GSL L RNG s CL FB FL m m' _ [] SP); [exact G| exact MU| exact WM| exact HW| apply Forall_nil| lia| |].
    { eapply (errno_cell_kept FO GIOA fflagA GL GSL L RNG s CL FB FL m m' _ [] SP); [exact G| exact MU| exact WM| | apply Forall_nil].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd];
        [left; lia | right; right; left; lia | right; right; right; lia]. }
    rewrite app_nil_r in MU.
    unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_stderr].
    assert (AG : agrees_on (fun a => outside [(lo, SP); (694960, 694960 + 232); (6298816, 6298816 + 0)] a) m m').
    { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hs. exact Hs. }
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    pose proof SOI as (_ & _ & SObs & _).
    split. { eapply FILE_R_agree; [exact SO | exact AG | intros a Ha; cbn [outside]; lia | rewrite SObs; unfold BUFSIZ; intros a Ha; cbn [outside]; lia]. }
    split; [exact SOI|].
    split; [exact FR'|]. split; [exact INV'|].
    split. { eapply agrees_rw_cells; [exact AG | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; cbn [outside]; lia. }
    split; [eapply agrees_rw_cells; [exact AG | exact U1 | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [eapply agrees_rw_cells; [exact AG | exact U2 | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [eapply agrees_rw_cells; [exact AG | exact U3 | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [eapply agrees_rw_cells; [exact AG | exact OL | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [eapply agrees_rw_cells; [exact AG | exact OH | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [| exact ND].
    eapply files_R_agree; [exact FS | exact AG |]. intros a Ha. pose proof (in_block_FB_range FO GIOA fflagA GL _ _ _ _ _ _ _ _ G Ha) as R. cbn [outside]. lia.
  Qed.
  End Sz10.
  Lemma GIOA_stderr_step : ltac:(let t := eval cbv delta [GIOA_stderr_step__stmt] in GIOA_stderr_step__stmt in exact t).
  Proof using GL GSL. intros L RNG s CL FB FL m m' f' lo SP. ltac2:(SecDiet.SzSec.closeP 'GIOA_stderr_step__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition str_arg_factsD__stmt : Prop := forall L RNG (s : PS) CL FB FL m lo SP Fp FS B BS ap P (str slack : list byte),
    GIOA L RNG s CL FB FL m -> ATOP + 4096 <= lo -> lo < SP ->
    bytes_at asegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^24 ->
    (- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
    mobjA RNG m P (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) ->
    (forall a, P <= a < P + Z.of_nat (length str) + 1 -> client_keeps FL CL SP a) ->
    Fp + FS <= 0x603000 -> lo <= B -> B + BS <= SP -> lo <= ap -> ap + 8 <= SP ->
    arg_ok Fp FS B BS RNG m lo SP ap (Z_to_bv 64 P) (PA_s (map bv_unsigned str))
    /\ (forall sp : word, bv_unsigned sp = SP -> pword_ok RNG lo sp m (AStr (map bv_unsigned str)) (Z_to_bv 64 P)).
  Section Sz11.
  Variables L RNG s CL FB FL m lo SP Fp FS B BS ap P str slack : ltac2:(SecDiet.SzSec.tyM 'str_arg_factsD__stmt "vvvvvvvvvvvvvvvvv" @L).
  Lemma str_arg_factsD__body : ltac2:(SecDiet.SzSec.bodyP 'str_arg_factsD__stmt "vvvvvvvvvvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G LOA LOSP BY NZ LB PAD MOP KEEP DF DB1 DB2 DA1 DA2.
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    pose proof (pad8_range (P + Z.of_nat (length str) + 1)) as PR. unfold pad8 in PR.
    set (pd := (- (P + Z.of_nat (length str) + 1)) mod 8) in *.
    pose proof (@ATOP_lo rc) as ATL.
    assert (MOP' : mobjA RNG m P (Z.of_nat (length str) + 1 + pd)) by (eapply mobjA_sub; [exact MOP | lia | lia | lia]).
    pose proof MOP' as (P0 & P47 & _ & RGP & _ & _).
    pose proof (mobjA_sobj _ _ _ _ MOP' ltac:(lia)) as SOD.
    assert (EP : bv_unsigned (Z_to_bv 64 P : word) = P) by (apply unsigned_lit; lia).
    assert (SOS : sobj RNG m P (P + (Z.of_nat (length str) + 1))) by (eapply sobj_sub; [exact SOD | lia | lia | lia]).
    assert (NZF : Forall (fun b : byte => bv_unsigned b <> 0) str).
    { apply Forall_forall. intros b Hb E. apply NZ. replace (Z_to_bv 8 0) with b; [exact Hb|].
      rewrite <- (definitions.Z_to_bv_bv_unsigned 8 b), E. reflexivity. }
    (* [comment removed for export] *)
    assert (PLACE : SP <= P \/ (0x603000 <= P /\ P + (Z.of_nat (length str) + 1 + pd) <= lo)).
    { destruct (Z_le_gt_dec SP P) as [HSP|HSP]; [left; exact HSP | right].
      pose proof (keeps_lowD _ _ _ _ _ _ _ SP P G (KEEP P ltac:(lia)) ltac:(lia)) as [PL PH].
      split; [exact PL|].
      destruct (Z_lt_le_dec (P + Z.of_nat (length str)) SP) as [LT|GE].
      - pose proof (keeps_lowD _ _ _ _ _ _ _ SP (P + Z.of_nat (length str)) G (KEEP (P + Z.of_nat (length str)) ltac:(lia)) LT) as [_ EH]. lia.
      - exfalso. pose proof (keeps_lowD _ _ _ _ _ _ _ SP lo G (KEEP lo ltac:(lia)) LOSP) as [_ X]. lia. }
    split.
    - cbn [arg_ok]. rewrite EP. exists (firstn (Z.to_nat pd) slack).
      assert (LS : length (firstn (Z.to_nat pd) slack) = Z.to_nat pd) by (rewrite length_firstn; lia).
      unfold zlength. rewrite length_map, LS.
      split. { rewrite zb_unsigned. rewrite <- (firstn_skipn (Z.to_nat pd) slack) in BY.
               change (str ++ Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack ++ skipn (Z.to_nat pd) slack)
                 with (str ++ (Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack) ++ skipn (Z.to_nat pd) slack) in BY.
               rewrite app_assoc in BY. apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. exact (proj1 BY). }
      split. { apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & Hb).
               pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
               pose proof (proj1 (Forall_forall _ _) NZF b Hb) as Nb. cbv beta in Nb. lia. }
      split; [lia|]. split; [lia|].
      split; [destruct PLACE as [X|[X1 X2]]; [right; lia | left; lia]|].
      split; [right; destruct PLACE as [X|[X1 X2]]; lia|].
      split; [destruct PLACE as [X|[X1 X2]]; [right; lia | left; lia]|].
      split; [destruct PLACE as [X|[X1 X2]]; [right; lia | left; lia]|].
      split; [lia|].
      split; [eapply rng_sub'; [exact RGP | lia]|].
      replace (P + Z.of_nat (length str) + 1) with (P + (Z.of_nat (length str) + 1)) by lia. exact SOS.
    - intros sp ESP. cbn [pword_ok]. rewrite EP, zb_unsigned. unfold pstrL.
      split. { change (str ++ Z_to_bv 8 0 :: slack) with (str ++ [Z_to_bv 8 0] ++ slack) in BY. rewrite app_assoc in BY.
               apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. exact (proj1 BY). }
      split; [exact NZF|]. split; [destruct PLACE as [X|[X1 X2]]; [right; lia | left; lia]|]. split; [lia|]. split; [exact SOS|].
      eapply rng_sub'; [exact RGP | lia].
  Qed.
  End Sz11.
  Lemma str_arg_factsD : ltac:(let t := eval cbv delta [str_arg_factsD__stmt] in str_arg_factsD__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m lo SP Fp FS B BS ap P str slack. ltac2:(SecDiet.SzSec.closeP 'str_arg_factsD__body "vvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition stderr_after__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
        L RNG (s : PS) CL FB FL (m : mem) (lo : Z) (canary : word) (ps : list (list Z)) (tail bufbytes : list byte)
        (f' : file_st) (st' : PS) (ms' : machine_state),
      GIOA L RNG s CL FB FL m -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp ->
      firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8 ->
      rw_cells asegs m A_STDERR_BUF [CB 0 bufbytes] ->
      vfprintf_ubf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A_STDERR A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail lo canary
                        m s f' st' ms' ->
      mleaf (vfprintf (lc_stderr (ps_libc s)) ps) s f' st' ->
      st' = s /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
        /\ GIOA L RNG (set_libc (set_stderr f' (ps_libc s)) s) CL FB FL m'.
  Section Sz12.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL m lo canary ps tail bufbytes f' st' ms' : ltac2:(SecDiet.SzSec.tyM 'stderr_after__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma stderr_after__body : ltac2:(SecDiet.SzSec.bodyP 'stderr_after__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
 intros G LOA LOS GLN BUF PO LF.
    pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G) as SR.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof SEI as (CH2 & FD2 & BS2 & ND2 & NW2 & EOF2 & RB2 & SW2 & LB2).
    sbl_pose_in PO. destruct PO as (-> & WA' & WB' & RB' & BS' & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & flags' & mode' & m'
                     & -> & MU & WM & MI' & ST' & SSP' & FC' & FL'). sbl_subst_all.
    destruct (vfprintf_leaf_unbuffered _ _ _ _ _ BS2 LF) as [(E1 & E2 & E3 & E4 & E5 & E6 & _ & _ & _ & SW' & LB') _].
    split; [reflexivity|].
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    assert (MU3 : munch [(lo, bv_unsigned sp); (A_STDERR, A_STDERR + 232); (A_STDERR_BUF, A_STDERR_BUF + 0)] m m').
    { eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros a Ha; repeat split; tauto. }
    assert (FR' : FILE_R m' f' A_STDERR A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0).
    { exists flags', mode', 0, tail, bufbytes.
      rewrite WA', RB', BS', WB'. change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
      split; [exact FC'|]. split; [exact FL'|].
      split. { eapply (rw_cells_transport asegs _ m m'); [exact BUF | exact MU | exact WM |]. unfold A_STDERR, A_STDERR_BUF. cbn [disjoint_from cells_size csize Nat.add]. pose proof (@ATOP_lo rc). lia. }
      split; [reflexivity|]. split; [intros _; reflexivity|]. split; [lia|].
      split; [intros X; exfalso; exact (X eq_refl)|]. split; [lia|]. split; [lia| exact GLN]. }
    assert (INV' : stderr_inv f').
    { unfold stderr_inv. rewrite E1, E2, E3, E4, E5, E6, RB'.
      split; [exact CH2|]. split; [exact FD2|]. split; [reflexivity|]. split; [exact ND2|]. split; [exact NW2|]. split; [exact EOF2|]. split; [reflexivity|].
      split.
      - destruct (f_stdoutw f'); [| reflexivity]. exfalso. pose proof (SW' eq_refl) as X. rewrite SW2 in X. discriminate X.
      - destruct (f_lbf_nl f'); [| reflexivity]. exfalso. pose proof (LB' eq_refl) as X. rewrite LB2 in X. discriminate X. }
    destruct (GIOA_stderr_step L RNG s CL FB FL m m' f' lo (bv_unsigned sp) G LOA LOS MU3 WM FR' INV') as [G' AG].
    split; [exact AG | exact G'].
  Qed.
  End Sz12.
  Lemma stderr_after : ltac:(let t := eval cbv delta [stderr_after__stmt] in stderr_after__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL m lo canary ps tail bufbytes f' st' ms'. ltac2:(SecDiet.SzSec.closeP 'stderr_after__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition eprintf_s_genA__stmt : Prop := forall FMT fl (mk : list Z -> list (list Z)) fs,
    (forall sv, zlength sv <= 2^24 -> fmt_call_okD FMT fs [AStr sv] [PA_s sv] (mk sv)) ->
    zlength (str fs ++ [0]) = fl + 1 ->
    eprintf_s_stmt_o GIOA FMT fl mk.
  Section Sz13.
  Variables FMT fl mk fs ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo P str slack : ltac2:(SecDiet.SzSec.tyM 'eprintf_s_genA__stmt "vvvvhhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @FMT).
  Lemma eprintf_s_genA__body : ltac2:(SecDiet.SzSec.bodyP 'eprintf_s_genA__stmt "vvvvhhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros CALL EZ.
 intros SPD TOPLO -> -> -> MOF BY NZ LEN PAD MOP KEEP.
    pose proof (spd_factsA _ _ _ _ _ _ _ _ _ _ _ SPD) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SP47 & TOP47 & Etp & RSTK & RIMG & RIMGSH & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK, STDERR_FILE in *.
    sbl_pose_in SE. destruct SE as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    pose proof SEI as (CH2 & FD2 & BS2 & ND2 & NW2 & EOF2 & RB2 & SW2 & LB2).
    assert (WBN : f_wbuf (lc_stderr (ps_libc s)) = []).
    { destruct (f_wbuf (lc_stderr (ps_libc s))) eqn:E; [reflexivity|]. exfalso. rewrite BS2 in WBL. unfold zlength in WBL. cbn [Datatypes.length] in WBL. lia. }
    rewrite BS2, RB2, WBN in FC. rewrite BS2 in BUF. change (zlength (@nil Z)) with 0 in FC. rewrite RB2 in RP1. change (zlength (@nil Z)) with 0 in RP1.
    change (Z.to_nat 0) with 0%nat in BUF.
    assert (EL : zlength (map bv_unsigned str) = Z.of_nat (length str)) by (unfold zlength; rewrite length_map; reflexivity).
    pose proof (CALL (map bv_unsigned str) ltac:(rewrite EL; lia)) as (HF & P1 & PIECES & SMALL & HA & BYf & IOK).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL.
    destruct (str_arg_factsD L RNG s CL FB FL m lo (bv_unsigned sp) A_STDERR 232 (bv_unsigned sp - 464) 80 (bv_unsigned sp - 480) P str slack
                G LOA ltac:(lia) BY NZ LEN PAD MOP KEEP ltac:(unfold A_STDERR; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [AOK1 PWD1].
    destruct (pitems_facts fs [AStr (map bv_unsigned str)] [Z_to_bv 64 P] IOK eq_refl) as (FSTR & NOZ & EF & OKI).
    assert (PW : pwords_ok RNG lo sp m (pitems fs [AStr (map bv_unsigned str)] [Z_to_bv 64 P]) [Z_to_bv 64 P; a3; a4; a5; a6; a7]).
    { apply (pwords_ok_more RNG lo sp m _ [Z_to_bv 64 P] [a3; a4; a5; a6; a7]).
      apply pitems_words_fs; [exact IOK | apply Forall2_cons; [exact (PWD1 sp eq_refl) | apply Forall2_nil]]. }
    assert (SOFMT : sobj RNG m FMT (FMT + zlength (Fmt.str fs ++ [0]))) by (rewrite EZ; apply mobjA_sobj; [exact MOF | unfold zlength in *; lia]).
    destruct (gs_statics _ GSL _ _ _ _ _ _ _ G RIMG RIMGSH) as [SOS1 SOS2].
    unfold eprintf. apply implMG_rd_lc.
    eapply implMG_bind.
    { eapply implMG_leaf. apply implAM_implMG. unfold FPRINTF_ENTRY. change A_STDERR with 694960 in FC.
      eapply (fprintf_i_ubf_spec (St:=PS) RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 694960 A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail
                FMT lo (Fmt.str fs ++ [0]) (Z_to_bv 64 P) a3 a4 a5 a6 a7 [PA_s (map bv_unsigned str)]
                (mk (map bv_unsigned str)) _ canary (zb (Fmt.str fs)) (pitems fs [AStr (map bv_unsigned str)] [Z_to_bv 64 P]))
        with (rpos := rp) (flags := flags) (mode := mode).
      all: match goal with |- ?g => first
             [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact KLO | exact RSTK | exact RIMG | exact FSTR | exact NOZ | exact EF | exact OKI
             | reflexivity | exact FC | exact FLG
             | exact BS2 | exact NW2 | exact RB2 | exact WBN | exact CH2 | (right; exact FD2) | exact SW2
             | (apply BYf; exact MI)
             | (cbn [args_ok]; split; [exact AOK1 | exact I])
             | exact ST | exact SSP | exact MI | exact ENV | exact (gs_ckpf _ GSL _ _ _ _ _ _ _ G) | exact (gs_rng0 _ GSL _ _ _ _ _ _ _ G) | exact PW | exact SOFMT
             | (apply (gs_stack _ GSL _ _ _ _ _ _ _ lo (bv_unsigned sp - 112) G); (keep_hyps rc lo P str slack LOA sp LOB L TOPLO SP47; lia))
             | (apply (gs_rodata _ GSL _ _ _ _ _ _ _ 68460 68469 G RIMG RIMGSH); [left; (keep_hyps rc P str slack; lia) | (keep_hyps rc P str slack; lia)])
             | (eapply sobj_sub; [exact SOS1 | (keep_hyps rc lo P str slack GLO sp LOA LOB; lia) | (keep_hyps rc sp P str slack SP47; lia) | (keep_hyps rc P str slack; lia)])
             | (eapply rng_sub'; [exact RIMG | (keep_hyps rc P str slack; lia)])
             | (unfold iesafe; cbn [disjoint_from]; repeat split; (keep_hyps rc sp P str slack SP47 lo rp RP0 RP1; lia))
             | (left; lia)
             | (unfold FPRINTF_I_DEPTH, GLOBALS_TOP, A_STDERR_BUF in *; try destruct (f_wactive (lc_stderr (ps_libc s))); (keep_hyps rc sp lo P str slack LOB GLO; lia))
             | idtac "EPS-LEFT:" g ] end. }
    cbv beta. intros f' st' RNG' ms' [(-> & PO) LF].
    assert (LOS : lo <= bv_unsigned sp) by lia.
    destruct (stderr_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L RNG s CL FB FL m lo canary _ tail bufbytes f' st' ms' G LOA LOS GLN BUF PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & AG & G').
    unfold upd_lc. apply implMG_upd. apply evtF_done. unfold out_post_o.
    split; [apply fp_le_refl|].
    exists a0', m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. exact G'.
  Qed.
  End Sz13.
  Lemma eprintf_s_genA : ltac:(let t := eval cbv delta [eprintf_s_genA__stmt] in eprintf_s_genA__stmt in exact t).
  Proof using GL GSL. intros FMT fl mk fs CALL EZ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo P str slack. ltac2:(SecDiet.SzSec.closeP 'eprintf_s_genA__body "vvvvhhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Theorem eprintf_usage_proofA : eprintf_s_stmt_o GIOA FMT_USAGE 16 pieces_usage.
  Proof using GL GSL. exact (eprintf_s_genA FMT_USAGE 16 pieces_usage FS_USAGE call_usageD ltac:(vm_compute; reflexivity)). Qed.
  Theorem eprintf_cannot_open_proofA : eprintf_s_stmt_o GIOA FMT_CANNOT_OPEN 20 pieces_cannot_open.
  Proof using GL GSL. exact (eprintf_s_genA FMT_CANNOT_OPEN 20 pieces_cannot_open FS_CANNOT_OPEN call_cannot_openD ltac:(vm_compute; reflexivity)). Qed.
  Theorem eprintf_read_error_proofA : eprintf_s_stmt_o GIOA FMT_READ_ERROR 22 pieces_read_error.
  Proof using GL GSL. exact (eprintf_s_genA FMT_READ_ERROR 22 pieces_read_error FS_READ_ERROR call_read_errorD ltac:(vm_compute; reflexivity)). Qed.

  Definition eprintf_too_big_proofA__stmt : Prop := eprintf_i_stmt_o GIOA FMT_TOO_BIG 32 0x4000000 pieces_too_big.
  Section Sz17.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo : ltac2:(SecDiet.SzSec.tyM 'eprintf_too_big_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma eprintf_too_big_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'eprintf_too_big_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
 intros SPD TOPLO -> -> -> MOF.
    pose proof (spd_factsA _ _ _ _ _ _ _ _ _ _ _ SPD) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SP47 & TOP47 & Etp & RSTK & RIMG & RIMGSH & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK, STDERR_FILE in *.
    sbl_pose_in SE. destruct SE as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    pose proof SEI as (CH2 & FD2 & BS2 & ND2 & NW2 & EOF2 & RB2 & SW2 & LB2).
    assert (WBN : f_wbuf (lc_stderr (ps_libc s)) = []).
    { destruct (f_wbuf (lc_stderr (ps_libc s))) eqn:E; [reflexivity|]. exfalso. rewrite BS2 in WBL. unfold zlength in WBL. cbn [Datatypes.length] in WBL. lia. }
    rewrite BS2, RB2, WBN in FC. rewrite BS2 in BUF. change (zlength (@nil Z)) with 0 in FC. rewrite RB2 in RP1. change (zlength (@nil Z)) with 0 in RP1.
    change (Z.to_nat 0) with 0%nat in BUF.
    pose proof call_too_bigD as (HF & P1 & PIECES & SMALL & HA & BYf & IOK).
    pose proof (u32_facts 0x4000000) as U32.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL.
    destruct (pitems_facts FS_TOO_BIG [AInt 0x4000000] [Z_to_bv 64 0x4000000] IOK eq_refl) as (FSTR & NOZ & EF & OKI).
    assert (PW : pwords_ok RNG lo sp m (pitems FS_TOO_BIG [AInt 0x4000000] [Z_to_bv 64 0x4000000]) [Z_to_bv 64 0x4000000; a3; a4; a5; a6; a7]).
    { apply (pwords_ok_more RNG lo sp m _ [Z_to_bv 64 0x4000000] [a3; a4; a5; a6; a7]).
      apply pitems_words_fs; [exact IOK | apply Forall2_cons; [exact I | apply Forall2_nil]]. }
    assert (EZ : zlength (str FS_TOO_BIG ++ [0]) = 33) by (vm_compute; reflexivity).
    assert (SOFMT : sobj RNG m FMT_TOO_BIG (FMT_TOO_BIG + zlength (str FS_TOO_BIG ++ [0]))) by (rewrite EZ; apply mobjA_sobj; [exact MOF | lia]).
    destruct (gs_statics _ GSL _ _ _ _ _ _ _ G RIMG RIMGSH) as [SOS1 SOS2].
    assert (LOS : lo <= bv_unsigned sp) by lia.
    unfold eprintf. apply implMG_rd_lc.
    eapply implMG_bind.
    { eapply implMG_leaf. apply implAM_implMG. unfold FPRINTF_ENTRY. change A_STDERR with 694960 in FC.
      eapply (fprintf_i_ubf_spec (St:=PS) RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 694960 A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail
                FMT_TOO_BIG lo (str FS_TOO_BIG ++ [0]) (Z_to_bv 64 0x4000000) a3 a4 a5 a6 a7 [PA_u (u32 0x4000000)]
                pieces_too_big _ canary (zb (str FS_TOO_BIG)) (pitems FS_TOO_BIG [AInt 0x4000000] [Z_to_bv 64 0x4000000]))
        with (rpos := rp) (flags := flags) (mode := mode).
      all: match goal with |- ?g => first
             [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact KLO | exact RSTK | exact RIMG | exact FSTR | exact NOZ | exact EF | exact OKI
             | reflexivity | exact FC | exact FLG
             | exact BS2 | exact NW2 | exact RB2 | exact WBN | exact CH2 | (right; exact FD2) | exact SW2
             | (apply BYf; exact MI)
             | (cbn [args_ok]; split; [exact U32 | exact I])
             | exact ST | exact SSP | exact MI | exact ENV | exact (gs_ckpf _ GSL _ _ _ _ _ _ _ G) | exact (gs_rng0 _ GSL _ _ _ _ _ _ _ G) | exact PW | exact SOFMT
             | (apply (gs_stack _ GSL _ _ _ _ _ _ _ lo (bv_unsigned sp - 112) G); (keep_hyps rc lo LOA sp LOB L TOPLO SP47; lia))
             | (apply (gs_rodata _ GSL _ _ _ _ _ _ _ 68460 68469 G RIMG RIMGSH); [left; (keep_hyps rc; lia) | (keep_hyps rc; lia)])
             | (eapply sobj_sub; [exact SOS1 | (keep_hyps rc lo GLO sp LOA LOB; lia) | (keep_hyps rc sp SP47; lia) | (keep_hyps rc; lia)])
             | (eapply rng_sub'; [exact RIMG | (keep_hyps rc; lia)])
             | (unfold iesafe; cbn [disjoint_from]; repeat split; (keep_hyps rc sp SP47 lo rp RP0 RP1; lia))
             | (left; lia)
             | (unfold FPRINTF_I_DEPTH, GLOBALS_TOP, A_STDERR_BUF in *; try destruct (f_wactive (lc_stderr (ps_libc s))); (keep_hyps rc sp lo LOB GLO; lia))
             | idtac "EPI-LEFT:" g ] end. }
    cbv beta. intros f' st' RNG' ms' [(-> & PO) LF].
    destruct (stderr_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L RNG s CL FB FL m lo canary _ tail bufbytes f' st' ms' G LOA LOS GLN BUF PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & AG & G').
    unfold upd_lc. apply implMG_upd. apply evtF_done. unfold out_post_o.
    split; [apply fp_le_refl|].
    exists a0', m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. exact G'.
  Qed.
  End Sz17.
  Theorem eprintf_too_big_proofA : ltac:(let t := eval cbv delta [eprintf_too_big_proofA__stmt] in eprintf_too_big_proofA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo. ltac2:(SecDiet.SzSec.closeP 'eprintf_too_big_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition stderr_inv_fx__stmt : Prop := forall f f', stderr_inv f -> fx_inv f f' -> stderr_inv f'.
  Section Sz18.
  Variables f f' : ltac2:(SecDiet.SzSec.tyM 'stderr_inv_fx__stmt "vv" @f).
  Lemma stderr_inv_fx__body : ltac2:(SecDiet.SzSec.bodyP 'stderr_inv_fx__stmt "vv").
  Proof using Type. pin_using tt.
    intros (CH & FD & BS & NRD & NWR & EOF & RB & SW & LB) (E1 & E2 & E3 & E4 & E5 & E6 & WA & RB' & SW' & LB').
    unfold stderr_inv. rewrite E1, E2, E3, E4, E5, E6, RB', RB.
    split; [exact CH|]. split; [exact FD|]. split; [exact BS|]. split; [exact NRD|]. split; [exact NWR|]. split; [exact EOF|].
    split; [destruct (f_wactive f); reflexivity|].
    split; [destruct (f_stdoutw f'); [exfalso; pose proof (SW' eq_refl) as X; rewrite SW in X; discriminate X| reflexivity]|].
    destruct (f_lbf_nl f'); [exfalso; pose proof (LB' eq_refl) as X; rewrite LB in X; discriminate X| reflexivity].
  Qed.
  End Sz18.
  Lemma stderr_inv_fx : ltac:(let t := eval cbv delta [stderr_inv_fx__stmt] in stderr_inv_fx__stmt in exact t).
  Proof using Type. intros f f'. ltac2:(SecDiet.SzSec.closeP 'stderr_inv_fx__body "vv"). Qed.

  Definition efwrite_proofA__stmt : Prop := efwrite_stmt_o GIOA.
  Section Sz19.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo MSG bs : ltac2:(SecDiet.SzSec.tyM 'efwrite_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma efwrite_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'efwrite_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
 intros SPD -> -> -> -> HSRC ROD LEN1 MOS.
    pose proof (spd_factsA _ _ _ _ _ _ _ _ _ _ _ SPD) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SP47 & TOP47 & Etp & RSTK & RIMG & RIMGSH & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK, STDERR_FILE, DRV_RODATA_LO, DRV_RODATA_HI in *.
    sbl_pose_in SE. destruct SE as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP). sbl_subst_all.
    pose proof FLG as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    pose proof SEI as (CH2 & FD2 & BS2 & ND2 & NW2 & EOF2 & RB2 & SW2 & LB2).
    rewrite NW2 in FLw. rewrite BS2 in *.
    pose proof (bytes_at_bound _ _ _ _ HSRC) as BSRC.
    assert (WBN : f_wbuf (lc_stderr (ps_libc s)) = []).
    { destruct (f_wbuf (lc_stderr (ps_libc s))) eqn:E; [reflexivity|]. exfalso. unfold zlength in WBL. cbn [length] in WBL. lia. }
    pose proof MOS as (_ & _ & _ & RGS & _ & _).
    pose proof (mobjA_sobj _ _ _ _ MOS ltac:(lia)) as SOS.
    destruct (gs_statics _ GSL _ _ _ _ _ _ _ G RIMG RIMGSH) as [SOS1 SOS2].
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL.
    unfold efwrite. apply implMG_rd_lc.
    eapply implMG_bind.
    { apply implAM_implMG. unfold FWRITE_ENTRY. unfold A_STDERR, A_STDERR_BUF in *.
      eapply (fwrite_i_spec (St:=PS) RNG) with (f := lc_stderr (ps_libc s)) (s := map bv_unsigned bs) (S := MSG) (lo := lo) (canary := canary)
        (Fp := 694960) (flags := flags) (rpos := rp) (rend := rp + zlength (f_rbuf (lc_stderr (ps_libc s)))) (closefn := F_STDIO_CLOSE) (readfn := 0)
        (seekfn := F_STDIO_SEEK) (B := 6298816) (prev := 0) (next := 0) (mode := mode) (tail := tail) (bufbytes := bufbytes)
        (size := Z.of_nat (length bs)) (nmemb := 1).
      all: try unfold fcells in *. all: rewrite ?BS2 in *.
      all: unfold FWRITE_I_DEPTH, got_ssp, ssp_guard in *.
      all: unfold zlength in *; rewrite ?length_map.
      all: try first [ exact FC | exact BUF | exact BP | exact WB0 | exact ST | exact MI | exact SSP | exact FLsvb | exact FLw
                 | (change (map bv_unsigned bs) with (of_bytes bs); rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read.to_of_bytes; exact HSRC)
                 | (apply Forall_map; apply Forall_forall; intros b _; pose proof (bv_unsigned_in_range 8 b); unfold bv_modulus in *; cbn in *; (keep_hyps rc H hptr s bs b H0; lia))
                 | reflexivity | (f_equal; (keep_hyps rc H hptr s MSG bs ROD LEN1 sp lo LOB GLO SP47 WBL LOA KLO; lia)) | (rewrite CH2; right; exact FD2)
                 | exact KLO | exact ENV | exact SOS | exact RSTK | exact RGS | exact RIMG
                 | (eapply sobj_sub; [exact SOS2 | (keep_hyps rc H hptr s bs; lia) | (keep_hyps rc H hptr s bs; lia) | (keep_hyps rc H hptr s bs; lia)])
                 | (eapply rng_sub'; [exact RIMG | (keep_hyps rc H hptr s bs; lia)])
                 | (unfold iesafe; cbn [disjoint_from]; repeat split; (keep_hyps rc H hptr s bs; lia))
                 | (apply (sobj_appW RNG m); eapply sobj_sub; [exact SOS1 | (keep_hyps rc H hptr s bs; lia) | (keep_hyps rc H hptr s bs; lia) | (keep_hyps rc H hptr s bs; lia)])
                 | (apply (sobj_appW RNG m); eapply sobj_sub; [exact SOS2 | (keep_hyps rc H hptr s bs; lia) | (keep_hyps rc H hptr s bs; lia) | (keep_hyps rc H hptr s bs; lia)])
                 | (rewrite WBN; cbn [length Z.of_nat]; lia)
                 | lia | (left; lia) | (right; lia) | (right; repeat split; lia) | (split; lia) ]. }
    cbv beta. intros f' st' RNG' ms' (-> & -> & INV' & PO).
    sbl_pose_in PO. destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mode' & bufbytes' & m' & -> & MU & WM & MI' & ST' & FC' & BUF' & BP' & WBL' & SSP'). sbl_subst_all.
    unfold fx_W in MU. rewrite ?BS2 in MU.
    assert (FR' : FILE_R m' f' A_STDERR A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0).
    { pose proof INV' as (E1 & E2 & E3 & E4 & E5 & E6 & WA & RB & SW & LB).
      assert (RBN' : f_rbuf f' = []) by (rewrite RB, RB2; destruct (f_wactive (lc_stderr (ps_libc s))); reflexivity).
      rewrite RB2 in FC'.
      exists flags, mode', (if f_wactive (lc_stderr (ps_libc s)) then rp else 0), tail, bufbytes'.
      rewrite WA, RBN', E1, E3, BS2. unfold A_STDERR, A_STDERR_BUF.
      split. { unfold fcells in *. rewrite ?BS2 in FC'. destruct (f_wactive (lc_stderr (ps_libc s))); cbn [zlength length Z.of_nat] in FC' |- *; rewrite ?Z.add_0_r in FC' |- *; exact FC'. }
      split. { unfold flags_ok in *. rewrite E2, E4, E5, E6. rewrite NW2 in FLG |- *. exact FLG. }
      split; [rewrite ?BS2 in BUF'; exact BUF'|]. split; [exact BP'|]. split; [intros X; discriminate X|]. split; [rewrite ?BS2 in WBL'; exact WBL'|].
      split; [intros X; exfalso; exact (X eq_refl)|]. destruct (f_wactive (lc_stderr (ps_libc s))); unfold zlength in RP |- *; cbn [length Z.of_nat]; (split; [lia| split; [lia| exact (proj2 (proj2 RP))]]). }
    destruct (GIOA_stderr_step L RNG s CL FB FL m m' f' lo (bv_unsigned sp) G LOA ltac:(lia) MU WM FR' (stderr_inv_fx _ _ SEI INV')) as [G' AG].
    unfold upd_lc. apply implMG_upd. apply evtF_done. unfold out_post_o.
    split; [apply fp_le_refl|].
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. exact G'.
  Qed.
  End Sz19.
  Theorem efwrite_proofA : ltac:(let t := eval cbv delta [efwrite_proofA__stmt] in efwrite_proofA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo MSG bs. ltac2:(SecDiet.SzSec.closeP 'efwrite_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueDrv.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_fwrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.Printf_fsink.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.F_vfprintf_file.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_words.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_mkstemp__A3S.I_snprintf_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.I_fprintf_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.I_printf_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fwrite_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_fmtA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.Printf_pitems.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Vfprintf_leafA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_snA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_pfA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sbl_is_big n := lazymatch n with S _ => let b := eval vm_compute in (Nat.leb 200 n) in lazymatch b with true => idtac end end.
Local Ltac sbl_pose_in H :=
  (let T := type of H in let T' := eval hnf in T in change T' in H);
  repeat match type of H with
  | context [repeat ?b ?n] => sbl_is_big n; let z := fresh "sblz" in pose (z := repeat b n); change (repeat b n) with z in H
  | context [CB ?n _] => sbl_is_big n; let x := fresh "sblv" in pose (x := n); change n with x in H
  end.
Local Ltac sbl_subst_all :=
  repeat match goal with
  | z := repeat _ ?n |- _ => sbl_is_big n; subst z
  | x := ?n |- _ => sbl_is_big n; subst x
  end.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithRc. Context {rc : runConstT}.
Definition fmt_call_okD (FMT : Z) (fs : string) (args : list farg) (pargs : list parg) (ps : list (list Z)) : Prop :=
  Forall (fun c => 0 <= c < 256) (str fs ++ [0]) /\ pass1_ok (str fs ++ [0]) = true
  /\ printf_pieces (str fs ++ [0]) pargs = Some (ps, zlength (fmt_output (fmt fs) args)) /\ pieces_small ps
  /\ (65536 <= FMT /\ FMT + zlength (str fs ++ [0]) <= 204800)
  /\ (forall m, mem_inv asegs m -> bytes_at asegs m FMT (zb (str fs ++ [0])))
  /\ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true.

#[using="Type"] Lemma fmt_call_okD_intro : forall fs FMT args,
  fmt_staticA fs FMT -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> (length args <= 2)%nat ->
  Forall (fun a => farg_len a <= 2^24) args -> zlength (str fs) < 4096 ->
  fmt_call_okD FMT fs args (to_pargs (fmt fs) args) (fmt_pieces (fmt fs) args).
Proof.
  intros fs FMT args FS OK L2 SM FL.
  destruct (fmt_facts fs args OK L2 SM FL) as (HF & P1 & PIECES & SMALL & RB).
  pose proof FS as (RO & LO & HI).
  split; [exact HF|]. split; [exact P1|]. split; [exact PIECES|]. split; [exact SMALL|].
  split; [split; [exact LO| exact HI]|]. split; [intros m MI; exact (fmt_bytesA m fs FMT MI FS) | exact OK].
Qed.
End WithRc.

Local Close Scope string_scope.

Local Ltac fmt_callD :=
  apply fmt_call_okD_intro;
    [ split; [vm_compute; reflexivity | vm_compute; split; intros HH; discriminate HH]
    | vm_compute; reflexivity
    | cbn [length]; Lia.lia
    | repeat constructor; cbn [farg_len]; try assumption; try Lia.lia
    | vm_compute; reflexivity ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Open Scope string_scope.
Definition FS_EMIT_D : string := "%d
".
Definition FS_USAGE : string := "usage: %s INPUT
".
Definition FS_CANNOT_OPEN : string := "cli: cannot open %s
".
Definition FS_READ_ERROR : string := "cli: read error on %s
".
Definition FS_TOO_BIG : string := "cli: input >= %u bytes, refused
".
Local Close Scope string_scope.

Section WithRc2. Context {rc : runConstT}.
#[using="Type"] Lemma call_emit_dD : forall v, fmt_call_okD FMT_D FS_EMIT_D [AInt v] [PA_i (s32 v)] (pieces_emit_d v).
Proof. intros v. fmt_callD. Qed.
#[using="Type"] Lemma call_usageD : forall s, zlength s <= 2^24 -> fmt_call_okD FMT_USAGE FS_USAGE [AStr s] [PA_s s] (pieces_usage s).
Proof. intros s Hs. fmt_callD. Qed.
#[using="Type"] Lemma call_cannot_openD : forall s, zlength s <= 2^24 -> fmt_call_okD FMT_CANNOT_OPEN FS_CANNOT_OPEN [AStr s] [PA_s s] (pieces_cannot_open s).
Proof. intros s Hs. fmt_callD. Qed.
#[using="Type"] Lemma call_read_errorD : forall s, zlength s <= 2^24 -> fmt_call_okD FMT_READ_ERROR FS_READ_ERROR [AStr s] [PA_s s] (pieces_read_error s).
Proof. intros s Hs. fmt_callD. Qed.
#[using="Type"] Lemma call_too_bigD : fmt_call_okD FMT_TOO_BIG FS_TOO_BIG [AInt 0x4000000] [PA_u (u32 0x4000000)] pieces_too_big.
Proof. fmt_callD. Qed.
End WithRc2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section GlueDrv.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vprintf_d_proofA__stmt : Prop := vprintf_d_stmt_o GIOA.
  Section Sz7.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo AP v rest : ltac2:(SecDiet.SzSec.tyM 'vprintf_d_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma vprintf_d_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'vprintf_d_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
 intros SPO -> -> HV MOF APC APLO APHI.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & _ & _ & (RSTKF & _ & RIMGSH & _)).
    pose proof (spo_factsA GIOA GSL _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK in *.
    sbl_pose_in SO. destruct SO as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    pose proof SOI as (CH1 & FD1 & BS1 & NRD1 & NWR1 & EOF1 & RB1 & LBF1).
    pose proof (call_emit_dD v) as (HF & P1 & PIECES & SMALL & HA & BYf & IOK).
    pose proof (s32_facts v) as [S32a S32b].
    rewrite BS1 in FC, BUF, WBL. unfold BUFSIZ in FC, BUF, WBL.
    pose proof (rw_cells_bound _ _ _ _ APC) as APB. cbn [cells_size csize Nat.add] in APB.
    apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in APC. destruct APC as [APC _].
    destruct (pitems_facts FS_EMIT_D [AInt v] [Z_to_bv 64 v] IOK eq_refl) as (FSTR & NOZ & EF & OKI).
    assert (RVA : rng RNG AP 8) by (eapply rng_sub'; [exact RSTKF | lia]).
    assert (PW : pargs_okL RNG lo sp m (pitems FS_EMIT_D [AInt v] [Z_to_bv 64 v]) (Z_to_bv 64 AP)).
    { apply (pargs_okL_of_words RNG lo sp m _ [Z_to_bv 64 v] AP); [| exact APC | exact APLO | cbn [length]; lia | exact RVA].
      apply pitems_words_fs; [exact IOK | apply Forall2_cons; [exact I | apply Forall2_nil]]. }
    destruct (gs_statics _ GSL _ _ _ _ _ _ _ G RIMG RIMGSH) as [SOS1 SOS2].
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL.
    assert (EZ : zlength (str FS_EMIT_D ++ [0]) = 4) by (vm_compute; reflexivity).
    assert (SOFMT : sobj RNG m FMT_D (FMT_D + zlength (str FS_EMIT_D ++ [0]))) by (rewrite EZ; apply mobjA_sobj; [exact MOF | lia]).
    unfold printf. apply implMG_rd_lc.
    eapply implMG_bind.
    { eapply implMG_leaf. apply implAM_implMG. unfold VPRINTF_ENTRY.
      eapply (vprintf_i_spec (St:=PS) RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail FMT_D AP lo
                (str FS_EMIT_D ++ [0]) [Z_to_bv 64 v] [PA_i (s32 v)] (pieces_emit_d v) _ canary (zb (str FS_EMIT_D)) (pitems FS_EMIT_D [AInt v] [Z_to_bv 64 v]) true true)
        with (rpos := rp) (rend := rp + zlength (f_rbuf (lc_stdout (ps_libc s)))) (flags := flags) (mode := mode) (bufbytes := bufbytes).
      all: match goal with |- ?g => first
             [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact KLO | exact RSTK | exact RIMG | exact FSTR | exact NOZ | exact EF | exact OKI
             | reflexivity | exact FC | exact FLG | exact BUF | exact BP | exact WB0
             | exact BS1 | exact WBL | exact NWR1 | exact RB1
             | (rewrite CH1; left; exact FD1) | exact CH1 | (intros _; reflexivity)
             | (apply BYf; exact MI)
             | (apply va_area_of_cells; exact APC)
             | (cbn [args_ok]; split; [split; [exact S32a | exact S32b] | exact I])
             | exact ST | exact SSP | exact MI | exact ENV | exact (gs_ckpf _ GSL _ _ _ _ _ _ _ G) | exact PW
             | (apply (gs_stack _ GSL _ _ _ _ _ _ _ lo (bv_unsigned sp) G); (keep_hyps rc lo AP v LOA sp LOB L SPT APLO APHI TOP47; lia))
             | exact SOFMT | exact RVA
             | (apply (gs_rodata _ GSL _ _ _ _ _ _ _ 68460 68469 G RIMG RIMGSH); [left; (keep_hyps rc AP v; lia) | (keep_hyps rc AP v; lia)])
             | (eapply sobj_sub; [exact SOS1 | unfold A_STDOUT; (keep_hyps rc lo AP v GLO; lia) | (keep_hyps rc AP v; lia) | unfold A_STDOUT; (keep_hyps rc AP v; lia)])
             | (eapply sobj_sub; [exact SOS2 | unfold A_STDOUT_BUF; (keep_hyps rc lo AP v GLO; lia) | (keep_hyps rc AP v; lia) | unfold A_STDOUT_BUF; (keep_hyps rc AP v; lia)])
             | (eapply rng_sub'; [exact RIMG | unfold A_STDOUT_BUF; lia])
             | (cbv [zlength Datatypes.length Z.of_nat Pos.of_succ_nat Pos.succ]; unfold VPRINTF_I_DEPTH, GLOBALS_TOP in *; (keep_hyps rc sp lo AP v LOB GLO L APLO APHI TOP47; lia))
             | idtac "VPD-LEFT:" g ] end. }
    cbv beta. intros f' st' RNG' ms' [(-> & PO) LF].
    sbl_pose_in PO. destruct PO as (-> & INV' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & flags' & mode' & bufbytes' & m' & rpos' & rend'
                     & -> & MU & WM & MI' & ST' & SSP' & FC' & RP' & FL' & BUF' & BP' & WBL'). sbl_subst_all.
    assert (BSnz : f_bufsize (lc_stdout (ps_libc s)) <> 0) by (rewrite BS1; unfold BUFSIZ; lia).
    pose proof (vfprintf_leaf_buffered _ _ _ _ _ BSnz LF) as [FX _].
    pose proof (vfprintf_leaf_buffered_wl _ _ _ _ _ BSnz LF) as WL.
    pose proof INV' as (WA' & RB' & BS' & NW' & FDC' & _ & CHN').
    rewrite RB1 in RP1. change (zlength (@nil Z)) with 0 in RP1.
    assert (FR' : FILE_R m' f' A_STDOUT A_STDOUT_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0).
    { exists flags', mode', rpos', tail, bufbytes'.
      rewrite WA', RB', BS'. change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
      assert (Erend : rend' = rpos') by (rewrite RB1 in RP'; change (zlength (@nil Z)) with 0 in RP'; lia).
      rewrite Erend in FC'.
      split; [exact FC'|]. split; [exact FL'|]. split; [exact BUF'|]. split; [exact BP'|]. split; [intros X; discriminate X|]. split; [exact WBL'|].
      split; [intros X; exfalso; exact (X eq_refl)|]. split; [lia|]. split; [lia| exact GLN]. }
    assert (SOI' : stdout_inv f').
    { pose proof FX as (E1 & E2 & E3 & E4 & E5 & E6 & _ & _ & SW' & LB').
      unfold stdout_inv. rewrite E1, E2, E4, E5, E6.
      split; [exact CH1|]. split; [exact FD1|]. split; [exact BS'|]. split; [exact NRD1|]. split; [exact NWR1|]. split; [exact EOF1|]. split; [exact RB'|].
      destruct WL as [[W1 W2]|[W1 W2]]; rewrite W1, ?W2; [exact LBF1| intros X; discriminate X]. }
    destruct (GIOA_stdout_step FO GIOA fflagA GL GSL L RNG s CL FB FL m m' f' lo (bv_unsigned sp) G LOA ltac:(lia) MU WM FR' SOI') as [G' AG].
    unfold upd_lc. apply implMG_upd. apply evtF_done. unfold out_post_o.
    split; [apply fp_le_refl|].
    exists a0', m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. exact G'.
  Qed.
  End Sz7.
  Theorem vprintf_d_proofA : ltac:(let t := eval cbv delta [vprintf_d_proofA__stmt] in vprintf_d_proofA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo AP v rest. ltac2:(SecDiet.SzSec.closeP 'vprintf_d_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition spd_factsA__stmt : Prop := forall L RNG sp tp (s : PS) CL FB FL lo budget m,
    std_pre_d GIOA L RNG sp tp s CL FB FL lo budget m ->
    GIOA L RNG s CL FB FL m /\ STDIOR (ps_libc s) FB m /\ stk asegs m lo (bv_unsigned sp) /\ mem_inv asegs m
    /\ (exists canary, ssp_cells m canary) /\ icptenv m
    /\ ATOP + 4096 <= lo /\ lo + budget <= bv_unsigned sp /\ bv_unsigned sp < 2^47 /\ al_top L <= 2^47
    /\ tp = Z_to_bv 64 ATP
    /\ rng RNG lo (bv_unsigned sp - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG /\ KHIGH <= lo /\ 0x604000 <= lo.
  Section Sz8.
  Variables L RNG sp tp s CL FB FL lo budget m : ltac2:(SecDiet.SzSec.tyM 'spd_factsA__stmt "vvvvvvvvvvv" @L).
  Lemma spd_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'spd_factsA__stmt "vvvvvvvvvvv").
  Proof using GSL. pin_using (fun (GSL : unit) => tt).
    intros (G & ST & LOA & LOB & (SPT & TOP47) & MI & Etp & SPAL & (RSTKT & RSTK & RIMG & RIMGSH & RTLS)).
    pose proof (@ATOP_lo rc) as AL. pose proof (@ATOP_hi rc) as AH.
    split; [exact G|]. split; [exact (gs_stdio _ GSL _ _ _ _ _ _ _ G)|]. split; [exact ST|]. split; [exact MI|].
    split; [destruct (gs_ssp _ GSL L) as [canL SSPL]; exists canL; exact (SSPL _ _ _ _ _ _ G)|]. split; [exact (gs_env _ GSL _ _ _ _ _ _ _ G)|].
    split; [exact LOA|]. split; [exact LOB|]. split; [exact SPT|]. split; [exact TOP47|]. split; [exact Etp|].
    split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RIMGSH|]. split; [exact RTLS|].
    unfold KHIGH. split; lia.
  Qed.
  End Sz8.
  Lemma spd_factsA : ltac:(let t := eval cbv delta [spd_factsA__stmt] in spd_factsA__stmt in exact t).
  Proof using GSL. intros L RNG sp tp s CL FB FL lo budget m. ltac2:(SecDiet.SzSec.closeP 'spd_factsA__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition keeps_lowD__stmt : Prop := forall L RNG (s : PS) CL FB FL m SP a,
    GIOA L RNG s CL FB FL m -> client_keeps FL CL SP a -> a < SP -> 0x604000 <= a < ATOP.
  Section Sz9.
  Variables L RNG s CL FB FL m SP a : ltac2:(SecDiet.SzSec.tyM 'keeps_lowD__stmt "vvvvvvvvv" @L).
  Lemma keeps_lowD__body : ltac2:(SecDiet.SzSec.bodyP 'keeps_lowD__stmt "vvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G KEEP LT.
    pose proof (@ATOP_lo rc) as ATL.
    destruct KEEP as [X|[X|[X|X]]]; [lia| | |].
    - pose proof (gia_in_block_below FO GIOA fflagA GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; exact X)) as [B0 B1].
      apply in_block_In in X as (b & Hb & Hr).
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; exact Hb)) as ((ABLK & _) & _).
      unfold ablk, AIMG_HI, KLS in ABLK. lia.
    - pose proof (gia_in_frames_below FO GIOA fflagA GL _ _ _ _ _ _ _ a G X) as [B0 B1].
      apply in_frames_In in X as (fr & Hf & Hr).
      destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr Hf) as (BAND & _).
      unfold ablk, AIMG_HI, KLS in BAND. lia.
    - pose proof (gia_in_frame_sh_band FO GIOA fflagA GL _ _ _ _ _ _ _ a G X) as [B0 B1]. lia.
  Qed.
  End Sz9.
  Lemma keeps_lowD : ltac:(let t := eval cbv delta [keeps_lowD__stmt] in keeps_lowD__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m SP a. ltac2:(SecDiet.SzSec.closeP 'keeps_lowD__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition GIOA_stderr_step__stmt : Prop := forall L RNG (s : PS) CL FB FL m m' (f' : file_st) lo SP,
    GIOA L RNG s CL FB FL m -> ATOP + 4096 <= lo -> lo <= SP ->
    munch [(lo, SP); (A_STDERR, A_STDERR + 232); (A_STDERR_BUF, A_STDERR_BUF + 0)] m m' -> wmono asegs m m' ->
    FILE_R m' f' A_STDERR A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 -> stderr_inv f' ->
    GIOA L RNG (set_libc (set_stderr f' (ps_libc s)) s) CL FB FL m' /\ agrees_on (client_keeps FL CL SP) m m'.
  Section Sz10.
  Variables L RNG s CL FB FL m m' f' lo SP : ltac2:(SecDiet.SzSec.tyM 'GIOA_stderr_step__stmt "vvvvvvvvvvv" @L).
  Lemma GIOA_stderr_step__body : ltac2:(SecDiet.SzSec.bodyP 'GIOA_stderr_step__stmt "vvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros G LOA LOSP MU WM FR' INV'.
    pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G) as SR.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof (@ATOP_lo rc) as ATL.
    unfold A_STDERR, A_STDERR_BUF in MU.
    assert (HW : Forall (stdio_ivA FB SP) [(lo, SP); (695952, 695952 + 232); (6299840, 6299840 + 0)]).
    { unfold stdio_ivA. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd];
        [left; lia | right; right; left; lia | right; right; right; left; lia]. }
    rewrite <- (app_nil_r [(lo, SP); (695952, 695952 + 232); (6299840, 6299840 + 0)]) in MU.
    split.
    2:{ eapply agrees_on_weaken; [eapply (gs_keeps _ GSL L RNG s CL FB FL m m' _ [] SP); [exact G| exact MU| exact WM| exact HW| lia]|].
        intros a Ha. split; [exact Ha | exact I]. }
    eapply (gs_step _ GSL L RNG s CL FB FL m m' _ [] SP); [exact G| exact MU| exact WM| exact HW| apply Forall_nil| lia| |].
    { eapply (errno_cell_kept FO GIOA fflagA GL GSL L RNG s CL FB FL m m' _ [] SP); [exact G| exact MU| exact WM| | apply Forall_nil].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd];
        [left; lia | right; right; left; lia | right; right; right; lia]. }
    rewrite app_nil_r in MU.
    unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_stderr].
    assert (AG : agrees_on (fun a => outside [(lo, SP); (695952, 695952 + 232); (6299840, 6299840 + 0)] a) m m').
    { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hs. exact Hs. }
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    pose proof SOI as (_ & _ & SObs & _).
    split. { eapply FILE_R_agree; [exact SO | exact AG | intros a Ha; cbn [outside]; lia | rewrite SObs; unfold BUFSIZ; intros a Ha; cbn [outside]; lia]. }
    split; [exact SOI|].
    split; [exact FR'|]. split; [exact INV'|].
    split. { eapply agrees_rw_cells; [exact AG | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; cbn [outside]; lia. }
    split; [eapply agrees_rw_cells; [exact AG | exact U1 | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [eapply agrees_rw_cells; [exact AG | exact U2 | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [eapply agrees_rw_cells; [exact AG | exact U3 | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [eapply agrees_rw_cells; [exact AG | exact OL | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [eapply agrees_rw_cells; [exact AG | exact OH | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [| exact ND].
    eapply files_R_agree; [exact FS | exact AG |]. intros a Ha. pose proof (in_block_FB_range FO GIOA fflagA GL _ _ _ _ _ _ _ _ G Ha) as R. cbn [outside]. lia.
  Qed.
  End Sz10.
  Lemma GIOA_stderr_step : ltac:(let t := eval cbv delta [GIOA_stderr_step__stmt] in GIOA_stderr_step__stmt in exact t).
  Proof using GL GSL. intros L RNG s CL FB FL m m' f' lo SP. ltac2:(SecDiet.SzSec.closeP 'GIOA_stderr_step__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition str_arg_factsD__stmt : Prop := forall L RNG (s : PS) CL FB FL m lo SP Fp FS B BS ap P (str slack : list byte),
    GIOA L RNG s CL FB FL m -> ATOP + 4096 <= lo -> lo < SP ->
    bytes_at asegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^24 ->
    (- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
    mobjA RNG m P (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) ->
    (forall a, P <= a < P + Z.of_nat (length str) + 1 -> client_keeps FL CL SP a) ->
    Fp + FS <= 0x604000 -> lo <= B -> B + BS <= SP -> lo <= ap -> ap + 8 <= SP ->
    arg_ok Fp FS B BS RNG m lo SP ap (Z_to_bv 64 P) (PA_s (map bv_unsigned str))
    /\ (forall sp : word, bv_unsigned sp = SP -> pword_ok RNG lo sp m (AStr (map bv_unsigned str)) (Z_to_bv 64 P)).
  Section Sz11.
  Variables L RNG s CL FB FL m lo SP Fp FS B BS ap P str slack : ltac2:(SecDiet.SzSec.tyM 'str_arg_factsD__stmt "vvvvvvvvvvvvvvvvv" @L).
  Lemma str_arg_factsD__body : ltac2:(SecDiet.SzSec.bodyP 'str_arg_factsD__stmt "vvvvvvvvvvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G LOA LOSP BY NZ LB PAD MOP KEEP DF DB1 DB2 DA1 DA2.
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    pose proof (pad8_range (P + Z.of_nat (length str) + 1)) as PR. unfold pad8 in PR.
    set (pd := (- (P + Z.of_nat (length str) + 1)) mod 8) in *.
    pose proof (@ATOP_lo rc) as ATL.
    assert (MOP' : mobjA RNG m P (Z.of_nat (length str) + 1 + pd)) by (eapply mobjA_sub; [exact MOP | lia | lia | lia]).
    pose proof MOP' as (P0 & P47 & _ & RGP & _ & _).
    pose proof (mobjA_sobj _ _ _ _ MOP' ltac:(lia)) as SOD.
    assert (EP : bv_unsigned (Z_to_bv 64 P : word) = P) by (apply unsigned_lit; lia).
    assert (SOS : sobj RNG m P (P + (Z.of_nat (length str) + 1))) by (eapply sobj_sub; [exact SOD | lia | lia | lia]).
    assert (NZF : Forall (fun b : byte => bv_unsigned b <> 0) str).
    { apply Forall_forall. intros b Hb E. apply NZ. replace (Z_to_bv 8 0) with b; [exact Hb|].
      rewrite <- (definitions.Z_to_bv_bv_unsigned 8 b), E. reflexivity. }
    (* [comment removed for export] *)
    assert (PLACE : SP <= P \/ (0x604000 <= P /\ P + (Z.of_nat (length str) + 1 + pd) <= lo)).
    { destruct (Z_le_gt_dec SP P) as [HSP|HSP]; [left; exact HSP | right].
      pose proof (keeps_lowD _ _ _ _ _ _ _ SP P G (KEEP P ltac:(lia)) ltac:(lia)) as [PL PH].
      split; [exact PL|].
      destruct (Z_lt_le_dec (P + Z.of_nat (length str)) SP) as [LT|GE].
      - pose proof (keeps_lowD _ _ _ _ _ _ _ SP (P + Z.of_nat (length str)) G (KEEP (P + Z.of_nat (length str)) ltac:(lia)) LT) as [_ EH]. lia.
      - exfalso. pose proof (keeps_lowD _ _ _ _ _ _ _ SP lo G (KEEP lo ltac:(lia)) LOSP) as [_ X]. lia. }
    split.
    - cbn [arg_ok]. rewrite EP. exists (firstn (Z.to_nat pd) slack).
      assert (LS : length (firstn (Z.to_nat pd) slack) = Z.to_nat pd) by (rewrite length_firstn; lia).
      unfold zlength. rewrite length_map, LS.
      split. { rewrite zb_unsigned. rewrite <- (firstn_skipn (Z.to_nat pd) slack) in BY.
               change (str ++ Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack ++ skipn (Z.to_nat pd) slack)
                 with (str ++ (Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack) ++ skipn (Z.to_nat pd) slack) in BY.
               rewrite app_assoc in BY. apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. exact (proj1 BY). }
      split. { apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & Hb).
               pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
               pose proof (proj1 (Forall_forall _ _) NZF b Hb) as Nb. cbv beta in Nb. lia. }
      split; [lia|]. split; [lia|].
      split; [destruct PLACE as [X|[X1 X2]]; [right; lia | left; lia]|].
      split; [right; destruct PLACE as [X|[X1 X2]]; lia|].
      split; [destruct PLACE as [X|[X1 X2]]; [right; lia | left; lia]|].
      split; [destruct PLACE as [X|[X1 X2]]; [right; lia | left; lia]|].
      split; [lia|].
      split; [eapply rng_sub'; [exact RGP | lia]|].
      replace (P + Z.of_nat (length str) + 1) with (P + (Z.of_nat (length str) + 1)) by lia. exact SOS.
    - intros sp ESP. cbn [pword_ok]. rewrite EP, zb_unsigned. unfold pstrL.
      split. { change (str ++ Z_to_bv 8 0 :: slack) with (str ++ [Z_to_bv 8 0] ++ slack) in BY. rewrite app_assoc in BY.
               apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. exact (proj1 BY). }
      split; [exact NZF|]. split; [destruct PLACE as [X|[X1 X2]]; [right; lia | left; lia]|]. split; [lia|]. split; [exact SOS|].
      eapply rng_sub'; [exact RGP | lia].
  Qed.
  End Sz11.
  Lemma str_arg_factsD : ltac:(let t := eval cbv delta [str_arg_factsD__stmt] in str_arg_factsD__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m lo SP Fp FS B BS ap P str slack. ltac2:(SecDiet.SzSec.closeP 'str_arg_factsD__body "vvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition stderr_after__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
        L RNG (s : PS) CL FB FL (m : mem) (lo : Z) (canary : word) (ps : list (list Z)) (tail bufbytes : list byte)
        (f' : file_st) (st' : PS) (ms' : machine_state),
      GIOA L RNG s CL FB FL m -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp ->
      firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8 ->
      rw_cells asegs m A_STDERR_BUF [CB 0 bufbytes] ->
      vfprintf_ubf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A_STDERR A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail lo canary
                        m s f' st' ms' ->
      mleaf (vfprintf (lc_stderr (ps_libc s)) ps) s f' st' ->
      st' = s /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
        /\ GIOA L RNG (set_libc (set_stderr f' (ps_libc s)) s) CL FB FL m'.
  Section Sz12.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL m lo canary ps tail bufbytes f' st' ms' : ltac2:(SecDiet.SzSec.tyM 'stderr_after__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma stderr_after__body : ltac2:(SecDiet.SzSec.bodyP 'stderr_after__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
 intros G LOA LOS GLN BUF PO LF.
    pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G) as SR.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof SEI as (CH2 & FD2 & BS2 & ND2 & NW2 & EOF2 & RB2 & SW2 & LB2).
    sbl_pose_in PO. destruct PO as (-> & WA' & WB' & RB' & BS' & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & flags' & mode' & m'
                     & -> & MU & WM & MI' & ST' & SSP' & FC' & FL'). sbl_subst_all.
    destruct (vfprintf_leaf_unbuffered _ _ _ _ _ BS2 LF) as [(E1 & E2 & E3 & E4 & E5 & E6 & _ & _ & _ & SW' & LB') _].
    split; [reflexivity|].
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    assert (MU3 : munch [(lo, bv_unsigned sp); (A_STDERR, A_STDERR + 232); (A_STDERR_BUF, A_STDERR_BUF + 0)] m m').
    { eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros a Ha; repeat split; tauto. }
    assert (FR' : FILE_R m' f' A_STDERR A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0).
    { exists flags', mode', 0, tail, bufbytes.
      rewrite WA', RB', BS', WB'. change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
      split; [exact FC'|]. split; [exact FL'|].
      split. { eapply (rw_cells_transport asegs _ m m'); [exact BUF | exact MU | exact WM |]. unfold A_STDERR, A_STDERR_BUF. cbn [disjoint_from cells_size csize Nat.add]. pose proof (@ATOP_lo rc). lia. }
      split; [reflexivity|]. split; [intros _; reflexivity|]. split; [lia|].
      split; [intros X; exfalso; exact (X eq_refl)|]. split; [lia|]. split; [lia| exact GLN]. }
    assert (INV' : stderr_inv f').
    { unfold stderr_inv. rewrite E1, E2, E3, E4, E5, E6, RB'.
      split; [exact CH2|]. split; [exact FD2|]. split; [reflexivity|]. split; [exact ND2|]. split; [exact NW2|]. split; [exact EOF2|]. split; [reflexivity|].
      split.
      - destruct (f_stdoutw f'); [| reflexivity]. exfalso. pose proof (SW' eq_refl) as X. rewrite SW2 in X. discriminate X.
      - destruct (f_lbf_nl f'); [| reflexivity]. exfalso. pose proof (LB' eq_refl) as X. rewrite LB2 in X. discriminate X. }
    destruct (GIOA_stderr_step L RNG s CL FB FL m m' f' lo (bv_unsigned sp) G LOA LOS MU3 WM FR' INV') as [G' AG].
    split; [exact AG | exact G'].
  Qed.
  End Sz12.
  Lemma stderr_after : ltac:(let t := eval cbv delta [stderr_after__stmt] in stderr_after__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL m lo canary ps tail bufbytes f' st' ms'. ltac2:(SecDiet.SzSec.closeP 'stderr_after__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition eprintf_s_genA__stmt : Prop := forall FMT fl (mk : list Z -> list (list Z)) fs,
    (forall sv, zlength sv <= 2^24 -> fmt_call_okD FMT fs [AStr sv] [PA_s sv] (mk sv)) ->
    zlength (str fs ++ [0]) = fl + 1 ->
    eprintf_s_stmt_o GIOA FMT fl mk.
  Section Sz13.
  Variables FMT fl mk fs ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo P str slack : ltac2:(SecDiet.SzSec.tyM 'eprintf_s_genA__stmt "vvvvhhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @FMT).
  Lemma eprintf_s_genA__body : ltac2:(SecDiet.SzSec.bodyP 'eprintf_s_genA__stmt "vvvvhhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros CALL EZ.
 intros SPD TOPLO -> -> -> MOF BY NZ LEN PAD MOP KEEP.
    pose proof (spd_factsA _ _ _ _ _ _ _ _ _ _ _ SPD) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SP47 & TOP47 & Etp & RSTK & RIMG & RIMGSH & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK, STDERR_FILE in *.
    sbl_pose_in SE. destruct SE as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    pose proof SEI as (CH2 & FD2 & BS2 & ND2 & NW2 & EOF2 & RB2 & SW2 & LB2).
    assert (WBN : f_wbuf (lc_stderr (ps_libc s)) = []).
    { destruct (f_wbuf (lc_stderr (ps_libc s))) eqn:E; [reflexivity|]. exfalso. rewrite BS2 in WBL. unfold zlength in WBL. cbn [Datatypes.length] in WBL. lia. }
    rewrite BS2, RB2, WBN in FC. rewrite BS2 in BUF. change (zlength (@nil Z)) with 0 in FC. rewrite RB2 in RP1. change (zlength (@nil Z)) with 0 in RP1.
    change (Z.to_nat 0) with 0%nat in BUF.
    assert (EL : zlength (map bv_unsigned str) = Z.of_nat (length str)) by (unfold zlength; rewrite length_map; reflexivity).
    pose proof (CALL (map bv_unsigned str) ltac:(rewrite EL; lia)) as (HF & P1 & PIECES & SMALL & HA & BYf & IOK).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL.
    destruct (str_arg_factsD L RNG s CL FB FL m lo (bv_unsigned sp) A_STDERR 232 (bv_unsigned sp - 464) 80 (bv_unsigned sp - 480) P str slack
                G LOA ltac:(lia) BY NZ LEN PAD MOP KEEP ltac:(unfold A_STDERR; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [AOK1 PWD1].
    destruct (pitems_facts fs [AStr (map bv_unsigned str)] [Z_to_bv 64 P] IOK eq_refl) as (FSTR & NOZ & EF & OKI).
    assert (PW : pwords_ok RNG lo sp m (pitems fs [AStr (map bv_unsigned str)] [Z_to_bv 64 P]) [Z_to_bv 64 P; a3; a4; a5; a6; a7]).
    { apply (pwords_ok_more RNG lo sp m _ [Z_to_bv 64 P] [a3; a4; a5; a6; a7]).
      apply pitems_words_fs; [exact IOK | apply Forall2_cons; [exact (PWD1 sp eq_refl) | apply Forall2_nil]]. }
    assert (SOFMT : sobj RNG m FMT (FMT + zlength (Fmt.str fs ++ [0]))) by (rewrite EZ; apply mobjA_sobj; [exact MOF | unfold zlength in *; lia]).
    destruct (gs_statics _ GSL _ _ _ _ _ _ _ G RIMG RIMGSH) as [SOS1 SOS2].
    unfold eprintf. apply implMG_rd_lc.
    eapply implMG_bind.
    { eapply implMG_leaf. apply implAM_implMG. unfold FPRINTF_ENTRY. change A_STDERR with 695952 in FC.
      eapply (fprintf_i_ubf_spec (St:=PS) RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 695952 A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail
                FMT lo (Fmt.str fs ++ [0]) (Z_to_bv 64 P) a3 a4 a5 a6 a7 [PA_s (map bv_unsigned str)]
                (mk (map bv_unsigned str)) _ canary (zb (Fmt.str fs)) (pitems fs [AStr (map bv_unsigned str)] [Z_to_bv 64 P]))
        with (rpos := rp) (flags := flags) (mode := mode).
      all: match goal with |- ?g => first
             [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact KLO | exact RSTK | exact RIMG | exact FSTR | exact NOZ | exact EF | exact OKI
             | reflexivity | exact FC | exact FLG
             | exact BS2 | exact NW2 | exact RB2 | exact WBN | exact CH2 | (right; exact FD2) | exact SW2
             | (apply BYf; exact MI)
             | (cbn [args_ok]; split; [exact AOK1 | exact I])
             | exact ST | exact SSP | exact MI | exact ENV | exact (gs_ckpf _ GSL _ _ _ _ _ _ _ G) | exact (gs_rng0 _ GSL _ _ _ _ _ _ _ G) | exact PW | exact SOFMT
             | (apply (gs_stack _ GSL _ _ _ _ _ _ _ lo (bv_unsigned sp - 112) G); (keep_hyps rc lo P str slack LOA sp LOB L TOPLO SP47; lia))
             | (apply (gs_rodata _ GSL _ _ _ _ _ _ _ 68460 68469 G RIMG RIMGSH); [left; (keep_hyps rc P str slack; lia) | (keep_hyps rc P str slack; lia)])
             | (eapply sobj_sub; [exact SOS1 | (keep_hyps rc lo P str slack GLO sp LOA LOB; lia) | (keep_hyps rc sp P str slack SP47; lia) | (keep_hyps rc P str slack; lia)])
             | (eapply rng_sub'; [exact RIMG | (keep_hyps rc P str slack; lia)])
             | (unfold iesafe; cbn [disjoint_from]; repeat split; (keep_hyps rc sp P str slack SP47 lo rp RP0 RP1; lia))
             | (left; lia)
             | (unfold FPRINTF_I_DEPTH, GLOBALS_TOP, A_STDERR_BUF in *; try destruct (f_wactive (lc_stderr (ps_libc s))); (keep_hyps rc sp lo P str slack LOB GLO; lia))
             | idtac "EPS-LEFT:" g ] end. }
    cbv beta. intros f' st' RNG' ms' [(-> & PO) LF].
    assert (LOS : lo <= bv_unsigned sp) by lia.
    destruct (stderr_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L RNG s CL FB FL m lo canary _ tail bufbytes f' st' ms' G LOA LOS GLN BUF PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & AG & G').
    unfold upd_lc. apply implMG_upd. apply evtF_done. unfold out_post_o.
    split; [apply fp_le_refl|].
    exists a0', m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. exact G'.
  Qed.
  End Sz13.
  Lemma eprintf_s_genA : ltac:(let t := eval cbv delta [eprintf_s_genA__stmt] in eprintf_s_genA__stmt in exact t).
  Proof using GL GSL. intros FMT fl mk fs CALL EZ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo P str slack. ltac2:(SecDiet.SzSec.closeP 'eprintf_s_genA__body "vvvvhhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Theorem eprintf_usage_proofA : eprintf_s_stmt_o GIOA FMT_USAGE 16 pieces_usage.
  Proof using GL GSL. exact (eprintf_s_genA FMT_USAGE 16 pieces_usage FS_USAGE call_usageD ltac:(vm_compute; reflexivity)). Qed.
  Theorem eprintf_cannot_open_proofA : eprintf_s_stmt_o GIOA FMT_CANNOT_OPEN 20 pieces_cannot_open.
  Proof using GL GSL. exact (eprintf_s_genA FMT_CANNOT_OPEN 20 pieces_cannot_open FS_CANNOT_OPEN call_cannot_openD ltac:(vm_compute; reflexivity)). Qed.
  Theorem eprintf_read_error_proofA : eprintf_s_stmt_o GIOA FMT_READ_ERROR 22 pieces_read_error.
  Proof using GL GSL. exact (eprintf_s_genA FMT_READ_ERROR 22 pieces_read_error FS_READ_ERROR call_read_errorD ltac:(vm_compute; reflexivity)). Qed.

  Definition eprintf_too_big_proofA__stmt : Prop := eprintf_i_stmt_o GIOA FMT_TOO_BIG 32 0x4000000 pieces_too_big.
  Section Sz17.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo : ltac2:(SecDiet.SzSec.tyM 'eprintf_too_big_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma eprintf_too_big_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'eprintf_too_big_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
 intros SPD TOPLO -> -> -> MOF.
    pose proof (spd_factsA _ _ _ _ _ _ _ _ _ _ _ SPD) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SP47 & TOP47 & Etp & RSTK & RIMG & RIMGSH & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK, STDERR_FILE in *.
    sbl_pose_in SE. destruct SE as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    pose proof SEI as (CH2 & FD2 & BS2 & ND2 & NW2 & EOF2 & RB2 & SW2 & LB2).
    assert (WBN : f_wbuf (lc_stderr (ps_libc s)) = []).
    { destruct (f_wbuf (lc_stderr (ps_libc s))) eqn:E; [reflexivity|]. exfalso. rewrite BS2 in WBL. unfold zlength in WBL. cbn [Datatypes.length] in WBL. lia. }
    rewrite BS2, RB2, WBN in FC. rewrite BS2 in BUF. change (zlength (@nil Z)) with 0 in FC. rewrite RB2 in RP1. change (zlength (@nil Z)) with 0 in RP1.
    change (Z.to_nat 0) with 0%nat in BUF.
    pose proof call_too_bigD as (HF & P1 & PIECES & SMALL & HA & BYf & IOK).
    pose proof (u32_facts 0x4000000) as U32.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL.
    destruct (pitems_facts FS_TOO_BIG [AInt 0x4000000] [Z_to_bv 64 0x4000000] IOK eq_refl) as (FSTR & NOZ & EF & OKI).
    assert (PW : pwords_ok RNG lo sp m (pitems FS_TOO_BIG [AInt 0x4000000] [Z_to_bv 64 0x4000000]) [Z_to_bv 64 0x4000000; a3; a4; a5; a6; a7]).
    { apply (pwords_ok_more RNG lo sp m _ [Z_to_bv 64 0x4000000] [a3; a4; a5; a6; a7]).
      apply pitems_words_fs; [exact IOK | apply Forall2_cons; [exact I | apply Forall2_nil]]. }
    assert (EZ : zlength (str FS_TOO_BIG ++ [0]) = 33) by (vm_compute; reflexivity).
    assert (SOFMT : sobj RNG m FMT_TOO_BIG (FMT_TOO_BIG + zlength (str FS_TOO_BIG ++ [0]))) by (rewrite EZ; apply mobjA_sobj; [exact MOF | lia]).
    destruct (gs_statics _ GSL _ _ _ _ _ _ _ G RIMG RIMGSH) as [SOS1 SOS2].
    assert (LOS : lo <= bv_unsigned sp) by lia.
    unfold eprintf. apply implMG_rd_lc.
    eapply implMG_bind.
    { eapply implMG_leaf. apply implAM_implMG. unfold FPRINTF_ENTRY. change A_STDERR with 695952 in FC.
      eapply (fprintf_i_ubf_spec (St:=PS) RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 695952 A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail
                FMT_TOO_BIG lo (str FS_TOO_BIG ++ [0]) (Z_to_bv 64 0x4000000) a3 a4 a5 a6 a7 [PA_u (u32 0x4000000)]
                pieces_too_big _ canary (zb (str FS_TOO_BIG)) (pitems FS_TOO_BIG [AInt 0x4000000] [Z_to_bv 64 0x4000000]))
        with (rpos := rp) (flags := flags) (mode := mode).
      all: match goal with |- ?g => first
             [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact KLO | exact RSTK | exact RIMG | exact FSTR | exact NOZ | exact EF | exact OKI
             | reflexivity | exact FC | exact FLG
             | exact BS2 | exact NW2 | exact RB2 | exact WBN | exact CH2 | (right; exact FD2) | exact SW2
             | (apply BYf; exact MI)
             | (cbn [args_ok]; split; [exact U32 | exact I])
             | exact ST | exact SSP | exact MI | exact ENV | exact (gs_ckpf _ GSL _ _ _ _ _ _ _ G) | exact (gs_rng0 _ GSL _ _ _ _ _ _ _ G) | exact PW | exact SOFMT
             | (apply (gs_stack _ GSL _ _ _ _ _ _ _ lo (bv_unsigned sp - 112) G); (keep_hyps rc lo LOA sp LOB L TOPLO SP47; lia))
             | (apply (gs_rodata _ GSL _ _ _ _ _ _ _ 68460 68469 G RIMG RIMGSH); [left; (keep_hyps rc; lia) | (keep_hyps rc; lia)])
             | (eapply sobj_sub; [exact SOS1 | (keep_hyps rc lo GLO sp LOA LOB; lia) | (keep_hyps rc sp SP47; lia) | (keep_hyps rc; lia)])
             | (eapply rng_sub'; [exact RIMG | (keep_hyps rc; lia)])
             | (unfold iesafe; cbn [disjoint_from]; repeat split; (keep_hyps rc sp SP47 lo rp RP0 RP1; lia))
             | (left; lia)
             | (unfold FPRINTF_I_DEPTH, GLOBALS_TOP, A_STDERR_BUF in *; try destruct (f_wactive (lc_stderr (ps_libc s))); (keep_hyps rc sp lo LOB GLO; lia))
             | idtac "EPI-LEFT:" g ] end. }
    cbv beta. intros f' st' RNG' ms' [(-> & PO) LF].
    destruct (stderr_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L RNG s CL FB FL m lo canary _ tail bufbytes f' st' ms' G LOA LOS GLN BUF PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & AG & G').
    unfold upd_lc. apply implMG_upd. apply evtF_done. unfold out_post_o.
    split; [apply fp_le_refl|].
    exists a0', m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. exact G'.
  Qed.
  End Sz17.
  Theorem eprintf_too_big_proofA : ltac:(let t := eval cbv delta [eprintf_too_big_proofA__stmt] in eprintf_too_big_proofA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo. ltac2:(SecDiet.SzSec.closeP 'eprintf_too_big_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition stderr_inv_fx__stmt : Prop := forall f f', stderr_inv f -> fx_inv f f' -> stderr_inv f'.
  Section Sz18.
  Variables f f' : ltac2:(SecDiet.SzSec.tyM 'stderr_inv_fx__stmt "vv" @f).
  Lemma stderr_inv_fx__body : ltac2:(SecDiet.SzSec.bodyP 'stderr_inv_fx__stmt "vv").
  Proof using Type. pin_using tt.
    intros (CH & FD & BS & NRD & NWR & EOF & RB & SW & LB) (E1 & E2 & E3 & E4 & E5 & E6 & WA & RB' & SW' & LB').
    unfold stderr_inv. rewrite E1, E2, E3, E4, E5, E6, RB', RB.
    split; [exact CH|]. split; [exact FD|]. split; [exact BS|]. split; [exact NRD|]. split; [exact NWR|]. split; [exact EOF|].
    split; [destruct (f_wactive f); reflexivity|].
    split; [destruct (f_stdoutw f'); [exfalso; pose proof (SW' eq_refl) as X; rewrite SW in X; discriminate X| reflexivity]|].
    destruct (f_lbf_nl f'); [exfalso; pose proof (LB' eq_refl) as X; rewrite LB in X; discriminate X| reflexivity].
  Qed.
  End Sz18.
  Lemma stderr_inv_fx : ltac:(let t := eval cbv delta [stderr_inv_fx__stmt] in stderr_inv_fx__stmt in exact t).
  Proof using Type. intros f f'. ltac2:(SecDiet.SzSec.closeP 'stderr_inv_fx__body "vv"). Qed.

  Definition efwrite_proofA__stmt : Prop := efwrite_stmt_o GIOA.
  Section Sz19.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo MSG bs : ltac2:(SecDiet.SzSec.tyM 'efwrite_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma efwrite_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'efwrite_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
 intros SPD -> -> -> -> HSRC ROD LEN1 MOS.
    pose proof (spd_factsA _ _ _ _ _ _ _ _ _ _ _ SPD) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SP47 & TOP47 & Etp & RSTK & RIMG & RIMGSH & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK, STDERR_FILE, DRV_RODATA_LO, DRV_RODATA_HI in *.
    sbl_pose_in SE. destruct SE as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP). sbl_subst_all.
    pose proof FLG as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    pose proof SEI as (CH2 & FD2 & BS2 & ND2 & NW2 & EOF2 & RB2 & SW2 & LB2).
    rewrite NW2 in FLw. rewrite BS2 in *.
    pose proof (bytes_at_bound _ _ _ _ HSRC) as BSRC.
    assert (WBN : f_wbuf (lc_stderr (ps_libc s)) = []).
    { destruct (f_wbuf (lc_stderr (ps_libc s))) eqn:E; [reflexivity|]. exfalso. unfold zlength in WBL. cbn [length] in WBL. lia. }
    pose proof MOS as (_ & _ & _ & RGS & _ & _).
    pose proof (mobjA_sobj _ _ _ _ MOS ltac:(lia)) as SOS.
    destruct (gs_statics _ GSL _ _ _ _ _ _ _ G RIMG RIMGSH) as [SOS1 SOS2].
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL.
    unfold efwrite. apply implMG_rd_lc.
    eapply implMG_bind.
    { apply implAM_implMG. unfold FWRITE_ENTRY. unfold A_STDERR, A_STDERR_BUF in *.
      eapply (fwrite_i_spec (St:=PS) RNG) with (f := lc_stderr (ps_libc s)) (s := map bv_unsigned bs) (S := MSG) (lo := lo) (canary := canary)
        (Fp := 695952) (flags := flags) (rpos := rp) (rend := rp + zlength (f_rbuf (lc_stderr (ps_libc s)))) (closefn := F_STDIO_CLOSE) (readfn := 0)
        (seekfn := F_STDIO_SEEK) (B := 6299840) (prev := 0) (next := 0) (mode := mode) (tail := tail) (bufbytes := bufbytes)
        (size := Z.of_nat (length bs)) (nmemb := 1).
      all: try unfold fcells in *. all: rewrite ?BS2 in *.
      all: unfold FWRITE_I_DEPTH, got_ssp, ssp_guard in *.
      all: unfold zlength in *; rewrite ?length_map.
      all: try first [ exact FC | exact BUF | exact BP | exact WB0 | exact ST | exact MI | exact SSP | exact FLsvb | exact FLw
                 | (change (map bv_unsigned bs) with (of_bytes bs); rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read.TwB.to_of_bytes; exact HSRC)
                 | (apply Forall_map; apply Forall_forall; intros b _; pose proof (bv_unsigned_in_range 8 b); unfold bv_modulus in *; cbn in *; (keep_hyps rc H hptr s bs b H0; lia))
                 | reflexivity | (f_equal; (keep_hyps rc H hptr s MSG bs ROD LEN1 sp lo LOB GLO SP47 WBL LOA KLO; lia)) | (rewrite CH2; right; exact FD2)
                 | exact KLO | exact ENV | exact SOS | exact RSTK | exact RGS | exact RIMG
                 | (eapply sobj_sub; [exact SOS2 | (keep_hyps rc H hptr s bs; lia) | (keep_hyps rc H hptr s bs; lia) | (keep_hyps rc H hptr s bs; lia)])
                 | (eapply rng_sub'; [exact RIMG | (keep_hyps rc H hptr s bs; lia)])
                 | (unfold iesafe; cbn [disjoint_from]; repeat split; (keep_hyps rc H hptr s bs; lia))
                 | (apply (sobj_appW RNG m); eapply sobj_sub; [exact SOS1 | (keep_hyps rc H hptr s bs; lia) | (keep_hyps rc H hptr s bs; lia) | (keep_hyps rc H hptr s bs; lia)])
                 | (apply (sobj_appW RNG m); eapply sobj_sub; [exact SOS2 | (keep_hyps rc H hptr s bs; lia) | (keep_hyps rc H hptr s bs; lia) | (keep_hyps rc H hptr s bs; lia)])
                 | (rewrite WBN; cbn [length Z.of_nat]; lia)
                 | lia | (left; lia) | (right; lia) | (right; repeat split; lia) | (split; lia) ]. }
    cbv beta. intros f' st' RNG' ms' (-> & -> & INV' & PO).
    sbl_pose_in PO. destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mode' & bufbytes' & m' & -> & MU & WM & MI' & ST' & FC' & BUF' & BP' & WBL' & SSP'). sbl_subst_all.
    unfold fx_W in MU. rewrite ?BS2 in MU.
    assert (FR' : FILE_R m' f' A_STDERR A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0).
    { pose proof INV' as (E1 & E2 & E3 & E4 & E5 & E6 & WA & RB & SW & LB).
      assert (RBN' : f_rbuf f' = []) by (rewrite RB, RB2; destruct (f_wactive (lc_stderr (ps_libc s))); reflexivity).
      rewrite RB2 in FC'.
      exists flags, mode', (if f_wactive (lc_stderr (ps_libc s)) then rp else 0), tail, bufbytes'.
      rewrite WA, RBN', E1, E3, BS2. unfold A_STDERR, A_STDERR_BUF.
      split. { unfold fcells in *. rewrite ?BS2 in FC'. destruct (f_wactive (lc_stderr (ps_libc s))); cbn [zlength length Z.of_nat] in FC' |- *; rewrite ?Z.add_0_r in FC' |- *; exact FC'. }
      split. { unfold flags_ok in *. rewrite E2, E4, E5, E6. rewrite NW2 in FLG |- *. exact FLG. }
      split; [rewrite ?BS2 in BUF'; exact BUF'|]. split; [exact BP'|]. split; [intros X; discriminate X|]. split; [rewrite ?BS2 in WBL'; exact WBL'|].
      split; [intros X; exfalso; exact (X eq_refl)|]. destruct (f_wactive (lc_stderr (ps_libc s))); unfold zlength in RP |- *; cbn [length Z.of_nat]; (split; [lia| split; [lia| exact (proj2 (proj2 RP))]]). }
    destruct (GIOA_stderr_step L RNG s CL FB FL m m' f' lo (bv_unsigned sp) G LOA ltac:(lia) MU WM FR' (stderr_inv_fx _ _ SEI INV')) as [G' AG].
    unfold upd_lc. apply implMG_upd. apply evtF_done. unfold out_post_o.
    split; [apply fp_le_refl|].
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. exact G'.
  Qed.
  End Sz19.
  Theorem efwrite_proofA : ltac:(let t := eval cbv delta [efwrite_proofA__stmt] in efwrite_proofA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo MSG bs. ltac2:(SecDiet.SzSec.closeP 'efwrite_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueDrv.
End TwB.
