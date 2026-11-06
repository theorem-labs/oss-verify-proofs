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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim PcapPrelim PcapTypes PcapPure Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_chkD__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfHandleA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardNgB__B3P.
From Stdlib Require String.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad Fmt StdioCore Stdio Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA LibcKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_modelA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_ngchk_fsegA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_chkD__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfHandleA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ngblk_ok (RNG : footprint) (SPA P Fb bP kPF : Z) : Prop :=
  rng RNG P 680 /\ rng RNG (shad P) (nshad 680) /\ rng RNG SPA 152 /\ rng RNG Fb 64
  /\ (P mod 16 = 0)%Z /\ (0 <= bP <= 1)%Z /\ (P + 680 <= 2147446784 + bP * 140737479966720)%Z /\ (17594333495296 * bP <= P)%Z /\ (6303744 <= P)%Z
  /\ (P + 680 <= SPA)%Z /\ (Fb + 64 <= SPA)%Z /\ (0 < Fb)%Z /\ (SPA + 152 <= 2^47)%Z /\ (17594333495296 <= SPA)%Z
  /\ (0 <= kPF <= 1)%Z /\ (P + 680 <= Fb + kPF * 18446744073709551616)%Z /\ (Fb + 64 <= P + (1 - kPF) * 18446744073709551616)%Z.

Lemma ngblk_ok_fp_le : forall RNG RNG' SPA P Fb bP kPF, fp_le RNG RNG' -> ngblk_ok RNG SPA P Fb bP kPF -> ngblk_ok RNG' SPA P Fb bP kPF.
Proof.
  intros RNG RNG' SPA P Fb bP kPF FP (A1 & A2 & A3 & A4 & REST).
  split; [eapply rng_fp_le; eassumption|]. split; [eapply rng_fp_le; eassumption|]. split; [eapply rng_fp_le; eassumption|]. split; [eapply rng_fp_le; eassumption| exact REST].
Qed.

(* [comment removed for export] *)
Local Ltac qfold := lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end.
Section CANSEC1. Context {rc : runConstT}.
Section FillSeg.
  Variables (gp tp t0 t1 t2 s0 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (RNG : footprint) (SPA P Fb EB ERR FA : Z) (bP kPF : Z).
  Variables (sw : bool) (TL : Z) (j : list byte).
  Hypothesis PBK : ngblk_ok RNG SPA P Fb bP kPF.
  Hypothesis TLR : (28 <= TL <= 1048576)%Z.
  Local Notation BS0 := (if 2048 <? TL then TL else 2048)%Z.
  Local Notation REGS xra xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs7 xs8 :=
    (mkR xra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
         (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) xs5 (Z_to_bv 64 FA) xs7 xs8
         (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6).
  Local Notation B8 := (C8 (Z_to_bv 64 0)).
  Local Notation B4 := (C4 (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Definition fill_segA__stmt : Prop := forall (m : mem) (ra a1 a2 a3 a4 a5 a6 a7 : word) (j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 : list byte),
    mem_inv asegs m -> unpoisoned m P (P + 680) ->
    rw_cells asegs m SPA [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 8 j8; CB 8 j9; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb)] ->
    rw_cells asegs m P (ngcells0 P) -> rw_cells asegs m (P + 648) (ng_cells ng0 0 pad0) ->
    evtF asegs RNG (fun ms' => exists a1' a2' a3' m',
        ms' = MS (REGS (Z_to_bv 64 0x8b14c) (Z_to_bv 64 BS0) a1' a2' a3' (Z_to_bv 64 (P + 648)) (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 (P + 156))
                       (Z_to_bv 64 (Fb + 48)) (Z_to_bv 64 P) (Z_to_bv 64 TL))
                 F (Z_to_bv 64 0x56178) fc None m' (seg_rom asegs)
        /\ munch [(SPA, SPA + 128); (P, P + 680)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ unpoisoned m' P (P + 680)
        /\ rw_cells asegs m' SPA [CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 (Z.shiftr (P + 156) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 156)); CB 8 j5;
                                   C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 (P + 648)); CB 8 j9;
                                   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb)]
        /\ rw_cells asegs m' P (ngcells P B8 (C4 (Z_to_bv 64 BS0)) B8 (C4 (Z_to_bv 64 (Z.b2z sw))) B4 B4 B4 B4 B4 B4 B8)
        /\ rw_cells asegs m' (P + 648) (ng_cells (mkNg 1000000 0 0 0 []) 0 pad0))
      (MS (REGS ra (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Fb + 48)) (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 TL)) F (Z_to_bv 64 0x8b058) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables m ra a1 a2 a3 a4 a5 a6 a7 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 : ltac2:(SecDiet.SzSec.tyM 'fill_segA__stmt "vvvvvvvvvvvvvvvvvvv" @m).
  #[using="bP kPF PBK TLR"] Lemma fill_segA__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segA__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI PUNP FRA CELLS NG.
 qfold.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof (munch_refl [(SPA, SPA + 128); (P, P + 680)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold ngcells0, ngcells in CELLS. unfold ng_cells, ng0 in NG. cbn [ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size] in NG.
    zstep. ck0 PUNP; ck_go.
    zstep.
    zstep. ck0 PUNP; ck_go.
    zstep. zstep. zstep. if_true.
    zstep. zstep. ck0 PUNP; ck_go.
    zstep.
    zstep. zstep. zstep. zstep.
    ck0_at PUNP (P + 156)%Z; ck_go.
    zstep. zstep.
    zstep. zstep. zstep. zstep.
    zstep.
    unfold bv_ltu. rewrite (unsigned_lit 2048), (unsigned_lit TL) by lia.
    destruct (2048 <? TL)%Z eqn:ELT; cbv iota.
    2: zstep.
    all: zstep; zstep; zstep; zstep.
    all: ck0 PUNP; ck_go.
    all: zstep; zstep; zstep; zstep.
    all: apply evtF_done; do 4 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [assumption|].
    all: split; [assumption|]; split; [unfold ngcells; assumption|].
    all: unfold ng_cells; cbn [ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size]; assumption.
  Qed.
  End Sz2.
  #[using="bP kPF PBK TLR"] Lemma fill_segA : ltac:(let t := eval cbv delta [fill_segA__stmt] in fill_segA__stmt in exact t).
  Proof. intros m ra a1 a2 a3 a4 a5 a6 a7 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9. ltac2:(SecDiet.SzSec.closeP 'fill_segA__body "vvvvvvvvvvvvvvvvvvv"). Qed.

End FillSeg.

Section FillSeg2.
  Variables (gp tp t0 t1 t2 s0 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (RNG : footprint) (SPA P Fb EB ERR FA : Z) (bP kPF : Z).
  Variables (sw : bool) (TL BS0 : Z) (j : list byte).
  Hypothesis PBK : ngblk_ok RNG SPA P Fb bP kPF.
  Hypothesis TLR : (28 <= TL <= 1048576)%Z.
  Hypothesis BSR : (2048 <= BS0 <= 1048576)%Z.   (* [comment removed for export] *)
  Local Notation REGS xra xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs7 xs8 :=
    (mkR xra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
         (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) xs5 (Z_to_bv 64 FA) xs7 xs8
         (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6).
  Local Notation B8 := (C8 (Z_to_bv 64 0)).
  Local Notation B4 := (C4 (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Variables (B bU kUF kPU : Z).
  Hypothesis BBK : rng RNG B BS0 /\ rng RNG (shad B) (nshad BS0) /\ (B mod 16 = 0)%Z /\ (0 <= bU <= 1)%Z /\ (B + BS0 <= 2147446784 + bU * 140737479966720)%Z
                   /\ (17594333495296 * bU <= B)%Z /\ (6303744 <= B)%Z /\ (B + BS0 <= SPA)%Z
                   /\ (0 <= kUF <= 1)%Z /\ (B + BS0 <= Fb + kUF * 18446744073709551616)%Z /\ (Fb + 64 <= B + (1 - kUF) * 18446744073709551616)%Z
                   /\ (0 <= kPU <= 1)%Z /\ (P + 680 <= B + kPU * 18446744073709551616)%Z /\ (B + BS0 <= P + (1 - kPU) * 18446744073709551616)%Z.

  Definition fill_segB__stmt : Prop := forall (m : mem) (a1 a2 a3 a4 a5 a6 a7 : word) (j0 j1 j2 j5 j9 b0 b1 b2 : list byte) (fpre fmid fpost : list byte) (k0 k1 k2 tlw flagw : word),
    mem_inv asegs m -> unpoisoned m P (P + 680) -> unpoisoned m B (B + BS0) ->
    rw_cells asegs m SPA [CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 (Z.shiftr (P + 156) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 156)); CB 8 j5;
                          C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 (P + 648)); CB 8 j9;
                          C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb)] ->
    rw_cells asegs m Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; C4 tlw; CB 12 fmid; C4 (Z_to_bv 64 439041101); CB 4 fpost; C8 flagw] ->
    rw_cells asegs m P (ngcells P B8 (C4 (Z_to_bv 64 BS0)) B8 (C4 (Z_to_bv 64 (Z.b2z sw))) B4 B4 B4 B4 B4 B4 B8) ->
    rw_cells asegs m (P + 648) (ng_cells (mkNg 1000000 0 0 0 []) 0 pad0) ->
    rw_cells asegs m B [CB 4 b0; CB 4 b1; CB 4 b2] ->
    evtF asegs RNG (fun ms' => exists a5' a6' a7' m',
        ms' = MS (REGS (Z_to_bv 64 0x8b210) (Z_to_bv 64 FA) (Z_to_bv 64 (B + 12)) (Z_to_bv 64 (TL + -12)) (Z_to_bv 64 1) (Z_to_bv 64 EB) a5' a6' a7'
                       (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL))
                 F (Z_to_bv 64 0x8ba38) fc None m' (seg_rom asegs)
        /\ munch [(SPA, SPA + 128); (P, P + 680); (B, B + 12)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ unpoisoned m' P (P + 680) /\ unpoisoned m' B (B + BS0)
        /\ rw_cells asegs m' SPA (ngc_spill P EB Fb j)
        /\ rw_cells asegs m' P (ngcells P B8 (C4 (Z_to_bv 64 BS0)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 (Z.b2z sw))) B4 B4 B4 B4 B4 B4 B8)
        /\ rw_cells asegs m' (P + 648) (ng_cells (mkNg 1000000 16777216 0 0 []) 0 pad0)
        /\ rw_cells asegs m' B [C4 (Z_to_bv 64 168627466); C4 (Z_to_bv 64 TL); C4 (Z_to_bv 64 439041101)])
      (MS (REGS (Z_to_bv 64 0x8b14c) (Z_to_bv 64 B) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Fb + 48)) (Z_to_bv 64 P) (Z_to_bv 64 TL)) F (Z_to_bv 64 0x8b14c) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables m a1 a2 a3 a4 a5 a6 a7 j0 j1 j2 j5 j9 b0 b1 b2 fpre fmid fpost k0 k1 k2 tlw flagw : ltac2:(SecDiet.SzSec.tyM 'fill_segB__stmt "vvvvvvvvvvvvvvvvvvvvvvvv" @m).
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segB__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segB__stmt "vvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI PUNP BUNP FRA FRC CELLS NG HB.
 qfold.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof BBK as (BRNG & BRSH & B16 & bUr & bUhi & bUlo & bUimg & BSP & kUFr & kUF1 & kUF2 & kPUr & kPU1 & kPU2).
    pose proof (munch_refl [(SPA, SPA + 128); (P, P + 680); (B, B + 12)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold ngcells in CELLS. unfold ng_cells in NG. cbn [ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size] in NG.
    zstep. zstep. ck0 PUNP; ck_go.
    zstep. zstep. zstep. zstep.
    if_false_by (eqb_lits_false B 0 ltac:(lia) ltac:(lia) ltac:(lia)).
    zstep. zstep.
    replace (P + 648 + 8)%Z with (P + 656)%Z by lia.
    zstep. zstep. zstep.
    ck0_at PUNP (P + 656)%Z; ck_go.
    zstep. zstep. zstep.
    ck0 BUNP; ck_go.
    zstep. zstep. zstep. zstep.
    ck0 BUNP; ck_go.
    zstep. zstep. zstep.
    ck0 BUNP; ck_go.
    do 8 zstep. zstep.
    apply evtF_done. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [unfold ngc_spill; assumption|]. split; [unfold ngcells; assumption|].
    split; [unfold ng_cells; cbn [ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size]; assumption| assumption].
  Qed.
  End Sz3.
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segB : ltac:(let t := eval cbv delta [fill_segB__stmt] in fill_segB__stmt in exact t).
  Proof. intros m a1 a2 a3 a4 a5 a6 a7 j0 j1 j2 j5 j9 b0 b1 b2 fpre fmid fpost k0 k1 k2 tlw flagw. ltac2:(SecDiet.SzSec.closeP 'fill_segB__body "vvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Local Notation HCELLS maj min := (ngcells P B8 (C4 (Z_to_bv 64 BS0)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 (Z.b2z sw))) maj min B4 B4 B4 B4 B8).

  Definition fill_segC_nat__stmt : Prop := forall (m : mem) (ra a0 a1 a2 a3 a4 a5 a6 a7 : word) (g0 g1 g2 g3 : Z),
    sw = false ->
    mem_inv asegs m -> unpoisoned m P (P + 680) -> unpoisoned m B (B + BS0) ->
    rw_cells asegs m SPA (ngc_spill P EB Fb j) -> rw_cells asegs m P (HCELLS B4 B4) ->
    rw_cells asegs m (B + 12) [C2 (Z_to_bv 64 (g0 + 256 * g1)); C2 (Z_to_bv 64 (g2 + 256 * g3))] ->
    (0 <= g0 < 256)%Z -> (0 <= g1 < 256)%Z -> (0 <= g2 < 256)%Z -> (0 <= g3 < 256)%Z ->
    evtF asegs RNG (fun ms' => exists a2' a4',
        ms' = MS (REGS ra (Z_to_bv 64 (B + 14)) (Z_to_bv 64 P) a2' (Z_to_bv 64 (g0 + 256 * g1)) a4' a5 (Z_to_bv 64 EB) (Z_to_bv 64 0)
                       (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL))
                 F (Z_to_bv 64 0x8b2a0) fc None m (seg_rom asegs))
      (MS (REGS ra a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL)) F (Z_to_bv 64 0x8b218) fc None m (seg_rom asegs)).
  Section Sz4.
  Variables m ra a0 a1 a2 a3 a4 a5 a6 a7 g0 g1 g2 g3 : ltac2:(SecDiet.SzSec.tyM 'fill_segC_nat__stmt "vvvvvvvvvvvvvv" @m).
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segC_nat__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segC_nat__stmt "vvvvvvvvvvvvvv").
  Proof.
 intros SW MI PUNP BUNP FRA CELLS HV G0 G1 G2 G3. subst sw.
 qfold.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof BBK as (BRNG & BRSH & B16 & bUr & bUhi & bUlo & bUimg & BSP & kUFr & kUF1 & kUF2 & kPUr & kPU1 & kPU2).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold ngc_spill in FRA. unfold ngcells in CELLS. cbn [Z.b2z] in CELLS.
    ck0_at PUNP (P + 56)%Z.
    zstep. zstep. zstep. if_false.
    ck0 BUNP.
    do 8 zstep. zstep. if_false.
    zstep. zstep. zstep.
    replace (sx32 z64) with z64 by (vm_compute; reflexivity). if_true.
    rewrite (zx16_lit (g0 + 256 * g1)) by lia.
    zstep. zstep.
    rewrite (Z.mod_small (g0 + 256 * g1) 65536) by lia.
    apply evtF_done. do 2 eexists. reflexivity.
  Qed.
  End Sz4.
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segC_nat : ltac:(let t := eval cbv delta [fill_segC_nat__stmt] in fill_segC_nat__stmt in exact t).
  Proof. intros m ra a0 a1 a2 a3 a4 a5 a6 a7 g0 g1 g2 g3. ltac2:(SecDiet.SzSec.closeP 'fill_segC_nat__body "vvvvvvvvvvvvvv"). Qed.

  Definition fill_segC_sw__stmt : Prop := forall (m : mem) (ra a0 a1 a2 a3 a4 a5 a6 a7 : word) (g0 g1 g2 g3 : Z),
    sw = true ->
    mem_inv asegs m -> unpoisoned m P (P + 680) -> unpoisoned m B (B + BS0) ->
    rw_cells asegs m SPA (ngc_spill P EB Fb j) -> rw_cells asegs m P (HCELLS B4 B4) ->
    rw_cells asegs m (B + 12) [C2 (Z_to_bv 64 (g0 + 256 * g1)); C2 (Z_to_bv 64 (g2 + 256 * g3))] ->
    (0 <= g0 < 256)%Z -> (0 <= g1 < 256)%Z -> (0 <= g2 < 256)%Z -> (0 <= g3 < 256)%Z ->
    evtF asegs RNG (fun ms' => exists a2' a4' m',
        ms' = MS (REGS ra (Z_to_bv 64 (B + 14)) (Z_to_bv 64 P) a2' (Z_to_bv 64 (g1 + 256 * g0)) a4' a5 (Z_to_bv 64 EB) (Z_to_bv 64 0)
                       (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL))
                 F (Z_to_bv 64 0x8b2a0) fc None m' (seg_rom asegs)
        /\ munch [(B + 12, B + 16)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (B + 12) [C2 (Z_to_bv 64 (g1 + 256 * g0)); C2 (Z_to_bv 64 (g3 + 256 * g2))])
      (MS (REGS ra a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL)) F (Z_to_bv 64 0x8b218) fc None m (seg_rom asegs)).
  Section Sz5.
  Variables m ra a0 a1 a2 a3 a4 a5 a6 a7 g0 g1 g2 g3 : ltac2:(SecDiet.SzSec.tyM 'fill_segC_sw__stmt "vvvvvvvvvvvvvv" @m).
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segC_sw__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segC_sw__stmt "vvvvvvvvvvvvvv").
  Proof.
 intros SW MI PUNP BUNP FRA CELLS HV G0 G1 G2 G3. subst sw.
 qfold.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof BBK as (BRNG & BRSH & B16 & bUr & bUhi & bUlo & bUimg & BSP & kUFr & kUF1 & kUF2 & kPUr & kPU1 & kPU2).
    pose proof (munch_refl [(B + 12, B + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold ngc_spill in FRA. unfold ngcells in CELLS. cbn [Z.b2z] in CELLS.
    ck0_at PUNP (P + 56)%Z.
    zstep. zstep. zstep. if_false.
    ck0 BUNP.
    do 8 zstep. zstep. if_false.
    zstep. zstep. zstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity). if_false.
    zstep. zstep. if_false.
    do 5 zstep.
    ck0_at BUNP (B + 14)%Z.
    zstep. zstep. zstep. if_false.
    zstep. zstep. zstep. if_false.
    do 4 zstep.
    zstep. zstep.
    rewrite (unsigned_zx16 (g0 + 256 * g1)) by lia.
    rewrite (Z.shiftl_mul_pow2 (g0 + 256 * g1) 8), (Z.shiftr_div_pow2 (g0 + 256 * g1) 8) by lia.
    replace ((g0 + 256 * g1) / 2^8)%Z with g1 by (Z.div_mod_to_equations; lia).
    rewrite (Z.mod_small ((g0 + 256 * g1) * 2^8)) by lia.
    rewrite (lor_high_low (g0 + 256 * g1) g1 8) by lia.
    replace (((g0 + 256 * g1) * 2 ^ 8 + g1) mod 65536)%Z with (g1 + 256 * g0)%Z by (Z.div_mod_to_equations; lia).
    apply evtF_done. do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    eapply rw_cells_recell; [exact HV | cbn; repeat split; exact Logic.I |].
    cbn [cells_bytes cbytes app].
    rewrite (le2_lit g1 g0), (le2_lit g3 g2) by lia.
    rewrite (le2_of_val _ g1 g0 g1); [| lia | lia | lia | apply (swap16_valA _ g0 g1); [lia|lia| apply unsigned_zx16; lia]].
    rewrite (le2_of_val _ g3 g2 g3); [| lia | lia | lia | apply (swap16_valA _ g2 g3); [lia|lia| apply unsigned_zx16; lia]].
    reflexivity.
  Qed.
  End Sz5.
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segC_sw : ltac:(let t := eval cbv delta [fill_segC_sw__stmt] in fill_segC_sw__stmt in exact t).
  Proof. intros m ra a0 a1 a2 a3 a4 a5 a6 a7 g0 g1 g2 g3. ltac2:(SecDiet.SzSec.closeP 'fill_segC_sw__body "vvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fill_segD_ok__stmt : Prop := forall (m : mem) (ra a2 a4 a5 : word) (MIN : Z),
    (MIN = 0 \/ MIN = 2)%Z ->
    mem_inv asegs m -> unpoisoned m P (P + 680) -> unpoisoned m B (B + BS0) ->
    rw_cells asegs m SPA (ngc_spill P EB Fb j) -> rw_cells asegs m P (HCELLS B4 B4) ->
    rw_cells asegs m (B + 12) [C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 MIN)] ->
    evtF asegs RNG (fun ms' => exists a0' a1' a2' a3' a4' a5' m',
        ms' = MS (REGS ra a0' a1' a2' a3' a4' a5' (Z_to_bv 64 EB) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 2) (Z_to_bv 64 6))
                 F (Z_to_bv 64 0x8b31c) fc None m' (seg_rom asegs)
        /\ munch [(P, P + 648)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' P (HCELLS (C4 (Z_to_bv 64 1)) (C4 (Z_to_bv 64 MIN))))
      (MS (REGS ra (Z_to_bv 64 (B + 14)) (Z_to_bv 64 P) a2 (Z_to_bv 64 1) a4 a5 (Z_to_bv 64 EB) (Z_to_bv 64 0) (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL))
          F (Z_to_bv 64 0x8b2a0) fc None m (seg_rom asegs)).
  Section Sz6.
  Variables m ra a2 a4 a5 MIN : ltac2:(SecDiet.SzSec.tyM 'fill_segD_ok__stmt "vvvvvv" @m).
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segD_ok__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segD_ok__stmt "vvvvvv").
  Proof.
 intros HMIN MI PUNP BUNP FRA CELLS HV.
 qfold.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof BBK as (BRNG & BRSH & B16 & bUr & bUhi & bUlo & bUimg & BSP & kUFr & kUF1 & kUF2 & kPUr & kPU1 & kPU2).
    pose proof (munch_refl [(P, P + 648)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold ngc_spill in FRA. unfold ngcells in CELLS.
    zstep. zstep. if_false.
    ck0 BUNP; ck_go.
    zstep. rewrite (zx16_lit MIN) by lia.
    zstep. zstep. zstep.
    replace (Z.lor MIN 2) with 2%Z by (destruct HMIN as [-> | ->]; reflexivity). if_false.
    zstep. ck0 PUNP; ck_go.
    zstep. zstep. zstep.
    ck0 PUNP; ck_go.
    zstep.
    ck0_at PUNP (P + 156)%Z.
    zstep. zstep. zstep. if_false.
    zstep. zstep.
    zstep. zstep. zstep.
    apply evtF_done. do 7 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    unfold ngcells. exact CELLS.
  Qed.
  End Sz6.
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segD_ok : ltac:(let t := eval cbv delta [fill_segD_ok__stmt] in fill_segD_ok__stmt in exact t).
  Proof. intros m ra a2 a4 a5 MIN. ltac2:(SecDiet.SzSec.closeP 'fill_segD_ok__body "vvvvvv"). Qed.

  Definition fill_segD_bad__stmt : Prop := forall (m : mem) (ra a2 a4 a5 : word) (MAJ MIN : Z),
    (0 <= MAJ < 65536)%Z -> (0 <= MIN < 65536)%Z -> ~ (MAJ = 1 /\ (MIN = 0 \/ MIN = 2))%Z ->
    mem_inv asegs m -> unpoisoned m P (P + 680) -> unpoisoned m B (B + BS0) ->
    rw_cells asegs m (B + 12) [C2 (Z_to_bv 64 MAJ); C2 (Z_to_bv 64 MIN)] ->
    evtF asegs RNG (fun ms' => exists a5',
        ms' = MS (REGS (Z_to_bv 64 0x8b414) (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 0x221c0) (Z_to_bv 64 MAJ) (Z_to_bv 64 MIN) a5' (Z_to_bv 64 EB) (Z_to_bv 64 0)
                       (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL))
                 F (Z_to_bv 64 0x444b0) fc None m (seg_rom asegs))
      (MS (REGS ra (Z_to_bv 64 (B + 14)) (Z_to_bv 64 P) a2 (Z_to_bv 64 MAJ) a4 a5 (Z_to_bv 64 EB) (Z_to_bv 64 0) (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL))
          F (Z_to_bv 64 0x8b2a0) fc None m (seg_rom asegs)).
  Section Sz7.
  Variables m ra a2 a4 a5 MAJ MIN : ltac2:(SecDiet.SzSec.tyM 'fill_segD_bad__stmt "vvvvvvv" @m).
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segD_bad__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segD_bad__stmt "vvvvvvv").
  Proof.
 intros MAJR MINR HBAD MI PUNP BUNP HV.
 qfold.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof BBK as (BRNG & BRSH & B16 & bUr & bUhi & bUlo & bUimg & BSP & kUFr & kUF1 & kUF2 & kPUr & kPU1 & kPU2).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    assert (TAIL : forall (b2 b4 b5 : word),
      evtF asegs RNG (fun ms' => exists a5',
          ms' = MS (REGS (Z_to_bv 64 0x8b414) (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 0x221c0) (Z_to_bv 64 MAJ) (Z_to_bv 64 MIN) a5' (Z_to_bv 64 EB) (Z_to_bv 64 0)
                         (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL))
                   F (Z_to_bv 64 0x444b0) fc None m (seg_rom asegs))
        (MS (REGS ra (Z_to_bv 64 (B + 14)) (Z_to_bv 64 P) b2 (Z_to_bv 64 MAJ) b4 b5 (Z_to_bv 64 EB) (Z_to_bv 64 0) (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL))
            F (Z_to_bv 64 0x8b3ec) fc None m (seg_rom asegs))).
    { intros b2 b4 b5.
      ck0 BUNP; ck_go.
      zstep. rewrite (zx16_lit MIN) by lia.
      do 4 zstep. zstep.
      apply evtF_done. eexists. reflexivity. }
    zstep. zstep.
    destruct (Z.eq_dec MAJ 1) as [EM|NM].
    - subst MAJ. if_false.
      ck0 BUNP; ck_go.
      zstep. rewrite (zx16_lit MIN) by lia.
      zstep. zstep. zstep.
      assert (CND : negb (bv_eqb (Z_to_bv 64 (Z.lor MIN 2)) (Z_to_bv 64 2)) = true).
      { pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_sfpcapng_chkE.lor2_range MIN MINR) as LR. unfold bv_eqb. rewrite (unsigned_lit (Z.lor MIN 2)), (unsigned_lit 2) by lia.
        rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_sfpcapng_chkE.lor2_eqb2 MIN) by lia. apply Bool.negb_true_iff. apply Bool.orb_false_iff.
        split; apply Z.eqb_neq; intros E; apply HBAD; split; [reflexivity| left; exact E| reflexivity| right; exact E]. }
      rewrite CND. cbv iota.
      apply TAIL.
    - rewrite (eqb_lits_false MAJ 1 ltac:(lia) ltac:(lia) NM). cbn [negb]. cbv iota.
      apply TAIL.
  Qed.
  End Sz7.
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segD_bad : ltac:(let t := eval cbv delta [fill_segD_bad__stmt] in fill_segD_bad__stmt in exact t).
  Proof. intros m ra a2 a4 a5 MAJ MIN. ltac2:(SecDiet.SzSec.closeP 'fill_segD_bad__body "vvvvvvv"). Qed.
End FillSeg2.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardNgB__B3P.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardNgB__B3P.UbGuardNgB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ngblk_ok (RNG : footprint) (SPA P Fb bP kPF : Z) : Prop :=
  rng RNG P 680 /\ rng RNG (shad P) (nshad 680) /\ rng RNG SPA 152 /\ rng RNG Fb 64
  /\ (P mod 16 = 0)%Z /\ (0 <= bP <= 1)%Z /\ (P + 680 <= 2147446784 + bP * 140737479966720)%Z /\ (17594333495296 * bP <= P)%Z /\ (6307840 <= P)%Z
  /\ (P + 680 <= SPA)%Z /\ (Fb + 64 <= SPA)%Z /\ (0 < Fb)%Z /\ (SPA + 152 <= 2^47)%Z /\ (17594333495296 <= SPA)%Z
  /\ (0 <= kPF <= 1)%Z /\ (P + 680 <= Fb + kPF * 18446744073709551616)%Z /\ (Fb + 64 <= P + (1 - kPF) * 18446744073709551616)%Z.

Lemma ngblk_ok_fp_le : forall RNG RNG' SPA P Fb bP kPF, fp_le RNG RNG' -> ngblk_ok RNG SPA P Fb bP kPF -> ngblk_ok RNG' SPA P Fb bP kPF.
Proof.
  intros RNG RNG' SPA P Fb bP kPF FP (A1 & A2 & A3 & A4 & REST).
  split; [eapply rng_fp_le; eassumption|]. split; [eapply rng_fp_le; eassumption|]. split; [eapply rng_fp_le; eassumption|]. split; [eapply rng_fp_le; eassumption| exact REST].
Qed.

(* [comment removed for export] *)
Local Ltac qfold := lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end.
Section CANSEC1. Context {rc : runConstT}.
Section FillSeg.
  Variables (gp tp t0 t1 t2 s0 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (RNG : footprint) (SPA P Fb EB ERR FA : Z) (bP kPF : Z).
  Variables (sw : bool) (TL : Z) (j : list byte).
  Hypothesis PBK : ngblk_ok RNG SPA P Fb bP kPF.
  Hypothesis TLR : (28 <= TL <= 1048576)%Z.
  Local Notation BS0 := (if 2048 <? TL then TL else 2048)%Z.
  Local Notation REGS xra xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs7 xs8 :=
    (mkR xra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
         (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 FA) xs5 xs7 xs8
         (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6).
  Local Notation B8 := (C8 (Z_to_bv 64 0)).
  Local Notation B4 := (C4 (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Definition fill_segA__stmt : Prop := forall (m : mem) (ra a1 a2 a3 a4 a5 a6 a7 : word) (j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 : list byte),
    mem_inv asegs m -> unpoisoned m P (P + 680) ->
    rw_cells asegs m SPA [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 8 j8; CB 8 j9; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb)] ->
    rw_cells asegs m P (ngcells0 P) -> rw_cells asegs m (P + 648) (ng_cells ng0 0 pad0) ->
    evtF asegs RNG (fun ms' => exists a1' a2' a3' m',
        ms' = MS (REGS (Z_to_bv 64 0x8b0c4) (Z_to_bv 64 BS0) a1' a2' a3' (Z_to_bv 64 (P + 648)) (Z_to_bv 64 (P + 156)) a6 a7   (* [comment removed for export] *)
                       (Z_to_bv 64 (Fb + 48)) (Z_to_bv 64 P) (Z_to_bv 64 TL))
                 F (Z_to_bv 64 0x561e0) fc None m' (seg_rom asegs)
        /\ munch [(SPA, SPA + 128); (P, P + 680)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ unpoisoned m' P (P + 680)
        /\ rw_cells asegs m' SPA [CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 (Z.shiftr (P + 156) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 156)); CB 8 j5;
                                   C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 (P + 648)); CB 8 j9;
                                   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb)]
        /\ rw_cells asegs m' P (ngcells P B8 (C4 (Z_to_bv 64 BS0)) B8 (C4 (Z_to_bv 64 (Z.b2z sw))) B4 B4 B4 B4 B4 B4 B8)
        /\ rw_cells asegs m' (P + 648) (ng_cells (mkNg 1000000 0 0 0 []) 0 pad0))
      (MS (REGS ra (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Fb + 48)) (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 TL)) F (Z_to_bv 64 0x8afb0) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables m ra a1 a2 a3 a4 a5 a6 a7 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 : ltac2:(SecDiet.SzSec.tyM 'fill_segA__stmt "vvvvvvvvvvvvvvvvvvv" @m).
  #[using="bP kPF PBK TLR"] Lemma fill_segA__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segA__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI PUNP FRA CELLS NG.
 qfold.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof (munch_refl [(SPA, SPA + 128); (P, P + 680)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold ngcells0, ngcells in CELLS. unfold ng_cells, ng0 in NG. cbn [ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size] in NG.
    (* [comment removed for export] *)
    zstep. ub_al 7%Z ltac:(al16 P16). zstep. if_false.
    zstep. zstep. zstep. zstep. zstep. ck0_at PUNP (P + 56)%Z; ck_go.
    zstep. zstep. ck0 PUNP; ck_go.
    do 4 zstep. if_false. zstep. if_false.
    ub_null.
    zstep. ub_al 7%Z ltac:(al16 P16). zstep. if_false.
    do 3 zstep.
    ck0 PUNP; ck_go.
    zstep. zstep. zstep. zstep.
    zstep. ck0_at PUNP (P + 156)%Z; ck_go.
    zstep. zstep. zstep. zstep. zstep.
    zstep.
    unfold bv_ltu. rewrite (unsigned_lit 2048), (unsigned_lit TL) by lia.
    destruct (2048 <? TL)%Z eqn:ELT; cbv iota.
    2: zstep.
    all: zstep; zstep.
    all: ck0 PUNP; ck_go.
    all: zstep; zstep; zstep; zstep.
    all: apply evtF_done; do 4 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [assumption|].
    all: split; [assumption|]; split; [unfold ngcells; assumption|].
    all: unfold ng_cells; cbn [ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size]; assumption.
  Qed.
  End Sz2.
  #[using="bP kPF PBK TLR"] Lemma fill_segA : ltac:(let t := eval cbv delta [fill_segA__stmt] in fill_segA__stmt in exact t).
  Proof. intros m ra a1 a2 a3 a4 a5 a6 a7 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9. ltac2:(SecDiet.SzSec.closeP 'fill_segA__body "vvvvvvvvvvvvvvvvvvv"). Qed.

End FillSeg.

Section FillSeg2.
  Variables (gp tp t0 t1 t2 s0 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (RNG : footprint) (SPA P Fb EB ERR FA : Z) (bP kPF : Z).
  Variables (sw : bool) (TL BS0 : Z) (j : list byte).
  Hypothesis PBK : ngblk_ok RNG SPA P Fb bP kPF.
  Hypothesis TLR : (28 <= TL <= 1048576)%Z.
  Hypothesis BSR : (2048 <= BS0 <= 1048576)%Z.   (* [comment removed for export] *)
  Local Notation REGS xra xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs7 xs8 :=
    (mkR xra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
         (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 FA) xs5 xs7 xs8
         (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6).
  Local Notation B8 := (C8 (Z_to_bv 64 0)).
  Local Notation B4 := (C4 (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Variables (B bU kUF kPU : Z).
  Hypothesis BBK : rng RNG B BS0 /\ rng RNG (shad B) (nshad BS0) /\ (B mod 16 = 0)%Z /\ (0 <= bU <= 1)%Z /\ (B + BS0 <= 2147446784 + bU * 140737479966720)%Z
                   /\ (17594333495296 * bU <= B)%Z /\ (6307840 <= B)%Z /\ (B + BS0 <= SPA)%Z
                   /\ (0 <= kUF <= 1)%Z /\ (B + BS0 <= Fb + kUF * 18446744073709551616)%Z /\ (Fb + 64 <= B + (1 - kUF) * 18446744073709551616)%Z
                   /\ (0 <= kPU <= 1)%Z /\ (P + 680 <= B + kPU * 18446744073709551616)%Z /\ (B + BS0 <= P + (1 - kPU) * 18446744073709551616)%Z.

  Definition fill_segB__stmt : Prop := forall (m : mem) (a1 a2 a3 a4 a5 a6 a7 : word) (j0 j1 j2 j5 j9 b0 b1 b2 : list byte) (fpre fmid fpost : list byte) (k0 k1 k2 tlw flagw : word),
    mem_inv asegs m -> unpoisoned m P (P + 680) -> unpoisoned m B (B + BS0) ->
    rw_cells asegs m SPA [CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 (Z.shiftr (P + 156) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 156)); CB 8 j5;
                          C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 (P + 648)); CB 8 j9;
                          C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb)] ->
    rw_cells asegs m Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; C4 tlw; CB 12 fmid; C4 (Z_to_bv 64 439041101); CB 4 fpost; C8 flagw] ->
    rw_cells asegs m P (ngcells P B8 (C4 (Z_to_bv 64 BS0)) B8 (C4 (Z_to_bv 64 (Z.b2z sw))) B4 B4 B4 B4 B4 B4 B8) ->
    rw_cells asegs m (P + 648) (ng_cells (mkNg 1000000 0 0 0 []) 0 pad0) ->
    rw_cells asegs m B [CB 4 b0; CB 4 b1; CB 4 b2] ->
    evtF asegs RNG (fun ms' => exists a5' a6' a7' m',
        ms' = MS (REGS (Z_to_bv 64 0x8b1b0) (Z_to_bv 64 FA) (Z_to_bv 64 (B + 12)) (Z_to_bv 64 (TL + -12)) (Z_to_bv 64 1) (Z_to_bv 64 EB) a5' a6' a7'
                       (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL))
                 F (Z_to_bv 64 0x8b9d4) fc None m' (seg_rom asegs)
        /\ munch [(SPA, SPA + 128); (P, P + 680); (B, B + 12)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ unpoisoned m' P (P + 680) /\ unpoisoned m' B (B + BS0)
        /\ rw_cells asegs m' SPA (ngc_spill P EB Fb j)
        /\ rw_cells asegs m' P (ngcells P B8 (C4 (Z_to_bv 64 BS0)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 (Z.b2z sw))) B4 B4 B4 B4 B4 B4 B8)
        /\ rw_cells asegs m' (P + 648) (ng_cells (mkNg 1000000 16777216 0 0 []) 0 pad0)
        /\ rw_cells asegs m' B [C4 (Z_to_bv 64 168627466); C4 (Z_to_bv 64 TL); C4 (Z_to_bv 64 439041101)])
      (MS (REGS (Z_to_bv 64 0x8b0c4) (Z_to_bv 64 B) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Fb + 48)) (Z_to_bv 64 P) (Z_to_bv 64 TL)) F (Z_to_bv 64 0x8b0c4) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables m a1 a2 a3 a4 a5 a6 a7 j0 j1 j2 j5 j9 b0 b1 b2 fpre fmid fpost k0 k1 k2 tlw flagw : ltac2:(SecDiet.SzSec.tyM 'fill_segB__stmt "vvvvvvvvvvvvvvvvvvvvvvvv" @m).
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segB__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segB__stmt "vvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI PUNP BUNP FRA FRC CELLS NG HB.
 qfold.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof BBK as (BRNG & BRSH & B16 & bUr & bUhi & bUlo & bUimg & BSP & kUFr & kUF1 & kUF2 & kPUr & kPU1 & kPU2).
    pose proof (munch_refl [(SPA, SPA + 128); (P, P + 680); (B, B + 12)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold ngcells in CELLS. unfold ng_cells in NG. cbn [ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size] in NG.
    zstep. zstep. ck0 PUNP; ck_go.
    zstep. zstep. zstep. zstep.
    if_false_by (eqb_lits_false B 0 ltac:(lia) ltac:(lia) ltac:(lia)).
    (* [comment removed for export] *)
    zstep. zstep. zstep. ub_al 7%Z ltac:(al16 P16). zstep. if_false.
    zstep.
    replace (P + 648 + 8)%Z with (P + 656)%Z by lia.
    zstep. zstep. zstep.
    ck0_at PUNP (P + 656)%Z; ck_go.
    (* [comment removed for export] *)
    do 5 zstep. zstep. ub_ovf.
    zstep. ub_al 3%Z ltac:(al16 B16). zstep. if_false.
    ck0 BUNP; ck_go.
    zstep. zstep. zstep. zstep.
    ck0 BUNP; ck_go.
    (* [comment removed for export] *)
    zstep. replace (Z.land (B + 8) 4) with 0%Z by (symmetry; apply land4_0; apply (mod8_of_16 _ _ B16); reflexivity).
    zstep. zstep. if_false.
    ck0 BUNP; ck_go.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ub_ovf.
    do 7 zstep. zstep.
    apply evtF_done. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [unfold ngc_spill; assumption|]. split; [unfold ngcells; assumption|].
    split; [unfold ng_cells; cbn [ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size]; assumption| assumption].
  Qed.
  End Sz3.
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segB : ltac:(let t := eval cbv delta [fill_segB__stmt] in fill_segB__stmt in exact t).
  Proof. intros m a1 a2 a3 a4 a5 a6 a7 j0 j1 j2 j5 j9 b0 b1 b2 fpre fmid fpost k0 k1 k2 tlw flagw. ltac2:(SecDiet.SzSec.closeP 'fill_segB__body "vvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Local Notation HCELLS maj min := (ngcells P B8 (C4 (Z_to_bv 64 BS0)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 (Z.b2z sw))) maj min B4 B4 B4 B4 B8).

  Definition fill_segC_nat__stmt : Prop := forall (m : mem) (ra a0 a1 a2 a3 a4 a5 a6 a7 : word) (g0 g1 g2 g3 : Z),
    sw = false ->
    mem_inv asegs m -> unpoisoned m P (P + 680) -> unpoisoned m B (B + BS0) ->
    rw_cells asegs m SPA (ngc_spill P EB Fb j) -> rw_cells asegs m P (HCELLS B4 B4) ->
    rw_cells asegs m (B + 12) [C2 (Z_to_bv 64 (g0 + 256 * g1)); C2 (Z_to_bv 64 (g2 + 256 * g3))] ->
    (0 <= g0 < 256)%Z -> (0 <= g1 < 256)%Z -> (0 <= g2 < 256)%Z -> (0 <= g3 < 256)%Z ->
    evtF asegs RNG (fun ms' => exists a2' a4' a7',   (* [comment removed for export] *)
        ms' = MS (REGS ra (Z_to_bv 64 (B + 14)) (Z_to_bv 64 P) a2' (Z_to_bv 64 (g0 + 256 * g1)) a4' a5 (Z_to_bv 64 0) a7'
                       (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL))
                 F (Z_to_bv 64 0x8b248) fc None m (seg_rom asegs))
      (MS (REGS ra a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL)) F (Z_to_bv 64 0x8b1b8) fc None m (seg_rom asegs)).
  Section Sz4.
  Variables m ra a0 a1 a2 a3 a4 a5 a6 a7 g0 g1 g2 g3 : ltac2:(SecDiet.SzSec.tyM 'fill_segC_nat__stmt "vvvvvvvvvvvvvv" @m).
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segC_nat__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segC_nat__stmt "vvvvvvvvvvvvvv").
  Proof.
 intros SW MI PUNP BUNP FRA CELLS HV G0 G1 G2 G3. subst sw.
 qfold.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof BBK as (BRNG & BRSH & B16 & bUr & bUhi & bUlo & bUimg & BSP & kUFr & kUF1 & kUF2 & kPUr & kPU1 & kPU2).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold ngc_spill in FRA. unfold ngcells in CELLS. cbn [Z.b2z] in CELLS.
    (* [comment removed for export] *)
    ck0_at PUNP (P + 56)%Z.
    zstep. zstep. zstep. if_false.
    do 6 zstep. zstep.
    replace (sx32 z64) with z64 by (vm_compute; reflexivity). if_true.
    ck0_at BUNP (B + 12)%Z.
    zstep. zstep. zstep. if_false.
    zstep.
    rewrite (zx16_lit (g0 + 256 * g1)) by lia.
    rewrite ?(Z.mod_small (g0 + 256 * g1) 65536) by lia.
    apply evtF_done. do 3 eexists. reflexivity.
  Qed.
  End Sz4.
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segC_nat : ltac:(let t := eval cbv delta [fill_segC_nat__stmt] in fill_segC_nat__stmt in exact t).
  Proof. intros m ra a0 a1 a2 a3 a4 a5 a6 a7 g0 g1 g2 g3. ltac2:(SecDiet.SzSec.closeP 'fill_segC_nat__body "vvvvvvvvvvvvvv"). Qed.

  Definition fill_segC_sw__stmt : Prop := forall (m : mem) (ra a0 a1 a2 a3 a4 a5 a6 a7 : word) (g0 g1 g2 g3 : Z),
    sw = true ->
    mem_inv asegs m -> unpoisoned m P (P + 680) -> unpoisoned m B (B + BS0) ->
    rw_cells asegs m SPA (ngc_spill P EB Fb j) -> rw_cells asegs m P (HCELLS B4 B4) ->
    rw_cells asegs m (B + 12) [C2 (Z_to_bv 64 (g0 + 256 * g1)); C2 (Z_to_bv 64 (g2 + 256 * g3))] ->
    (0 <= g0 < 256)%Z -> (0 <= g1 < 256)%Z -> (0 <= g2 < 256)%Z -> (0 <= g3 < 256)%Z ->
    evtF asegs RNG (fun ms' => exists a2' a4' a7' m',
        ms' = MS (REGS ra (Z_to_bv 64 (B + 14)) (Z_to_bv 64 P) a2' (Z_to_bv 64 (g1 + 256 * g0)) a4' a5 (Z_to_bv 64 0) a7'
                       (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL))
                 F (Z_to_bv 64 0x8b248) fc None m' (seg_rom asegs)
        /\ munch [(B + 12, B + 16)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (B + 12) [C2 (Z_to_bv 64 (g1 + 256 * g0)); C2 (Z_to_bv 64 (g3 + 256 * g2))])
      (MS (REGS ra a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL)) F (Z_to_bv 64 0x8b1b8) fc None m (seg_rom asegs)).
  Section Sz5.
  Variables m ra a0 a1 a2 a3 a4 a5 a6 a7 g0 g1 g2 g3 : ltac2:(SecDiet.SzSec.tyM 'fill_segC_sw__stmt "vvvvvvvvvvvvvv" @m).
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segC_sw__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segC_sw__stmt "vvvvvvvvvvvvvv").
  Proof.
 intros SW MI PUNP BUNP FRA CELLS HV G0 G1 G2 G3. subst sw.
 qfold.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof BBK as (BRNG & BRSH & B16 & bUr & bUhi & bUlo & bUimg & BSP & kUFr & kUF1 & kUF2 & kPUr & kPU1 & kPU2).
    pose proof (munch_refl [(B + 12, B + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold ngc_spill in FRA. unfold ngcells in CELLS. cbn [Z.b2z] in CELLS.
    (* [comment removed for export] *)
    ck0_at PUNP (P + 56)%Z.
    zstep. zstep. zstep. if_false.
    do 6 zstep. zstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity). if_false.
    zstep. zstep.
    ck0_at BUNP (B + 12)%Z.
    zstep. zstep. if_false.
    zstep. zstep. zstep. if_false.
    do 5 zstep.
    ck0_at BUNP (B + 14)%Z.
    zstep. zstep. zstep. if_false.
    zstep. zstep. zstep. if_false.
    do 4 zstep.
    ck0_at BUNP (B + 12)%Z.
    zstep. zstep. zstep. if_false.
    zstep.
    rewrite (unsigned_zx16 (g0 + 256 * g1)) by lia.
    rewrite (Z.shiftl_mul_pow2 (g0 + 256 * g1) 8), (Z.shiftr_div_pow2 (g0 + 256 * g1) 8) by lia.
    replace ((g0 + 256 * g1) / 2^8)%Z with g1 by (Z.div_mod_to_equations; lia).
    rewrite (Z.mod_small ((g0 + 256 * g1) * 2^8)) by lia.
    rewrite (lor_high_low (g0 + 256 * g1) g1 8) by lia.
    replace (zx16 (Z_to_bv 64 ((g0 + 256 * g1) * 2 ^ 8 + g1))) with (Z_to_bv 64 (g1 + 256 * g0) : word)
      by (unfold zx16; rewrite unsigned_lit by lia; f_equal; Z.div_mod_to_equations; lia).
    apply evtF_done. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    eapply rw_cells_recell; [exact HV | cbn; repeat split; exact Logic.I |].
    cbn [cells_bytes cbytes app].
    rewrite (le2_lit g1 g0), (le2_lit g3 g2) by lia.
    rewrite (le2_of_val _ g1 g0 g1); [| lia | lia | lia | apply (swap16_valA _ g0 g1); [lia|lia| apply unsigned_zx16; lia]].
    rewrite (le2_of_val _ g3 g2 g3); [| lia | lia | lia | apply (swap16_valA _ g2 g3); [lia|lia| apply unsigned_zx16; lia]].
    reflexivity.
  Qed.
  End Sz5.
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segC_sw : ltac:(let t := eval cbv delta [fill_segC_sw__stmt] in fill_segC_sw__stmt in exact t).
  Proof. intros m ra a0 a1 a2 a3 a4 a5 a6 a7 g0 g1 g2 g3. ltac2:(SecDiet.SzSec.closeP 'fill_segC_sw__body "vvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fill_segD_ok__stmt : Prop := forall (m : mem) (ra a2 a4 a5 a7 : word) (MIN : Z),   (* [comment removed for export] *)
    (MIN = 0 \/ MIN = 2)%Z ->
    mem_inv asegs m -> unpoisoned m P (P + 680) -> unpoisoned m B (B + BS0) ->
    rw_cells asegs m SPA (ngc_spill P EB Fb j) -> rw_cells asegs m P (HCELLS B4 B4) ->
    rw_cells asegs m (B + 12) [C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 MIN)] ->
    evtF asegs RNG (fun ms' => exists a0' a1' a2' a3' a4' a5' m',
        ms' = MS (REGS ra a0' a1' a2' a3' a4' a5' (Z_to_bv 64 0) a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 2) (Z_to_bv 64 6))
                 F (Z_to_bv 64 0x8b2c4) fc None m' (seg_rom asegs)
        /\ munch [(P, P + 648)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' P (HCELLS (C4 (Z_to_bv 64 1)) (C4 (Z_to_bv 64 MIN))))
      (MS (REGS ra (Z_to_bv 64 (B + 14)) (Z_to_bv 64 P) a2 (Z_to_bv 64 1) a4 a5 (Z_to_bv 64 0) a7 (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL))
          F (Z_to_bv 64 0x8b248) fc None m (seg_rom asegs)).
  Section Sz6.
  Variables m ra a2 a4 a5 a7 MIN : ltac2:(SecDiet.SzSec.tyM 'fill_segD_ok__stmt "vvvvvvv" @m).
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segD_ok__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segD_ok__stmt "vvvvvvv").
  Proof.
 intros HMIN MI PUNP BUNP FRA CELLS HV.
 qfold.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof BBK as (BRNG & BRSH & B16 & bUr & bUhi & bUlo & bUimg & BSP & kUFr & kUF1 & kUF2 & kPUr & kPU1 & kPU2).
    pose proof (munch_refl [(P, P + 648)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold ngc_spill in FRA. unfold ngcells in CELLS.
    zstep. zstep. if_false.
    ck0 BUNP; ck_go.
    zstep. rewrite (zx16_lit MIN) by lia.
    zstep. zstep. zstep.
    replace (Z.lor MIN 2) with 2%Z by (destruct HMIN as [-> | ->]; reflexivity). if_false.
    zstep. ck0 PUNP; ck_go.
    zstep. zstep. zstep.
    ck0 PUNP; ck_go.
    zstep.
    ck0_at PUNP (P + 156)%Z.
    zstep. zstep. zstep. if_false.
    zstep.   (* [comment removed for export] *)
    zstep. zstep. zstep.
    apply evtF_done. do 7 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    unfold ngcells. exact CELLS.
  Qed.
  End Sz6.
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segD_ok : ltac:(let t := eval cbv delta [fill_segD_ok__stmt] in fill_segD_ok__stmt in exact t).
  Proof. intros m ra a2 a4 a5 a7 MIN. ltac2:(SecDiet.SzSec.closeP 'fill_segD_ok__body "vvvvvvv"). Qed.

  Definition fill_segD_bad__stmt : Prop := forall (m : mem) (ra a2 a4 a5 a7 : word) (MAJ MIN : Z),
    (0 <= MAJ < 65536)%Z -> (0 <= MIN < 65536)%Z -> ~ (MAJ = 1 /\ (MIN = 0 \/ MIN = 2))%Z ->
    mem_inv asegs m -> unpoisoned m P (P + 680) -> unpoisoned m B (B + BS0) ->
    rw_cells asegs m SPA (ngc_spill P EB Fb j) ->   (* [comment removed for export] *)
    rw_cells asegs m (B + 12) [C2 (Z_to_bv 64 MAJ); C2 (Z_to_bv 64 MIN)] ->
    evtF asegs RNG (fun ms' => exists a5',
        ms' = MS (REGS (Z_to_bv 64 0x8b598) (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 0x221c0) (Z_to_bv 64 MAJ) (Z_to_bv 64 MIN) a5' (Z_to_bv 64 0) a7
                       (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL))
                 F (Z_to_bv 64 0x44518) fc None m (seg_rom asegs))
      (MS (REGS ra (Z_to_bv 64 (B + 14)) (Z_to_bv 64 P) a2 (Z_to_bv 64 MAJ) a4 a5 (Z_to_bv 64 0) a7 (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL))
          F (Z_to_bv 64 0x8b248) fc None m (seg_rom asegs)).
  Section Sz7.
  Variables m ra a2 a4 a5 a7 MAJ MIN : ltac2:(SecDiet.SzSec.tyM 'fill_segD_bad__stmt "vvvvvvvv" @m).
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segD_bad__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segD_bad__stmt "vvvvvvvv").
  Proof.
 intros MAJR MINR HBAD MI PUNP BUNP FRA HV. unfold ngc_spill in FRA.
 qfold.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof BBK as (BRNG & BRSH & B16 & bUr & bUhi & bUlo & bUimg & BSP & kUFr & kUF1 & kUF2 & kPUr & kPU1 & kPU2).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    assert (TAIL : forall (b2 b4 b5 : word),
      evtF asegs RNG (fun ms' => exists a5',
          ms' = MS (REGS (Z_to_bv 64 0x8b598) (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 0x221c0) (Z_to_bv 64 MAJ) (Z_to_bv 64 MIN) a5' (Z_to_bv 64 0) a7
                         (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL))
                   F (Z_to_bv 64 0x44518) fc None m (seg_rom asegs))
        (MS (REGS ra (Z_to_bv 64 (B + 14)) (Z_to_bv 64 P) b2 (Z_to_bv 64 MAJ) b4 b5 (Z_to_bv 64 0) a7 (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL))
            F (Z_to_bv 64 0x8b570) fc None m (seg_rom asegs))).
    { intros b2 b4 b5.
      ck0 BUNP; ck_go.
      zstep. rewrite (zx16_lit MIN) by lia.
      do 4 zstep. zstep.
      apply evtF_done. eexists. reflexivity. }
    zstep. zstep.
    destruct (Z.eq_dec MAJ 1) as [EM|NM].
    - subst MAJ. if_false.
      ck0 BUNP; ck_go.
      zstep. rewrite (zx16_lit MIN) by lia.
      zstep. zstep. zstep.
      assert (CND : negb (bv_eqb (Z_to_bv 64 (Z.lor MIN 2)) (Z_to_bv 64 2)) = true).
      { pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_sfpcapng_chkE.lor2_range MIN MINR) as LR. unfold bv_eqb. rewrite (unsigned_lit (Z.lor MIN 2)), (unsigned_lit 2) by lia.
        rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_sfpcapng_chkE.lor2_eqb2 MIN) by lia. apply Bool.negb_true_iff. apply Bool.orb_false_iff.
        split; apply Z.eqb_neq; intros E; apply HBAD; split; [reflexivity| left; exact E| reflexivity| right; exact E]. }
      rewrite CND. cbv iota.
      apply TAIL.
    - rewrite (eqb_lits_false MAJ 1 ltac:(lia) ltac:(lia) NM). cbn [negb]. cbv iota.
      apply TAIL.
  Qed.
  End Sz7.
  #[using="bP kPF PBK BSR bU kUF kPU BBK"] Lemma fill_segD_bad : ltac:(let t := eval cbv delta [fill_segD_bad__stmt] in fill_segD_bad__stmt in exact t).
  Proof. intros m ra a2 a4 a5 a7 MAJ MIN. ltac2:(SecDiet.SzSec.closeP 'fill_segD_bad__body "vvvvvvvv"). Qed.
End FillSeg2.
End CANSEC1.
End TwB.
End F_ngchk_fsegA.

(* [comment removed for export] *)
Module F_ngchk_okA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfHandleA F_ngchk_modelA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
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
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (Z.shiftl _ (32)%Z) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
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
Section NgcOk.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).

  Definition ngc_ok_tail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 r20 r24 t3 t4 t5 t6 : word)
      (qs qb : hptr) (P B ba : Z) (sw : bool) (BS0 MINOR : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) (I : Z)
      (pad bs e j : list byte) (ccs fcs : list cell) (k0 k1 k2 : word),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngi_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m f qs P sw BS0 MINOR
            RNGx sx mm qb B ba bufdata sg i I pad bs e j ccs fcs k0 k1 k2 ->
    (16 <= Z.of_nat (length bufdata))%Z -> (1 <= BS0 <= 2^21)%Z -> (0 <= MINOR < 2^16)%Z ->
    implMG RNGx (ngc_done (prims HO FO sites) 0 8 (ngc_p f qs sw BS0 MINOR qb ba bufdata sg i)) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 r20 (Z_to_bv 64 (B + 12)) (Z_to_bv 64 (B + 8)) (Z_to_bv 64 (Z.shiftr (B + 8) 3)) r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b608) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 r20 r24 t3 t4 t5 t6 qs qb P B ba sw BS0 MINOR bufdata sg i I pad bs e j ccs fcs k0 k1 k2 : ltac2:(SecDiet.SzSec.tyM 'ngc_ok_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_ok_tail__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_ok_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET LT2DLT ADJSNAP MAXSNAP.
 intros CTX NGI LENB BS0R MINR.
    (nd_pre NGI 21%nat; intros INV FRA FCUR Hccs FRC Hfcs HE HEB CELLS NG5 UTS MB IC IS HIF BUF5 PFX LBA BAR BSB GRD; nd_post).
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    (* [comment removed for export] *)
    assert (HinP : In (qs, P, 680%Z) ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg)) by (left; reflexivity).
    assert (HinB : In (qb, B, ba) ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg)) by (right; left; reflexivity).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ndP__; nd_pre ndP__ 6%nat; intros (PBAND & _ & PTOP & P16) P0 PUNP PRNG PSRNG _; nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinB)) as ndP__; nd_pre ndP__ 6%nat; intros (BBAND & _ & BTOP & B16) B0 BUNP BRNG BSRNG _; nd_post).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0, PUNP, PRNG, PSRNG, BBAND, BTOP, B16, B0, BUNP, BRNG, BSRNG.
    band_ind PBAND bP. band_ind BBAND bU.
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) 4%nat; intros kMP kMPr kMP1 kMP2; nd_post).
    cbn [cb_addr cb_size fst snd] in kMP1, kMP2.
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) 4%nat; intros kEP kEPr kEP1 kEP2; nd_post).
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) 4%nat; intros kBP kBPr kBP1 kBP2; nd_post).
    cbn [cb_addr cb_size fst snd] in kEP1, kEP2, kBP1, kBP2.
    (nd_pre (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ (qs, P, 680%Z) (NGFR Fb) G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP) ltac:(left; reflexivity) ltac:(cbn; lia)) 4%nat; intros kPF kPFr kPF1 kPF2; nd_post).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2.
    assert (EPB : (qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg = pcap_blocks (ngc_p f qs sw BS0 MINOR qb ba bufdata sg i) P B I)
      by (unfold pcap_blocks, psize, is_ng; cbn [pc_priv pc_self pc_buffer pc_bufalloc ngc_p]; destruct i; reflexivity).
    destruct (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G EPB) as (APB & API).
    unfold psize, is_ng in APB, API. cbn [pc_priv pc_bufalloc ngc_p] in APB, API. unfold PCAP_NG_SF_TOTAL in APB, API.
    assert (ITOP : forall q, i = Some q -> (0 < I /\ I + 40 * ng_ifaces_size sg <= ATOP)%Z).
    { intros q ->. cbn [IBLK] in G.
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ (q, I, 40 * ng_ifaces_size sg)%Z G ltac:(apply in_or_app; left; apply in_or_app; right; right; right; left; reflexivity)) as ndP__; nd_pre ndP__ 3%nat; intros (_ & _ & IT & _) I0 _; nd_post).
      cbn [cb_addr cb_size fst snd] in IT, I0. lia. }
    (* [comment removed for export] *)
    (nd_pre (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.split_at8 bufdata 8 ltac:(lia)) 12%nat; intros pre8 l0 l1 r0 r1 n0 n1 n2 n3 post Ebuf Lpre8; nd_post).
    assert (GX : (0 <= l0 < 256 /\ 0 <= l1 < 256 /\ 0 <= r0 < 256 /\ 0 <= r1 < 256 /\ 0 <= n0 < 256 /\ 0 <= n1 < 256 /\ 0 <= n2 < 256 /\ 0 <= n3 < 256)%Z).
    { rewrite Ebuf in GRD. apply Forall_app in GRD as [_ GB].
      pose proof (Forall_inv GB) as X0. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X1. apply Forall_inv_tail in GB.
      pose proof (Forall_inv GB) as X2. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X3. apply Forall_inv_tail in GB.
      pose proof (Forall_inv GB) as X4. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X5. apply Forall_inv_tail in GB.
      pose proof (Forall_inv GB) as X6. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X7.
      cbv beta in X0, X1, X2, X3, X4, X5, X6, X7. lia. }
    (nd_pre GX 8%nat; intros L0 L1 R0' R1' N0 N1 N2 N3; nd_post).
    assert (GLT : get_le16 bufdata 8 = (l0 + 256 * l1)%Z) by (rewrite Ebuf; replace 8%Z with (Z.of_nat (length pre8)) by lia; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.get_le16_at).
    assert (GSN : get_le32 bufdata 12 = le4val n0 n1 n2 n3).
    { rewrite Ebuf. change (pre8 ++ l0 :: l1 :: r0 :: r1 :: n0 :: n1 :: n2 :: n3 :: post) with (pre8 ++ [l0; l1; r0; r1] ++ n0 :: n1 :: n2 :: n3 :: post).
      rewrite app_assoc. replace 12%Z with (Z.of_nat (length (pre8 ++ [l0; l1; r0; r1]))) by (rewrite length_app; cbn; lia). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_ai.get_le32_at. }
    pose proof PFX as PFX0. rewrite Ebuf in PFX0.
    change (pre8 ++ l0 :: l1 :: r0 :: r1 :: n0 :: n1 :: n2 :: n3 :: post) with (pre8 ++ [l0; l1; r0; r1; n0; n1; n2; n3] ++ post) in PFX0.
    (nd_pre (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pfx_decomp pre8 [l0; l1; r0; r1; n0; n1; n2; n3] post bs PFX0) 3%nat; intros bsr Ebs PFXr; nd_post). cbn [map] in Ebs.
    pose proof BUF5 as BX. rewrite Ebs in BX.
    assert (Lbsr : (length pre8 + 8 + length bsr = Z.to_nat ba)%nat).
    { pose proof (proj1 (proj1 BX)) as WF. cbn in WF. rewrite !length_app, length_map in WF. cbn in WF. lia. }
    pose proof (rw_cells_recell _ _ _ [CB (length pre8) (map b8 pre8); C2 (Z_to_bv 64 (l0 + 256 * l1)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (length bsr) bsr] BX
                  ltac:(cbn; rewrite length_map; repeat split; first [reflexivity | lia])
                  ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit, le4_lit by lia; rewrite !app_nil_r; cbn [app]; reflexivity)) as BX'.
    destruct (rw_cells_cut _ _ _ 1 BX') as [_ BX2]. destruct (rw_cells_cut _ _ _ 3 BX2) as [HIDB _]. clear BX BX' BX2.
    cbn [firstn skipn cells_size csize Nat.add app] in HIDB. rewrite Lpre8 in HIDB.
    lazymatch type of HIDB with rw_cells _ _ ?A _ => replace A with (B + 8)%Z in HIDB by lia end.
    (* [comment removed for export] *)
    unfold ngc_done. cbn [e_fret prims]. cbn [pc_bufdata pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_swapped pc_version_major pc_version_minor ng_of ngc_p pc_priv ng_ifaces_ptr_of].
    rewrite GLT. replace (8 + 4)%Z with 12%Z by reflexivity. rewrite GSN, MB, UTS.
    set (lt := linktype_to_dlt (l0 + 256 * l1)). set (snap := pcapint_adjust_snapshot lt (le4val n0 n1 n2 n3)).
    pose proof (linktype_to_dlt_range (l0 + 256 * l1) ltac:(lia)) as LTR. fold lt in LTR.
    pose proof (adjust_snapshot_range lt (le4val n0 n1 n2 n3) ltac:(unfold le4val; lia)) as SNR. fold snap in SNR. unfold INT_MAX in SNR.
    set (msl := max_snaplen_for_dlt lt). pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_chkB.max_snaplen_le3 lt) as MSR. fold msl in MSR.
    unfold MAX_BLOCKSIZE_FOR_SNAPLEN, INITIAL_MAX_BLOCKSIZE.
    (* [comment removed for export] *)
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as (RT & _).
    assert (HGlt : In (LT_TABLE, 28%Z) client_globals) by (unfold client_globals, LT_TABLE; repeat (first [left; reflexivity | right])).
    (pose proof (gia_global_mobjA _ _ _ GL _ _ _ _ _ _ _ _ _ G HGlt RIMG RISH) as ndP__; nd_pre ndP__ 4%nat; intros _ _ LTUNP _; nd_post).
    unfold ngc_hcells, ngcells in CELLS. unfold ng_cells in NG5. rewrite MB, UTS in NG5. unfold INITIAL_MAX_BLOCKSIZE in NG5.
    unfold ngc_spill in FRA.
    hide FCUR. hide FRC. hide HE. hide HEB. hide BUF5. hide FR. hide MGc. hide SHC.
    pose proof (munch_refl [(SPA - 16, SPA); (P, P + 680)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    (* [comment removed for export] *)
    ck0_at BUNP (B + 8)%Z.
    zstep. zstep. zstep. if_false.
    zstep.
    rewrite (zx16_lit (l0 + 256 * l1)) by lia.
    zstep.
    (* [comment removed for export] *)
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (LT2DLT _ spa) with (lo := lo) (lt := (l0 + 256 * l1)%Z);
        [ exact MI | rewrite Hspa; exact ST | rewrite Hspa; lia | lia | exact RT | exact LTUNP
        | rewrite Hspa; eapply rng_sub'; [exact RSPW| lia] | exact RIMG | exact RISH | reflexivity | lia ]
      | ].
    cbv beta. intros ms' PO. unfold leaf_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MUc WMc MIc STc ndR2__; nd_post; revert ndR2__; intros ->).
    rewrite Hspa in *.
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end; clear MUc WMc.
    try clear ST. rename STc into ST. try clear MI. rename MIc into MI.
    replace (ret_pc (Z_to_bv 64 0x8b61c)) with (Z_to_bv 64 0x8b61c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    fold lt. clear Hspa. subst spa.
    (* [comment removed for export] *)
    zstep. zstep.
    ck0 PUNP; ck_go.
    zstep.
    (* [comment removed for export] *)
    ck0 BUNP; ck_go.
    zstep. rewrite (sx32_s32 (le4val n0 n1 n2 n3)) by (unfold le4val; lia).
    zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (ADJSNAP _ spa) with (lo := lo) (lt := lt) (snaplen := le4val n0 n1 n2 n3);
        [ assumption | rewrite Hspa; exact ST | reflexivity | lia | reflexivity | unfold le4val; lia ]
      | ].
    cbv beta. intros ms' PO. unfold leaf_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MUc WMc MIc STc ndR2__; nd_post; revert ndR2__; intros ->).
    rewrite Hspa in *.
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end; clear MUc WMc.
    try clear ST. rename STc into ST. try clear MI. rename MIc into MI.
    replace (ret_pc (Z_to_bv 64 0x8b650)) with (Z_to_bv 64 0x8b650) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    fold snap. clear Hspa. subst spa.
    (* [comment removed for export] *)
    zstep. zstep.
    ck0 PUNP; ck_go.
    zstep. zstep. zstep.
    ck0 PUNP; ck_go.
    zstep.
    (* [comment removed for export] *)
    ck0_at PUNP (P + 100)%Z.
    zstep. zstep. if_false.
    zstep. rewrite (sx32_small lt) by lia.
    zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (MAXSNAP _ spa) with (lo := lo) (dlt := lt);
        [ assumption | rewrite Hspa; exact ST | reflexivity | lia ]
      | ].
    cbv beta. intros ms' PO. unfold leaf_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MUc WMc MIc STc ndR2__; nd_post; revert ndR2__; intros ->).
    rewrite Hspa in *.
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end; clear MUc WMc.
    try clear ST. rename STc into ST. try clear MI. rename MIc into MI.
    replace (ret_pc (Z_to_bv 64 0x8b698)) with (Z_to_bv 64 0x8b698) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    fold msl. clear Hspa. subst spa.
    (* [comment removed for export] *)
    zstep.
    ck0_at PUNP (P + 656)%Z.
    zstep. zstep. if_false.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite (zx32_lit 16777216) by lia. rewrite (Z.mod_small msl 4294967296) by lia.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    (* [comment removed for export] *)
    assert (FIN : forall (rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word) (m6 : mem) (mb : Z),
      (0 <= mb <= 2^28)%Z ->
      (if 16777216 <? msl + 131104 then mb = msl + 131104 else mb = 16777216)%Z ->
      mem_inv asegs m6 -> stk asegs m6 lo SPA -> munch [(SPA - 16, SPA); (P, P + 680)]%Z mm m6 -> wmono asegs mm m6 ->
      rw_cells asegs m6 P (ngcells P (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 BS0)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 (Z.b2z sw))) (C4 (Z_to_bv 64 1)) (C4 (Z_to_bv 64 MINOR))
                             (C4 (Z_to_bv 64 snap)) (C4 (Z_to_bv 64 lt)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0))) ->
      rw_cells asegs m6 (P + 648) [C8 (Z_to_bv 64 1000000); C4 (Z_to_bv 64 mb); C4 (Z_to_bv 64 (ng_ifcount sg)); C4 (Z_to_bv 64 (ng_ifaces_size sg)); CB 4 pad; C8 (Z_to_bv 64 I)] ->
      rw_cells asegs m6 SPA (ngc_spill P EB Fb j) -> unpoisoned m6 P (P + 680) ->
      evtF asegs RNGx (fun ms' => implMG RNGx (fo_ret FO _ FF_NG_CHECK_HEADER (CH_Ok (mkPcap qs f BS0 ba qb bufdata sw 1 MINOR snap lt 0 0 0 [] hdr0
                                (PrivNg (if 16777216 <? msl + 131104 then mkNg 1000000 (msl + 131104) (ng_ifcount sg) (ng_ifaces_size sg) (ng_ifaces sg) else sg) i)))) sx POSTQ ms')
        (MS (mkR rax (Z_to_bv 64 SPA) gp tp t0x t1x t2x sp (Z_to_bv 64 SPA) a0x a1x a2x a3x a4x a5x a6x a7x
                 (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 100)) (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)) (Z_to_bv 64 (B + 12)) (Z_to_bv 64 (B + 8))
                 (Z_to_bv 64 (Z.shiftr (B + 8) 3 + 2147450880)) r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3x t4x t5x t6x)
            F (Z_to_bv 64 0x8b6f4) fc None m6 (seg_rom asegs))).
    { intros until mb. intros MBR MBE MI6 ST6 MU6 WM6 CELLS6 NG6 FRA6 PUNP6.
      clear MU WM CELLS NG5 ST MI FRA PUNP BUNP. unfold ngcells in CELLS6. unfold ngc_spill in FRA6.
      zstep. zstep.
      ck0 PUNP6; ck_go.
      zstep. zstep. zstep. zstep.
      ck0 PUNP6; ck_go.
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
      assert (AGS : agrees_on (fun a => outside [(SPA - 16, SPA); (P, P + 680)]%Z a) mm m7) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      assert (INV7 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg) m7).
      { eapply (ngc_inv_own FO GIOA TP fflagA GL); [exact CTX| exact INV| | exact MU6| exact WM6| exact MI6| exact ST6| ].
        - apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil]. right; left. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
        - intros a Ha. cbn [outside fst snd]. (atop_facts; plia). }
      unhide FCUR. unhide FRC. unhide HE. unhide HEB. unhide BUF5.
      assert (FCUR7 : rw_cells asegs m7 (SPA + 128) ccs) by (eapply agrees_rw_cells; [exact AGS| exact FCUR|]; intros a Ha; rewrite Hccs in Ha; cbn [outside fst snd]; lia).
      assert (FRC7 : rw_cells asegs m7 Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]))
        by (eapply agrees_rw_cells; [exact AGS| exact FRC|]; intros a Ha; rewrite !cells_size_app, Hfcs in Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
      assert (HE7 : rw_cells asegs m7 ERR [C4 z64]) by (eapply agrees_rw_cells; [exact AGS| exact HE|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
      assert (HEB7 : rw_cells asegs m7 EB [CB 256 e]) by (eapply agrees_rw_cells; [exact AGS| exact HEB|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
      assert (BUF7 : rw_cells asegs m7 B [CB (Z.to_nat ba) bs])
        by (eapply agrees_rw_cells; [exact AGS| exact BUF5|]; intros a Ha; cbn [cells_size csize] in Ha; rewrite Nat.add_0_r, Z2Nat.id in Ha by lia; cbn [outside fst snd]; lia).
      assert (HIF7 : ifaces_ok (ngc_p f qs sw BS0 MINOR qb ba bufdata sg i) I m7).
      { eapply ifaces_ok_agree; [exact AGS | | exact HIF]. intros sg' q E a Ha. cbn [pc_priv ngc_p] in E. injection E as <- ->.
        destruct (API sg q eq_refl) as (IP & IB). unfold PCAP_NG_SF_TOTAL in IP. destruct (ITOP q eq_refl) as (I0 & IT). cbn [outside fst snd]. (atop_facts; plia). }
      pose proof (rw_cells_uncut _ _ _ _ _ FRA6 FCUR7 ltac:(cbn; lia)) as SCS.
      apply evtF_done. subst POSTQ.
      eapply (ngc_exit FO GIOA TP fflagA GL FRET) with (PB := (qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (ew := z64);
        [ exact CTX | exact INV7 | exact SCS | rewrite cells_size_app, Hccs; reflexivity | exact FRC7 | exact Hfcs | exact HE7 | ].
      cbn [ngc_result]. exists P. split; [reflexivity|]. split; [| split; [reflexivity| exists e; exact HEB7]].
      exists z8, z8, z8. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists B, I, blank_junk, pad, bs.
      destruct (16777216 <? msl + 131104) eqn:HLT; subst mb.
      all: split; [unfold pcap_blocks, psize, is_ng; cbn [pc_priv pc_self pc_buffer pc_bufalloc ng_ifaces_size]; destruct i; reflexivity|].
      all: split; [unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, PK, blank_junk;
                  cbn [app pj_read_op pj_fd pj_a pj_b pj_c pj_d pj_e pj_f pj_g pj_h pj_breakloop pk_next_ng pk_cleanup_ng
                       pc_priv pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
                       pc_tstamp_precision pc_header h_sec h_usec h_caplen h_len hdr0];
                  exact CELLS6 |].
      all: split; [unfold priv_cells, PCAP_PRIV_OFF; cbn [pc_priv]; unfold ng_cells; cbn [ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size ng_ifaces]; rewrite ?UTS, ?MB; exact NG6|].
      all: split; [exact BUF7|]. all: split; [exact PFX|].
      all: split; [unfold ifaces_ok in HIF7 |- *; cbn [pc_priv ngc_p ng_ifaces ng_ifcount ng_ifaces_size] in HIF7 |- *; exact HIF7|].
      all: unfold pcap_wf; cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                pc_linktype pc_linktype_ext pc_header pc_priv h_caplen h_len hdr0 ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size].
      all: rewrite ?UTS, ?MB; unfold INT_MAX, INITIAL_MAX_BLOCKSIZE; repeat split; lia. }
    unfold bv_ltu. rewrite (unsigned_lit (msl + 131104)), (unsigned_lit 16777216) by lia.
    destruct (Z.lt_ge_cases 16777216 (msl + 131104)) as [LT|GE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.ltb_lt _ _) LT) in FIN |- *. cbn [negb]. cbv iota.
      ck0_at PUNP (P + 100)%Z.
      zstep. zstep. if_false.
      zstep. rewrite (sx32_small lt) by lia.
      zstep.
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      eapply evtF_cut;
        [ eapply (MAXSNAP _ spa) with (lo := lo) (dlt := lt);
          [ assumption | rewrite Hspa; exact ST | reflexivity | lia ]
        | ].
      cbv beta. intros ms' PO. unfold leaf_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MUc WMc MIc STc ndR2__; nd_post; revert ndR2__; intros ->).
      rewrite Hspa in *.
      lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end; clear MUc WMc.
      try clear ST. rename STc into ST. try clear MI. rename MIc into MI.
      replace (ret_pc (Z_to_bv 64 0x8b6d4)) with (Z_to_bv 64 0x8b6d4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      fold msl. clear Hspa. subst spa.
      zstep.
      ck0_at PUNP (P + 656)%Z.
      zstep. zstep. if_false.
      zstep. zstep. zstep. zstep. zstep.
      eapply FIN with (mb := (msl + 131104)%Z); [lia | reflexivity | exact MI | exact ST | exact MU | exact WM | exact CELLS | exact NG5 | exact FRA | exact PUNP].
    - rewrite (proj2 (Z.ltb_ge _ _) GE) in FIN |- *. cbn [negb]. cbv iota.
      eapply FIN with (mb := 16777216%Z); [lia | reflexivity | exact MI | exact ST | exact MU | exact WM | exact CELLS | exact NG5 | exact FRA | exact PUNP].
  Qed.
  End Sz1.
  Lemma ngc_ok_tail : ltac:(let t := eval cbv delta [ngc_ok_tail__stmt] in ngc_ok_tail__stmt in exact t).
  Proof using GL FRET LT2DLT ADJSNAP MAXSNAP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 r20 r24 t3 t4 t5 t6 qs qb P B ba sw BS0 MINOR bufdata sg i I pad bs e j ccs fcs k0 k1 k2. ltac2:(SecDiet.SzSec.closeP 'ngc_ok_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcOk.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardNgB__B3P.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardNgB__B3P.UbGuardNgB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (Z.shiftl _ (32)%Z) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
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
Section NgcOk.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).

  Definition ngc_ok_tail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 r20 t3 t4 t5 t6 : word)
      (qs qb : hptr) (P B ba : Z) (sw : bool) (BS0 MINOR : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) (I : Z)
      (pad bs e j : list byte) (ccs fcs : list cell) (k0 k1 k2 : word),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngi_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m f qs P sw BS0 MINOR
            RNGx sx mm qb B ba bufdata sg i I pad bs e j ccs fcs k0 k1 k2 ->
    (16 <= Z.of_nat (length bufdata))%Z -> (1 <= BS0 <= 2^21)%Z -> (0 <= MINOR < 2^16)%Z ->
    implMG RNGx (ngc_done (prims HO FO sites) 0 8 (ngc_p f qs sw BS0 MINOR qb ba bufdata sg i)) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 r20 (Z_to_bv 64 (B + 12)) (Z_to_bv 64 (B + 8)) (Z_to_bv 64 (Z.shiftr (B + 8) 3)) (Z_to_bv 64 (Z.land (B + 8) 3))   (* [comment removed for export] *)
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b3c4) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 r20 t3 t4 t5 t6 qs qb P B ba sw BS0 MINOR bufdata sg i I pad bs e j ccs fcs k0 k1 k2 : ltac2:(SecDiet.SzSec.tyM 'ngc_ok_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_ok_tail__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_ok_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET LT2DLT ADJSNAP MAXSNAP.
 intros CTX NGI LENB BS0R MINR.
    (nd_pre NGI 21%nat; intros INV FRA FCUR Hccs FRC Hfcs HE HEB CELLS NG5 UTS MB IC IS HIF BUF5 PFX LBA BAR BSB GRD; nd_post).
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    (* [comment removed for export] *)
    assert (HinP : In (qs, P, 680%Z) ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg)) by (left; reflexivity).
    assert (HinB : In (qb, B, ba) ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg)) by (right; left; reflexivity).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ndP__; nd_pre ndP__ 6%nat; intros (PBAND & _ & PTOP & P16) P0 PUNP PRNG PSRNG _; nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinB)) as ndP__; nd_pre ndP__ 6%nat; intros (BBAND & _ & BTOP & B16) B0 BUNP BRNG BSRNG _; nd_post).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0, PUNP, PRNG, PSRNG, BBAND, BTOP, B16, B0, BUNP, BRNG, BSRNG.
    band_ind PBAND bP. band_ind BBAND bU.
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) 4%nat; intros kMP kMPr kMP1 kMP2; nd_post).
    cbn [cb_addr cb_size fst snd] in kMP1, kMP2.
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) 4%nat; intros kEP kEPr kEP1 kEP2; nd_post).
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) 4%nat; intros kBP kBPr kBP1 kBP2; nd_post).
    cbn [cb_addr cb_size fst snd] in kEP1, kEP2, kBP1, kBP2.
    (nd_pre (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ (qs, P, 680%Z) (NGFR Fb) G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP) ltac:(left; reflexivity) ltac:(cbn; lia)) 4%nat; intros kPF kPFr kPF1 kPF2; nd_post).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2.
    assert (EPB : (qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg = pcap_blocks (ngc_p f qs sw BS0 MINOR qb ba bufdata sg i) P B I)
      by (unfold pcap_blocks, psize, is_ng; cbn [pc_priv pc_self pc_buffer pc_bufalloc ngc_p]; destruct i; reflexivity).
    destruct (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G EPB) as (APB & API).
    unfold psize, is_ng in APB, API. cbn [pc_priv pc_bufalloc ngc_p] in APB, API. unfold PCAP_NG_SF_TOTAL in APB, API.
    assert (ITOP : forall q, i = Some q -> (0 < I /\ I + 40 * ng_ifaces_size sg <= ATOP)%Z).
    { intros q ->. cbn [IBLK] in G.
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ (q, I, 40 * ng_ifaces_size sg)%Z G ltac:(apply in_or_app; left; apply in_or_app; right; right; right; left; reflexivity)) as ndP__; nd_pre ndP__ 3%nat; intros (_ & _ & IT & _) I0 _; nd_post).
      cbn [cb_addr cb_size fst snd] in IT, I0. lia. }
    (* [comment removed for export] *)
    (nd_pre (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.split_at8 bufdata 8 ltac:(lia)) 12%nat; intros pre8 l0 l1 r0 r1 n0 n1 n2 n3 post Ebuf Lpre8; nd_post).
    assert (GX : (0 <= l0 < 256 /\ 0 <= l1 < 256 /\ 0 <= r0 < 256 /\ 0 <= r1 < 256 /\ 0 <= n0 < 256 /\ 0 <= n1 < 256 /\ 0 <= n2 < 256 /\ 0 <= n3 < 256)%Z).
    { rewrite Ebuf in GRD. apply Forall_app in GRD as [_ GB].
      pose proof (Forall_inv GB) as X0. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X1. apply Forall_inv_tail in GB.
      pose proof (Forall_inv GB) as X2. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X3. apply Forall_inv_tail in GB.
      pose proof (Forall_inv GB) as X4. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X5. apply Forall_inv_tail in GB.
      pose proof (Forall_inv GB) as X6. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X7.
      cbv beta in X0, X1, X2, X3, X4, X5, X6, X7. lia. }
    (nd_pre GX 8%nat; intros L0 L1 R0' R1' N0 N1 N2 N3; nd_post).
    assert (GLT : get_le16 bufdata 8 = (l0 + 256 * l1)%Z) by (rewrite Ebuf; replace 8%Z with (Z.of_nat (length pre8)) by lia; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.get_le16_at).
    assert (GSN : get_le32 bufdata 12 = le4val n0 n1 n2 n3).
    { rewrite Ebuf. change (pre8 ++ l0 :: l1 :: r0 :: r1 :: n0 :: n1 :: n2 :: n3 :: post) with (pre8 ++ [l0; l1; r0; r1] ++ n0 :: n1 :: n2 :: n3 :: post).
      rewrite app_assoc. replace 12%Z with (Z.of_nat (length (pre8 ++ [l0; l1; r0; r1]))) by (rewrite length_app; cbn; lia). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_ai.get_le32_at. }
    pose proof PFX as PFX0. rewrite Ebuf in PFX0.
    change (pre8 ++ l0 :: l1 :: r0 :: r1 :: n0 :: n1 :: n2 :: n3 :: post) with (pre8 ++ [l0; l1; r0; r1; n0; n1; n2; n3] ++ post) in PFX0.
    (nd_pre (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pfx_decomp pre8 [l0; l1; r0; r1; n0; n1; n2; n3] post bs PFX0) 3%nat; intros bsr Ebs PFXr; nd_post). cbn [map] in Ebs.
    pose proof BUF5 as BX. rewrite Ebs in BX.
    assert (Lbsr : (length pre8 + 8 + length bsr = Z.to_nat ba)%nat).
    { pose proof (proj1 (proj1 BX)) as WF. cbn in WF. rewrite !length_app, length_map in WF. cbn in WF. lia. }
    pose proof (rw_cells_recell _ _ _ [CB (length pre8) (map b8 pre8); C2 (Z_to_bv 64 (l0 + 256 * l1)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (length bsr) bsr] BX
                  ltac:(cbn; rewrite length_map; repeat split; first [reflexivity | lia])
                  ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit, le4_lit by lia; rewrite !app_nil_r; cbn [app]; reflexivity)) as BX'.
    destruct (rw_cells_cut _ _ _ 1 BX') as [_ BX2]. destruct (rw_cells_cut _ _ _ 3 BX2) as [HIDB _]. clear BX BX' BX2.
    cbn [firstn skipn cells_size csize Nat.add app] in HIDB. rewrite Lpre8 in HIDB.
    lazymatch type of HIDB with rw_cells _ _ ?A _ => replace A with (B + 8)%Z in HIDB by lia end.
    (* [comment removed for export] *)
    unfold ngc_done. cbn [e_fret prims]. cbn [pc_bufdata pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_swapped pc_version_major pc_version_minor ng_of ngc_p pc_priv ng_ifaces_ptr_of].
    rewrite GLT. replace (8 + 4)%Z with 12%Z by reflexivity. rewrite GSN, MB, UTS.
    set (lt := linktype_to_dlt (l0 + 256 * l1)). set (snap := pcapint_adjust_snapshot lt (le4val n0 n1 n2 n3)).
    pose proof (linktype_to_dlt_range (l0 + 256 * l1) ltac:(lia)) as LTR. fold lt in LTR.
    pose proof (adjust_snapshot_range lt (le4val n0 n1 n2 n3) ltac:(unfold le4val; lia)) as SNR. fold snap in SNR. unfold INT_MAX in SNR.
    set (msl := max_snaplen_for_dlt lt). pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_chkB.max_snaplen_le3 lt) as MSR. fold msl in MSR.
    unfold MAX_BLOCKSIZE_FOR_SNAPLEN, INITIAL_MAX_BLOCKSIZE.
    (* [comment removed for export] *)
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as (RT & _).
    assert (HGlt : In (LT_TABLE, 28%Z) client_globals) by (unfold client_globals, LT_TABLE; repeat (first [left; reflexivity | right])).
    (pose proof (gia_global_mobjA _ _ _ GL _ _ _ _ _ _ _ _ _ G HGlt RIMG RISH) as ndP__; nd_pre ndP__ 4%nat; intros _ _ LTUNP _; nd_post).
    unfold ngc_hcells, ngcells in CELLS. unfold ng_cells in NG5. rewrite MB, UTS in NG5. unfold INITIAL_MAX_BLOCKSIZE in NG5.
    unfold ngc_spill in FRA.
    hide FCUR. hide FRC. hide HE. hide HEB. hide BUF5. hide FR. hide MGc. hide SHC.
    pose proof (munch_refl [(SPA - 16, SPA); (P, P + 680)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    (* [comment removed for export] *)
    replace (Z.land (B + 8) 3) with 0%Z by (symmetry; apply land3_0; apply (mod4_of_16 _ _ B16); reflexivity).
    zstep. if_false.
    (* [comment removed for export] *)
    ck0_at BUNP (B + 8)%Z.
    zstep. zstep. zstep. if_false.
    zstep.
    rewrite (zx16_lit (l0 + 256 * l1)) by lia.
    zstep.
    (* [comment removed for export] *)
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (LT2DLT _ spa) with (lo := lo) (lt := (l0 + 256 * l1)%Z);
        [ exact MI | rewrite Hspa; exact ST | rewrite Hspa; lia | lia | exact RT | exact LTUNP
        | rewrite Hspa; eapply rng_sub'; [exact RSPW| lia] | exact RIMG | exact RISH | reflexivity | lia ]
      | ].
    cbv beta. intros ms' PO. unfold leaf_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MUc WMc MIc STc ndR2__; nd_post; revert ndR2__; intros ->).
    rewrite Hspa in *.
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end; clear MUc WMc.
    try clear ST. rename STc into ST. try clear MI. rename MIc into MI.
    replace (ret_pc (Z_to_bv 64 0x8b3dc)) with (Z_to_bv 64 0x8b3dc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    fold lt. clear Hspa. subst spa.
    (* [comment removed for export] *)
    zstep. zstep.
    ck0 PUNP; ck_go.
    zstep.
    (* [comment removed for export] *)
    ck0 BUNP; ck_go.
    zstep. rewrite (sx32_s32 (le4val n0 n1 n2 n3)) by (unfold le4val; lia).
    zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (ADJSNAP _ spa) with (lo := lo) (lt := lt) (snaplen := le4val n0 n1 n2 n3);
        [ assumption | rewrite Hspa; exact ST | reflexivity | lia | reflexivity | unfold le4val; lia ]
      | ].
    cbv beta. intros ms' PO. unfold leaf_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MUc WMc MIc STc ndR2__; nd_post; revert ndR2__; intros ->).
    rewrite Hspa in *.
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end; clear MUc WMc.
    try clear ST. rename STc into ST. try clear MI. rename MIc into MI.
    replace (ret_pc (Z_to_bv 64 0x8b414)) with (Z_to_bv 64 0x8b414) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    fold snap. clear Hspa. subst spa.
    (* [comment removed for export] *)
    zstep. zstep.
    ck0 PUNP; ck_go.
    zstep. zstep. zstep.
    ck0 PUNP; ck_go.
    zstep.
    (* [comment removed for export] *)
    ck0_at PUNP (P + 100)%Z.
    zstep. zstep. if_false.
    zstep. rewrite (sx32_small lt) by lia.
    zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (MAXSNAP _ spa) with (lo := lo) (dlt := lt);
        [ assumption | rewrite Hspa; exact ST | reflexivity | lia ]
      | ].
    cbv beta. intros ms' PO. unfold leaf_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MUc WMc MIc STc ndR2__; nd_post; revert ndR2__; intros ->).
    rewrite Hspa in *.
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end; clear MUc WMc.
    try clear ST. rename STc into ST. try clear MI. rename MIc into MI.
    replace (ret_pc (Z_to_bv 64 0x8b460)) with (Z_to_bv 64 0x8b460) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    fold msl. clear Hspa. subst spa.
    (* [comment removed for export] *)
    ck0_at PUNP (P + 656)%Z.
    zstep. zstep. if_false.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite (zx32_lit 16777216) by lia. rewrite (Z.mod_small msl 4294967296) by lia.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    (* [comment removed for export] *)
    assert (FIN : forall (rax t0x t1x t2x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word) (m6 : mem) (mb : Z),
      (0 <= mb <= 2^28)%Z ->
      (if 16777216 <? msl + 131104 then mb = msl + 131104 else mb = 16777216)%Z ->
      mem_inv asegs m6 -> stk asegs m6 lo SPA -> munch [(SPA - 16, SPA); (P, P + 680)]%Z mm m6 -> wmono asegs mm m6 ->
      rw_cells asegs m6 P (ngcells P (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 BS0)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 (Z.b2z sw))) (C4 (Z_to_bv 64 1)) (C4 (Z_to_bv 64 MINOR))
                             (C4 (Z_to_bv 64 snap)) (C4 (Z_to_bv 64 lt)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0))) ->
      rw_cells asegs m6 (P + 648) [C8 (Z_to_bv 64 1000000); C4 (Z_to_bv 64 mb); C4 (Z_to_bv 64 (ng_ifcount sg)); C4 (Z_to_bv 64 (ng_ifaces_size sg)); CB 4 pad; C8 (Z_to_bv 64 I)] ->
      rw_cells asegs m6 SPA (ngc_spill P EB Fb j) -> unpoisoned m6 P (P + 680) ->
      evtF asegs RNGx (fun ms' => implMG RNGx (fo_ret FO _ FF_NG_CHECK_HEADER (CH_Ok (mkPcap qs f BS0 ba qb bufdata sw 1 MINOR snap lt 0 0 0 [] hdr0
                                (PrivNg (if 16777216 <? msl + 131104 then mkNg 1000000 (msl + 131104) (ng_ifcount sg) (ng_ifaces_size sg) (ng_ifaces sg) else sg) i)))) sx POSTQ ms')
        (MS (mkR rax (Z_to_bv 64 SPA) gp tp t0x t1x t2x sp (Z_to_bv 64 SPA) (Z_to_bv 64 P) a1x a2x a3x a4x a5x a6x a7x   (* [comment removed for export] *)
                 (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 100)) (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880))
                 (Z_to_bv 64 (Z.shiftr (P + 656) 3 + 2147450880)) (Z_to_bv 64 (P + 656))
                 (Z_to_bv 64 (Z.shiftr (B + 8) 3 + 2147450880)) z64 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3x t4x t5x t6x)
            F (Z_to_bv 64 0x8b4b8) fc None m6 (seg_rom asegs))).
    { intros until mb. intros MBR MBE MI6 ST6 MU6 WM6 CELLS6 NG6 FRA6 PUNP6.
      clear MU WM CELLS NG5 ST MI FRA PUNP BUNP. unfold ngcells in CELLS6. unfold ngc_spill in FRA6.
      zstep.
      ck0 PUNP6; ck_go.
      zstep. zstep. zstep. zstep.
      ck0 PUNP6; ck_go.
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
      assert (AGS : agrees_on (fun a => outside [(SPA - 16, SPA); (P, P + 680)]%Z a) mm m7) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      assert (INV7 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg) m7).
      { eapply (ngc_inv_own FO GIOA TP fflagA GL); [exact CTX| exact INV| | exact MU6| exact WM6| exact MI6| exact ST6| ].
        - apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil]. right; left. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
        - intros a Ha. cbn [outside fst snd]. (atop_facts; plia). }
      unhide FCUR. unhide FRC. unhide HE. unhide HEB. unhide BUF5.
      assert (FCUR7 : rw_cells asegs m7 (SPA + 128) ccs) by (eapply agrees_rw_cells; [exact AGS| exact FCUR|]; intros a Ha; rewrite Hccs in Ha; cbn [outside fst snd]; lia).
      assert (FRC7 : rw_cells asegs m7 Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]))
        by (eapply agrees_rw_cells; [exact AGS| exact FRC|]; intros a Ha; rewrite !cells_size_app, Hfcs in Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
      assert (HE7 : rw_cells asegs m7 ERR [C4 z64]) by (eapply agrees_rw_cells; [exact AGS| exact HE|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
      assert (HEB7 : rw_cells asegs m7 EB [CB 256 e]) by (eapply agrees_rw_cells; [exact AGS| exact HEB|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
      assert (BUF7 : rw_cells asegs m7 B [CB (Z.to_nat ba) bs])
        by (eapply agrees_rw_cells; [exact AGS| exact BUF5|]; intros a Ha; cbn [cells_size csize] in Ha; rewrite Nat.add_0_r, Z2Nat.id in Ha by lia; cbn [outside fst snd]; lia).
      assert (HIF7 : ifaces_ok (ngc_p f qs sw BS0 MINOR qb ba bufdata sg i) I m7).
      { eapply ifaces_ok_agree; [exact AGS | | exact HIF]. intros sg' q E a Ha. cbn [pc_priv ngc_p] in E. injection E as <- ->.
        destruct (API sg q eq_refl) as (IP & IB). unfold PCAP_NG_SF_TOTAL in IP. destruct (ITOP q eq_refl) as (I0 & IT). cbn [outside fst snd]. (atop_facts; plia). }
      pose proof (rw_cells_uncut _ _ _ _ _ FRA6 FCUR7 ltac:(cbn; lia)) as SCS.
      apply evtF_done. subst POSTQ.
      eapply (ngc_exit FO GIOA TP fflagA GL FRET) with (PB := (qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (ew := z64);
        [ exact CTX | exact INV7 | exact SCS | rewrite cells_size_app, Hccs; reflexivity | exact FRC7 | exact Hfcs | exact HE7 | ].
      cbn [ngc_result]. exists P. split; [reflexivity|]. split; [| split; [reflexivity| exists e; exact HEB7]].
      exists z8, z8, z8. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists B, I, blank_junk, pad, bs.
      destruct (16777216 <? msl + 131104) eqn:HLT; subst mb.
      all: split; [unfold pcap_blocks, psize, is_ng; cbn [pc_priv pc_self pc_buffer pc_bufalloc ng_ifaces_size]; destruct i; reflexivity|].
      all: split; [unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, PK, blank_junk;
                  cbn [app pj_read_op pj_fd pj_a pj_b pj_c pj_d pj_e pj_f pj_g pj_h pj_breakloop pk_next_ng pk_cleanup_ng
                       pc_priv pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
                       pc_tstamp_precision pc_header h_sec h_usec h_caplen h_len hdr0];
                  exact CELLS6 |].
      all: split; [unfold priv_cells, PCAP_PRIV_OFF; cbn [pc_priv]; unfold ng_cells; cbn [ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size ng_ifaces]; rewrite ?UTS, ?MB; exact NG6|].
      all: split; [exact BUF7|]. all: split; [exact PFX|].
      all: split; [unfold ifaces_ok in HIF7 |- *; cbn [pc_priv ngc_p ng_ifaces ng_ifcount ng_ifaces_size] in HIF7 |- *; exact HIF7|].
      all: unfold pcap_wf; cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                pc_linktype pc_linktype_ext pc_header pc_priv h_caplen h_len hdr0 ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size].
      all: rewrite ?UTS, ?MB; unfold INT_MAX, INITIAL_MAX_BLOCKSIZE; repeat split; lia. }
    unfold bv_ltu. rewrite (unsigned_lit (msl + 131104)), (unsigned_lit 16777216) by lia.
    destruct (Z.lt_ge_cases 16777216 (msl + 131104)) as [LT|GE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.ltb_lt _ _) LT) in FIN |- *. cbn [negb]. cbv iota.
      ck0_at PUNP (P + 100)%Z.
      zstep. zstep. if_false.
      zstep. rewrite (sx32_small lt) by lia.
      zstep.
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      eapply evtF_cut;
        [ eapply (MAXSNAP _ spa) with (lo := lo) (dlt := lt);
          [ assumption | rewrite Hspa; exact ST | reflexivity | lia ]
        | ].
      cbv beta. intros ms' PO. unfold leaf_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MUc WMc MIc STc ndR2__; nd_post; revert ndR2__; intros ->).
      rewrite Hspa in *.
      lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end; clear MUc WMc.
      try clear ST. rename STc into ST. try clear MI. rename MIc into MI.
      replace (ret_pc (Z_to_bv 64 0x8b498)) with (Z_to_bv 64 0x8b498) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      fold msl. clear Hspa. subst spa.
      ck0_at PUNP (P + 656)%Z.
      zstep. zstep. if_false.
      zstep. zstep. zstep. zstep. zstep.
      zstep.   (* [comment removed for export] *)
      eapply FIN with (mb := (msl + 131104)%Z); [lia | reflexivity | exact MI | exact ST | exact MU | exact WM | exact CELLS | exact NG5 | exact FRA | exact PUNP].
    - rewrite (proj2 (Z.ltb_ge _ _) GE) in FIN |- *. cbn [negb]. cbv iota.
      eapply FIN with (mb := 16777216%Z); [lia | reflexivity | exact MI | exact ST | exact MU | exact WM | exact CELLS | exact NG5 | exact FRA | exact PUNP].
  Qed.
  End Sz1.
  Lemma ngc_ok_tail : ltac:(let t := eval cbv delta [ngc_ok_tail__stmt] in ngc_ok_tail__stmt in exact t).
  Proof using GL FRET LT2DLT ADJSNAP MAXSNAP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 r20 t3 t4 t5 t6 qs qb P B ba sw BS0 MINOR bufdata sg i I pad bs e j ccs fcs k0 k1 k2. ltac2:(SecDiet.SzSec.closeP 'ngc_ok_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcOk.
End CANSEC1.
End TwB.
End F_ngchk_okA.

(* [comment removed for export] *)
Module F_ngchk_idbcA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfHandleA F_ngchk_modelA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_fail3A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_msgA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_okA.
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
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcIdbCall.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).
  #[local] Notation PR := (prims HO FO sites).

  Definition ngc_idb_call__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a4 a5 a6 a7 r24 t3 t4 t5 t6 : word)
      (qs qb : hptr) (P B ba : Z) (sw : bool) (BS0 MINOR : Z) (bd : list Z) (sg : pcap_ng_sf) (i : option hptr) (I rem : Z)
      (pad bs e j cpad : list byte) (fcs : list cell) (k0 k1 k2 : word),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngi_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m f qs P sw BS0 MINOR
            RNGx sx mm qb B ba bd sg i I pad bs e j (cursor_cells B (mkCursor 16 (rem - 8) 1) cpad) fcs k0 k1 k2 ->
    (Z.of_nat (length bd) = rem + 12)%Z -> (8 <= rem)%Z -> (rem + 12 <= 2^30)%Z -> (1 <= BS0 <= 2^21)%Z -> (0 <= MINOR < 2^16)%Z ->
    implMG RNGx (mbind (mbind (add_interface MOps PR (ngc_p f qs sw BS0 MINOR qb ba bd sg i) 8 (mkCursor 16 (rem - 8) 1))
                              (fun x : bool * cursor * PcapTypes.pcap hptr hptr * list Z => let '(ok, _, p, msg) := x in
                                 if ok then mret (@inr (list Z) Z 8%Z, p) else mret (@inl (list Z) Z msg, p)))
                       (ngc_loop_tail MOps PR 0)) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 P) a1 a2 (Z_to_bv 64 EB) a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 (B + 12)) (Z_to_bv 64 (B + 8)) (Z_to_bv 64 (Z.shiftr (B + 8) 3)) r24
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b5f8) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a4 a5 a6 a7 r24 t3 t4 t5 t6 qs qb P B ba sw BS0 MINOR bd sg i I rem pad bs e j cpad fcs k0 k1 k2 : ltac2:(SecDiet.SzSec.tyM 'ngc_idb_call__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_idb_call__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_idb_call__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET FREE FREENULL LT2DLT ADJSNAP MAXSNAP ADDIF.
 intros CTX NGI LBD REM R30 BS0R MINR.
    pose proof NGI as (INV & FRA & FCUR & Hccs & FRC & Hfcs & HE & HEB & CELLS & NG5 & UTS & MB & IC & IS & HIF & BUF5 & PFX & LBA & BAR & BSB & GRD).
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof TR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TRAI & _).
    assert (UCm : ucallerA (depth_check_header true) L mm sp s0 ra trC) by (eapply (ngc_uc_now FO GIOA TP fflagA GL); [exact CTX| exact INV]).
    edestruct (ngc_cobj_now FO GIOA TP fflagA GL) as (_ & _ & OEB'); [exact CTX| exact INV|].
    (* [comment removed for export] *)
    assert (HinP : In (qs, P, 680%Z) ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg)) by (left; reflexivity).
    assert (HinB : In (qb, B, ba) ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg)) by (right; left; reflexivity).
    assert (EPB : (qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg = pcap_blocks (ngc_p f qs sw BS0 MINOR qb ba bd sg i) P B I)
      by (unfold pcap_blocks, psize, is_ng; cbn [pc_priv pc_self pc_buffer pc_bufalloc ngc_p]; destruct i; reflexivity).
    destruct (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G EPB) as (APB & API).
    unfold psize, is_ng in APB. cbn [pc_priv pc_bufalloc ngc_p] in APB. unfold PCAP_NG_SF_TOTAL in APB.
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) as (kBP & kBPr & kBP1 & kBP2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn; lia)) as (kBB & kBBr & kBB1 & kBB2).
    cbn [cb_addr cb_size fst snd] in kBP1, kBP2, kBB1, kBB2.
    pose proof (hcells_cut _ _ _ _ _ _ CELLS) as (HPB & HP48).
    unfold ngc_spill in FRA.
    hide FRC. hide HE. hide CELLS. hide FR. hide MGc. hide SHC. hide BUF5. hide NG5. hide HPB. hide HP48. hide HEB. hide FCUR.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    zstep. zstep. zstep.
    clear MU WM.
    unhide FRC. unhide HE. unhide CELLS. unhide FR. unhide MGc. unhide SHC. unhide BUF5. unhide NG5. unhide HPB. unhide HP48. unhide HEB. unhide FCUR.
    apply evtF_done. subst POSTQ. apply implMG_bind_assoc. eapply implMG_bind.
    { eapply ADDIF with (L := L) (st := sx) (C1 := (CL ++ [(qs, P, PCAP_NG_SF_TOTAL); (qb, B, ba)])%list) (C2 := []) (FB := FB) (FL := NGFR Fb :: FL) (trC := (bv_unsigned ra :: trC)%list)
                        (P := P) (B := B) (I := I) (CUR := (SPA + 128)%Z) (EB := EB) (lo := lo) (idb_off := 8%Z) (p := ngc_p f qs sw BS0 MINOR qb ba bd sg i) (s := sg) (i := i)
                        (c := mkCursor 16 (rem - 8) 1) (bs := bs) (ej := e) (pad := pad) (cpad := cpad).
      - rewrite app_nil_r, <- app_assoc. cbn [app]. unfold PCAP_NG_SF_TOTAL.
        eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G| exact ST| exact MI| unfold ADD_INTERFACE_STACK, STDIO_STACK, PCAP_L2_STACK; lia].
      - eapply (ngc_ucaller 0%nat) with (X := 0x8b604%Z); [exact UCm| exact SPAB| lia| exact SPT| exact ALN| exact FR| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_ng_check_header; lia].
      - rewrite unsigned_lit by lia. exact TRAI.
      - intros ff [].
      - reflexivity.
      - rewrite app_nil_r. apply in_or_app; right; left; reflexivity.
      - rewrite app_nil_r. apply in_or_app; right; right; left; reflexivity.
      - unfold PCAP_NG_SF_TOTAL. cbn [pc_bufalloc ngc_p]. exact APB.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact HP48.
      - exact NG5.
      - exact HIF.
      - rewrite UTS; lia.
      - rewrite MB; unfold INITIAL_MAX_BLOCKSIZE; lia.
      - exact BUF5.
      - exact PFX.
      - cbn [pc_bufdata pc_bufalloc ngc_p]; lia.
      - exact GRD.
      - exact FCUR.
      - rewrite ESPA. lia.
      - Z.div_mod_to_equations; lia.
      - lia.
      - reflexivity.
      - reflexivity.
      - cbn [cur_remaining]; lia.
      - cbn [cur_off cur_remaining pc_bufdata ngc_p]; lia.
      - cbn [cur_block_type]; lia.
      - exact HEB.
      - left. rewrite app_nil_r. split; [split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB') (incl_appl _ (incl_refl _)) IFL)| exact (proj2 OEB')]|].
        cbn [pc_bufalloc ngc_p]. unfold PCAP_NG_SF_TOTAL. lia. }
    intros [[[ok c5] p5] msg5] sy RNGy msy PO. cbv beta iota in PO.
    destruct PO as (FPy & a0v & my & s' & i' & I' & pad' & bs' & E & OFy & MIy & STy & AGy & EP & Gy & NGy & U1 & U2 & U3 & U4 & BUFy & PFXy & LENy & GRy & -> & RM).
    rewrite ESPA in *. post_regs E.
    rewrite app_nil_r in Gy, AGy. cbn [pc_bufalloc pc_bufdata ngc_p] in AGy, BUFy, LENy.
    set (bd' := pc_bufdata p5) in *.
    assert (EP' : p5 = ngc_p f qs sw BS0 MINOR qb ba bd' s' i') by (rewrite EP; reflexivity).
    (* [comment removed for export] *)
    assert (Gy' : GIOA L RNGy sy (CL ++ (qs, P, 680%Z) :: (qb, B, ba) :: IBLK i' I' s') FB (NGFR Fb :: FL) my).
    { eapply GPL; [exact Gy|]. unfold PCAP_NG_SF_TOTAL. eapply Permutation.Permutation_trans; [apply Permutation.Permutation_app_comm|].
      rewrite <- app_assoc. cbn [app]. apply Permutation.Permutation_refl. }
    assert (INVy : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGy sy ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i' I' s') my).
    { eapply (ngc_inv_keep2 FO GIOA TP fflagA GL) with (CLk := (CL ++ [(qs, P, PCAP_NG_SF_TOTAL); (qb, B, ba)])%list)
          (Pn := fun a => (~ (P + PCAP_PRIV_OFF <= a < P + PCAP_NG_SF_TOTAL) /\ ~ (SPA + 128 <= a < SPA + 128 + 24) /\ ~ (EB <= a < EB + 256) /\ ~ (B <= a < B + ba))%Z);
        [exact CTX| exact INV| exact FPy| exact Gy'| exact OFy| exact MIy| exact STy| exact AGy| apply incl_appl, incl_refl| ].
      intros a N1 N2 NPBa NSP. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL.
      pose proof (NPBa _ HinP) as X1. pose proof (NPBa _ HinB) as X2. cbn [cb_addr cb_size fst snd] in X1, X2. lia. }
    (* [comment removed for export] *)
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ((_ & _ & PTOP & _) & P0 & _).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinB)) as ((_ & _ & BTOP & _) & B0 & _).
    cbn [cb_addr cb_size fst snd] in PTOP, P0, BTOP, B0.
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ (qs, P, 680%Z) (NGFR Fb) G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP) ltac:(left; reflexivity) ltac:(cbn; lia)) as (kPF & kPFr & kPF1 & kPF2).
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ (qb, B, ba) (NGFR Fb) G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinB) ltac:(left; reflexivity) ltac:(cbn; lia)) as (kUF & kUFr & kUF1 & kUF2).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2, kUF1, kUF2.
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) as (kEP & kEPr & kEP1 & kEP2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn; lia)) as (kEU & kEUr & kEU1 & kEU2).
    cbn [cb_addr cb_size fst snd] in kEP1, kEP2, kEU1, kEU2.
    (* [comment removed for export] *)
    assert (KEEP : forall A cs, rw_cells asegs mm A cs ->
                     ((SPA <= A /\ A + Z.of_nat (cells_size cs) <= SPA + 128) \/ (Fb <= A /\ A + Z.of_nat (cells_size cs) <= Fb + 64)
                      \/ (ERR = A /\ cells_size cs = 4%nat) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 648))%Z -> rw_cells asegs my A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AGy| exact HC|]. intros a Ha. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL.
      destruct HA as [HA|[HA|[HA|HA]]].
      - split; [left; lia| lia].
      - split; [right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia| lia].
      - destruct HA as (<- & HS). rewrite HS in Ha. split; [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_appl _ (incl_refl _)) IFL)| lia]| lia].
      - split; [right; left; apply in_block_In; exists (qs, P, 680%Z); split; [apply in_or_app; right; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]| lia]. }
    pose proof (KEEP _ _ FRA ltac:(left; cbn [cells_size csize Nat.add]; lia)) as FRAy.
    pose proof (KEEP _ _ FRC ltac:(right; left; rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia)) as FRCy.
    pose proof (KEEP _ _ HE ltac:(right; right; left; split; reflexivity)) as HEy.
    pose proof (KEEP _ _ CELLS ltac:(right; right; right; unfold ngc_hcells; rewrite ngcells_size by reflexivity; lia)) as CELLSy.
    clear KEEP.
    pose proof (munch_refl ([] : list (Z * Z)) my) as MU. pose proof (wmono_refl asegs my) as WM.
    destruct ok; cbn [Z.b2z] in *.
    - (* [comment removed for export] *)
      destruct RM as (HIFy & (cpad' & HCURy) & CR1' & CR2' & CR3' & CBT' & HEBy & ->). rewrite EP' in HIFy.
      ienterG. zstep. if_false.
      apply evtF_done. subst POSTQ. apply implMG_retb. unfold ngc_loop_tail. rewrite EP'.
      eapply (ngc_ok_tail HO FO sites GIOA TP fflagA GL FRET LT2DLT ADJSNAP MAXSNAP) with (j := j) (ccs := cursor_cells B c5 cpad') (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2)
                                                                                          (pad := pad') (bs := bs') (e := e) (I := I');
        [ exact CTX | | lia | exact BS0R | exact MINR ].
      split; [exact INVy|]. split; [exact FRAy|]. split; [exact HCURy|]. split; [reflexivity|]. split; [exact FRCy|]. split; [exact Hfcs|].
      split; [exact HEy|]. split; [exact HEBy|]. split; [exact CELLSy|]. split; [exact NGy|]. split; [rewrite U1; exact UTS|]. split; [rewrite U2; exact MB|].
      split; [exact U3|]. split; [exact U4|]. split; [exact HIFy|]. split; [exact BUFy|]. split; [exact PFXy|].
      split; [lia|]. split; [exact BAR|]. split; [exact BSB| exact GRy].
    - (* [comment removed for export] *)
      destruct RM as (CLOS & (ccs' & HCURy & Hccs') & (junk6 & HEBy) & LENM & MOK).
      ienterG. zstep. if_true.
      apply evtF_done. subst POSTQ. apply implMG_retb. unfold ngc_loop_tail, ngc_fail. rewrite EP'.
      cbn [ngc_p pc_priv ng_ifaces_ptr_of pc_buffer pc_self free_opt e_free e_fret prims mo_bind mo_ret MOps].
      assert (HI' : match i' with Some _ => True | None => I' = 0%Z end) by (unfold ng_ifaces_closable in CLOS; destruct i'; [exact Logic.I| exact CLOS]).
      eapply (ngc_fail3 HO FO GIOA TP fflagA GL FRET FREE FREENULL) with (i := i') (sg := s') (j := j) (ccs := ccs') (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (I := I');
        [ exact CTX | exact INVy | exact HI' | exact FRAy | exact HCURy | exact Hccs' | exact FRCy | exact Hfcs | exact HEy | exact HEBy | exact LENM | exact MOK
        | exact (proj1 (hcells_cut _ _ _ _ _ _ CELLSy)) | exact (ngcells_cut672 _ _ _ _ _ NGy) ].
  Qed.
  End Sz1.
  Lemma ngc_idb_call : ltac:(let t := eval cbv delta [ngc_idb_call__stmt] in ngc_idb_call__stmt in exact t).
  Proof using GL GPL FRET FREE FREENULL LT2DLT ADJSNAP MAXSNAP ADDIF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a4 a5 a6 a7 r24 t3 t4 t5 t6 qs qb P B ba sw BS0 MINOR bd sg i I rem pad bs e j cpad fcs k0 k1 k2. ltac2:(SecDiet.SzSec.closeP 'ngc_idb_call__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcIdbCall.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_fail3A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_msgA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_okA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcIdbCall.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).
  #[local] Notation PR := (prims HO FO sites).

  Definition ngc_idb_call__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)   (* [comment removed for export] *)
      (qs qb : hptr) (P B ba : Z) (sw : bool) (BS0 MINOR : Z) (bd : list Z) (sg : pcap_ng_sf) (i : option hptr) (I rem : Z)
      (pad bs e j cpad : list byte) (fcs : list cell) (k0 k1 k2 : word),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngi_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m f qs P sw BS0 MINOR
            RNGx sx mm qb B ba bd sg i I pad bs e j (cursor_cells B (mkCursor 16 (rem - 8) 1) cpad) fcs k0 k1 k2 ->
    (Z.of_nat (length bd) = rem + 12)%Z -> (8 <= rem)%Z -> (rem + 12 <= 2^30)%Z -> (1 <= BS0 <= 2^21)%Z -> (0 <= MINOR < 2^16)%Z ->
    implMG RNGx (mbind (mbind (add_interface MOps PR (ngc_p f qs sw BS0 MINOR qb ba bd sg i) 8 (mkCursor 16 (rem - 8) 1))
                              (fun x : bool * cursor * PcapTypes.pcap hptr hptr * list Z => let '(ok, _, p, msg) := x in
                                 if ok then mret (@inr (list Z) Z 8%Z, p) else mret (@inl (list Z) Z msg, p)))
                       (ngc_loop_tail MOps PR 0)) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 (B + 12)) (Z_to_bv 64 (B + 8)) (Z_to_bv 64 (Z.shiftr (B + 8) 3))
               (Z_to_bv 64 (Z.land (B + 8) 3))
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b3b0) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 qs qb P B ba sw BS0 MINOR bd sg i I rem pad bs e j cpad fcs k0 k1 k2 : ltac2:(SecDiet.SzSec.tyM 'ngc_idb_call__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_idb_call__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_idb_call__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET FREE FREENULL LT2DLT ADJSNAP MAXSNAP ADDIF.
 intros CTX NGI LBD REM R30 BS0R MINR.
    pose proof NGI as (INV & FRA & FCUR & Hccs & FRC & Hfcs & HE & HEB & CELLS & NG5 & UTS & MB & IC & IS & HIF & BUF5 & PFX & LBA & BAR & BSB & GRD).
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (ngc_tr_a3 _ _ _ _ TR) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TRAI & _).
    assert (UCm : ucallerA (depth_check_header true) L mm sp s0 ra trC) by (eapply (ngc_uc_now FO GIOA TP fflagA GL); [exact CTX| exact INV]).
    edestruct (ngc_cobj_now FO GIOA TP fflagA GL) as (_ & _ & OEB'); [exact CTX| exact INV|].
    (* [comment removed for export] *)
    assert (HinP : In (qs, P, 680%Z) ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg)) by (left; reflexivity).
    assert (HinB : In (qb, B, ba) ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg)) by (right; left; reflexivity).
    assert (EPB : (qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg = pcap_blocks (ngc_p f qs sw BS0 MINOR qb ba bd sg i) P B I)
      by (unfold pcap_blocks, psize, is_ng; cbn [pc_priv pc_self pc_buffer pc_bufalloc ngc_p]; destruct i; reflexivity).
    destruct (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G EPB) as (APB & API).
    unfold psize, is_ng in APB. cbn [pc_priv pc_bufalloc ngc_p] in APB. unfold PCAP_NG_SF_TOTAL in APB.
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) as (kBP & kBPr & kBP1 & kBP2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn; lia)) as (kBB & kBBr & kBB1 & kBB2).
    cbn [cb_addr cb_size fst snd] in kBP1, kBP2, kBB1, kBB2.
    pose proof (hcells_cut _ _ _ _ _ _ CELLS) as (HPB & HP48).
    unfold ngc_spill in FRA.
    hide FRC. hide HE. hide CELLS. hide FR. hide MGc. hide SHC. hide BUF5. hide NG5. hide HPB. hide HP48. hide HEB. hide FCUR.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
    clear MU WM.
    unhide FRC. unhide HE. unhide CELLS. unhide FR. unhide MGc. unhide SHC. unhide BUF5. unhide NG5. unhide HPB. unhide HP48. unhide HEB. unhide FCUR.
    apply evtF_done. subst POSTQ. apply implMG_bind_assoc. eapply implMG_bind.
    { eapply ADDIF with (L := L) (st := sx) (C1 := (CL ++ [(qs, P, PCAP_NG_SF_TOTAL); (qb, B, ba)])%list) (C2 := []) (FB := FB) (FL := NGFR Fb :: FL) (trC := (bv_unsigned ra :: trC)%list)
                        (P := P) (B := B) (I := I) (CUR := (SPA + 128)%Z) (EB := EB) (lo := lo) (idb_off := 8%Z) (p := ngc_p f qs sw BS0 MINOR qb ba bd sg i) (s := sg) (i := i)
                        (c := mkCursor 16 (rem - 8) 1) (bs := bs) (ej := e) (pad := pad) (cpad := cpad).
      - rewrite app_nil_r, <- app_assoc. cbn [app]. unfold PCAP_NG_SF_TOTAL.
        eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G| exact ST| exact MI| unfold ADD_INTERFACE_STACK, STDIO_STACK, PCAP_L2_STACK; lia].
      - eapply (ngc_ucaller 0%nat) with (X := 0x8b3c0%Z); [exact UCm| exact SPAB| lia| exact SPT| exact ALN| exact FR| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_ng_check_header; lia].
      - rewrite unsigned_lit by lia. exact TRAI.
      - intros ff [].
      - reflexivity.
      - rewrite app_nil_r. apply in_or_app; right; left; reflexivity.
      - rewrite app_nil_r. apply in_or_app; right; right; left; reflexivity.
      - unfold PCAP_NG_SF_TOTAL. cbn [pc_bufalloc ngc_p]. exact APB.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact HP48.
      - exact NG5.
      - exact HIF.
      - rewrite UTS; lia.
      - rewrite MB; unfold INITIAL_MAX_BLOCKSIZE; lia.
      - exact BUF5.
      - exact PFX.
      - cbn [pc_bufdata pc_bufalloc ngc_p]; lia.
      - exact GRD.
      - exact FCUR.
      - rewrite ESPA. lia.
      - Z.div_mod_to_equations; lia.
      - lia.
      - reflexivity.
      - reflexivity.
      - cbn [cur_remaining]; lia.
      - cbn [cur_off cur_remaining pc_bufdata ngc_p]; lia.
      - cbn [cur_block_type]; lia.
      - exact HEB.
      - left. rewrite app_nil_r. split; [split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB') (incl_appl _ (incl_refl _)) IFL)| exact (proj2 OEB')]|].
        cbn [pc_bufalloc ngc_p]. unfold PCAP_NG_SF_TOTAL. lia. }
    intros [[[ok c5] p5] msg5] sy RNGy msy PO. cbv beta iota in PO.
    destruct PO as (FPy & a0v & my & s' & i' & I' & pad' & bs' & E & OFy & MIy & STy & AGy & EP & Gy & NGy & U1 & U2 & U3 & U4 & BUFy & PFXy & LENy & GRy & -> & RM).
    rewrite ESPA in *. post_regs E.
    rewrite app_nil_r in Gy, AGy. cbn [pc_bufalloc pc_bufdata ngc_p] in AGy, BUFy, LENy.
    set (bd' := pc_bufdata p5) in *.
    assert (EP' : p5 = ngc_p f qs sw BS0 MINOR qb ba bd' s' i') by (rewrite EP; reflexivity).
    (* [comment removed for export] *)
    assert (Gy' : GIOA L RNGy sy (CL ++ (qs, P, 680%Z) :: (qb, B, ba) :: IBLK i' I' s') FB (NGFR Fb :: FL) my).
    { eapply GPL; [exact Gy|]. unfold PCAP_NG_SF_TOTAL. eapply Permutation.Permutation_trans; [apply Permutation.Permutation_app_comm|].
      rewrite <- app_assoc. cbn [app]. apply Permutation.Permutation_refl. }
    assert (INVy : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGy sy ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i' I' s') my).
    { eapply (ngc_inv_keep2 FO GIOA TP fflagA GL) with (CLk := (CL ++ [(qs, P, PCAP_NG_SF_TOTAL); (qb, B, ba)])%list)
          (Pn := fun a => (~ (P + PCAP_PRIV_OFF <= a < P + PCAP_NG_SF_TOTAL) /\ ~ (SPA + 128 <= a < SPA + 128 + 24) /\ ~ (EB <= a < EB + 256) /\ ~ (B <= a < B + ba))%Z);
        [exact CTX| exact INV| exact FPy| exact Gy'| exact OFy| exact MIy| exact STy| exact AGy| apply incl_appl, incl_refl| ].
      intros a N1 N2 NPBa NSP. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL.
      pose proof (NPBa _ HinP) as X1. pose proof (NPBa _ HinB) as X2. cbn [cb_addr cb_size fst snd] in X1, X2. lia. }
    (* [comment removed for export] *)
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ((_ & _ & PTOP & _) & P0 & _).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinB)) as ((_ & _ & BTOP & _) & B0 & _).
    cbn [cb_addr cb_size fst snd] in PTOP, P0, BTOP, B0.
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ (qs, P, 680%Z) (NGFR Fb) G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP) ltac:(left; reflexivity) ltac:(cbn; lia)) as (kPF & kPFr & kPF1 & kPF2).
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ (qb, B, ba) (NGFR Fb) G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinB) ltac:(left; reflexivity) ltac:(cbn; lia)) as (kUF & kUFr & kUF1 & kUF2).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2, kUF1, kUF2.
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) as (kEP & kEPr & kEP1 & kEP2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn; lia)) as (kEU & kEUr & kEU1 & kEU2).
    cbn [cb_addr cb_size fst snd] in kEP1, kEP2, kEU1, kEU2.
    (* [comment removed for export] *)
    assert (KEEP : forall A cs, rw_cells asegs mm A cs ->
                     ((SPA <= A /\ A + Z.of_nat (cells_size cs) <= SPA + 128) \/ (Fb <= A /\ A + Z.of_nat (cells_size cs) <= Fb + 64)
                      \/ (ERR = A /\ cells_size cs = 4%nat) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 648))%Z -> rw_cells asegs my A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AGy| exact HC|]. intros a Ha. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL.
      destruct HA as [HA|[HA|[HA|HA]]].
      - split; [left; lia| lia].
      - split; [right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia| lia].
      - destruct HA as (<- & HS). rewrite HS in Ha. split; [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_appl _ (incl_refl _)) IFL)| lia]| lia].
      - split; [right; left; apply in_block_In; exists (qs, P, 680%Z); split; [apply in_or_app; right; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]| lia]. }
    pose proof (KEEP _ _ FRA ltac:(left; cbn [cells_size csize Nat.add]; lia)) as FRAy.
    pose proof (KEEP _ _ FRC ltac:(right; left; rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia)) as FRCy.
    pose proof (KEEP _ _ HE ltac:(right; right; left; split; reflexivity)) as HEy.
    pose proof (KEEP _ _ CELLS ltac:(right; right; right; unfold ngc_hcells; rewrite ngcells_size by reflexivity; lia)) as CELLSy.
    clear KEEP.
    pose proof (munch_refl ([] : list (Z * Z)) my) as MU. pose proof (wmono_refl asegs my) as WM.
    destruct ok; cbn [Z.b2z] in *.
    - (* [comment removed for export] *)
      destruct RM as (HIFy & (cpad' & HCURy) & CR1' & CR2' & CR3' & CBT' & HEBy & ->). rewrite EP' in HIFy.
      ienterG. zstep. if_false.
      apply evtF_done. subst POSTQ. apply implMG_retb. unfold ngc_loop_tail. rewrite EP'.
      eapply (ngc_ok_tail HO FO sites GIOA TP fflagA GL FRET LT2DLT ADJSNAP MAXSNAP) with (j := j) (ccs := cursor_cells B c5 cpad') (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2)
                                                                                          (pad := pad') (bs := bs') (e := e) (I := I');
        [ exact CTX | | lia | exact BS0R | exact MINR ].
      split; [exact INVy|]. split; [exact FRAy|]. split; [exact HCURy|]. split; [reflexivity|]. split; [exact FRCy|]. split; [exact Hfcs|].
      split; [exact HEy|]. split; [exact HEBy|]. split; [exact CELLSy|]. split; [exact NGy|]. split; [rewrite U1; exact UTS|]. split; [rewrite U2; exact MB|].
      split; [exact U3|]. split; [exact U4|]. split; [exact HIFy|]. split; [exact BUFy|]. split; [exact PFXy|].
      split; [lia|]. split; [exact BAR|]. split; [exact BSB| exact GRy].
    - (* [comment removed for export] *)
      destruct RM as (CLOS & (ccs' & HCURy & Hccs') & (junk6 & HEBy) & LENM & MOK).
      ienterG. zstep. if_true.
      apply evtF_done. subst POSTQ. apply implMG_retb. unfold ngc_loop_tail, ngc_fail. rewrite EP'.
      cbn [ngc_p pc_priv ng_ifaces_ptr_of pc_buffer pc_self free_opt e_free e_fret prims mo_bind mo_ret MOps].
      assert (HI' : match i' with Some _ => True | None => I' = 0%Z end) by (unfold ng_ifaces_closable in CLOS; destruct i'; [exact Logic.I| exact CLOS]).
      eapply (ngc_fail3 HO FO GIOA TP fflagA GL FRET FREE FREENULL) with (i := i') (sg := s') (j := j) (ccs := ccs') (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (I := I');
        [ exact CTX | exact INVy | exact HI' | exact FRAy | exact HCURy | exact Hccs' | exact FRCy | exact Hfcs | exact HEy | exact HEBy | exact LENM | exact MOK
        | exact (proj1 (hcells_cut _ _ _ _ _ _ CELLSy)) | exact (ngcells_cut672 _ _ _ _ _ NGy) ].
  Qed.
  End Sz1.
  Lemma ngc_idb_call : ltac:(let t := eval cbv delta [ngc_idb_call__stmt] in ngc_idb_call__stmt in exact t).
  Proof using GL GPL FRET FREE FREENULL LT2DLT ADJSNAP MAXSNAP ADDIF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 qs qb P B ba sw BS0 MINOR bd sg i I rem pad bs e j cpad fcs k0 k1 k2. ltac2:(SecDiet.SzSec.closeP 'ngc_idb_call__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcIdbCall.
End CANSEC1.
End TwB.
End F_ngchk_idbcA.

(* [comment removed for export] *)
Module F_ngchk_idbA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfHandleA F_ngchk_modelA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_fail3A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_msgA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_okA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_idbcA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
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
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

(* [comment removed for export] *)
Section CANSEC0. Context {rc : runConstT}.
Section IdbSwapSeg.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint).

  Definition idb_swap_seq__stmt : Prop := forall (m : mem) (a0 a1 a2 a3 : word) (B ba bU l0 l1 r0 r1 n0 n1 n2 n3 : Z),
    mem_inv asegs m ->
    rw_cells asegs m (B + 8) [C2 (Z_to_bv 64 (l0 + 256 * l1)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3))] ->
    unpoisoned m B (B + ba) -> rng RNG (shad B) (nshad ba) -> rng RNG B ba ->
    (B mod 16 = 0)%Z -> (16 <= ba)%Z -> (B + ba <= 2^47)%Z ->
    (B + ba <= 0x7fff7000 + bU * 0x7FFFFF800000)%Z -> (0x10007fff8000 * bU <= B)%Z -> (0 <= bU <= 1)%Z -> (0x603000 <= B)%Z ->
    (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z -> (0 <= r0 < 256)%Z -> (0 <= r1 < 256)%Z ->
    (0 <= n0 < 256)%Z -> (0 <= n1 < 256)%Z -> (0 <= n2 < 256)%Z -> (0 <= n3 < 256)%Z ->
    evtF asegs RNG (fun ms' => exists (a0' a1' a2' a3' : word) (m' : mem),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (B + 12)) (Z_to_bv 64 (B + 8)) (Z_to_bv 64 (Z.shiftr (B + 8) 3))
                      s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8b5f0) fc None m' (seg_rom asegs)
        /\ munch [(B + 8, B + 16)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (B + 8) [C2 (Z_to_bv 64 (l1 + 256 * l0)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n3 n2 n1 n0))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (B + 12)) (Z_to_bv 64 (B + 8)) (Z_to_bv 64 (Z.shiftr (B + 8) 3))
               s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8b57c) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables m a0 a1 a2 a3 B ba bU l0 l1 r0 r1 n0 n1 n2 n3 : ltac2:(SecDiet.SzSec.tyM 'idb_swap_seq__stmt "vvvvvvvvvvvvvvvv" @m).
  Lemma idb_swap_seq__body : ltac2:(SecDiet.SzSec.bodyP 'idb_swap_seq__stmt "vvvvvvvvvvvvvvvv").
  Proof using .
 intros MI HX BUNP BSRNG BRNG B16 BA16 BA47 bUhi bUlo bUr bUimg L0 L1 R0 R1 N0 N1 N2 N3.
 qfold.
    pose proof (munch_refl [(B + 8, B + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    ck0_at BUNP (B + 8)%Z.
    zstep. zstep. zstep. if_false.
    zstep. zstep. zstep. if_false.
    do 5 zstep.
    (* [comment removed for export] *)
    ck0_at BUNP (B + 12)%Z.
    zstep. zstep. zstep. if_false.
    zstep. zstep. zstep. if_false.
    do 12 zstep.
    apply evtF_done. do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    eapply rw_cells_recell; [eassumption | cbn; repeat split; exact Logic.I |].
    cbn [cells_bytes cbytes app].
    rewrite (le2_lit l1 l0), (le2_lit r0 r1), (le4_lit n3 n2 n1 n0) by lia.
    rewrite (le2_of_val _ l1 l0 l1); [| lia | lia | lia | apply (swap16_valA _ l0 l1); [lia|lia| apply unsigned_zx16; lia]].
    rewrite (le4_of_val _ n3 n2 n1 n0 (n1 + 256 * n2 + 65536 * n3 + 16777216 * (((n3 / 128) * 4294967295) mod 256)));
      [| lia | lia | lia | lia | Z.div_mod_to_equations; lia
       | apply (swap32_valA _ n0 n1 n2 n3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
    reflexivity.
  Qed.
  End Sz1.
  Lemma idb_swap_seq : ltac:(let t := eval cbv delta [idb_swap_seq__stmt] in idb_swap_seq__stmt in exact t).
  Proof using . intros m a0 a1 a2 a3 B ba bU l0 l1 r0 r1 n0 n1 n2 n3. ltac2:(SecDiet.SzSec.closeP 'idb_swap_seq__body "vvvvvvvvvvvvvvvv"). Qed.
End IdbSwapSeg.
End CANSEC0.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcIdb.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).
  #[local] Notation PR := (prims HO FO sites).

  Definition ngc_idb__stmt : Prop := forall (fuel : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 : word)
      (qs qb : hptr) (P B ba : Z) (sw : bool) (BS0 MINOR : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) (I : Z)
      (pad bs e j cpad : list byte) (fcs : list cell) (k0 k1 k2 : word) (c : cursor),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngi_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m f qs P sw BS0 MINOR
            RNGx sx mm qb B ba bufdata sg i I pad bs e j (cursor_cells B c cpad) fcs k0 k1 k2 ->
    (Z.of_nat (length bufdata) = cur_remaining c + 12)%Z -> cur_off c = 8%Z -> (0 <= cur_remaining c)%Z -> (cur_remaining c + 12 <= 2^30)%Z ->
    cur_block_type c = 1%Z -> (1 <= BS0 <= 2^21)%Z -> (0 <= MINOR < 2^16)%Z ->
    implMG RNGx (mbind (ngc_K MOps PR fuel (RB_Ok c (ngc_p f qs sw BS0 MINOR qb ba bufdata sg i))) (ngc_loop_tail MOps PR 0)) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b350) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 qs qb P B ba sw BS0 MINOR bufdata sg i I pad bs e j cpad fcs k0 k1 k2 c : ltac2:(SecDiet.SzSec.tyM 'ngc_idb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ngc_idb__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_idb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF.
 intros CTX NGI LENB COFF CREM CR30 CBT BS0R MINR.
 qfold.
    destruct c as [coff rem cbt]. cbn [cur_off cur_remaining cur_block_type] in LENB, COFF, CREM, CR30, CBT. subst coff cbt.
    pose proof NGI as (INV & FRA & FCUR & Hccs & FRC & Hfcs & HE & HEB & CELLS & NG5 & UTS & MB & IC & IS & HIF & BUF5 & PFX & LBA & BAR & BSB & GRD).
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    (* [comment removed for export] *)
    assert (HinP : In (qs, P, 680%Z) ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg)) by (left; reflexivity).
    assert (HinB : In (qb, B, ba) ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg)) by (right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ((PBAND & _ & PTOP & P16) & P0 & PUNP & PRNG & PSRNG & _).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinB)) as ((BBAND & _ & BTOP & B16) & B0 & BUNP & BRNG & BSRNG & _).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0, PUNP, PRNG, PSRNG, BBAND, BTOP, B16, B0, BUNP, BRNG, BSRNG.
    band_ind PBAND bP. band_ind BBAND bU.
    assert (EPB : (qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg = pcap_blocks (ngc_p f qs sw BS0 MINOR qb ba bufdata sg i) P B I)
      by (unfold pcap_blocks, psize, is_ng; cbn [pc_priv pc_self pc_buffer pc_bufalloc ngc_p]; destruct i; reflexivity).
    destruct (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G EPB) as (APB & API).
    unfold psize, is_ng in APB, API. cbn [pc_priv pc_bufalloc ngc_p] in APB, API. unfold PCAP_NG_SF_TOTAL in APB, API.
    assert (ITOP : forall q, i = Some q -> (0 < I /\ I + 40 * ng_ifaces_size sg <= ATOP)%Z).
    { intros q ->. cbn [IBLK] in G.
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ (q, I, 40 * ng_ifaces_size sg)%Z G ltac:(apply in_or_app; left; apply in_or_app; right; right; right; left; reflexivity)) as ((_ & _ & IT & _) & I0 & _).
      cbn [cb_addr cb_size fst snd] in IT, I0. lia. }
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ (qb, B, ba) (NGFR Fb) G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinB) ltac:(left; reflexivity) ltac:(cbn; lia)) as (kUF & kUFr & kUF1 & kUF2).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kUF1, kUF2.
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn; lia)) as (kMU & kMUr & kMU1 & kMU2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn; lia)) as (kEU & kEUr & kEU1 & kEU2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn; lia)) as (kBU & kBUr & kBU1 & kBU2).
    cbn [cb_addr cb_size fst snd] in kMU1, kMU2, kEU1, kEU2, kBU1, kBU2.
    assert (HI : match i with Some _ => True | None => I = 0%Z end).
    { unfold ifaces_ok in HIF. cbn [pc_priv ngc_p] in HIF. destruct i; [exact Logic.I| exact (proj1 HIF)]. }
    (* [comment removed for export] *)
    unfold ngc_K. cbn [cur_block_type]. change (1 =? BT_IDB)%Z with true. cbv iota.
    unfold get_from_block_data. cbn [cur_off cur_remaining cur_block_type].
    unfold cursor_cells in FCUR. cbn [cur_off cur_remaining cur_block_type] in FCUR.
    pose proof (hcells_cut _ _ _ _ _ _ CELLS) as (HPB & HP48).
    destruct (rw_cells_cut _ _ _ 1 HP48) as [_ HP56]. cbn [firstn skipn cells_size csize Nat.add] in HP56.
    replace (P + 48 + Z.of_nat 8)%Z with (P + 56)%Z in HP56 by lia.
    pose proof FRA as FRAu. unfold ngc_spill in FRAu.
    hide FRA. hide FRC. hide HE. hide HEB. hide CELLS. hide NG5. hide FR. hide MGc. hide SHC. hide BUF5. hide HPB. hide HP48.
    pose proof (munch_refl [(SPA + 128, SPA + 152)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    zstep. zstep. zstep.
    destruct (Z.lt_ge_cases rem 8) as [RLT|RGE].
    - (* [comment removed for export] *)
      unfold bv_ltu. rewrite (unsigned_lit 7), (unsigned_lit rem) by lia. rewrite (proj2 (Z.ltb_ge 7 rem)) by lia. cbv iota.
      rewrite (proj2 (Z.ltb_lt rem 8) RLT). cbv iota.
      do 5 zstep. zstep.
      unhide FRA. unhide FRC. unhide HE. unhide HEB. unhide CELLS. unhide NG5. unhide FR. unhide MGc. unhide SHC. unhide BUF5. unhide HPB. unhide HP48.
      assert (MSG : fmt_at mm 0x22520 "block of type %u in pcapng dump file is too short"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm 0x22520 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "block of type %u in pcapng dump file is too short"%string) ++ [Z_to_bv 8 0])
                                 MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      apply evtF_done. subst POSTQ. apply implMG_retb. unfold ngc_loop_tail, ngc_fail.
      cbn [ngc_p pc_priv ng_ifaces_ptr_of pc_buffer pc_self free_opt e_free e_fret prims mo_bind mo_ret MOps].
      eapply (ngc_snp_fail HO FO GIOA TP fflagA GL FRET FREE FREENULL SNPRINTF) with (j := j) (ccs := [C8 (Z_to_bv 64 (B + 8)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 1); CB 4 cpad])
                                                                               (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (e := e) (RA := 0x8b374%Z) (FMTA := 0x22520%Z)
                                                                               (fs := "block of type %u in pcapng dump file is too short"%string) (args := [AInt 1]);
        [ exact CTX | exact INV | exact HI | exact FRA | exact FCUR | reflexivity | exact FRC | exact Hfcs | exact HE | exact HEB | exact HPB | exact (ngcells_cut672 _ _ _ _ _ NG5)
        | left; reflexivity | exact MSG | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor]
        | vm_compute; reflexivity | repeat constructor | unfold Msg.block_too_short, PCAP_ERRBUF_SIZE; reflexivity ].
    - (* [comment removed for export] *)
      unfold bv_ltu. rewrite (unsigned_lit 7), (unsigned_lit rem) by lia. rewrite (proj2 (Z.ltb_lt 7 rem)) by lia. cbv iota.
      rewrite (proj2 (Z.ltb_ge rem 8) RGE). cbv iota.
      cbn [pc_swapped ngc_p pc_bufdata]. change (8 + 4)%Z with 12%Z. change (8 + 8)%Z with 16%Z.
      (* [comment removed for export] *)
      assert (CALL : forall (rax t0x t1x t2x a1x a2x a4x a5x a6x a7x t3x t4x t5x t6x : word) (m6 : mem) (bd : list Z) (bs6 : list byte),
        mem_inv asegs m6 -> stk asegs m6 lo SPA -> munch [(SPA + 128, SPA + 152); (B + 8, B + 16)]%Z mm m6 -> wmono asegs mm m6 ->
        rw_cells asegs m6 (SPA + 128) (cursor_cells B (mkCursor 16 (rem - 8) 1) cpad) ->
        rw_cells asegs m6 B [CB (Z.to_nat ba) bs6] -> firstn (length bd) bs6 = map b8 bd -> length bd = length bufdata -> Forall (fun z => 0 <= z < 256)%Z bd ->
        evtF asegs RNGx (fun ms1 => implMG RNGx (mbind (mbind (add_interface MOps PR (ngc_p f qs sw BS0 MINOR qb ba bd sg i) 8 (mkCursor 16 (rem - 8) 1))
                              (fun x : bool * cursor * PcapTypes.pcap hptr hptr * list Z => let '(ok, _, p, msg) := x in
                                 if ok then mret (@inr (list Z) Z 8%Z, p) else mret (@inl (list Z) Z msg, p)))
                       (ngc_loop_tail MOps PR 0)) sx POSTQ ms1)
          (MS (mkR rax (Z_to_bv 64 SPA) gp tp t0x t1x t2x sp (Z_to_bv 64 SPA) (Z_to_bv 64 P) a1x a2x (Z_to_bv 64 EB) a4x a5x a6x a7x
                   (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 (B + 12)) (Z_to_bv 64 (B + 8)) (Z_to_bv 64 (Z.shiftr (B + 8) 3)) r24
                   (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3x t4x t5x t6x)
              F (Z_to_bv 64 0x8b5f8) fc None m6 (seg_rom asegs))).
      { intros until bs6. intros MI6 ST6 MU6 WM6 FCUR6 BUF6 PFX6 LEN6 GRD6.
        clear MU WM.
        unhide FRA. unhide FRC. unhide HE. unhide HEB. unhide CELLS. unhide NG5. unhide BUF5.
        assert (AGS : agrees_on (fun a => outside [(SPA + 128, SPA + 152); (B + 8, B + 16)]%Z a) mm m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
        assert (INV6 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg) m6).
        { eapply (ngc_inv_own FO GIOA TP fflagA GL); [exact CTX| exact INV| | exact MU6| exact WM6| exact MI6| exact ST6| ].
          - apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil]. right; left. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
          - intros a Ha. cbn [outside fst snd]. lia. }
        assert (FRA6 : rw_cells asegs m6 SPA (ngc_spill P EB Fb j)) by (eapply agrees_rw_cells; [exact AGS| exact FRA|]; intros a Ha; rewrite ngc_spill_size in Ha; cbn [outside fst snd]; lia).
        assert (FRC6 : rw_cells asegs m6 Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]))
          by (eapply agrees_rw_cells; [exact AGS| exact FRC|]; intros a Ha; rewrite !cells_size_app, Hfcs in Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
        assert (HE6 : rw_cells asegs m6 ERR [C4 z64]) by (eapply agrees_rw_cells; [exact AGS| exact HE|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
        assert (HEB6 : rw_cells asegs m6 EB [CB 256 e]) by (eapply agrees_rw_cells; [exact AGS| exact HEB|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
        assert (CELLS6 : rw_cells asegs m6 P (ngc_hcells P sw BS0 MINOR B))
          by (eapply agrees_rw_cells; [exact AGS| exact CELLS|]; intros a Ha; unfold ngc_hcells in Ha; rewrite ngcells_size in Ha by reflexivity; cbn [outside fst snd]; lia).
        assert (NG6 : rw_cells asegs m6 (P + 648) (ng_cells sg I pad))
          by (eapply agrees_rw_cells; [exact AGS| exact NG5|]; intros a Ha; unfold ng_cells in Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
        assert (HIF6 : ifaces_ok (ngc_p f qs sw BS0 MINOR qb ba bd sg i) I m6).
        { assert (HIF' : ifaces_ok (ngc_p f qs sw BS0 MINOR qb ba bd sg i) I mm) by exact HIF.
          eapply ifaces_ok_agree; [exact AGS | | exact HIF']. intros sg' q E a Ha. cbn [pc_priv ngc_p] in E. injection E as <- ->.
          destruct (API sg q eq_refl) as (IP & IB). destruct (ITOP q eq_refl) as (I0 & IT). cbn [outside fst snd]. lia. }
        apply evtF_done. subst POSTQ.
        eapply (ngc_idb_call HO FO sites GIOA TP fflagA GL GPL FRET FREE FREENULL LT2DLT ADJSNAP MAXSNAP ADDIF) with (j := j) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2)
                 (pad := pad) (bs := bs6) (e := e) (I := I) (cpad := cpad) (rem := rem);
          [ exact CTX | | lia | lia | lia | exact BS0R | exact MINR ].
        split; [exact INV6|]. split; [exact FRA6|]. split; [exact FCUR6|]. split; [reflexivity|]. split; [exact FRC6|]. split; [exact Hfcs|].
        split; [exact HE6|]. split; [exact HEB6|]. split; [exact CELLS6|]. split; [exact NG6|]. split; [exact UTS|]. split; [exact MB|].
        split; [exact IC|]. split; [exact IS|]. split; [exact HIF6|]. split; [exact BUF6|]. split; [exact PFX6|].
        split; [lia|]. split; [exact BAR|]. split; [exact BSB| exact GRD6]. }
      (* [comment removed for export] *)
      do 5 zstep. zstep. if_false_by (eqb_lits_false (B + 8) 0 ltac:(lia) ltac:(lia) ltac:(lia)).
      ck0_at PUNP (P + 56)%Z.
      zstep. zstep. zstep. if_false.
      do 6 zstep. zstep.
      replace (B + 8 + 4)%Z with (B + 12)%Z by lia.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      assert (AGS1 : agrees_on (fun a => outside [(SPA + 128, SPA + 152)]%Z a) mm m5) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      assert (SUB : sub_fp [(SPA + 128, SPA + 152)]%Z [(SPA + 128, SPA + 152); (B + 8, B + 16)]%Z) by (intros x Hx; cbn [outside fst snd] in Hx |- *; clear - Hx; tauto).
      unhide BUF5.
      assert (BUF5' : rw_cells asegs m5 B [CB (Z.to_nat ba) bs])
        by (eapply agrees_rw_cells; [exact AGS1| exact BUF5|]; intros a Ha; cbn [cells_size csize] in Ha; rewrite Nat.add_0_r, Z2Nat.id in Ha by lia; cbn [outside fst snd]; lia).
      assert (FCUR5 : rw_cells asegs m5 (SPA + 128) (cursor_cells B (mkCursor 16 (rem - 8) 1) cpad)).
      { unfold cursor_cells. cbn [cur_off cur_remaining cur_block_type]. replace (rem - 8)%Z with (rem + -8)%Z by lia. exact FCUR. }
      destruct sw; cbn [Z.b2z].
      + (* [comment removed for export] *)
        replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
        if_false.
        destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.split_at8 bufdata 8 ltac:(lia)) as (pre8 & l0 & l1 & r0 & r1 & n0 & n1 & n2 & n3 & post & Ebuf & Lpre8).
        assert (GX : (0 <= l0 < 256 /\ 0 <= l1 < 256 /\ 0 <= r0 < 256 /\ 0 <= r1 < 256 /\ 0 <= n0 < 256 /\ 0 <= n1 < 256 /\ 0 <= n2 < 256 /\ 0 <= n3 < 256)%Z).
        { rewrite Ebuf in GRD. apply Forall_app in GRD as [_ GB].
          pose proof (Forall_inv GB) as X0. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X1. apply Forall_inv_tail in GB.
          pose proof (Forall_inv GB) as X2. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X3. apply Forall_inv_tail in GB.
          pose proof (Forall_inv GB) as X4. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X5. apply Forall_inv_tail in GB.
          pose proof (Forall_inv GB) as X6. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X7.
          cbv beta in X0, X1, X2, X3, X4, X5, X6, X7. lia. }
        destruct GX as (L0 & L1 & R0' & R1' & N0 & N1 & N2 & N3).
        pose proof PFX as PFX0. rewrite Ebuf in PFX0.
        change (pre8 ++ l0 :: l1 :: r0 :: r1 :: n0 :: n1 :: n2 :: n3 :: post) with (pre8 ++ [l0; l1; r0; r1; n0; n1; n2; n3] ++ post) in PFX0.
        destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pfx_decomp pre8 [l0; l1; r0; r1; n0; n1; n2; n3] post bs PFX0) as (bsr & Ebs & PFXr). cbn [map] in Ebs.
        pose proof BUF5' as BX. rewrite Ebs in BX.
        assert (Lbsr : (length pre8 + 8 + length bsr = Z.to_nat ba)%nat).
        { pose proof (proj1 (proj1 BX)) as WF. cbn in WF. rewrite !length_app, length_map in WF. cbn in WF. lia. }
        pose proof (rw_cells_recell _ _ _ [CB (length pre8) (map b8 pre8); C2 (Z_to_bv 64 (l0 + 256 * l1)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (length bsr) bsr] BX
                      ltac:(cbn; rewrite length_map; repeat split; first [reflexivity | lia])
                      ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit, le4_lit by lia; rewrite !app_nil_r; cbn [app]; reflexivity)) as BX'.
        destruct (rw_cells_cut _ _ _ 1 BX') as [HB0 BX2]. destruct (rw_cells_cut _ _ _ 3 BX2) as [HX HBR]. clear BX BX' BX2.
        cbn [firstn skipn cells_size csize Nat.add app] in HB0, HX, HBR. rewrite Lpre8 in HX, HBR.
        lazymatch type of HX with rw_cells _ _ ?A _ => replace A with (B + 8)%Z in HX by lia end.
        lazymatch type of HBR with rw_cells _ _ ?A _ => replace A with (B + 16)%Z in HBR by lia end.
        eapply evtF_cut.
        { eapply idb_swap_seq with (B := B) (ba := ba) (bU := bU) (l0 := l0) (l1 := l1) (r0 := r0) (r1 := r1) (n0 := n0) (n1 := n1) (n2 := n2) (n3 := n3);
            [ eassumption | exact HX | exact BUNP | exact BSRNG | exact BRNG | exact B16 | lia | atop_facts; lia | exact bUhi | exact bUlo | exact bUr | exact bUimg
            | lia | lia | lia | lia | lia | lia | lia | lia ]. }
        cbv beta. intros ms' PO. destruct PO as (z1 & z2 & z3 & z4 & m6 & -> & MU6 & WM6 & MI6 & HX6). clear HX.
        assert (AGS56 : agrees_on (fun a => outside [(B + 8, B + 16)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
        assert (ST6 : stk asegs m6 lo SPA) by (eapply agrees_stk; [exact AGS56| eassumption| intros a Ha; cbn [outside fst snd]; lia]).
        assert (FRA6 : rw_cells asegs m6 SPA (ngc_spill P EB Fb j)).
        { eapply agrees_rw_cells; [exact AGS56| |intros a Ha; rewrite ngc_spill_size in Ha; cbn [outside fst snd]; lia].
          unhide FRA. eapply agrees_rw_cells; [exact AGS1| exact FRA|]. intros a Ha. rewrite ngc_spill_size in Ha. cbn [outside fst snd]. lia. }
        assert (FCUR6 : rw_cells asegs m6 (SPA + 128) (cursor_cells B (mkCursor 16 (rem - 8) 1) cpad))
          by (eapply agrees_rw_cells; [exact AGS56| exact FCUR5|]; intros a Ha; cbn [cells_size csize Nat.add cursor_cells] in Ha; cbn [outside fst snd]; lia).
        assert (HB06 : rw_cells asegs m6 B [CB (length pre8) (map b8 pre8)])
          by (eapply agrees_rw_cells; [exact AGS56| exact HB0|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
        assert (HBR6 : rw_cells asegs m6 (B + 16) [CB (length bsr) bsr])
          by (eapply agrees_rw_cells; [exact AGS56| exact HBR|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
        assert (BUF6 : rw_cells asegs m6 B [CB (Z.to_nat ba) (map b8 pre8 ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ bsr)]).
        { replace (B + 8)%Z with (B + Z.of_nat (cells_size [CB (length pre8) (map b8 pre8)]))%Z in HX6 by (cbn; lia).
          pose proof (rw_cells_uncut _ _ _ _ _ HB06 HX6 ltac:(cbn; lia)) as J1.
          replace (B + 16)%Z with (B + Z.of_nat (cells_size ([CB (length pre8) (map b8 pre8)] ++ [C2 (Z_to_bv 64 (l1 + 256 * l0)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n3 n2 n1 n0))])))%Z in HBR6 by (cbn; lia).
          pose proof (rw_cells_uncut _ _ _ _ _ J1 HBR6 ltac:(cbn; lia)) as J2. cbn [app] in J2.
          eapply rw_cells_recell; [exact J2 | cbn; rewrite ?length_app, ?length_map; cbn; repeat split; try exact Logic.I; lia |].
          cbn [cells_bytes cbytes app]. rewrite !le2_lit, le4_lit by lia. rewrite !app_nil_r, <- ?app_assoc. cbn [app]. reflexivity. }
        assert (EQSW : swap_field 4 12 (swap_field 2 8 bufdata) = pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post).
        { rewrite Ebuf. replace 8%Z with (Z.of_nat (length pre8)) by lia. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.swap2_at.
          change (pre8 ++ l1 :: l0 :: r0 :: r1 :: n0 :: n1 :: n2 :: n3 :: post) with (pre8 ++ [l1; l0; r0; r1] ++ n0 :: n1 :: n2 :: n3 :: post). rewrite app_assoc.
          replace 12%Z with (Z.of_nat (length (pre8 ++ [l1; l0; r0; r1]))) by (rewrite length_app; cbn; lia). rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_chkC.swap4_at, <- app_assoc. reflexivity. }
        rewrite EQSW.
        change (set_bufdata (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) (ngc_p f qs true BS0 MINOR qb ba bufdata sg i))
          with (ngc_p f qs true BS0 MINOR qb ba (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) sg i).
        (* [comment removed for export] *)
        assert (MU56 : munch [(SPA + 128, SPA + 152); (B + 8, B + 16)]%Z mm m6).
        { eapply munch_trans; [eapply munch_weaken; [exact SUB| exact MU]|]. eapply munch_weaken; [| exact MU6]. intros x Hx; cbn [outside fst snd] in Hx |- *; clear - Hx; tauto. }
        assert (WM56 : wmono asegs mm m6) by (eapply wmono_trans; [exact WM| exact WM6]).
        clear MU WM MU6 WM6. unfold ngc_spill in FRA6.
        pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
        zstep. zstep.
        eapply (CALL _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) (map b8 pre8 ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ bsr));
          [ exact MI6 | exact ST6 | exact MU56 | exact WM56 | exact FCUR6 | exact BUF6
          | change (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) with (pre8 ++ [l1; l0; r0; r1; n3; n2; n1; n0] ++ post);
            replace (map b8 pre8 ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ bsr) with (map b8 pre8 ++ map b8 [l1; l0; r0; r1; n3; n2; n1; n0] ++ bsr) by reflexivity;
            apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pfx_comp; exact PFXr
          | rewrite Ebuf, !length_app; cbn [length]; lia
          | rewrite Ebuf in GRD; apply Forall_app in GRD as [GA GB]; apply Forall_app; split; [exact GA|]; do 8 (apply Forall_inv_tail in GB); repeat (constructor; [cbv beta; lia|]); exact GB ].
      + (* [comment removed for export] *)
        replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
        if_true.
        eapply (CALL _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 bufdata bs);
          [ eassumption | eassumption | eapply munch_weaken; [exact SUB| exact MU] | exact WM | exact FCUR5 | exact BUF5' | exact PFX | reflexivity | exact GRD ].
  Qed.
  End Sz2.
  Lemma ngc_idb : ltac:(let t := eval cbv delta [ngc_idb__stmt] in ngc_idb__stmt in exact t).
  Proof using GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF. intros fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 qs qb P B ba sw BS0 MINOR bufdata sg i I pad bs e j cpad fcs k0 k1 k2 c. ltac2:(SecDiet.SzSec.closeP 'ngc_idb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcIdb.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardNgB__B3P.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_fail3A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_msgA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_okA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_idbcA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardNgB__B3P.UbGuardNgB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardNgB__B3P.F_gfbdB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
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
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

(* [comment removed for export] *)
Section CANSEC0. Context {rc : runConstT}.
Section IdbSwapSeg.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint).

  (* [comment removed for export] *)
  Definition idb_swap_seq__stmt : Prop := forall (m : mem) (a1 a2 a3 a4 : word) (B ba bU l0 l1 r0 r1 n0 n1 n2 n3 : Z),
    mem_inv asegs m ->
    rw_cells asegs m (B + 8) [C2 (Z_to_bv 64 (l0 + 256 * l1)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3))] ->
    unpoisoned m B (B + ba) -> rng RNG (shad B) (nshad ba) -> rng RNG B ba ->
    (B mod 16 = 0)%Z -> (16 <= ba)%Z -> (B + ba <= 2^47)%Z ->
    (B + ba <= 0x7fff7000 + bU * 0x7FFFFF800000)%Z -> (0x10007fff8000 * bU <= B)%Z -> (0 <= bU <= 1)%Z -> (0x604000 <= B)%Z ->
    (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z -> (0 <= r0 < 256)%Z -> (0 <= r1 < 256)%Z ->
    (0 <= n0 < 256)%Z -> (0 <= n1 < 256)%Z -> (0 <= n2 < 256)%Z -> (0 <= n3 < 256)%Z ->
    evtF asegs RNG (fun ms' => exists (a1' a2' a3' a4' : word) (m' : mem),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (B + 12)) (Z_to_bv 64 (B + 8)) (Z_to_bv 64 (Z.shiftr (B + 8) 3))
                      s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8b3b0) fc None m' (seg_rom asegs)
        /\ munch [(B + 8, B + 16)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (B + 8) [C2 (Z_to_bv 64 (l1 + 256 * l0)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n3 n2 n1 n0))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (B + 12)) (Z_to_bv 64 (B + 8)) (Z_to_bv 64 (Z.shiftr (B + 8) 3))
               s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8b33c) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables m a1 a2 a3 a4 B ba bU l0 l1 r0 r1 n0 n1 n2 n3 : ltac2:(SecDiet.SzSec.tyM 'idb_swap_seq__stmt "vvvvvvvvvvvvvvvv" @m).
  Lemma idb_swap_seq__body : ltac2:(SecDiet.SzSec.bodyP 'idb_swap_seq__stmt "vvvvvvvvvvvvvvvv").
  Proof using .
 intros MI HX BUNP BSRNG BRNG B16 BA16 BA47 bUhi bUlo bUr bUimg L0 L1 R0 R1 N0 N1 N2 N3.
 qfold.
    pose proof (munch_refl [(B + 8, B + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    ck0_at BUNP (B + 8)%Z.
    zstep. zstep. zstep. if_false.
    zstep. zstep. zstep. if_false.
    do 5 zstep.
    (* [comment removed for export] *)
    ck0_at BUNP (B + 12)%Z.
    zstep. zstep. zstep. if_false.
    zstep. zstep. zstep. if_false.
    do 12 zstep.
    apply evtF_done. do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    eapply rw_cells_recell; [eassumption | cbn; repeat split; exact Logic.I |].
    cbn [cells_bytes cbytes app].
    rewrite (le2_lit l1 l0), (le2_lit r0 r1), (le4_lit n3 n2 n1 n0) by lia.
    rewrite (le2_of_val _ l1 l0 l1); [| lia | lia | lia | apply (swap16_valA _ l0 l1); [lia|lia| apply unsigned_zx16; lia]].
    rewrite (le4_of_val _ n3 n2 n1 n0 (n1 + 256 * n2 + 65536 * n3 + 16777216 * (((n3 / 128) * 4294967295) mod 256)));
      [| lia | lia | lia | lia | Z.div_mod_to_equations; lia
       | apply (swap32_valA _ n0 n1 n2 n3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
    reflexivity.
  Qed.
  End Sz1.
  Lemma idb_swap_seq : ltac:(let t := eval cbv delta [idb_swap_seq__stmt] in idb_swap_seq__stmt in exact t).
  Proof using . intros m a1 a2 a3 a4 B ba bU l0 l1 r0 r1 n0 n1 n2 n3. ltac2:(SecDiet.SzSec.closeP 'idb_swap_seq__body "vvvvvvvvvvvvvvvv"). Qed.
End IdbSwapSeg.
End CANSEC0.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcIdb.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).
  #[local] Notation PR := (prims HO FO sites).

  Lemma ngc_idb : forall (fuel : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 : word)
      (qs qb : hptr) (P B ba : Z) (sw : bool) (BS0 MINOR : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) (I : Z)
      (pad bs e j cpad : list byte) (fcs : list cell) (k0 k1 k2 : word) (c : cursor),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngi_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m f qs P sw BS0 MINOR
            RNGx sx mm qb B ba bufdata sg i I pad bs e j (cursor_cells B c cpad) fcs k0 k1 k2 ->
    (Z.of_nat (length bufdata) = cur_remaining c + 12)%Z -> cur_off c = 8%Z -> (0 <= cur_remaining c)%Z -> (cur_remaining c + 12 <= 2^30)%Z ->
    cur_block_type c = 1%Z -> (1 <= BS0 <= 2^21)%Z -> (0 <= MINOR < 2^16)%Z ->
    implMG RNGx (mbind (ngc_K MOps PR fuel (RB_Ok c (ngc_p f qs sw BS0 MINOR qb ba bufdata sg i))) (ngc_loop_tail MOps PR 0)) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b2f8) fc None mm (seg_rom asegs)).   (* [comment removed for export] *)
  Proof using GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF.
    intros until c. intros CTX NGI LENB COFF CREM CR30 CBT BS0R MINR.
    destruct c as [coff rem cbt]. cbn [cur_off cur_remaining cur_block_type] in LENB, COFF, CREM, CR30, CBT. subst coff cbt.
    pose proof NGI as (INV & FRA & FCUR & Hccs & FRC & Hfcs & HE & HEB & CELLS & NG5 & UTS & MB & IC & IS & HIF & BUF5 & PFX & LBA & BAR & BSB & GRD).
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    (* [comment removed for export] *)
    assert (HinP : In (qs, P, 680%Z) ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg)) by (left; reflexivity).
    assert (HinB : In (qb, B, ba) ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg)) by (right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ((PBAND & _ & PTOP & P16) & P0 & PUNP & PRNG & PSRNG & _).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinB)) as ((BBAND & _ & BTOP & B16) & B0 & BUNP & BRNG & BSRNG & _).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0, PUNP, PRNG, PSRNG, BBAND, BTOP, B16, B0, BUNP, BRNG, BSRNG.
    band_ind PBAND bP. band_ind BBAND bU.
    assert (EPB : (qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg = pcap_blocks (ngc_p f qs sw BS0 MINOR qb ba bufdata sg i) P B I)
      by (unfold pcap_blocks, psize, is_ng; cbn [pc_priv pc_self pc_buffer pc_bufalloc ngc_p]; destruct i; reflexivity).
    destruct (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G EPB) as (APB & API).
    unfold psize, is_ng in APB, API. cbn [pc_priv pc_bufalloc ngc_p] in APB, API. unfold PCAP_NG_SF_TOTAL in APB, API.
    assert (ITOP : forall q, i = Some q -> (0 < I /\ I + 40 * ng_ifaces_size sg <= ATOP)%Z).
    { intros q ->. cbn [IBLK] in G.
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ (q, I, 40 * ng_ifaces_size sg)%Z G ltac:(apply in_or_app; left; apply in_or_app; right; right; right; left; reflexivity)) as ((_ & _ & IT & _) & I0 & _).
      cbn [cb_addr cb_size fst snd] in IT, I0. lia. }
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ (qb, B, ba) (NGFR Fb) G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinB) ltac:(left; reflexivity) ltac:(cbn; lia)) as (kUF & kUFr & kUF1 & kUF2).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kUF1, kUF2.
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn; lia)) as (kMU & kMUr & kMU1 & kMU2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn; lia)) as (kEU & kEUr & kEU1 & kEU2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn; lia)) as (kBU & kBUr & kBU1 & kBU2).
    cbn [cb_addr cb_size fst snd] in kMU1, kMU2, kEU1, kEU2, kBU1, kBU2.
    assert (HI : match i with Some _ => True | None => I = 0%Z end).
    { unfold ifaces_ok in HIF. cbn [pc_priv ngc_p] in HIF. destruct i; [exact Logic.I| exact (proj1 HIF)]. }
    (* [comment removed for export] *)
    unfold ngc_K. cbn [cur_block_type]. change (1 =? BT_IDB)%Z with true. cbv iota.
    unfold get_from_block_data. cbn [cur_off cur_remaining cur_block_type].
    unfold cursor_cells in FCUR. cbn [cur_off cur_remaining cur_block_type] in FCUR.
    pose proof (hcells_cut _ _ _ _ _ _ CELLS) as (HPB & HP48).
    destruct (rw_cells_cut _ _ _ 1 HP48) as [_ HP56]. cbn [firstn skipn cells_size csize Nat.add] in HP56.
    replace (P + 48 + Z.of_nat 8)%Z with (P + 56)%Z in HP56 by lia.
    pose proof FRA as FRAu. unfold ngc_spill in FRAu.
    hide FRA. hide FRC. hide HE. hide HEB. hide CELLS. hide NG5. hide FR. hide MGc. hide SHC. hide BUF5. hide HPB. hide HP48.
    pose proof (munch_refl [(SPA - 16, SPA); (SPA + 128, SPA + 152)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
    destruct (Z.lt_ge_cases rem 8) as [RLT|RGE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.ltb_lt rem 8) RLT). cbv iota.
      unhide FRA. unhide FRC. unhide HE. unhide HEB. unhide CELLS. unhide NG5. unhide FR. unhide MGc. unhide SHC. unhide BUF5. unhide HPB. unhide HP48.
      apply evtF_done. subst POSTQ. apply implMG_retb. unfold ngc_loop_tail, ngc_fail.
      cbn [ngc_p pc_priv ng_ifaces_ptr_of pc_buffer pc_self free_opt e_free e_fret prims mo_bind mo_ret MOps].
      eapply (ngc_gfbd_fail HO FO GIOA TP fflagA GL FRET FREE FREENULL SNPRINTF) with (j := j) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (e := e)
                                                                                  (D := (B + 8)%Z) (R := rem) (BT := 1%Z) (cpad := cpad);
        [ exact CTX | exact INV | exact HI | exact FRA | exact FCUR | exact FRC | exact Hfcs | exact HE | exact HEB | exact HPB | exact (ngcells_cut672 _ _ _ _ _ NG5) | lia | lia ].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.ltb_ge rem 8) RGE). cbv iota.
      cbn [pc_swapped ngc_p pc_bufdata]. change (8 + 4)%Z with 12%Z. change (8 + 8)%Z with 16%Z.
      (* [comment removed for export] *)
      assert (CALL : forall (rax t0x t1x t2x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word) (m6 : mem) (bd : list Z) (bs6 : list byte),
        mem_inv asegs m6 -> stk asegs m6 lo SPA -> munch [(SPA - 16, SPA); (SPA + 128, SPA + 152); (B + 8, B + 16)]%Z mm m6 -> wmono asegs mm m6 ->
        rw_cells asegs m6 (SPA + 128) (cursor_cells B (mkCursor 16 (rem - 8) 1) cpad) ->
        rw_cells asegs m6 B [CB (Z.to_nat ba) bs6] -> firstn (length bd) bs6 = map b8 bd -> length bd = length bufdata -> Forall (fun z => 0 <= z < 256)%Z bd ->
        evtF asegs RNGx (fun ms1 => implMG RNGx (mbind (mbind (add_interface MOps PR (ngc_p f qs sw BS0 MINOR qb ba bd sg i) 8 (mkCursor 16 (rem - 8) 1))
                              (fun x : bool * cursor * PcapTypes.pcap hptr hptr * list Z => let '(ok, _, p, msg) := x in
                                 if ok then mret (@inr (list Z) Z 8%Z, p) else mret (@inl (list Z) Z msg, p)))
                       (ngc_loop_tail MOps PR 0)) sx POSTQ ms1)
          (MS (mkR rax (Z_to_bv 64 SPA) gp tp t0x t1x t2x sp (Z_to_bv 64 SPA) (Z_to_bv 64 P) a1x a2x a3x a4x a5x a6x a7x
                   (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 (B + 12)) (Z_to_bv 64 (B + 8)) (Z_to_bv 64 (Z.shiftr (B + 8) 3))
                   (Z_to_bv 64 (Z.land (B + 8) 3))
                   (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3x t4x t5x t6x)
              F (Z_to_bv 64 0x8b3b0) fc None m6 (seg_rom asegs))).
      { intros until bs6. intros MI6 ST6 MU6 WM6 FCUR6 BUF6 PFX6 LEN6 GRD6.
        clear MU WM.
        unhide FRA. unhide FRC. unhide HE. unhide HEB. unhide CELLS. unhide NG5. unhide BUF5.
        assert (AGS : agrees_on (fun a => outside [(SPA - 16, SPA); (SPA + 128, SPA + 152); (B + 8, B + 16)]%Z a) mm m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
        assert (INV6 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg) m6).
        { eapply (ngc_inv_own FO GIOA TP fflagA GL); [exact CTX| exact INV| | exact MU6| exact WM6| exact MI6| exact ST6| ].
          - apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil]. right; left. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
          - intros a Ha. cbn [outside fst snd]. lia. }
        assert (FRA6 : rw_cells asegs m6 SPA (ngc_spill P EB Fb j)) by (eapply agrees_rw_cells; [exact AGS| exact FRA|]; intros a Ha; rewrite ngc_spill_size in Ha; cbn [outside fst snd]; lia).
        assert (FRC6 : rw_cells asegs m6 Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]))
          by (eapply agrees_rw_cells; [exact AGS| exact FRC|]; intros a Ha; rewrite !cells_size_app, Hfcs in Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
        assert (HE6 : rw_cells asegs m6 ERR [C4 z64]) by (eapply agrees_rw_cells; [exact AGS| exact HE|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
        assert (HEB6 : rw_cells asegs m6 EB [CB 256 e]) by (eapply agrees_rw_cells; [exact AGS| exact HEB|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
        assert (CELLS6 : rw_cells asegs m6 P (ngc_hcells P sw BS0 MINOR B))
          by (eapply agrees_rw_cells; [exact AGS| exact CELLS|]; intros a Ha; unfold ngc_hcells in Ha; rewrite ngcells_size in Ha by reflexivity; cbn [outside fst snd]; lia).
        assert (NG6 : rw_cells asegs m6 (P + 648) (ng_cells sg I pad))
          by (eapply agrees_rw_cells; [exact AGS| exact NG5|]; intros a Ha; unfold ng_cells in Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
        assert (HIF6 : ifaces_ok (ngc_p f qs sw BS0 MINOR qb ba bd sg i) I m6).
        { assert (HIF' : ifaces_ok (ngc_p f qs sw BS0 MINOR qb ba bd sg i) I mm) by exact HIF.
          eapply ifaces_ok_agree; [exact AGS | | exact HIF']. intros sg' q E a Ha. cbn [pc_priv ngc_p] in E. injection E as <- ->.
          destruct (API sg q eq_refl) as (IP & IB). destruct (ITOP q eq_refl) as (I0 & IT). cbn [outside fst snd]. lia. }
        apply evtF_done. subst POSTQ.
        eapply (ngc_idb_call HO FO sites GIOA TP fflagA GL GPL FRET FREE FREENULL LT2DLT ADJSNAP MAXSNAP ADDIF) with (j := j) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2)
                 (pad := pad) (bs := bs6) (e := e) (I := I) (cpad := cpad) (rem := rem);
          [ exact CTX | | lia | lia | lia | exact BS0R | exact MINR ].
        split; [exact INV6|]. split; [exact FRA6|]. split; [exact FCUR6|]. split; [reflexivity|]. split; [exact FRC6|]. split; [exact Hfcs|].
        split; [exact HE6|]. split; [exact HEB6|]. split; [exact CELLS6|]. split; [exact NG6|]. split; [exact UTS|]. split; [exact MB|].
        split; [exact IC|]. split; [exact IS|]. split; [exact HIF6|]. split; [exact BUF6|]. split; [exact PFX6|].
        split; [lia|]. split; [exact BAR|]. split; [exact BSB| exact GRD6]. }
      (* [comment removed for export] *)
      pose proof (gia_stack_sobjA _ _ _ GL _ _ _ _ _ _ _ lo SPA (SPA + 128) 24 G ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(atop_facts; lia) ltac:(exact RSTK)) as (_ & _ & CUNP & CRNG & CRSH).
      replace ((SPA + 128) mod 8)%Z with 0%Z in CRSH by (Z.div_mod_to_equations; lia).
      rewrite Z.sub_0_r, Z.add_0_r in CRSH.
      pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as (RT & _).
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      call (gfbd_ok (Z_to_bv 64 0x8b308) spa gp tp sp spa (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24
                    (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) F fc RNGx lo (SPA + 128)%Z).
      1: rewrite Hspa; lia.
      1: atop_facts; lia.
      1: lia.
      1: atop_facts; lia.
      1: Z.div_mod_to_equations; lia.
      1: right; rewrite Hspa; lia.
      1: exact MI.
      1: rewrite Hspa; exact ST.
      1: exact RT.
      1: exact FCUR.
      1: exact CUNP.
      1: lia.
      1: lia.
      1: lia.
      1: lia.
      rewrite Hspa in *. clear Hspa. subst spa.
      rename PC into ST. rename PC0 into FCURg. rename MI0 into MI.
      replace (B + 8 + 8)%Z with (B + 16)%Z in FCURg by lia.
      (* [comment removed for export] *)
      zstep. if_false_by (eqb_lits_false (B + 8) 0 ltac:(lia) ltac:(lia) ltac:(lia)).
      zstep.
      ck0_at PUNP (P + 56)%Z.
      zstep. zstep. zstep. if_false.
      do 6 zstep. zstep.
      replace (B + 8 + 4)%Z with (B + 12)%Z by lia.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      assert (AGS1 : agrees_on (fun a => outside [(SPA - 16, SPA); (SPA + 128, SPA + 152)]%Z a) mm m5) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      assert (SUB : sub_fp [(SPA - 16, SPA); (SPA + 128, SPA + 152)]%Z [(SPA - 16, SPA); (SPA + 128, SPA + 152); (B + 8, B + 16)]%Z) by (intros xx Hxx; cbn [outside fst snd] in Hxx |- *; clear - Hxx; tauto).
      unhide BUF5.
      assert (BUF5' : rw_cells asegs m5 B [CB (Z.to_nat ba) bs])
        by (eapply agrees_rw_cells; [exact AGS1| exact BUF5|]; intros a Ha; cbn [cells_size csize] in Ha; rewrite Nat.add_0_r, Z2Nat.id in Ha by lia; cbn [outside fst snd]; lia).
      assert (FCUR5 : rw_cells asegs m5 (SPA + 128) (cursor_cells B (mkCursor 16 (rem - 8) 1) cpad)).
      { unfold cursor_cells. cbn [cur_off cur_remaining cur_block_type]. exact FCURg. }
      destruct sw; cbn [Z.b2z].
      + (* [comment removed for export] *)
        replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
        if_false.
        (* [comment removed for export] *)
        zstep.
        lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
          replace c with false by (symmetry; rewrite (land3_0 (B + 8)) by (apply (mod4_of_16 _ _ B16); reflexivity); reflexivity) end.
        cbv iota.
        destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.split_at8 bufdata 8 ltac:(lia)) as (pre8 & l0 & l1 & r0 & r1 & n0 & n1 & n2 & n3 & post & Ebuf & Lpre8).
        assert (GX : (0 <= l0 < 256 /\ 0 <= l1 < 256 /\ 0 <= r0 < 256 /\ 0 <= r1 < 256 /\ 0 <= n0 < 256 /\ 0 <= n1 < 256 /\ 0 <= n2 < 256 /\ 0 <= n3 < 256)%Z).
        { rewrite Ebuf in GRD. apply Forall_app in GRD as [_ GB].
          pose proof (Forall_inv GB) as X0. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X1. apply Forall_inv_tail in GB.
          pose proof (Forall_inv GB) as X2. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X3. apply Forall_inv_tail in GB.
          pose proof (Forall_inv GB) as X4. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X5. apply Forall_inv_tail in GB.
          pose proof (Forall_inv GB) as X6. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X7.
          cbv beta in X0, X1, X2, X3, X4, X5, X6, X7. lia. }
        destruct GX as (L0 & L1 & R0' & R1' & N0 & N1 & N2 & N3).
        pose proof PFX as PFX0. rewrite Ebuf in PFX0.
        change (pre8 ++ l0 :: l1 :: r0 :: r1 :: n0 :: n1 :: n2 :: n3 :: post) with (pre8 ++ [l0; l1; r0; r1; n0; n1; n2; n3] ++ post) in PFX0.
        destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pfx_decomp pre8 [l0; l1; r0; r1; n0; n1; n2; n3] post bs PFX0) as (bsr & Ebs & PFXr). cbn [map] in Ebs.
        pose proof BUF5' as BX. rewrite Ebs in BX.
        assert (Lbsr : (length pre8 + 8 + length bsr = Z.to_nat ba)%nat).
        { pose proof (proj1 (proj1 BX)) as WF. cbn in WF. rewrite !length_app, length_map in WF. cbn in WF. lia. }
        pose proof (rw_cells_recell _ _ _ [CB (length pre8) (map b8 pre8); C2 (Z_to_bv 64 (l0 + 256 * l1)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (length bsr) bsr] BX
                      ltac:(cbn; rewrite length_map; repeat split; first [reflexivity | lia])
                      ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit, le4_lit by lia; rewrite !app_nil_r; cbn [app]; reflexivity)) as BX'.
        destruct (rw_cells_cut _ _ _ 1 BX') as [HB0 BX2]. destruct (rw_cells_cut _ _ _ 3 BX2) as [HX HBR]. clear BX BX' BX2.
        cbn [firstn skipn cells_size csize Nat.add app] in HB0, HX, HBR. rewrite Lpre8 in HX, HBR.
        lazymatch type of HX with rw_cells _ _ ?A _ => replace A with (B + 8)%Z in HX by lia end.
        lazymatch type of HBR with rw_cells _ _ ?A _ => replace A with (B + 16)%Z in HBR by lia end.
        eapply evtF_cut.
        { eapply idb_swap_seq with (B := B) (ba := ba) (bU := bU) (l0 := l0) (l1 := l1) (r0 := r0) (r1 := r1) (n0 := n0) (n1 := n1) (n2 := n2) (n3 := n3);
            [ eassumption | exact HX | exact BUNP | exact BSRNG | exact BRNG | exact B16 | lia | atop_facts; lia | exact bUhi | exact bUlo | exact bUr | exact bUimg
            | lia | lia | lia | lia | lia | lia | lia | lia ]. }
        cbv beta. intros ms' PO. destruct PO as (z1 & z2 & z3 & z4 & m6 & -> & MU6 & WM6 & MI6 & HX6). clear HX.
        assert (AGS56 : agrees_on (fun a => outside [(B + 8, B + 16)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
        assert (ST6 : stk asegs m6 lo SPA) by (eapply agrees_stk; [exact AGS56| eassumption| intros a Ha; cbn [outside fst snd]; lia]).
        assert (FRA6 : rw_cells asegs m6 SPA (ngc_spill P EB Fb j)).
        { eapply agrees_rw_cells; [exact AGS56| |intros a Ha; rewrite ngc_spill_size in Ha; cbn [outside fst snd]; lia].
          unhide FRA. eapply agrees_rw_cells; [exact AGS1| exact FRA|]. intros a Ha. rewrite ngc_spill_size in Ha. cbn [outside fst snd]. lia. }
        assert (FCUR6 : rw_cells asegs m6 (SPA + 128) (cursor_cells B (mkCursor 16 (rem - 8) 1) cpad))
          by (eapply agrees_rw_cells; [exact AGS56| exact FCUR5|]; intros a Ha; cbn [cells_size csize Nat.add cursor_cells] in Ha; cbn [outside fst snd]; lia).
        assert (HB06 : rw_cells asegs m6 B [CB (length pre8) (map b8 pre8)])
          by (eapply agrees_rw_cells; [exact AGS56| exact HB0|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
        assert (HBR6 : rw_cells asegs m6 (B + 16) [CB (length bsr) bsr])
          by (eapply agrees_rw_cells; [exact AGS56| exact HBR|]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside fst snd]; lia).
        assert (BUF6 : rw_cells asegs m6 B [CB (Z.to_nat ba) (map b8 pre8 ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ bsr)]).
        { replace (B + 8)%Z with (B + Z.of_nat (cells_size [CB (length pre8) (map b8 pre8)]))%Z in HX6 by (cbn; lia).
          pose proof (rw_cells_uncut _ _ _ _ _ HB06 HX6 ltac:(cbn; lia)) as J1.
          replace (B + 16)%Z with (B + Z.of_nat (cells_size ([CB (length pre8) (map b8 pre8)] ++ [C2 (Z_to_bv 64 (l1 + 256 * l0)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n3 n2 n1 n0))])))%Z in HBR6 by (cbn; lia).
          pose proof (rw_cells_uncut _ _ _ _ _ J1 HBR6 ltac:(cbn; lia)) as J2. cbn [app] in J2.
          eapply rw_cells_recell; [exact J2 | cbn; rewrite ?length_app, ?length_map; cbn; repeat split; try exact Logic.I; lia |].
          cbn [cells_bytes cbytes app]. rewrite !le2_lit, le4_lit by lia. rewrite !app_nil_r, <- ?app_assoc. cbn [app]. reflexivity. }
        assert (EQSW : swap_field 4 12 (swap_field 2 8 bufdata) = pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post).
        { rewrite Ebuf. replace 8%Z with (Z.of_nat (length pre8)) by lia. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.swap2_at.
          change (pre8 ++ l1 :: l0 :: r0 :: r1 :: n0 :: n1 :: n2 :: n3 :: post) with (pre8 ++ [l1; l0; r0; r1] ++ n0 :: n1 :: n2 :: n3 :: post). rewrite app_assoc.
          replace 12%Z with (Z.of_nat (length (pre8 ++ [l1; l0; r0; r1]))) by (rewrite length_app; cbn; lia). rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_chkC.swap4_at, <- app_assoc. reflexivity. }
        rewrite EQSW.
        change (set_bufdata (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) (ngc_p f qs true BS0 MINOR qb ba bufdata sg i))
          with (ngc_p f qs true BS0 MINOR qb ba (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) sg i).
        (* [comment removed for export] *)
        assert (MU56 : munch [(SPA - 16, SPA); (SPA + 128, SPA + 152); (B + 8, B + 16)]%Z mm m6).
        { eapply munch_trans; [eapply munch_weaken; [exact SUB| exact MU]|]. eapply munch_weaken; [| exact MU6]. intros xx Hxx; cbn [outside fst snd] in Hxx |- *; clear - Hxx; tauto. }
        assert (WM56 : wmono asegs mm m6) by (eapply wmono_trans; [exact WM| exact WM6]).
        clear MU WM MU6 WM6. unfold ngc_spill in FRA6.
        pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
        eapply (CALL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) (map b8 pre8 ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ bsr));
          [ exact MI6 | exact ST6 | exact MU56 | exact WM56 | exact FCUR6 | exact BUF6
          | change (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) with (pre8 ++ [l1; l0; r0; r1; n3; n2; n1; n0] ++ post);
            replace (map b8 pre8 ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ bsr) with (map b8 pre8 ++ map b8 [l1; l0; r0; r1; n3; n2; n1; n0] ++ bsr) by reflexivity;
            apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pfx_comp; exact PFXr
          | rewrite Ebuf, !length_app; cbn [length]; lia
          | rewrite Ebuf in GRD; apply Forall_app in GRD as [GA GB]; apply Forall_app; split; [exact GA|]; do 8 (apply Forall_inv_tail in GB); repeat (constructor; [cbv beta; lia|]); exact GB ].
      + (* [comment removed for export] *)
        replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
        if_true.
        eapply (CALL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 bufdata bs);
          [ eassumption | eassumption | eapply munch_weaken; [exact SUB| exact MU] | exact WM | exact FCUR5 | exact BUF5' | exact PFX | reflexivity | exact GRD ].
  Qed.
End NgcIdb.
End CANSEC1.
End TwB.
End F_ngchk_idbA.

(* [comment removed for export] *)
Module F_ngchk_loopA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfHandleA F_ngchk_modelA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_fail3A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_msgA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_okA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_idbcA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_idbA.
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
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

(* [comment removed for export] *)
Lemma bt_minus2_ltuA : forall bt, (0 <= bt < 2^32)%Z ->
  ((bv_unsigned (Z_to_bv 64 (s32 bt + -2)) <? 2) = ((bt =? 2) || (bt =? 3)))%Z.
Proof.
  intros bt Hbt. rewrite unsigned_lit_wrap. unfold s32.
  destruct (Z.eq_dec bt 2) as [->|N2]; [reflexivity|]. destruct (Z.eq_dec bt 3) as [->|N3]; [reflexivity|].
  rewrite (proj2 (Z.eqb_neq _ _) N2), (proj2 (Z.eqb_neq _ _) N3). cbn [orb]. apply Z.ltb_ge.
  change (bv_modulus 64) with (2^64)%Z. Z.div_mod_to_equations. lia.
Qed.

Lemma eqb_s32_litA : forall bt k, (0 <= bt < 2^32)%Z -> (0 <= k < 2^31)%Z -> bv_eqb (Z_to_bv 64 (s32 bt)) (Z_to_bv 64 k) = (bt =? k)%Z.
Proof.
  intros bt k Hb Hk. unfold bv_eqb. rewrite unsigned_lit_wrap, (unsigned_lit k) by lia. unfold s32. change (bv_modulus 64) with (2^64)%Z.
  destruct (Z.eqb_spec bt k) as [->|NE]; [apply Z.eqb_eq| apply Z.eqb_neq]; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma msg_ok_b : forall l : list Z, forallb (fun z => (0 <? z)%Z && (z <? 256)%Z) l = true -> Forall (fun z => 0 < z < 256)%Z l.
Proof. intros l H. apply Forall_forall. intros x Hx. rewrite forallb_forall in H. specialize (H x Hx). apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia. Qed.
Ltac msg_ok := first [ apply msg_ok_b; vm_compute; reflexivity
                     | vm_compute; repeat first [apply Forall_nil | apply Forall_cons; [split; reflexivity|]] ].

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcLoop.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.
  Hypothesis RBLK : read_block_stmt HO FO sites GIOA TP.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).
  #[local] Notation PR := (prims HO FO sites).

  Lemma ngc_loop : forall (fuel : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (qs qb : hptr) (P B ba : Z) (sw : bool) (BS0 MINOR : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) (I : Z)
      (pad bs e j : list byte) (ccs fcs : list cell) (k0 k1 k2 : word),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngi_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m f qs P sw BS0 MINOR
            RNGx sx mm qb B ba bufdata sg i I pad bs e j ccs fcs k0 k1 k2 ->
    (1 <= BS0 <= 2^21)%Z -> (0 <= MINOR < 2^16)%Z ->
    implMG RNGx (ngc_find MOps PR fuel 0 (ngc_p f qs sw BS0 MINOR qb ba bufdata sg i)) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 (-1)) (Z_to_bv 64 FA) (Z_to_bv 64 2) (Z_to_bv 64 6)
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b31c) fc None mm (seg_rom asegs)).
  Proof using GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK.
    induction fuel as [|fuel IH]; intros until k2; intros CTX NGI BS0R MINR.
    { unfold ngc_find. cbn [ng_find_idb].
      eapply (implMG_bind _ _ _ _ (fun _ _ _ _ => False)); [apply implMG_unr | intros a' s' R' ms' X; exact (False_rect _ X)]. }
    (pose proof NGI as ndP__; nd_pre ndP__ 21%nat; intros INV FRA FCUR Hccs FRC Hfcs HE HEB CELLS NG5 UTS MB IC IS HIF BUF5 PFX LBA BAR BSB GRD; nd_post).
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    (pose proof TR as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ TRRB _; nd_post).
    assert (UCm : ucallerA (depth_check_header true) L mm sp s0 ra trC) by (eapply (ngc_uc_now FO GIOA TP fflagA GL); [exact CTX| exact INV]).
    edestruct (ngc_cobj_now FO GIOA TP fflagA GL) as (_ & _ & OEB'); [exact CTX| exact INV|].
    (* [comment removed for export] *)
    assert (HinP : In (qs, P, 680%Z) ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg)) by (left; reflexivity).
    assert (HinB : In (qb, B, ba) ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg)) by (right; left; reflexivity).
    assert (EPB : (qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg = pcap_blocks (ngc_p f qs sw BS0 MINOR qb ba bufdata sg i) P B I)
      by (unfold pcap_blocks, psize, is_ng; cbn [pc_priv pc_self pc_buffer pc_bufalloc ngc_p]; destruct i; reflexivity).
    destruct (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G EPB) as (APB & API).
    unfold psize, is_ng in APB, API. cbn [pc_priv pc_bufalloc ngc_p] in APB, API. unfold PCAP_NG_SF_TOTAL in APB, API.
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ndP__; nd_pre ndP__ 3%nat; intros (_ & _ & PTOP & _) P0 _; nd_post).
    cbn [cb_addr cb_size fst snd] in PTOP, P0.
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) 4%nat; intros kBP kBPr kBP1 kBP2; nd_post).
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn; lia)) 4%nat; intros kBB kBBr kBB1 kBB2; nd_post).
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) 4%nat; intros kEP kEPr kEP1 kEP2; nd_post).
    cbn [cb_addr cb_size fst snd] in kBP1, kBP2, kBB1, kBB2, kEP1, kEP2.
    (nd_pre (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ (qs, P, 680%Z) (NGFR Fb) G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP) ltac:(left; reflexivity) ltac:(cbn; lia)) 4%nat; intros kPF kPFr kPF1 kPF2; nd_post).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2.
    assert (HI : match i with Some _ => True | None => I = 0%Z end).
    { unfold ifaces_ok in HIF. cbn [pc_priv ngc_p] in HIF. destruct i; [exact Logic.I| exact (proj1 HIF)]. }
    (* [comment removed for export] *)
    assert (IFACTS : forall q a, i = Some q -> (I <= a < I + 40 * ng_ifaces_size sg)%Z ->
              (~ (EB <= a < EB + 256) /\ a < ATOP /\ ~ (P <= a < P + 680) /\ in_block ((CL ++ [(qs, P, PCAP_NG_SF_TOTAL)]) ++ IBLK i I sg) a)%Z).
    { intros q a -> Ha. cbn [IBLK] in G.
      assert (HinI : In (q, I, (40 * ng_ifaces_size sg)%Z) ((qs, P, 680%Z) :: (qb, B, ba) :: [(q, I, (40 * ng_ifaces_size sg)%Z)])) by (right; right; left; reflexivity).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinI)) as ndP__; nd_pre ndP__ 3%nat; intros (_ & _ & IT & _) I0 _; nd_post).
      cbn [cb_addr cb_size fst snd] in IT, I0.
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinI ltac:(lia) ltac:(cbn; lia)) 4%nat; intros kBI kBIr kBI1 kBI2; nd_post).
      cbn [cb_addr cb_size fst snd] in kBI1, kBI2. destruct (API sg q eq_refl) as (IP & IB).
      split; [lia|]. split; [lia|]. split; [lia|].
      apply in_block_app. right. cbn [IBLK]. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    (* [comment removed for export] *)
    unfold ngc_find. rewrite (ng_find_idb_S MOps PR). apply implMG_bind_assoc. fold (ngc_find MOps PR fuel 0).
    pose proof (hcells_cut20 _ _ _ _ _ _ CELLS) as HBS. pose proof (proj2 (hcells_cut _ _ _ _ _ _ CELLS)) as HPV. pose proof (ngcells_cut656 _ _ _ _ _ NG5) as HMB.
    pose proof FRA as FRAu. unfold ngc_spill in FRAu.
    hide FRA. hide FRC. hide HE. hide HEB. hide CELLS. hide NG5. hide FR. hide MGc. hide SHC. hide BUF5. hide FCUR. hide HBS. hide HPV. hide HMB.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    do 4 zstep. zstep.
    clear MU WM FRAu.
    unhide FRA. unhide FRC. unhide HE. unhide HEB. unhide CELLS. unhide NG5. unhide FR. unhide MGc. unhide SHC. unhide BUF5. unhide FCUR. unhide HBS. unhide HPV. unhide HMB.
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply RBLK with (L := L) (st := sx) (C1 := (CL ++ [(qs, P, PCAP_NG_SF_TOTAL)])%list) (C2 := IBLK i I sg) (FB := FB) (FL := NGFR Fb :: FL) (trC := (bv_unsigned ra :: trC)%list)
                       (f := f) (Af := FA) (P := P) (B := B) (CUR := (SPA + 128)%Z) (EB := EB) (lo := lo) (p := ngc_p f qs sw BS0 MINOR qb ba bufdata sg i) (s := sg) (i := i)
                       (a_bhdr := DStack SiteBhdrCheckHeader 0) (bs := bs) (ej := e) (ccs := ccs).
      - rewrite <- app_assoc. cbn [app pc_buffer pc_bufalloc ngc_p]. unfold PCAP_NG_SF_TOTAL.
        eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G| exact ST| exact MI| unfold READ_BLOCK_STACK, PCAP_L1_STACK, PCAP_L2_STACK; lia].
      - eapply (ngc_ucaller 2%nat) with (X := 0x8b330%Z); [exact UCm| exact SPAB| lia| exact SPT| exact ALN| exact FR| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_ng_check_header; lia].
      - rewrite unsigned_lit by lia. exact TRRB.
      - apply nofr_cons; [eapply nofr_sub; [exact NF|]|].
        + intros ff Hf. unfold frames_read_block in Hf. unfold frames_check_header, frames_pcap_ng_check_header.
          destruct Hf as [<-|[<-|[]]]; [right; right; left; reflexivity| right; left; reflexivity].
        + unfold fb_fn, frames_read_block. cbn [fst]. intros [E|[E|[]]]; discriminate E.
      - exact HinF.
      - reflexivity.
      - reflexivity.
      - apply in_or_app; left; apply in_or_app; right; left; reflexivity.
      - exists SiteBhdrCheckHeader. split; reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - split; [exact HBS|]. split; [exact HPV|]. split; [exact HMB|]. rewrite MB. unfold INITIAL_MAX_BLOCKSIZE. cbn [pc_bufsize pc_bufalloc ngc_p]. lia.
      - exact BUF5.
      - exact PFX.
      - cbn [pc_bufdata pc_bufalloc ngc_p]; lia.
      - exact FCUR.
      - exact Hccs.
      - rewrite ESPA. lia.
      - Z.div_mod_to_equations; lia.
      - exact HEB.
      - left. split; [split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB') (incl_appl _ (incl_appl _ (incl_refl _))) IFL)| exact (proj2 OEB')]|].
        cbn [pc_bufalloc ngc_p]. unfold PCAP_NG_SF_TOTAL. lia.
      - exact EB8. }
    intros rb sy RNGy msy PO. cbv beta in PO.
    (nd_pre PO 23%nat; intros FPy a0v my p' B' bs' E OFy MIy STy AGy Gy BHy BUFy PFXy LENy PRIVE RFE SELFE BSZE SWE META RM; nd_post).
    rewrite ESPA in *. post_regs E.
    (* [comment removed for export] *)
    destruct p' as [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17]. unfold same_meta in META.
    cbn [pc_priv pc_rfile pc_self pc_bufsize pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
         pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_buffer pc_bufalloc pc_bufdata ngc_p] in PRIVE, RFE, SELFE, BSZE, SWE, META, RM, Gy, BHy, BUFy, PFXy, LENy, AGy.
    (nd_pre META 9%nat; intros M1 M2 M3 M4 M5 M6 M7 M8 M9; nd_post). subst f1 f2 f3 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17.
    rename f4 into ba'. rename f5 into qb'. rename f6 into bufdata'.
    change (mkPcap qs f BS0 ba' qb' bufdata' sw 1 MINOR 0 0 0 0 0 [] hdr0 (PrivNg sg i)) with (ngc_p f qs sw BS0 MINOR qb' ba' bufdata' sg i) in *.
    (nd_pre BHy 7%nat; intros HBSy HPVy HMBy _ _ BARy BSBy; nd_post). cbn [pc_bufsize pc_bufalloc pc_swapped ngc_p] in HBSy, HPVy, BARy, BSBy.
    (* [comment removed for export] *)
    assert (Gy' : GIOA L RNGy sy (CL ++ (qs, P, 680%Z) :: (qb', B', ba') :: IBLK i I sg) FB (NGFR Fb :: FL) my).
    { eapply GPL; [exact Gy|]. unfold PCAP_NG_SF_TOTAL. rewrite <- app_assoc. cbn [app].
      apply Permutation.Permutation_sym. eapply Permutation.Permutation_trans; [apply Permutation.Permutation_app_comm|]. cbn [app].
      eapply Permutation.Permutation_trans; [apply Permutation.perm_swap|]. apply Permutation.perm_skip.
      eapply Permutation.Permutation_trans; [|apply Permutation.Permutation_app_comm]. cbn [app]. apply Permutation.Permutation_refl. }
    assert (INVy : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGy sy ((qs, P, 680%Z) :: (qb', B', ba') :: IBLK i I sg) my).
    { eapply (ngc_inv_keep2 FO GIOA TP fflagA GL) with (CLk := ((CL ++ [(qs, P, PCAP_NG_SF_TOTAL)]) ++ IBLK i I sg)%list)
          (Pn := fun a => (~ (P + 24 <= a < P + 32) /\ ~ (SPA + 128 <= a < SPA + 128 + 24) /\ ~ (EB <= a < EB + 256))%Z);
        [exact CTX| exact INV| exact FPy| exact Gy'| exact OFy| exact MIy| exact STy| exact AGy| apply incl_appl, incl_appl, incl_refl| ].
      intros a N1 N2 NPBa NSP. pose proof (NPBa _ HinP) as X1. cbn [cb_addr cb_size fst snd] in X1. lia. }
    (* [comment removed for export] *)
    assert (KEEP : forall A cs, rw_cells asegs mm A cs ->
                     ((SPA <= A /\ A + Z.of_nat (cells_size cs) <= SPA + 128) \/ (Fb <= A /\ A + Z.of_nat (cells_size cs) <= Fb + 64)
                      \/ (ERR = A /\ cells_size cs = 4%nat) \/ (P + 32 <= A /\ A + Z.of_nat (cells_size cs) <= P + 680))%Z -> rw_cells asegs my A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AGy| exact HC|]. intros a Ha.
      destruct HA as [HA|[HA|[HA|HA]]].
      - split; [left; lia| lia].
      - split; [right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia| lia].
      - destruct HA as (<- & HS). rewrite HS in Ha. split; [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_appl _ (incl_appl _ (incl_refl _))) IFL)| lia]| lia].
      - split; [right; left; apply in_block_app; left; apply in_block_app; right; apply Exists_cons_hd; unfold PCAP_NG_SF_TOTAL; cbn [cb_addr cb_size fst snd]; lia| lia]. }
    pose proof (KEEP _ _ FRA ltac:(left; rewrite ngc_spill_size; lia)) as FRAy.
    pose proof (KEEP _ _ FRC ltac:(right; left; rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia)) as FRCy.
    pose proof (KEEP _ _ HE ltac:(right; right; left; split; reflexivity)) as HEy.
    pose proof (KEEP _ _ NG5 ltac:(right; right; right; unfold ng_cells; cbn [cells_size csize Nat.add]; lia)) as NGy.
    clear KEEP.
    assert (CELLSy : rw_cells asegs my P (ngc_hcells P sw BS0 MINOR B')).
    { eapply hcells_rebuf; [exact CELLS | | ].
      - eapply agrees_on_weaken; [exact AGy|]. intros a Ha. split; [| lia].
        right; left. apply in_block_app; left; apply in_block_app; right. apply Exists_cons_hd. unfold PCAP_NG_SF_TOTAL. cbn [cb_addr cb_size fst snd]. lia.
      - destruct (rw_cells_cut _ _ _ 1 HBSy) as [_ X2]. cbn [firstn skipn cells_size csize Nat.add app] in X2.
        replace (P + 24)%Z with (P + 20 + Z.of_nat 4)%Z by lia. exact X2. }
    assert (HIFy : ifaces_ok (ngc_p f qs sw BS0 MINOR qb' ba' bufdata' sg i) I my).
    { assert (HIF' : ifaces_ok (ngc_p f qs sw BS0 MINOR qb' ba' bufdata' sg i) I mm) by exact HIF.
      eapply ifaces_ok_agree; [exact AGy | | exact HIF']. intros sg' q E' a Ha. cbn [pc_priv ngc_p] in E'. injection E' as <- ->.
      (nd_pre (IFACTS q a eq_refl Ha) 4%nat; intros X1 X2 X3 X4; nd_post). split; [right; left; exact X4| lia]. }
    repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FPy) in HR end.
    pose proof (munch_refl ([] : list (Z * Z)) my) as MU. pose proof (wmono_refl asegs my) as WM.
    (* [comment removed for export] *)
    destruct rb as [p'' | msg p'' | c p''].
    - (* [comment removed for export] *)
      (destruct RM as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 2%nat; intros HEBy (ccs' & HCURy & Hccs'); nd_post).
      ienterG. zstep. if_false. zstep. if_true. do 3 zstep.
      apply evtF_done. subst POSTQ. unfold ngc_K. apply implMG_retb. unfold ngc_loop_tail, ngc_fail.
      cbn [ngc_p pc_priv ng_ifaces_ptr_of pc_buffer pc_self free_opt e_free e_fret prims mo_bind mo_ret MOps].
      eapply (ngc_mcp_fail HO FO GIOA TP fflagA GL FRET FREE FREENULL) with (j := j) (ccs := ccs') (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (e := e) (SRC := 0x22220%Z) (n := 53%Z);
        [ exact CTX | exact INVy | exact HI | exact FRAy | exact HCURy | exact Hccs' | exact FRCy | exact Hfcs | exact HEy | exact HEBy
        | exact (proj1 (hcells_cut _ _ _ _ _ _ CELLSy)) | exact (ngcells_cut672 _ _ _ _ _ NGy)
        | exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs my 0x22220 (map b8 Msg.no_idb ++ [Z_to_bv 8 0]) MIy ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; discriminate)))
        | vm_compute; reflexivity | lia | unfold client_globals; repeat (first [left; reflexivity | right]) | msg_ok ].
    - (* [comment removed for export] *)
      (destruct RM as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros (junk4 & HEBy) LENM MOK (ccs' & HCURy & Hccs'); nd_post).
      ienterG. zstep. if_true.
      apply evtF_done. subst POSTQ. unfold ngc_K. apply implMG_retb. unfold ngc_loop_tail, ngc_fail.
      cbn [ngc_p pc_priv ng_ifaces_ptr_of pc_buffer pc_self free_opt e_free e_fret prims mo_bind mo_ret MOps].
      eapply (ngc_fail3 HO FO GIOA TP fflagA GL FRET FREE FREENULL) with (j := j) (ccs := ccs') (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2);
        [ exact CTX | exact INVy | exact HI | exact FRAy | exact HCURy | exact Hccs' | exact FRCy | exact Hfcs | exact HEy | exact HEBy | exact LENM | exact MOK
        | exact (proj1 (hcells_cut _ _ _ _ _ _ CELLSy)) | exact (ngcells_cut672 _ _ _ _ _ NGy) ].
    - (* [comment removed for export] *)
      (destruct RM as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros HEBy (cpad & HCURy) COFF CREM CR1 CR2 CBT LEN' GRD'; nd_post).
      cbn [pc_bufalloc pc_bufdata ngc_p] in CR1, LEN', GRD'.
      set (bt := cur_block_type c) in *.
      assert (NGIy : ngi_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m f qs P sw BS0 MINOR
                       RNGy sy my qb' B' ba' bufdata' sg i I pad bs' e j (cursor_cells B' c cpad) fcs k0 k1 k2).
      { split; [exact INVy|]. split; [exact FRAy|]. split; [unfold cursor_cells; rewrite COFF; fold bt; exact HCURy|]. split; [reflexivity|]. split; [exact FRCy|]. split; [exact Hfcs|].
        split; [exact HEy|]. split; [exact HEBy|]. split; [exact CELLSy|]. split; [exact NGy|]. split; [exact UTS|]. split; [exact MB|].
        split; [exact IC|]. split; [exact IS|]. split; [exact HIFy|]. split; [exact BUFy|]. split; [exact PFXy|].
        split; [lia|]. split; [exact BARy|]. split; [exact BSBy| exact GRD']. }
      hide NGIy. hide INVy. hide FRAy. hide FRCy. hide HEy. hide HEBy. hide CELLSy. hide NGy. hide BUFy.
      ienterG. zstep. if_false. zstep. if_false.
      zstep. rewrite (sx32_s32 bt) by lia. zstep. zstep.
      unfold bv_ltu. rewrite (unsigned_lit 2), (bt_minus2_ltuA bt) by lia.
      (* [comment removed for export] *)
      assert (PKT : forall (a1x : word), (bt = 2 \/ bt = 3 \/ bt = 6)%Z ->
        evtF asegs RNGy (fun ms1 => implMG RNGy (mbind (ngc_K MOps PR fuel (RB_Ok c (ngc_p f qs sw BS0 MINOR qb' ba' bufdata' sg i))) (ngc_loop_tail MOps PR 0)) sy POSTQ ms1)
          (MS (mkR (Z_to_bv 64 0x8b330) (Z_to_bv 64 SPA) gp tp x x0 x1 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (s32 bt)) a1x x3 x4 x5 x6 x7 x8
                   (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 (-1)) (Z_to_bv 64 FA) (Z_to_bv 64 2) (Z_to_bv 64 6)
                   (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) x9 x10 x11 x12)
              F (Z_to_bv 64 0x8b418) fc None my (seg_rom asegs))).
      { intros a1x HBT.
        unfold ngc_K. fold bt. replace (bt =? BT_IDB)%Z with false by (symmetry; apply Z.eqb_neq; unfold BT_IDB; lia).
        replace ((bt =? BT_EPB) || (bt =? BT_SPB) || (bt =? BT_PB))%Z with true
          by (unfold BT_EPB, BT_SPB, BT_PB; destruct HBT as [-> |[-> | ->]]; reflexivity). cbv iota.
        do 4 zstep.
        unhide INVy. unhide FRAy. unhide FRCy. unhide HEy. unhide HEBy. unhide CELLSy. unhide NGy.
        apply evtF_done. subst POSTQ. apply implMG_retb. unfold ngc_loop_tail, ngc_fail.
        cbn [ngc_p pc_priv ng_ifaces_ptr_of pc_buffer pc_self free_opt e_free e_fret prims mo_bind mo_ret MOps].
        eapply (ngc_mcp_fail HO FO GIOA TP fflagA GL FRET FREE FREENULL) with (j := j) (ccs := [C8 (Z_to_bv 64 (B' + 8)); C8 (Z_to_bv 64 (cur_remaining c)); C4 (Z_to_bv 64 bt); CB 4 cpad])
                 (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (e := e) (SRC := 0x22280%Z) (n := 76%Z);
          [ exact CTX | exact INVy | exact HI | exact FRAy | exact HCURy | reflexivity | exact FRCy | exact Hfcs | exact HEy | exact HEBy
          | exact (proj1 (hcells_cut _ _ _ _ _ _ CELLSy)) | exact (ngcells_cut672 _ _ _ _ _ NGy)
          | exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs my 0x22280 (map b8 Msg.packet_before_idb ++ [Z_to_bv 8 0]) MIy ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; discriminate)))
          | vm_compute; reflexivity | lia | unfold client_globals; repeat (first [left; reflexivity | right]) | msg_ok ]. }
      destruct (Z.eq_dec bt 2) as [E2'|N2]; [| destruct (Z.eq_dec bt 3) as [E3|N3]].
      1,2: replace ((bt =? 2) || (bt =? 3))%Z with true by (symmetry; apply Bool.orb_true_iff; first [left; apply Z.eqb_eq; exact E2' | right; apply Z.eqb_eq; exact E3]); cbv iota.
      1,2: apply PKT; lia.
      replace ((bt =? 2) || (bt =? 3))%Z with false by (symmetry; rewrite (proj2 (Z.eqb_neq _ _) N2), (proj2 (Z.eqb_neq _ _) N3); reflexivity). cbv iota.
      (* [comment removed for export] *)
      zstep. rewrite (eqb_s32_litA bt 6) by lia.
      destruct (Z.eq_dec bt 6) as [E6|N6].
      { rewrite (proj2 (Z.eqb_eq _ _) E6). cbv iota. apply PKT; lia. }
      rewrite (proj2 (Z.eqb_neq _ _) N6). cbv iota.
      (* [comment removed for export] *)
      zstep. zstep. rewrite (eqb_s32_litA bt 1) by lia.
      destruct (Z.eq_dec bt 1) as [E1'|N1].
      + (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_eq _ _) E1'). cbn [negb]. cbv iota.
        unhide NGIy.
        apply evtF_done. subst POSTQ.
        eapply (ngc_idb HO FO sites GIOA TP fflagA GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF) with (c := c) (cpad := cpad) (j := j) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2)
                 (pad := pad) (bs := bs') (e := e) (I := I);
          [ exact CTX | exact NGIy | exact LEN' | exact COFF | exact CREM | exact CR2 | exact E1' | exact BS0R | exact MINR ].
      + (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_neq _ _) N1). cbn [negb]. cbv iota.
        unhide NGIy.
        apply evtF_done. subst POSTQ.
        unfold ngc_K. fold bt. replace (bt =? BT_IDB)%Z with false by (symmetry; apply Z.eqb_neq; unfold BT_IDB; lia).
        replace ((bt =? BT_EPB) || (bt =? BT_SPB) || (bt =? BT_PB))%Z with false
          by (unfold BT_EPB, BT_SPB, BT_PB; rewrite (proj2 (Z.eqb_neq _ _) N6), (proj2 (Z.eqb_neq _ _) N3), (proj2 (Z.eqb_neq _ _) N2); reflexivity). cbv iota.
        fold (ngc_find MOps PR fuel 0 (ngc_p f qs sw BS0 MINOR qb' ba' bufdata' sg i)).
        eapply IH; [exact CTX| exact NGIy| exact BS0R| exact MINR].
  Qed.
End NgcLoop.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_fail3A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_msgA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_okA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_idbcA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_idbA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

(* [comment removed for export] *)
Lemma bt_minus2_ltuA : forall bt, (0 <= bt < 2^32)%Z ->
  ((bv_unsigned (Z_to_bv 64 (s32 bt + -2)) <? 2) = ((bt =? 2) || (bt =? 3)))%Z.
Proof.
  intros bt Hbt. rewrite unsigned_lit_wrap. unfold s32.
  destruct (Z.eq_dec bt 2) as [->|N2]; [reflexivity|]. destruct (Z.eq_dec bt 3) as [->|N3]; [reflexivity|].
  rewrite (proj2 (Z.eqb_neq _ _) N2), (proj2 (Z.eqb_neq _ _) N3). cbn [orb]. apply Z.ltb_ge.
  change (bv_modulus 64) with (2^64)%Z. Z.div_mod_to_equations. lia.
Qed.

Lemma eqb_s32_litA : forall bt k, (0 <= bt < 2^32)%Z -> (0 <= k < 2^31)%Z -> bv_eqb (Z_to_bv 64 (s32 bt)) (Z_to_bv 64 k) = (bt =? k)%Z.
Proof.
  intros bt k Hb Hk. unfold bv_eqb. rewrite unsigned_lit_wrap, (unsigned_lit k) by lia. unfold s32. change (bv_modulus 64) with (2^64)%Z.
  destruct (Z.eqb_spec bt k) as [->|NE]; [apply Z.eqb_eq| apply Z.eqb_neq]; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma msg_ok_b1 : forall l : list Z, forallb (fun z => (0 <? z)%Z && (z <? 256)%Z) l = true -> Forall (fun z => 0 < z < 256)%Z l.
Proof. intros l H. apply Forall_forall. intros x Hx. rewrite forallb_forall in H. specialize (H x Hx). apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia. Qed.
Ltac msg_ok := first [ apply msg_ok_b1; vm_compute; reflexivity
                     | vm_compute; repeat first [apply Forall_nil | apply Forall_cons; [split; reflexivity|]] ].

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcLoop.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.
  Hypothesis RBLK : read_block_stmt HO FO sites GIOA TP.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).
  #[local] Notation PR := (prims HO FO sites).

  Lemma ngc_loop : forall (fuel : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (qs qb : hptr) (P B ba : Z) (sw : bool) (BS0 MINOR : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) (I : Z)
      (pad bs e j : list byte) (ccs fcs : list cell) (k0 k1 k2 : word),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngi_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m f qs P sw BS0 MINOR
            RNGx sx mm qb B ba bufdata sg i I pad bs e j ccs fcs k0 k1 k2 ->
    (1 <= BS0 <= 2^21)%Z -> (0 <= MINOR < 2^16)%Z ->
    implMG RNGx (ngc_find MOps PR fuel 0 (ngc_p f qs sw BS0 MINOR qb ba bufdata sg i)) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 FA) (Z_to_bv 64 (-1)) (Z_to_bv 64 2) (Z_to_bv 64 6)   (* [comment removed for export] *)
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b2c4) fc None mm (seg_rom asegs)).
  Proof using GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK.
    induction fuel as [|fuel IH]; intros until k2; intros CTX NGI BS0R MINR.
    { unfold ngc_find. cbn [ng_find_idb].
      eapply (implMG_bind _ _ _ _ (fun _ _ _ _ => False)); [apply implMG_unr | intros a' s' R' ms' X; exact (False_rect _ X)]. }
    (pose proof NGI as ndP__; nd_pre ndP__ 21%nat; intros INV FRA FCUR Hccs FRC Hfcs HE HEB CELLS NG5 UTS MB IC IS HIF BUF5 PFX LBA BAR BSB GRD; nd_post).
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    (pose proof (ngc_tr_a3 _ _ _ _ TR) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ TRRB _; nd_post).
    assert (UCm : ucallerA (depth_check_header true) L mm sp s0 ra trC) by (eapply (ngc_uc_now FO GIOA TP fflagA GL); [exact CTX| exact INV]).
    edestruct (ngc_cobj_now FO GIOA TP fflagA GL) as (_ & _ & OEB'); [exact CTX| exact INV|].
    (* [comment removed for export] *)
    assert (HinP : In (qs, P, 680%Z) ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg)) by (left; reflexivity).
    assert (HinB : In (qb, B, ba) ((qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg)) by (right; left; reflexivity).
    assert (EPB : (qs, P, 680%Z) :: (qb, B, ba) :: IBLK i I sg = pcap_blocks (ngc_p f qs sw BS0 MINOR qb ba bufdata sg i) P B I)
      by (unfold pcap_blocks, psize, is_ng; cbn [pc_priv pc_self pc_buffer pc_bufalloc ngc_p]; destruct i; reflexivity).
    destruct (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G EPB) as (APB & API).
    unfold psize, is_ng in APB, API. cbn [pc_priv pc_bufalloc ngc_p] in APB, API. unfold PCAP_NG_SF_TOTAL in APB, API.
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ndP__; nd_pre ndP__ 3%nat; intros (_ & _ & PTOP & _) P0 _; nd_post).
    cbn [cb_addr cb_size fst snd] in PTOP, P0.
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) 4%nat; intros kBP kBPr kBP1 kBP2; nd_post).
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn; lia)) 4%nat; intros kBB kBBr kBB1 kBB2; nd_post).
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)) 4%nat; intros kEP kEPr kEP1 kEP2; nd_post).
    cbn [cb_addr cb_size fst snd] in kBP1, kBP2, kBB1, kBB2, kEP1, kEP2.
    (nd_pre (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ (qs, P, 680%Z) (NGFR Fb) G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP) ltac:(left; reflexivity) ltac:(cbn; lia)) 4%nat; intros kPF kPFr kPF1 kPF2; nd_post).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2.
    assert (HI : match i with Some _ => True | None => I = 0%Z end).
    { unfold ifaces_ok in HIF. cbn [pc_priv ngc_p] in HIF. destruct i; [exact Logic.I| exact (proj1 HIF)]. }
    (* [comment removed for export] *)
    assert (IFACTS : forall q a, i = Some q -> (I <= a < I + 40 * ng_ifaces_size sg)%Z ->
              (~ (EB <= a < EB + 256) /\ a < ATOP /\ ~ (P <= a < P + 680) /\ in_block ((CL ++ [(qs, P, PCAP_NG_SF_TOTAL)]) ++ IBLK i I sg) a)%Z).
    { intros q a -> Ha. cbn [IBLK] in G.
      assert (HinI : In (q, I, (40 * ng_ifaces_size sg)%Z) ((qs, P, 680%Z) :: (qb, B, ba) :: [(q, I, (40 * ng_ifaces_size sg)%Z)])) by (right; right; left; reflexivity).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinI)) as ndP__; nd_pre ndP__ 3%nat; intros (_ & _ & IT & _) I0 _; nd_post).
      cbn [cb_addr cb_size fst snd] in IT, I0.
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinI ltac:(lia) ltac:(cbn; lia)) 4%nat; intros kBI kBIr kBI1 kBI2; nd_post).
      cbn [cb_addr cb_size fst snd] in kBI1, kBI2. destruct (API sg q eq_refl) as (IP & IB).
      split; [lia|]. split; [lia|]. split; [lia|].
      apply in_block_app. right. cbn [IBLK]. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    (* [comment removed for export] *)
    unfold ngc_find. rewrite (ng_find_idb_S MOps PR). apply implMG_bind_assoc. fold (ngc_find MOps PR fuel 0).
    pose proof (hcells_cut20 _ _ _ _ _ _ CELLS) as HBS. pose proof (proj2 (hcells_cut _ _ _ _ _ _ CELLS)) as HPV. pose proof (ngcells_cut656 _ _ _ _ _ NG5) as HMB.
    pose proof FRA as FRAu. unfold ngc_spill in FRAu.
    hide FRA. hide FRC. hide HE. hide HEB. hide CELLS. hide NG5. hide FR. hide MGc. hide SHC. hide BUF5. hide FCUR. hide HBS. hide HPV. hide HMB.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    do 4 zstep. zstep.
    clear MU WM FRAu.
    unhide FRA. unhide FRC. unhide HE. unhide HEB. unhide CELLS. unhide NG5. unhide FR. unhide MGc. unhide SHC. unhide BUF5. unhide FCUR. unhide HBS. unhide HPV. unhide HMB.
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply RBLK with (L := L) (st := sx) (C1 := (CL ++ [(qs, P, PCAP_NG_SF_TOTAL)])%list) (C2 := IBLK i I sg) (FB := FB) (FL := NGFR Fb :: FL) (trC := (bv_unsigned ra :: trC)%list)
                       (f := f) (Af := FA) (P := P) (B := B) (CUR := (SPA + 128)%Z) (EB := EB) (lo := lo) (p := ngc_p f qs sw BS0 MINOR qb ba bufdata sg i) (s := sg) (i := i)
                       (a_bhdr := DStack SiteBhdrCheckHeader 0) (bs := bs) (ej := e) (ccs := ccs).
      - rewrite <- app_assoc. cbn [app pc_buffer pc_bufalloc ngc_p]. unfold PCAP_NG_SF_TOTAL.
        eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G| exact ST| exact MI| unfold READ_BLOCK_STACK, PCAP_L1_STACK, PCAP_L2_STACK; lia].
      - eapply (ngc_ucaller 2%nat) with (X := 0x8b2d8%Z); [exact UCm| exact SPAB| lia| exact SPT| exact ALN| exact FR| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_ng_check_header; lia].
      - rewrite unsigned_lit by lia. exact TRRB.
      - apply nofr_cons; [eapply nofr_sub; [exact NF|]|].
        + intros ff Hf. unfold frames_read_block in Hf. unfold frames_check_header, frames_pcap_ng_check_header.
          destruct Hf as [<-|[<-|[]]]; [right; right; left; reflexivity| right; left; reflexivity].
        + unfold fb_fn, frames_read_block. cbn [fst]. intros [E|[E|[]]]; discriminate E.
      - exact HinF.
      - reflexivity.
      - reflexivity.
      - apply in_or_app; left; apply in_or_app; right; left; reflexivity.
      - exists SiteBhdrCheckHeader. split; reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - split; [exact HBS|]. split; [exact HPV|]. split; [exact HMB|]. rewrite MB. unfold INITIAL_MAX_BLOCKSIZE. cbn [pc_bufsize pc_bufalloc ngc_p]. lia.
      - exact BUF5.
      - exact PFX.
      - cbn [pc_bufdata pc_bufalloc ngc_p]; lia.
      - exact FCUR.
      - exact Hccs.
      - rewrite ESPA. lia.
      - Z.div_mod_to_equations; lia.
      - exact HEB.
      - left. split; [split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB') (incl_appl _ (incl_appl _ (incl_refl _))) IFL)| exact (proj2 OEB')]|].
        cbn [pc_bufalloc ngc_p]. unfold PCAP_NG_SF_TOTAL. lia.
      - exact EB8. }
    intros rb sy RNGy msy PO. cbv beta in PO.
    (nd_pre PO 23%nat; intros FPy a0v my p' B' bs' E OFy MIy STy AGy Gy BHy BUFy PFXy LENy PRIVE RFE SELFE BSZE SWE META RM; nd_post).
    rewrite ESPA in *. post_regs E.
    (* [comment removed for export] *)
    destruct p' as [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17]. unfold same_meta in META.
    cbn [pc_priv pc_rfile pc_self pc_bufsize pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
         pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_buffer pc_bufalloc pc_bufdata ngc_p] in PRIVE, RFE, SELFE, BSZE, SWE, META, RM, Gy, BHy, BUFy, PFXy, LENy, AGy.
    (nd_pre META 9%nat; intros M1 M2 M3 M4 M5 M6 M7 M8 M9; nd_post). subst f1 f2 f3 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17.
    rename f4 into ba'. rename f5 into qb'. rename f6 into bufdata'.
    change (mkPcap qs f BS0 ba' qb' bufdata' sw 1 MINOR 0 0 0 0 0 [] hdr0 (PrivNg sg i)) with (ngc_p f qs sw BS0 MINOR qb' ba' bufdata' sg i) in *.
    (nd_pre BHy 7%nat; intros HBSy HPVy HMBy _ _ BARy BSBy; nd_post). cbn [pc_bufsize pc_bufalloc pc_swapped ngc_p] in HBSy, HPVy, BARy, BSBy.
    (* [comment removed for export] *)
    assert (Gy' : GIOA L RNGy sy (CL ++ (qs, P, 680%Z) :: (qb', B', ba') :: IBLK i I sg) FB (NGFR Fb :: FL) my).
    { eapply GPL; [exact Gy|]. unfold PCAP_NG_SF_TOTAL. rewrite <- app_assoc. cbn [app].
      apply Permutation.Permutation_sym. eapply Permutation.Permutation_trans; [apply Permutation.Permutation_app_comm|]. cbn [app].
      eapply Permutation.Permutation_trans; [apply Permutation.perm_swap|]. apply Permutation.perm_skip.
      eapply Permutation.Permutation_trans; [|apply Permutation.Permutation_app_comm]. cbn [app]. apply Permutation.Permutation_refl. }
    assert (INVy : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGy sy ((qs, P, 680%Z) :: (qb', B', ba') :: IBLK i I sg) my).
    { eapply (ngc_inv_keep2 FO GIOA TP fflagA GL) with (CLk := ((CL ++ [(qs, P, PCAP_NG_SF_TOTAL)]) ++ IBLK i I sg)%list)
          (Pn := fun a => (~ (P + 24 <= a < P + 32) /\ ~ (SPA + 128 <= a < SPA + 128 + 24) /\ ~ (EB <= a < EB + 256))%Z);
        [exact CTX| exact INV| exact FPy| exact Gy'| exact OFy| exact MIy| exact STy| exact AGy| apply incl_appl, incl_appl, incl_refl| ].
      intros a N1 N2 NPBa NSP. pose proof (NPBa _ HinP) as X1. cbn [cb_addr cb_size fst snd] in X1. lia. }
    (* [comment removed for export] *)
    assert (KEEP : forall A cs, rw_cells asegs mm A cs ->
                     ((SPA <= A /\ A + Z.of_nat (cells_size cs) <= SPA + 128) \/ (Fb <= A /\ A + Z.of_nat (cells_size cs) <= Fb + 64)
                      \/ (ERR = A /\ cells_size cs = 4%nat) \/ (P + 32 <= A /\ A + Z.of_nat (cells_size cs) <= P + 680))%Z -> rw_cells asegs my A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AGy| exact HC|]. intros a Ha.
      destruct HA as [HA|[HA|[HA|HA]]].
      - split; [left; lia| lia].
      - split; [right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia| lia].
      - destruct HA as (<- & HS). rewrite HS in Ha. split; [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_appl _ (incl_appl _ (incl_refl _))) IFL)| lia]| lia].
      - split; [right; left; apply in_block_app; left; apply in_block_app; right; apply Exists_cons_hd; unfold PCAP_NG_SF_TOTAL; cbn [cb_addr cb_size fst snd]; lia| lia]. }
    pose proof (KEEP _ _ FRA ltac:(left; rewrite ngc_spill_size; lia)) as FRAy.
    pose proof (KEEP _ _ FRC ltac:(right; left; rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia)) as FRCy.
    pose proof (KEEP _ _ HE ltac:(right; right; left; split; reflexivity)) as HEy.
    pose proof (KEEP _ _ NG5 ltac:(right; right; right; unfold ng_cells; cbn [cells_size csize Nat.add]; lia)) as NGy.
    clear KEEP.
    assert (CELLSy : rw_cells asegs my P (ngc_hcells P sw BS0 MINOR B')).
    { eapply hcells_rebuf; [exact CELLS | | ].
      - eapply agrees_on_weaken; [exact AGy|]. intros a Ha. split; [| lia].
        right; left. apply in_block_app; left; apply in_block_app; right. apply Exists_cons_hd. unfold PCAP_NG_SF_TOTAL. cbn [cb_addr cb_size fst snd]. lia.
      - destruct (rw_cells_cut _ _ _ 1 HBSy) as [_ X2]. cbn [firstn skipn cells_size csize Nat.add app] in X2.
        replace (P + 24)%Z with (P + 20 + Z.of_nat 4)%Z by lia. exact X2. }
    assert (HIFy : ifaces_ok (ngc_p f qs sw BS0 MINOR qb' ba' bufdata' sg i) I my).
    { assert (HIF' : ifaces_ok (ngc_p f qs sw BS0 MINOR qb' ba' bufdata' sg i) I mm) by exact HIF.
      eapply ifaces_ok_agree; [exact AGy | | exact HIF']. intros sg' q E' a Ha. cbn [pc_priv ngc_p] in E'. injection E' as <- ->.
      (nd_pre (IFACTS q a eq_refl Ha) 4%nat; intros X1 X2 X3 X4; nd_post). split; [right; left; exact X4| lia]. }
    repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FPy) in HR end.
    pose proof (munch_refl ([] : list (Z * Z)) my) as MU. pose proof (wmono_refl asegs my) as WM.
    (* [comment removed for export] *)
    destruct rb as [p'' | msg p'' | c p''].
    - (* [comment removed for export] *)
      (destruct RM as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 2%nat; intros HEBy (ccs' & HCURy & Hccs'); nd_post).
      ienterG. zstep. if_false. zstep. if_true. do 3 zstep.
      apply evtF_done. subst POSTQ. unfold ngc_K. apply implMG_retb. unfold ngc_loop_tail, ngc_fail.
      cbn [ngc_p pc_priv ng_ifaces_ptr_of pc_buffer pc_self free_opt e_free e_fret prims mo_bind mo_ret MOps].
      eapply (ngc_mcp_fail HO FO GIOA TP fflagA GL FRET FREE FREENULL) with (j := j) (ccs := ccs') (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (e := e) (SRC := 0x22220%Z) (n := 53%Z);
        [ exact CTX | exact INVy | exact HI | exact FRAy | exact HCURy | exact Hccs' | exact FRCy | exact Hfcs | exact HEy | exact HEBy
        | exact (proj1 (hcells_cut _ _ _ _ _ _ CELLSy)) | exact (ngcells_cut672 _ _ _ _ _ NGy)
        | exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs my 0x22220 (map b8 Msg.no_idb ++ [Z_to_bv 8 0]) MIy ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; discriminate)))
        | vm_compute; reflexivity | lia | unfold client_globals; repeat (first [left; reflexivity | right]) | msg_ok ].
    - (* [comment removed for export] *)
      (destruct RM as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros (junk4 & HEBy) LENM MOK (ccs' & HCURy & Hccs'); nd_post).
      ienterG. zstep. if_true.
      apply evtF_done. subst POSTQ. unfold ngc_K. apply implMG_retb. unfold ngc_loop_tail, ngc_fail.
      cbn [ngc_p pc_priv ng_ifaces_ptr_of pc_buffer pc_self free_opt e_free e_fret prims mo_bind mo_ret MOps].
      eapply (ngc_fail3 HO FO GIOA TP fflagA GL FRET FREE FREENULL) with (j := j) (ccs := ccs') (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2);
        [ exact CTX | exact INVy | exact HI | exact FRAy | exact HCURy | exact Hccs' | exact FRCy | exact Hfcs | exact HEy | exact HEBy | exact LENM | exact MOK
        | exact (proj1 (hcells_cut _ _ _ _ _ _ CELLSy)) | exact (ngcells_cut672 _ _ _ _ _ NGy) ].
    - (* [comment removed for export] *)
      (destruct RM as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros HEBy (cpad & HCURy) COFF CREM CR1 CR2 CBT LEN' GRD'; nd_post).
      cbn [pc_bufalloc pc_bufdata ngc_p] in CR1, LEN', GRD'.
      set (bt := cur_block_type c) in *.
      assert (NGIy : ngi_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m f qs P sw BS0 MINOR
                       RNGy sy my qb' B' ba' bufdata' sg i I pad bs' e j (cursor_cells B' c cpad) fcs k0 k1 k2).
      { split; [exact INVy|]. split; [exact FRAy|]. split; [unfold cursor_cells; rewrite COFF; fold bt; exact HCURy|]. split; [reflexivity|]. split; [exact FRCy|]. split; [exact Hfcs|].
        split; [exact HEy|]. split; [exact HEBy|]. split; [exact CELLSy|]. split; [exact NGy|]. split; [exact UTS|]. split; [exact MB|].
        split; [exact IC|]. split; [exact IS|]. split; [exact HIFy|]. split; [exact BUFy|]. split; [exact PFXy|].
        split; [lia|]. split; [exact BARy|]. split; [exact BSBy| exact GRD']. }
      hide NGIy. hide INVy. hide FRAy. hide FRCy. hide HEy. hide HEBy. hide CELLSy. hide NGy. hide BUFy.
      ienterG. zstep. if_false. zstep. if_false.
      zstep. rewrite (sx32_s32 bt) by lia. zstep. zstep.
      unfold bv_ltu. rewrite (unsigned_lit 2), (bt_minus2_ltuA bt) by lia.
      (* [comment removed for export] *)
      assert (PKT : forall (a1x : word), (bt = 2 \/ bt = 3 \/ bt = 6)%Z ->
        evtF asegs RNGy (fun ms1 => implMG RNGy (mbind (ngc_K MOps PR fuel (RB_Ok c (ngc_p f qs sw BS0 MINOR qb' ba' bufdata' sg i))) (ngc_loop_tail MOps PR 0)) sy POSTQ ms1)
          (MS (mkR (Z_to_bv 64 0x8b2d8) (Z_to_bv 64 SPA) gp tp x x0 x1 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (s32 bt)) a1x x3 x4 x5 x6 x7 x8
                   (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 FA) (Z_to_bv 64 (-1)) (Z_to_bv 64 2) (Z_to_bv 64 6)
                   (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) x9 x10 x11 x12)
              F (Z_to_bv 64 0x8b59c) fc None my (seg_rom asegs))).
      { intros a1x HBT.
        unfold ngc_K. fold bt. replace (bt =? BT_IDB)%Z with false by (symmetry; apply Z.eqb_neq; unfold BT_IDB; lia).
        replace ((bt =? BT_EPB) || (bt =? BT_SPB) || (bt =? BT_PB))%Z with true
          by (unfold BT_EPB, BT_SPB, BT_PB; destruct HBT as [-> |[-> | ->]]; reflexivity). cbv iota.
        do 4 zstep.
        unhide INVy. unhide FRAy. unhide FRCy. unhide HEy. unhide HEBy. unhide CELLSy. unhide NGy.
        apply evtF_done. subst POSTQ. apply implMG_retb. unfold ngc_loop_tail, ngc_fail.
        cbn [ngc_p pc_priv ng_ifaces_ptr_of pc_buffer pc_self free_opt e_free e_fret prims mo_bind mo_ret MOps].
        eapply (ngc_mcp_fail HO FO GIOA TP fflagA GL FRET FREE FREENULL) with (j := j) (ccs := [C8 (Z_to_bv 64 (B' + 8)); C8 (Z_to_bv 64 (cur_remaining c)); C4 (Z_to_bv 64 bt); CB 4 cpad])
                 (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (e := e) (SRC := 0x22280%Z) (n := 76%Z);
          [ exact CTX | exact INVy | exact HI | exact FRAy | exact HCURy | reflexivity | exact FRCy | exact Hfcs | exact HEy | exact HEBy
          | exact (proj1 (hcells_cut _ _ _ _ _ _ CELLSy)) | exact (ngcells_cut672 _ _ _ _ _ NGy)
          | exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs my 0x22280 (map b8 Msg.packet_before_idb ++ [Z_to_bv 8 0]) MIy ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; discriminate)))
          | vm_compute; reflexivity | lia | unfold client_globals; repeat (first [left; reflexivity | right]) | msg_ok ]. }
      destruct (Z.eq_dec bt 2) as [E2'|N2]; [| destruct (Z.eq_dec bt 3) as [E3|N3]].
      1,2: replace ((bt =? 2) || (bt =? 3))%Z with true by (symmetry; apply Bool.orb_true_iff; first [left; apply Z.eqb_eq; exact E2' | right; apply Z.eqb_eq; exact E3]); cbv iota.
      1,2: apply PKT; lia.
      replace ((bt =? 2) || (bt =? 3))%Z with false by (symmetry; rewrite (proj2 (Z.eqb_neq _ _) N2), (proj2 (Z.eqb_neq _ _) N3); reflexivity). cbv iota.
      (* [comment removed for export] *)
      zstep. rewrite (eqb_s32_litA bt 6) by lia.
      destruct (Z.eq_dec bt 6) as [E6|N6].
      { rewrite (proj2 (Z.eqb_eq _ _) E6). cbv iota. apply PKT; lia. }
      rewrite (proj2 (Z.eqb_neq _ _) N6). cbv iota.
      (* [comment removed for export] *)
      zstep. zstep. rewrite (eqb_s32_litA bt 1) by lia.
      destruct (Z.eq_dec bt 1) as [E1'|N1].
      + (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_eq _ _) E1'). cbn [negb]. cbv iota.
        unhide NGIy.
        apply evtF_done. subst POSTQ.
        eapply (ngc_idb HO FO sites GIOA TP fflagA GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF) with (c := c) (cpad := cpad) (j := j) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2)
                 (pad := pad) (bs := bs') (e := e) (I := I);
          [ exact CTX | exact NGIy | exact LEN' | exact COFF | exact CREM | exact CR2 | exact E1' | exact BS0R | exact MINR ].
      + (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_neq _ _) N1). cbn [negb]. cbv iota.
        unhide NGIy.
        apply evtF_done. subst POSTQ.
        unfold ngc_K. fold bt. replace (bt =? BT_IDB)%Z with false by (symmetry; apply Z.eqb_neq; unfold BT_IDB; lia).
        replace ((bt =? BT_EPB) || (bt =? BT_SPB) || (bt =? BT_PB))%Z with false
          by (unfold BT_EPB, BT_SPB, BT_PB; rewrite (proj2 (Z.eqb_neq _ _) N6), (proj2 (Z.eqb_neq _ _) N3), (proj2 (Z.eqb_neq _ _) N2); reflexivity). cbv iota.
        fold (ngc_find MOps PR fuel 0 (ngc_p f qs sw BS0 MINOR qb' ba' bufdata' sg i)).
        eapply IH; [exact CTX| exact NGIy| exact BS0R| exact MINR].
  Qed.
End NgcLoop.
End CANSEC1.
End TwB.
End F_ngchk_loopA.

(* [comment removed for export] *)
Module F_ngchk_fverA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfHandleA F_ngchk_modelA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_fail3A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_msgA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_loopA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_fsegA.
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
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

(* [comment removed for export] *)
Definition shb_hdr (TL : Z) : list Z := le_bytes 4 BT_SHB ++ le_bytes 4 TL ++ le_bytes 4 BYTE_ORDER_MAGIC.
Lemma shb_hdr_length : forall TL, length (shb_hdr TL) = 12%nat.
Proof. intros. unfold shb_hdr. rewrite !length_app, !OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.length_le_bytes. reflexivity. Qed.
Lemma shb_hdr_range : forall TL, Forall (fun z => 0 <= z < 256)%Z (shb_hdr TL).
Proof.
  intros. unfold shb_hdr. apply (proj2 (Forall_app _ _ _)). split; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le_bytes_4_range|].
  apply (proj2 (Forall_app _ _ _)). split; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le_bytes_4_range.
Qed.
Lemma shb_hdr_bytes : forall TL, (0 <= TL < 2^32)%Z ->
  map b8 (shb_hdr TL) = le4 (Z_to_bv 64 168627466) ++ le4 (Z_to_bv 64 TL) ++ le4 (Z_to_bv 64 439041101).
Proof.
  intros TL HT. unfold shb_hdr. rewrite !map_app.
  rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le4_le_bytes 168627466), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le4_le_bytes TL), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le4_le_bytes 439041101) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition apartk (A n X xs : Z) : Prop :=
  exists k, (0 <= k <= 1 /\ A + n <= X + k * 18446744073709551616 /\ X + xs <= A + (1 - k) * 18446744073709551616)%Z.

Section CANSEC0. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcBlocks.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).

  (* [comment removed for export] *)
  Definition ngc_blocks_ok__stmt : Prop := forall ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m
      RNGx sx mm (qs qb : hptr) P B BS0,
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [(qs, P, 680%Z); (qb, B, BS0)] mm ->
    (1 <= BS0)%Z ->
    exists bP kPF bU kUF kPU,
      ngblk_ok RNGx SPA P Fb bP kPF
      /\ (rng RNGx B BS0 /\ rng RNGx (shad B) (nshad BS0) /\ (B mod 16 = 0)%Z /\ (0 <= bU <= 1)%Z /\ (B + BS0 <= 2147446784 + bU * 140737479966720)%Z
          /\ (17594333495296 * bU <= B)%Z /\ (6303744 <= B)%Z /\ (B + BS0 <= SPA)%Z
          /\ (0 <= kUF <= 1)%Z /\ (B + BS0 <= Fb + kUF * 18446744073709551616)%Z /\ (Fb + 64 <= B + (1 - kUF) * 18446744073709551616)%Z
          /\ (0 <= kPU <= 1)%Z /\ (P + 680 <= B + kPU * 18446744073709551616)%Z /\ (B + BS0 <= P + (1 - kPU) * 18446744073709551616)%Z)
      /\ unpoisoned mm P (P + 680) /\ unpoisoned mm B (B + BS0)
      /\ (P + 680 <= ATOP /\ B + BS0 <= ATOP)%Z
      /\ apartk MG 4 P 680 /\ apartk ERR 4 P 680 /\ apartk EB 256 P 680 /\ apartk MG 4 B BS0 /\ apartk ERR 4 B BS0 /\ apartk EB 256 B BS0.
  Section Sz4.
  Variables ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx mm qs qb P B BS0 : ltac2:(SecDiet.SzSec.tyM 'ngc_blocks_ok__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_blocks_ok__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_blocks_ok__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL.
 intros CTX INV HBS.
    ngc_setup GL CTX INV.
    assert (HinP : In (qs, P, 680%Z) [(qs, P, 680%Z); (qb, B, BS0)]) by (left; reflexivity).
    assert (HinB : In (qb, B, BS0) [(qs, P, 680%Z); (qb, B, BS0)]) by (right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ((PBAND & _ & PTOP & P16) & P0 & PUNP & PRNG & PSRNG & _).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinB)) as ((BBAND & _ & BTOP & B16) & B0 & BUNP & BRNG & BSRNG & _).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0, PUNP, PRNG, PSRNG, BBAND, BTOP, B16, B0, BUNP, BRNG, BSRNG.
    band_ind PBAND bP. band_ind BBAND bU.
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ (qs, P, 680%Z) (NGFR Fb) G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP) ltac:(left; reflexivity) ltac:(cbn; lia)) as (kPF & kPFr & kPF1 & kPF2).
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ (qb, B, BS0) (NGFR Fb) G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinB) ltac:(left; reflexivity) ltac:(cbn; lia)) as (kUF & kUFr & kUF1 & kUF2).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2, kUF1, kUF2.
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _). apply blocks_apart_app_inv in BA as (_ & BA & _).
    cbn [blocks_apart] in BA. destruct BA as (F1 & _). pose proof (Forall_inv F1) as APB. unfold apart, cb_addr, cb_size in APB. cbn [fst snd] in APB.
    assert (KPU : exists kPU, (0 <= kPU <= 1 /\ P + 680 <= B + kPU * 18446744073709551616 /\ B + BS0 <= P + (1 - kPU) * 18446744073709551616)%Z)
      by (destruct APB as [X|X]; [exists 0%Z| exists 1%Z]; lia).
    destruct KPU as (kPU & kPUr & kPU1 & kPU2).
    atop_facts.
    exists bP, kPF, bU, kUF, kPU.
    split. { unfold ngblk_ok. split; [exact PRNG|]. split; [exact PSRNG|]. split; [eapply rng_sub'; [exact RSPA| lia]|]. split; [exact FRNG|].
             split; [exact P16|]. repeat (split; [lia|]). lia. }
    split. { split; [exact BRNG|]. split; [exact BSRNG|]. split; [exact B16|]. repeat (split; [lia|]). lia. }
    split; [exact PUNP|]. split; [exact BUNP|]. split; [lia|].
    unfold apartk.
    split; [exact (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia))|].
    split; [exact (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia))|].
    split; [exact (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia))|].
    split; [exact (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn; lia))|].
    split; [exact (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn; lia))|].
    exact (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn; lia)).
  Qed.
  End Sz4.
  Lemma ngc_blocks_ok : ltac:(let t := eval cbv delta [ngc_blocks_ok__stmt] in ngc_blocks_ok__stmt in exact t).
  Proof using GL. intros ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx mm qs qb P B BS0. ltac2:(SecDiet.SzSec.closeP 'ngc_blocks_ok__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End NgcBlocks.
End CANSEC0.

(* [comment removed for export] *)
Ltac fill_setup GL CTX INV :=
  ngc_setup GL CTX INV;
  match goal with TPx : tparams |- _ =>
    edestruct (ngc_blocks_ok _ _ TPx _ GL) as (bP & kPF & bU & kUF & kPU & PBK & BBK & PUNP & BUNP & (PTOP & BTOP) & (kMP & kMPr & kMP1 & kMP2) & (kEP & kEPr & kEP1 & kEP2) & (kBP & kBPr & kBP1 & kBP2)
                              & (kMU & kMUr & kMU1 & kMU2) & (kEU & kEUr & kEU1 & kEU2) & (kBU & kBUr & kBU1 & kBU2)); [exact CTX| exact INV| lia|] end;
  lazymatch goal with PBKh : ngblk_ok _ _ _ _ _ _ |- _ =>
    pose proof PBKh as (PRNG & PRSH & RSPk & RFR & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & _ & SPAHI & SPALO & kPFr & kPF1 & kPF2) end;
  lazymatch goal with BBKh : rng _ _ _ /\ rng _ (shad _) _ /\ _ |- _ =>
    pose proof BBKh as (BRNG & BRSH & B16 & bUr & bUhi & bUlo & bUimg & BSP & kUFr & kUF1 & kUF2 & kPUr & kPU1 & kPU2) end.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcFillVer.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.
  Hypothesis RBLK : read_block_stmt HO FO sites GIOA TP.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).
  #[local] Notation PR := (prims HO FO sites).
  #[local] Notation B8 := (C8 (Z_to_bv 64 0)).
  #[local] Notation B4 := (C4 (Z_to_bv 64 0)).
  #[local] Notation SG0 := (mkNg 1000000 INITIAL_MAX_BLOCKSIZE 0 0 []).

  (* [comment removed for export] *)
  Definition ngc_fill_ver__stmt : Prop := forall (fuel : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a2 a4 a5 t3 t4 t5 t6 : word)
      (qs qb : hptr) (P B BS0 TL : Z) (sw : bool) (v0 v1 v2 v3 : Z) (rest : list Z) (jr e j : list byte) (ccs fcs : list cell) (k0 k1 k2 : word),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [(qs, P, 680%Z); (qb, B, BS0)] mm ->
    (28 <= TL <= 1048576)%Z -> (2048 <= BS0 <= 1048576)%Z -> (TL <= BS0)%Z ->
    (0 <= v0 < 256)%Z -> (0 <= v1 < 256)%Z -> (0 <= v2 < 256)%Z -> (0 <= v3 < 256)%Z ->
    rw_cells asegs mm SPA (ngc_spill P EB Fb j) -> rw_cells asegs mm (SPA + 128) ccs -> cells_size ccs = 24%nat ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    rw_cells asegs mm P (ngcells P B8 (C4 (Z_to_bv 64 BS0)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 (Z.b2z sw))) B4 B4 B4 B4 B4 B4 B8) ->
    rw_cells asegs mm (P + 648) (ng_cells (mkNg 1000000 16777216 0 0 []) 0 pad0) ->
    rw_cells asegs mm B [C4 (Z_to_bv 64 168627466); C4 (Z_to_bv 64 TL); C4 (Z_to_bv 64 439041101)] ->
    rw_cells asegs mm (B + 12) [C2 (Z_to_bv 64 (v0 + 256 * v1)); C2 (Z_to_bv 64 (v2 + 256 * v3)); CB (length rest) (map b8 rest)] ->
    rw_cells asegs mm (B + TL) [CB (Z.to_nat (BS0 - TL)) jr] ->
    (Z.of_nat (length rest) = TL - 16)%Z -> Forall (fun z => 0 <= z < 256)%Z rest ->
    implMG RNGx (if negb ((v0 + 256 * v1 =? 1) && ((v2 + 256 * v3 =? 0) || (v2 + 256 * v3 =? 2)))%Z
                 then ngc_fail MOps PR (Msg.unsupported_pcapng_version (v0 + 256 * v1) (v2 + 256 * v3))
                        (mkPcap qs f BS0 BS0 qb (shb_hdr TL ++ v0 :: v1 :: v2 :: v3 :: rest) sw 0 0 0 0 0 0 0 [] hdr0 (PrivNg SG0 None))
                 else ngc_find MOps PR fuel 0
                        (mkPcap qs f BS0 BS0 qb (shb_hdr TL ++ v0 :: v1 :: v2 :: v3 :: rest) sw (v0 + 256 * v1) (v2 + 256 * v3) 0 0 0 0 0 [] hdr0 (PrivNg SG0 None))) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (B + 14)) (Z_to_bv 64 P) a2 (Z_to_bv 64 (v0 + 256 * v1)) a4 a5 (Z_to_bv 64 EB) (Z_to_bv 64 0)
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 (B + 12)) (Z_to_bv 64 FA) (Z_to_bv 64 B) (Z_to_bv 64 TL)
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b2a0) fc None mm (seg_rom asegs)).
  Section Sz5.
  Variables fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a2 a4 a5 t3 t4 t5 t6 qs qb P B BS0 TL sw v0 v1 v2 v3 rest jr e j ccs fcs k0 k1 k2 : ltac2:(SecDiet.SzSec.tyM 'ngc_fill_ver__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ngc_fill_ver__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_fill_ver__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK.
 intros CTX INV TLR BSR TLB V0 V1 V2 V3 FRA FCUR Hccs FRC Hfcs HE HEB CELLS NG HBH HDV HBR LREST GRr.
    fill_setup GL CTX INV.
    set (MAJ := (v0 + 256 * v1)%Z) in *. set (MIN := (v2 + 256 * v3)%Z) in *.
    assert (MAJR : (0 <= MAJ < 65536)%Z) by (subst MAJ; lia). assert (MINR : (0 <= MIN < 65536)%Z) by (subst MIN; lia).
    destruct ((MAJ =? 1) && ((MIN =? 0) || (MIN =? 2)))%Z eqn:VOK; cbn [negb]; cbv iota.
    - (* [comment removed for export] *)
      apply andb_true_iff in VOK as [M1 MOK]. apply Z.eqb_eq in M1.
      assert (HMIN : (MIN = 0 \/ MIN = 2)%Z) by (apply orb_true_iff in MOK as [X|X]; apply Z.eqb_eq in X; [left| right]; exact X).
      rewrite M1 in *.
      ienterG.
      eapply evtF_cut.
      { eapply (fill_segD_ok gp tp t0 t1 t2 sp t3 t4 t5 t6 F fc RNGx SPA P Fb EB ERR FA bP kPF sw TL BS0 j PBK BSR B bU kUF kPU BBK) with (MIN := MIN);
          [ exact HMIN | apply INV | exact PUNP | exact BUNP | exact FRA | exact CELLS | ].
        destruct (rw_cells_cut _ _ _ 2 HDV) as [X _]. cbn [firstn] in X. exact X. }
      cbv beta. intros ms' PO. destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & m9 & -> & MU9 & WM9 & MI9 & CELLS9).
      assert (AGS : agrees_on (fun a => outside [(P, P + 648)]%Z a) mm m9) by (eapply agrees_on_of_munch; [exact MU9 | exact WM9 | intros a _ Ho; exact Ho]).
      assert (ST9 : stk asegs m9 lo SPA) by (eapply agrees_stk; [exact AGS| exact ST| intros a Ha; cbn [outside fst snd]; lia]).
      assert (INV9 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx [(qs, P, 680%Z); (qb, B, BS0)] m9).
      { eapply (ngc_inv_own FO GIOA TP fflagA GL); [exact CTX| exact INV| | exact MU9| exact WM9| exact MI9| exact ST9| ].
        - apply Forall_cons; [|apply Forall_nil]. right; left. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
        - intros a Ha. cbn [outside fst snd]. lia. }
      assert (KEEP : forall A cs, rw_cells asegs mm A cs -> (A + Z.of_nat (cells_size cs) <= P \/ P + 648 <= A)%Z -> rw_cells asegs m9 A cs).
      { intros A cs HC HA. eapply agrees_rw_cells; [exact AGS| exact HC|]. intros a Ha. cbn [outside fst snd]. lia. }
      pose proof (KEEP _ _ FRA ltac:(rewrite ngc_spill_size; lia)) as FRA9.
      pose proof (KEEP _ _ FCUR ltac:(rewrite Hccs; lia)) as FCUR9.
      pose proof (KEEP _ _ FRC ltac:(rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia)) as FRC9.
      pose proof (KEEP _ _ HE ltac:(cbn [cells_size csize Nat.add]; lia)) as HE9.
      pose proof (KEEP _ _ HEB ltac:(cbn [cells_size csize Nat.add]; lia)) as HEB9.
      pose proof (KEEP _ _ NG ltac:(unfold ng_cells; cbn [cells_size csize Nat.add]; lia)) as NG9.
      pose proof (KEEP _ _ HBH ltac:(cbn [cells_size csize Nat.add]; lia)) as HBH9.
      pose proof (KEEP _ _ HDV ltac:(cbn [cells_size csize Nat.add]; lia)) as HDV9.
      pose proof (KEEP _ _ HBR ltac:(cbn [cells_size csize Nat.add]; lia)) as HBR9.
      clear KEEP.
      (* [comment removed for export] *)
      assert (Ljr : length jr = Z.to_nat (BS0 - TL)) by (pose proof (proj1 (proj1 HBR9)) as WF; cbn in WF; lia).
      assert (BUF9 : rw_cells asegs m9 B [CB (Z.to_nat BS0) (map b8 (shb_hdr TL ++ v0 :: v1 :: v2 :: v3 :: rest) ++ jr)]).
      { replace (B + 12)%Z with (B + Z.of_nat (cells_size [C4 (Z_to_bv 64 168627466); C4 (Z_to_bv 64 TL); C4 (Z_to_bv 64 439041101)]))%Z in HDV9 by (cbn; lia).
        pose proof (rw_cells_uncut _ _ _ _ _ HBH9 HDV9 ltac:(cbn; lia)) as J1.
        replace (B + TL)%Z with (B + Z.of_nat (cells_size ([C4 (Z_to_bv 64 168627466); C4 (Z_to_bv 64 TL); C4 (Z_to_bv 64 439041101)] ++ [C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 MIN); CB (length rest) (map b8 rest)])))%Z in HBR9
          by (rewrite cells_size_app; cbn [cells_size csize Nat.add]; lia).
        pose proof (rw_cells_uncut _ _ _ _ _ J1 HBR9 ltac:(reflexivity)) as J2. cbn [app] in J2.
        eapply rw_cells_recell; [exact J2 | cbn; rewrite ?length_app, ?length_map; cbn; rewrite ?length_app, ?shb_hdr_length; cbn; repeat split; try exact Logic.I; lia |].
        cbn [cells_bytes cbytes app]. rewrite map_app, (shb_hdr_bytes TL) by lia. cbn [map app]. rewrite <- M1. subst MAJ MIN. rewrite !le2_lit by lia. rewrite !app_nil_r, <- !app_assoc. reflexivity. }
      apply evtF_done. subst POSTQ.
      eapply (ngc_loop HO FO sites GIOA TP fflagA GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK) with (qs := qs) (qb := qb) (P := P) (B := B) (ba := BS0) (sw := sw) (BS0 := BS0) (MINOR := MIN)
               (bufdata := (shb_hdr TL ++ v0 :: v1 :: v2 :: v3 :: rest)%list) (sg := SG0) (i := None) (I := 0%Z) (pad := pad0) (e := e) (j := j) (ccs := ccs) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2);
        [ exact CTX | | lia | lia ].
      split; [exact INV9|]. split; [exact FRA9|]. split; [exact FCUR9|]. split; [exact Hccs|]. split; [exact FRC9|]. split; [exact Hfcs|].
      split; [exact HE9|]. split; [exact HEB9|]. split; [exact CELLS9|]. split; [exact NG9|].
      split; [reflexivity|]. split; [reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|].
      split; [unfold ifaces_ok; cbn; repeat split; reflexivity|].
      split; [exact BUF9|].
      split; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.firstn_len_app'; rewrite length_map; reflexivity|].
      split; [rewrite length_app, shb_hdr_length; cbn [length]; lia|]. split; [lia|]. split; [lia|].
      apply Forall_app. split; [apply shb_hdr_range|]. repeat (constructor; [cbv beta; lia|]). exact GRr.
    - (* [comment removed for export] *)
      assert (HBAD : ~ (MAJ = 1 /\ (MIN = 0 \/ MIN = 2))%Z).
      { intros (E1 & E2). rewrite E1 in VOK. cbn [Z.eqb Pos.eqb andb] in VOK. destruct E2 as [E2|E2]; rewrite E2 in VOK; discriminate VOK. }
      ienterG.
      eapply evtF_cut.
      { destruct (rw_cells_cut _ _ _ 2 HDV) as [HV2 _]. cbn [firstn] in HV2.
        eapply fill_segD_bad with (MAJ := MAJ) (MIN := MIN) (bP := bP) (kPF := kPF) (bU := bU) (kUF := kUF) (kPU := kPU);
          first [ exact PBK | exact BBK | exact BSR | exact TLR | exact MAJR | exact MINR | exact HBAD | exact MI | exact PUNP | exact BUNP | exact HV2 ]. }
      cbv beta. intros ms' PO. destruct PO as (z5 & ->).
      assert (MSG : fmt_at mm 0x221c0 "unsupported pcapng savefile version %u.%u"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm 0x221c0 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "unsupported pcapng savefile version %u.%u"%string) ++ [Z_to_bv 8 0])
                                 MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      apply evtF_done. subst POSTQ. unfold ngc_fail.
      cbn [pc_priv ng_ifaces_ptr_of pc_buffer pc_self free_opt e_free e_fret prims mo_bind mo_ret MOps].
      pose proof CELLS as CELLSu. unfold ngcells in CELLSu.
      destruct (rw_cells_cut _ _ _ 4 CELLSu) as [_ Y1]. destruct (rw_cells_cut _ _ _ 1 Y1) as [HPB _]. cbn [firstn skipn cells_size csize Nat.add app] in HPB.
      lazymatch type of HPB with rw_cells _ _ ?A _ => replace A with (P + 24)%Z in HPB by lia end.
      eapply (ngc_snp_fail HO FO GIOA TP fflagA GL FRET FREE FREENULL SNPRINTF) with (j := j) (ccs := ccs) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (e := e)
               (i := None) (sg := SG0) (qs := qs) (qb := qb) (P := P) (B := B) (I := 0%Z) (nb := BS0) (RA := 0x8b414%Z) (FMTA := 0x221c0%Z)
               (fs := "unsupported pcapng savefile version %u.%u"%string) (args := [AInt MAJ; AInt MIN]);
        [ exact CTX | exact INV | reflexivity | exact FRA | exact FCUR | exact Hccs | exact FRC | exact Hfcs | exact HE | exact HEB
        | exact HPB | exact (ngcells_cut672 _ _ _ _ _ NG)
        | right; reflexivity | exact MSG | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
        | vm_compute; reflexivity | repeat constructor | unfold Msg.unsupported_pcapng_version, PCAP_ERRBUF_SIZE; reflexivity ].
  Qed.
  End Sz5.
  Lemma ngc_fill_ver : ltac:(let t := eval cbv delta [ngc_fill_ver__stmt] in ngc_fill_ver__stmt in exact t).
  Proof using GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK. intros fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a2 a4 a5 t3 t4 t5 t6 qs qb P B BS0 TL sw v0 v1 v2 v3 rest jr e j ccs fcs k0 k1 k2. ltac2:(SecDiet.SzSec.closeP 'ngc_fill_ver__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_fill_after_rb__stmt : Prop := forall (fuel : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (qs qb : hptr) (P B BS0 TL : Z) (sw : bool) (got : list Z) (junk' jr e j : list byte) (ccs fcs : list cell) (k0 k1 k2 : word),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [(qs, P, 680%Z); (qb, B, BS0)] mm ->
    (28 <= TL <= 1048576)%Z -> (2048 <= BS0 <= 1048576)%Z -> (TL <= BS0)%Z ->
    rw_cells asegs mm SPA (ngc_spill P EB Fb j) -> rw_cells asegs mm (SPA + 128) ccs -> cells_size ccs = 24%nat ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    rw_cells asegs mm P (ngcells P B8 (C4 (Z_to_bv 64 BS0)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 (Z.b2z sw))) B4 B4 B4 B4 B4 B4 B8) ->
    rw_cells asegs mm (P + 648) (ng_cells (mkNg 1000000 16777216 0 0 []) 0 pad0) ->
    rw_cells asegs mm B [C4 (Z_to_bv 64 168627466); C4 (Z_to_bv 64 TL); C4 (Z_to_bv 64 439041101)] ->
    rw_cells asegs mm (B + 12) [CB (length got) (map b8 got); CB (Z.to_nat (TL - 12) - length got) junk'] ->
    rw_cells asegs mm (B + TL) [CB (Z.to_nat (BS0 - TL)) jr] ->
    (zlength got = TL - 12)%Z -> Forall (fun z => 0 <= z < 256)%Z got ->
    implMG RNGx (ngc_after_rb MOps PR fuel 0 sw (mkPcap qs f BS0 BS0 qb (shb_hdr TL) sw 0 0 0 0 0 0 0 [] hdr0 (PrivNg SG0 None)) RBS_Ok got) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 (B + 12)) (Z_to_bv 64 FA) (Z_to_bv 64 B) (Z_to_bv 64 TL)
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b218) fc None mm (seg_rom asegs)).
  Section Sz6.
  Variables fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 qs qb P B BS0 TL sw got junk' jr e j ccs fcs k0 k1 k2 : ltac2:(SecDiet.SzSec.tyM 'ngc_fill_after_rb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ngc_fill_after_rb__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_fill_after_rb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK.
 intros CTX INV TLR BSR TLB FRA FCUR Hccs FRC Hfcs HE HEB CELLS NG HBH HD HBR GLn GR.
    fill_setup GL CTX INV.
    unfold zlength in GLn.
    destruct got as [|g0 [|g1 [|g2 [|g3 rest]]]]; try (exfalso; cbn [length] in GLn; lia).
    pose proof (Forall_inv GR) as X0. pose proof (Forall_inv (Forall_inv_tail GR)) as X1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail GR))) as X2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail GR)))) as X3.
    cbv beta in X0, X1, X2, X3.
    assert (GRr : Forall (fun z => 0 <= z < 256)%Z rest) by (do 4 apply Forall_inv_tail in GR; exact GR).
    assert (Lrest : Z.of_nat (length rest) = (TL - 16)%Z) by (cbn [length] in GLn; lia).
    destruct (rw_cells_cut _ _ _ 1 HD) as [HDg _]. cbn [firstn skipn cells_size csize Nat.add app map] in HDg.
    pose proof (rw_cells_recell _ _ _ [C2 (Z_to_bv 64 (g0 + 256 * g1)); C2 (Z_to_bv 64 (g2 + 256 * g3)); CB (length rest) (map b8 rest)] HDg
                  ltac:(cbn; rewrite ?length_map; repeat split; first [reflexivity | lia | exact Logic.I])
                  ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit by lia; rewrite !app_nil_r; reflexivity)) as HDV. clear HDg.
    destruct (rw_cells_cut _ _ _ 2 HDV) as [HV HRST]. cbn [firstn skipn cells_size csize Nat.add app] in HV, HRST.
    lazymatch type of HRST with rw_cells _ _ ?A _ => replace A with (B + 16)%Z in HRST by lia end.
    (* [comment removed for export] *)
    unfold ngc_after_rb.
    cbn [pc_bufdata set_bufdata pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_swapped pc_snapshot pc_linktype pc_linktype_ext pc_priv pc_version_major pc_version_minor].
    assert (LH : Z.of_nat (length (shb_hdr TL)) = 12%Z) by (rewrite shb_hdr_length; reflexivity).
    ienterG.
    destruct sw; cbv iota;
      cbn [pc_bufdata set_bufdata pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_swapped pc_snapshot pc_linktype pc_linktype_ext pc_priv pc_version_major pc_version_minor].
    - (* [comment removed for export] *)
      eapply evtF_cut.
      { eapply (fill_segC_sw gp tp t0 t1 t2 sp t3 t4 t5 t6 F fc RNGx SPA P Fb EB ERR FA bP kPF true TL BS0 j PBK BSR B bU kUF kPU BBK) with (g0 := g0) (g1 := g1) (g2 := g2) (g3 := g3);
          [ reflexivity | exact MI | exact PUNP | exact BUNP | exact FRA | exact CELLS | exact HV | lia | lia | lia | lia ]. }
      cbv beta. intros ms' PO. destruct PO as (z2 & z4 & m7 & -> & MU7 & WM7 & MI7 & HV7).
      assert (AGS : agrees_on (fun a => outside [(B + 12, B + 16)]%Z a) mm m7) by (eapply agrees_on_of_munch; [exact MU7 | exact WM7 | intros a _ Ho; exact Ho]).
      assert (ST7 : stk asegs m7 lo SPA) by (eapply agrees_stk; [exact AGS| exact ST| intros a Ha; cbn [outside fst snd]; lia]).
      assert (INV7 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx [(qs, P, 680%Z); (qb, B, BS0)] m7).
      { eapply (ngc_inv_own FO GIOA TP fflagA GL); [exact CTX| exact INV| | exact MU7| exact WM7| exact MI7| exact ST7| ].
        - apply Forall_cons; [|apply Forall_nil]. right; left. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
        - intros a Ha. cbn [outside fst snd]. lia. }
      assert (KEEP : forall A cs, rw_cells asegs mm A cs -> (A + Z.of_nat (cells_size cs) <= B + 12 \/ B + 16 <= A)%Z -> rw_cells asegs m7 A cs).
      { intros A cs HC HA. eapply agrees_rw_cells; [exact AGS| exact HC|]. intros a Ha. cbn [outside fst snd]. lia. }
      pose proof (KEEP _ _ FRA ltac:(rewrite ngc_spill_size; lia)) as FRA7.
      pose proof (KEEP _ _ FCUR ltac:(rewrite Hccs; lia)) as FCUR7.
      pose proof (KEEP _ _ FRC ltac:(rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia)) as FRC7.
      pose proof (KEEP _ _ HE ltac:(cbn [cells_size csize Nat.add]; lia)) as HE7.
      pose proof (KEEP _ _ HEB ltac:(cbn [cells_size csize Nat.add]; lia)) as HEB7.
      pose proof (KEEP _ _ CELLS ltac:(rewrite ngcells_size by reflexivity; lia)) as CELLS7.
      pose proof (KEEP _ _ NG ltac:(unfold ng_cells; cbn [cells_size csize Nat.add]; lia)) as NG7.
      pose proof (KEEP _ _ HBH ltac:(cbn [cells_size csize Nat.add]; lia)) as HBH7.
      pose proof (KEEP _ _ HRST ltac:(cbn [cells_size csize Nat.add]; lia)) as HRST7.
      pose proof (KEEP _ _ HBR ltac:(cbn [cells_size csize Nat.add]; lia)) as HBR7.
      clear KEEP.
      assert (HDV7 : rw_cells asegs m7 (B + 12) [C2 (Z_to_bv 64 (g1 + 256 * g0)); C2 (Z_to_bv 64 (g3 + 256 * g2)); CB (length rest) (map b8 rest)]).
      { replace (B + 16)%Z with (B + 12 + Z.of_nat (cells_size [C2 (Z_to_bv 64 (g1 + 256 * g0)); C2 (Z_to_bv 64 (g3 + 256 * g2))]))%Z in HRST7 by (cbn; lia).
        exact (rw_cells_uncut _ _ _ _ _ HV7 HRST7 ltac:(reflexivity)). }
      assert (SW12 : swap_field 2 14 (swap_field 2 12 (shb_hdr TL ++ g0 :: g1 :: g2 :: g3 :: rest)) = shb_hdr TL ++ g1 :: g0 :: g3 :: g2 :: rest).
      { replace 12%Z with (Z.of_nat (length (shb_hdr TL))) by lia. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.swap2_at.
        replace 14%Z with (Z.of_nat (length (shb_hdr TL)) + 2)%Z by lia. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.swap2_at2. reflexivity. }
      rewrite !SW12.
      replace (get_le16 (shb_hdr TL ++ g1 :: g0 :: g3 :: g2 :: rest) 12) with (g1 + 256 * g0)%Z
        by (replace 12%Z with (Z.of_nat (length (shb_hdr TL))) by lia; symmetry; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.get_le16_at).
      replace (get_le16 (shb_hdr TL ++ g1 :: g0 :: g3 :: g2 :: rest) 14) with (g3 + 256 * g2)%Z
        by (replace 14%Z with (Z.of_nat (length (shb_hdr TL)) + 2)%Z by lia; symmetry; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.get_le16_at2).
      apply evtF_done. subst POSTQ.
      eapply (ngc_fill_ver fuel) with (qs := qs) (qb := qb) (P := P) (B := B) (BS0 := BS0) (TL := TL) (sw := true) (v0 := g1) (v1 := g0) (v2 := g3) (v3 := g2) (rest := rest)
               (jr := jr) (e := e) (j := j) (ccs := ccs) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2);
        [ exact CTX | exact INV7 | exact TLR | exact BSR | exact TLB | lia | lia | lia | lia | exact FRA7 | exact FCUR7 | exact Hccs | exact FRC7 | exact Hfcs | exact HE7 | exact HEB7
        | exact CELLS7 | exact NG7 | exact HBH7 | exact HDV7 | exact HBR7 | exact Lrest | exact GRr ].
    - (* [comment removed for export] *)
      eapply evtF_cut.
      { eapply (fill_segC_nat gp tp t0 t1 t2 sp t3 t4 t5 t6 F fc RNGx SPA P Fb EB ERR FA bP kPF false TL BS0 j PBK BSR B bU kUF kPU BBK) with (g0 := g0) (g1 := g1) (g2 := g2) (g3 := g3);
          [ reflexivity | exact MI | exact PUNP | exact BUNP | exact FRA | exact CELLS | exact HV | lia | lia | lia | lia ]. }
      cbv beta. intros ms' PO. destruct PO as (z2 & z4 & ->).
      replace (get_le16 (shb_hdr TL ++ g0 :: g1 :: g2 :: g3 :: rest) 12) with (g0 + 256 * g1)%Z
        by (replace 12%Z with (Z.of_nat (length (shb_hdr TL))) by lia; symmetry; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.get_le16_at).
      replace (get_le16 (shb_hdr TL ++ g0 :: g1 :: g2 :: g3 :: rest) 14) with (g2 + 256 * g3)%Z
        by (replace 14%Z with (Z.of_nat (length (shb_hdr TL)) + 2)%Z by lia; symmetry; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.get_le16_at2).
      apply evtF_done. subst POSTQ.
      eapply (ngc_fill_ver fuel) with (qs := qs) (qb := qb) (P := P) (B := B) (BS0 := BS0) (TL := TL) (sw := false) (v0 := g0) (v1 := g1) (v2 := g2) (v3 := g3) (rest := rest)
               (jr := jr) (e := e) (j := j) (ccs := ccs) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2);
        [ exact CTX | exact INV | exact TLR | exact BSR | exact TLB | lia | lia | lia | lia | exact FRA | exact FCUR | exact Hccs | exact FRC | exact Hfcs | exact HE | exact HEB
        | exact CELLS | exact NG | exact HBH | exact HDV | exact HBR | exact Lrest | exact GRr ].
  Qed.
  End Sz6.
  Lemma ngc_fill_after_rb : ltac:(let t := eval cbv delta [ngc_fill_after_rb__stmt] in ngc_fill_after_rb__stmt in exact t).
  Proof using GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK. intros fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 qs qb P B BS0 TL sw got junk' jr e j ccs fcs k0 k1 k2. ltac2:(SecDiet.SzSec.closeP 'ngc_fill_after_rb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcFillVer.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_fail3A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_msgA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_loopA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_fsegA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

(* [comment removed for export] *)
Definition shb_hdr (TL : Z) : list Z := le_bytes 4 BT_SHB ++ le_bytes 4 TL ++ le_bytes 4 BYTE_ORDER_MAGIC.
Lemma shb_hdr_length : forall TL, length (shb_hdr TL) = 12%nat.
Proof. intros. unfold shb_hdr. rewrite !length_app, !OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.length_le_bytes. reflexivity. Qed.
Lemma shb_hdr_range : forall TL, Forall (fun z => 0 <= z < 256)%Z (shb_hdr TL).
Proof.
  intros. unfold shb_hdr. apply (proj2 (Forall_app _ _ _)). split; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le_bytes_4_range|].
  apply (proj2 (Forall_app _ _ _)). split; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le_bytes_4_range.
Qed.
Lemma shb_hdr_bytes : forall TL, (0 <= TL < 2^32)%Z ->
  map b8 (shb_hdr TL) = le4 (Z_to_bv 64 168627466) ++ le4 (Z_to_bv 64 TL) ++ le4 (Z_to_bv 64 439041101).
Proof.
  intros TL HT. unfold shb_hdr. rewrite !map_app.
  rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le4_le_bytes 168627466), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le4_le_bytes TL), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.le4_le_bytes 439041101) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition apartk (A n X xs : Z) : Prop :=
  exists k, (0 <= k <= 1 /\ A + n <= X + k * 18446744073709551616 /\ X + xs <= A + (1 - k) * 18446744073709551616)%Z.

Section CANSEC0. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcBlocks.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).

  (* [comment removed for export] *)
  Definition ngc_blocks_ok__stmt : Prop := forall ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m
      RNGx sx mm (qs qb : hptr) P B BS0,
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [(qs, P, 680%Z); (qb, B, BS0)] mm ->
    (1 <= BS0)%Z ->
    exists bP kPF bU kUF kPU,
      ngblk_ok RNGx SPA P Fb bP kPF
      /\ (rng RNGx B BS0 /\ rng RNGx (shad B) (nshad BS0) /\ (B mod 16 = 0)%Z /\ (0 <= bU <= 1)%Z /\ (B + BS0 <= 2147446784 + bU * 140737479966720)%Z
          /\ (17594333495296 * bU <= B)%Z /\ (6307840 <= B)%Z /\ (B + BS0 <= SPA)%Z
          /\ (0 <= kUF <= 1)%Z /\ (B + BS0 <= Fb + kUF * 18446744073709551616)%Z /\ (Fb + 64 <= B + (1 - kUF) * 18446744073709551616)%Z
          /\ (0 <= kPU <= 1)%Z /\ (P + 680 <= B + kPU * 18446744073709551616)%Z /\ (B + BS0 <= P + (1 - kPU) * 18446744073709551616)%Z)
      /\ unpoisoned mm P (P + 680) /\ unpoisoned mm B (B + BS0)
      /\ (P + 680 <= ATOP /\ B + BS0 <= ATOP)%Z
      /\ apartk MG 4 P 680 /\ apartk ERR 4 P 680 /\ apartk EB 256 P 680 /\ apartk MG 4 B BS0 /\ apartk ERR 4 B BS0 /\ apartk EB 256 B BS0.
  Section Sz4.
  Variables ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx mm qs qb P B BS0 : ltac2:(SecDiet.SzSec.tyM 'ngc_blocks_ok__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_blocks_ok__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_blocks_ok__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL.
 intros CTX INV HBS.
    ngc_setup GL CTX INV.
    assert (HinP : In (qs, P, 680%Z) [(qs, P, 680%Z); (qb, B, BS0)]) by (left; reflexivity).
    assert (HinB : In (qb, B, BS0) [(qs, P, 680%Z); (qb, B, BS0)]) by (right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ((PBAND & _ & PTOP & P16) & P0 & PUNP & PRNG & PSRNG & _).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinB)) as ((BBAND & _ & BTOP & B16) & B0 & BUNP & BRNG & BSRNG & _).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0, PUNP, PRNG, PSRNG, BBAND, BTOP, B16, B0, BUNP, BRNG, BSRNG.
    band_ind PBAND bP. band_ind BBAND bU.
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ (qs, P, 680%Z) (NGFR Fb) G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP) ltac:(left; reflexivity) ltac:(cbn; lia)) as (kPF & kPFr & kPF1 & kPF2).
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ (qb, B, BS0) (NGFR Fb) G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinB) ltac:(left; reflexivity) ltac:(cbn; lia)) as (kUF & kUFr & kUF1 & kUF2).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2, kUF1, kUF2.
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _). apply blocks_apart_app_inv in BA as (_ & BA & _).
    cbn [blocks_apart] in BA. destruct BA as (F1 & _). pose proof (Forall_inv F1) as APB. unfold apart, cb_addr, cb_size in APB. cbn [fst snd] in APB.
    assert (KPU : exists kPU, (0 <= kPU <= 1 /\ P + 680 <= B + kPU * 18446744073709551616 /\ B + BS0 <= P + (1 - kPU) * 18446744073709551616)%Z)
      by (destruct APB as [X|X]; [exists 0%Z| exists 1%Z]; lia).
    destruct KPU as (kPU & kPUr & kPU1 & kPU2).
    atop_facts.
    exists bP, kPF, bU, kUF, kPU.
    split. { unfold ngblk_ok. split; [exact PRNG|]. split; [exact PSRNG|]. split; [eapply rng_sub'; [exact RSPA| lia]|]. split; [exact FRNG|].
             split; [exact P16|]. repeat (split; [lia|]). lia. }
    split. { split; [exact BRNG|]. split; [exact BSRNG|]. split; [exact B16|]. repeat (split; [lia|]). lia. }
    split; [exact PUNP|]. split; [exact BUNP|]. split; [lia|].
    unfold apartk.
    split; [exact (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia))|].
    split; [exact (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia))|].
    split; [exact (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia))|].
    split; [exact (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn; lia))|].
    split; [exact (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn; lia))|].
    exact (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinB ltac:(lia) ltac:(cbn; lia)).
  Qed.
  End Sz4.
  Lemma ngc_blocks_ok : ltac:(let t := eval cbv delta [ngc_blocks_ok__stmt] in ngc_blocks_ok__stmt in exact t).
  Proof using GL. intros ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx mm qs qb P B BS0. ltac2:(SecDiet.SzSec.closeP 'ngc_blocks_ok__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End NgcBlocks.
End CANSEC0.

(* [comment removed for export] *)
Ltac fill_setup GL CTX INV :=
  ngc_setup GL CTX INV;
  match goal with TPx : tparams |- _ =>
    edestruct (ngc_blocks_ok _ _ TPx _ GL) as (bP & kPF & bU & kUF & kPU & PBK & BBK & PUNP & BUNP & (PTOP & BTOP) & (kMP & kMPr & kMP1 & kMP2) & (kEP & kEPr & kEP1 & kEP2) & (kBP & kBPr & kBP1 & kBP2)
                              & (kMU & kMUr & kMU1 & kMU2) & (kEU & kEUr & kEU1 & kEU2) & (kBU & kBUr & kBU1 & kBU2)); [exact CTX| exact INV| lia|] end;
  lazymatch goal with PBKh : ngblk_ok _ _ _ _ _ _ |- _ =>
    pose proof PBKh as (PRNG & PRSH & RSPk & RFR & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & _ & SPAHI & SPALO & kPFr & kPF1 & kPF2) end;
  lazymatch goal with BBKh : rng _ _ _ /\ rng _ (shad _) _ /\ _ |- _ =>
    pose proof BBKh as (BRNG & BRSH & B16 & bUr & bUhi & bUlo & bUimg & BSP & kUFr & kUF1 & kUF2 & kPUr & kPU1 & kPU2) end.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcFillVer.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.
  Hypothesis RBLK : read_block_stmt HO FO sites GIOA TP.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).
  #[local] Notation PR := (prims HO FO sites).
  #[local] Notation B8 := (C8 (Z_to_bv 64 0)).
  #[local] Notation B4 := (C4 (Z_to_bv 64 0)).
  #[local] Notation SG0 := (mkNg 1000000 INITIAL_MAX_BLOCKSIZE 0 0 []).

  (* [comment removed for export] *)
  Definition ngc_fill_ver__stmt : Prop := forall (fuel : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a2 a4 a5 a7 t3 t4 t5 t6 : word)
      (qs qb : hptr) (P B BS0 TL : Z) (sw : bool) (v0 v1 v2 v3 : Z) (rest : list Z) (jr e j : list byte) (ccs fcs : list cell) (k0 k1 k2 : word),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [(qs, P, 680%Z); (qb, B, BS0)] mm ->
    (28 <= TL <= 1048576)%Z -> (2048 <= BS0 <= 1048576)%Z -> (TL <= BS0)%Z ->
    (0 <= v0 < 256)%Z -> (0 <= v1 < 256)%Z -> (0 <= v2 < 256)%Z -> (0 <= v3 < 256)%Z ->
    rw_cells asegs mm SPA (ngc_spill P EB Fb j) -> rw_cells asegs mm (SPA + 128) ccs -> cells_size ccs = 24%nat ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    rw_cells asegs mm P (ngcells P B8 (C4 (Z_to_bv 64 BS0)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 (Z.b2z sw))) B4 B4 B4 B4 B4 B4 B8) ->
    rw_cells asegs mm (P + 648) (ng_cells (mkNg 1000000 16777216 0 0 []) 0 pad0) ->
    rw_cells asegs mm B [C4 (Z_to_bv 64 168627466); C4 (Z_to_bv 64 TL); C4 (Z_to_bv 64 439041101)] ->
    rw_cells asegs mm (B + 12) [C2 (Z_to_bv 64 (v0 + 256 * v1)); C2 (Z_to_bv 64 (v2 + 256 * v3)); CB (length rest) (map b8 rest)] ->
    rw_cells asegs mm (B + TL) [CB (Z.to_nat (BS0 - TL)) jr] ->
    (Z.of_nat (length rest) = TL - 16)%Z -> Forall (fun z => 0 <= z < 256)%Z rest ->
    implMG RNGx (if negb ((v0 + 256 * v1 =? 1) && ((v2 + 256 * v3 =? 0) || (v2 + 256 * v3 =? 2)))%Z
                 then ngc_fail MOps PR (Msg.unsupported_pcapng_version (v0 + 256 * v1) (v2 + 256 * v3))
                        (mkPcap qs f BS0 BS0 qb (shb_hdr TL ++ v0 :: v1 :: v2 :: v3 :: rest) sw 0 0 0 0 0 0 0 [] hdr0 (PrivNg SG0 None))
                 else ngc_find MOps PR fuel 0
                        (mkPcap qs f BS0 BS0 qb (shb_hdr TL ++ v0 :: v1 :: v2 :: v3 :: rest) sw (v0 + 256 * v1) (v2 + 256 * v3) 0 0 0 0 0 [] hdr0 (PrivNg SG0 None))) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (B + 14)) (Z_to_bv 64 P) a2 (Z_to_bv 64 (v0 + 256 * v1)) a4 a5 (Z_to_bv 64 0) a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 FA) (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL)
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b248) fc None mm (seg_rom asegs)).
  Section Sz5.
  Variables fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a2 a4 a5 a7 t3 t4 t5 t6 qs qb P B BS0 TL sw v0 v1 v2 v3 rest jr e j ccs fcs k0 k1 k2 : ltac2:(SecDiet.SzSec.tyM 'ngc_fill_ver__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ngc_fill_ver__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_fill_ver__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK.
 intros CTX INV TLR BSR TLB V0 V1 V2 V3 FRA FCUR Hccs FRC Hfcs HE HEB CELLS NG HBH HDV HBR LREST GRr.
    fill_setup GL CTX INV.
    set (MAJ := (v0 + 256 * v1)%Z) in *. set (MIN := (v2 + 256 * v3)%Z) in *.
    assert (MAJR : (0 <= MAJ < 65536)%Z) by (subst MAJ; lia). assert (MINR : (0 <= MIN < 65536)%Z) by (subst MIN; lia).
    destruct ((MAJ =? 1) && ((MIN =? 0) || (MIN =? 2)))%Z eqn:VOK; cbn [negb]; cbv iota.
    - (* [comment removed for export] *)
      apply andb_true_iff in VOK as [M1 MOK]. apply Z.eqb_eq in M1.
      assert (HMIN : (MIN = 0 \/ MIN = 2)%Z) by (apply orb_true_iff in MOK as [X|X]; apply Z.eqb_eq in X; [left| right]; exact X).
      rewrite M1 in *.
      ienterG.
      eapply evtF_cut.
      { eapply (fill_segD_ok gp tp t0 t1 t2 sp t3 t4 t5 t6 F fc RNGx SPA P Fb EB ERR FA bP kPF sw TL BS0 j PBK BSR B bU kUF kPU BBK) with (MIN := MIN);
          [ exact HMIN | apply INV | exact PUNP | exact BUNP | exact FRA | exact CELLS | ].
        destruct (rw_cells_cut _ _ _ 2 HDV) as [X _]. cbn [firstn] in X. exact X. }
      cbv beta. intros ms' PO. destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & m9 & -> & MU9 & WM9 & MI9 & CELLS9).
      assert (AGS : agrees_on (fun a => outside [(P, P + 648)]%Z a) mm m9) by (eapply agrees_on_of_munch; [exact MU9 | exact WM9 | intros a _ Ho; exact Ho]).
      assert (ST9 : stk asegs m9 lo SPA) by (eapply agrees_stk; [exact AGS| exact ST| intros a Ha; cbn [outside fst snd]; lia]).
      assert (INV9 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx [(qs, P, 680%Z); (qb, B, BS0)] m9).
      { eapply (ngc_inv_own FO GIOA TP fflagA GL); [exact CTX| exact INV| | exact MU9| exact WM9| exact MI9| exact ST9| ].
        - apply Forall_cons; [|apply Forall_nil]. right; left. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
        - intros a Ha. cbn [outside fst snd]. lia. }
      assert (KEEP : forall A cs, rw_cells asegs mm A cs -> (A + Z.of_nat (cells_size cs) <= P \/ P + 648 <= A)%Z -> rw_cells asegs m9 A cs).
      { intros A cs HC HA. eapply agrees_rw_cells; [exact AGS| exact HC|]. intros a Ha. cbn [outside fst snd]. lia. }
      pose proof (KEEP _ _ FRA ltac:(rewrite ngc_spill_size; lia)) as FRA9.
      pose proof (KEEP _ _ FCUR ltac:(rewrite Hccs; lia)) as FCUR9.
      pose proof (KEEP _ _ FRC ltac:(rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia)) as FRC9.
      pose proof (KEEP _ _ HE ltac:(cbn [cells_size csize Nat.add]; lia)) as HE9.
      pose proof (KEEP _ _ HEB ltac:(cbn [cells_size csize Nat.add]; lia)) as HEB9.
      pose proof (KEEP _ _ NG ltac:(unfold ng_cells; cbn [cells_size csize Nat.add]; lia)) as NG9.
      pose proof (KEEP _ _ HBH ltac:(cbn [cells_size csize Nat.add]; lia)) as HBH9.
      pose proof (KEEP _ _ HDV ltac:(cbn [cells_size csize Nat.add]; lia)) as HDV9.
      pose proof (KEEP _ _ HBR ltac:(cbn [cells_size csize Nat.add]; lia)) as HBR9.
      clear KEEP.
      (* [comment removed for export] *)
      assert (Ljr : length jr = Z.to_nat (BS0 - TL)) by (pose proof (proj1 (proj1 HBR9)) as WF; cbn in WF; lia).
      assert (BUF9 : rw_cells asegs m9 B [CB (Z.to_nat BS0) (map b8 (shb_hdr TL ++ v0 :: v1 :: v2 :: v3 :: rest) ++ jr)]).
      { replace (B + 12)%Z with (B + Z.of_nat (cells_size [C4 (Z_to_bv 64 168627466); C4 (Z_to_bv 64 TL); C4 (Z_to_bv 64 439041101)]))%Z in HDV9 by (cbn; lia).
        pose proof (rw_cells_uncut _ _ _ _ _ HBH9 HDV9 ltac:(cbn; lia)) as J1.
        replace (B + TL)%Z with (B + Z.of_nat (cells_size ([C4 (Z_to_bv 64 168627466); C4 (Z_to_bv 64 TL); C4 (Z_to_bv 64 439041101)] ++ [C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 MIN); CB (length rest) (map b8 rest)])))%Z in HBR9
          by (rewrite cells_size_app; cbn [cells_size csize Nat.add]; lia).
        pose proof (rw_cells_uncut _ _ _ _ _ J1 HBR9 ltac:(reflexivity)) as J2. cbn [app] in J2.
        eapply rw_cells_recell; [exact J2 | cbn; rewrite ?length_app, ?length_map; cbn; rewrite ?length_app, ?shb_hdr_length; cbn; repeat split; try exact Logic.I; lia |].
        cbn [cells_bytes cbytes app]. rewrite map_app, (shb_hdr_bytes TL) by lia. cbn [map app]. rewrite <- M1. subst MAJ MIN. rewrite !le2_lit by lia. rewrite !app_nil_r, <- !app_assoc. reflexivity. }
      apply evtF_done. subst POSTQ.
      eapply (ngc_loop HO FO sites GIOA TP fflagA GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK) with (qs := qs) (qb := qb) (P := P) (B := B) (ba := BS0) (sw := sw) (BS0 := BS0) (MINOR := MIN)
               (bufdata := (shb_hdr TL ++ v0 :: v1 :: v2 :: v3 :: rest)%list) (sg := SG0) (i := None) (I := 0%Z) (pad := pad0) (e := e) (j := j) (ccs := ccs) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2);
        [ exact CTX | | lia | lia ].
      split; [exact INV9|]. split; [exact FRA9|]. split; [exact FCUR9|]. split; [exact Hccs|]. split; [exact FRC9|]. split; [exact Hfcs|].
      split; [exact HE9|]. split; [exact HEB9|]. split; [exact CELLS9|]. split; [exact NG9|].
      split; [reflexivity|]. split; [reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|].
      split; [unfold ifaces_ok; cbn; repeat split; reflexivity|].
      split; [exact BUF9|].
      split; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.firstn_len_app'; rewrite length_map; reflexivity|].
      split; [rewrite length_app, shb_hdr_length; cbn [length]; lia|]. split; [lia|]. split; [lia|].
      apply Forall_app. split; [apply shb_hdr_range|]. repeat (constructor; [cbv beta; lia|]). exact GRr.
    - (* [comment removed for export] *)
      assert (HBAD : ~ (MAJ = 1 /\ (MIN = 0 \/ MIN = 2))%Z).
      { intros (E1 & E2). rewrite E1 in VOK. cbn [Z.eqb Pos.eqb andb] in VOK. destruct E2 as [E2|E2]; rewrite E2 in VOK; discriminate VOK. }
      ienterG.
      eapply evtF_cut.
      { destruct (rw_cells_cut _ _ _ 2 HDV) as [HV2 _]. cbn [firstn] in HV2.
        eapply fill_segD_bad with (MAJ := MAJ) (MIN := MIN) (bP := bP) (kPF := kPF) (bU := bU) (kUF := kUF) (kPU := kPU);
          first [ exact PBK | exact BBK | exact BSR | exact TLR | exact MAJR | exact MINR | exact HBAD | exact MI | exact PUNP | exact BUNP | exact HV2 | exact FRA ]. }
      cbv beta. intros ms' PO. destruct PO as (z5 & ->).
      assert (MSG : fmt_at mm 0x221c0 "unsupported pcapng savefile version %u.%u"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm 0x221c0 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "unsupported pcapng savefile version %u.%u"%string) ++ [Z_to_bv 8 0])
                                 MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      apply evtF_done. subst POSTQ. unfold ngc_fail.
      cbn [pc_priv ng_ifaces_ptr_of pc_buffer pc_self free_opt e_free e_fret prims mo_bind mo_ret MOps].
      pose proof CELLS as CELLSu. unfold ngcells in CELLSu.
      destruct (rw_cells_cut _ _ _ 4 CELLSu) as [_ Y1]. destruct (rw_cells_cut _ _ _ 1 Y1) as [HPB _]. cbn [firstn skipn cells_size csize Nat.add app] in HPB.
      lazymatch type of HPB with rw_cells _ _ ?A _ => replace A with (P + 24)%Z in HPB by lia end.
      eapply (ngc_snp_fail HO FO GIOA TP fflagA GL FRET FREE FREENULL SNPRINTF) with (j := j) (ccs := ccs) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2) (e := e)
               (i := None) (sg := SG0) (qs := qs) (qb := qb) (P := P) (B := B) (I := 0%Z) (nb := BS0) (RA := 0x8b598%Z) (FMTA := 0x221c0%Z)
               (fs := "unsupported pcapng savefile version %u.%u"%string) (args := [AInt MAJ; AInt MIN]);
        [ exact CTX | exact INV | reflexivity | exact FRA | exact FCUR | exact Hccs | exact FRC | exact Hfcs | exact HE | exact HEB
        | exact HPB | exact (ngcells_cut672 _ _ _ _ _ NG)
        | reflexivity | exact MSG | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
        | vm_compute; reflexivity | repeat constructor | unfold Msg.unsupported_pcapng_version, PCAP_ERRBUF_SIZE; reflexivity ].
  Qed.
  End Sz5.
  Lemma ngc_fill_ver : ltac:(let t := eval cbv delta [ngc_fill_ver__stmt] in ngc_fill_ver__stmt in exact t).
  Proof using GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK. intros fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a2 a4 a5 a7 t3 t4 t5 t6 qs qb P B BS0 TL sw v0 v1 v2 v3 rest jr e j ccs fcs k0 k1 k2. ltac2:(SecDiet.SzSec.closeP 'ngc_fill_ver__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_fill_after_rb__stmt : Prop := forall (fuel : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (qs qb : hptr) (P B BS0 TL : Z) (sw : bool) (got : list Z) (junk' jr e j : list byte) (ccs fcs : list cell) (k0 k1 k2 : word),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [(qs, P, 680%Z); (qb, B, BS0)] mm ->
    (28 <= TL <= 1048576)%Z -> (2048 <= BS0 <= 1048576)%Z -> (TL <= BS0)%Z ->
    rw_cells asegs mm SPA (ngc_spill P EB Fb j) -> rw_cells asegs mm (SPA + 128) ccs -> cells_size ccs = 24%nat ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    rw_cells asegs mm P (ngcells P B8 (C4 (Z_to_bv 64 BS0)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 (Z.b2z sw))) B4 B4 B4 B4 B4 B4 B8) ->
    rw_cells asegs mm (P + 648) (ng_cells (mkNg 1000000 16777216 0 0 []) 0 pad0) ->
    rw_cells asegs mm B [C4 (Z_to_bv 64 168627466); C4 (Z_to_bv 64 TL); C4 (Z_to_bv 64 439041101)] ->
    rw_cells asegs mm (B + 12) [CB (length got) (map b8 got); CB (Z.to_nat (TL - 12) - length got) junk'] ->
    rw_cells asegs mm (B + TL) [CB (Z.to_nat (BS0 - TL)) jr] ->
    (zlength got = TL - 12)%Z -> Forall (fun z => 0 <= z < 256)%Z got ->
    implMG RNGx (ngc_after_rb MOps PR fuel 0 sw (mkPcap qs f BS0 BS0 qb (shb_hdr TL) sw 0 0 0 0 0 0 0 [] hdr0 (PrivNg SG0 None)) RBS_Ok got) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 FA) (Z_to_bv 64 (B + 12)) (Z_to_bv 64 B) (Z_to_bv 64 TL)
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b1b8) fc None mm (seg_rom asegs)).
  Section Sz6.
  Variables fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 qs qb P B BS0 TL sw got junk' jr e j ccs fcs k0 k1 k2 : ltac2:(SecDiet.SzSec.tyM 'ngc_fill_after_rb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ngc_fill_after_rb__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_fill_after_rb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK.
 intros CTX INV TLR BSR TLB FRA FCUR Hccs FRC Hfcs HE HEB CELLS NG HBH HD HBR GLn GR.
    fill_setup GL CTX INV.
    unfold zlength in GLn.
    destruct got as [|g0 [|g1 [|g2 [|g3 rest]]]]; try (exfalso; cbn [length] in GLn; lia).
    pose proof (Forall_inv GR) as X0. pose proof (Forall_inv (Forall_inv_tail GR)) as X1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail GR))) as X2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail GR)))) as X3.
    cbv beta in X0, X1, X2, X3.
    assert (GRr : Forall (fun z => 0 <= z < 256)%Z rest) by (do 4 apply Forall_inv_tail in GR; exact GR).
    assert (Lrest : Z.of_nat (length rest) = (TL - 16)%Z) by (cbn [length] in GLn; lia).
    destruct (rw_cells_cut _ _ _ 1 HD) as [HDg _]. cbn [firstn skipn cells_size csize Nat.add app map] in HDg.
    pose proof (rw_cells_recell _ _ _ [C2 (Z_to_bv 64 (g0 + 256 * g1)); C2 (Z_to_bv 64 (g2 + 256 * g3)); CB (length rest) (map b8 rest)] HDg
                  ltac:(cbn; rewrite ?length_map; repeat split; first [reflexivity | lia | exact Logic.I])
                  ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit by lia; rewrite !app_nil_r; reflexivity)) as HDV. clear HDg.
    destruct (rw_cells_cut _ _ _ 2 HDV) as [HV HRST]. cbn [firstn skipn cells_size csize Nat.add app] in HV, HRST.
    lazymatch type of HRST with rw_cells _ _ ?A _ => replace A with (B + 16)%Z in HRST by lia end.
    (* [comment removed for export] *)
    unfold ngc_after_rb.
    cbn [pc_bufdata set_bufdata pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_swapped pc_snapshot pc_linktype pc_linktype_ext pc_priv pc_version_major pc_version_minor].
    assert (LH : Z.of_nat (length (shb_hdr TL)) = 12%Z) by (rewrite shb_hdr_length; reflexivity).
    ienterG.
    destruct sw; cbv iota;
      cbn [pc_bufdata set_bufdata pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_swapped pc_snapshot pc_linktype pc_linktype_ext pc_priv pc_version_major pc_version_minor].
    - (* [comment removed for export] *)
      eapply evtF_cut.
      { eapply (fill_segC_sw gp tp t0 t1 t2 sp t3 t4 t5 t6 F fc RNGx SPA P Fb EB ERR FA bP kPF true TL BS0 j PBK BSR B bU kUF kPU BBK) with (g0 := g0) (g1 := g1) (g2 := g2) (g3 := g3);
          [ reflexivity | exact MI | exact PUNP | exact BUNP | exact FRA | exact CELLS | exact HV | lia | lia | lia | lia ]. }
      cbv beta. intros ms' PO. destruct PO as (z2 & z4 & z7 & m7 & -> & MU7 & WM7 & MI7 & HV7).
      assert (AGS : agrees_on (fun a => outside [(B + 12, B + 16)]%Z a) mm m7) by (eapply agrees_on_of_munch; [exact MU7 | exact WM7 | intros a _ Ho; exact Ho]).
      assert (ST7 : stk asegs m7 lo SPA) by (eapply agrees_stk; [exact AGS| exact ST| intros a Ha; cbn [outside fst snd]; lia]).
      assert (INV7 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx [(qs, P, 680%Z); (qb, B, BS0)] m7).
      { eapply (ngc_inv_own FO GIOA TP fflagA GL); [exact CTX| exact INV| | exact MU7| exact WM7| exact MI7| exact ST7| ].
        - apply Forall_cons; [|apply Forall_nil]. right; left. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
        - intros a Ha. cbn [outside fst snd]. lia. }
      assert (KEEP : forall A cs, rw_cells asegs mm A cs -> (A + Z.of_nat (cells_size cs) <= B + 12 \/ B + 16 <= A)%Z -> rw_cells asegs m7 A cs).
      { intros A cs HC HA. eapply agrees_rw_cells; [exact AGS| exact HC|]. intros a Ha. cbn [outside fst snd]. lia. }
      pose proof (KEEP _ _ FRA ltac:(rewrite ngc_spill_size; lia)) as FRA7.
      pose proof (KEEP _ _ FCUR ltac:(rewrite Hccs; lia)) as FCUR7.
      pose proof (KEEP _ _ FRC ltac:(rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia)) as FRC7.
      pose proof (KEEP _ _ HE ltac:(cbn [cells_size csize Nat.add]; lia)) as HE7.
      pose proof (KEEP _ _ HEB ltac:(cbn [cells_size csize Nat.add]; lia)) as HEB7.
      pose proof (KEEP _ _ CELLS ltac:(rewrite ngcells_size by reflexivity; lia)) as CELLS7.
      pose proof (KEEP _ _ NG ltac:(unfold ng_cells; cbn [cells_size csize Nat.add]; lia)) as NG7.
      pose proof (KEEP _ _ HBH ltac:(cbn [cells_size csize Nat.add]; lia)) as HBH7.
      pose proof (KEEP _ _ HRST ltac:(cbn [cells_size csize Nat.add]; lia)) as HRST7.
      pose proof (KEEP _ _ HBR ltac:(cbn [cells_size csize Nat.add]; lia)) as HBR7.
      clear KEEP.
      assert (HDV7 : rw_cells asegs m7 (B + 12) [C2 (Z_to_bv 64 (g1 + 256 * g0)); C2 (Z_to_bv 64 (g3 + 256 * g2)); CB (length rest) (map b8 rest)]).
      { replace (B + 16)%Z with (B + 12 + Z.of_nat (cells_size [C2 (Z_to_bv 64 (g1 + 256 * g0)); C2 (Z_to_bv 64 (g3 + 256 * g2))]))%Z in HRST7 by (cbn; lia).
        exact (rw_cells_uncut _ _ _ _ _ HV7 HRST7 ltac:(reflexivity)). }
      assert (SW12 : swap_field 2 14 (swap_field 2 12 (shb_hdr TL ++ g0 :: g1 :: g2 :: g3 :: rest)) = shb_hdr TL ++ g1 :: g0 :: g3 :: g2 :: rest).
      { replace 12%Z with (Z.of_nat (length (shb_hdr TL))) by lia. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.swap2_at.
        replace 14%Z with (Z.of_nat (length (shb_hdr TL)) + 2)%Z by lia. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.swap2_at2. reflexivity. }
      rewrite !SW12.
      replace (get_le16 (shb_hdr TL ++ g1 :: g0 :: g3 :: g2 :: rest) 12) with (g1 + 256 * g0)%Z
        by (replace 12%Z with (Z.of_nat (length (shb_hdr TL))) by lia; symmetry; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.get_le16_at).
      replace (get_le16 (shb_hdr TL ++ g1 :: g0 :: g3 :: g2 :: rest) 14) with (g3 + 256 * g2)%Z
        by (replace 14%Z with (Z.of_nat (length (shb_hdr TL)) + 2)%Z by lia; symmetry; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.get_le16_at2).
      apply evtF_done. subst POSTQ.
      eapply (ngc_fill_ver fuel) with (qs := qs) (qb := qb) (P := P) (B := B) (BS0 := BS0) (TL := TL) (sw := true) (v0 := g1) (v1 := g0) (v2 := g3) (v3 := g2) (rest := rest)
               (jr := jr) (e := e) (j := j) (ccs := ccs) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2);
        [ exact CTX | exact INV7 | exact TLR | exact BSR | exact TLB | lia | lia | lia | lia | exact FRA7 | exact FCUR7 | exact Hccs | exact FRC7 | exact Hfcs | exact HE7 | exact HEB7
        | exact CELLS7 | exact NG7 | exact HBH7 | exact HDV7 | exact HBR7 | exact Lrest | exact GRr ].
    - (* [comment removed for export] *)
      eapply evtF_cut.
      { eapply (fill_segC_nat gp tp t0 t1 t2 sp t3 t4 t5 t6 F fc RNGx SPA P Fb EB ERR FA bP kPF false TL BS0 j PBK BSR B bU kUF kPU BBK) with (g0 := g0) (g1 := g1) (g2 := g2) (g3 := g3);
          [ reflexivity | exact MI | exact PUNP | exact BUNP | exact FRA | exact CELLS | exact HV | lia | lia | lia | lia ]. }
      cbv beta. intros ms' PO. destruct PO as (z2 & z4 & z7 & ->).
      replace (get_le16 (shb_hdr TL ++ g0 :: g1 :: g2 :: g3 :: rest) 12) with (g0 + 256 * g1)%Z
        by (replace 12%Z with (Z.of_nat (length (shb_hdr TL))) by lia; symmetry; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.get_le16_at).
      replace (get_le16 (shb_hdr TL ++ g0 :: g1 :: g2 :: g3 :: rest) 14) with (g2 + 256 * g3)%Z
        by (replace 14%Z with (Z.of_nat (length (shb_hdr TL)) + 2)%Z by lia; symmetry; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.get_le16_at2).
      apply evtF_done. subst POSTQ.
      eapply (ngc_fill_ver fuel) with (qs := qs) (qb := qb) (P := P) (B := B) (BS0 := BS0) (TL := TL) (sw := false) (v0 := g0) (v1 := g1) (v2 := g2) (v3 := g3) (rest := rest)
               (jr := jr) (e := e) (j := j) (ccs := ccs) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2);
        [ exact CTX | exact INV | exact TLR | exact BSR | exact TLB | lia | lia | lia | lia | exact FRA | exact FCUR | exact Hccs | exact FRC | exact Hfcs | exact HE | exact HEB
        | exact CELLS | exact NG | exact HBH | exact HDV | exact HBR | exact Lrest | exact GRr ].
  Qed.
  End Sz6.
  Lemma ngc_fill_after_rb : ltac:(let t := eval cbv delta [ngc_fill_after_rb__stmt] in ngc_fill_after_rb__stmt in exact t).
  Proof using GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK. intros fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 qs qb P B BS0 TL sw got junk' jr e j ccs fcs k0 k1 k2. ltac2:(SecDiet.SzSec.closeP 'ngc_fill_after_rb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcFillVer.
End CANSEC1.
End TwB.
End F_ngchk_fverA.

(* [comment removed for export] *)
Module F_ngchk_frbA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfHandleA F_ngchk_modelA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_fail3A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_msgA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_loopA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_fsegA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_fverA.
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
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcFillRb.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.
  Hypothesis RBLK : read_block_stmt HO FO sites GIOA TP.
  Hypothesis RBYTES : read_bytes_stmt HO FO sites GIOA TP.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).
  #[local] Notation PR := (prims HO FO sites).
  #[local] Notation B8 := (C8 (Z_to_bv 64 0)).
  #[local] Notation B4 := (C4 (Z_to_bv 64 0)).
  #[local] Notation SG0 := (mkNg 1000000 INITIAL_MAX_BLOCKSIZE 0 0 []).

  Definition ngc_fill_rb__stmt : Prop := forall (fuel : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (qs qb : hptr) (P B BS0 TL : Z) (sw : bool) (j0 j1 j2 j5 j9 j bjunk e fpre fmid fpost : list byte) (ccs : list cell) (k0 k1 k2 tlw : word),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [(qs, P, 680%Z); (qb, B, BS0)] mm ->
    (28 <= TL <= 1048576)%Z -> (2048 <= BS0 <= 1048576)%Z -> (TL <= BS0)%Z ->
    rw_cells asegs mm SPA [CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 (Z.shiftr (P + 156) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 156)); CB 8 j5;
                           C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 (P + 648)); CB 8 j9;
                           C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb)] ->
    rw_cells asegs mm (SPA + 128) ccs -> cells_size ccs = 24%nat ->
    rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; C4 tlw; CB 12 fmid; C4 (Z_to_bv 64 439041101); CB 4 fpost; C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))] ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    rw_cells asegs mm P (ngcells P B8 (C4 (Z_to_bv 64 BS0)) B8 (C4 (Z_to_bv 64 (Z.b2z sw))) B4 B4 B4 B4 B4 B4 B8) ->
    rw_cells asegs mm (P + 648) (ng_cells (mkNg 1000000 0 0 0 []) 0 pad0) ->
    rw_cells asegs mm B [CB (Z.to_nat BS0) bjunk] ->
    implMG RNGx (mbind (read_bytes MOps PR f (DHeap qb 12) (TL - 12) true)
                   (fun x : rb_status * list Z => let '(st, data) := x in
                      ngc_after_rb MOps PR fuel 0 sw (mkPcap qs f BS0 BS0 qb (shb_hdr TL) sw 0 0 0 0 0 0 0 [] hdr0 (PrivNg SG0 None)) st data)) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR (Z_to_bv 64 0x8b14c) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 B) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 (Fb + 48)) (Z_to_bv 64 FA) (Z_to_bv 64 P) (Z_to_bv 64 TL)
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b14c) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 qs qb P B BS0 TL sw j0 j1 j2 j5 j9 j bjunk e fpre fmid fpost ccs k0 k1 k2 tlw : ltac2:(SecDiet.SzSec.tyM 'ngc_fill_rb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ngc_fill_rb__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_fill_rb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL HAL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK RBYTES.
 intros CTX INV TLR BSR TLB FRA FCUR Hccs FRC HE HEB CELLS NG HBUF.
    fill_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof TR as (_ & _ & _ & _ & TRRB & _).
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB asegs _ _ [] _ _ [] [4%nat; 4%nat; 4%nat; Z.to_nat (TL - 12); Z.to_nat (BS0 - TL)] HBUF ltac:(cbn; lia)) as HB'. cbn [mk_CB_cells app] in HB'.
    destruct (rw_cells_cut _ _ _ 3 HB') as [HBH X]. destruct (rw_cells_cut _ _ _ 1 X) as [HBD HBR]. clear HB' X.
    cbn [firstn skipn cells_size csize Nat.add app] in HBH, HBD, HBR.
    lazymatch type of HBD with rw_cells _ _ ?A _ => replace A with (B + 12)%Z in HBD by lia end.
    lazymatch type of HBR with rw_cells _ _ ?A _ => replace A with (B + TL)%Z in HBR by lia end.
    ienterG.
    eapply evtF_cut.
    { eapply (fill_segB gp tp t0 t1 t2 sp t3 t4 t5 t6 F fc RNGx SPA P Fb EB ERR FA bP kPF sw TL BS0 j PBK BSR B bU kUF kPU BBK);
        [ exact MI | exact PUNP | exact BUNP | exact FRA | exact FRC | exact CELLS | exact NG | exact HBH ]. }
    cbv beta. intros ms' PO. destruct PO as (z5 & z6 & z7 & m4 & -> & MU4 & WM4 & MI4 & PUNP4 & BUNP4 & FRA4 & CELLS4 & NG4 & HBH4).
    assert (AGS : agrees_on (fun a => outside [(SPA, SPA + 128); (P, P + 680); (B, B + 12)]%Z a) mm m4) by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    assert (ST4 : stk asegs m4 lo SPA) by (eapply agrees_stk; [exact AGS| exact ST| intros a Ha; cbn [outside fst snd]; lia]).
    assert (INV4 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx [(qs, P, 680%Z); (qb, B, BS0)] m4).
    { eapply (ngc_inv_own FO GIOA TP fflagA GL); [exact CTX| exact INV| | exact MU4| exact WM4| exact MI4| exact ST4| ].
      - apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [right; left; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia|].
        apply Forall_cons; [|apply Forall_nil]. right; left. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
      - intros a Ha. cbn [outside fst snd]. lia. }
    assert (KEEP : forall A cs, rw_cells asegs mm A cs ->
              ((A + Z.of_nat (cells_size cs) <= P \/ P + 680 <= A) /\ (A + Z.of_nat (cells_size cs) <= B \/ B + 12 <= A) /\ (A + Z.of_nat (cells_size cs) <= SPA \/ SPA + 128 <= A))%Z -> rw_cells asegs m4 A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AGS| exact HC|]. intros a Ha. cbn [outside fst snd]. lia. }
    pose proof (KEEP _ _ FCUR ltac:(rewrite Hccs; lia)) as FCUR4.
    pose proof (KEEP _ _ FRC ltac:(cbn [cells_size csize Nat.add]; lia)) as FRC4.
    pose proof (KEEP _ _ HE ltac:(cbn [cells_size csize Nat.add]; lia)) as HE4.
    pose proof (KEEP _ _ HEB ltac:(cbn [cells_size csize Nat.add]; lia)) as HEB4.
    pose proof (KEEP _ _ HBD ltac:(cbn [cells_size csize Nat.add]; lia)) as HBD4.
    pose proof (KEEP _ _ HBR ltac:(cbn [cells_size csize Nat.add]; lia)) as HBR4.
    clear KEEP.
    pose proof INV4 as (_ & G4 & _ & _ & _ & _ & FR4 & _).
    assert (UCm : ucallerA (depth_check_header true) L m4 sp s0 ra trC) by (eapply (ngc_uc_now FO GIOA TP fflagA GL); [exact CTX| exact INV4]).
    edestruct (ngc_cobj_now FO GIOA TP fflagA GL) as (_ & _ & OEB'); [exact CTX| exact INV4|].
    assert (HinB : In (qb, B, BS0) ((CL ++ [(qs, P, 680%Z); (qb, B, BS0)]) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
    (* [comment removed for export] *)
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply RBYTES with (L := L) (s := sx) (CL := (CL ++ [(qs, P, 680%Z); (qb, B, BS0)])%list) (FB := FB) (FL := NGFR Fb :: FL) (trC := (bv_unsigned ra :: trC)%list)
                         (f := f) (Af := FA) (D := (B + 12)%Z) (n := (TL - 12)%Z) (EB := EB) (lo := lo) (foe := true) (dest := DHeap qb 12) (ej := e).
      - eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G4| exact ST4| exact MI4| unfold READ_BYTES_STACK, PCAP_L1_STACK, PCAP_L2_STACK; lia].
      - eapply (ngc_ucaller 1%nat) with (X := 0x8b210%Z); [exact UCm| exact SPAB| lia| exact SPT| exact ALN| exact FR4| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_ng_check_header; lia].
      - rewrite unsigned_lit by lia. exact TRRB.
      - apply nofr_cons; [eapply nofr_sub; [exact NF|]|].
        + intros ff Hf. unfold frames_read_bytes in Hf. unfold frames_check_header, frames_pcap_ng_check_header. destruct Hf as [<-|[]]. right; left; reflexivity.
        + unfold fb_fn, frames_read_bytes. cbn [fst]. intros [E|[]]; discriminate E.
      - exact HinF.
      - pose proof (HAL _ _ _ _ _ _ _ (qb, B, BS0) G4 HinB) as EA. unfold cb_tok, cb_addr in EA. cbn [fst snd] in EA. unfold eval_rdest. rewrite EA. reflexivity.
      - reflexivity.
      - reflexivity.
      - f_equal; lia.
      - reflexivity.
      - reflexivity.
      - lia.
      - exact HBD4.
      - split; [left; exists (qb, B, BS0); split; [apply in_or_app; right; right; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]|].
        eapply blockA_aobj; [eapply (gl_block _ _ _ GL); [exact G4| exact HinB]| cbn [cb_addr cb_size fst snd]; lia| cbn [cb_addr cb_size fst snd]; lia| lia].
      - exact HEB4.
      - split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB') ICL IFL)| exact (proj2 OEB')].
      - lia.
      - exact EB8. }
    intros [st got] sy RNGy msy PO. cbv beta in PO.
    destruct PO as (FPy & a0v & my & junk' & E & OFy & MIy & STy & AGy & Gy & HDy & GRy & GLy & RM).
    rewrite ESPA in *. post_regs E.
    assert (HinP' : In (qs, P, 680%Z) [(qs, P, 680%Z); (qb, B, BS0)]) by (left; reflexivity).
    assert (HinB' : In (qb, B, BS0) [(qs, P, 680%Z); (qb, B, BS0)]) by (right; left; reflexivity).
    assert (INVy : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGy sy [(qs, P, 680%Z); (qb, B, BS0)] my).
    { eapply (ngc_inv_keep2 FO GIOA TP fflagA GL) with (CLk := (CL ++ [(qs, P, 680%Z); (qb, B, BS0)])%list)
          (Pn := fun a => (~ (B + 12 <= a < B + 12 + (TL - 12)) /\ ~ (EB <= a < EB + 256))%Z);
        [exact CTX| exact INV4| exact FPy| exact Gy| exact OFy| exact MIy| exact STy| exact AGy| apply incl_appl, incl_refl| ].
      intros a N1 N2 NPBa NSP. pose proof (NPBa _ HinB') as X2. cbn [cb_addr cb_size fst snd] in X2. lia. }
    assert (KEEP : forall A cs, rw_cells asegs m4 A cs ->
                     ((SPA <= A /\ A + Z.of_nat (cells_size cs) <= SPA + 152) \/ (Fb <= A /\ A + Z.of_nat (cells_size cs) <= Fb + 64)
                      \/ (ERR = A /\ cells_size cs = 4%nat) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 680)
                      \/ (B <= A /\ A + Z.of_nat (cells_size cs) <= B + 12) \/ (B + TL <= A /\ A + Z.of_nat (cells_size cs) <= B + BS0))%Z -> rw_cells asegs my A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AGy| exact HC|]. intros a Ha.
      destruct HA as [HA|[HA|[HA|[HA|[HA|HA]]]]].
      - split; [left; lia| lia].
      - split; [right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia| lia].
      - destruct HA as (<- & HS). rewrite HS in Ha. split; [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_appl _ (incl_refl _)) IFL)| lia]| lia].
      - split; [right; left; apply in_block_In; exists (qs, P, 680%Z); split; [apply in_or_app; right; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]| lia].
      - split; [right; left; apply in_block_In; exists (qb, B, BS0); split; [apply in_or_app; right; right; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]| lia].
      - split; [right; left; apply in_block_In; exists (qb, B, BS0); split; [apply in_or_app; right; right; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]| lia]. }
    pose proof (KEEP _ _ FRA4 ltac:(left; rewrite ngc_spill_size; lia)) as FRAy.
    pose proof (KEEP _ _ FCUR4 ltac:(left; rewrite Hccs; lia)) as FCURy.
    pose proof (KEEP _ _ FRC4 ltac:(right; left; cbn [cells_size csize Nat.add]; lia)) as FRCy.
    pose proof (KEEP _ _ HE4 ltac:(right; right; left; split; reflexivity)) as HEy.
    pose proof (KEEP _ _ CELLS4 ltac:(right; right; right; left; rewrite ngcells_size by reflexivity; lia)) as CELLSy.
    pose proof (KEEP _ _ NG4 ltac:(right; right; right; left; unfold ng_cells; cbn [cells_size csize Nat.add]; lia)) as NGy.
    pose proof (KEEP _ _ HBH4 ltac:(right; right; right; right; left; cbn [cells_size csize Nat.add]; lia)) as HBHy.
    pose proof (KEEP _ _ HBR4 ltac:(right; right; right; right; right; cbn [cells_size csize Nat.add]; lia)) as HBRy.
    clear KEEP.
    pose proof (munch_refl ([] : list (Z * Z)) my) as MU. pose proof (wmono_refl asegs my) as WM.
    destruct st as [ | | msg].
    - (* [comment removed for export] *)
      destruct RM as (-> & GLn & HEBy).
      ienterG. zstep. zstep. if_false.
      apply evtF_done. subst POSTQ.
      eapply (ngc_fill_after_rb HO FO sites GIOA TP fflagA GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK fuel) with (qs := qs) (qb := qb) (P := P) (B := B) (BS0 := BS0) (TL := TL) (sw := sw)
               (got := got) (junk' := junk') (e := e) (j := j) (ccs := ccs) (fcs := [CB 8 fpre; C4 tlw; CB 12 fmid; C4 (Z_to_bv 64 439041101); CB 4 fpost]) (k0 := k0) (k1 := k1) (k2 := k2);
        [ exact CTX | exact INVy | exact TLR | exact BSR | exact TLB | exact FRAy | exact FCURy | exact Hccs | exact FRCy | reflexivity | exact HEy | exact HEBy
        | exact CELLSy | exact NGy | exact HBHy | exact HDy | exact HBRy | exact GLn | exact GRy ].
    - (* [comment removed for export] *)
      destruct RM as (_ & _ & X & _). discriminate X.
    - (* [comment removed for export] *)
      destruct RM as (junk6 & -> & HEBy & LENM & MOK).
      ienterG. zstep. zstep. if_true.
      apply evtF_done. subst POSTQ. unfold ngc_after_rb, ngc_fail.
      cbn [pc_priv ng_ifaces_ptr_of pc_buffer pc_self set_bufdata free_opt e_free e_fret prims mo_bind mo_ret MOps].
      pose proof CELLSy as CELLSu. unfold ngcells in CELLSu.
      destruct (rw_cells_cut _ _ _ 4 CELLSu) as [_ Y1]. destruct (rw_cells_cut _ _ _ 1 Y1) as [HPB _]. cbn [firstn skipn cells_size csize Nat.add app] in HPB.
      lazymatch type of HPB with rw_cells _ _ ?A _ => replace A with (P + 24)%Z in HPB by lia end.
      eapply (ngc_fail3 HO FO GIOA TP fflagA GL FRET FREE FREENULL) with (i := None) (sg := SG0) (I := 0%Z) (j := j) (ccs := ccs)
               (fcs := [CB 8 fpre; C4 tlw; CB 12 fmid; C4 (Z_to_bv 64 439041101); CB 4 fpost]) (k0 := k0) (k1 := k1) (k2 := k2);
        [ exact CTX | exact INVy | reflexivity | exact FRAy | exact FCURy | exact Hccs | exact FRCy | reflexivity | exact HEy | exact HEBy | exact LENM | exact MOK
        | exact HPB | exact (ngcells_cut672 _ _ _ _ _ NGy) ].
  Qed.
  End Sz1.
  Lemma ngc_fill_rb : ltac:(let t := eval cbv delta [ngc_fill_rb__stmt] in ngc_fill_rb__stmt in exact t).
  Proof using GL GPL HAL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK RBYTES. intros fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 qs qb P B BS0 TL sw j0 j1 j2 j5 j9 j bjunk e fpre fmid fpost ccs k0 k1 k2 tlw. ltac2:(SecDiet.SzSec.closeP 'ngc_fill_rb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcFillRb.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_fail3A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_msgA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_loopA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_fsegA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_fverA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcFillRb.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.
  Hypothesis RBLK : read_block_stmt HO FO sites GIOA TP.
  Hypothesis RBYTES : read_bytes_stmt HO FO sites GIOA TP.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).
  #[local] Notation PR := (prims HO FO sites).
  #[local] Notation B8 := (C8 (Z_to_bv 64 0)).
  #[local] Notation B4 := (C4 (Z_to_bv 64 0)).
  #[local] Notation SG0 := (mkNg 1000000 INITIAL_MAX_BLOCKSIZE 0 0 []).

  Definition ngc_fill_rb__stmt : Prop := forall (fuel : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (qs qb : hptr) (P B BS0 TL : Z) (sw : bool) (j0 j1 j2 j5 j9 j bjunk e fpre fmid fpost : list byte) (ccs : list cell) (k0 k1 k2 tlw : word),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [(qs, P, 680%Z); (qb, B, BS0)] mm ->
    (28 <= TL <= 1048576)%Z -> (2048 <= BS0 <= 1048576)%Z -> (TL <= BS0)%Z ->
    rw_cells asegs mm SPA [CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 (Z.shiftr (P + 156) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 156)); CB 8 j5;
                           C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 (P + 648)); CB 8 j9;
                           C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb)] ->
    rw_cells asegs mm (SPA + 128) ccs -> cells_size ccs = 24%nat ->
    rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; C4 tlw; CB 12 fmid; C4 (Z_to_bv 64 439041101); CB 4 fpost; C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))] ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    rw_cells asegs mm P (ngcells P B8 (C4 (Z_to_bv 64 BS0)) B8 (C4 (Z_to_bv 64 (Z.b2z sw))) B4 B4 B4 B4 B4 B4 B8) ->
    rw_cells asegs mm (P + 648) (ng_cells (mkNg 1000000 0 0 0 []) 0 pad0) ->
    rw_cells asegs mm B [CB (Z.to_nat BS0) bjunk] ->
    implMG RNGx (mbind (read_bytes MOps PR f (DHeap qb 12) (TL - 12) true)
                   (fun x : rb_status * list Z => let '(st, data) := x in
                      ngc_after_rb MOps PR fuel 0 sw (mkPcap qs f BS0 BS0 qb (shb_hdr TL) sw 0 0 0 0 0 0 0 [] hdr0 (PrivNg SG0 None)) st data)) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR (Z_to_bv 64 0x8b0c4) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 B) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 FA) (Z_to_bv 64 (Fb + 48)) (Z_to_bv 64 P) (Z_to_bv 64 TL)
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b0c4) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 qs qb P B BS0 TL sw j0 j1 j2 j5 j9 j bjunk e fpre fmid fpost ccs k0 k1 k2 tlw : ltac2:(SecDiet.SzSec.tyM 'ngc_fill_rb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ngc_fill_rb__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_fill_rb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL HAL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK RBYTES.
 intros CTX INV TLR BSR TLB FRA FCUR Hccs FRC HE HEB CELLS NG HBUF.
    fill_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof TR as (_ & _ & _ & _ & TRRB & _).
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB asegs _ _ [] _ _ [] [4%nat; 4%nat; 4%nat; Z.to_nat (TL - 12); Z.to_nat (BS0 - TL)] HBUF ltac:(cbn; lia)) as HB'. cbn [mk_CB_cells app] in HB'.
    destruct (rw_cells_cut _ _ _ 3 HB') as [HBH X]. destruct (rw_cells_cut _ _ _ 1 X) as [HBD HBR]. clear HB' X.
    cbn [firstn skipn cells_size csize Nat.add app] in HBH, HBD, HBR.
    lazymatch type of HBD with rw_cells _ _ ?A _ => replace A with (B + 12)%Z in HBD by lia end.
    lazymatch type of HBR with rw_cells _ _ ?A _ => replace A with (B + TL)%Z in HBR by lia end.
    ienterG.
    eapply evtF_cut.
    { eapply (fill_segB gp tp t0 t1 t2 sp t3 t4 t5 t6 F fc RNGx SPA P Fb EB ERR FA bP kPF sw TL BS0 j PBK BSR B bU kUF kPU BBK);
        [ exact MI | exact PUNP | exact BUNP | exact FRA | exact FRC | exact CELLS | exact NG | exact HBH ]. }
    cbv beta. intros ms' PO. destruct PO as (z5 & z6 & z7 & m4 & -> & MU4 & WM4 & MI4 & PUNP4 & BUNP4 & FRA4 & CELLS4 & NG4 & HBH4).
    assert (AGS : agrees_on (fun a => outside [(SPA, SPA + 128); (P, P + 680); (B, B + 12)]%Z a) mm m4) by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    assert (ST4 : stk asegs m4 lo SPA) by (eapply agrees_stk; [exact AGS| exact ST| intros a Ha; cbn [outside fst snd]; lia]).
    assert (INV4 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx [(qs, P, 680%Z); (qb, B, BS0)] m4).
    { eapply (ngc_inv_own FO GIOA TP fflagA GL); [exact CTX| exact INV| | exact MU4| exact WM4| exact MI4| exact ST4| ].
      - apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [right; left; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia|].
        apply Forall_cons; [|apply Forall_nil]. right; left. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
      - intros a Ha. cbn [outside fst snd]. lia. }
    assert (KEEP : forall A cs, rw_cells asegs mm A cs ->
              ((A + Z.of_nat (cells_size cs) <= P \/ P + 680 <= A) /\ (A + Z.of_nat (cells_size cs) <= B \/ B + 12 <= A) /\ (A + Z.of_nat (cells_size cs) <= SPA \/ SPA + 128 <= A))%Z -> rw_cells asegs m4 A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AGS| exact HC|]. intros a Ha. cbn [outside fst snd]. lia. }
    pose proof (KEEP _ _ FCUR ltac:(rewrite Hccs; lia)) as FCUR4.
    pose proof (KEEP _ _ FRC ltac:(cbn [cells_size csize Nat.add]; lia)) as FRC4.
    pose proof (KEEP _ _ HE ltac:(cbn [cells_size csize Nat.add]; lia)) as HE4.
    pose proof (KEEP _ _ HEB ltac:(cbn [cells_size csize Nat.add]; lia)) as HEB4.
    pose proof (KEEP _ _ HBD ltac:(cbn [cells_size csize Nat.add]; lia)) as HBD4.
    pose proof (KEEP _ _ HBR ltac:(cbn [cells_size csize Nat.add]; lia)) as HBR4.
    clear KEEP.
    pose proof INV4 as (_ & G4 & _ & _ & _ & _ & FR4 & _).
    assert (UCm : ucallerA (depth_check_header true) L m4 sp s0 ra trC) by (eapply (ngc_uc_now FO GIOA TP fflagA GL); [exact CTX| exact INV4]).
    edestruct (ngc_cobj_now FO GIOA TP fflagA GL) as (_ & _ & OEB'); [exact CTX| exact INV4|].
    assert (HinB : In (qb, B, BS0) ((CL ++ [(qs, P, 680%Z); (qb, B, BS0)]) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
    (* [comment removed for export] *)
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply RBYTES with (L := L) (s := sx) (CL := (CL ++ [(qs, P, 680%Z); (qb, B, BS0)])%list) (FB := FB) (FL := NGFR Fb :: FL) (trC := (bv_unsigned ra :: trC)%list)
                         (f := f) (Af := FA) (D := (B + 12)%Z) (n := (TL - 12)%Z) (EB := EB) (lo := lo) (foe := true) (dest := DHeap qb 12) (ej := e).
      - eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G4| exact ST4| exact MI4| unfold READ_BYTES_STACK, PCAP_L1_STACK, PCAP_L2_STACK; lia].
      - eapply (ngc_ucaller 1%nat) with (X := 0x8b1b0%Z); [exact UCm| exact SPAB| lia| exact SPT| exact ALN| exact FR4| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_ng_check_header; lia].
      - rewrite unsigned_lit by lia. exact TRRB.
      - apply nofr_cons; [eapply nofr_sub; [exact NF|]|].
        + intros ff Hf. unfold frames_read_bytes in Hf. unfold frames_check_header, frames_pcap_ng_check_header. destruct Hf as [<-|[]]. right; left; reflexivity.
        + unfold fb_fn, frames_read_bytes. cbn [fst]. intros [E|[]]; discriminate E.
      - exact HinF.
      - pose proof (HAL _ _ _ _ _ _ _ (qb, B, BS0) G4 HinB) as EA. unfold cb_tok, cb_addr in EA. cbn [fst snd] in EA. unfold eval_rdest. rewrite EA. reflexivity.
      - reflexivity.
      - reflexivity.
      - f_equal; lia.
      - reflexivity.
      - reflexivity.
      - lia.
      - exact HBD4.
      - split; [left; exists (qb, B, BS0); split; [apply in_or_app; right; right; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]|].
        eapply blockA_aobj; [eapply (gl_block _ _ _ GL); [exact G4| exact HinB]| cbn [cb_addr cb_size fst snd]; lia| cbn [cb_addr cb_size fst snd]; lia| lia].
      - exact HEB4.
      - split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB') ICL IFL)| exact (proj2 OEB')].
      - lia.
      - exact EB8. }
    intros [st got] sy RNGy msy PO. cbv beta in PO.
    destruct PO as (FPy & a0v & my & junk' & E & OFy & MIy & STy & AGy & Gy & HDy & GRy & GLy & RM).
    rewrite ESPA in *. post_regs E.
    assert (HinP' : In (qs, P, 680%Z) [(qs, P, 680%Z); (qb, B, BS0)]) by (left; reflexivity).
    assert (HinB' : In (qb, B, BS0) [(qs, P, 680%Z); (qb, B, BS0)]) by (right; left; reflexivity).
    assert (INVy : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGy sy [(qs, P, 680%Z); (qb, B, BS0)] my).
    { eapply (ngc_inv_keep2 FO GIOA TP fflagA GL) with (CLk := (CL ++ [(qs, P, 680%Z); (qb, B, BS0)])%list)
          (Pn := fun a => (~ (B + 12 <= a < B + 12 + (TL - 12)) /\ ~ (EB <= a < EB + 256))%Z);
        [exact CTX| exact INV4| exact FPy| exact Gy| exact OFy| exact MIy| exact STy| exact AGy| apply incl_appl, incl_refl| ].
      intros a N1 N2 NPBa NSP. pose proof (NPBa _ HinB') as X2. cbn [cb_addr cb_size fst snd] in X2. lia. }
    assert (KEEP : forall A cs, rw_cells asegs m4 A cs ->
                     ((SPA <= A /\ A + Z.of_nat (cells_size cs) <= SPA + 152) \/ (Fb <= A /\ A + Z.of_nat (cells_size cs) <= Fb + 64)
                      \/ (ERR = A /\ cells_size cs = 4%nat) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 680)
                      \/ (B <= A /\ A + Z.of_nat (cells_size cs) <= B + 12) \/ (B + TL <= A /\ A + Z.of_nat (cells_size cs) <= B + BS0))%Z -> rw_cells asegs my A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AGy| exact HC|]. intros a Ha.
      destruct HA as [HA|[HA|[HA|[HA|[HA|HA]]]]].
      - split; [left; lia| lia].
      - split; [right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia| lia].
      - destruct HA as (<- & HS). rewrite HS in Ha. split; [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_appl _ (incl_refl _)) IFL)| lia]| lia].
      - split; [right; left; apply in_block_In; exists (qs, P, 680%Z); split; [apply in_or_app; right; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]| lia].
      - split; [right; left; apply in_block_In; exists (qb, B, BS0); split; [apply in_or_app; right; right; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]| lia].
      - split; [right; left; apply in_block_In; exists (qb, B, BS0); split; [apply in_or_app; right; right; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]| lia]. }
    pose proof (KEEP _ _ FRA4 ltac:(left; rewrite ngc_spill_size; lia)) as FRAy.
    pose proof (KEEP _ _ FCUR4 ltac:(left; rewrite Hccs; lia)) as FCURy.
    pose proof (KEEP _ _ FRC4 ltac:(right; left; cbn [cells_size csize Nat.add]; lia)) as FRCy.
    pose proof (KEEP _ _ HE4 ltac:(right; right; left; split; reflexivity)) as HEy.
    pose proof (KEEP _ _ CELLS4 ltac:(right; right; right; left; rewrite ngcells_size by reflexivity; lia)) as CELLSy.
    pose proof (KEEP _ _ NG4 ltac:(right; right; right; left; unfold ng_cells; cbn [cells_size csize Nat.add]; lia)) as NGy.
    pose proof (KEEP _ _ HBH4 ltac:(right; right; right; right; left; cbn [cells_size csize Nat.add]; lia)) as HBHy.
    pose proof (KEEP _ _ HBR4 ltac:(right; right; right; right; right; cbn [cells_size csize Nat.add]; lia)) as HBRy.
    clear KEEP.
    pose proof (munch_refl ([] : list (Z * Z)) my) as MU. pose proof (wmono_refl asegs my) as WM.
    destruct st as [ | | msg].
    - (* [comment removed for export] *)
      destruct RM as (-> & GLn & HEBy).
      ienterG. zstep. zstep. if_false.
      apply evtF_done. subst POSTQ.
      eapply (ngc_fill_after_rb HO FO sites GIOA TP fflagA GL GPL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK fuel) with (qs := qs) (qb := qb) (P := P) (B := B) (BS0 := BS0) (TL := TL) (sw := sw)
               (got := got) (junk' := junk') (e := e) (j := j) (ccs := ccs) (fcs := [CB 8 fpre; C4 tlw; CB 12 fmid; C4 (Z_to_bv 64 439041101); CB 4 fpost]) (k0 := k0) (k1 := k1) (k2 := k2);
        [ exact CTX | exact INVy | exact TLR | exact BSR | exact TLB | exact FRAy | exact FCURy | exact Hccs | exact FRCy | reflexivity | exact HEy | exact HEBy
        | exact CELLSy | exact NGy | exact HBHy | exact HDy | exact HBRy | exact GLn | exact GRy ].
    - (* [comment removed for export] *)
      destruct RM as (_ & _ & X & _). discriminate X.
    - (* [comment removed for export] *)
      destruct RM as (junk6 & -> & HEBy & LENM & MOK).
      ienterG. zstep. zstep. if_true.
      apply evtF_done. subst POSTQ. unfold ngc_after_rb, ngc_fail.
      cbn [pc_priv ng_ifaces_ptr_of pc_buffer pc_self set_bufdata free_opt e_free e_fret prims mo_bind mo_ret MOps].
      pose proof CELLSy as CELLSu. unfold ngcells in CELLSu.
      destruct (rw_cells_cut _ _ _ 4 CELLSu) as [_ Y1]. destruct (rw_cells_cut _ _ _ 1 Y1) as [HPB _]. cbn [firstn skipn cells_size csize Nat.add app] in HPB.
      lazymatch type of HPB with rw_cells _ _ ?A _ => replace A with (P + 24)%Z in HPB by lia end.
      eapply (ngc_fail3 HO FO GIOA TP fflagA GL FRET FREE FREENULL) with (i := None) (sg := SG0) (I := 0%Z) (j := j) (ccs := ccs)
               (fcs := [CB 8 fpre; C4 tlw; CB 12 fmid; C4 (Z_to_bv 64 439041101); CB 4 fpost]) (k0 := k0) (k1 := k1) (k2 := k2);
        [ exact CTX | exact INVy | reflexivity | exact FRAy | exact FCURy | exact Hccs | exact FRCy | reflexivity | exact HEy | exact HEBy | exact LENM | exact MOK
        | exact HPB | exact (ngcells_cut672 _ _ _ _ _ NGy) ].
  Qed.
  End Sz1.
  Lemma ngc_fill_rb : ltac:(let t := eval cbv delta [ngc_fill_rb__stmt] in ngc_fill_rb__stmt in exact t).
  Proof using GL GPL HAL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK RBYTES. intros fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 qs qb P B BS0 TL sw j0 j1 j2 j5 j9 j bjunk e fpre fmid fpost ccs k0 k1 k2 tlw. ltac2:(SecDiet.SzSec.closeP 'ngc_fill_rb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcFillRb.
End CANSEC1.
End TwB.
End F_ngchk_frbA.

(* [comment removed for export] *)
Module F_ngchk_fillA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfHandleA F_ngchk_modelA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_fail3A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_msgA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_loopA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_fsegA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_fverA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_frbA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_fstmtA.
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
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcFill.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis MALLOCS : malloc_stmt_o HO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.
  Hypothesis OPENC : open_offline_common_stmt HO FO sites GIOA TP.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.
  Hypothesis RBLK : read_block_stmt HO FO sites GIOA TP.
  Hypothesis RBYTES : read_bytes_stmt HO FO sites GIOA TP.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).
  #[local] Notation PR := (prims HO FO sites).
  #[local] Notation B8 := (C8 (Z_to_bv 64 0)).
  #[local] Notation B4 := (C4 (Z_to_bv 64 0)).
  #[local] Notation SG0 := (mkNg 1000000 INITIAL_MAX_BLOCKSIZE 0 0 []).

  (* [comment removed for export] *)
  Definition ngc_block1_ok__stmt : Prop := forall ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m
      RNGx sx mm (qs : hptr) P,
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [(qs, P, 680%Z)] mm ->
    exists bP kPF, ngblk_ok RNGx SPA P Fb bP kPF /\ unpoisoned mm P (P + 680) /\ (P + 680 <= ATOP)%Z
      /\ apartk MG 4 P 680 /\ apartk ERR 4 P 680 /\ apartk EB 256 P 680.
  Section Sz1.
  Variables ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx mm qs P : ltac2:(SecDiet.SzSec.tyM 'ngc_block1_ok__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_block1_ok__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_block1_ok__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL.
 intros CTX INV.
    ngc_setup GL CTX INV.
    assert (HinP : In (qs, P, 680%Z) [(qs, P, 680%Z)]) by (left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ((PBAND & _ & PTOP & P16) & P0 & PUNP & PRNG & PSRNG & _).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0, PUNP, PRNG, PSRNG.
    band_ind PBAND bP.
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ (qs, P, 680%Z) (NGFR Fb) G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP) ltac:(left; reflexivity) ltac:(cbn; lia)) as (kPF & kPFr & kPF1 & kPF2).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2.
    atop_facts.
    exists bP, kPF.
    split. { unfold ngblk_ok. split; [exact PRNG|]. split; [exact PSRNG|]. split; [eapply rng_sub'; [exact RSPA| lia]|]. split; [exact FRNG|].
             split; [exact P16|]. repeat (split; [lia|]). lia. }
    split; [exact PUNP|]. split; [lia|].
    unfold apartk.
    split; [exact (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia))|].
    split; [exact (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia))|].
    exact (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)).
  Qed.
  End Sz1.
  Lemma ngc_block1_ok : ltac:(let t := eval cbv delta [ngc_block1_ok__stmt] in ngc_block1_ok__stmt in exact t).
  Proof using GL. intros ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx mm qs P. ltac2:(SecDiet.SzSec.closeP 'ngc_block1_ok__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_fill_alloc__stmt : Prop := forall (fuel : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (qs : hptr) (P TL : Z) (sw : bool) (j0 j e fpre fmid fpost : list byte) (ccs : list cell) (k0 k1 k2 tlw : word),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [(qs, P, 680%Z)] mm ->
    (28 <= TL <= 1048576)%Z ->
    rw_cells asegs mm SPA [CB 80 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb)] ->
    rw_cells asegs mm (SPA + 128) ccs -> cells_size ccs = 24%nat ->
    rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; C4 tlw; CB 12 fmid; C4 (Z_to_bv 64 439041101); CB 4 fpost; C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))] ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    rw_cells asegs mm P (ngcells0 P ++ ng_cells ng0 0 pad0) ->
    implMG RNGx (ngc_buf MOps PR fuel f 0 BT_SHB sw TL qs 1000000) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 (Fb + 48)) (Z_to_bv 64 FA) (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 TL)
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b058) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 qs P TL sw j0 j e fpre fmid fpost ccs k0 k1 k2 tlw : ltac2:(SecDiet.SzSec.tyM 'ngc_fill_alloc__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ngc_fill_alloc__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_fill_alloc__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL HAL FRET FREE FREENULL MALLOCS SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK RBYTES.
 intros CTX INV TLR FRA0 FCUR Hccs FRC HE HEB CELLS0.
    ngc_setup GL CTX INV.
    edestruct ngc_block1_ok as (bP & kPF & PBK & PUNP & PTOP & (kMP & kMPr & kMP1 & kMP2) & (kEP & kEPr & kEP1 & kEP2) & (kBP & kBPr & kBP1 & kBP2)); [exact CTX| exact INV|].
    pose proof PBK as (PRNG & PRSH & RSPk & RFR & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & _ & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof TR as (_ & _ & _ & TRMA & _).
    (* [comment removed for export] *)
    destruct (proj1 (rw_cells_app asegs mm _ _ _) CELLS0) as [CELLS NG]. unfold ngcells0 in NG. rewrite ngcells_size in NG by reflexivity.
    replace (P + Z.of_nat 648)%Z with (P + 648)%Z in NG by lia. fold (ngcells0 P) in CELLS.
    pose proof (rw_cells_split_CB asegs _ _ [] _ _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb)] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat FRA0 ltac:(cbn; lia)) as FRA.
    cbn [mk_CB_cells app] in FRA.
    ienterG.
    eapply evtF_cut.
    { eapply (fill_segA gp tp t0 t1 t2 sp t3 t4 t5 t6 F fc RNGx SPA P Fb EB ERR FA bP kPF sw TL j PBK TLR); [ exact MI | exact PUNP | exact FRA | exact CELLS | exact NG ]. }
    cbv beta. intros ms' PO. destruct PO as (z1 & z2 & z3 & m4 & -> & MU4 & WM4 & MI4 & PUNP4 & FRA4 & CELLS4 & NG4).
    (* [comment removed for export] *)
    unfold ngc_buf, ngc_p0. cbv zeta.
    remember (if 2048 <? TL then TL else 2048)%Z as BS0 eqn:EBS.
    assert (BSR : (2048 <= BS0 <= 1048576 /\ TL <= BS0)%Z) by (subst BS0; destruct (Z.ltb_spec 2048 TL); lia).
    clear EBS. destruct BSR as (BSR & TLB).
    assert (AGS : agrees_on (fun a => outside [(SPA, SPA + 128); (P, P + 680)]%Z a) mm m4) by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    assert (ST4 : stk asegs m4 lo SPA) by (eapply agrees_stk; [exact AGS| exact ST| intros a Ha; cbn [outside fst snd]; lia]).
    assert (INV4 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx [(qs, P, 680%Z)] m4).
    { eapply (ngc_inv_own FO GIOA TP fflagA GL); [exact CTX| exact INV| | exact MU4| exact WM4| exact MI4| exact ST4| ].
      - apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil]. right; left. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
      - intros a Ha. cbn [outside fst snd]. lia. }
    assert (KEEP : forall A cs, rw_cells asegs mm A cs ->
              ((A + Z.of_nat (cells_size cs) <= P \/ P + 680 <= A) /\ (A + Z.of_nat (cells_size cs) <= SPA \/ SPA + 128 <= A))%Z -> rw_cells asegs m4 A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AGS| exact HC|]. intros a Ha. cbn [outside fst snd]. lia. }
    pose proof (KEEP _ _ FCUR ltac:(rewrite Hccs; lia)) as FCUR4.
    pose proof (KEEP _ _ FRC ltac:(cbn [cells_size csize Nat.add]; lia)) as FRC4.
    pose proof (KEEP _ _ HE ltac:(cbn [cells_size csize Nat.add]; lia)) as HE4.
    pose proof (KEEP _ _ HEB ltac:(cbn [cells_size csize Nat.add]; lia)) as HEB4.
    clear KEEP.
    pose proof INV4 as (_ & G4 & _ & _ & _ & _ & FR4 & _).
    assert (UCm : ucallerA (depth_check_header true) L m4 sp s0 ra trC) by (eapply (ngc_uc_now FO GIOA TP fflagA GL); [exact CTX| exact INV4]).
    (* [comment removed for export] *)
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply MALLOCS with (L := L) (s := sx) (CL := (CL ++ [(qs, P, 680%Z)])%list) (FB := FB) (FL := NGFR Fb :: FL) (lo := lo) (n := BS0).
      - eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G4| exact ST4| exact MI4| unfold MALLOC_STACK, PCAP_L2_STACK; lia].
      - reflexivity.
      - lia.
      - eapply (unw_of_ucaller 2%nat);
          [ eapply (ngc_ucaller 2%nat) with (X := 0x8b14c%Z); [exact UCm| exact SPAB| lia| exact SPT| exact ALN| exact FR4| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_ng_check_header; lia]
          | unfold ACLIENT_LO, ACLIENT_HI, AMALLOC_PC; lia
          | rewrite ESPA; lia
          | rewrite unsigned_lit by lia; exact TRMA
          | exact RSTK ]. }
    intros r sy RNGy msy PO. cbv beta in PO. destruct PO as (FPy & a0v & my & E & OFy & MIy & STy & AGy & RM).
    destruct r as [qb|]; [|destruct RM]. destruct RM as (B & bjunk & -> & Gy & HBUF).
    rewrite ESPA in *. post_regs E. cbv iota.
    assert (Gy' : GIOA L RNGy sy (CL ++ [(qs, P, 680%Z); (qb, B, BS0)]) FB (NGFR Fb :: FL) my).
    { eapply GPL; [exact Gy|]. eapply Permutation.Permutation_trans; [apply Permutation.Permutation_cons_append|]. rewrite <- app_assoc. apply Permutation.Permutation_refl. }
    assert (INVy : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGy sy [(qs, P, 680%Z); (qb, B, BS0)] my).
    { eapply (ngc_inv_keep FO GIOA TP fflagA GL) with (CLk := (CL ++ [(qs, P, 680%Z)])%list) (Pn := fun _ : Z => True);
        [exact CTX| exact INV4| exact FPy| exact Gy'| exact OFy| exact MIy| exact STy| | apply incl_appl, incl_refl| exact G4| intros; exact Logic.I].
      eapply agrees_on_weaken; [exact AGy|]. intros a (K & _). exact K. }
    assert (KEEP : forall A cs, rw_cells asegs m4 A cs ->
                     ((SPA <= A) \/ (Fb <= A /\ A + Z.of_nat (cells_size cs) <= Fb + 64)
                      \/ (ERR = A /\ cells_size cs = 4%nat) \/ (EB = A /\ cells_size cs = 256%nat) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 680))%Z -> rw_cells asegs my A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AGy| exact HC|]. intros a Ha.
      destruct HA as [HA|[HA|[HA|[HA|HA]]]].
      - left; lia.
      - right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia.
      - destruct HA as (<- & HS). rewrite HS in Ha. eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_appl _ (incl_refl _)) IFL)| lia].
      - destruct HA as (<- & HS). rewrite HS in Ha. eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_appl _ (incl_refl _)) IFL)| lia].
      - right; left; apply in_block_In; exists (qs, P, 680%Z); split; [apply in_or_app; right; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]. }
    pose proof (KEEP _ _ FRA4 ltac:(left; lia)) as FRAy.
    pose proof (KEEP _ _ FCUR4 ltac:(left; lia)) as FCURy.
    pose proof (KEEP _ _ FRC4 ltac:(right; left; cbn [cells_size csize Nat.add]; lia)) as FRCy.
    pose proof (KEEP _ _ HE4 ltac:(right; right; left; split; reflexivity)) as HEy.
    pose proof (KEEP _ _ HEB4 ltac:(right; right; right; left; split; reflexivity)) as HEBy.
    pose proof (KEEP _ _ CELLS4 ltac:(right; right; right; right; rewrite ngcells_size by reflexivity; lia)) as CELLSy.
    pose proof (KEEP _ _ NG4 ltac:(right; right; right; right; unfold ng_cells; cbn [cells_size csize Nat.add]; lia)) as NGy.
    clear KEEP.
    eapply (ngc_fill_rb HO FO sites GIOA TP fflagA GL GPL HAL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK RBYTES fuel) with (qs := qs) (qb := qb) (P := P) (B := B) (BS0 := BS0) (TL := TL) (sw := sw)
             (j := j) (bjunk := bjunk) (e := e) (fpre := fpre) (fmid := fmid) (fpost := fpost) (ccs := ccs) (k0 := k0) (k1 := k1) (k2 := k2) (tlw := tlw);
      [ exact CTX | exact INVy | exact TLR | exact BSR | exact TLB | exact FRAy | exact FCURy | exact Hccs | exact FRCy | exact HEy | exact HEBy | exact CELLSy | exact NGy | exact HBUF ].
  Qed.
  End Sz2.
  Lemma ngc_fill_alloc : ltac:(let t := eval cbv delta [ngc_fill_alloc__stmt] in ngc_fill_alloc__stmt in exact t).
  Proof using GL GPL HAL FRET FREE FREENULL MALLOCS SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK RBYTES. intros fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 qs P TL sw j0 j e fpre fmid fpost ccs k0 k1 k2 tlw. ltac2:(SecDiet.SzSec.closeP 'ngc_fill_alloc__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_fill__stmt : Prop := ngc_fill_stmt HO FO sites GIOA TP fflagA.
  Section Sz3.
  Variables fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sw TL j0 j ccs fpre fmid fpost k0 k1 k2 tlw e : ltac2:(SecDiet.SzSec.tyM 'ngc_fill__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ngc_fill__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_fill__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL HAL FRET FREE FREENULL MALLOCS SNPRINTF LT2DLT ADJSNAP MAXSNAP OPENC ADDIF RBLK RBYTES.
 intros CTX INV TLR FRA0 FCUR Hccs FRC HE HEB.
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof TR as (_ & _ & TROC & _).
    assert (UCm : ucallerA (depth_check_header true) L mm sp s0 ra trC) by (eapply (ngc_uc_now FO GIOA TP fflagA GL); [exact CTX| exact INV]).
    edestruct (ngc_cobj_now FO GIOA TP fflagA GL) as (_ & _ & OEB'); [exact CTX| exact INV|].
    unfold ngc_open.
    hide FCUR. hide FRC. hide HE. hide HEB. hide FR. hide MGc. hide SHC.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    do 3 zstep. zstep.
    clear MU WM.
    unhide FCUR. unhide FRC. unhide HE. unhide HEB. unhide FR. unhide MGc. unhide SHC.
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply OPENC with (L := L) (s := sx) (CL := (CL ++ [])%list) (FB := FB) (FL := NGFR Fb :: FL) (trC := (bv_unsigned ra :: trC)%list) (lo := lo) (EB := EB) (total := PCAP_NG_SF_TOTAL) (ej := e).
      - eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G| exact ST| exact MI| unfold PCAP_L1B_STACK, PCAP_L2_STACK; lia].
      - eapply (ngc_ucaller 1%nat) with (X := 0x8b054%Z); [exact UCm| exact SPAB| lia| exact SPT| exact ALN| exact FR| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_ng_check_header; lia].
      - rewrite unsigned_lit by lia. exact TROC.
      - apply nofr_cons; [eapply nofr_sub; [exact NF|]|].
        + intros ff Hf. unfold frames_open_offline_common in Hf. unfold frames_check_header, frames_pcap_ng_check_header. destruct Hf as [<-|[]]. right; left; reflexivity.
        + unfold fb_fn, frames_open_offline_common. cbn [fst]. intros [E|[]]; discriminate E.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - right; reflexivity.
      - exact HEB.
      - split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB') ICL IFL)| exact (proj2 OEB')].
      - exact EB8. }
    intros r sy RNGy msy PO. cbv beta in PO. destruct PO as (FPy & a0v & my & E & OFy & MIy & STy & AGy & RM).
    rewrite ESPA in *. post_regs E.
    assert (KEEP : forall A cs, rw_cells asegs mm A cs ->
                     ((SPA <= A) \/ (Fb <= A /\ A + Z.of_nat (cells_size cs) <= Fb + 64) \/ (ERR = A /\ cells_size cs = 4%nat))%Z -> rw_cells asegs my A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AGy| exact HC|]. intros a Ha.
      destruct HA as [HA|[HA|HA]].
      - split; [left; lia| lia].
      - split; [right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia| lia].
      - destruct HA as (<- & HS). rewrite HS in Ha. split; [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)| lia]| lia]. }
    pose proof (KEEP _ _ FRA0 ltac:(left; lia)) as FRAy.
    pose proof (KEEP _ _ FCUR ltac:(left; lia)) as FCURy.
    pose proof (KEEP _ _ FRC ltac:(right; left; cbn [cells_size csize Nat.add]; lia)) as FRCy.
    pose proof (KEEP _ _ HE ltac:(right; right; split; reflexivity)) as HEy.
    clear KEEP.
    pose proof (munch_refl ([] : list (Z * Z)) my) as MU. pose proof (wmono_refl asegs my) as WM.
    destruct r as [msg | qs].
    - (* [comment removed for export] *)
      destruct RM as (junk2 & -> & Gy & HEBy & LENM & MOK). cbv iota. cbn [e_fret prims].
      assert (INVy : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGy sy [] my).
      { eapply (ngc_inv_keep FO GIOA TP fflagA GL) with (CLk := (CL ++ [])%list) (Pn := fun a : Z => ~ (EB <= a < EB + 256)%Z);
          [exact CTX| exact INV| exact FPy| exact Gy| exact OFy| exact MIy| exact STy| exact AGy| apply incl_appl, incl_refl| exact G| intros a N1 N2; exact N1]. }
      ienterG. zstep. if_true.
      pose proof (rw_cells_uncut _ _ _ _ _ FRAy FCURy ltac:(cbn; lia)) as SCS.
      apply evtF_done. subst POSTQ.
      eapply (ngc_failx FO GIOA TP fflagA GL FRET) with (fcs := [CB 8 fpre; C4 tlw; CB 12 fmid; C4 (Z_to_bv 64 BYTE_ORDER_MAGIC); CB 4 fpost]) (k0 := k0) (k1 := k1) (k2 := k2) (pcX := 0x8b0ac%Z);
        [ exact CTX | exact INVy | right; right; right; left; reflexivity | exact SCS | rewrite cells_size_app, Hccs; reflexivity | exact FRCy | reflexivity | exact HEy | exact HEBy | exact LENM | exact MOK ].
    - (* [comment removed for export] *)
      destruct RM as (P & -> & Gy & CELLS0 & HEBy). cbv iota.
      assert (Gy' : GIOA L RNGy sy (CL ++ [(qs, P, 680%Z)]) FB (NGFR Fb :: FL) my).
      { eapply GPL; [exact Gy|]. unfold PCAP_NG_SF_TOTAL. rewrite app_nil_r. apply Permutation.Permutation_cons_append. }
      assert (INVy : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGy sy [(qs, P, 680%Z)] my).
      { eapply (ngc_inv_keep FO GIOA TP fflagA GL) with (CLk := (CL ++ [])%list) (Pn := fun a : Z => ~ (EB <= a < EB + 256)%Z);
          [exact CTX| exact INV| exact FPy| exact Gy'| exact OFy| exact MIy| exact STy| exact AGy| apply incl_appl, incl_refl| exact G| intros a N1 N2; exact N1]. }
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ (qs, P, 680%Z) Gy' ltac:(apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as ((_ & _ & PTOP & _) & P0 & _).
      cbn [cb_addr cb_size fst snd] in PTOP, P0. atop_facts.
      apply blank_recell_ng in CELLS0.
      unfold PCAP_TSTAMP_PRECISION_MICRO. cbn [Z.eqb].
      ienterG. zstep. if_false_by (eqb_lits_false P 0 ltac:(lia) ltac:(lia) ltac:(lia)).
      apply evtF_done. subst POSTQ.
      eapply (ngc_fill_alloc fuel) with (qs := qs) (P := P) (TL := TL) (sw := sw) (j0 := j0) (j := j) (e := e) (fpre := fpre) (fmid := fmid) (fpost := fpost) (ccs := ccs) (k0 := k0) (k1 := k1) (k2 := k2) (tlw := tlw);
        [ exact CTX | exact INVy | exact TLR | exact FRAy | exact FCURy | exact Hccs | exact FRCy | exact HEy | exact HEBy | exact CELLS0 ].
  Qed.
  End Sz3.
  Theorem ngc_fill : ltac:(let t := eval cbv delta [ngc_fill__stmt] in ngc_fill__stmt in exact t).
  Proof using GL GPL HAL FRET FREE FREENULL MALLOCS SNPRINTF LT2DLT ADJSNAP MAXSNAP OPENC ADDIF RBLK RBYTES. red. intros fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sw TL j0 j ccs fpre fmid fpost k0 k1 k2 tlw e. ltac2:(SecDiet.SzSec.closeP 'ngc_fill__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcFill.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_modelA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_fail3A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_msgA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_loopA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_fsegA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_fverA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_frbA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_fstmtA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcFill.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis MALLOCS : malloc_stmt_o HO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.
  Hypothesis OPENC : open_offline_common_stmt HO FO sites GIOA TP.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.
  Hypothesis RBLK : read_block_stmt HO FO sites GIOA TP.
  Hypothesis RBYTES : read_bytes_stmt HO FO sites GIOA TP.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).
  #[local] Notation PR := (prims HO FO sites).
  #[local] Notation B8 := (C8 (Z_to_bv 64 0)).
  #[local] Notation B4 := (C4 (Z_to_bv 64 0)).
  #[local] Notation SG0 := (mkNg 1000000 INITIAL_MAX_BLOCKSIZE 0 0 []).

  (* [comment removed for export] *)
  Definition ngc_block1_ok__stmt : Prop := forall ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m
      RNGx sx mm (qs : hptr) P,
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [(qs, P, 680%Z)] mm ->
    exists bP kPF, ngblk_ok RNGx SPA P Fb bP kPF /\ unpoisoned mm P (P + 680) /\ (P + 680 <= ATOP)%Z
      /\ apartk MG 4 P 680 /\ apartk ERR 4 P 680 /\ apartk EB 256 P 680.
  Section Sz1.
  Variables ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx mm qs P : ltac2:(SecDiet.SzSec.tyM 'ngc_block1_ok__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_block1_ok__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_block1_ok__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL.
 intros CTX INV.
    ngc_setup GL CTX INV.
    assert (HinP : In (qs, P, 680%Z) [(qs, P, 680%Z)]) by (left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ((PBAND & _ & PTOP & P16) & P0 & PUNP & PRNG & PSRNG & _).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0, PUNP, PRNG, PSRNG.
    band_ind PBAND bP.
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ (qs, P, 680%Z) (NGFR Fb) G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP) ltac:(left; reflexivity) ltac:(cbn; lia)) as (kPF & kPFr & kPF1 & kPF2).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2.
    atop_facts.
    exists bP, kPF.
    split. { unfold ngblk_ok. split; [exact PRNG|]. split; [exact PSRNG|]. split; [eapply rng_sub'; [exact RSPA| lia]|]. split; [exact FRNG|].
             split; [exact P16|]. repeat (split; [lia|]). lia. }
    split; [exact PUNP|]. split; [lia|].
    unfold apartk.
    split; [exact (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia))|].
    split; [exact (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia))|].
    exact (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinP ltac:(lia) ltac:(cbn; lia)).
  Qed.
  End Sz1.
  Lemma ngc_block1_ok : ltac:(let t := eval cbv delta [ngc_block1_ok__stmt] in ngc_block1_ok__stmt in exact t).
  Proof using GL. intros ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx mm qs P. ltac2:(SecDiet.SzSec.closeP 'ngc_block1_ok__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_fill_alloc__stmt : Prop := forall (fuel : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (qs : hptr) (P TL : Z) (sw : bool) (j0 j e fpre fmid fpost : list byte) (ccs : list cell) (k0 k1 k2 tlw : word),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [(qs, P, 680%Z)] mm ->
    (28 <= TL <= 1048576)%Z ->
    rw_cells asegs mm SPA [CB 80 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb)] ->
    rw_cells asegs mm (SPA + 128) ccs -> cells_size ccs = 24%nat ->
    rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 8 fpre; C4 tlw; CB 12 fmid; C4 (Z_to_bv 64 439041101); CB 4 fpost; C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))] ->
    rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 e] ->
    rw_cells asegs mm P (ngcells0 P ++ ng_cells ng0 0 pad0) ->
    implMG RNGx (ngc_buf MOps PR fuel f 0 BT_SHB sw TL qs 1000000) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) (Z_to_bv 64 FA) (Z_to_bv 64 (Fb + 48)) (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 TL)
               (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8afb0) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 qs P TL sw j0 j e fpre fmid fpost ccs k0 k1 k2 tlw : ltac2:(SecDiet.SzSec.tyM 'ngc_fill_alloc__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ngc_fill_alloc__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_fill_alloc__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL HAL FRET FREE FREENULL MALLOCS SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK RBYTES.
 intros CTX INV TLR FRA0 FCUR Hccs FRC HE HEB CELLS0.
    ngc_setup GL CTX INV.
    edestruct ngc_block1_ok as (bP & kPF & PBK & PUNP & PTOP & (kMP & kMPr & kMP1 & kMP2) & (kEP & kEPr & kEP1 & kEP2) & (kBP & kBPr & kBP1 & kBP2)); [exact CTX| exact INV|].
    pose proof PBK as (PRNG & PRSH & RSPk & RFR & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & _ & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof TR as (_ & _ & _ & TRMA & _).
    (* [comment removed for export] *)
    destruct (proj1 (rw_cells_app asegs mm _ _ _) CELLS0) as [CELLS NG]. unfold ngcells0 in NG. rewrite ngcells_size in NG by reflexivity.
    replace (P + Z.of_nat 648)%Z with (P + 648)%Z in NG by lia. fold (ngcells0 P) in CELLS.
    pose proof (rw_cells_split_CB asegs _ _ [] _ _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb)] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat FRA0 ltac:(cbn; lia)) as FRA.
    cbn [mk_CB_cells app] in FRA.
    ienterG.
    eapply evtF_cut.
    { eapply (fill_segA gp tp t0 t1 t2 sp t3 t4 t5 t6 F fc RNGx SPA P Fb EB ERR FA bP kPF sw TL j PBK TLR); [ exact MI | exact PUNP | exact FRA | exact CELLS | exact NG ]. }
    cbv beta. intros ms' PO. destruct PO as (z1 & z2 & z3 & m4 & -> & MU4 & WM4 & MI4 & PUNP4 & FRA4 & CELLS4 & NG4).
    (* [comment removed for export] *)
    unfold ngc_buf, ngc_p0. cbv zeta.
    remember (if 2048 <? TL then TL else 2048)%Z as BS0 eqn:EBS.
    assert (BSR : (2048 <= BS0 <= 1048576 /\ TL <= BS0)%Z) by (subst BS0; destruct (Z.ltb_spec 2048 TL); lia).
    clear EBS. destruct BSR as (BSR & TLB).
    assert (AGS : agrees_on (fun a => outside [(SPA, SPA + 128); (P, P + 680)]%Z a) mm m4) by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    assert (ST4 : stk asegs m4 lo SPA) by (eapply agrees_stk; [exact AGS| exact ST| intros a Ha; cbn [outside fst snd]; lia]).
    assert (INV4 : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGx sx [(qs, P, 680%Z)] m4).
    { eapply (ngc_inv_own FO GIOA TP fflagA GL); [exact CTX| exact INV| | exact MU4| exact WM4| exact MI4| exact ST4| ].
      - apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil]. right; left. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
      - intros a Ha. cbn [outside fst snd]. lia. }
    assert (KEEP : forall A cs, rw_cells asegs mm A cs ->
              ((A + Z.of_nat (cells_size cs) <= P \/ P + 680 <= A) /\ (A + Z.of_nat (cells_size cs) <= SPA \/ SPA + 128 <= A))%Z -> rw_cells asegs m4 A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AGS| exact HC|]. intros a Ha. cbn [outside fst snd]. lia. }
    pose proof (KEEP _ _ FCUR ltac:(rewrite Hccs; lia)) as FCUR4.
    pose proof (KEEP _ _ FRC ltac:(cbn [cells_size csize Nat.add]; lia)) as FRC4.
    pose proof (KEEP _ _ HE ltac:(cbn [cells_size csize Nat.add]; lia)) as HE4.
    pose proof (KEEP _ _ HEB ltac:(cbn [cells_size csize Nat.add]; lia)) as HEB4.
    clear KEEP.
    pose proof INV4 as (_ & G4 & _ & _ & _ & _ & FR4 & _).
    assert (UCm : ucallerA (depth_check_header true) L m4 sp s0 ra trC) by (eapply (ngc_uc_now FO GIOA TP fflagA GL); [exact CTX| exact INV4]).
    (* [comment removed for export] *)
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply MALLOCS with (L := L) (s := sx) (CL := (CL ++ [(qs, P, 680%Z)])%list) (FB := FB) (FL := NGFR Fb :: FL) (lo := lo) (n := BS0).
      - eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G4| exact ST4| exact MI4| unfold MALLOC_STACK, PCAP_L2_STACK; lia].
      - reflexivity.
      - lia.
      - eapply (unw_of_ucaller 2%nat);
          [ eapply (ngc_ucaller 2%nat) with (X := 0x8b0c4%Z); [exact UCm| exact SPAB| lia| exact SPT| exact ALN| exact FR4| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_ng_check_header; lia]
          | unfold ACLIENT_LO, ACLIENT_HI, AMALLOC_PC; lia
          | rewrite ESPA; lia
          | rewrite unsigned_lit by lia; exact TRMA
          | exact RSTK ]. }
    intros r sy RNGy msy PO. cbv beta in PO. destruct PO as (FPy & a0v & my & E & OFy & MIy & STy & AGy & RM).
    destruct r as [qb|]; [|destruct RM]. destruct RM as (B & bjunk & -> & Gy & HBUF).
    rewrite ESPA in *. post_regs E. cbv iota.
    assert (Gy' : GIOA L RNGy sy (CL ++ [(qs, P, 680%Z); (qb, B, BS0)]) FB (NGFR Fb :: FL) my).
    { eapply GPL; [exact Gy|]. eapply Permutation.Permutation_trans; [apply Permutation.Permutation_cons_append|]. rewrite <- app_assoc. apply Permutation.Permutation_refl. }
    assert (INVy : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGy sy [(qs, P, 680%Z); (qb, B, BS0)] my).
    { eapply (ngc_inv_keep FO GIOA TP fflagA GL) with (CLk := (CL ++ [(qs, P, 680%Z)])%list) (Pn := fun _ : Z => True);
        [exact CTX| exact INV4| exact FPy| exact Gy'| exact OFy| exact MIy| exact STy| | apply incl_appl, incl_refl| exact G4| intros; exact Logic.I].
      eapply agrees_on_weaken; [exact AGy|]. intros a (K & _). exact K. }
    assert (KEEP : forall A cs, rw_cells asegs m4 A cs ->
                     ((SPA <= A) \/ (Fb <= A /\ A + Z.of_nat (cells_size cs) <= Fb + 64)
                      \/ (ERR = A /\ cells_size cs = 4%nat) \/ (EB = A /\ cells_size cs = 256%nat) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 680))%Z -> rw_cells asegs my A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AGy| exact HC|]. intros a Ha.
      destruct HA as [HA|[HA|[HA|[HA|HA]]]].
      - left; lia.
      - right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia.
      - destruct HA as (<- & HS). rewrite HS in Ha. eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_appl _ (incl_refl _)) IFL)| lia].
      - destruct HA as (<- & HS). rewrite HS in Ha. eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_appl _ (incl_refl _)) IFL)| lia].
      - right; left; apply in_block_In; exists (qs, P, 680%Z); split; [apply in_or_app; right; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]. }
    pose proof (KEEP _ _ FRA4 ltac:(left; lia)) as FRAy.
    pose proof (KEEP _ _ FCUR4 ltac:(left; lia)) as FCURy.
    pose proof (KEEP _ _ FRC4 ltac:(right; left; cbn [cells_size csize Nat.add]; lia)) as FRCy.
    pose proof (KEEP _ _ HE4 ltac:(right; right; left; split; reflexivity)) as HEy.
    pose proof (KEEP _ _ HEB4 ltac:(right; right; right; left; split; reflexivity)) as HEBy.
    pose proof (KEEP _ _ CELLS4 ltac:(right; right; right; right; rewrite ngcells_size by reflexivity; lia)) as CELLSy.
    pose proof (KEEP _ _ NG4 ltac:(right; right; right; right; unfold ng_cells; cbn [cells_size csize Nat.add]; lia)) as NGy.
    clear KEEP.
    eapply (ngc_fill_rb HO FO sites GIOA TP fflagA GL GPL HAL FRET FREE FREENULL SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK RBYTES fuel) with (qs := qs) (qb := qb) (P := P) (B := B) (BS0 := BS0) (TL := TL) (sw := sw)
             (j := j) (bjunk := bjunk) (e := e) (fpre := fpre) (fmid := fmid) (fpost := fpost) (ccs := ccs) (k0 := k0) (k1 := k1) (k2 := k2) (tlw := tlw);
      [ exact CTX | exact INVy | exact TLR | exact BSR | exact TLB | exact FRAy | exact FCURy | exact Hccs | exact FRCy | exact HEy | exact HEBy | exact CELLSy | exact NGy | exact HBUF ].
  Qed.
  End Sz2.
  Lemma ngc_fill_alloc : ltac:(let t := eval cbv delta [ngc_fill_alloc__stmt] in ngc_fill_alloc__stmt in exact t).
  Proof using GL GPL HAL FRET FREE FREENULL MALLOCS SNPRINTF LT2DLT ADJSNAP MAXSNAP ADDIF RBLK RBYTES. intros fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 qs P TL sw j0 j e fpre fmid fpost ccs k0 k1 k2 tlw. ltac2:(SecDiet.SzSec.closeP 'ngc_fill_alloc__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_fill__stmt : Prop := ngc_fill_stmt HO FO sites GIOA TP fflagA.
  Section Sz3.
  Variables fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sw TL j0 j ccs fpre fmid fpost k0 k1 k2 tlw e : ltac2:(SecDiet.SzSec.tyM 'ngc_fill__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ngc_fill__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_fill__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL HAL FRET FREE FREENULL MALLOCS SNPRINTF LT2DLT ADJSNAP MAXSNAP OPENC ADDIF RBLK RBYTES.
 intros CTX INV TLR FRA0 FCUR Hccs FRC HE HEB.
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof TR as (_ & _ & TROC & _).
    assert (UCm : ucallerA (depth_check_header true) L mm sp s0 ra trC) by (eapply (ngc_uc_now FO GIOA TP fflagA GL); [exact CTX| exact INV]).
    edestruct (ngc_cobj_now FO GIOA TP fflagA GL) as (_ & _ & OEB'); [exact CTX| exact INV|].
    unfold ngc_open.
    hide FCUR. hide FRC. hide HE. hide HEB. hide FR. hide MGc. hide SHC.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    do 3 zstep. zstep.
    clear MU WM.
    unhide FCUR. unhide FRC. unhide HE. unhide HEB. unhide FR. unhide MGc. unhide SHC.
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply OPENC with (L := L) (s := sx) (CL := (CL ++ [])%list) (FB := FB) (FL := NGFR Fb :: FL) (trC := (bv_unsigned ra :: trC)%list) (lo := lo) (EB := EB) (total := PCAP_NG_SF_TOTAL) (ej := e).
      - eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G| exact ST| exact MI| unfold PCAP_L1B_STACK, PCAP_L2_STACK; lia].
      - eapply (ngc_ucaller 1%nat) with (X := 0x8afac%Z); [exact UCm| exact SPAB| lia| exact SPT| exact ALN| exact FR| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_ng_check_header; lia].
      - rewrite unsigned_lit by lia. exact TROC.
      - apply nofr_cons; [eapply nofr_sub; [exact NF|]|].
        + intros ff Hf. unfold frames_open_offline_common in Hf. unfold frames_check_header, frames_pcap_ng_check_header. destruct Hf as [<-|[]]. right; left; reflexivity.
        + unfold fb_fn, frames_open_offline_common. cbn [fst]. intros [E|[]]; discriminate E.
      - rewrite ESPA; lia.               (* [comment removed for export] *)
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - right; reflexivity.
      - exact HEB.
      - split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEB') ICL IFL)| exact (proj2 OEB')].
      - exact EB8. }
    intros r sy RNGy msy PO. cbv beta in PO. destruct PO as (FPy & a0v & my & E & OFy & MIy & STy & AGy & RM).
    rewrite ESPA in *. post_regs E.
    assert (KEEP : forall A cs, rw_cells asegs mm A cs ->
                     ((SPA <= A) \/ (Fb <= A /\ A + Z.of_nat (cells_size cs) <= Fb + 64) \/ (ERR = A /\ cells_size cs = 4%nat))%Z -> rw_cells asegs my A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AGy| exact HC|]. intros a Ha.
      destruct HA as [HA|[HA|HA]].
      - split; [left; lia| lia].
      - split; [right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia| lia].
      - destruct HA as (<- & HS). rewrite HS in Ha. split; [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)| lia]| lia]. }
    pose proof (KEEP _ _ FRA0 ltac:(left; lia)) as FRAy.
    pose proof (KEEP _ _ FCUR ltac:(left; lia)) as FCURy.
    pose proof (KEEP _ _ FRC ltac:(right; left; cbn [cells_size csize Nat.add]; lia)) as FRCy.
    pose proof (KEEP _ _ HE ltac:(right; right; split; reflexivity)) as HEy.
    clear KEEP.
    pose proof (munch_refl ([] : list (Z * Z)) my) as MU. pose proof (wmono_refl asegs my) as WM.
    destruct r as [msg | qs].
    - (* [comment removed for export] *)
      destruct RM as (junk2 & -> & Gy & HEBy & LENM & MOK). cbv iota. cbn [e_fret prims].
      assert (INVy : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGy sy [] my).
      { eapply (ngc_inv_keep FO GIOA TP fflagA GL) with (CLk := (CL ++ [])%list) (Pn := fun a : Z => ~ (EB <= a < EB + 256)%Z);
          [exact CTX| exact INV| exact FPy| exact Gy| exact OFy| exact MIy| exact STy| exact AGy| apply incl_appl, incl_refl| exact G| intros a N1 N2; exact N1]. }
      ienterG. zstep. if_true.
      pose proof (rw_cells_uncut _ _ _ _ _ FRAy FCURy ltac:(cbn; lia)) as SCS.
      apply evtF_done. subst POSTQ.
      eapply (ngc_failx FO GIOA TP fflagA GL FRET) with (fcs := [CB 8 fpre; C4 tlw; CB 12 fmid; C4 (Z_to_bv 64 BYTE_ORDER_MAGIC); CB 4 fpost]) (k0 := k0) (k1 := k1) (k2 := k2) (pcX := 0x8b020%Z);
        [ exact CTX | exact INVy | right; right; right; left; reflexivity | exact SCS | rewrite cells_size_app, Hccs; reflexivity | exact FRCy | reflexivity | exact HEy | exact HEBy | exact LENM | exact MOK ].
    - (* [comment removed for export] *)
      destruct RM as (P & -> & Gy & CELLS0 & HEBy). cbv iota.
      assert (Gy' : GIOA L RNGy sy (CL ++ [(qs, P, 680%Z)]) FB (NGFR Fb :: FL) my).
      { eapply GPL; [exact Gy|]. unfold PCAP_NG_SF_TOTAL. rewrite app_nil_r. apply Permutation.Permutation_cons_append. }
      assert (INVy : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGy sy [(qs, P, 680%Z)] my).
      { eapply (ngc_inv_keep FO GIOA TP fflagA GL) with (CLk := (CL ++ [])%list) (Pn := fun a : Z => ~ (EB <= a < EB + 256)%Z);
          [exact CTX| exact INV| exact FPy| exact Gy'| exact OFy| exact MIy| exact STy| exact AGy| apply incl_appl, incl_refl| exact G| intros a N1 N2; exact N1]. }
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ (qs, P, 680%Z) Gy' ltac:(apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as ((_ & _ & PTOP & _) & P0 & _).
      cbn [cb_addr cb_size fst snd] in PTOP, P0. atop_facts.
      apply blank_recell_ng in CELLS0.
      unfold PCAP_TSTAMP_PRECISION_MICRO. cbn [Z.eqb].
      ienterG. zstep. if_false_by (eqb_lits_false P 0 ltac:(lia) ltac:(lia) ltac:(lia)).
      apply evtF_done. subst POSTQ.
      eapply (ngc_fill_alloc fuel) with (qs := qs) (P := P) (TL := TL) (sw := sw) (j0 := j0) (j := j) (e := e) (fpre := fpre) (fmid := fmid) (fpost := fpost) (ccs := ccs) (k0 := k0) (k1 := k1) (k2 := k2) (tlw := tlw);
        [ exact CTX | exact INVy | exact TLR | exact FRAy | exact FCURy | exact Hccs | exact FRCy | exact HEy | exact HEBy | exact CELLS0 ].
  Qed.
  End Sz3.
  Theorem ngc_fill : ltac:(let t := eval cbv delta [ngc_fill__stmt] in ngc_fill__stmt in exact t).
  Proof using GL GPL HAL FRET FREE FREENULL MALLOCS SNPRINTF LT2DLT ADJSNAP MAXSNAP OPENC ADDIF RBLK RBYTES. red. intros fuel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sw TL j0 j ccs fpre fmid fpost k0 k1 k2 tlw e. ltac2:(SecDiet.SzSec.closeP 'ngc_fill__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcFill.
End CANSEC1.
End TwB.
End F_ngchk_fillA.

(* [comment removed for export] *)
Module F_ngchk_allA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_fstmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_hstmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_hstmt2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_fillA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_hshortA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_ngchk_hlenA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_hbomA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_headA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcAll.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis FENTER0 : fenter_stmt_o FO GIOA fflagA 0 STACK_MALLOC_0.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis MALLOCS : malloc_stmt_o HO GIOA.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.
  Hypothesis OPENC : open_offline_common_stmt HO FO sites GIOA TP.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.
  Hypothesis RBLK : read_block_stmt HO FO sites GIOA TP.
  Hypothesis RBYTES : read_bytes_stmt HO FO sites GIOA TP.

  Local Ltac close thm := eapply thm; eassumption.
  Let FILL : ngc_fill_stmt HO FO sites GIOA TP fflagA. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_fillA.ngc_fill. Qed.
  Let SHORT : ngc_short_stmt HO FO sites GIOA TP fflagA. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_hshortA.ngc_short. Qed.
  Let LENFAIL : ngc_lenfail_stmt HO FO sites GIOA TP fflagA. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_ngchk_hlenA.ngc_lenfail. Qed.
  Let BOM : ngc_bom_stmt HO FO sites GIOA TP fflagA. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_hbomA.ngc_bom. Qed.

  #[using="fflagA GL GPL HAL FENTER0 FRET FREE FREENULL MALLOCS FREAD FERROR FMT SNPRINTF LT2DLT ADJSNAP MAXSNAP OPENC ADDIF RBLK RBYTES FILL SHORT LENFAIL BOM"] Theorem pcap_ng_check_header_proofA : pcap_ng_check_header_stmt HO FO sites GIOA TP.
  Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_headA.pcap_ng_check_header_headA. Qed.
End NgcAll.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_fstmtA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_hstmtA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_hstmt2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_fillA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_hshortA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_ngchk_hlenA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_hbomA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_headA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcAll.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis FENTER0 : fenter_stmt_o FO GIOA fflagA 0 STACK_MALLOC_0.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis MALLOCS : malloc_stmt_o HO GIOA.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.
  Hypothesis OPENC : open_offline_common_stmt HO FO sites GIOA TP.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.
  Hypothesis RBLK : read_block_stmt HO FO sites GIOA TP.
  Hypothesis RBYTES : read_bytes_stmt HO FO sites GIOA TP.

  Local Ltac close thm := eapply thm; eassumption.
  Let FILL : ngc_fill_stmt HO FO sites GIOA TP fflagA. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_fsegA__A3P.F_ngchk_fillA.TwB.ngc_fill. Qed.
  Let SHORT : ngc_short_stmt HO FO sites GIOA TP fflagA. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_hshortA.TwB.ngc_short. Qed.
  Let LENFAIL : ngc_lenfail_stmt HO FO sites GIOA TP fflagA. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_ngchk_hlenA.TwB.ngc_lenfail. Qed.
  Let BOM : ngc_bom_stmt HO FO sites GIOA TP fflagA. Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_hbomA.TwB.ngc_bom. Qed.

  #[using="fflagA GL GPL HAL FENTER0 FRET FREE FREENULL MALLOCS FREAD FERROR FMT SNPRINTF LT2DLT ADJSNAP MAXSNAP OPENC ADDIF RBLK RBYTES FILL SHORT LENFAIL BOM"] Theorem pcap_ng_check_header_proofA : pcap_ng_check_header_stmt HO FO sites GIOA TP.
  Proof. close @OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_ngchk_headA.TwB.pcap_ng_check_header_headA. Qed.
End NgcAll.
End CANSEC1.
End TwB.
End F_ngchk_allA.
