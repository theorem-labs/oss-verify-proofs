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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfHandleA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad Fmt StdioCore Stdio Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_gotA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P.
From Stdlib Require String.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_iface_ppA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_exitA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_normA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_sfchk_fsegA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfHandleA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
(* [comment removed for export] *)
Local Ltac qnorm := try change (2^64 - 2^32)%Z with 18446744069414584320%Z.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pblk_ok (RNG : footprint) (SPA P Fb bP kPF : Z) : Prop :=
  rng RNG P 664 /\ rng RNG (shad P) (nshad 664) /\ rng RNG SPA 88 /\ rng RNG Fb 128 /\ rng_aimg RNG
  /\ (P mod 16 = 0)%Z /\ (0 <= bP <= 1)%Z /\ (P + 664 <= 2147446784 + bP * 140737479966720)%Z /\ (17594333495296 * bP <= P)%Z /\ (6307840 <= P)%Z
  /\ (P + 664 <= SPA)%Z /\ (Fb + 128 <= SPA)%Z /\ (0 < Fb)%Z /\ (SPA + 88 <= 2^47)%Z /\ (17594333495296 <= SPA)%Z
  /\ (0 <= kPF <= 1)%Z /\ (P + 664 <= Fb + kPF * 18446744073709551616)%Z /\ (Fb + 128 <= P + (1 - kPF) * 18446744073709551616)%Z.
Definition hdrf_ok (mi maj min n0 n1 n2 n3 l0 l1 l2 l3 : Z) : Prop :=
  (2^31 <= mi < 2^32)%Z /\ (0 <= maj < 2^16)%Z /\ (0 <= min < 2^16)%Z
  /\ (0 <= n0 < 256)%Z /\ (0 <= n1 < 256)%Z /\ (0 <= n2 < 256)%Z /\ (0 <= n3 < 256)%Z
  /\ (0 <= l0 < 256)%Z /\ (0 <= l1 < 256)%Z /\ (0 <= l2 < 256)%Z /\ (0 <= l3 < 256)%Z /\ l2 = 0%Z /\ (l3 mod 4 = 0)%Z.


(* [comment removed for export] *)
Definition ltext_wordB__stmt : Prop := forall l0 l1 l2 l3, (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z -> (0 <= l2 < 256)%Z -> (0 <= l3 < 256)%Z ->
  Z_to_bv 64 (Z.land (sxv l0 l1 l2 l3 mod 18446744073709551616) 18446744073709486080) = Z_to_bv 64 (s32 (Z.land (le4val l0 l1 l2 l3) 4294901760)).
Section Sz1.
Variables l0 l1 l2 l3 : ltac2:(SecDiet.SzSec.tyM 'ltext_wordB__stmt "vvvv" @l0).
#[using="Type"] Lemma ltext_wordB__body : ltac2:(SecDiet.SzSec.bodyP 'ltext_wordB__stmt "vvvv").
Proof.
  intros B0 B1 B2 B3.
  qnorm.
  qfold.
  unfold sxv, le4val. apply bv_eq. rewrite !Z_to_bv_unsigned.
  change 18446744073709486080%Z with (Z.shiftl (Z.ones 48) 16). rewrite land_ones_shift' by (Z.div_mod_to_equations; lia).
  change 4294901760%Z with (Z.shiftl (Z.ones 16) 16). rewrite land_ones_shift' by lia.
  unfold s32, bv_wrap, bv_modulus. cbn -[Z.add Z.sub Z.modulo Z.mul Z.div Z.pow]. cbn [Z.pow Z.pow_pos Pos.iter Z.mul].
  Z.div_mod_to_equations. lia.
Qed.
End Sz1.
Lemma ltext_wordB : ltac:(let t := eval cbv delta [ltext_wordB__stmt] in ltext_wordB__stmt in exact t).
Proof. intros l0 l1 l2 l3. ltac2:(SecDiet.SzSec.closeP 'ltext_wordB__body "vvvv"). Qed.

Section CANSEC1. Context {rc : runConstT}.
Section FillSeg.
  Variables (ra sp gp tp t1 t2 s0 s3 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (RNG : footprint) (SPA P Fb EB ERR : Z) (bP kPF : Z).
  (* [comment removed for export] *)
  Variables (mi maj min n0 n1 n2 n3 l0 l1 l2 l3 : Z) (sw : bool) (j1 j3 pre mid post : list byte) (k0 k1 k2 flagw : word).
  (* [comment removed for export] *)
  Hypothesis PBK : pblk_ok RNG SPA P Fb bP kPF.
  Hypothesis HOK : hdrf_ok mi maj min n0 n1 n2 n3 l0 l1 l2 l3.
  (* [comment removed for export] *)
  Local Notation MW := (mi + (2^64 - 2^32))%Z.
  (* [comment removed for export] *)
  Local Notation FRAME := [C8 k0; C8 k1; C8 k2; CB 8 pre; C4 (Z_to_bv 64 MW); C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid;
                           C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3)); CB 64 post; C8 flagw].
  Local Notation REGS xra xt0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 :=
    (mkR xra (Z_to_bv 64 SPA) gp tp xt0 t1 t2 s0 (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
         xs2 s3 (Z_to_bv 64 (Fb + 36)) (Z_to_bv 64 MW) xs6 (Z_to_bv 64 (Fb + 32)) xs8 s9 s10 (Z_to_bv 64 2147450880) t3 t4 t5 t6).
  (* [comment removed for export] *)
  Local Notation SPILL0 := [CB 24 j1; C8 (Z_to_bv 64 (Z.b2z sw)); C8 z64; C8 (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880));
                            C8 (Z_to_bv 64 EB); C8 (Z_to_bv 64 ERR); CB 16 j3; C8 (Z_to_bv 64 Fb)].
  Local Notation SPILL1 := [CB 16 (firstn 16 j1); C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 100));
                            C8 z64; C8 (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)); C8 (Z_to_bv 64 EB); C8 (Z_to_bv 64 ERR); CB 16 j3; C8 (Z_to_bv 64 Fb)].
  Local Notation B8 := (C8 (Z_to_bv 64 0)).
  Local Notation B4 := (C4 (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Definition fill_seg1__stmt : Prop := forall (m : mem) (t0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s8 : word),
    mem_inv asegs m -> unpoisoned m P (P + 664) ->
    rw_cells asegs m SPA SPILL0 -> rw_cells asegs m Fb FRAME -> rw_cells asegs m P (blank_cells P) ->
    evtF asegs RNG (fun ms' => exists a1' a2' a3' a4' m',
        ms' = MS (REGS (Z_to_bv 64 0x88094) t0 (Z_to_bv 64 (l0 + 256 * l1)) a1' a2' a3' a4' a5 a6 a7 (Z_to_bv 64 (sxv l0 l1 l2 l3)) s6 (Z_to_bv 64 P))
                 F (Z_to_bv 64 LINKTYPE_TO_DLT_ENTRY) fc None m' (seg_rom asegs)
        /\ munch [(P, P + 664)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' P (pcells P sw maj min 0 0 B8 B4 B8 B4 B8 B8 B4 B4))
      (MS (REGS ra t0 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s6 s8) F (Z_to_bv 64 0x88020) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables m t0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s8 : ltac2:(SecDiet.SzSec.tyM 'fill_seg1__stmt "vvvvvvvvvvvv" @m).
  #[using="bP kPF PBK HOK"] Lemma fill_seg1__body : ltac2:(SecDiet.SzSec.bodyP 'fill_seg1__stmt "vvvvvvvvvvvv").
  Proof.
 intros MI PUNP FRA FRC CELLS.
 qnorm.
 qfold.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & RIMG & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof HOK as (MIB & Bmaj & Bmin & N0 & N1 & N2 & N3 & L0 & L1 & L2 & L3 & Z2 & Z3).
    pose proof (munch_refl [(P, P + 664)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold blank_cells, PCAP_PRIV_OFF in CELLS.
    zstep. replace (Z.land P 7) with 0%Z by (rewrite land7_mod; Z.div_mod_to_equations; lia).
    zstep. if_false.
    zstep. ck0 PUNP; ck_go.
    do 2 zstep. ck0 PUNP; ck_go.
    do 2 zstep. ck0 PUNP; ck_go.
    zstep. rewrite (sx32_lit l0 l1 l2 l3) by lia. zstep.
    rewrite ?zx16_lit by lia.
    do 5 zstep.
    rewrite (lt16_wordA l0 l1 l2 l3) by lia.
    apply evtF_done. do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    unfold pcells. rewrite !zx16_lit in CELLS by lia. exact CELLS.
  Qed.
  End Sz2.
  #[using="bP kPF PBK HOK"] Lemma fill_seg1 : ltac:(let t := eval cbv delta [fill_seg1__stmt] in fill_seg1__stmt in exact t).
  Proof. intros m t0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s8. ltac2:(SecDiet.SzSec.closeP 'fill_seg1__body "vvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fill_seg2__stmt : Prop := forall (m : mem) (t0 a1 a2 a3 a4 a5 a6 a7 s6 : word) (lt : Z),
    mem_inv asegs m -> unpoisoned m P (P + 664) ->
    rw_cells asegs m SPA SPILL0 -> rw_cells asegs m Fb FRAME -> rw_cells asegs m P (pcells P sw maj min 0 0 B8 B4 B8 B4 B8 B8 B4 B4) ->
    evtF asegs RNG (fun ms' => exists a2' a3' a4' m',
        ms' = MS (REGS (Z_to_bv 64 0x880e8) t0 (Z_to_bv 64 lt) (Z_to_bv 64 (s32 (le4val n0 n1 n2 n3))) a2' a3' a4' a5 a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 P) (Z_to_bv 64 P))
                 F (Z_to_bv 64 PCAP_ADJUST_SNAPSHOT_ENTRY) fc None m' (seg_rom asegs)
        /\ munch [(SPA, SPA + 88); (P, P + 664)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' SPA SPILL1
        /\ rw_cells asegs m' P (pcells P sw maj min lt (s32 (Z.land (le4val l0 l1 l2 l3) 4294901760)) B8 B4 B8 B4 B8 B8 B4 B4))
      (MS (REGS (Z_to_bv 64 0x88094) t0 (Z_to_bv 64 lt) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (sxv l0 l1 l2 l3)) s6 (Z_to_bv 64 P))
          F (Z_to_bv 64 0x88094) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables m t0 a1 a2 a3 a4 a5 a6 a7 s6 lt : ltac2:(SecDiet.SzSec.tyM 'fill_seg2__stmt "vvvvvvvvvvv" @m).
  #[using="bP kPF PBK HOK"] Lemma fill_seg2__body : ltac2:(SecDiet.SzSec.bodyP 'fill_seg2__stmt "vvvvvvvvvvv").
  Proof.
 intros MI PUNP FRA FRC CELLS.
 qnorm.
 qfold.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & RIMG & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof HOK as (MIB & Bmaj & Bmin & N0 & N1 & N2 & N3 & L0 & L1 & L2 & L3 & Z2 & Z3).
    pose proof (munch_refl [(SPA, SPA + 88); (P, P + 664)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold pcells in CELLS.
    do 2 zstep. ck0 PUNP; ck_go.
    do 4 zstep.
    zstep. ck0 PUNP; ck_go.
    do 5 zstep.
    zstep.
    rewrite (ltext_wordB l0 l1 l2 l3) in * by assumption.
    rewrite (sx32_s32 (le4val n0 n1 n2 n3)) by (unfold le4val; lia).
    apply evtF_done. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [exact FRA|]. unfold pcells. exact CELLS.
  Qed.
  End Sz3.
  #[using="bP kPF PBK HOK"] Lemma fill_seg2 : ltac:(let t := eval cbv delta [fill_seg2__stmt] in fill_seg2__stmt in exact t).
  Proof. intros m t0 a1 a2 a3 a4 a5 a6 a7 s6 lt. ltac2:(SecDiet.SzSec.closeP 'fill_seg2__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fill_seg3__stmt : Prop := forall (m : mem) (t0 a1 a2 a3 a4 a5 a6 a7 : word) (lt ext snap : Z),
    mem_inv asegs m -> unpoisoned m P (P + 664) ->
    rw_cells asegs m SPA SPILL1 -> rw_cells asegs m P (pcells P sw maj min lt ext B8 B4 B8 B4 B8 B8 B4 B4) ->
    evtF asegs RNG (fun ms' => exists a3' a6' m',
        ms' = MS (REGS (Z_to_bv 64 0x880e8) t0 (Z_to_bv 64 snap) (Z_to_bv 64 (P + 96)) (Z_to_bv 64 (P + 648)) a3' (Z_to_bv 64 P)
                       (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) a6' (Z_to_bv 64 0)
                       (Z_to_bv 64 ERR) (Z_to_bv 64 P) s3)
                 F (Z_to_bv 64 0x8817c) fc None m' (seg_rom asegs)
        /\ munch [(P, P + 664)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' P (pcells P sw maj min lt ext (C8 (Z_to_bv 64 0x885a0)) B4 B8 (C4 (Z_to_bv 64 snap)) B8 B8 B4 B4))
      (MS (REGS (Z_to_bv 64 0x880e8) t0 (Z_to_bv 64 snap) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 P) (Z_to_bv 64 P))
          F (Z_to_bv 64 0x880e8) fc None m (seg_rom asegs)).
  Section Sz4.
  Variables m t0 a1 a2 a3 a4 a5 a6 a7 lt ext snap : ltac2:(SecDiet.SzSec.tyM 'fill_seg3__stmt "vvvvvvvvvvvv" @m).
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_seg3__body : ltac2:(SecDiet.SzSec.bodyP 'fill_seg3__stmt "vvvvvvvvvvvv").
  Proof.
 intros MI PUNP FRA CELLS.
 qnorm.
 qfold.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & RIMG & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof HOK as (MIB & Bmaj & Bmin & N0 & N1 & N2 & N3 & L0 & L1 & L2 & L3 & Z2 & Z3).
    pose proof (munch_refl [(P, P + 664)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold pcells in CELLS.
    zstep. ck0 PUNP; ck_go.
    do 2 zstep. ck0 PUNP; ck_go.
    do 5 zstep. ck0 PUNP; ck_go.
    zstep. ck0 PUNP; ck_go.
    do 3 zstep.
    zstep. if_false.
    zstep.
    zstep. if_false.
    assert (XX : (0 < P + 648 < 2^64)%Z) by lia.
    zstep. if_false_by (eqz_false _ XX).
    zstep. replace (Z.land (P + 648) 7) with 0%Z by (rewrite land7_mod; Z.div_mod_to_equations; lia).
    zstep. if_false.
    apply evtF_done. do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    unfold pcells. exact CELLS.
  Qed.
  End Sz4.
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_seg3 : ltac:(let t := eval cbv delta [fill_seg3__stmt] in fill_seg3__stmt in exact t).
  Proof. intros m t0 a1 a2 a3 a4 a5 a6 a7 lt ext snap. ltac2:(SecDiet.SzSec.closeP 'fill_seg3__body "vvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fill_scale : sf_scale_t := if (mi =? NSEC_TCPDUMP_MAGIC)%Z then SF_SCALE_DOWN else SF_PASS_THROUGH.
  Definition fill_lensw : lenswap_t :=
    if (maj =? 2)%Z then (if (min <? 3)%Z then SWAPPED else if (min =? 3)%Z then MAYBE_SWAPPED else NOT_SWAPPED)
    else if (maj =? 543)%Z then SWAPPED else NOT_SWAPPED.
  Definition fill_hs_ss (lt snap : Z) : Z * Z :=
    if (mi =? KUZNETZOV_TCPDUMP_MAGIC)%Z
    then (24, if (lt =? DLT_EN10MB)%Z then (if (snap <=? INT_MAX - 14)%Z then snap + 14 else INT_MAX) else snap)%Z
    else (16, snap)%Z.

  (* [comment removed for export] *)
  Definition fill_seg4__stmt : Prop := forall (m : mem) (t0 a0 a1 a3 a4 a5 a6 a7 s2 s6 s8 : word) (lt ext : Z) (nxtw snapw : word),
    mem_inv asegs m -> unpoisoned m P (P + 664) -> rw_cells asegs m Fb FRAME ->
    rw_cells asegs m P (pcells P sw maj min lt ext (C8 nxtw) B4 B8 (C4 snapw) B8 B8 B4 B4) ->
    evtF asegs RNG (fun ms' => exists a3' a6' m',
        ms' = MS (REGS (Z_to_bv 64 0x880e8) (Z_to_bv 64 543) a0 a1 (Z_to_bv 64 (P + 648)) a3' a4 a5 a6' (Z_to_bv 64 maj) s2 s6 s8)
                 F (Z_to_bv 64 0x881f0) fc None m' (seg_rom asegs)
        /\ munch [(P, P + 664)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' P (pcells P sw maj min lt ext (C8 nxtw) B4 B8 (C4 snapw) B8 B8 B4 (C4 (Z_to_bv 64 (sfscale_code fill_scale)))))
      (MS (REGS (Z_to_bv 64 0x880e8) t0 a0 a1 (Z_to_bv 64 (P + 648)) a3 a4 a5 a6 a7 s2 s6 s8)
          F (Z_to_bv 64 0x8817c) fc None m (seg_rom asegs)).
  Section Sz5.
  Variables m t0 a0 a1 a3 a4 a5 a6 a7 s2 s6 s8 lt ext nxtw snapw : ltac2:(SecDiet.SzSec.tyM 'fill_seg4__stmt "vvvvvvvvvvvvvvvv" @m).
  #[using="bP kPF PBK HOK"] Lemma fill_seg4__body : ltac2:(SecDiet.SzSec.bodyP 'fill_seg4__stmt "vvvvvvvvvvvvvvvv").
  Proof.
 intros MI PUNP FRC CELLS.
 qnorm.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & RIMG & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof HOK as (MIB & Bmaj & Bmin & N0 & N1 & N2 & N3 & L0 & L1 & L2 & L3 & Z2 & Z3).
    pose proof (munch_refl [(P, P + 664)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold pcells in CELLS. unfold fill_scale.
    do 3 zstep.
    zstep.
    destruct (Z.eq_dec mi NSEC_TCPDUMP_MAGIC) as [EN|NN].
    - replace (Z.lxor (mi + 18446744069414584320) 18446744072127396941 <? 1)%Z with true by (rewrite EN; reflexivity).
      replace (mi =? NSEC_TCPDUMP_MAGIC)%Z with true by (symmetry; apply Z.eqb_eq; exact EN).
      cbn [Z.b2z].
      do 3 zstep. ck0 PUNP; ck_go.
      zstep. rewrite ?zx16_lit by lia. do 2 zstep.
      apply evtF_done. do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      unfold pcells. exact CELLS.
    - replace (Z.lxor (mi + 18446744069414584320) 18446744072127396941 <? 1)%Z with false.
      2:{ symmetry. apply Z.ltb_ge.
          assert (NZ : Z.lxor (mi + 18446744069414584320) 18446744072127396941 <> 0%Z)
            by (intro E0; apply Z.lxor_eq in E0; unfold NSEC_TCPDUMP_MAGIC in NN; lia).
          assert (NNg : (0 <= Z.lxor (mi + 18446744069414584320) 18446744072127396941)%Z) by (apply Z.lxor_nonneg; split; lia).
          lia. }
      replace (mi =? NSEC_TCPDUMP_MAGIC)%Z with false by (symmetry; apply Z.eqb_neq; exact NN).
      cbn [Z.b2z].
      do 3 zstep. ck0 PUNP; ck_go.
      zstep. rewrite ?zx16_lit by lia. do 2 zstep.
      apply evtF_done. do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      unfold pcells. exact CELLS.
  Qed.
  End Sz5.
  #[using="bP kPF PBK HOK"] Lemma fill_seg4 : ltac:(let t := eval cbv delta [fill_seg4__stmt] in fill_seg4__stmt in exact t).
  Proof. intros m t0 a0 a1 a3 a4 a5 a6 a7 s2 s6 s8 lt ext nxtw snapw. ltac2:(SecDiet.SzSec.closeP 'fill_seg4__body "vvvvvvvvvvvvvvvv"). Qed.

  Local Tactic Notation "seg_done" integer(n) ident(MU) ident(WM) :=
    apply evtF_done; do n eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|].
  Local Ltac decide_ifs :=
    repeat first [ rewrite (proj2 (Z.eqb_eq _ _)) by lia | rewrite (proj2 (Z.eqb_neq _ _)) by lia
                 | rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia
                 | rewrite (proj2 (Z.leb_le _ _)) by lia | rewrite (proj2 (Z.leb_gt _ _)) by lia ].
  (* [comment removed for export] *)
  Local Ltac priv_guard :=
    zstep; replace (Z.land (P + 648) 7) with 0%Z by (rewrite land7_mod; Z.div_mod_to_equations; lia); zstep; if_false.

  (* [comment removed for export] *)
  Definition fill_segL__stmt : Prop := forall (m : mem) (a0 a1 a3 a4 a5 a6 s2 s6 s8 : word) (lt ext : Z) (nxtw snapw sclw : word),
    mem_inv asegs m -> unpoisoned m P (P + 664) -> rw_cells asegs m Fb FRAME ->
    rw_cells asegs m P (pcells P sw maj min lt ext (C8 nxtw) B4 B8 (C4 snapw) B8 B8 B4 (C4 sclw)) ->
    evtF asegs RNG (fun ms' => exists a3' a6' a7' m',
        ms' = MS (REGS (Z_to_bv 64 0x880e8) (Z_to_bv 64 543) a0 a1 (Z_to_bv 64 (P + 648)) a3' a4 a5 a6' a7' s2 s6 s8)
                 F (Z_to_bv 64 0x88290) fc None m' (seg_rom asegs)
        /\ munch [(P, P + 664)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' P (pcells P sw maj min lt ext (C8 nxtw) B4 B8 (C4 snapw) B8 B8 (C4 (Z_to_bv 64 (lenswap_code fill_lensw))) (C4 sclw)))
      (MS (REGS (Z_to_bv 64 0x880e8) (Z_to_bv 64 543) a0 a1 (Z_to_bv 64 (P + 648)) a3 a4 a5 a6 (Z_to_bv 64 maj) s2 s6 s8)
          F (Z_to_bv 64 0x881f0) fc None m (seg_rom asegs)).
  Section Sz6.
  Variables m a0 a1 a3 a4 a5 a6 s2 s6 s8 lt ext nxtw snapw sclw : ltac2:(SecDiet.SzSec.tyM 'fill_segL__stmt "vvvvvvvvvvvvvvv" @m).
  #[using="bP kPF PBK HOK"] Lemma fill_segL__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segL__stmt "vvvvvvvvvvvvvvv").
  Proof.
 intros MI PUNP FRC CELLS.
 qnorm.
 qfold.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & RIMG & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof HOK as (MIB & Bmaj & Bmin & N0 & N1 & N2 & N3 & L0 & L1 & L2 & L3 & Z2 & Z3).
    pose proof (munch_refl [(P, P + 664)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold pcells in CELLS.
    zstep. if_cases K543; zify_cond K543.
    - priv_guard. do 3 zstep. ck0 PUNP; ck_go. zstep.
      seg_done 4 MU WM. unfold pcells, fill_lensw. decide_ifs. exact CELLS.
    - do 2 zstep. if_cases K2; zify_cond K2.
      + priv_guard. do 3 zstep. ck0 PUNP; ck_go. zstep.
        seg_done 4 MU WM. unfold pcells, fill_lensw. decide_ifs. exact CELLS.
      + zstep. rewrite ?zx16_lit by lia. zstep. if_cases Klt; zify_cond Klt.
        * priv_guard. do 2 zstep.
          destruct (Z.eq_dec min 3) as [E3|E3].
          -- replace (min + -3 <? 1)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
             do 2 zstep. ck0 PUNP; ck_go. zstep.
             seg_done 4 MU WM. unfold pcells, fill_lensw. decide_ifs. exact CELLS.
          -- replace (min + -3 <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
             do 2 zstep. ck0 PUNP; ck_go. zstep.
             seg_done 4 MU WM. unfold pcells, fill_lensw. decide_ifs. exact CELLS.
        * priv_guard. do 3 zstep. ck0 PUNP; ck_go. zstep.
          seg_done 4 MU WM. unfold pcells, fill_lensw. decide_ifs. exact CELLS.
  Qed.
  End Sz6.
  #[using="bP kPF PBK HOK"] Lemma fill_segL : ltac:(let t := eval cbv delta [fill_segL__stmt] in fill_segL__stmt in exact t).
  Proof. intros m a0 a1 a3 a4 a5 a6 s2 s6 s8 lt ext nxtw snapw sclw. ltac2:(SecDiet.SzSec.closeP 'fill_segL__body "vvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fill_segH__stmt : Prop := forall (m : mem) (t0 a3 a6 a7 s2 s6 s8 : word) (lt ext snap : Z) (nxtw lsww sclw : word),
    mem_inv asegs m -> unpoisoned m P (P + 664) -> (0 <= lt < 2^31)%Z -> (1 <= snap <= 2147483647)%Z ->
    rw_cells asegs m SPA SPILL1 ->
    rw_cells asegs m P (pcells P sw maj min lt ext (C8 nxtw) B4 B8 (C4 (Z_to_bv 64 snap)) B8 B8 (C4 lsww) (C4 sclw)) ->
    evtF asegs RNG (fun ms' => exists a0' a2' a3' a6' m',
        ms' = MS (REGS (Z_to_bv 64 0x880e8) t0 a0' (Z_to_bv 64 (P + 96)) a2' a3' (Z_to_bv 64 P) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) a6' a7
                       s2 s6 s8)
                 F (Z_to_bv 64 0x88324) fc None m' (seg_rom asegs)
        /\ munch [(P, P + 664)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' P (pcells P sw maj min lt ext (C8 nxtw) B4 B8 (C4 (Z_to_bv 64 (snd (fill_hs_ss lt snap)))) B8
                                       (C8 (Z_to_bv 64 (fst (fill_hs_ss lt snap)))) (C4 lsww) (C4 sclw)))
      (MS (REGS (Z_to_bv 64 0x880e8) t0 (Z_to_bv 64 snap) (Z_to_bv 64 (P + 96)) (Z_to_bv 64 (P + 648)) a3 (Z_to_bv 64 P)
                (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) a6 a7 s2 s6 s8)
          F (Z_to_bv 64 0x88290) fc None m (seg_rom asegs)).
  Section Sz7.
  Variables m t0 a3 a6 a7 s2 s6 s8 lt ext snap nxtw lsww sclw : ltac2:(SecDiet.SzSec.tyM 'fill_segH__stmt "vvvvvvvvvvvvvv" @m).
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_segH__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segH__stmt "vvvvvvvvvvvvvv").
  Proof.
 intros MI PUNP LTR SNR FRA CELLS.
 qnorm.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & RIMG & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof HOK as (MIB & Bmaj & Bmin & N0 & N1 & N2 & N3 & L0 & L1 & L2 & L3 & Z2 & Z3).
    pose proof (munch_refl [(P, P + 664)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold pcells in CELLS. unfold fill_hs_ss, INT_MAX, DLT_EN10MB.
    do 3 zstep.
    replace (Z.land (P + 648) 7) with 0%Z by (rewrite land7_mod; Z.div_mod_to_equations; lia).
    replace (Z_to_bv 64 (-1582117580)) with (Z_to_bv 64 18446744072127434036) by (apply Z_to_bv_eqm; reflexivity).
    zstep.
    destruct (Z.eq_dec mi KUZNETZOV_TCPDUMP_MAGIC) as [EK|NK].
    - subst mi. rewrite Z.eqb_refl. if_false.
      zstep. if_false.
      ck0 PUNP; ck_go.
      do 2 zstep.
      ck0_at PUNP (P + 100)%Z; ck_go.
      zstep. rewrite (sx32_small lt) by lia.
      do 2 zstep.
      destruct (Z.eq_dec lt 1) as [EL1|EL1].
      + subst lt. if_false.
        do 3 zstep.
        destruct (Z.le_gt_cases snap 2147483633) as [S1|S1].
        * if_cases Ks; [zify_cond Ks; rewrite ?signed_lit_small in Ks by lia; exfalso; lia|].
          ck0_at PUNP (P + 96)%Z; ck_go.
          do 2 zstep.
          ck0_at PUNP (P + 96)%Z; ck_go.
          seg_done 5 MU WM. cbn [fst snd]. decide_ifs. unfold pcells. exact CELLS.
        * if_cases Ks; [|zify_cond Ks; rewrite ?signed_lit_small in Ks by lia; exfalso; lia].
          ck0_at PUNP (P + 96)%Z; ck_go.
          do 3 zstep.
          ck0_at PUNP (P + 96)%Z; ck_go.
          seg_done 5 MU WM. cbn [fst snd]. decide_ifs. unfold pcells.
          lazymatch type of CELLS with rw_cells _ ?mm _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: C4 ?w :: ?post) =>
            pose proof (rw_cells_C4_low mm P [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13] w (Z_to_bv 64 2147483647) post CELLS le4_intmax) as CELLS2 end.
          cbn [app] in CELLS2. exact CELLS2.
      + if_cases Kl; [|zify_cond Kl; exfalso; lia].
        ck0_at PUNP (P + 96)%Z; ck_go.
        seg_done 5 MU WM. cbn [fst snd]. decide_ifs. unfold pcells. exact CELLS.
    - replace (mi =? KUZNETZOV_TCPDUMP_MAGIC)%Z with false by (symmetry; apply Z.eqb_neq; exact NK).
      unfold KUZNETZOV_TCPDUMP_MAGIC in NK.
      if_cases KK; [|zify_cond KK; exfalso; lia].
      zstep. if_false.
      ck0 PUNP; ck_go.
      do 2 zstep.
      ck0_at PUNP (P + 96)%Z; ck_go.
      seg_done 5 MU WM. cbn [fst snd]. unfold pcells. exact CELLS.
  Qed.
  End Sz7.
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_segH : ltac:(let t := eval cbv delta [fill_segH__stmt] in fill_segH__stmt in exact t).
  Proof. intros m t0 a3 a6 a7 s2 s6 s8 lt ext snap nxtw lsww sclw. ltac2:(SecDiet.SzSec.closeP 'fill_segH__body "vvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fill_segB__stmt : Prop := forall (m : mem) (t0 a0 a2 a3 a5 a6 a7 s2 s6 s8 : word) (lt ext SS : Z) (nxtw hszw lsww sclw : word),
    mem_inv asegs m -> unpoisoned m P (P + 664) -> (1 <= SS <= 2147483647)%Z ->
    rw_cells asegs m P (pcells P sw maj min lt ext (C8 nxtw) B4 B8 (C4 (Z_to_bv 64 SS)) B8 (C8 hszw) (C4 lsww) (C4 sclw)) ->
    evtF asegs RNG (fun ms' => exists a1' a2' m',
        ms' = MS (REGS (Z_to_bv 64 0x88358) t0 (Z_to_bv 64 (if 2048 <? SS then 2048 else SS)%Z) a1' a2' a3 (Z_to_bv 64 P) a5 a6 a7 (Z_to_bv 64 P) s6 s8)
                 F (Z_to_bv 64 0x561e0) fc None m' (seg_rom asegs)
        /\ munch [(P, P + 664)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' P (pcells P sw maj min lt ext (C8 nxtw) (C4 (Z_to_bv 64 (if 2048 <? SS then 2048 else SS)%Z)) B8 (C4 (Z_to_bv 64 SS)) B8
                                       (C8 hszw) (C4 lsww) (C4 sclw)))
      (MS (REGS (Z_to_bv 64 0x880e8) t0 a0 (Z_to_bv 64 (P + 96)) a2 a3 (Z_to_bv 64 P) a5 a6 a7 s2 s6 s8) F (Z_to_bv 64 0x88324) fc None m (seg_rom asegs)).
  Section Sz8.
  Variables m t0 a0 a2 a3 a5 a6 a7 s2 s6 s8 lt ext SS nxtw hszw lsww sclw : ltac2:(SecDiet.SzSec.tyM 'fill_segB__stmt "vvvvvvvvvvvvvvvvvv" @m).
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_segB__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segB__stmt "vvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI PUNP SSR CELLS.
 qnorm.
 qfold.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & RIMG & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof HOK as (MIB & Bmaj & Bmin & N0 & N1 & N2 & N3 & L0 & L1 & L2 & L3 & Z2 & Z3).
    pose proof (munch_refl [(P, P + 664)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold pcells in CELLS.
    zstep. rewrite (sx32_small SS) by lia.
    do 3 zstep. zstep.
    destruct (Z.lt_ge_cases SS 2048) as [S2|S2].
    - if_cases Kt; [|zify_cond Kt; exfalso; lia].
      ck0 PUNP; ck_go. do 3 zstep.
      try unfold QQ. decide_ifs. seg_done 3 MU WM. unfold pcells. exact CELLS.
    - if_cases Kt; [zify_cond Kt; exfalso; lia|].
      zstep. ck0 PUNP; ck_go. do 3 zstep.
      destruct (Z.eq_dec SS 2048) as [E2|E2].
      + subst SS. change (2048 <? 2048)%Z with false. cbv iota. seg_done 3 MU WM. unfold pcells. exact CELLS.
      + try unfold QQ. decide_ifs. seg_done 3 MU WM. unfold pcells. exact CELLS.
  Qed.
  End Sz8.
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_segB : ltac:(let t := eval cbv delta [fill_segB__stmt] in fill_segB__stmt in exact t).
  Proof. intros m t0 a0 a2 a3 a5 a6 a7 s2 s6 s8 lt ext SS nxtw hszw lsww sclw. ltac2:(SecDiet.SzSec.closeP 'fill_segB__body "vvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fill_segE__stmt : Prop := forall (m : mem) (t0 a1 a2 a3 a4 a5 a6 a7 s8 : word) (lt ext B : Z) (nxtw bszw snapw hszw lsww sclw g0 g1 g2 : word),
    mem_inv asegs m -> unpoisoned m P (P + 664) -> (0 < B < 2^64)%Z ->
    rw_cells asegs m SPA SPILL1 ->
    rw_cells asegs m 0xa6508 [C8 g0; C8 g1; C8 g2; C8 (Z_to_bv 64 (pk_cleanup_sf PK))] ->
    rw_cells asegs m P (pcells P sw maj min lt ext (C8 nxtw) (C4 bszw) B8 (C4 snapw) B8 (C8 hszw) (C4 lsww) (C4 sclw)) ->
    evtF asegs RNG (fun ms' => exists a1' a2' m',
        ms' = MS (REGS (Z_to_bv 64 0x88358) t0 (Z_to_bv 64 P) a1' a2' a3 a4 a5 a6 a7 (Z_to_bv 64 ERR) (Z_to_bv 64 P) s8)
                 F (Z_to_bv 64 0x87f24) fc None m' (seg_rom asegs)
        /\ munch [(P, P + 664)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' P (pcells P sw maj min lt ext (C8 nxtw) (C4 bszw) (C8 (Z_to_bv 64 B)) (C4 snapw) (C8 (Z_to_bv 64 (pk_cleanup_sf PK)))
                                       (C8 hszw) (C4 lsww) (C4 sclw)))
      (MS (REGS (Z_to_bv 64 0x88358) t0 (Z_to_bv 64 B) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 P) s8) F (Z_to_bv 64 0x88358) fc None m (seg_rom asegs)).
  Section Sz9.
  Variables m t0 a1 a2 a3 a4 a5 a6 a7 s8 lt ext B nxtw bszw snapw hszw lsww sclw g0 g1 g2 : ltac2:(SecDiet.SzSec.tyM 'fill_segE__stmt "vvvvvvvvvvvvvvvvvvvvvv" @m).
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_segE__body : ltac2:(SecDiet.SzSec.bodyP 'fill_segE__stmt "vvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI PUNP BR FRA GOT CELLS.
 qnorm.
 qfold.
    pose proof PBK as (PRNG & PRSH & RSP & RFR & RIMG & P16 & bPr & bPhi & bPlo & bPimg & PSP & FSP & Fb0 & SPAHI & SPALO & kPFr & kPF1 & kPF2).
    pose proof HOK as (MIB & Bmaj & Bmin & N0 & N1 & N2 & N3 & L0 & L1 & L2 & L3 & Z2 & Z3).
    pose proof (munch_refl [(P, P + 664)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold pcells in CELLS. unfold PK in *. cbn [pk_cleanup_sf] in *.
    zstep. ck0 PUNP; ck_go.
    do 2 zstep.
    zstep. if_false_by (eqz_false B BR).
    zstep. ck0 PUNP; ck_go.
    do 3 zstep.
    do 2 zstep.
    seg_done 3 MU WM. unfold pcells. exact CELLS.
  Qed.
  End Sz9.
  #[using="bP kPF n0 n1 n2 n3 l0 l1 l2 l3 PBK HOK"] Lemma fill_segE : ltac:(let t := eval cbv delta [fill_segE__stmt] in fill_segE__stmt in exact t).
  Proof. intros m t0 a1 a2 a3 a4 a5 a6 a7 s8 lt ext B nxtw bszw snapw hszw lsww sclw g0 g1 g2. ltac2:(SecDiet.SzSec.closeP 'fill_segE__body "vvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fill_hs_ss_range : forall lt snap, (1 <= snap <= 2147483647)%Z ->
    (1 <= snd (fill_hs_ss lt snap) <= 2147483647)%Z /\ (fst (fill_hs_ss lt snap) = 16 \/ fst (fill_hs_ss lt snap) = 24)%Z.
  Proof.
    intros lt snap SNR. unfold fill_hs_ss, INT_MAX. destruct (mi =? KUZNETZOV_TCPDUMP_MAGIC)%Z; cbn [fst snd]; [|lia].
    destruct (lt =? DLT_EN10MB)%Z; [|lia]. destruct (Z.leb_spec snap (2^31 - 1 - 14)); lia.
  Qed.
End FillSeg.

#[using="Type"] Lemma pblk_ok_fp_le : forall RNG RNG' SPA P Fb bP kPF, fp_le RNG RNG' -> pblk_ok RNG SPA P Fb bP kPF -> pblk_ok RNG' SPA P Fb bP kPF.
Proof.
  intros RNG RNG' SPA P Fb bP kPF FP (H1 & H2 & H3 & H4 & H5 & REST).
  split; [exact (rng_fp_le _ _ _ _ FP H1)|]. split; [exact (rng_fp_le _ _ _ _ FP H2)|]. split; [exact (rng_fp_le _ _ _ _ FP H3)|].
  split; [exact (rng_fp_le _ _ _ _ FP H4)|]. split; [exact (rng_fp_le _ _ _ _ FP H5)| exact REST].
Qed.
End CANSEC1.
End F_sfchk_fsegA.

(* [comment removed for export] *)
Module F_sfchk_fillA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_gotA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfHandleA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_gotA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_exitA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_sfchk_fsegA__B3P.F_sfchk_fsegA. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac seg_side1 := lazymatch goal with |- (_ <= _ < _)%Z => idtac | |- (_ <= _ <= _)%Z => idtac | |- (_ < _ < _)%Z => idtac | _ => eassumption end.
Ltac open_pcells := repeat match goal with HH : rw_cells _ _ _ (pcells _ _ _ _ _ _ _ _ _ _ _ _ _ _) |- _ => unfold pcells in HH end.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section ChkFill.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis GOTL : gia_got_law GIOA.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MALLOC : malloc_stmt_o HO GIOA.

  Definition chk_fill__stmt : Prop := chk_fill_stmt HO FO sites GIOA TP fflagA.
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 j1 j3 pre mid post ej k0 k1 k2 q P maj min n0 n1 n2 n3 l0 l1 l2 l3 mi sw : ltac2:(SecDiet.SzSec.tyM 'chk_fill__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL FRET GPL GOTL LT2DLT ADJSNAP MALLOC"] Lemma chk_fill__body : ltac2:(SecDiet.SzSec.bodyP 'chk_fill__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros CTX INV MI3 Bmaj Bmin N0 N1 N2 N3 L0 L1 L2 L3 Z2 Z3 FRA FRC CELLS0 HE HEB.
    chk_setup GL CTX INV.
    assert (MIB : (2^31 <= mi < 2^32)%Z) by (unfold TCPDUMP_MAGIC, KUZNETZOV_TCPDUMP_MAGIC, NSEC_TCPDUMP_MAGIC in MI3; lia).
    (* [comment removed for export] *)
    assert (HinPB : In (q, P, PCAP_SF_TOTAL) [(q, P, PCAP_SF_TOTAL)]) by (left; reflexivity).
    assert (HinP : In (q, P, PCAP_SF_TOTAL) ((CL ++ [(q, P, PCAP_SF_TOTAL)]) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; exact HinPB).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP) as ((PBAND & _ & PTOP & P16) & P0 & PUNP & PRNG & PRSH & _).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0, PUNP, PRNG, PRSH. unfold PCAP_SF_TOTAL in PBAND, PTOP, PUNP, PRNG, PRSH.
    band_ind PBAND bP.
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ G HinP (or_introl eq_refl) ltac:(cbn [cb_size snd]; unfold PCAP_SF_TOTAL; lia)) as (kPF & kPFr & kPF1 & kPF2).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2. unfold PCAP_SF_TOTAL in kPF1, kPF2.
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) (incl_refl _) IFL) HinPB ltac:(lia) ltac:(cbn [cb_size snd]; unfold PCAP_SF_TOTAL; lia)) as (kMP & kMPr & kMP1 & kMP2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_refl _) IFL) HinPB ltac:(lia) ltac:(cbn [cb_size snd]; unfold PCAP_SF_TOTAL; lia)) as (kEP & kEPr & kEP1 & kEP2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinPB ltac:(lia) ltac:(cbn [cb_size snd]; unfold PCAP_SF_TOTAL; lia)) as (kBP & kBPr & kBP1 & kBP2).
    cbn [cb_addr cb_size fst snd] in kMP1, kMP2, kEP1, kEP2, kBP1, kBP2. unfold PCAP_SF_TOTAL in kMP1, kMP2, kEP1, kEP2, kBP1, kBP2.
    assert (PBK : pblk_ok RNGx SPA P Fb bP kPF).
    { unfold pblk_ok. split; [exact PRNG|]. split; [exact PRSH|]. split; [eapply rng_sub'; [exact RSPA| lia]|]. split; [exact FRNG|]. split; [exact RIMG|].
      atop_facts. repeat (split; [first [assumption | lia]|]). first [assumption | lia]. }
    assert (SPALO : (17594333495296 <= SPA)%Z) by (atop_facts; lia).
    assert (HOK : hdrf_ok mi maj min n0 n1 n2 n3 l0 l1 l2 l3) by (unfold hdrf_ok; repeat (split; [assumption|]); assumption).
    apply blank_recell in CELLS0. rename CELLS0 into CELLS.
    (* [comment removed for export] *)
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as (RT0 & _).
    pose proof (gia_global_unp FO GIOA fflagA GL _ _ _ _ _ _ _ 0x22000%Z 28%Z G ltac:(unfold client_globals; repeat (first [left; reflexivity | right]))) as LTUNP.
    pose proof (GOTL _ _ _ _ _ _ _ G) as GOT. unfold GOT_PCAP_ADDR in GOT.
    (* [comment removed for export] *)
    unfold chk_fill_model. cbn [e_fret prims]. rewrite (land_ffff l0 l1 l2 l3) by lia.
    unfold PCAP_TSTAMP_PRECISION_MICRO. cbn [Z.eqb mo_bind mo_ret MOps e_malloc e_free prims].
    set (lt := linktype_to_dlt (l0 + 256 * l1)). set (snap := pcapint_adjust_snapshot lt (le4val n0 n1 n2 n3)).
    pose proof (linktype_to_dlt_range (l0 + 256 * l1) ltac:(lia)) as LTR. fold lt in LTR.
    pose proof (adjust_snapshot_range lt (le4val n0 n1 n2 n3) ltac:(unfold le4val; lia)) as SNR. fold snap in SNR. unfold INT_MAX in SNR.
    set (EXT := s32 (Z.land (le4val l0 l1 l2 l3) 4294901760)).
    set (POSTQ := check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR [mg0; mg1; mg2; mg3] f m (ps_outfile s)).
    pose proof (munch_refl [(bv_unsigned sp - 57344, bv_unsigned sp); (P, P + 664)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF.
    (* [comment removed for export] *)
    call fill_seg1; [eassumption .. | ]. open_pcells.
    (* [comment removed for export] *)
    assert (FWI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv)%Z [(bv_unsigned sp - 57344, bv_unsigned sp); (P, P + 664)]%Z)
      by (repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI; lia|]); apply Forall_nil).
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (LT2DLT _ spa) with (lo := lo) (lt := (l0 + 256 * l1)%Z);
        [ assumption | rewrite Hspa; exact ST | rewrite Hspa; lia | lia | exact (A3P.LibcKit.TwB.artcells_munch _ _ _ RT0 MU WM FWI) | exact LTUNP
        | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] | exact RIMG | exact RISH | reflexivity | lia ]
      | ].
    cbv beta. intros ms' PO. unfold leaf_post in PO. destruct_exs PO. destruct PO as (-> & MUc & WMc & MIc & STc & ->).
    rewrite Hspa in *.
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end; clear MUc WMc.
    try clear ST. rename STc into ST.
    replace (ret_pc (Z_to_bv 64 557204)) with (Z_to_bv 64 557204) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    fold lt. clear Hspa. subst spa.
    (* [comment removed for export] *)
    call fill_seg2; [eassumption .. | ]. open_pcells.
    (* [comment removed for export] *)
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (ADJSNAP _ spa) with (lo := lo) (lt := lt) (snaplen := le4val n0 n1 n2 n3);
        [ assumption | rewrite Hspa; exact ST | reflexivity | lia | reflexivity | unfold le4val; lia ]
      | ].
    cbv beta. intros ms' PO. unfold leaf_post in PO. destruct_exs PO. destruct PO as (-> & MUc & WMc & MIc & STc & ->).
    rewrite Hspa in *.
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end; clear MUc WMc.
    try clear ST. rename STc into ST.
    replace (ret_pc (Z_to_bv 64 557288)) with (Z_to_bv 64 557288) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    fold snap. clear Hspa. subst spa.
    (* [comment removed for export] *)
    call fill_seg3; [eassumption .. | ]. open_pcells.
    call fill_seg4; [eassumption .. | ]. open_pcells.
    call fill_segL; [eassumption .. | ]. open_pcells.
    call fill_segH; [seg_side1 .. | ]; [lia .. | ]. open_pcells.
    destruct (fill_hs_ss_range mi lt snap SNR) as (SSR & HSR).
    (* [comment removed for export] *)
    call fill_segB; [seg_side1 .. | ]; [lia .. | ]. open_pcells.
    lazymatch goal with HH : rw_cells asegs _ SPA _ |- _ => rename HH into FRA1 end.
    lazymatch goal with HH : rw_cells asegs _ P _ |- _ => rename HH into CELLS end.
    (* [comment removed for export] *)
    set (HS := fst (fill_hs_ss mi lt snap)) in *. set (SS := snd (fill_hs_ss mi lt snap)) in *.
    set (BS := (if 2048 <? SS then 2048 else SS)%Z) in *.
    assert (BSR : (1 <= BS <= 2048)%Z) by (subst BS; destruct (Z.ltb_spec 2048 SS); lia).
    replace (chk_sf_model MOps (prims HO FO sites) q f 0 mi sw maj min lt EXT snap
               (if (maj =? 2)%Z then if (min <? 3)%Z then SWAPPED else if (min =? 3)%Z then MAYBE_SWAPPED else NOT_SWAPPED
                else if (maj =? 543)%Z then SWAPPED else NOT_SWAPPED)
               (if (mi =? NSEC_TCPDUMP_MAGIC)%Z then SF_SCALE_DOWN else SF_PASS_THROUGH))
      with (chk_buf_model MOps (prims HO FO sites) q f 0 sw maj min lt EXT HS SS (fill_lensw maj min) (fill_scale mi))
      by (unfold chk_sf_model, HS, SS, fill_hs_ss, fill_lensw, fill_scale; destruct (mi =? KUZNETZOV_TCPDUMP_MAGIC)%Z; reflexivity).
    unfold chk_buf_model. fold BS. cbn [e_malloc e_fret e_free prims mo_bind mo_ret MOps].
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_CHECK_HEADER, Fb, 128%Z)] [(q, P, PCAP_SF_TOTAL)] (bv_unsigned sp))
                   [(bv_unsigned sp - 57344, bv_unsigned sp); (P, P + 664)]%Z) by (unfold PCAP_SF_TOTAL; own_ivs).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mx _ [] _ FW (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
      assert (AGm5 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m mx)
        by (eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG5|]; intros a (K & _); split; [exact K| exact I]);
      assert (UC5 : ucallerA (depth_check_header false) L mx sp s0 ra trC)
        by (eapply ucaller_keep; [exact UC| lia|]; intros a Ha;
            destruct (AGm5 a ltac:(lia) ltac:(split; [left; lia| cbn [outside fst snd]; lia])) as [E1 _]; congruence)
    end.
    pose proof (rw_cells_nth_C8 _ _ _ 11%nat _ FR eq_refl) as BS0. pose proof (rw_cells_nth_C8 _ _ _ 12%nat _ FR eq_refl) as BRA.
    cbn [firstn cells_size csize Nat.add] in BS0, BRA.
    replace (bv_unsigned sp + -104 + Z.of_nat 88)%Z with (bv_unsigned sp - 16)%Z in BS0 by lia.
    replace (bv_unsigned sp + -104 + Z.of_nat 96)%Z with (bv_unsigned sp - 8)%Z in BRA by lia.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { eapply (MALLOC _ spa) with (L := L) (s := sx) (CL := CL ++ [(q, P, PCAP_SF_TOTAL)]) (FB := FB) (FL := (FF_CHECK_HEADER, Fb, 128%Z) :: FL) (lo := lo) (n := BS);
        [ split; [exact G5|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold MALLOC_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | reflexivity | lia
        | eapply (unw_of_ucaller (pred (depth_check_header false)));
            [ eapply (ucaller_frame _ _ _ _ _ _ _ _ _ _ 0x88358%Z UC5); [rewrite Hspa; lia| lia| Z.div_mod_to_equations; lia| exact BS0| exact BRA
                | reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_check_header; cbn; lia]
            | unfold ACLIENT_LO, ACLIENT_HI, AMALLOC_PC; lia
            | rewrite Hspa; lia
            | rewrite unsigned_lit by lia; unfold traces_check_header, traces_pcap_check_header in TR; destruct TR as (_ & _ & _ & _ & _ & T6 & _); exact T6
            | exact RSTK ] ]. }
    intros r s2' RNG2 ms' PO. cbv beta in PO. destruct PO as (FP2 & av & m6 & E & OF6 & MI6 & ST6 & AG6 & PO).
    destruct r as [qb|]; [|destruct PO]. destruct PO as (B & bjunk & -> & G6 & BUF).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 557912)) with (Z_to_bv 64 557912) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    cbn [app] in AG6.
    (* [comment removed for export] *)
    repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
    pose proof (pblk_ok_fp_le _ _ _ _ _ _ _ FP2 PBK) as PBK2.
    lazymatch type of AG6 with agrees_on _ ?m5 _ =>
      assert (KST : forall A cs, rw_cells asegs m5 A cs -> (SPA <= A)%Z -> rw_cells asegs m6 A cs)
        by (intros A cs HC HA; eapply agrees_rw_cells; [exact AG6| exact HC|]; intros a Ha; left; lia);
      assert (KFR : forall A cs, rw_cells asegs m5 A cs -> (Fb <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fb + 128)%Z -> rw_cells asegs m6 A cs)
        by (intros A cs HC H1 H3; eapply agrees_rw_cells; [exact AG6| exact HC|]; intros a Ha;
            right; right; left; apply in_frames_In; exists (FF_CHECK_HEADER, Fb, 128%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]);
      assert (KOB : forall A n cs, rw_cells asegs m5 A cs -> clocA FL CL A n -> Z.of_nat (cells_size cs) = n -> rw_cells asegs m6 A cs)
        by (intros A n cs HC LOC HSz; eapply agrees_rw_cells; [exact AG6| exact HC|]; intros a Ha;
            eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ LOC ICL IFL)| lia])
    end.
    apply KST in FR; [|lia]. apply KST in FRA1; [|lia].
    apply (agrees_rw_cells _ _ _ _ _ AG6) in CELLS;
      [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; right; left; apply in_block_app; right; apply in_block_In; exists (q, P, PCAP_SF_TOTAL);
        split; [left; reflexivity| cbn [cb_addr cb_size fst snd]; unfold PCAP_SF_TOTAL; lia]].
    apply (agrees_stk _ _ _ _ _ AG6) in STG; [|intros a Ha; left; lia].
    apply KFR in FRC; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG6) in SHC;
      [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; right; right; right; apply in_frame_sh_In; exists (FF_CHECK_HEADER, Fb, 128%Z);
        split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 128 3) with 16%Z; lia]].
    apply (KOB _ 4%Z) in HE; [|exact (proj1 OERR)|reflexivity].
    apply (KOB _ 256%Z) in HEB; [|exact (proj1 OEB)|reflexivity].
    apply (KOB _ 4%Z) in MGc; [|exact (proj1 OMG)|reflexivity].
    clear KST KFR KOB.
    (* [comment removed for export] *)
    assert (G6' : GIOA L RNG2 s2' (CL ++ [(q, P, PCAP_SF_TOTAL); (qb, B, BS)]) FB ((FF_CHECK_HEADER, Fb, 128%Z) :: FL) m6).
    { eapply GPL; [exact G6|]. replace (CL ++ [(q, P, PCAP_SF_TOTAL); (qb, B, BS)]) with ((CL ++ [(q, P, PCAP_SF_TOTAL)]) ++ [(qb, B, BS)])
        by (rewrite <- app_assoc; reflexivity). apply Permutation.Permutation_cons_append. }
    assert (HinP6 : In (q, P, PCAP_SF_TOTAL) ((CL ++ [(q, P, PCAP_SF_TOTAL); (qb, B, BS)]) ++ FB))
      by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (HinB6 : In (qb, B, BS) ((CL ++ [(q, P, PCAP_SF_TOTAL); (qb, B, BS)]) ++ FB))
      by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G6' HinP6) as (_ & _ & PUNP6 & _).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G6' HinB6) as ((_ & _ & BTOP & _) & B0 & _).
    cbn [cb_addr cb_size fst snd] in PUNP6, BTOP, B0. unfold PCAP_SF_TOTAL in PUNP6.
    pose proof (GOTL _ _ _ _ _ _ _ G6') as GOT6. unfold GOT_PCAP_ADDR in GOT6.
    assert (BR : (0 < B < 2^64)%Z) by (atop_facts; lia).
    assert (APB : exists k, (0 <= k <= 1 /\ P + 664 <= B + k * 18446744073709551616 /\ B + BS <= P + (1 - k) * 18446744073709551616)%Z).
    { pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G6') as BA.
      apply blocks_apart_app_inv in BA as (BA & _ & _). apply blocks_apart_app_inv in BA as (_ & BA & _).
      cbn [blocks_apart] in BA. destruct BA as (F1 & _). pose proof (Forall_inv F1) as A12.
      unfold apart, cb_addr, cb_size, PCAP_SF_TOTAL in A12; cbn [fst snd] in A12. atop_facts.
      destruct A12 as [D|D]; [exists 0%Z | exists 1%Z]; lia. }
    destruct APB as (kPB & kPBr & kPB1 & kPB2).
    pose proof (munch_refl [(P, P + 664)]%Z m6) as MU6. pose proof (wmono_refl asegs m6) as WM6.
    (* [comment removed for export] *)
    apply implMG_from_evtF.
    call fill_segE; [seg_side1 .. | ]; [lia .. | ]. open_pcells.
    lazymatch goal with HH : rw_cells asegs _ P _ |- _ => rename HH into CELLS7 end.
    (* [comment removed for export] *)
    assert (FW7 : Forall (own_ivA [(FF_CHECK_HEADER, Fb, 128%Z)] [(q, P, PCAP_SF_TOTAL); (qb, B, BS)] (bv_unsigned sp)) [(P, P + 664)]%Z)
      by (unfold PCAP_SF_TOTAL; own_ivs).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m7 _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ m7 _ [] _ FW7 (Forall_nil _) G6' MU6 WM6 ltac:(lia)) as [G7 AG7];
      assert (AGm7 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m7)
        by (eapply agrees_on_trans; [exact AGm5|]; eapply agrees_on_trans;
            [ eapply (keeps_callee0 (CL ++ [(q, P, PCAP_SF_TOTAL)]) (FF_CHECK_HEADER, Fb, 128%Z) FL _ _ CL (bv_unsigned sp) SPA); [exact ICL| lia| exact AG6]
            | eapply agrees_on_weaken; [exact AG7|]; intros a (K & _); split; [exact K| exact I] ])
    end.
    apply evtF_done. subst POSTQ.
    pose proof (s32_range (Z.land (le4val l0 l1 l2 l3) 4294901760)) as EXR. fold EXT in EXR.
    lazymatch goal with |- implMG _ (fo_ret _ _ _ (CH_Ok ?pp)) _ _ (MS _ _ _ _ _ ?m7 _) =>
      eapply (chk_exit FO GIOA TP fflagA GL FRET) with (mm := m7) (PB := [(q, P, PCAP_SF_TOTAL); (qb, B, BS)]) (r := CH_Ok pp)
             (fcs := [CB 8 pre; C4 (Z_to_bv 64 (mi + (2^64 - 2^32))); C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid;
                      C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3)); CB 64 post]);
        [ exact CTX | | exact FRA1 | reflexivity | exact FRC | reflexivity | exact HE | ] end.
    - unfold chk_inv, chk_shadow. split; [eapply fp_le_trans; [exact FP| exact FP2]|]. split; [exact G7|]. split; [congruence|].
      repeat (split; [assumption|]). assumption.
    - cbn [chk_result]. exists P. split; [reflexivity|]. split; [| split; [reflexivity| exists ej; exact HEB]].
      exists z8, z8, z8. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists B, 0%Z, blank_junk, [], bjunk.
      destruct (rw_cells_cut _ _ _ 33 CELLS7) as [CP CQ]. cbn [firstn skipn cells_size csize Nat.add] in CP, CQ.
      split; [unfold pcap_blocks, psize, is_ng; cbn [pc_priv pc_self pc_buffer pc_bufalloc]; reflexivity|].
      split. { unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, PK, blank_junk.
               cbn [app pj_read_op pj_fd pj_a pj_b pj_c pj_d pj_e pj_f pj_g pj_h pj_breakloop pk_next_pcap pk_cleanup_sf
                    pc_priv pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
                    pc_tstamp_precision pc_header h_sec h_usec h_caplen h_len hdr0].
               exact CP. }
      split. { unfold priv_cells, PCAP_PRIV_OFF. cbn [pc_priv sf_cells sf_hdrsize sf_lengths_swapped sf_scale_type].
               replace (P + 648)%Z with (P + Z.of_nat 648)%Z by lia. exact CQ. }
      split; [exact BUF|]. split; [reflexivity|]. split; [reflexivity|].
      unfold pcap_wf. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                            pc_linktype pc_linktype_ext pc_header pc_priv h_caplen h_len hdr0 sf_hdrsize length Z.of_nat].
      unfold INT_MAX. repeat split; try lia.
  Qed.
  End Sz1.
  #[using="GL FRET GPL GOTL LT2DLT ADJSNAP MALLOC"] Lemma chk_fill : ltac:(let t := eval cbv delta [chk_fill__stmt] in chk_fill__stmt in exact t).
  Proof. red. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 j1 j3 pre mid post ej k0 k1 k2 q P maj min n0 n1 n2 n3 l0 l1 l2 l3 mi sw. ltac2:(SecDiet.SzSec.closeP 'chk_fill__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkFill.
End CANSEC1.
End F_sfchk_fillA.

(* [comment removed for export] *)
Module F_sfnp_scaleA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_exitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_normA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_normA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_growA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_norm2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_discA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_overA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_over2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_chkA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_bodyA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require Import UbGuardB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sassume := first [ match goal with H : ?T |- ?G => constr_eq T G; exact H end | eassumption ].
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

(* [comment removed for export] *)
Lemma div1000_magic71 : forall u, (0 <= u < 2^32)%Z -> (u * 2361183241434822607 / 2^64 / 2^7 = u / 1000)%Z.
Proof. intros u Hu. rewrite Z.div_div by lia. change (2^64 * 2^7)%Z with (2^71)%Z. Z.div_mod_to_equations. lia. Qed.
Definition usec_div1000_A__stmt : Prop := forall u, (0 <= u < 2^32)%Z ->
  (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 u) * 2361183241434822607) 64))) 7
   + Z.shiftr (Z.shiftr (bv_signed (Z_to_bv 64 u) * 2361183241434822607) 64 mod 18446744073709551616) 63 = u / 1000)%Z.
Section Sz2.
Variables u : ltac2:(SecDiet.SzSec.tyM 'usec_div1000_A__stmt "v" @u).
#[using="Type"] Lemma usec_div1000_A__body : ltac2:(SecDiet.SzSec.bodyP 'usec_div1000_A__stmt "v").
Proof.
  intros Hu.
 rewrite (signed_lit_small u) by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  assert (Q : (0 <= u * 2361183241434822607 / 2^64 < 2^30)%Z) by (Z.div_mod_to_equations; lia).
  set (q := (u * 2361183241434822607 / 2^64)%Z) in *.
  rewrite (signed_lit_small q) by lia. rewrite (Z.mod_small q) by lia.
  replace (q / 2^63)%Z with 0%Z by (symmetry; apply Z.div_small; lia). rewrite Z.add_0_r.
  subst q. apply div1000_magic71. exact Hu.
Qed.
End Sz2.
Lemma usec_div1000_A : ltac:(let t := eval cbv delta [usec_div1000_A__stmt] in usec_div1000_A__stmt in exact t).
Proof. intros u. ltac2:(SecDiet.SzSec.closeP 'usec_div1000_A__body "v"). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NpScale.
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
  Hypothesis MAXSNAP : max_snaplen_stmt.

  (* [comment removed for export] *)
  Definition np_scale__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a3 a4 a5 a6 a7 r22 r23 t3 t4 t5 t6 : word)
      (c0 c1 c4 c5 c6 c7 c8 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec capx lenx : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 c4; C8 c5; C8 c6; C8 c8; C8 c7; C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 capx); C4 (Z_to_bv 64 lenx)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= sec < 2^32)%Z -> (0 <= usec < 2^32)%Z -> (0 <= capx < 2^64)%Z -> (0 <= lenx < 2^64)%Z -> (0 < alloc)%Z ->
    implMG RNGx (np_body_model MOps (prims HO FO sites) (pv k bq bsz alloc data eb) sec usec (capx mod 2^32) (lenx mod 2^32)) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (HA + 20)) (Z_to_bv 64 (P + 660)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
               (Z_to_bv 64 (HA + 16)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb)
               r22 r23 (Z_to_bv 64 HA) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 648)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x889f4) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a3 a4 a5 a6 a7 r22 r23 t3 t4 t5 t6 c0 c1 c4 c5 c6 c7 c8 c12 c13 c14 k bq Bx bsz alloc data eb sec usec capx lenx dw : ltac2:(SecDiet.SzSec.tyM 'np_scale__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_scale__body : ltac2:(SecDiet.SzSec.bodyP 'np_scale__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP.
 intros CTX INV PC FRA HH HD Hd Rs Ru Hcx Hlx AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    clear CELLS BUF.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    assert (ROM : ro_cells asegs mm 0x10350 [C8 (Z_to_bv 64 2361183241434822607)]).
    { pose proof (ro_cells_image asegs mm 0x10350 (le8 (Z_to_bv 64 2361183241434822607)) MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite length_le8; lia)) as [WFr BYr].
      split; [cbn; repeat split| cbn [cells_bytes cbytes] in *; exact BYr]. }
    unfold np_body_model. cbn [sf_of pc_priv sf_scale_type sf_lengths_swapped pv].
    pose proof (munch_refl [(HA, HA + 24)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep. rewrite (np_sx32_small (sfscale_code (k_scl k))) by (destruct (k_scl k); cbn; lia).
    zstep. zstep.
    assert (FX : Forall (cobj_iv FL CL) [(HA, HA + 24)]%Z) by cobj_ivs.
    assert (FIN : forall (usecv : Z) (m7 : mem) (ra7 t07 t17 t27 a17 a37 a47 a57 a67 a77 t37 t47 t57 t67 : word),
      munch [(HA, HA + 24)]%Z mm m7 -> wmono asegs mm m7 -> mem_inv asegs m7 ->
      stk asegs m7 lo SPA -> stk asegs m7 (SPA + 120) (bv_unsigned sp + -104) ->
      rw_cells asegs m7 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs m7 Fb [C8 k0; C8 k1; C8 k2; CB (Z.to_nat 8160) fj; C8 (Z_to_bv 64 (fflagA L FF_NEXT_PACKET Fb))] ->
      rw_cells asegs m7 (Z.shiftr Fb 3 + 2147450880) np_shadow -> rw_cells asegs m7 (Z.shiftr Fb 3 + 2147450892) [CB 512 dsh] ->
      rw_cells asegs m7 SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 c4; C8 c5; C8 c6; C8 c8; C8 c7; C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                             C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
      rw_cells asegs m7 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usecv); C4 (Z_to_bv 64 capx); C4 (Z_to_bv 64 lenx)] ->
      rw_cells asegs m7 DA [CB 8 dwj] ->
      implMG RNGx (let '(caplen, len) := match k_lsw k with
                                          | NOT_SWAPPED => ((capx mod 2^32)%Z, (lenx mod 2^32)%Z)
                                          | MAYBE_SWAPPED => if (capx mod 2^32 <=? lenx mod 2^32)%Z then ((capx mod 2^32)%Z, (lenx mod 2^32)%Z) else ((lenx mod 2^32)%Z, (capx mod 2^32)%Z)
                                          | SWAPPED => ((lenx mod 2^32)%Z, (capx mod 2^32)%Z)
                                          end in
                   np_tail MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (mkHdr sec usecv caplen len) caplen len sec usecv) sx POSTQ
        (MS (mkR ra7 (Z_to_bv 64 SPA) gp tp t07 t17 t27 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (HA + 20)) a17 (Z_to_bv 64 0) a37 a47 a57 a67 a77
                 (Z_to_bv 64 (HA + 16)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb)
                 r22 r23 (Z_to_bv 64 HA) (Z_to_bv 64 2147450880)
                 (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 648)) t37 t47 t57 t67)
            F (Z_to_bv 64 0x88a80) fc None m7 (seg_rom asegs))).
    { intros usecv m7 ra7 t07 t17 t27 a17 a37 a47 a57 a67 a77 t37 t47 t57 t67 MU7 WM7 MI7 ST7 STG7 FR7 FRC7 SHC7 SHD7 FRA7 HH7 HD7.
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m7 [] _ (bv_unsigned sp) (Forall_nil _) FX G MU7 WM7 ltac:(lia)) as [G7 AG7].
      assert (PC7 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m7)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU7| exact WM7|]; intros a _ Ha; exact Ha| | exact PC];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ [] _ (bv_unsigned sp) (Forall_nil _) FX G a Ha)).
      subst POSTQ.
      eapply (np_lsw HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP) with (dsh := dsh) (dw := CB 8 dwj);
        [ exact CTX | | exact PC7 | exact FRA7 | exact HH7 | exact HD7 | reflexivity | exact Hcx | exact Hlx | exact AL0 ].
      unfold np_inv0. split; [exact FP|]. split; [exact G7|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG7|]. intros a (K & (QN & _)). split; [exact K|]. split; [exact QN| exact I]. }
      split; [exists k0, k1, k2, fj; assumption|]. split; assumption. }
    destruct (k_scl k) eqn:ESCL; cbn [sfscale_code].
    - (* [comment removed for export] *)
      if_false. zstep. zstep. if_true.
      apply evtF_done. eapply FIN; sassume.
    - (* [comment removed for export] *)
      if_false. zstep. zstep. if_false.
      zstep. if_false.
      zstep.
      ck0 HAUNP; ck_go.
      zstep. zstep. zstep. zstep. zstep.
      rewrite (signed_lit_small usec) by lia. rewrite (signed_lit_small (usec * 1000)) by lia.
      replace (Z.shiftr (usec * 1000) 64) with 0%Z by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
      replace (Z.shiftr (usec * 1000) 63) with 0%Z by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
      zstep. if_false.
      ck0_at HAUNP (HA + 8)%Z; ck_go.
      zstep. zstep.
      apply evtF_done. eapply FIN; sassume.
    - (* [comment removed for export] *)
      if_true.
      zstep. if_false.
      zstep.
      ck0 HAUNP; ck_go.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite (usec_div1000_A usec) by lia.
      zstep.
      apply evtF_done. eapply FIN; sassume.
  Qed.
  End Sz3.
  Lemma np_scale : ltac:(let t := eval cbv delta [np_scale__stmt] in np_scale__stmt in exact t).
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a3 a4 a5 a6 a7 r22 r23 t3 t4 t5 t6 c0 c1 c4 c5 c6 c7 c8 c12 c13 c14 k bq Bx bsz alloc data eb sec usec capx lenx dw. ltac2:(SecDiet.SzSec.closeP 'np_scale__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpScale.
End CANSEC1.
End F_sfnp_scaleA.

(* [comment removed for export] *)
Module SfAuxB.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma fmt_errmsg_length : forall f args e, (length (fmt_errmsg f args e) <= 255)%nat.
Proof.
  intros f args e. unfold fmt_errmsg, snprintf, snprintf_out, PCAP_ERRBUF_SIZE, zlength.
  set (mm := firstn (Z.to_nat (256 - 1)) (fmt_output (fmt f) args)).
  assert (Hm : (length mm <= 255)%nat) by (subst mm; rewrite length_firstn; apply Nat.le_min_l).
  destruct (256 <? Z.of_nat (length mm) + 3)%Z eqn:E; [exact Hm|].
  apply Z.ltb_ge in E. rewrite !length_app, length_firstn. cbn [length str String.list_ascii_of_string map].
  unfold str. cbn [String.list_ascii_of_string map length]. lia.
Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Aux.
  Context {H hptr : Type}.
  #[using="Type"] Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M (PState H hptr) B) (g : B -> Monad.M (PState H hptr) C) (s : PState H hptr) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof. intros B C f g s RNG Q ms HH. exact HH. Qed.
End Aux.
End CANSEC1.
End SfAuxB.
