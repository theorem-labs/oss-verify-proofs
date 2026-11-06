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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Fuzz_ifaceA LibcKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_fuzz_segA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac zstep_0 :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with SHH : rw_cells asegs mx _ (C1 _ :: _) |- _ =>
      let SOK := fresh "SOK" in
      pose proof (rw_cells_store_ok asegs mx _ _ 0%nat _ 1%nat SHH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK; zstep; clear SOK
    end
  end.
(* [comment removed for export] *)
Ltac seg_recell H :=
  eapply rw_cells_recell; [exact H | cbn; repeat split; reflexivity |];
  cbn [cells_bytes cbytes app repeat]; repeat (apply f_equal2; [apply bv_eq; reflexivity|]); reflexivity.

Open Scope bv_scope.
(* [comment removed for export] *)
Local Ltac nlb_hyp A :=
  repeat match goal with
  | H : rw_cells _ _ A ?cs |- _ =>
      match cs with context [C1 (Z_to_bv 8 ?z)] =>
        is_Zlit z; let z' := eval vm_compute in (Z.modulo z 256) in
        tryif constr_eq z z' then fail else
        replace (Z_to_bv 8 z) with (Z_to_bv 8 z') in H by (apply (proj2 (bv_eq _ _ _)); reflexivity)
      end
  end.
Local Ltac mem_after_store_opt ::=
  norm_lit_store_bytes;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store; try nlb_hyp A
      | _ => idtac
      end
  | _ => idtac
  end.
Local Ltac alia ::= lia.   (* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.

  (* [comment removed for export] *)
  Definition fz_seg1__stmt : Prop := forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SH : Z),
    mem_inv asegs m -> (0 <= SH)%Z -> (SH + 584 < 2^64)%Z -> rng RNG SH 44 ->
    rw_cells asegs m SH [CB 44 (repeat (Z_to_bv 8 0) 44)] ->
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 18446744073709551601) a4 a5 a6 a7 (Z_to_bv 64 18446744073709551602) (Z_to_bv 64 SH) s4 s5 s6 (Z_to_bv 64 18446744073709551608) s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x84760) fc None m' (seg_rom asegs)
        /\ munch [(SH, SH + 44)%Z] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' SH [CB 44 (repeat (Z_to_bv 8 0xf1) 4 ++ repeat (Z_to_bv 8 0xf8) 32 ++ repeat (Z_to_bv 8 0xf2) 8)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 18446744073709551601) a4 a5 a6 a7 (Z_to_bv 64 18446744073709551602) (Z_to_bv 64 SH) s4 s5 s6 (Z_to_bv 64 18446744073709551608) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x846b0) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SH : ltac2:(SecDiet.SzSec.tyM 'fz_seg1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  #[using="Type"] Lemma fz_seg1__body : ltac2:(SecDiet.SzSec.bodyP 'fz_seg1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI SH0 SHT RSH CA.
    pose proof (munch_refl [(SH, SH + 44)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    apply sh_zero_cells in CA. cbn [repeat] in CA.
    do 4 zstep. zstep_0. do 3 zstep.
    do 36 zstep.
    apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    seg_recell CA.
  Qed.
  End Sz1.
  #[using="Type"] Lemma fz_seg1 : ltac:(let t := eval cbv delta [fz_seg1__stmt] in fz_seg1__stmt in exact t).
  Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SH. ltac2:(SecDiet.SzSec.closeP 'fz_seg1__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition fz_seg2__stmt : Prop := forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SH : Z),
    mem_inv asegs m -> (0 <= SH)%Z -> (SH + 584 < 2^64)%Z -> rng RNG (SH + 556) 28 ->
    rw_cells asegs m (SH + 556) [CB 28 (repeat (Z_to_bv 8 0) 28)] ->
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 18446744073709551602) (Z_to_bv 64 SH) s4 s5 s6 (Z_to_bv 64 18446744073709551608) s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x847d0) fc None m' (seg_rom asegs)
        /\ munch [(SH + 556, SH + 584)%Z] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (SH + 556) [CB 28 (repeat (Z_to_bv 8 0xf2) 16 ++ [Z_to_bv 8 0xf8; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2;
                                                      Z_to_bv 8 0xf8; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2] ++ repeat (Z_to_bv 8 0) 4)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 18446744073709551602) (Z_to_bv 64 SH) s4 s5 s6 (Z_to_bv 64 18446744073709551608) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x84770) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SH : ltac2:(SecDiet.SzSec.tyM 'fz_seg2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  #[using="Type"] Lemma fz_seg2__body : ltac2:(SecDiet.SzSec.bodyP 'fz_seg2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI SH0 SHT RSH CC.
    pose proof (munch_refl [(SH + 556, SH + 584)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    apply sh_zero_cells in CC. cbn [repeat] in CC.
    do 4 zstep. zstep_0. do 3 zstep.
    do 16 zstep.
    apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    seg_recell CC.
  Qed.
  End Sz2.
  #[using="Type"] Lemma fz_seg2 : ltac:(let t := eval cbv delta [fz_seg2__stmt] in fz_seg2__stmt in exact t).
  Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SH. ltac2:(SecDiet.SzSec.closeP 'fz_seg2__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fz_seg3__stmt : Prop := forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SH : Z),
    mem_inv asegs m -> (0 <= SH)%Z -> (SH + 584 < 2^64)%Z -> rng RNG SH 44 -> rng RNG (SH + 556) 28 ->
    rw_cells asegs m SH [CB 44 (repeat (Z_to_bv 8 0xf1) 4 ++ repeat (Z_to_bv 8 0xf8) 32 ++ repeat (Z_to_bv 8 0xf2) 8)] ->
    rw_cells asegs m (SH + 556) [CB 28 (repeat (Z_to_bv 8 0xf2) 16 ++ [Z_to_bv 8 0xf8; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2;
                                             Z_to_bv 8 0xf8; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2] ++ repeat (Z_to_bv 8 0) 4)] ->
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 18446744073709551603) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 18446744073709551602) (Z_to_bv 64 SH) s4 s5 s6 (Z_to_bv 64 18446744073709551608) s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x84864) fc None m' (seg_rom asegs)
        /\ munch [(SH, SH + 44); (SH + 556, SH + 584)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' SH [CB 44 (repeat (Z_to_bv 8 0xf1) 4 ++ repeat (Z_to_bv 8 0) 32 ++ repeat (Z_to_bv 8 0xf2) 8)]
        /\ rw_cells asegs m' (SH + 556) [CB 28 (repeat (Z_to_bv 8 0xf2) 16 ++ [Z_to_bv 8 0xf8; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2;
                                                     Z_to_bv 8 0xf8; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2;
                                                     Z_to_bv 8 0xf8; Z_to_bv 8 0xf8; Z_to_bv 8 0xf3; Z_to_bv 8 0xf3])])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 18446744073709551602) (Z_to_bv 64 SH) s4 s5 s6 (Z_to_bv 64 18446744073709551608) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x847d0) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SH : ltac2:(SecDiet.SzSec.tyM 'fz_seg3__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  #[using="Type"] Lemma fz_seg3__body : ltac2:(SecDiet.SzSec.bodyP 'fz_seg3__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI SH0 SHT RSA RSC CA CC.
    pose proof (munch_refl [(SH, SH + 44); (SH + 556, SH + 584)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    eapply (rw_cells_recell _ _ _ (repeat (C1 (Z_to_bv 8 0xf1)) 4 ++ repeat (C1 (Z_to_bv 8 0xf8)) 32 ++ repeat (C1 (Z_to_bv 8 0xf2)) 8)) in CA;
      [| cbn; repeat split; reflexivity | reflexivity]. cbn [repeat app] in CA.
    eapply (rw_cells_recell _ _ _ (repeat (C1 (Z_to_bv 8 0xf2)) 16 ++ [C1 (Z_to_bv 8 0xf8); C1 (Z_to_bv 8 0xf2); C1 (Z_to_bv 8 0xf2); C1 (Z_to_bv 8 0xf2);
                                      C1 (Z_to_bv 8 0xf8); C1 (Z_to_bv 8 0xf2); C1 (Z_to_bv 8 0xf2); C1 (Z_to_bv 8 0xf2)] ++ repeat (C1 (Z_to_bv 8 0)) 4)) in CC;
      [| cbn; repeat split; reflexivity | reflexivity]. cbn [repeat app] in CC.
    zstep. neg_lits.
    do 28 zstep.
    do 4 zstep.
    do 4 zstep.
    apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [seg_recell CA| seg_recell CC].
  Qed.
  End Sz3.
  #[using="Type"] Lemma fz_seg3 : ltac:(let t := eval cbv delta [fz_seg3__stmt] in fz_seg3__stmt in exact t).
  Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SH. ltac2:(SecDiet.SzSec.closeP 'fz_seg3__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fz_seg4__stmt : Prop := forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SH : Z),
    mem_inv asegs m -> (0 <= SH)%Z -> (SH + 584 < 2^64)%Z -> rng RNG (SH + 556) 28 ->
    rw_cells asegs m (SH + 556) [CB 28 (repeat (Z_to_bv 8 0xf2) 16 ++ [Z_to_bv 8 0xf8; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2;
                                             Z_to_bv 8 0xf8; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2;
                                             Z_to_bv 8 0xf8; Z_to_bv 8 0xf8; Z_to_bv 8 0xf3; Z_to_bv 8 0xf3])] ->
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 4) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 SH) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x84894) fc None m' (seg_rom asegs)
        /\ munch [(SH + 556, SH + 584)%Z] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (SH + 556) [CB 28 (repeat (Z_to_bv 8 0xf2) 16 ++ [Z_to_bv 8 0; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2;
                                                     Z_to_bv 8 0; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2;
                                                     Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0xf3; Z_to_bv 8 0xf3])])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 SH) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x84880) fc None m (seg_rom asegs)).
  Section Sz4.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SH : ltac2:(SecDiet.SzSec.tyM 'fz_seg4__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  #[using="Type"] Lemma fz_seg4__body : ltac2:(SecDiet.SzSec.bodyP 'fz_seg4__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI SH0 SHT RSC CC.
    pose proof (munch_refl [(SH + 556, SH + 584)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    eapply (rw_cells_recell _ _ _ (repeat (C1 (Z_to_bv 8 0xf2)) 16 ++ [C1 (Z_to_bv 8 0xf8); C1 (Z_to_bv 8 0xf2); C1 (Z_to_bv 8 0xf2); C1 (Z_to_bv 8 0xf2);
                                      C1 (Z_to_bv 8 0xf8); C1 (Z_to_bv 8 0xf2); C1 (Z_to_bv 8 0xf2); C1 (Z_to_bv 8 0xf2);
                                      C1 (Z_to_bv 8 0xf8); C1 (Z_to_bv 8 0xf8); C1 (Z_to_bv 8 0xf3); C1 (Z_to_bv 8 0xf3)])) in CC;
      [| cbn; repeat split; reflexivity | reflexivity]. cbn [repeat app] in CC.
    zstep.
    do 4 zstep.
    apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    seg_recell CC.
  Qed.
  End Sz4.
  #[using="Type"] Lemma fz_seg4 : ltac:(let t := eval cbv delta [fz_seg4__stmt] in fz_seg4__stmt in exact t).
  Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SH. ltac2:(SecDiet.SzSec.closeP 'fz_seg4__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac zstep_0 :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with SHH : rw_cells asegs mx _ (C1 _ :: _) |- _ =>
      let SOK := fresh "SOK" in
      pose proof (rw_cells_store_ok asegs mx _ _ 0%nat _ 1%nat SHH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK; zstep; clear SOK
    end
  end.
(* [comment removed for export] *)
Ltac seg_recell H :=
  eapply rw_cells_recell; [exact H | cbn; repeat split; reflexivity |];
  cbn [cells_bytes cbytes app repeat]; repeat (apply f_equal2; [apply bv_eq; reflexivity|]); reflexivity.

Open Scope bv_scope.
(* [comment removed for export] *)
Local Ltac nlb_hyp A :=
  repeat match goal with
  | H : rw_cells _ _ A ?cs |- _ =>
      match cs with context [C1 (Z_to_bv 8 ?z)] =>
        is_Zlit z; let z' := eval vm_compute in (Z.modulo z 256) in
        tryif constr_eq z z' then fail else
        replace (Z_to_bv 8 z) with (Z_to_bv 8 z') in H by (apply (proj2 (bv_eq _ _ _)); reflexivity)
      end
  end.
Local Ltac mem_after_store_opt ::=
  norm_lit_store_bytes;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store; try nlb_hyp A
      | _ => idtac
      end
  | _ => idtac
  end.
Local Ltac alia ::= lia.   (* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.

  (* [comment removed for export] *)
  Definition fz_seg1__stmt : Prop := forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SH : Z),
    mem_inv asegs m -> (0 <= SH)%Z -> (SH + 584 < 2^64)%Z -> rng RNG SH 44 ->
    rw_cells asegs m SH [CB 44 (repeat (Z_to_bv 8 0) 44)] ->
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 18446744073709551601) a4 a5 a6 a7 (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 SH) s4 s5 s6 (Z_to_bv 64 18446744073709551602) s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x847c8) fc None m' (seg_rom asegs)
        /\ munch [(SH, SH + 44)%Z] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' SH [CB 44 (repeat (Z_to_bv 8 0xf1) 4 ++ repeat (Z_to_bv 8 0xf8) 32 ++ repeat (Z_to_bv 8 0xf2) 8)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 18446744073709551601) a4 a5 a6 a7 (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 SH) s4 s5 s6 (Z_to_bv 64 18446744073709551602) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x84718) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SH : ltac2:(SecDiet.SzSec.tyM 'fz_seg1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  #[using="Type"] Lemma fz_seg1__body : ltac2:(SecDiet.SzSec.bodyP 'fz_seg1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI SH0 SHT RSH CA.
    pose proof (munch_refl [(SH, SH + 44)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    apply sh_zero_cells in CA. cbn [repeat] in CA.
    do 4 zstep. zstep_0. do 3 zstep.
    do 36 zstep.
    apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    seg_recell CA.
  Qed.
  End Sz1.
  #[using="Type"] Lemma fz_seg1 : ltac:(let t := eval cbv delta [fz_seg1__stmt] in fz_seg1__stmt in exact t).
  Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SH. ltac2:(SecDiet.SzSec.closeP 'fz_seg1__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition fz_seg2__stmt : Prop := forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SH : Z),
    mem_inv asegs m -> (0 <= SH)%Z -> (SH + 584 < 2^64)%Z -> rng RNG (SH + 556) 28 ->
    rw_cells asegs m (SH + 556) [CB 28 (repeat (Z_to_bv 8 0) 28)] ->
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 SH) s4 s5 s6 (Z_to_bv 64 18446744073709551602) s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x84838) fc None m' (seg_rom asegs)
        /\ munch [(SH + 556, SH + 584)%Z] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (SH + 556) [CB 28 (repeat (Z_to_bv 8 0xf2) 16 ++ [Z_to_bv 8 0xf8; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2;
                                                      Z_to_bv 8 0xf8; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2] ++ repeat (Z_to_bv 8 0) 4)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 SH) s4 s5 s6 (Z_to_bv 64 18446744073709551602) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x847d8) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SH : ltac2:(SecDiet.SzSec.tyM 'fz_seg2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  #[using="Type"] Lemma fz_seg2__body : ltac2:(SecDiet.SzSec.bodyP 'fz_seg2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI SH0 SHT RSH CC.
    pose proof (munch_refl [(SH + 556, SH + 584)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    apply sh_zero_cells in CC. cbn [repeat] in CC.
    do 4 zstep. zstep_0. do 3 zstep.
    do 16 zstep.
    apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    seg_recell CC.
  Qed.
  End Sz2.
  #[using="Type"] Lemma fz_seg2 : ltac:(let t := eval cbv delta [fz_seg2__stmt] in fz_seg2__stmt in exact t).
  Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SH. ltac2:(SecDiet.SzSec.closeP 'fz_seg2__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fz_seg3__stmt : Prop := forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SH : Z),
    mem_inv asegs m -> (0 <= SH)%Z -> (SH + 584 < 2^64)%Z -> rng RNG SH 44 -> rng RNG (SH + 556) 28 ->
    rw_cells asegs m SH [CB 44 (repeat (Z_to_bv 8 0xf1) 4 ++ repeat (Z_to_bv 8 0xf8) 32 ++ repeat (Z_to_bv 8 0xf2) 8)] ->
    rw_cells asegs m (SH + 556) [CB 28 (repeat (Z_to_bv 8 0xf2) 16 ++ [Z_to_bv 8 0xf8; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2;
                                             Z_to_bv 8 0xf8; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2] ++ repeat (Z_to_bv 8 0) 4)] ->
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 18446744073709551603) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 SH) s4 s5 s6 (Z_to_bv 64 18446744073709551602) s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x848cc) fc None m' (seg_rom asegs)
        /\ munch [(SH, SH + 44); (SH + 556, SH + 584)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' SH [CB 44 (repeat (Z_to_bv 8 0xf1) 4 ++ repeat (Z_to_bv 8 0) 32 ++ repeat (Z_to_bv 8 0xf2) 8)]
        /\ rw_cells asegs m' (SH + 556) [CB 28 (repeat (Z_to_bv 8 0xf2) 16 ++ [Z_to_bv 8 0xf8; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2;
                                                     Z_to_bv 8 0xf8; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2;
                                                     Z_to_bv 8 0xf8; Z_to_bv 8 0xf8; Z_to_bv 8 0xf3; Z_to_bv 8 0xf3])])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 SH) s4 s5 s6 (Z_to_bv 64 18446744073709551602) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x84838) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SH : ltac2:(SecDiet.SzSec.tyM 'fz_seg3__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  #[using="Type"] Lemma fz_seg3__body : ltac2:(SecDiet.SzSec.bodyP 'fz_seg3__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI SH0 SHT RSA RSC CA CC.
    pose proof (munch_refl [(SH, SH + 44); (SH + 556, SH + 584)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    eapply (rw_cells_recell _ _ _ (repeat (C1 (Z_to_bv 8 0xf1)) 4 ++ repeat (C1 (Z_to_bv 8 0xf8)) 32 ++ repeat (C1 (Z_to_bv 8 0xf2)) 8)) in CA;
      [| cbn; repeat split; reflexivity | reflexivity]. cbn [repeat app] in CA.
    eapply (rw_cells_recell _ _ _ (repeat (C1 (Z_to_bv 8 0xf2)) 16 ++ [C1 (Z_to_bv 8 0xf8); C1 (Z_to_bv 8 0xf2); C1 (Z_to_bv 8 0xf2); C1 (Z_to_bv 8 0xf2);
                                      C1 (Z_to_bv 8 0xf8); C1 (Z_to_bv 8 0xf2); C1 (Z_to_bv 8 0xf2); C1 (Z_to_bv 8 0xf2)] ++ repeat (C1 (Z_to_bv 8 0)) 4)) in CC;
      [| cbn; repeat split; reflexivity | reflexivity]. cbn [repeat app] in CC.
    zstep. neg_lits.
    do 28 zstep.
    do 4 zstep.
    do 4 zstep.
    apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [seg_recell CA| seg_recell CC].
  Qed.
  End Sz3.
  #[using="Type"] Lemma fz_seg3 : ltac:(let t := eval cbv delta [fz_seg3__stmt] in fz_seg3__stmt in exact t).
  Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SH. ltac2:(SecDiet.SzSec.closeP 'fz_seg3__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fz_seg4__stmt : Prop := forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SH : Z),
    mem_inv asegs m -> (0 <= SH)%Z -> (SH + 584 < 2^64)%Z -> rng RNG (SH + 556) 28 ->
    rw_cells asegs m (SH + 556) [CB 28 (repeat (Z_to_bv 8 0xf2) 16 ++ [Z_to_bv 8 0xf8; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2;
                                             Z_to_bv 8 0xf8; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2;
                                             Z_to_bv 8 0xf8; Z_to_bv 8 0xf8; Z_to_bv 8 0xf3; Z_to_bv 8 0xf3])] ->
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 4) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 SH) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x848fc) fc None m' (seg_rom asegs)
        /\ munch [(SH + 556, SH + 584)%Z] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (SH + 556) [CB 28 (repeat (Z_to_bv 8 0xf2) 16 ++ [Z_to_bv 8 0; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2;
                                                     Z_to_bv 8 0; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2;
                                                     Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0xf3; Z_to_bv 8 0xf3])])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 SH) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x848e8) fc None m (seg_rom asegs)).
  Section Sz4.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SH : ltac2:(SecDiet.SzSec.tyM 'fz_seg4__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  #[using="Type"] Lemma fz_seg4__body : ltac2:(SecDiet.SzSec.bodyP 'fz_seg4__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI SH0 SHT RSC CC.
    pose proof (munch_refl [(SH + 556, SH + 584)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    eapply (rw_cells_recell _ _ _ (repeat (C1 (Z_to_bv 8 0xf2)) 16 ++ [C1 (Z_to_bv 8 0xf8); C1 (Z_to_bv 8 0xf2); C1 (Z_to_bv 8 0xf2); C1 (Z_to_bv 8 0xf2);
                                      C1 (Z_to_bv 8 0xf8); C1 (Z_to_bv 8 0xf2); C1 (Z_to_bv 8 0xf2); C1 (Z_to_bv 8 0xf2);
                                      C1 (Z_to_bv 8 0xf8); C1 (Z_to_bv 8 0xf8); C1 (Z_to_bv 8 0xf3); C1 (Z_to_bv 8 0xf3)])) in CC;
      [| cbn; repeat split; reflexivity | reflexivity]. cbn [repeat app] in CC.
    zstep.
    do 4 zstep.
    apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    seg_recell CC.
  Qed.
  End Sz4.
  #[using="Type"] Lemma fz_seg4 : ltac:(let t := eval cbv delta [fz_seg4__stmt] in fz_seg4__stmt in exact t).
  Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SH. ltac2:(SecDiet.SzSec.closeP 'fz_seg4__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End CANSEC1.
End TwB.
End F_fuzz_segA.

(* [comment removed for export] *)
Module F_sfnp_epiA.
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
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NpEpi.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.

  Definition np_epi__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CLc PB FB : list (@cblock hptr)) (FL : list fblock) (lo SPA Fb : Z) (m : mem)
      (ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 av r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 : word)
      (jS : list byte) (k0 : word) (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : byte)
      (A : Type) (x : A),
    (bv_unsigned sp - 240 <= SPA <= bv_unsigned sp - 224)%Z -> (SPA mod 32 = 0)%Z -> (ATOP + 4096 <= lo)%Z -> (lo + FAKE_STACK <= SPA)%Z ->
    (bv_unsigned sp + 16 < al_top L)%Z -> (al_top L <= 2^47)%Z -> tp = Z_to_bv 64 ATP ->
    GIOA L RNG s (CLc ++ PB) FB ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) m -> mem_inv asegs m ->
    stk asegs m lo SPA -> stk asegs m (SPA + 120) (bv_unsigned sp + -104) ->
    rw_cells asegs m SPA [CB 120 jS] ->
    rw_cells asegs m (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m Fb [C8 k0] ->
    rw_cells asegs m (Fb + 8184) [C8 (Z_to_bv 64 (fflagA L FF_NEXT_PACKET Fb))] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9; C1 b10; C1 b11] ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_atls RNG ->
    implMG RNG (fo_ret FO _ FF_NEXT_PACKET x) s
      (fun r s' RNG' ms' => r = x /\ RNG' = RNG /\ exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 av a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m' /\ agrees_on (fun a => in_block (CLc ++ PB) a) m m'
           /\ GIOA L RNG s' (CLc ++ PB) FB FL m' /\ ps_outfile s' = ps_outfile s)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp r9 a0 a1 a2 a3 a4 a5 a6 a7
               av (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r20 (Z_to_bv 64 Fb) r22 r23 r24 (Z_to_bv 64 Fb) r26 r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88aec) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CLc PB FB FL lo SPA Fb m ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 av r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 jS k0 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 A x : ltac2:(SecDiet.SzSec.tyM 'np_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL FFREE7"] Lemma np_epi__body : ltac2:(SecDiet.SzSec.bodyP 'np_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros SPAB SPA32 LO LOS SPT TOP47 TPE G MI ST STG FRA FR FRC0 FRL SHC RSTK RIMG RISH RTLS.
    unfold FAKE_STACK in LOS.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. pose proof (Forall_inv FAll) as (FBAND & FTOP & F64 & _ & FRNG & FSRNG & _ & _).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64, FRNG, FSRNG. clear FAll. change (Z.shiftr 8192 3) with 1024%Z in FSRNG.
    pose proof (ablk_lin _ _ FBAND) as (_ & Fb0 & _ & _). band_ind FBAND bF.
    assert (SHQ : (Fb = 8 * Z.shiftr Fb 3)%Z) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(Fb, Fb + 8192); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z) by own_ivs.
    pose proof (munch_refl [(Fb, Fb + 8192); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    zstep. neg_lits.
    do 3 zstep.
    do 2 zstep.
    zstep.
    zstep. if_false_by (eqz_false Fb ltac:(lia)).
    do 3 zstep.
    zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ (Forall_impl _ (own_ivA_PB _ PB _) FW) (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
      assert (AGP5 : agrees_on (fun a => in_block (CLc ++ PB) a) m mm)
        by (eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha;
            exact (pb_outside _ _ _ GL _ _ _ [] (CLc ++ PB) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a Ha))
    end.
    clear MU WM.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FFREE7 _ spa) with (lo := lo) (req := 4320%Z).
    { split; [exact G5|]. rewrite Hspa. split; [exact ST|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [Z.div_mod_to_equations; lia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { reflexivity. }
    { change (ff_size FF_NEXT_PACKET) with 8192%Z. replace (Fb + 8192 - 8)%Z with (Fb + 8184)%Z by lia. exact FRL. }
    intros s6' m6 a0' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G6 OF6 LC6 TL6 MI6 ST6 AG6.
    rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 559900)) with (Z_to_bv 64 559900) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG6) in FR; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG6) in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG6) in STG; [|intros a Ha; left; lia].
    clear FRNG FSRNG bF bFr bFhi bFlo bFimg SHQ FRC0 FRL SHC.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    zstep.
    do 2 zstep.
    do 15 zstep.
    release_frame FRA ST6 (SPA + 120)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST6 STG ltac:(lia)) as ST7. clear ST6 STG.
    release_frame FR ST7 (bv_unsigned sp).
    apply evtF_done. subst POSTQ. cbv beta iota.
    split; [reflexivity|]. split; [reflexivity|].
    do 14 eexists. exists m6.
    split; [reflexivity|]. split; [assumption|]. split; [exact ST7|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a K; split; [exact K| exact I]|].
             eapply agrees_on_weaken; [exact AG6|]. intros a [K|[K|[K|K]]];
               [left; lia| right; left; apply in_block_app; left; exact K| right; right; left; exact K| right; right; right; exact K]. }
    split. { eapply agrees_on_trans; [exact AGP5|]. eapply agrees_on_weaken; [exact AG6|]. intros a K. right; left; exact K. }
    split; [exact G6| exact OF6].
  Qed.
  End Sz1.
  #[using="GL FFREE7"] Lemma np_epi : ltac:(let t := eval cbv delta [np_epi__stmt] in np_epi__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CLc PB FB FL lo SPA Fb m ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 av r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 jS k0 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 A x. ltac2:(SecDiet.SzSec.closeP 'np_epi__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpEpi.
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
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NpEpi.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.

  Definition np_epi__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CLc PB FB : list (@cblock hptr)) (FL : list fblock) (lo SPA Fb : Z) (m : mem)
      (ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 av r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 : word)
      (jS : list byte) (k0 : word) (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : byte)
      (A : Type) (x : A),
    (bv_unsigned sp - 240 <= SPA <= bv_unsigned sp - 224)%Z -> (SPA mod 32 = 0)%Z -> (ATOP + 4096 <= lo)%Z -> (lo + FAKE_STACK <= SPA)%Z ->
    (bv_unsigned sp + 16 < al_top L)%Z -> (al_top L <= 2^47)%Z -> tp = Z_to_bv 64 ATP ->
    GIOA L RNG s (CLc ++ PB) FB ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) m -> mem_inv asegs m ->
    stk asegs m lo SPA -> stk asegs m (SPA + 120) (bv_unsigned sp + -104) ->
    rw_cells asegs m SPA [CB 120 jS] ->
    rw_cells asegs m (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m Fb [C8 k0] ->
    rw_cells asegs m (Fb + 8184) [C8 (Z_to_bv 64 (fflagA L FF_NEXT_PACKET Fb))] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9; C1 b10; C1 b11] ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_atls RNG ->
    implMG RNG (fo_ret FO _ FF_NEXT_PACKET x) s
      (fun r s' RNG' ms' => r = x /\ RNG' = RNG /\ exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 av a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m' /\ agrees_on (fun a => in_block (CLc ++ PB) a) m m'
           /\ GIOA L RNG s' (CLc ++ PB) FB FL m' /\ ps_outfile s' = ps_outfile s)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp r9 a0 a1 a2 a3 a4 a5 a6 a7
               av (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r20 (Z_to_bv 64 Fb) r22 r23 r24 r26 (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88d28) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CLc PB FB FL lo SPA Fb m ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 av r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 jS k0 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 A x : ltac2:(SecDiet.SzSec.tyM 'np_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL FFREE7"] Lemma np_epi__body : ltac2:(SecDiet.SzSec.bodyP 'np_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros SPAB SPA32 LO LOS SPT TOP47 TPE G MI ST STG FRA FR FRC0 FRL SHC RSTK RIMG RISH RTLS.
    unfold FAKE_STACK in LOS.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. pose proof (Forall_inv FAll) as (FBAND & FTOP & F64 & _ & FRNG & FSRNG & _ & _).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64, FRNG, FSRNG. clear FAll. change (Z.shiftr 8192 3) with 1024%Z in FSRNG.
    pose proof (ablk_lin _ _ FBAND) as (_ & Fb0 & _ & _). band_ind FBAND bF.
    assert (SHQ : (Fb = 8 * Z.shiftr Fb 3)%Z) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(Fb, Fb + 8192); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z) by own_ivs.
    pose proof (munch_refl [(Fb, Fb + 8192); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    zstep. neg_lits.
    do 3 zstep.
    do 2 zstep.
    zstep.
    zstep. if_false_by (eqz_false Fb ltac:(lia)).
    do 3 zstep.
    zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ (Forall_impl _ (own_ivA_PB _ PB _) FW) (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
      assert (AGP5 : agrees_on (fun a => in_block (CLc ++ PB) a) m mm)
        by (eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha;
            exact (pb_outside _ _ _ GL _ _ _ [] (CLc ++ PB) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a Ha))
    end.
    clear MU WM.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FFREE7 _ spa) with (lo := lo) (req := 4320%Z).
    { split; [exact G5|]. rewrite Hspa. split; [exact ST|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [Z.div_mod_to_equations; lia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { reflexivity. }
    { change (ff_size FF_NEXT_PACKET) with 8192%Z. replace (Fb + 8192 - 8)%Z with (Fb + 8184)%Z by lia. exact FRL. }
    intros s6' m6 a0' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G6 OF6 LC6 TL6 MI6 ST6 AG6.
    rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 560472)) with (Z_to_bv 64 560472) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG6) in FR; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG6) in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG6) in STG; [|intros a Ha; left; lia].
    clear FRNG FSRNG bF bFr bFhi bFlo bFimg SHQ FRC0 FRL SHC.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    zstep.
    do 2 zstep.
    do 15 zstep.
    release_frame FRA ST6 (SPA + 120)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST6 STG ltac:(lia)) as ST7. clear ST6 STG.
    release_frame FR ST7 (bv_unsigned sp).
    apply evtF_done. subst POSTQ. cbv beta iota.
    split; [reflexivity|]. split; [reflexivity|].
    do 14 eexists. exists m6.
    split; [reflexivity|]. split; [assumption|]. split; [exact ST7|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a K; split; [exact K| exact I]|].
             eapply agrees_on_weaken; [exact AG6|]. intros a [K|[K|[K|K]]];
               [left; lia| right; left; apply in_block_app; left; exact K| right; right; left; exact K| right; right; right; exact K]. }
    split. { eapply agrees_on_trans; [exact AGP5|]. eapply agrees_on_weaken; [exact AG6|]. intros a K. right; left; exact K. }
    split; [exact G6| exact OF6].
  Qed.
  End Sz1.
  #[using="GL FFREE7"] Lemma np_epi : ltac:(let t := eval cbv delta [np_epi__stmt] in np_epi__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CLc PB FB FL lo SPA Fb m ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 av r20 r22 r23 r24 r26 r27 t3 t4 t5 t6 jS k0 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 A x. ltac2:(SecDiet.SzSec.closeP 'np_epi__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpEpi.
End CANSEC1.
End TwB.
End F_sfnp_epiA.

(* [comment removed for export] *)
Module F_fuzz_exitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Open Scope bv_scope.
(* [comment removed for export] *)
Local Ltac nlb_hyp A :=
  repeat match goal with
  | H : rw_cells _ _ A ?cs |- _ =>
      match cs with context [C1 (Z_to_bv 8 ?z)] =>
        is_Zlit z; let z' := eval vm_compute in (Z.modulo z 256) in
        tryif constr_eq z z' then fail else
        replace (Z_to_bv 8 z) with (Z_to_bv 8 z') in H by (apply (proj2 (bv_eq _ _ _)); reflexivity)
      end
  end.
Local Ltac mem_after_store_opt ::=
  norm_lit_store_bytes;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store; try nlb_hyp A
      | _ => idtac
      end
  | _ => idtac
  end.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section FuzzExit.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETSHF8 : set_shadow_stmt 0x58388 0xf8.

  Definition fz_exit__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (lo SPA Fb : Z) (m : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r23 r25 t3 t4 t5 t6 : word)
      (k0 : word) (fra ca cb cc : list cell) (A : Type) (x : A),
    (bv_unsigned sp - 191 <= SPA <= bv_unsigned sp - 160)%Z -> (SPA mod 32 = 0)%Z -> (ATOP + 4096 <= lo)%Z -> (lo + 8192 <= SPA)%Z ->
    (bv_unsigned sp + 16 < al_top L)%Z -> (al_top L <= 2^47)%Z -> tp = Z_to_bv 64 ATP ->
    GIOA L RNG s CL FB [(FF_FUZZ_ONE_INPUT, Fb, 8192%Z)] m -> mem_inv asegs m ->
    stk asegs m lo SPA -> stk asegs m (SPA + 56) (bv_unsigned sp + -104) ->
    rw_cells asegs m SPA fra -> cells_size fra = 56%nat ->
    rw_cells asegs m (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m Fb [C8 k0] ->
    rw_cells asegs m (Fb + 8184) [C8 (Z_to_bv 64 (fflagA L FF_FUZZ_ONE_INPUT Fb))] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) ca -> cells_size ca = 44%nat ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450924) cb -> cells_size cb = 512%nat ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147451436) cc -> cells_size cc = 28%nat ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_atls RNG ->
    implMG RNG (fo_ret FO _ FF_FUZZ_ONE_INPUT x) s
      (fun r s' RNG' ms' => r = x /\ RNG' = RNG /\ exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (client_keeps [] CL (bv_unsigned sp)) m m'
           /\ GIOA L RNG s' CL FB [] m' /\ ps_outfile s' = ps_outfile s /\ ps_libc s' = ps_libc s /\ ps_tls s' = ps_tls s)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) r21 r22 r23 (Z_to_bv 64 Fb) r25 (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x84a9c) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb m ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r23 r25 t3 t4 t5 t6 k0 fra ca cb cc A x : ltac2:(SecDiet.SzSec.tyM 'fz_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL FFREE7 SETSHF8"] Lemma fz_exit__body : ltac2:(SecDiet.SzSec.bodyP 'fz_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros SPAB SPA32 LO LOS SPT TOP47 TPE G MI ST STG FRA FRAS FRs FK0 FLG SA SAS SB SBS SC SCS RSTK RIMG RISH RTLS.
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. pose proof (Forall_inv FAll) as (FBAND & FTOP & F64 & _ & FRNG & FSRNG & _ & _).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64, FRNG, FSRNG. clear FAll. change (Z.shiftr 8192 3) with 1024%Z in FSRNG.
    pose proof (ablk_lin _ _ FBAND) as (_ & Fb0 & _ & _). band_ind FBAND bF.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 1024 <= 0x10007fff8000
                   /\ (Fb + 8192 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 1024 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    destruct SHLO as (SH1 & SH2 & _).   (* [comment removed for export] *)
    destruct (rw_cells_forget _ _ _ _ SA) as [ja SA']. clear SA. rewrite SAS in SA'.
    destruct (rw_cells_forget _ _ _ _ SB) as [jb SB']. clear SB. rewrite SBS in SB'.
    destruct (rw_cells_forget _ _ _ _ SC) as [jc SC']. clear SC. rewrite SCS in SC'.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as (RT & _).
    pose proof (gl_got_memset _ _ _ GL _ _ _ _ _ _ _ G) as GMS. unfold GOT_MEMSET in GMS.
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    pose proof (munch_refl [(SPA - 4096, SPA); (Fb, Fb + 8192); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    zstep. neg_lits.
    do 4 zstep.
    do 3 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (RT1 : artcells mm)
        by (eapply artcells_munch; [exact RT| exact MU| exact WM|]; repeat (apply Forall_cons; [cbn [fst]; unfold AIMG_HI; lia|]); apply Forall_nil) end.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut.
    { eapply SETSHF8 with (lo := lo) (SA := (Z.shiftr Fb 3 + 2147450924)%Z) (n := 512%Z) (old := jb);
        [ assumption | rewrite Hspa; exact ST | rewrite Hspa; unfold FAKE_STACK; lia | lia | exact RT1 | unfold GOT_MEMSET; exact GMS | reflexivity | reflexivity | lia | lia
        | exact SB' | eapply rng_sub'; [exact FSRNG| lia] | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] | exact RIMG ]. }
    cbv beta. intros ms' PO. destruct PO as (av & m2 & E & MU2 & WM2 & MI2 & ST2 & SB2).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 543420)) with (Z_to_bv 64 543420) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unfold FAKE_STACK in MU2.
    lazymatch type of MU2 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU2 WM2 end.
    clear MU2 WM2 RT1.
    (* [comment removed for export] *)
    burst_begin [(Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z [(Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.   (* [comment removed for export] *)
    do 32 zstep.
    burst_end MUb WMb.
    do 3 zstep.
    zstep. if_false_by (eqz_false Fb ltac:(lia)).
    do 3 zstep. zstep.
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_FUZZ_ONE_INPUT, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(SPA - 4096, SPA); (Fb, Fb + 8192); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ FW (Forall_nil _) G' MU WM ltac:(lia)) as [G5 AG5] end.
    rewrite app_nil_r in G5. cbn [app] in G5.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FFREE7 _ spa) with (L := L) (CL := CL) (FB := FB) (FL := []) (lo := lo) (Fb := Fb) (req := 4672%Z) (f := FF_FUZZ_ONE_INPUT).
    { split; [exact G5|]. rewrite Hspa. split; [assumption|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [Z.div_mod_to_equations; lia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { reflexivity. }
    { replace (Fb + ff_size FF_FUZZ_ONE_INPUT - 8)%Z with (Fb + 8184)%Z by (unfold ff_size, ff_class; lia). exact FLG. }
    intros sx m6 a0' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G6 OF6 LC6 TL6 MI6 ST6 AG6.
    rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 543580)) with (Z_to_bv 64 543580) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG6) in FRs; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG6) in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG6) in STG; [|intros a Ha; left; lia].
    clear MU WM G5 G' RT. repeat match goal with HX : rw_cells asegs ?mx _ _ |- _ => lazymatch mx with m6 => fail | _ => clear HX end end.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU6. pose proof (wmono_refl asegs m6) as WM6.
    zstep.
    zstep.
    do 16 zstep.
    release_frame FRA ST6 (SPA + 56)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST6 STG ltac:(lia)) as ST7. clear ST6 STG.
    release_frame FRs ST7 (bv_unsigned sp).
    apply evtF_done. subst POSTQ. cbv beta iota.
    split; [reflexivity|]. split; [reflexivity|].
    do 14 eexists. lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end.
    split; [reflexivity|]. split; [assumption|]. split; [exact ST7|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a K; split; [exact K| exact I]|].
             eapply client_keeps_weaken; [exact AG6| lia| intros a Ha; exact Ha| apply incl_refl]. }
    split; [exact G6|]. split; [exact OF6|]. split; [exact LC6| exact TL6].
  Qed.
  End Sz1.
  #[using="GL FFREE7 SETSHF8"] Lemma fz_exit : ltac:(let t := eval cbv delta [fz_exit__stmt] in fz_exit__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb m ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r23 r25 t3 t4 t5 t6 k0 fra ca cb cc A x. ltac2:(SecDiet.SzSec.closeP 'fz_exit__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FuzzExit.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Open Scope bv_scope.
(* [comment removed for export] *)
Local Ltac nlb_hyp A :=
  repeat match goal with
  | H : rw_cells _ _ A ?cs |- _ =>
      match cs with context [C1 (Z_to_bv 8 ?z)] =>
        is_Zlit z; let z' := eval vm_compute in (Z.modulo z 256) in
        tryif constr_eq z z' then fail else
        replace (Z_to_bv 8 z) with (Z_to_bv 8 z') in H by (apply (proj2 (bv_eq _ _ _)); reflexivity)
      end
  end.
Local Ltac mem_after_store_opt ::=
  norm_lit_store_bytes;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store; try nlb_hyp A
      | _ => idtac
      end
  | _ => idtac
  end.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section FuzzExit.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETSHF8 : set_shadow_stmt 0x583f0 0xf8.

  Definition fz_exit__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (lo SPA Fb : Z) (m : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r23 r25 t3 t4 t5 t6 : word)
      (k0 : word) (fra ca cb cc : list cell) (A : Type) (x : A),
    (bv_unsigned sp - 191 <= SPA <= bv_unsigned sp - 160)%Z -> (SPA mod 32 = 0)%Z -> (ATOP + 4096 <= lo)%Z -> (lo + 8192 <= SPA)%Z ->
    (bv_unsigned sp + 16 < al_top L)%Z -> (al_top L <= 2^47)%Z -> tp = Z_to_bv 64 ATP ->
    GIOA L RNG s CL FB [(FF_FUZZ_ONE_INPUT, Fb, 8192%Z)] m -> mem_inv asegs m ->
    stk asegs m lo SPA -> stk asegs m (SPA + 56) (bv_unsigned sp + -104) ->
    rw_cells asegs m SPA fra -> cells_size fra = 56%nat ->
    rw_cells asegs m (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m Fb [C8 k0] ->
    rw_cells asegs m (Fb + 8184) [C8 (Z_to_bv 64 (fflagA L FF_FUZZ_ONE_INPUT Fb))] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) ca -> cells_size ca = 44%nat ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450924) cb -> cells_size cb = 512%nat ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147451436) cc -> cells_size cc = 28%nat ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_atls RNG ->
    implMG RNG (fo_ret FO _ FF_FUZZ_ONE_INPUT x) s
      (fun r s' RNG' ms' => r = x /\ RNG' = RNG /\ exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (client_keeps [] CL (bv_unsigned sp)) m m'
           /\ GIOA L RNG s' CL FB [] m' /\ ps_outfile s' = ps_outfile s /\ ps_libc s' = ps_libc s /\ ps_tls s' = ps_tls s)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) r21 r22 r23 (Z_to_bv 64 Fb) r25 (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x84ad4) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb m ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r23 r25 t3 t4 t5 t6 k0 fra ca cb cc A x : ltac2:(SecDiet.SzSec.tyM 'fz_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL FFREE7 SETSHF8"] Lemma fz_exit__body : ltac2:(SecDiet.SzSec.bodyP 'fz_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros SPAB SPA32 LO LOS SPT TOP47 TPE G MI ST STG FRA FRAS FRs FK0 FLG SA SAS SB SBS SC SCS RSTK RIMG RISH RTLS.
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. pose proof (Forall_inv FAll) as (FBAND & FTOP & F64 & _ & FRNG & FSRNG & _ & _).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64, FRNG, FSRNG. clear FAll. change (Z.shiftr 8192 3) with 1024%Z in FSRNG.
    pose proof (ablk_lin _ _ FBAND) as (_ & Fb0 & _ & _). band_ind FBAND bF.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 1024 <= 0x10007fff8000
                   /\ (Fb + 8192 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 1024 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    destruct SHLO as (SH1 & SH2 & _).   (* [comment removed for export] *)
    destruct (rw_cells_forget _ _ _ _ SA) as [ja SA']. clear SA. rewrite SAS in SA'.
    destruct (rw_cells_forget _ _ _ _ SB) as [jb SB']. clear SB. rewrite SBS in SB'.
    destruct (rw_cells_forget _ _ _ _ SC) as [jc SC']. clear SC. rewrite SCS in SC'.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as (RT & _).
    pose proof (gl_got_memset _ _ _ GL _ _ _ _ _ _ _ G) as GMS. unfold GOT_MEMSET in GMS.
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    pose proof (munch_refl [(SPA - 4096, SPA); (Fb, Fb + 8192); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    zstep. neg_lits.
    do 4 zstep.
    do 3 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (RT1 : artcells mm)
        by (eapply artcells_munch; [exact RT| exact MU| exact WM|]; repeat (apply Forall_cons; [cbn [fst]; unfold AIMG_HI; lia|]); apply Forall_nil) end.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut.
    { eapply SETSHF8 with (lo := lo) (SA := (Z.shiftr Fb 3 + 2147450924)%Z) (n := 512%Z) (old := jb);
        [ assumption | rewrite Hspa; exact ST | rewrite Hspa; unfold FAKE_STACK; lia | lia | exact RT1 | unfold GOT_MEMSET; exact GMS | reflexivity | reflexivity | lia | lia
        | exact SB' | eapply rng_sub'; [exact FSRNG| lia] | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] | exact RIMG ]. }
    cbv beta. intros ms' PO. destruct PO as (av & m2 & E & MU2 & WM2 & MI2 & ST2 & SB2).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 543476)) with (Z_to_bv 64 543476) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unfold FAKE_STACK in MU2.
    lazymatch type of MU2 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU2 WM2 end.
    clear MU2 WM2 RT1.
    (* [comment removed for export] *)
    burst_begin [(Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z [(Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.   (* [comment removed for export] *)
    do 32 zstep.
    burst_end MUb WMb.
    do 3 zstep.
    zstep. if_false_by (eqz_false Fb ltac:(lia)).
    do 3 zstep. zstep.
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_FUZZ_ONE_INPUT, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(SPA - 4096, SPA); (Fb, Fb + 8192); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ FW (Forall_nil _) G' MU WM ltac:(lia)) as [G5 AG5] end.
    rewrite app_nil_r in G5. cbn [app] in G5.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FFREE7 _ spa) with (L := L) (CL := CL) (FB := FB) (FL := []) (lo := lo) (Fb := Fb) (req := 4672%Z) (f := FF_FUZZ_ONE_INPUT).
    { split; [exact G5|]. rewrite Hspa. split; [assumption|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [Z.div_mod_to_equations; lia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { reflexivity. }
    { replace (Fb + ff_size FF_FUZZ_ONE_INPUT - 8)%Z with (Fb + 8184)%Z by (unfold ff_size, ff_class; lia). exact FLG. }
    intros sx m6 a0' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G6 OF6 LC6 TL6 MI6 ST6 AG6.
    rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 543636)) with (Z_to_bv 64 543636) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG6) in FRs; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG6) in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG6) in STG; [|intros a Ha; left; lia].
    clear MU WM G5 G' RT. repeat match goal with HX : rw_cells asegs ?mx _ _ |- _ => lazymatch mx with m6 => fail | _ => clear HX end end.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU6. pose proof (wmono_refl asegs m6) as WM6.
    zstep.
    zstep.
    do 16 zstep.
    release_frame FRA ST6 (SPA + 56)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST6 STG ltac:(lia)) as ST7. clear ST6 STG.
    release_frame FRs ST7 (bv_unsigned sp).
    apply evtF_done. subst POSTQ. cbv beta iota.
    split; [reflexivity|]. split; [reflexivity|].
    do 14 eexists. lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end.
    split; [reflexivity|]. split; [assumption|]. split; [exact ST7|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a K; split; [exact K| exact I]|].
             eapply client_keeps_weaken; [exact AG6| lia| intros a Ha; exact Ha| apply incl_refl]. }
    split; [exact G6|]. split; [exact OF6|]. split; [exact LC6| exact TL6].
  Qed.
  End Sz1.
  #[using="GL FFREE7 SETSHF8"] Lemma fz_exit : ltac:(let t := eval cbv delta [fz_exit__stmt] in fz_exit__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb m ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r23 r25 t3 t4 t5 t6 k0 fra ca cb cc A x. ltac2:(SecDiet.SzSec.closeP 'fz_exit__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FuzzExit.
End CANSEC1.
End TwB.
End F_fuzz_exitA.

(* [comment removed for export] *)
Module F_fuzz_kitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC0. Context {rc : runConstT}.
#[using="Type"] Lemma name_bytes : forall m A n (buf pre : list byte) k,
  rw_cells asegs m A [CB n buf] -> firstn k buf = pre -> bytes_at asegs m A pre.
Proof.
  intros m A n buf pre k RC E. apply rw_cells_bytes_at in RC. cbn [cells_bytes cbytes] in RC. rewrite app_nil_r in RC.
  rewrite <- (firstn_skipn k buf), E in RC. apply bytes_at_app in RC as [RC _]. exact RC.
Qed.
End CANSEC0.

Definition tmpname : list byte := map b8 TMPNAME.
Lemma tmpname_Z : map bv_unsigned tmpname = TMPNAME.
Proof. vm_compute. reflexivity. Qed.
Lemma tmpname_len : length tmpname = 24%nat.
Proof. reflexivity. Qed.
Lemma tmpname_nonul : ~ In (Z_to_bv 8 0) tmpname.
Proof. unfold tmpname, TMPNAME. cbn. intros Hin. repeat (destruct Hin as [E|Hin]; [discriminate E|]). exact Hin. Qed.
Lemma tmpname_first : nth_error tmpname 0 <> Some (Z_to_bv 8 45).
Proof. cbn. discriminate. Qed.
Lemma tmpname_ok : unlink_name_ok tmpname.
Proof.
  unfold unlink_name_ok. split; [vm_compute; reflexivity|]. split; [discriminate|]. split; [discriminate|].
  rewrite tmpname_len. unfold Uapi.NAME_MAX. lia.
Qed.
Lemma tmpname_open_w : open_name_ok true tmpname.
Proof. left. vm_compute. reflexivity. Qed.
Lemma tmpname_open_r : open_name_ok false tmpname.
Proof. split; vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
Definition SHA : list cell := [CB 44 (repeat (Z_to_bv 8 0xf1) 4 ++ repeat (Z_to_bv 8 0) 32 ++ repeat (Z_to_bv 8 0xf2) 8)].
Definition SHB : list cell := [CB 512 (repeat (Z_to_bv 8 0) 512)].
Definition SHC : list cell :=
  [CB 28 (repeat (Z_to_bv 8 0xf2) 16 ++ [Z_to_bv 8 0; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2;
                                            Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0xf3; Z_to_bv 8 0xf3])].

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section FuzzKit.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).

  Definition FZFL (Fb : Z) : list fblock := [(FF_FUZZ_ONE_INPUT, Fb, 8192)].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fz_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL : list cblk) (lo : Z) (m : mem) : unit -> PS -> footprint -> machine_state -> Prop :=
    fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' FB',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps [] CL (bv_unsigned sp)) m m'
      /\ GIOA L RNG' s' CL FB' [] m'.

  #[using="Type"] Lemma fz_post_back : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG0 RNG1 CL lo m0 m1 u s' RNG' ms',
    fp_le RNG0 RNG1 -> agrees_on (client_keeps [] CL (bv_unsigned sp)) m0 m1 ->
    fz_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG1 CL lo m1 u s' RNG' ms' ->
    fz_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG0 CL lo m0 u s' RNG' ms'.
  Proof.
    intros until ms'. intros FP AG (FP' & PO). destruct_exs PO. destruct PO as (E & MI & ST & AG2 & G).
    split; [intros b j Hb; apply FP', FP; exact Hb|].
    do 16 eexists. split; [exact E|]. split; [exact MI|]. split; [exact ST|]. split; [eapply agrees_on_trans; [exact AG| exact AG2]| exact G].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hpureA (L : alayout) (sp tp : word) (lo SPA : Z) : Prop :=
    (bv_unsigned sp - 191 <= SPA <= bv_unsigned sp - 160) /\ SPA mod 32 = 0 /\ ATOP + 4096 <= lo /\ lo + (FUZZ_STACK - 191) <= SPA
    /\ bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47 /\ tp = Z_to_bv 64 ATP /\ bv_unsigned sp mod 16 = 0.
  (* [comment removed for export] *)
  Definition hrngA (L : alayout) (RNG : footprint) (lo : Z) : Prop :=
    rng RNG lo (al_top L - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG.

  #[using="Type"] Lemma hrngA_le : forall L RNG RNG' lo, hrngA L RNG lo -> fp_le RNG RNG' -> hrngA L RNG' lo.
  Proof.
    intros L RNG RNG' lo (R1 & R2 & R3 & R4) FP.
    split; [eapply rng_fp_le; eassumption|]. split; [eapply rng_fp_le; eassumption|]. split; eapply rng_fp_le; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma hpureA_spo : forall L RNG sp tp lo SPA s CL FB FL m budget,
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s CL FB FL m -> stk asegs m lo SPA -> mem_inv asegs m -> budget <= FUZZ_STACK - 191 ->
    std_pre_o GIOA L RNG (Z_to_bv 64 SPA) tp s CL FB FL lo budget m.
  Proof.
    intros L RNG sp tp lo SPA s CL FB FL m budget (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) (R1 & R2 & R3 & R4) G ST MI HB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    unfold FUZZ_STACK, PCAP_L4_STACK in H4, HB.
    assert (E : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia). unfold std_pre_o. rewrite E.
    split; [exact G|]. split; [exact ST|]. split; [exact H3|]. split; [lia|]. split; [lia|]. split; [exact MI|]. split; [exact H7|].
    split; [Z.div_mod_to_equations; lia|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3| exact R4].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hcoreA (L : alayout) (sp : word) (lo SPA Fb : Z) (sv fra : list cell) (m : mem) : Prop :=
    mem_inv asegs m /\ stk asegs m lo SPA /\ stk asegs m (SPA + 56) (bv_unsigned sp + -104)
    /\ rw_cells asegs m SPA fra /\ rw_cells asegs m (bv_unsigned sp + -104) sv
    /\ (exists k0, rw_cells asegs m Fb [C8 k0]) /\ rw_cells asegs m (Fb + 8184) [C8 (Z_to_bv 64 (fflagA L FF_FUZZ_ONE_INPUT Fb))]
    /\ rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) SHA /\ rw_cells asegs m (Z.shiftr Fb 3 + 2147450924) SHB
    /\ rw_cells asegs m (Z.shiftr Fb 3 + 2147451436) SHC.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma fz_frame_facts : forall L RNG s CL FB Fb m, GIOA L RNG s CL FB (FZFL Fb) m ->
    ablk Fb (Fb + 8192) /\ Fb + 8192 <= ATOP /\ Fb mod 64 = 0 /\ 0 < Fb /\ Fb + 8192 + 8 <= 2^47
    /\ rng RNG Fb 8192 /\ rng RNG (Z.shiftr Fb 3 + 2147450880) 1024
    /\ 0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 1024 <= 0x10007fff8000.
  Proof.
    intros L RNG s CL FB Fb m G. destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _].
    pose proof (Forall_inv FAll) as (FBAND & FTOP & F64 & _ & FRNG & FSRNG & _ & _).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64, FRNG, FSRNG. change (Z.shiftr 8192 3) with 1024 in FSRNG.
    pose proof (ablk_lin _ _ FBAND) as (IMG & Fb0 & _ & T47). unfold AIMG_HI in IMG.
    split; [exact FBAND|]. split; [exact FTOP|]. split; [exact F64|]. split; [lia|]. split; [lia|]. split; [exact FRNG|]. split; [exact FSRNG|].
    rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="FO GL"] Lemma hcoreA_keep : forall L RNG s CLg (CL : list cblk) FB sp tp lo SPA Fb sv fra (X : Z -> Prop) m m',
    hcoreA L sp lo SPA Fb sv fra m -> GIOA L RNG s CLg FB (FZFL Fb) m ->
    hpureA L sp tp lo SPA -> cells_size fra = 56%nat -> cells_size sv = 104%nat ->
    agrees_on (fun a => client_keeps (FZFL Fb) CL SPA a /\ X a) m m' ->
    (forall a, ~ (Fb + 32 <= a < Fb + 8184) -> X a) ->
    mem_inv asegs m' -> stk asegs m' lo SPA ->
    hcoreA L sp lo SPA Fb sv fra m'.
  Proof.
    intros L RNG s CLg CL FB sp tp lo SPA Fb sv fra X m m' (MI & ST & STG & FRA & FRs & (k0 & FK0) & FLG & SA & SB & SC) G HP FRAS SVS AG HX MI' ST'.
    destruct HP as (SPAB & _ & LO & LOS & _). unfold FUZZ_STACK, PCAP_L4_STACK in LOS.
    pose proof (fz_frame_facts _ _ _ _ _ _ _ G) as (FBAND & FTOP & F64 & Fb0 & T47 & _ & _ & SH1 & SH2).
    band_ind FBAND bF. atop_facts.
    assert (SHE : Z.shiftr Fb 3 + 2147450880 = Fb / 8 + 2147450880) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (KS : forall a, SPA <= a -> client_keeps (FZFL Fb) CL SPA a /\ X a) by (intros a Ha; split; [left; exact Ha| apply HX; lia]).
    assert (KF : forall a, Fb <= a < Fb + 32 \/ Fb + 8184 <= a < Fb + 8192 -> client_keeps (FZFL Fb) CL SPA a /\ X a).
    { intros a Ha. split; [| apply HX; lia]. right; right; left. apply Exists_cons_hd. cbn [fb_addr fb_size fst snd]. lia. }
    assert (KSH : forall a, Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 1024 -> client_keeps (FZFL Fb) CL SPA a /\ X a).
    { intros a Ha. split; [| apply HX; rewrite SHE in Ha; Z.div_mod_to_equations; lia]. right; right; right. apply Exists_cons_hd. cbn [fb_addr fb_size fst snd].
      change (Z.shiftr 8192 3) with 1024. exact Ha. }
    split; [exact MI'|]. split; [exact ST'|].
    split; [eapply agrees_stk; [exact AG| exact STG| intros a Ha; apply KS; lia]|].
    split; [eapply agrees_rw_cells; [exact AG| exact FRA| intros a Ha; apply KS; lia]|].
    split; [eapply agrees_rw_cells; [exact AG| exact FRs| intros a Ha; apply KS; rewrite SVS in Ha; lia]|].
    split; [exists k0; eapply agrees_rw_cells; [exact AG| exact FK0| intros a Ha; apply KF; cbn [cells_size csize Nat.add] in Ha; lia]|].
    split; [eapply agrees_rw_cells; [exact AG| exact FLG| intros a Ha; apply KF; cbn [cells_size csize Nat.add] in Ha; lia]|].
    split; [eapply agrees_rw_cells; [exact AG| exact SA| intros a Ha; apply KSH; unfold SHA in Ha; cbn [cells_size csize Nat.add] in Ha; lia]|].
    split; [eapply agrees_rw_cells; [exact AG| exact SB| intros a Ha; apply KSH; unfold SHB in Ha; cbn [cells_size csize Nat.add] in Ha; lia]|].
    eapply agrees_rw_cells; [exact AG| exact SC| intros a Ha; apply KSH; unfold SHC in Ha; cbn [cells_size csize Nat.add] in Ha; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fz_local_keep : forall (CL : list cblk) SPA Fb (X : Z -> Prop) m m' A cs,
    rw_cells asegs m A cs -> agrees_on (fun a => client_keeps (FZFL Fb) CL SPA a /\ X a) m m' ->
    Fb <= A -> A + Z.of_nat (cells_size cs) <= Fb + 8192 -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> X a) ->
    rw_cells asegs m' A cs.
  Proof.
    intros CL SPA Fb X m m' A cs HC AG H1 H2 HX. eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. split; [| apply HX; exact Ha].
    right; right; left. apply Exists_cons_hd. cbn [fb_addr fb_size fst snd]. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fz_uc_keep : forall d L (CL : list cblk) SPA Fb (X : Z -> Prop) m m' (sp s0 ra : word) trC,
    ucallerA d L m sp s0 ra trC -> al_top L <= 2^47 -> agrees_on (fun a => client_keeps (FZFL Fb) CL SPA a /\ X a) m m' ->
    SPA <= bv_unsigned sp -> (forall a, bv_unsigned sp <= a -> X a) -> ucallerA d L m' sp s0 ra trC.
  Proof.
    intros d L CL SPA Fb X m m' sp s0 ra trC UC HT AG HS HX. eapply ucaller_keep; [exact UC| exact HT|].
    intros a Ha. apply (AG a); [pose proof (bv_unsigned_in_range 64 sp) as R; unfold bv_modulus in R; cbn in R; lia|].
    split; [left; lia| apply HX; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="FO GL"] Lemma hcoreA_keep0 : forall L RNG s CLg (CL : list cblk) FB sp tp lo SPA Fb sv fra m m',
    hcoreA L sp lo SPA Fb sv fra m -> GIOA L RNG s CLg FB (FZFL Fb) m ->
    hpureA L sp tp lo SPA -> cells_size fra = 56%nat -> cells_size sv = 104%nat ->
    agrees_on (client_keeps (FZFL Fb) CL SPA) m m' -> mem_inv asegs m' -> stk asegs m' lo SPA ->
    hcoreA L sp lo SPA Fb sv fra m'.
  Proof.
    intros L RNG s CLg CL FB sp tp lo SPA Fb sv fra m m' HC G HP FRAS SVS AG MI' ST'.
    eapply (hcoreA_keep _ _ _ CLg CL _ _ _ _ _ _ _ _ (fun _ => True)); [exact HC| exact G| exact HP| exact FRAS| exact SVS| | intros; exact I| exact MI'| exact ST'].
    eapply agrees_on_weaken; [exact AG| intros a [K _]; exact K].
  Qed.
  #[using="Type"] Lemma fz_local_keep0 : forall (CL : list cblk) SPA Fb m m' A cs,
    rw_cells asegs m A cs -> agrees_on (client_keeps (FZFL Fb) CL SPA) m m' ->
    Fb <= A -> A + Z.of_nat (cells_size cs) <= Fb + 8192 -> rw_cells asegs m' A cs.
  Proof.
    intros CL SPA Fb m m' A cs HC AG H1 H2. eapply (fz_local_keep CL SPA Fb (fun _ => True)); [exact HC| | exact H1| exact H2| intros; exact I].
    eapply agrees_on_weaken; [exact AG| intros a [K _]; exact K].
  Qed.
  #[using="Type"] Lemma fz_uc_keep0 : forall d L (CL : list cblk) SPA Fb m m' (sp s0 ra : word) trC,
    ucallerA d L m sp s0 ra trC -> al_top L <= 2^47 -> agrees_on (client_keeps (FZFL Fb) CL SPA) m m' ->
    SPA <= bv_unsigned sp -> ucallerA d L m' sp s0 ra trC.
  Proof.
    intros d L CL SPA Fb m m' sp s0 ra trC UC HT AG HS. eapply (fz_uc_keep d L CL SPA Fb (fun _ => True)); [exact UC| exact HT| | exact HS| intros; exact I].
    eapply agrees_on_weaken; [exact AG| intros a [K _]; exact K].
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma fz_ag_final : forall (CL : list cblk) SPA Fb (sp : word) m m',
    agrees_on (client_keeps (FZFL Fb) CL SPA) m m' -> SPA <= bv_unsigned sp -> agrees_on (client_keeps [] CL (bv_unsigned sp)) m m'.
  Proof. intros CL SPA Fb sp m m' AG HS. eapply client_keeps_weaken; [exact AG| exact HS| intros a Ha; exact Ha| intros fr0 []]. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fz_ucaller : forall d' L (sp tp s0 ra : word) lo SPA Fb sv fra m trC X (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : cell),
    ucallerA depth_fuzz_one L m sp s0 ra trC -> hpureA L sp tp lo SPA -> hcoreA L sp lo SPA Fb sv fra m ->
    sv = [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; C8 s0; C8 ra] -> cells_size [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] = 88%nat ->
    ACLIENT_LO <= X < ACLIENT_HI -> (S d' <= depth_fuzz_one)%nat ->
    ucallerA d' L m (Z_to_bv 64 SPA) sp (Z_to_bv 64 X) (bv_unsigned ra :: trC).
  Proof.
    intros d' L sp tp s0 ra lo SPA Fb sv fra m trC X c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 UC HP HC -> SZ HX HD.
    destruct HP as (SPAB & _ & LO & LOS & SPT & TOP47 & _ & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS.
    destruct HC as (_ & _ & _ & _ & FRs & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (E : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (rw_cells_nth_C8 _ _ _ 11%nat _ FRs eq_refl) as BS0. pose proof (rw_cells_nth_C8 _ _ _ 12%nat _ FRs eq_refl) as BRA.
    cbn [firstn] in BS0, BRA.
    change [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; C8 s0] with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ++ [C8 s0]) in BRA.
    rewrite cells_size_app, SZ in BRA. rewrite SZ in BS0. cbn [cells_size csize Nat.add] in BRA.
    eapply (ucaller_frame _ d' _ _ _ _ _ _ _ _ X UC); [rewrite E; lia| lia| Z.div_mod_to_equations; lia| | | reflexivity| exact HX| exact HD].
    - replace (bv_unsigned sp - 16) with (bv_unsigned sp + -104 + Z.of_nat 88) by lia. exact BS0.
    - replace (bv_unsigned sp - 8) with (bv_unsigned sp + -104 + Z.of_nat (88 + 8)) by lia. exact BRA.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma fz_cobj : forall L RNG s CLg (CL : list cblk) FB Fb m A n, GIOA L RNG s CLg FB (FZFL Fb) m ->
    Fb <= A -> A + n <= Fb + 8192 -> 0 <= n -> unpoisoned m A (A + n) -> cobjA RNG m (FZFL Fb) CL A n.
  Proof.
    intros L RNG s CLg CL FB Fb m A n G H1 H2 Hn UNP. destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. pose proof (Forall_inv FAll) as FRA.
    split.
    - right. exists (FF_FUZZ_ONE_INPUT, Fb, 8192). split; [left; reflexivity|]. cbn [fb_addr fb_size fst snd]. lia.
    - eapply frameA_aobj; [exact FRA| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| exact Hn| exact UNP].
  Qed.

  #[using="Type"] Lemma fz_unp_errbuf : forall m Fb, rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) SHA -> Fb mod 8 = 0 -> 0 <= Fb -> Fb + 8192 <= 2^47 ->
    unpoisoned m (Fb + 32) (Fb + 32 + 256).
  Proof.
    intros m Fb SA F8 F0 FT.
    pose proof (unp_of_sh_bytes m Fb SHA 4 32 SA F8 F0 ltac:(unfold SHA; cbn [cells_size csize Nat.add]; lia) ltac:(reflexivity) ltac:(unfold SHA; cbn; lia)) as U.
    replace (Fb + 8 * Z.of_nat 4) with (Fb + 32) in U by lia. replace (8 * Z.of_nat 32) with 256 in U by lia. exact U.
  Qed.
  #[using="Type"] Lemma fz_unp_fname : forall m Fb, rw_cells asegs m (Z.shiftr Fb 3 + 2147450924) SHB -> Fb mod 8 = 0 -> 0 <= Fb -> Fb + 8192 <= 2^47 ->
    unpoisoned m (Fb + 352) (Fb + 352 + 4096).
  Proof.
    intros m Fb SB F8 F0 FT.
    assert (E : Z.shiftr (Fb + 352) 3 + 2147450880 = Z.shiftr Fb 3 + 2147450924) by (replace (Fb + 352) with (Fb + 8 * 44) by lia; rewrite (shiftr3_add Fb 44 F8); lia).
    rewrite <- E in SB.
    pose proof (unp_of_sh_bytes m (Fb + 352) SHB 0 512 SB ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(unfold SHB; cbn [cells_size csize Nat.add]; lia)
                  ltac:(reflexivity) ltac:(unfold SHB; cbn; lia)) as U.
    replace (Fb + 352 + 8 * Z.of_nat 0) with (Fb + 352) in U by lia. replace (8 * Z.of_nat 512) with 4096 in U by lia. exact U.
  Qed.
  #[using="Type"] Lemma fz_unp_locals : forall m Fb, rw_cells asegs m (Z.shiftr Fb 3 + 2147451436) SHC -> Fb mod 8 = 0 -> 0 <= Fb -> Fb + 8192 <= 2^47 ->
    unpoisoned m (Fb + 4576) (Fb + 4576 + 8) /\ unpoisoned m (Fb + 4608) (Fb + 4608 + 8).
  Proof.
    intros m Fb SC F8 F0 FT.
    assert (E : Z.shiftr (Fb + 4448) 3 + 2147450880 = Z.shiftr Fb 3 + 2147451436) by (replace (Fb + 4448) with (Fb + 8 * 556) by lia; rewrite (shiftr3_add Fb 556 F8); lia).
    rewrite <- E in SC. split.
    - pose proof (unp_of_sh_bytes m (Fb + 4448) SHC 16 1 SC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(unfold SHC; cbn [cells_size csize Nat.add]; lia)
                    ltac:(reflexivity) ltac:(unfold SHC; cbn; lia)) as U.
      replace (Fb + 4448 + 8 * Z.of_nat 16) with (Fb + 4576) in U by lia. replace (8 * Z.of_nat 1) with 8 in U by lia. exact U.
    - pose proof (unp_of_sh_bytes m (Fb + 4448) SHC 20 1 SC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(unfold SHC; cbn [cells_size csize Nat.add]; lia)
                    ltac:(reflexivity) ltac:(unfold SHC; cbn; lia)) as U.
      replace (Fb + 4448 + 8 * Z.of_nat 20) with (Fb + 4608) in U by lia. replace (8 * Z.of_nat 1) with 8 in U by lia. exact U.
  Qed.
End FuzzKit.
End CANSEC1.

(* [comment removed for export] *)
Ltac hr_open HR :=
  let R1 := fresh "RSTK" in let R2 := fresh "RIMG" in let R3 := fresh "RISH" in let R4 := fresh "RTLS" in let R5 := fresh "RSPA" in
  pose proof HR as (R1 & R2 & R3 & R4);
  lazymatch type of R1 with rng ?RNG ?lo _ =>
    lazymatch goal with SPAB : (bv_unsigned ?sp - 191 <= ?SPA <= bv_unsigned ?sp - 160)%Z |- _ =>
      assert (R5 : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact R1| lia]) end end.
Ltac hr_next HR FP HR' :=
  pose proof (hrngA_le _ _ _ _ HR FP) as HR';
  lazymatch type of HR with hrngA _ ?RNG _ => repeat match goal with HX : rng RNG _ _ |- _ => clear HX end end;
  hr_open HR'.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC0. Context {rc : runConstT}.
#[using="Type"] Lemma name_bytes : forall m A n (buf pre : list byte) k,
  rw_cells asegs m A [CB n buf] -> firstn k buf = pre -> bytes_at asegs m A pre.
Proof.
  intros m A n buf pre k RC E. apply rw_cells_bytes_at in RC. cbn [cells_bytes cbytes] in RC. rewrite app_nil_r in RC.
  rewrite <- (firstn_skipn k buf), E in RC. apply bytes_at_app in RC as [RC _]. exact RC.
Qed.
End CANSEC0.

Definition tmpname : list byte := map b8 TMPNAME.
Lemma tmpname_Z : map bv_unsigned tmpname = TMPNAME.
Proof. vm_compute. reflexivity. Qed.
Lemma tmpname_len : length tmpname = 24%nat.
Proof. reflexivity. Qed.
Lemma tmpname_nonul : ~ In (Z_to_bv 8 0) tmpname.
Proof. unfold tmpname, TMPNAME. cbn. intros Hin. repeat (destruct Hin as [E|Hin]; [discriminate E|]). exact Hin. Qed.
Lemma tmpname_first : nth_error tmpname 0 <> Some (Z_to_bv 8 45).
Proof. cbn. discriminate. Qed.
Lemma tmpname_ok : unlink_name_ok tmpname.
Proof.
  unfold unlink_name_ok. split; [vm_compute; reflexivity|]. split; [discriminate|]. split; [discriminate|].
  rewrite tmpname_len. unfold Uapi.NAME_MAX. lia.
Qed.
Lemma tmpname_open_w : open_name_ok true tmpname.
Proof. left. vm_compute. reflexivity. Qed.
Lemma tmpname_open_r : open_name_ok false tmpname.
Proof. split; vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
Definition SHA : list cell := [CB 44 (repeat (Z_to_bv 8 0xf1) 4 ++ repeat (Z_to_bv 8 0) 32 ++ repeat (Z_to_bv 8 0xf2) 8)].
Definition SHB : list cell := [CB 512 (repeat (Z_to_bv 8 0) 512)].
Definition SHC : list cell :=
  [CB 28 (repeat (Z_to_bv 8 0xf2) 16 ++ [Z_to_bv 8 0; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2; Z_to_bv 8 0xf2;
                                            Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0xf3; Z_to_bv 8 0xf3])].

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section FuzzKit.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).

  Definition FZFL (Fb : Z) : list fblock := [(FF_FUZZ_ONE_INPUT, Fb, 8192)].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fz_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL : list cblk) (lo : Z) (m : mem) : unit -> PS -> footprint -> machine_state -> Prop :=
    fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' FB',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps [] CL (bv_unsigned sp)) m m'
      /\ GIOA L RNG' s' CL FB' [] m'.

  #[using="Type"] Lemma fz_post_back : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG0 RNG1 CL lo m0 m1 u s' RNG' ms',
    fp_le RNG0 RNG1 -> agrees_on (client_keeps [] CL (bv_unsigned sp)) m0 m1 ->
    fz_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG1 CL lo m1 u s' RNG' ms' ->
    fz_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG0 CL lo m0 u s' RNG' ms'.
  Proof.
    intros until ms'. intros FP AG (FP' & PO). destruct_exs PO. destruct PO as (E & MI & ST & AG2 & G).
    split; [intros b j Hb; apply FP', FP; exact Hb|].
    do 16 eexists. split; [exact E|]. split; [exact MI|]. split; [exact ST|]. split; [eapply agrees_on_trans; [exact AG| exact AG2]| exact G].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hpureA (L : alayout) (sp tp : word) (lo SPA : Z) : Prop :=
    (bv_unsigned sp - 191 <= SPA <= bv_unsigned sp - 160) /\ SPA mod 32 = 0 /\ ATOP + 4096 <= lo /\ lo + (FUZZ_STACK - 191) <= SPA
    /\ bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47 /\ tp = Z_to_bv 64 ATP /\ bv_unsigned sp mod 16 = 0.
  (* [comment removed for export] *)
  Definition hrngA (L : alayout) (RNG : footprint) (lo : Z) : Prop :=
    rng RNG lo (al_top L - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG.

  #[using="Type"] Lemma hrngA_le : forall L RNG RNG' lo, hrngA L RNG lo -> fp_le RNG RNG' -> hrngA L RNG' lo.
  Proof.
    intros L RNG RNG' lo (R1 & R2 & R3 & R4) FP.
    split; [eapply rng_fp_le; eassumption|]. split; [eapply rng_fp_le; eassumption|]. split; eapply rng_fp_le; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma hpureA_spo : forall L RNG sp tp lo SPA s CL FB FL m budget,
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s CL FB FL m -> stk asegs m lo SPA -> mem_inv asegs m -> budget <= FUZZ_STACK - 191 ->
    std_pre_o GIOA L RNG (Z_to_bv 64 SPA) tp s CL FB FL lo budget m.
  Proof.
    intros L RNG sp tp lo SPA s CL FB FL m budget (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) (R1 & R2 & R3 & R4) G ST MI HB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    unfold FUZZ_STACK, PCAP_L4_STACK in H4, HB.
    assert (E : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia). unfold std_pre_o. rewrite E.
    split; [exact G|]. split; [exact ST|]. split; [exact H3|]. split; [lia|]. split; [lia|]. split; [exact MI|]. split; [exact H7|].
    split; [Z.div_mod_to_equations; lia|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3| exact R4].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hcoreA (L : alayout) (sp : word) (lo SPA Fb : Z) (sv fra : list cell) (m : mem) : Prop :=
    mem_inv asegs m /\ stk asegs m lo SPA /\ stk asegs m (SPA + 56) (bv_unsigned sp + -104)
    /\ rw_cells asegs m SPA fra /\ rw_cells asegs m (bv_unsigned sp + -104) sv
    /\ (exists k0, rw_cells asegs m Fb [C8 k0]) /\ rw_cells asegs m (Fb + 8184) [C8 (Z_to_bv 64 (fflagA L FF_FUZZ_ONE_INPUT Fb))]
    /\ rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) SHA /\ rw_cells asegs m (Z.shiftr Fb 3 + 2147450924) SHB
    /\ rw_cells asegs m (Z.shiftr Fb 3 + 2147451436) SHC.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma fz_frame_facts : forall L RNG s CL FB Fb m, GIOA L RNG s CL FB (FZFL Fb) m ->
    ablk Fb (Fb + 8192) /\ Fb + 8192 <= ATOP /\ Fb mod 64 = 0 /\ 0 < Fb /\ Fb + 8192 + 8 <= 2^47
    /\ rng RNG Fb 8192 /\ rng RNG (Z.shiftr Fb 3 + 2147450880) 1024
    /\ 0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 1024 <= 0x10007fff8000.
  Proof.
    intros L RNG s CL FB Fb m G. destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _].
    pose proof (Forall_inv FAll) as (FBAND & FTOP & F64 & _ & FRNG & FSRNG & _ & _).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64, FRNG, FSRNG. change (Z.shiftr 8192 3) with 1024 in FSRNG.
    pose proof (ablk_lin _ _ FBAND) as (IMG & Fb0 & _ & T47). unfold AIMG_HI in IMG.
    split; [exact FBAND|]. split; [exact FTOP|]. split; [exact F64|]. split; [lia|]. split; [lia|]. split; [exact FRNG|]. split; [exact FSRNG|].
    rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="FO GL"] Lemma hcoreA_keep : forall L RNG s CLg (CL : list cblk) FB sp tp lo SPA Fb sv fra (X : Z -> Prop) m m',
    hcoreA L sp lo SPA Fb sv fra m -> GIOA L RNG s CLg FB (FZFL Fb) m ->
    hpureA L sp tp lo SPA -> cells_size fra = 56%nat -> cells_size sv = 104%nat ->
    agrees_on (fun a => client_keeps (FZFL Fb) CL SPA a /\ X a) m m' ->
    (forall a, ~ (Fb + 32 <= a < Fb + 8184) -> X a) ->
    mem_inv asegs m' -> stk asegs m' lo SPA ->
    hcoreA L sp lo SPA Fb sv fra m'.
  Proof.
    intros L RNG s CLg CL FB sp tp lo SPA Fb sv fra X m m' (MI & ST & STG & FRA & FRs & (k0 & FK0) & FLG & SA & SB & SC) G HP FRAS SVS AG HX MI' ST'.
    destruct HP as (SPAB & _ & LO & LOS & _). unfold FUZZ_STACK, PCAP_L4_STACK in LOS.
    pose proof (fz_frame_facts _ _ _ _ _ _ _ G) as (FBAND & FTOP & F64 & Fb0 & T47 & _ & _ & SH1 & SH2).
    band_ind FBAND bF. atop_facts.
    assert (SHE : Z.shiftr Fb 3 + 2147450880 = Fb / 8 + 2147450880) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (KS : forall a, SPA <= a -> client_keeps (FZFL Fb) CL SPA a /\ X a) by (intros a Ha; split; [left; exact Ha| apply HX; lia]).
    assert (KF : forall a, Fb <= a < Fb + 32 \/ Fb + 8184 <= a < Fb + 8192 -> client_keeps (FZFL Fb) CL SPA a /\ X a).
    { intros a Ha. split; [| apply HX; lia]. right; right; left. apply Exists_cons_hd. cbn [fb_addr fb_size fst snd]. lia. }
    assert (KSH : forall a, Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 1024 -> client_keeps (FZFL Fb) CL SPA a /\ X a).
    { intros a Ha. split; [| apply HX; rewrite SHE in Ha; Z.div_mod_to_equations; lia]. right; right; right. apply Exists_cons_hd. cbn [fb_addr fb_size fst snd].
      change (Z.shiftr 8192 3) with 1024. exact Ha. }
    split; [exact MI'|]. split; [exact ST'|].
    split; [eapply agrees_stk; [exact AG| exact STG| intros a Ha; apply KS; lia]|].
    split; [eapply agrees_rw_cells; [exact AG| exact FRA| intros a Ha; apply KS; lia]|].
    split; [eapply agrees_rw_cells; [exact AG| exact FRs| intros a Ha; apply KS; rewrite SVS in Ha; lia]|].
    split; [exists k0; eapply agrees_rw_cells; [exact AG| exact FK0| intros a Ha; apply KF; cbn [cells_size csize Nat.add] in Ha; lia]|].
    split; [eapply agrees_rw_cells; [exact AG| exact FLG| intros a Ha; apply KF; cbn [cells_size csize Nat.add] in Ha; lia]|].
    split; [eapply agrees_rw_cells; [exact AG| exact SA| intros a Ha; apply KSH; unfold SHA in Ha; cbn [cells_size csize Nat.add] in Ha; lia]|].
    split; [eapply agrees_rw_cells; [exact AG| exact SB| intros a Ha; apply KSH; unfold SHB in Ha; cbn [cells_size csize Nat.add] in Ha; lia]|].
    eapply agrees_rw_cells; [exact AG| exact SC| intros a Ha; apply KSH; unfold SHC in Ha; cbn [cells_size csize Nat.add] in Ha; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fz_local_keep : forall (CL : list cblk) SPA Fb (X : Z -> Prop) m m' A cs,
    rw_cells asegs m A cs -> agrees_on (fun a => client_keeps (FZFL Fb) CL SPA a /\ X a) m m' ->
    Fb <= A -> A + Z.of_nat (cells_size cs) <= Fb + 8192 -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> X a) ->
    rw_cells asegs m' A cs.
  Proof.
    intros CL SPA Fb X m m' A cs HC AG H1 H2 HX. eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. split; [| apply HX; exact Ha].
    right; right; left. apply Exists_cons_hd. cbn [fb_addr fb_size fst snd]. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fz_uc_keep : forall d L (CL : list cblk) SPA Fb (X : Z -> Prop) m m' (sp s0 ra : word) trC,
    ucallerA d L m sp s0 ra trC -> al_top L <= 2^47 -> agrees_on (fun a => client_keeps (FZFL Fb) CL SPA a /\ X a) m m' ->
    SPA <= bv_unsigned sp -> (forall a, bv_unsigned sp <= a -> X a) -> ucallerA d L m' sp s0 ra trC.
  Proof.
    intros d L CL SPA Fb X m m' sp s0 ra trC UC HT AG HS HX. eapply ucaller_keep; [exact UC| exact HT|].
    intros a Ha. apply (AG a); [pose proof (bv_unsigned_in_range 64 sp) as R; unfold bv_modulus in R; cbn in R; lia|].
    split; [left; lia| apply HX; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="FO GL"] Lemma hcoreA_keep0 : forall L RNG s CLg (CL : list cblk) FB sp tp lo SPA Fb sv fra m m',
    hcoreA L sp lo SPA Fb sv fra m -> GIOA L RNG s CLg FB (FZFL Fb) m ->
    hpureA L sp tp lo SPA -> cells_size fra = 56%nat -> cells_size sv = 104%nat ->
    agrees_on (client_keeps (FZFL Fb) CL SPA) m m' -> mem_inv asegs m' -> stk asegs m' lo SPA ->
    hcoreA L sp lo SPA Fb sv fra m'.
  Proof.
    intros L RNG s CLg CL FB sp tp lo SPA Fb sv fra m m' HC G HP FRAS SVS AG MI' ST'.
    eapply (hcoreA_keep _ _ _ CLg CL _ _ _ _ _ _ _ _ (fun _ => True)); [exact HC| exact G| exact HP| exact FRAS| exact SVS| | intros; exact I| exact MI'| exact ST'].
    eapply agrees_on_weaken; [exact AG| intros a [K _]; exact K].
  Qed.
  #[using="Type"] Lemma fz_local_keep0 : forall (CL : list cblk) SPA Fb m m' A cs,
    rw_cells asegs m A cs -> agrees_on (client_keeps (FZFL Fb) CL SPA) m m' ->
    Fb <= A -> A + Z.of_nat (cells_size cs) <= Fb + 8192 -> rw_cells asegs m' A cs.
  Proof.
    intros CL SPA Fb m m' A cs HC AG H1 H2. eapply (fz_local_keep CL SPA Fb (fun _ => True)); [exact HC| | exact H1| exact H2| intros; exact I].
    eapply agrees_on_weaken; [exact AG| intros a [K _]; exact K].
  Qed.
  #[using="Type"] Lemma fz_uc_keep0 : forall d L (CL : list cblk) SPA Fb m m' (sp s0 ra : word) trC,
    ucallerA d L m sp s0 ra trC -> al_top L <= 2^47 -> agrees_on (client_keeps (FZFL Fb) CL SPA) m m' ->
    SPA <= bv_unsigned sp -> ucallerA d L m' sp s0 ra trC.
  Proof.
    intros d L CL SPA Fb m m' sp s0 ra trC UC HT AG HS. eapply (fz_uc_keep d L CL SPA Fb (fun _ => True)); [exact UC| exact HT| | exact HS| intros; exact I].
    eapply agrees_on_weaken; [exact AG| intros a [K _]; exact K].
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma fz_ag_final : forall (CL : list cblk) SPA Fb (sp : word) m m',
    agrees_on (client_keeps (FZFL Fb) CL SPA) m m' -> SPA <= bv_unsigned sp -> agrees_on (client_keeps [] CL (bv_unsigned sp)) m m'.
  Proof. intros CL SPA Fb sp m m' AG HS. eapply client_keeps_weaken; [exact AG| exact HS| intros a Ha; exact Ha| intros fr0 []]. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fz_ucaller : forall d' L (sp tp s0 ra : word) lo SPA Fb sv fra m trC X (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : cell),
    ucallerA depth_fuzz_one L m sp s0 ra trC -> hpureA L sp tp lo SPA -> hcoreA L sp lo SPA Fb sv fra m ->
    sv = [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; C8 s0; C8 ra] -> cells_size [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] = 88%nat ->
    ACLIENT_LO <= X < ACLIENT_HI -> (S d' <= depth_fuzz_one)%nat ->
    ucallerA d' L m (Z_to_bv 64 SPA) sp (Z_to_bv 64 X) (bv_unsigned ra :: trC).
  Proof.
    intros d' L sp tp s0 ra lo SPA Fb sv fra m trC X c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 UC HP HC -> SZ HX HD.
    destruct HP as (SPAB & _ & LO & LOS & SPT & TOP47 & _ & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS.
    destruct HC as (_ & _ & _ & _ & FRs & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (E : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (rw_cells_nth_C8 _ _ _ 11%nat _ FRs eq_refl) as BS0. pose proof (rw_cells_nth_C8 _ _ _ 12%nat _ FRs eq_refl) as BRA.
    cbn [firstn] in BS0, BRA.
    change [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; C8 s0] with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ++ [C8 s0]) in BRA.
    rewrite cells_size_app, SZ in BRA. rewrite SZ in BS0. cbn [cells_size csize Nat.add] in BRA.
    eapply (ucaller_frame _ d' _ _ _ _ _ _ _ _ X UC); [rewrite E; lia| lia| Z.div_mod_to_equations; lia| | | reflexivity| exact HX| exact HD].
    - replace (bv_unsigned sp - 16) with (bv_unsigned sp + -104 + Z.of_nat 88) by lia. exact BS0.
    - replace (bv_unsigned sp - 8) with (bv_unsigned sp + -104 + Z.of_nat (88 + 8)) by lia. exact BRA.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma fz_cobj : forall L RNG s CLg (CL : list cblk) FB Fb m A n, GIOA L RNG s CLg FB (FZFL Fb) m ->
    Fb <= A -> A + n <= Fb + 8192 -> 0 <= n -> unpoisoned m A (A + n) -> cobjA RNG m (FZFL Fb) CL A n.
  Proof.
    intros L RNG s CLg CL FB Fb m A n G H1 H2 Hn UNP. destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. pose proof (Forall_inv FAll) as FRA.
    split.
    - right. exists (FF_FUZZ_ONE_INPUT, Fb, 8192). split; [left; reflexivity|]. cbn [fb_addr fb_size fst snd]. lia.
    - eapply frameA_aobj; [exact FRA| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| exact Hn| exact UNP].
  Qed.

  #[using="Type"] Lemma fz_unp_errbuf : forall m Fb, rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) SHA -> Fb mod 8 = 0 -> 0 <= Fb -> Fb + 8192 <= 2^47 ->
    unpoisoned m (Fb + 32) (Fb + 32 + 256).
  Proof.
    intros m Fb SA F8 F0 FT.
    pose proof (unp_of_sh_bytes m Fb SHA 4 32 SA F8 F0 ltac:(unfold SHA; cbn [cells_size csize Nat.add]; lia) ltac:(reflexivity) ltac:(unfold SHA; cbn; lia)) as U.
    replace (Fb + 8 * Z.of_nat 4) with (Fb + 32) in U by lia. replace (8 * Z.of_nat 32) with 256 in U by lia. exact U.
  Qed.
  #[using="Type"] Lemma fz_unp_fname : forall m Fb, rw_cells asegs m (Z.shiftr Fb 3 + 2147450924) SHB -> Fb mod 8 = 0 -> 0 <= Fb -> Fb + 8192 <= 2^47 ->
    unpoisoned m (Fb + 352) (Fb + 352 + 4096).
  Proof.
    intros m Fb SB F8 F0 FT.
    assert (E : Z.shiftr (Fb + 352) 3 + 2147450880 = Z.shiftr Fb 3 + 2147450924) by (replace (Fb + 352) with (Fb + 8 * 44) by lia; rewrite (shiftr3_add Fb 44 F8); lia).
    rewrite <- E in SB.
    pose proof (unp_of_sh_bytes m (Fb + 352) SHB 0 512 SB ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(unfold SHB; cbn [cells_size csize Nat.add]; lia)
                  ltac:(reflexivity) ltac:(unfold SHB; cbn; lia)) as U.
    replace (Fb + 352 + 8 * Z.of_nat 0) with (Fb + 352) in U by lia. replace (8 * Z.of_nat 512) with 4096 in U by lia. exact U.
  Qed.
  #[using="Type"] Lemma fz_unp_locals : forall m Fb, rw_cells asegs m (Z.shiftr Fb 3 + 2147451436) SHC -> Fb mod 8 = 0 -> 0 <= Fb -> Fb + 8192 <= 2^47 ->
    unpoisoned m (Fb + 4576) (Fb + 4576 + 8) /\ unpoisoned m (Fb + 4608) (Fb + 4608 + 8).
  Proof.
    intros m Fb SC F8 F0 FT.
    assert (E : Z.shiftr (Fb + 4448) 3 + 2147450880 = Z.shiftr Fb 3 + 2147451436) by (replace (Fb + 4448) with (Fb + 8 * 556) by lia; rewrite (shiftr3_add Fb 556 F8); lia).
    rewrite <- E in SC. split.
    - pose proof (unp_of_sh_bytes m (Fb + 4448) SHC 16 1 SC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(unfold SHC; cbn [cells_size csize Nat.add]; lia)
                    ltac:(reflexivity) ltac:(unfold SHC; cbn; lia)) as U.
      replace (Fb + 4448 + 8 * Z.of_nat 16) with (Fb + 4576) in U by lia. replace (8 * Z.of_nat 1) with 8 in U by lia. exact U.
    - pose proof (unp_of_sh_bytes m (Fb + 4448) SHC 20 1 SC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(unfold SHC; cbn [cells_size csize Nat.add]; lia)
                    ltac:(reflexivity) ltac:(unfold SHC; cbn; lia)) as U.
      replace (Fb + 4448 + 8 * Z.of_nat 20) with (Fb + 4608) in U by lia. replace (8 * Z.of_nat 1) with 8 in U by lia. exact U.
  Qed.
End FuzzKit.
End CANSEC1.

(* [comment removed for export] *)
Ltac hr_open HR :=
  let R1 := fresh "RSTK" in let R2 := fresh "RIMG" in let R3 := fresh "RISH" in let R4 := fresh "RTLS" in let R5 := fresh "RSPA" in
  pose proof HR as (R1 & R2 & R3 & R4);
  lazymatch type of R1 with rng ?RNG ?lo _ =>
    lazymatch goal with SPAB : (bv_unsigned ?sp - 191 <= ?SPA <= bv_unsigned ?sp - 160)%Z |- _ =>
      assert (R5 : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact R1| lia]) end end.
Ltac hr_next HR FP HR' :=
  pose proof (hrngA_le _ _ _ _ HR FP) as HR';
  lazymatch type of HR with hrngA _ ?RNG _ => repeat match goal with HX : rng RNG _ _ |- _ => clear HX end end;
  hr_open HR'.
End TwB.
End F_fuzz_kitA.
