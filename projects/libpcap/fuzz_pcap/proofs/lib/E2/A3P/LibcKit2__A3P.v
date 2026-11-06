(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge Frame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF Shadow StepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA LibcKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes Decode SysStep StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ITreeA SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG PcapRepA UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_iface_ngA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfHandleA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module LibcKit2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF Shadow StepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.I_asan_memset.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA LibcKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition asan_memset_specZ__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo Dst c n : Z) (junk : list byte),
  a0 = Z_to_bv 64 Dst -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n -> 0 <= c < 256 ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo + 2208 <= bv_unsigned sp -> ATOP + 4096 <= lo ->
  artcells m ->
  0 <= n <= 2^40 -> rw_cells asegs m Dst [CB (Z.to_nat n) junk] ->
  mobjA RNG m Dst n -> Dst + n <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Dst) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp); (Dst, Dst + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Dst [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x54e00) fc None m (seg_rom asegs)).
Section Sz1.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo Dst c n junk : ltac2:(SecDiet.SzSec.tyM 'asan_memset_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma asan_memset_specZ__body : ltac2:(SecDiet.SzSec.bodyP 'asan_memset_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros -> -> -> Hc MI ST BU LO RT Hn DST OD TD RIMG RSTK.
  destruct OD as (D0 & D47 & DUNP & DRNG & (RLO2 & RHI2 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28) & DAPP).
  destruct RT as (_ & GOT & GRIC & RMEM & SHB & _ & INI & LAY & _).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  assert (E0 : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (E1 : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evtF_mono.
  - eapply (asan_memset_spec RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 c) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo junk RLO2 RHI2); rewrite ?E0, ?E1, ?E2;
      first [ assumption | unfold KHIGH, KEND in *; lia | left; lia ].
  - cbv beta. intros ms' PO. unfold asan_memset_post in PO. rewrite ?E0, ?E1, ?E2 in PO. rewrite (Z.mod_small c 256) in PO by lia. exact PO.
Qed.
End Sz1.
#[using="Type"] Lemma asan_memset_specZ : ltac:(let t := eval cbv delta [asan_memset_specZ__stmt] in asan_memset_specZ__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo Dst c n junk. ltac2:(SecDiet.SzSec.closeP 'asan_memset_specZ__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.I_asan_memset.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition asan_memset_specZ__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo Dst c n : Z) (junk : list byte),
  a0 = Z_to_bv 64 Dst -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n -> 0 <= c < 256 ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo + 2208 <= bv_unsigned sp -> ATOP + 4096 <= lo ->
  artcells m ->
  0 <= n <= 2^40 -> rw_cells asegs m Dst [CB (Z.to_nat n) junk] ->
  mobjA RNG m Dst n -> Dst + n <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Dst) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp); (Dst, Dst + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Dst [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x54e68) fc None m (seg_rom asegs)).
Section Sz1.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo Dst c n junk : ltac2:(SecDiet.SzSec.tyM 'asan_memset_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma asan_memset_specZ__body : ltac2:(SecDiet.SzSec.bodyP 'asan_memset_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros -> -> -> Hc MI ST BU LO RT Hn DST OD TD RIMG RSTK.
  destruct OD as (D0 & D47 & DUNP & DRNG & (RLO2 & RHI2 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28) & DAPP).
  destruct RT as (_ & GOT & GRIC & RMEM & SHB & _ & INI & LAY & _).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  assert (E0 : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (E1 : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evtF_mono.
  - eapply (asan_memset_spec RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 c) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo junk RLO2 RHI2); rewrite ?E0, ?E1, ?E2;
      first [ assumption | unfold KHIGH, KEND in *; lia | left; lia ].
  - cbv beta. intros ms' PO. unfold asan_memset_post in PO. rewrite ?E0, ?E1, ?E2 in PO. rewrite (Z.mod_small c 256) in PO by lia. exact PO.
Qed.
End Sz1.
#[using="Type"] Lemma asan_memset_specZ : ltac:(let t := eval cbv delta [asan_memset_specZ__stmt] in asan_memset_specZ__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo Dst c n junk. ltac2:(SecDiet.SzSec.closeP 'asan_memset_specZ__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End LibcKit2.

(* [comment removed for export] *)
Module F_pcap_closeA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Local Ltac alia ::= lia.   (* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Freecode.
  Context {hptr : Type}.

  Definition pcap_freecode_specA__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (RNG : footprint) (lo P B NB : Z) (p : PcapTypes.pcap hptr hptr) (rf : cell) (j : pcap_junk),
    stk asegs m lo (bv_unsigned sp) -> (lo + 32 <= bv_unsigned sp)%Z -> (ATOP + 4096 <= lo)%Z -> mem_inv asegs m ->
    a0 = Z_to_bv 64 (P + 200) -> csize rf = 8%nat ->
    artcells m ->
    ablock_range P NB -> (0 < P)%Z -> (216 <= NB)%Z -> unpoisoned m P (P + NB) ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng RNG P NB -> rng RNG (shad P) (nshad NB) ->
    rw_cells asegs m P (pc_pre p P B rf j) ->
    evtF asegs RNG (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' f',
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (P + 200, P + 204)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (bv_unsigned sp)
        /\ unpoisoned m' P (P + NB)
        /\ rw_cells asegs m' P (pc_pre p P B rf (set_pj_f f' j)))   (* [comment removed for export] *)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PCAP_FREECODE_ENTRY) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo P B NB p rf j : ltac2:(SecDiet.SzSec.tyM 'pcap_freecode_specA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="Type"] Lemma pcap_freecode_specA__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_freecode_specA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros ST BU LO MI -> Hrf RT BR P0 NB1 UNP RSTK RIMG RP RSH CA.
 qfold.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    (nd_pre RT 6%nat; intros _ GOT _ _ SHB _; nd_post).
    (nd_pre BR 4%nat; intros BAND NB0 PTOP AL16; nd_post). band_ind BAND bP.
    unfold PCAP_FREECODE_ENTRY. unfold pc_pre, PCAP_PRIV_OFF in CA.
    destruct rf as [rv|rv|rv|rb|rn rbs]; try discriminate Hrf; [|cbn in Hrf; subst rn].
    all: pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (P + 200, P + 204)]%Z m) as MU; pose proof (wmono_refl asegs m) as WM.
    all: carve_frame 32%nat ST.
    all: do 7 zstep.
    all: ck0 UNP; ck_go.                                   (* [comment removed for export] *)
    all: do 2 zstep.
    all: ck0 UNP; ck_go.                                   (* [comment removed for export] *)
    all: do 2 zstep; if_true; do 5 zstep.
    all: release_frame FR ST (bv_unsigned sp).
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with CH : rw_cells _ mm ?PP ?cs, jj : pcap_junk |- _ =>
        let pre := eval cbn [firstn] in (firstn 21 cs) in
        pose proof (rw_cells_merge asegs mm PP pre [CB 40 (firstn 40 (pj_f jj)); C4 (Z_to_bv 64 0); CB 4 (skipn 44 (pj_f jj))] [C8 (Z_to_bv 64 0)] CH) as CH';
        cbn [app cells_size csize cells_bytes cbytes Nat.add] in CH';
        apply evtF_done; do 16 eexists; exists (firstn 40 (pj_f jj) ++ (le4 (Z_to_bv 64 0) ++ (skipn 44 (pj_f jj) ++ [])))
      end end.
    all: split; [reflexivity|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|].
    all: exact CH'.
  Qed.
  End Sz1.
  #[using="Type"] Lemma pcap_freecode_specA : ltac:(let t := eval cbv delta [pcap_freecode_specA__stmt] in pcap_freecode_specA__stmt in exact t).
  Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo P B NB p rf j. ltac2:(SecDiet.SzSec.closeP 'pcap_freecode_specA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Freecode.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Close.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  (* [comment removed for export] *)
  Hypothesis FCLOSE : fclose_stmt_o HO GIOA TP.
  Hypothesis FREE : free_stmt_o HO GIOA.

  Definition sf_cleanup_proofA__stmt : Prop := sf_cleanup_stmt HO FO sites GIOA TP.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc FB1 FB2 FL trC lo P B Af p j : ltac2:(SecDiet.SzSec.tyM 'sf_cleanup_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="fflagA GL FCLOSE FREE"] Lemma sf_cleanup_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'sf_cleanup_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros PRE UC TR NF CELLS -> NOF. (nd_pre TR 3%nat; intros TRC1 UTR _; nd_post).
 qfold.
    (nd_pre PRE 12%nat; intros G ST LO BU SPT MI TPE ALN RSTK RIMG RISH RTLS; nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as ndP__; nd_pre ndP__ 6%nat; intros (PBAND & P3 & PTOP & P2) P1 PUNP PRNG PRSH PAR; nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; right; left; reflexivity)) as ndP__; nd_pre ndP__ 6%nat; intros (BBAND & B3 & BTOP & B2) B1 BUNP BRNG BRSH BAR; nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity)) as ndP__; nd_pre ndP__ 3%nat; intros (FBAND & F3 & FTOP & F2) F1 _; nd_post).
    cbn [cb_addr cb_size fst snd] in *.
    (pose proof (gl_stdin _ _ _ GL _ _ _ _ _ _ _ G) as ndP__; nd_pre ndP__ 3%nat; intros GOT1 GOT2 SUNP; nd_post). unfold GOT_STDIN, STDIN_P, STDIN_FILE in GOT1, GOT2, SUNP.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & _) & _).
    pose proof (psize_pos p) as PS. unfold PCAP_L3_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    band_ind PBAND bP. band_ind BBAND bB. band_ind FBAND bF.
    unfold pcap_cells in CELLS. apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    unfold pc_pre, PCAP_PRIV_OFF in CA. unfold hdr_cells in CH. unfold pc_ops in CO.
    unfold Pcap.pcapint_sf_cleanup. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret prims e_fclose e_free prims]. unfold PK; cbn [pk_cleanup_sf].
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    carve_frame 32%nat ST.
    do 9 zstep.
    ck0 PUNP; ck_go.                      (* [comment removed for export] *)
    do 2 zstep.
    ck0 SUNP; ck_go.                      (* [comment removed for export] *)
    do 3 zstep. if_false_by (eqb_lits_false Af 0xa9ba0 ltac:(lia) ltac:(lia) ltac:(lia)).
    zstep.
    (* [comment removed for export] *)
    assert (KP : forall (CL : list cblock) SP mA mB A cs, In (pc_self p, P, psize p) CL -> agrees_on (client_keeps FL CL SP) mA mB ->
              rw_cells asegs mA A cs -> (P <= A)%Z -> (A + Z.of_nat (cells_size cs) <= P + psize p)%Z -> rw_cells asegs mB A cs).
    { intros CL SP mA mB A cs Hin AG HC HA HB. eapply keeps_rw_cells_block; [exact AG | exact HC |].
      intros a Ha. apply in_block_In. exists (pc_self p, P, psize p). split; [exact Hin| cbn [cb_addr cb_size fst snd]; lia]. }
    assert (HinP : In (pc_self p, P, psize p) (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)])) by (apply in_or_app; right; left; reflexivity).
    assert (HinP' : In (pc_self p, P, psize p) (CLc ++ [(pc_self p, P, psize p)])) by (apply in_or_app; right; left; reflexivity).
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW : Forall (pcap_iv FL [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) [(bv_unsigned sp + -32, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) (FB1 ++ (pc_rfile p, Af, FILE_BLOCK) :: FB2) FL mm)
        by (eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FW]);
      assert (AGa : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    clear MU WM.
    name_sp sp (-32)%Z.
    apply evtF_done. eapply implMG_bind.
    { eapply FCLOSE; [| eapply (ucaller_data _ _ _ _ _ _ 0x84c9c%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | first [lia | cbv; lia]]
                      | exact TRC1 | reflexivity | exact NOF].
      split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    intros [] s' RNG1 ms' PO. cbv beta in PO. (nd_pre PO 9%nat; intros FP1 av1 m2 E OF1 MI1 ST1 AG1 G1; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 543900)) with (Z_to_bv 64 543900) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
    clear PUNP BUNP.
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G1 ltac:(apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ PUNP _; nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G1 ltac:(apply in_or_app; left; apply in_or_app; right; right; left; reflexivity)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ BUNP _; nd_post).
    cbn [cb_addr cb_size fst snd] in PUNP, BUNP.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia].
    apply (KP _ _ _ _ _ _ HinP AG1) in CA; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP AG1) in CE; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP AG1) in CH; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP AG1) in CO; [|lia|cbn [cells_size csize Nat.add]; lia].
    clear MI.
    (* [comment removed for export] *)
    ienterG. zstep.
    ck0 PUNP; ck_go.                      (* [comment removed for export] *)
    do 2 zstep. if_false_by (eqz_false B ltac:(lia)). zstep.
    replace (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) with ((CLc ++ [(pc_self p, P, psize p)]) ++ [(pc_buffer p, B, pc_bufalloc p)]) in G1
      by (rewrite <- app_assoc; reflexivity).
    name_sp sp (-32)%Z.
    apply evtF_done. eapply implMG_post_evtF.
    { eapply FREE; [|reflexivity|].
      - split; [exact G1|]. split; [rewrite Hsp; exact ST1|]. split; [lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
        split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS].
      - eapply unw_of_ucaller; [eapply (ucaller_data 0%nat _ _ _ _ _ 0x84cbc%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | first [lia | cbv; lia]]
                               | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite Hsp; lia | rewrite unsigned_lit by lia; exact UTR | exact RSTK]. }
    intros [] s'' RNG2 ms'' PO. cbv beta in PO. (nd_pre PO 9%nat; intros FP2 av2 m3 E OF2 MI2 ST2 AG2 G2; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms''. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 543932)) with (Z_to_bv 64 543932) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite app_nil_r in AG2, G2.
    repeat match goal with HR : rng RNG1 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
    clear PUNP BUNP.
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 ltac:(apply in_or_app; left; exact HinP')) as ndP__; nd_pre ndP__ 6%nat; intros PBR _ PUNP PRNG2 PRSH2 _; nd_post).
    cbn [cb_addr cb_size fst snd] in PBR, PUNP, PRNG2, PRSH2.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G2) as RT2.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG2) in FR; [|lia].
    apply (KP _ _ _ _ _ _ HinP' AG2) in CA; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP' AG2) in CE; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP' AG2) in CH; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP' AG2) in CO; [|lia|cbn [cells_size csize Nat.add]; lia].
    clear MI1.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (P + 200, P + 204)]%Z m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
    do 6 zstep.
    release_frame FR ST2 (bv_unsigned sp).
    unfold PCAP_FREECODE_ENTRY.
    call (pcap_freecode_specA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo P B (psize p) p (C8 (Z_to_bv 64 Af)) j).
    1-12: [> exact ST2 | lia | lia | assumption | reflexivity | reflexivity | exact (proj1 RT2) | exact PBR | lia | lia | exact PUNP | exact CA ].
    (* [comment removed for export] *)
    assert (WK : forall (CL : list cblock) mA mB, agrees_on (client_keeps FL (CLc ++ CL) (bv_unsigned sp + -32)) mA mB ->
                 agrees_on (client_keeps FL CLc (bv_unsigned sp)) mA mB).
    { intros CL mA mB AG. eapply client_keeps_weaken; [exact AG | lia | intros a Ha; apply in_block_app; left; exact Ha | intros a Ha; exact Ha]. }
    apply WK in AG1. apply WK in AG2. clear WK.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AG3 : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m3 mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G2 | exact MU3 | exact WM3 | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia|];
            apply Forall_cons; [right; left; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia| apply Forall_nil]);
      assert (FW3 : Forall (pcap_iv FL [(pc_self p, P, psize p)]) [(bv_unsigned sp - 32, bv_unsigned sp); (P + 200, P + 204)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia|];
            apply Forall_cons; [right; left; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia| apply Forall_nil]);
      lazymatch goal with HCA : rw_cells _ mm P (pc_pre _ _ _ _ ?jj) |- _ =>
        pose proof (pcap_cells_join4 mm P p B (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jj _ (pc_header p)
                      eq_refl HCA CE eq_refl CH CO) as J;
        replace (set_header (pc_header p) p) with p in J by (destruct p; reflexivity)
      end;
      apply evtF_done; subst POSTQ0 POSTQ; unfold cleanup_post
    end.
    split; [eapply fp_le_trans; [exact FP1| exact FP2]|].
    lazymatch goal with |- context [MS (mkR _ _ _ _ _ _ _ _ _ ?av _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?mm _] =>
      lazymatch type of J with rw_cells _ _ _ (pcap_cells_gen _ _ _ _ _ _ ?jj) => exists av, mm, jj end end.
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [rewrite OF2; exact OF1|]. split; [assumption|]. split; [assumption|].
    split. { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_trans; [exact AG1|]. eapply agrees_on_trans; [exact AG2| exact AG3]. }
    split. { eapply (gl_frame _ _ _ GL); [exact G2 | exact MU3 | exact WM3 | exact FW3]. }
    exact J.
  Qed.
  End Sz2.
  #[using="fflagA GL FCLOSE FREE"] Theorem sf_cleanup_proofA : ltac:(let t := eval cbv delta [sf_cleanup_proofA__stmt] in sf_cleanup_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc FB1 FB2 FL trC lo P B Af p j. ltac2:(SecDiet.SzSec.closeP 'sf_cleanup_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Hypothesis NGC : ng_cleanup_stmt HO FO sites GIOA TP.

  Definition pcap_close_proofA__stmt : Prop := pcap_close_stmt HO FO sites GIOA TP.
  Section Sz3.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P p : ltac2:(SecDiet.SzSec.tyM 'pcap_close_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="fflagA GL FCLOSE FREE NGC"] Lemma pcap_close_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_close_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros PRE UC TR NF PC -> NOF. (nd_pre TR 4%nat; intros TRS TRN _ UTRT; nd_post).
 qfold.
    (nd_pre PRE 12%nat; intros G ST LO BU SPT MI TPE ALN RSTK RIMG RISH RTLS; nd_post).
    (pose proof PC as ndP__; nd_pre ndP__ 3%nat; intros Af HinF (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF); nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; rewrite EPB; left; reflexivity)) as ndP__; nd_pre ndP__ 6%nat; intros (PBAND & P3 & PTOP & P2) P1 PUNP PRNG PRSH PAR; nd_post).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & _) & _).
    pose proof (psize_pos p) as PS. unfold PCAP_L4_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    band_ind PBAND bP.
    (nd_pre (in_split _ _ HinF) 3%nat; intros FB1 FB2 EFB; nd_post).
    unfold pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF in CELLS. cbn [app] in CELLS.
    clear PRIV BUF PFX IFS.
    assert (HinP : In (pc_self p, P, psize p) (CLc ++ [(pc_self p, P, psize p)])) by (apply in_or_app; right; left; reflexivity).
    unfold Pcap.pcap_close. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret prims e_free prims]. unfold PCAP_CLOSE_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    (* [comment removed for export] *)
    assert (CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : mem) (ps2 : PState H hptr) (RNG2 : footprint) FB1' FB2' Af' B' j',
      FB = FB1' ++ (pc_rfile p, Af', FILE_BLOCK) :: FB2' -> fp_le RNG RNG2 ->
      mem_inv asegs m2 -> stk asegs m2 lo (bv_unsigned sp + -32) -> agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m2 ->
      GIOA L RNG2 ps2 (CLc ++ [(pc_self p, P, psize p)]) (FB1' ++ FB2') FL m2 ->
      rw_cells asegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] -> rw_cells asegs m2 P (pcap_cells p P B' Af' j') -> ps_outfile ps2 = ps_outfile s ->
      implMG RNG2 (pfree HO (pc_self p)) ps2 POSTQ
        (MS (mkR (Z_to_bv 64 0x85c70) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1' t2' (Z_to_bv 64 P) s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x85c70) fc None m2 (seg_rom asegs))).
    { intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 ps2 RNG2 FB1' FB2' Af' B' j' EFB' FP2 MI2 ST2 AG2 G2 FR2 CELLS2 OF2.
      clear CELLS MU WM MI G ST PUNP GOT SHB.
      repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 ltac:(apply in_or_app; left; exact HinP)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ PUNP _; nd_post). cbn [cb_addr cb_size fst snd] in PUNP.
      unfold pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF in CELLS2. cbn [app] in CELLS2.
      apply implMG_from_evtF. zstep.
      ck0 PUNP; ck_go.                    (* [comment removed for export] *)
      do 2 zstep. if_true. do 7 zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evtF_done. eapply implMG_mono.
      { unfold free_stmt_o in FREE. eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CLc [] _ FL); [|reflexivity|].
        - split; [exact G2|]. split; [exact ST2|]. split; [lia|]. split; [unfold FREE_STACK; lia|].
          split; [lia|]. split; [assumption|]. split; [exact TPE|]. split; [exact ALN|].
          split; [eapply rng_sub'; [exact RSTK| lia]|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS].
        - eapply unw_of_ucaller; [eapply ucaller_keep; [exact UC | lia |] | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | lia | exact UTRT | eapply rng_sub'; [exact RSTK| lia]].
          intros a Ha. destruct (AG2 a ltac:(lia) ltac:(left; lia)) as [E _]. exact E. }
      cbv beta. intros [] ps3 RNG3 ms3 PO. subst POSTQ. unfold pcap_post.
      (nd_pre PO 9%nat; intros FP3 a0v m' E OF' MI' ST' AG' G'; nd_post). rewrite app_nil_r in AG'.
      split; [eapply fp_le_trans; [exact FP2| exact FP3]|].
      exists a0v, m', [], (FB1' ++ FB2'). split; [exact E|]. split; [exact MI'|]. split; [exact ST'|].
      split; [eapply agrees_on_trans; [exact AG2| exact AG']|]. split; [exact G'|]. split; [rewrite OF'; exact OF2|]. split; [reflexivity|].
      exists FB1', FB2', Af'. split; [exact EFB'| reflexivity]. }
    carve_frame 32%nat ST.
    do 10 zstep.
    ck0 PUNP; ck_go.                      (* [comment removed for export] *)
    do 3 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW : Forall (pcap_iv FL PB) [(bv_unsigned sp + -32, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s (CLc ++ PB) FB FL mm) by (eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FW]);
      assert (AG0 : agrees_on (fun a => outside [(bv_unsigned sp + -32, bv_unsigned sp)]%Z a) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      assert (PC0 : PCAPR_closable P p PB FB mm)
        by (eapply PCAPR_closable_agree; [exact AG0 | intros a Ha; pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)); cbn [outside]; lia | exact PC]);
      assert (AGa : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    clear MU WM AG0.
    assert (WK : forall (CL : list cblock) mA mB, agrees_on (client_keeps FL (CLc ++ CL) (bv_unsigned sp + -32)) mA mB ->
                 agrees_on (client_keeps FL CLc (bv_unsigned sp)) mA mB).
    { intros CL mA mB AG. eapply client_keeps_weaken; [exact AG | lia | intros a Ha; apply in_block_app; left; exact Ha | intros a Ha; exact Ha]. }
    (* [comment removed for export] *)
    unfold pcap_blocks in EPB. unfold cleanup_entry, is_ng, PK. cbn [pk_cleanup_ng pk_cleanup_sf].
    destruct (pc_priv p) as [sf|sg oq] eqn:EP.
    - (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 543808)) with (Z_to_bv 64 (pk_cleanup_sf PK)) by (symmetry; apply ret_pc_even; [cbn; lia|reflexivity]).
      rewrite EPB, EFB in G0.
      name_sp sp (-32)%Z.
      apply evtF_done. eapply implMG_bind.
      { eapply sf_cleanup_proofA; [| eapply (ucaller_data _ _ _ _ _ _ 0x85c70%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | first [lia | cbv; lia]]
                                  | rewrite unsigned_lit by lia; exact TRS | intros f [] | exact CELLS | reflexivity | exact NOF].
        split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [lia|]. split; [unfold PCAP_L3_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
        split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
      intros [] s' RNG1 ms' PO. unfold cleanup_post in PO. (nd_pre PO 11%nat; intros FP1 av1 m2 j' E OF1 MI1 ST1 AG1 G1 HC1; nd_post).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x85c70)) with (Z_to_bv 64 0x85c70) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      eapply CONT; [exact EFB | exact FP1 | exact MI1 | exact ST1 | eapply agrees_on_trans; [exact AGa| apply (WK []); rewrite app_nil_r; exact AG1] | exact G1
             | eapply keeps_rw_cells_stack; [exact AG1 | exact FR | lia] | exact HC1 | exact OF1].
    - (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 580688)) with (Z_to_bv 64 (pk_cleanup_ng PK)) by (symmetry; apply ret_pc_even; [cbn; lia|reflexivity]).
      name_sp sp (-32)%Z.
      apply evtF_done. eapply implMG_bind.
      { eapply NGC; [| eapply (ucaller_data _ _ _ _ _ _ 0x85c70%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | first [lia | cbv; lia]]
                    | rewrite unsigned_lit by lia; exact TRN | intros f [] | exact PC0 | unfold is_ng; rewrite EP; reflexivity | reflexivity | exact NOF].
        split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [lia|]. split; [unfold PCAP_L3_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
        split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
      intros [] s' RNG1 ms' PO. cbv beta in PO. (nd_pre PO 7%nat; intros _ B' Af' FB1' FB2' EFB' PO; nd_post). unfold cleanup_post in PO.
      (nd_pre PO 11%nat; intros FP1 av1 m2 j' E OF1 MI1 ST1 AG1 G1 HC1; nd_post).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x85c70)) with (Z_to_bv 64 0x85c70) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      eapply CONT; [exact EFB' | exact FP1 | exact MI1 | exact ST1 | eapply agrees_on_trans; [exact AGa| apply (WK []); rewrite app_nil_r; exact AG1] | exact G1
             | eapply keeps_rw_cells_stack; [exact AG1 | exact FR | lia] | exact HC1 | exact OF1].
  Qed.
  End Sz3.
  #[using="fflagA GL FCLOSE FREE NGC"] Theorem pcap_close_proofA : ltac:(let t := eval cbv delta [pcap_close_proofA__stmt] in pcap_close_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P p. ltac2:(SecDiet.SzSec.closeP 'pcap_close_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Close.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Local Ltac alia ::= lia.   (* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Freecode.
  Context {hptr : Type}.

  Definition pcap_freecode_specA__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (RNG : footprint) (lo P B NB : Z) (p : PcapTypes.pcap hptr hptr) (rf : cell) (j : pcap_junk),
    stk asegs m lo (bv_unsigned sp) -> (lo + 32 <= bv_unsigned sp)%Z -> (ATOP + 4096 <= lo)%Z -> mem_inv asegs m ->
    a0 = Z_to_bv 64 (P + 200) -> csize rf = 8%nat ->
    artcells m ->
    ablock_range P NB -> (0 < P)%Z -> (216 <= NB)%Z -> unpoisoned m P (P + NB) ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng RNG P NB -> rng RNG (shad P) (nshad NB) ->
    rw_cells asegs m P (pc_pre p P B rf j) ->
    evtF asegs RNG (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' f',
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (P + 200, P + 204)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (bv_unsigned sp)
        /\ unpoisoned m' P (P + NB)
        /\ rw_cells asegs m' P (pc_pre p P B rf (set_pj_f f' j)))   (* [comment removed for export] *)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PCAP_FREECODE_ENTRY) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo P B NB p rf j : ltac2:(SecDiet.SzSec.tyM 'pcap_freecode_specA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="Type"] Lemma pcap_freecode_specA__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_freecode_specA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros ST BU LO MI -> Hrf RT BR P0 NB1 UNP RSTK RIMG RP RSH CA.
 qfold.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    (nd_pre RT 6%nat; intros _ GOT _ _ SHB _; nd_post).
    (nd_pre BR 4%nat; intros BAND NB0 PTOP AL16; nd_post). band_ind BAND bP.
    unfold PCAP_FREECODE_ENTRY. unfold pc_pre, PCAP_PRIV_OFF in CA.
    destruct rf as [rv|rv|rv|rb|rn rbs]; try discriminate Hrf; [|cbn in Hrf; subst rn].
    all: pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (P + 200, P + 204)]%Z m) as MU; pose proof (wmono_refl asegs m) as WM.
    all: carve_frame 32%nat ST.
    all: do 4 zstep.
    all: ub_null.                                          (* [comment removed for export] *)
    all: zstep; ub_al 7%Z ltac:(al16 AL16).
    all: zstep; if_false.
    all: do 3 zstep.
    all: ck0 UNP; ck_go.                                   (* [comment removed for export] *)
    all: do 2 zstep.
    all: ck0 UNP; ck_go.                                   (* [comment removed for export] *)
    all: do 2 zstep; if_true; do 5 zstep.
    all: release_frame FR ST (bv_unsigned sp).
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with CH : rw_cells _ mm ?PP ?cs, jj : pcap_junk |- _ =>
        let pre := eval cbn [firstn] in (firstn 21 cs) in
        pose proof (rw_cells_merge asegs mm PP pre [CB 40 (firstn 40 (pj_f jj)); C4 (Z_to_bv 64 0); CB 4 (skipn 44 (pj_f jj))] [C8 (Z_to_bv 64 0)] CH) as CH';
        cbn [app cells_size csize cells_bytes cbytes Nat.add] in CH';
        apply evtF_done; do 16 eexists; exists (firstn 40 (pj_f jj) ++ (le4 (Z_to_bv 64 0) ++ (skipn 44 (pj_f jj) ++ [])))
      end end.
    all: split; [reflexivity|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|].
    all: exact CH'.
  Qed.
  End Sz1.
  #[using="Type"] Lemma pcap_freecode_specA : ltac:(let t := eval cbv delta [pcap_freecode_specA__stmt] in pcap_freecode_specA__stmt in exact t).
  Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo P B NB p rf j. ltac2:(SecDiet.SzSec.closeP 'pcap_freecode_specA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Freecode.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Close.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  (* [comment removed for export] *)
  Hypothesis FCLOSE : fclose_stmt_o HO GIOA TP.
  Hypothesis FREE : free_stmt_o HO GIOA.

  Definition sf_cleanup_proofA__stmt : Prop := sf_cleanup_stmt HO FO sites GIOA TP.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc FB1 FB2 FL trC lo P B Af p j : ltac2:(SecDiet.SzSec.tyM 'sf_cleanup_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="fflagA GL FCLOSE FREE"] Lemma sf_cleanup_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'sf_cleanup_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros PRE UC TR NF CELLS -> NOF. (nd_pre TR 3%nat; intros TRC1 UTR _; nd_post).
 qfold.
    (nd_pre PRE 12%nat; intros G ST LO BU SPT MI TPE ALN RSTK RIMG RISH RTLS; nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as ndP__; nd_pre ndP__ 6%nat; intros (PBAND & P3 & PTOP & P2) P1 PUNP PRNG PRSH PAR; nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; right; left; reflexivity)) as ndP__; nd_pre ndP__ 6%nat; intros (BBAND & B3 & BTOP & B2) B1 BUNP BRNG BRSH BAR; nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity)) as ndP__; nd_pre ndP__ 3%nat; intros (FBAND & F3 & FTOP & F2) F1 _; nd_post).
    cbn [cb_addr cb_size fst snd] in *.
    (pose proof (gl_stdin _ _ _ GL _ _ _ _ _ _ _ G) as ndP__; nd_pre ndP__ 3%nat; intros GOT1 GOT2 SUNP; nd_post). unfold GOT_STDIN, STDIN_P, STDIN_FILE in GOT1, GOT2, SUNP.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & _) & _).
    pose proof (psize_pos p) as PS. unfold PCAP_L3_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    band_ind PBAND bP. band_ind BBAND bB. band_ind FBAND bF.
    unfold pcap_cells in CELLS. apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    unfold pc_pre, PCAP_PRIV_OFF in CA. unfold hdr_cells in CH. unfold pc_ops in CO.
    unfold Pcap.pcapint_sf_cleanup. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret prims e_fclose e_free prims]. unfold PK; cbn [pk_cleanup_sf].
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    carve_frame 32%nat ST.
    do 4 zstep. ub_null.                  (* [comment removed for export] *)
    do 2 zstep. ub_al 7%Z ltac:(al16 P2). zstep. if_false.
    do 4 zstep.
    ck0 PUNP; ck_go.                      (* [comment removed for export] *)
    do 2 zstep.
    ck0 SUNP; ck_go.                      (* [comment removed for export] *)
    do 3 zstep. if_false_by (eqb_lits_false Af 0xa9f80 ltac:(lia) ltac:(lia) ltac:(lia)).
    zstep.
    (* [comment removed for export] *)
    assert (KP : forall (CL : list cblock) SP mA mB A cs, In (pc_self p, P, psize p) CL -> agrees_on (client_keeps FL CL SP) mA mB ->
              rw_cells asegs mA A cs -> (P <= A)%Z -> (A + Z.of_nat (cells_size cs) <= P + psize p)%Z -> rw_cells asegs mB A cs).
    { intros CL SP mA mB A cs Hin AG HC HA HB. eapply keeps_rw_cells_block; [exact AG | exact HC |].
      intros a Ha. apply in_block_In. exists (pc_self p, P, psize p). split; [exact Hin| cbn [cb_addr cb_size fst snd]; lia]. }
    assert (HinP : In (pc_self p, P, psize p) (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)])) by (apply in_or_app; right; left; reflexivity).
    assert (HinP' : In (pc_self p, P, psize p) (CLc ++ [(pc_self p, P, psize p)])) by (apply in_or_app; right; left; reflexivity).
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW : Forall (pcap_iv FL [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) [(bv_unsigned sp + -32, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) (FB1 ++ (pc_rfile p, Af, FILE_BLOCK) :: FB2) FL mm)
        by (eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FW]);
      assert (AGa : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    clear MU WM.
    name_sp sp (-32)%Z.
    apply evtF_done. eapply implMG_bind.
    { eapply FCLOSE; [| eapply (ucaller_data _ _ _ _ _ _ 0x84d34%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | first [lia | cbv; lia]]
                      | exact TRC1 | reflexivity | exact NOF].
      split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    intros [] s' RNG1 ms' PO. cbv beta in PO. (nd_pre PO 9%nat; intros FP1 av1 m2 E OF1 MI1 ST1 AG1 G1; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 544052)) with (Z_to_bv 64 544052) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
    clear PUNP BUNP.
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G1 ltac:(apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ PUNP _; nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G1 ltac:(apply in_or_app; left; apply in_or_app; right; right; left; reflexivity)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ BUNP _; nd_post).
    cbn [cb_addr cb_size fst snd] in PUNP, BUNP.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia].
    apply (KP _ _ _ _ _ _ HinP AG1) in CA; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP AG1) in CE; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP AG1) in CH; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP AG1) in CO; [|lia|cbn [cells_size csize Nat.add]; lia].
    clear MI.
    (* [comment removed for export] *)
    ienterG. zstep.
    ck0 PUNP; ck_go.                      (* [comment removed for export] *)
    do 2 zstep. if_false_by (eqz_false B ltac:(lia)). zstep.
    replace (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) with ((CLc ++ [(pc_self p, P, psize p)]) ++ [(pc_buffer p, B, pc_bufalloc p)]) in G1
      by (rewrite <- app_assoc; reflexivity).
    name_sp sp (-32)%Z.
    apply evtF_done. eapply implMG_post_evtF.
    { eapply FREE; [|reflexivity|].
      - split; [exact G1|]. split; [rewrite Hsp; exact ST1|]. split; [lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
        split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS].
      - eapply unw_of_ucaller; [eapply (ucaller_data 0%nat _ _ _ _ _ 0x84d54%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | first [lia | cbv; lia]]
                               | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite Hsp; lia | rewrite unsigned_lit by lia; exact UTR | exact RSTK]. }
    intros [] s'' RNG2 ms'' PO. cbv beta in PO. (nd_pre PO 9%nat; intros FP2 av2 m3 E OF2 MI2 ST2 AG2 G2; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms''. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 544084)) with (Z_to_bv 64 544084) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite app_nil_r in AG2, G2.
    repeat match goal with HR : rng RNG1 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
    clear PUNP BUNP.
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 ltac:(apply in_or_app; left; exact HinP')) as ndP__; nd_pre ndP__ 6%nat; intros PBR _ PUNP PRNG2 PRSH2 _; nd_post).
    cbn [cb_addr cb_size fst snd] in PBR, PUNP, PRNG2, PRSH2.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G2) as RT2.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG2) in FR; [|lia].
    apply (KP _ _ _ _ _ _ HinP' AG2) in CA; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP' AG2) in CE; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP' AG2) in CH; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP' AG2) in CO; [|lia|cbn [cells_size csize Nat.add]; lia].
    clear MI1.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (P + 200, P + 204)]%Z m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
    do 6 zstep.
    release_frame FR ST2 (bv_unsigned sp).
    unfold PCAP_FREECODE_ENTRY.
    call (pcap_freecode_specA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo P B (psize p) p (C8 (Z_to_bv 64 Af)) j).
    1-12: [> exact ST2 | lia | lia | assumption | reflexivity | reflexivity | exact (proj1 RT2) | exact PBR | lia | lia | exact PUNP | exact CA ].
    (* [comment removed for export] *)
    assert (WK : forall (CL : list cblock) mA mB, agrees_on (client_keeps FL (CLc ++ CL) (bv_unsigned sp + -32)) mA mB ->
                 agrees_on (client_keeps FL CLc (bv_unsigned sp)) mA mB).
    { intros CL mA mB AG. eapply client_keeps_weaken; [exact AG | lia | intros a Ha; apply in_block_app; left; exact Ha | intros a Ha; exact Ha]. }
    apply WK in AG1. apply WK in AG2. clear WK.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AG3 : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m3 mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G2 | exact MU3 | exact WM3 | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia|];
            apply Forall_cons; [right; left; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia| apply Forall_nil]);
      assert (FW3 : Forall (pcap_iv FL [(pc_self p, P, psize p)]) [(bv_unsigned sp - 32, bv_unsigned sp); (P + 200, P + 204)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia|];
            apply Forall_cons; [right; left; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia| apply Forall_nil]);
      lazymatch goal with HCA : rw_cells _ mm P (pc_pre _ _ _ _ ?jj) |- _ =>
        pose proof (pcap_cells_join4 mm P p B (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jj _ (pc_header p)
                      eq_refl HCA CE eq_refl CH CO) as J;
        replace (set_header (pc_header p) p) with p in J by (destruct p; reflexivity)
      end;
      apply evtF_done; subst POSTQ0 POSTQ; unfold cleanup_post
    end.
    split; [eapply fp_le_trans; [exact FP1| exact FP2]|].
    lazymatch goal with |- context [MS (mkR _ _ _ _ _ _ _ _ _ ?av _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?mm _] =>
      lazymatch type of J with rw_cells _ _ _ (pcap_cells_gen _ _ _ _ _ _ ?jj) => exists av, mm, jj end end.
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [rewrite OF2; exact OF1|]. split; [assumption|]. split; [assumption|].
    split. { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_trans; [exact AG1|]. eapply agrees_on_trans; [exact AG2| exact AG3]. }
    split. { eapply (gl_frame _ _ _ GL); [exact G2 | exact MU3 | exact WM3 | exact FW3]. }
    exact J.
  Qed.
  End Sz2.
  #[using="fflagA GL FCLOSE FREE"] Theorem sf_cleanup_proofA : ltac:(let t := eval cbv delta [sf_cleanup_proofA__stmt] in sf_cleanup_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc FB1 FB2 FL trC lo P B Af p j. ltac2:(SecDiet.SzSec.closeP 'sf_cleanup_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Hypothesis NGC : ng_cleanup_stmt HO FO sites GIOA TP.

  Definition pcap_close_proofA__stmt : Prop := pcap_close_stmt HO FO sites GIOA TP.
  Section Sz3.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P p : ltac2:(SecDiet.SzSec.tyM 'pcap_close_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="fflagA GL FCLOSE FREE NGC"] Lemma pcap_close_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_close_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros PRE UC TR NF PC -> NOF. (nd_pre TR 4%nat; intros TRS TRN _ UTRT; nd_post).
 qfold.
    (nd_pre PRE 12%nat; intros G ST LO BU SPT MI TPE ALN RSTK RIMG RISH RTLS; nd_post).
    (pose proof PC as ndP__; nd_pre ndP__ 3%nat; intros Af HinF (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF); nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; rewrite EPB; left; reflexivity)) as ndP__; nd_pre ndP__ 6%nat; intros (PBAND & P3 & PTOP & P2) P1 PUNP PRNG PRSH PAR; nd_post).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & _) & _).
    pose proof (psize_pos p) as PS. unfold PCAP_L4_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    band_ind PBAND bP.
    (nd_pre (in_split _ _ HinF) 3%nat; intros FB1 FB2 EFB; nd_post).
    unfold pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF in CELLS. cbn [app] in CELLS.
    clear PRIV BUF PFX IFS.
    assert (HinP : In (pc_self p, P, psize p) (CLc ++ [(pc_self p, P, psize p)])) by (apply in_or_app; right; left; reflexivity).
    unfold Pcap.pcap_close. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret prims e_free prims]. unfold PCAP_CLOSE_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    (* [comment removed for export] *)
    assert (CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : mem) (ps2 : PState H hptr) (RNG2 : footprint) FB1' FB2' Af' B' j',
      FB = FB1' ++ (pc_rfile p, Af', FILE_BLOCK) :: FB2' -> fp_le RNG RNG2 ->
      mem_inv asegs m2 -> stk asegs m2 lo (bv_unsigned sp + -32) -> agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m2 ->
      GIOA L RNG2 ps2 (CLc ++ [(pc_self p, P, psize p)]) (FB1' ++ FB2') FL m2 ->
      rw_cells asegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] -> rw_cells asegs m2 P (pcap_cells p P B' Af' j') -> ps_outfile ps2 = ps_outfile s ->
      implMG RNG2 (pfree HO (pc_self p)) ps2 POSTQ
        (MS (mkR (Z_to_bv 64 0x85dcc) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1' t2' (Z_to_bv 64 P) s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x85dcc) fc None m2 (seg_rom asegs))).
    { intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 ps2 RNG2 FB1' FB2' Af' B' j' EFB' FP2 MI2 ST2 AG2 G2 FR2 CELLS2 OF2.
      clear CELLS MU WM MI G ST PUNP GOT SHB.
      repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 ltac:(apply in_or_app; left; exact HinP)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ PUNP _; nd_post). cbn [cb_addr cb_size fst snd] in PUNP.
      unfold pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF in CELLS2. cbn [app] in CELLS2.
      apply implMG_from_evtF. zstep.
      ck0 PUNP; ck_go.                    (* [comment removed for export] *)
      do 2 zstep. if_true. do 7 zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evtF_done. eapply implMG_mono.
      { unfold free_stmt_o in FREE. eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CLc [] _ FL); [|reflexivity|].
        - split; [exact G2|]. split; [exact ST2|]. split; [lia|]. split; [unfold FREE_STACK; lia|].
          split; [lia|]. split; [assumption|]. split; [exact TPE|]. split; [exact ALN|].
          split; [eapply rng_sub'; [exact RSTK| lia]|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS].
        - eapply unw_of_ucaller; [eapply ucaller_keep; [exact UC | lia |] | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | lia | exact UTRT | eapply rng_sub'; [exact RSTK| lia]].
          intros a Ha. destruct (AG2 a ltac:(lia) ltac:(left; lia)) as [E _]. exact E. }
      cbv beta. intros [] ps3 RNG3 ms3 PO. subst POSTQ. unfold pcap_post.
      (nd_pre PO 9%nat; intros FP3 a0v m' E OF' MI' ST' AG' G'; nd_post). rewrite app_nil_r in AG'.
      split; [eapply fp_le_trans; [exact FP2| exact FP3]|].
      exists a0v, m', [], (FB1' ++ FB2'). split; [exact E|]. split; [exact MI'|]. split; [exact ST'|].
      split; [eapply agrees_on_trans; [exact AG2| exact AG']|]. split; [exact G'|]. split; [rewrite OF'; exact OF2|]. split; [reflexivity|].
      exists FB1', FB2', Af'. split; [exact EFB'| reflexivity]. }
    carve_frame 32%nat ST.
    do 5 zstep. ub_null.                  (* [comment removed for export] *)
    do 2 zstep. ub_al 7%Z ltac:(al16 P2). zstep. if_false.
    do 4 zstep.
    ck0 PUNP; ck_go.                      (* [comment removed for export] *)
    do 3 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW : Forall (pcap_iv FL PB) [(bv_unsigned sp + -32, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s (CLc ++ PB) FB FL mm) by (eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FW]);
      assert (AG0 : agrees_on (fun a => outside [(bv_unsigned sp + -32, bv_unsigned sp)]%Z a) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      assert (PC0 : PCAPR_closable P p PB FB mm)
        by (eapply PCAPR_closable_agree; [exact AG0 | intros a Ha; pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)); cbn [outside]; lia | exact PC]);
      assert (AGa : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    clear MU WM AG0.
    assert (WK : forall (CL : list cblock) mA mB, agrees_on (client_keeps FL (CLc ++ CL) (bv_unsigned sp + -32)) mA mB ->
                 agrees_on (client_keeps FL CLc (bv_unsigned sp)) mA mB).
    { intros CL mA mB AG. eapply client_keeps_weaken; [exact AG | lia | intros a Ha; apply in_block_app; left; exact Ha | intros a Ha; exact Ha]. }
    (* [comment removed for export] *)
    unfold pcap_blocks in EPB. unfold cleanup_entry, is_ng, PK. cbn [pk_cleanup_ng pk_cleanup_sf].
    destruct (pc_priv p) as [sf|sg oq] eqn:EP.
    - (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 543948)) with (Z_to_bv 64 (pk_cleanup_sf PK)) by (symmetry; apply ret_pc_even; [cbn; lia|reflexivity]).
      rewrite EPB, EFB in G0.
      name_sp sp (-32)%Z.
      apply evtF_done. eapply implMG_bind.
      { eapply sf_cleanup_proofA; [| eapply (ucaller_data _ _ _ _ _ _ 0x85dcc%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | first [lia | cbv; lia]]
                                  | rewrite unsigned_lit by lia; exact TRS | intros f [] | exact CELLS | reflexivity | exact NOF].
        split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [lia|]. split; [unfold PCAP_L3_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
        split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
      intros [] s' RNG1 ms' PO. unfold cleanup_post in PO. (nd_pre PO 11%nat; intros FP1 av1 m2 j' E OF1 MI1 ST1 AG1 G1 HC1; nd_post).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x85dcc)) with (Z_to_bv 64 0x85dcc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      eapply CONT; [exact EFB | exact FP1 | exact MI1 | exact ST1 | eapply agrees_on_trans; [exact AGa| apply (WK []); rewrite app_nil_r; exact AG1] | exact G1
             | eapply keeps_rw_cells_stack; [exact AG1 | exact FR | lia] | exact HC1 | exact OF1].
    - (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 581656)) with (Z_to_bv 64 (pk_cleanup_ng PK)) by (symmetry; apply ret_pc_even; [cbn; lia|reflexivity]).
      name_sp sp (-32)%Z.
      apply evtF_done. eapply implMG_bind.
      { eapply NGC; [| eapply (ucaller_data _ _ _ _ _ _ 0x85dcc%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | first [lia | cbv; lia]]
                    | rewrite unsigned_lit by lia; exact TRN | intros f [] | exact PC0 | unfold is_ng; rewrite EP; reflexivity | reflexivity | exact NOF].
        split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [lia|]. split; [unfold PCAP_L3_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
        split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
      intros [] s' RNG1 ms' PO. cbv beta in PO. (nd_pre PO 7%nat; intros _ B' Af' FB1' FB2' EFB' PO; nd_post). unfold cleanup_post in PO.
      (nd_pre PO 11%nat; intros FP1 av1 m2 j' E OF1 MI1 ST1 AG1 G1 HC1; nd_post).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x85dcc)) with (Z_to_bv 64 0x85dcc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      eapply CONT; [exact EFB' | exact FP1 | exact MI1 | exact ST1 | eapply agrees_on_trans; [exact AGa| apply (WK []); rewrite app_nil_r; exact AG1] | exact G1
             | eapply keeps_rw_cells_stack; [exact AG1 | exact FR | lia] | exact HC1 | exact OF1].
  Qed.
  End Sz3.
  #[using="fflagA GL FCLOSE FREE NGC"] Theorem pcap_close_proofA : ltac:(let t := eval cbv delta [pcap_close_proofA__stmt] in pcap_close_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P p. ltac2:(SecDiet.SzSec.closeP 'pcap_close_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Close.
End CANSEC1.
End TwB.
End F_pcap_closeA.

(* [comment removed for export] *)
Module F_ng_cleanupA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_pcap_closeA.
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
Section NgCleanup.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FCLOSE : fclose_stmt_o HO GIOA TP.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.

  Definition ng_cleanup_proofA__stmt : Prop := ng_cleanup_stmt HO FO sites GIOA TP.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P p : ltac2:(SecDiet.SzSec.tyM 'ng_cleanup_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="fflagA GL FCLOSE FREE FREENULL"] Lemma ng_cleanup_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'ng_cleanup_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros PRE UC TR NF PC NG -> NOF. destruct TR as (UTR1 & TRS).
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    pose proof PC as (Af & HinF & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; rewrite EPB; left; reflexivity)) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & _) & _).
    pose proof (psize_pos p) as PS. unfold PCAP_L3_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    band_ind PBAND bP.
    destruct (in_split _ _ HinF) as (FB1 & FB2 & EFB).
    (* [comment removed for export] *)
    unfold is_ng in NG. unfold priv_cells in PRIV. unfold ifaces_closable in IFS. unfold pcap_blocks in EPB.
    destruct (pc_priv p) as [sf|sg oq] eqn:EP; [discriminate NG|]. clear NG. unfold ng_cells, PCAP_PRIV_OFF in PRIV.
    assert (PSZ : psize p = 680%Z) by (unfold psize, is_ng; rewrite EP; reflexivity).
    (* [comment removed for export] *)
    unfold pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF in CELLS. cbn [app] in CELLS.
    clear BUF PFX.
    unfold Pcap.pcap_ng_cleanup, ng_ifaces_ptr_of. rewrite EP. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret prims e_free prims]. unfold PK; cbn [pk_cleanup_ng].
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (KP : forall (CL : list cblock) SP mA mB A cs, In (pc_self p, P, psize p) CL -> agrees_on (client_keeps FL CL SP) mA mB ->
              rw_cells asegs mA A cs -> (P <= A)%Z -> (A + Z.of_nat (cells_size cs) <= P + psize p)%Z -> rw_cells asegs mB A cs).
    { intros CL SP mA mB A cs Hin AG HC HA HB. eapply keeps_rw_cells_block; [exact AG | exact HC |].
      intros a Ha. apply in_block_In. exists (pc_self p, P, psize p). split; [exact Hin| cbn [cb_addr cb_size fst snd]; lia]. }
    assert (HinP : In (pc_self p, P, psize p) (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)])) by (apply in_or_app; right; left; reflexivity).
    ienterG.
    carve_frame 16%nat ST.
    do 8 zstep.
    ck0 PUNP; ck_go.
    do 2 zstep.
    ck0 PUNP; ck_go.
    zstep.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW : Forall (pcap_iv FL PB) [(bv_unsigned sp + -16, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s (CLc ++ PB) FB FL mm) by (eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FW]);
      assert (AGa : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    clear MU WM.
    assert (WK : forall (CL : list cblock) mA mB, agrees_on (client_keeps FL (CLc ++ CL) (bv_unsigned sp + -16)) mA mB ->
                 agrees_on (client_keeps FL CLc (bv_unsigned sp)) mA mB).
    { intros CL mA mB AG. eapply client_keeps_weaken; [exact AG | lia | intros a Ha; apply in_block_app; left; exact Ha | intros a Ha; exact Ha]. }
    (* [comment removed for export] *)
    assert (CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : mem) (ps2 : PState H hptr) (RNG2 : footprint),
      fp_le RNG RNG2 ->
      mem_inv asegs m2 -> stk asegs m2 lo (bv_unsigned sp + -16) -> agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m2 ->
      GIOA L RNG2 ps2 (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) FB FL m2 ->
      rw_cells asegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra] -> rw_cells asegs m2 P (pcap_cells p P B Af j) -> ps_outfile ps2 = ps_outfile s ->
      implMG RNG2 (pcapint_sf_cleanup MOps (prims HO FO sites) p) ps2 POSTQ
        (MS (mkR (Z_to_bv 64 0x8dca0) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0' t1' t2' (Z_to_bv 64 P) s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x8dca0) fc None m2 (seg_rom asegs))).
    { intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 ps2 RNG2 FP2 MI2 ST2 AG2 G2 FR2 CELLS2 OF2.
      clear CELLS PRIV FR G0 AGa MI G IFS PUNP GOT SHB.
      repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
      apply implMG_from_evtF. do 5 zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evtF_done. eapply implMG_mono.
      { eapply (sf_cleanup_proofA HO FO sites GIOA TP fflagA GL FCLOSE FREE);
          [| eapply ucaller_keep; [exact UC | lia | intros a Ha; destruct (AG2 a ltac:(lia) ltac:(left; lia)) as [E _]; exact E]
           | exact TRS | intros f [] | exact CELLS2 | reflexivity | rewrite OF2; exact NOF].
        split; [rewrite EFB in G2; exact G2|]. split; [exact ST2|]. split; [lia|]. split; [unfold PCAP_L3_STACK; lia|].
        split; [lia|]. split; [assumption|]. split; [exact TPE|]. split; [exact ALN|].
        split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
      cbv beta. intros [] ps3 RNG3 ms3 PO. subst POSTQ.
      unfold cleanup_post in *. destruct PO as (FP3 & a0v & m' & j' & E & OF' & MI' & ST' & AG' & G' & HC').
      split; [eapply fp_le_trans; [exact FP2| exact FP3]|]. exists B, Af, FB1, FB2. split; [exact EFB|].
      split; [eapply fp_le_trans; [exact FP2| exact FP3]|].
      exists a0v, m', j'. split; [exact E|]. split; [rewrite OF'; exact OF2|]. split; [exact MI'|]. split; [exact ST'|].
      split; [eapply agrees_on_trans; [exact AG2| exact AG']|]. split; [exact G'| exact HC']. }
    (* [comment removed for export] *)
    destruct oq as [q|].
    - rewrite EPB in G0.
      replace (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p); (q, I, 40 * ng_ifaces_size sg)%Z])
        with ((CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) ++ [(q, I, 40 * ng_ifaces_size sg)%Z]) in G0
        by (rewrite <- app_assoc; reflexivity).
      name_sp sp (-16)%Z.
      apply evtF_done. eapply implMG_bind.
      { eapply FREE; [|reflexivity|].
        - split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
          split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
          split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS].
        - eapply unw_of_ucaller; [eapply (ucaller_data 0%nat _ _ _ _ _ 0x8dca0%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | first [lia | cbv; lia]]
                                 | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite Hsp; lia | rewrite unsigned_lit by lia; exact UTR1 | exact RSTK]. }
      intros [] s' RNG1 ms' PO. cbv beta in PO. destruct PO as (FP1 & av1 & m2 & E & OF1 & MI1 & ST1 & AG1 & G1).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x8dca0)) with (Z_to_bv 64 0x8dca0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite app_nil_r in AG1, G1.
      apply CONT; [exact FP1 | exact MI1 | exact ST1 | eapply agrees_on_trans; [exact AGa| apply (WK _ _ _ AG1)] | exact G1
            | eapply keeps_rw_cells_stack; [exact AG1 | exact FR | lia] | eapply KP; [exact HinP | exact AG1 | exact CELLS | lia | rewrite pcap_cells_size; lia] | exact OF1 ].
    - rewrite IFS in *. rewrite EPB in G0.
      name_sp sp (-16)%Z.
      eapply evtF_cut.
      { eapply FREENULL; [|reflexivity|].
        - split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
          split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
          split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS].
        - eapply unw_of_ucaller; [eapply (ucaller_data 0%nat _ _ _ _ _ 0x8dca0%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | first [lia | cbv; lia]]
                                 | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite Hsp; lia | rewrite unsigned_lit by lia; exact UTR1 | exact RSTK]. }
      intros ms' PO. cbv beta in PO. destruct PO as (av1 & m2 & E & MI1 & ST1 & AG1 & G1).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x8dca0)) with (Z_to_bv 64 0x8dca0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply evtF_done.
      apply CONT; [apply fp_le_refl | exact MI1 | exact ST1 | eapply agrees_on_trans; [exact AGa| apply (WK [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]); exact AG1] | exact G1
            | eapply keeps_rw_cells_stack; [exact AG1 | exact FR | lia] | eapply KP; [exact HinP | exact AG1 | exact CELLS | lia | rewrite pcap_cells_size; lia] | reflexivity ].
  Qed.
  End Sz1.
  #[using="fflagA GL FCLOSE FREE FREENULL"] Theorem ng_cleanup_proofA : ltac:(let t := eval cbv delta [ng_cleanup_proofA__stmt] in ng_cleanup_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P p. ltac2:(SecDiet.SzSec.closeP 'ng_cleanup_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgCleanup.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_pcap_closeA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
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
Section NgCleanup.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FCLOSE : fclose_stmt_o HO GIOA TP.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.

  Definition ng_cleanup_proofA__stmt : Prop := ng_cleanup_stmt HO FO sites GIOA TP.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P p : ltac2:(SecDiet.SzSec.tyM 'ng_cleanup_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="fflagA GL FCLOSE FREE FREENULL"] Lemma ng_cleanup_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'ng_cleanup_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros PRE UC TR NF PC NG -> NOF. destruct TR as (UTR1 & TRS).
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    pose proof PC as (Af & HinF & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; rewrite EPB; left; reflexivity)) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & _) & _).
    pose proof (psize_pos p) as PS. unfold PCAP_L3_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    band_ind PBAND bP.
    destruct (in_split _ _ HinF) as (FB1 & FB2 & EFB).
    (* [comment removed for export] *)
    unfold is_ng in NG. unfold priv_cells in PRIV. unfold ifaces_closable in IFS. unfold pcap_blocks in EPB.
    destruct (pc_priv p) as [sf|sg oq] eqn:EP; [discriminate NG|]. clear NG. unfold ng_cells, PCAP_PRIV_OFF in PRIV.
    assert (PSZ : psize p = 680%Z) by (unfold psize, is_ng; rewrite EP; reflexivity).
    (* [comment removed for export] *)
    unfold pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF in CELLS. cbn [app] in CELLS.
    clear BUF PFX.
    unfold Pcap.pcap_ng_cleanup, ng_ifaces_ptr_of. rewrite EP. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret prims e_free prims]. unfold PK; cbn [pk_cleanup_ng].
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (KP : forall (CL : list cblock) SP mA mB A cs, In (pc_self p, P, psize p) CL -> agrees_on (client_keeps FL CL SP) mA mB ->
              rw_cells asegs mA A cs -> (P <= A)%Z -> (A + Z.of_nat (cells_size cs) <= P + psize p)%Z -> rw_cells asegs mB A cs).
    { intros CL SP mA mB A cs Hin AG HC HA HB. eapply keeps_rw_cells_block; [exact AG | exact HC |].
      intros a Ha. apply in_block_In. exists (pc_self p, P, psize p). split; [exact Hin| cbn [cb_addr cb_size fst snd]; lia]. }
    assert (HinP : In (pc_self p, P, psize p) (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)])) by (apply in_or_app; right; left; reflexivity).
    ienterG.
    carve_frame 16%nat ST.
    do 3 zstep. ub_null.                  (* [comment removed for export] *)
    do 2 zstep. ub_al 7%Z ltac:(al16 P2). zstep. if_false.
    do 4 zstep.
    ck0 PUNP; ck_go.
    zstep. ub_null.                       (* [comment removed for export] *)
    zstep. ub_al 7%Z ltac:(al16 P2). zstep. if_false.
    zstep.
    ck0 PUNP; ck_go.
    zstep.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW : Forall (pcap_iv FL PB) [(bv_unsigned sp + -16, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s (CLc ++ PB) FB FL mm) by (eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FW]);
      assert (AGa : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    clear MU WM.
    assert (WK : forall (CL : list cblock) mA mB, agrees_on (client_keeps FL (CLc ++ CL) (bv_unsigned sp + -16)) mA mB ->
                 agrees_on (client_keeps FL CLc (bv_unsigned sp)) mA mB).
    { intros CL mA mB AG. eapply client_keeps_weaken; [exact AG | lia | intros a Ha; apply in_block_app; left; exact Ha | intros a Ha; exact Ha]. }
    (* [comment removed for export] *)
    assert (CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : mem) (ps2 : PState H hptr) (RNG2 : footprint),
      fp_le RNG RNG2 ->
      mem_inv asegs m2 -> stk asegs m2 lo (bv_unsigned sp + -16) -> agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m2 ->
      GIOA L RNG2 ps2 (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) FB FL m2 ->
      rw_cells asegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra] -> rw_cells asegs m2 P (pcap_cells p P B Af j) -> ps_outfile ps2 = ps_outfile s ->
      implMG RNG2 (pcapint_sf_cleanup MOps (prims HO FO sites) p) ps2 POSTQ
        (MS (mkR (Z_to_bv 64 0x8e080) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0' t1' t2' (Z_to_bv 64 P) s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x8e080) fc None m2 (seg_rom asegs))).
    { intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 ps2 RNG2 FP2 MI2 ST2 AG2 G2 FR2 CELLS2 OF2.
      clear CELLS PRIV FR G0 AGa MI G IFS PUNP GOT SHB.
      repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
      apply implMG_from_evtF. do 5 zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evtF_done. eapply implMG_mono.
      { eapply (sf_cleanup_proofA HO FO sites GIOA TP fflagA GL FCLOSE FREE);
          [| eapply ucaller_keep; [exact UC | lia | intros a Ha; destruct (AG2 a ltac:(lia) ltac:(left; lia)) as [E _]; exact E]
           | exact TRS | intros f [] | exact CELLS2 | reflexivity | rewrite OF2; exact NOF].
        split; [rewrite EFB in G2; exact G2|]. split; [exact ST2|]. split; [lia|]. split; [unfold PCAP_L3_STACK; lia|].
        split; [lia|]. split; [assumption|]. split; [exact TPE|]. split; [exact ALN|].
        split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
      cbv beta. intros [] ps3 RNG3 ms3 PO. subst POSTQ.
      unfold cleanup_post in *. destruct PO as (FP3 & a0v & m' & j' & E & OF' & MI' & ST' & AG' & G' & HC').
      split; [eapply fp_le_trans; [exact FP2| exact FP3]|]. exists B, Af, FB1, FB2. split; [exact EFB|].
      split; [eapply fp_le_trans; [exact FP2| exact FP3]|].
      exists a0v, m', j'. split; [exact E|]. split; [rewrite OF'; exact OF2|]. split; [exact MI'|]. split; [exact ST'|].
      split; [eapply agrees_on_trans; [exact AG2| exact AG']|]. split; [exact G'| exact HC']. }
    (* [comment removed for export] *)
    destruct oq as [q|].
    - rewrite EPB in G0.
      replace (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p); (q, I, 40 * ng_ifaces_size sg)%Z])
        with ((CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) ++ [(q, I, 40 * ng_ifaces_size sg)%Z]) in G0
        by (rewrite <- app_assoc; reflexivity).
      name_sp sp (-16)%Z.
      apply evtF_done. eapply implMG_bind.
      { eapply FREE; [|reflexivity|].
        - split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
          split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
          split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS].
        - eapply unw_of_ucaller; [eapply (ucaller_data 0%nat _ _ _ _ _ 0x8e080%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | first [lia | cbv; lia]]
                                 | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite Hsp; lia | rewrite unsigned_lit by lia; exact UTR1 | exact RSTK]. }
      intros [] s' RNG1 ms' PO. cbv beta in PO. destruct PO as (FP1 & av1 & m2 & E & OF1 & MI1 & ST1 & AG1 & G1).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x8e080)) with (Z_to_bv 64 0x8e080) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite app_nil_r in AG1, G1.
      apply CONT; [exact FP1 | exact MI1 | exact ST1 | eapply agrees_on_trans; [exact AGa| apply (WK _ _ _ AG1)] | exact G1
            | eapply keeps_rw_cells_stack; [exact AG1 | exact FR | lia] | eapply KP; [exact HinP | exact AG1 | exact CELLS | lia | rewrite pcap_cells_size; lia] | exact OF1 ].
    - rewrite IFS in *. rewrite EPB in G0.
      name_sp sp (-16)%Z.
      eapply evtF_cut.
      { eapply FREENULL; [|reflexivity|].
        - split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
          split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
          split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS].
        - eapply unw_of_ucaller; [eapply (ucaller_data 0%nat _ _ _ _ _ 0x8e080%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | first [lia | cbv; lia]]
                                 | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite Hsp; lia | rewrite unsigned_lit by lia; exact UTR1 | exact RSTK]. }
      intros ms' PO. cbv beta in PO. destruct PO as (av1 & m2 & E & MI1 & ST1 & AG1 & G1).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x8e080)) with (Z_to_bv 64 0x8e080) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply evtF_done.
      apply CONT; [apply fp_le_refl | exact MI1 | exact ST1 | eapply agrees_on_trans; [exact AGa| apply (WK [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]); exact AG1] | exact G1
            | eapply keeps_rw_cells_stack; [exact AG1 | exact FR | lia] | eapply KP; [exact HinP | exact AG1 | exact CELLS | lia | rewrite pcap_cells_size; lia] | reflexivity ].
  Qed.
  End Sz1.
  #[using="fflagA GL FCLOSE FREE FREENULL"] Theorem ng_cleanup_proofA : ltac:(let t := eval cbv delta [ng_cleanup_proofA__stmt] in ng_cleanup_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P p. ltac2:(SecDiet.SzSec.closeP 'ng_cleanup_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgCleanup.
End CANSEC1.
End TwB.
End F_ng_cleanupA.

(* [comment removed for export] *)
Module F_pcap_close_allA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad PcapTypes Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_pcap_closeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ng_cleanupA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[using="Type"] Theorem pcap_close_closedA :
    gia_laws FO GIOA fflagA -> fclose_stmt_o HO GIOA TP -> free_stmt_o HO GIOA -> free_null_stmt_o GIOA -> pcap_close_stmt HO FO sites GIOA TP.
  Proof.
    intros GL FCLOSE FREE FREENULL.
    exact (pcap_close_proofA HO FO sites GIOA TP fflagA GL FCLOSE FREE (ng_cleanup_proofA HO FO sites GIOA TP fflagA GL FCLOSE FREE FREENULL)).
  Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_pcap_closeA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ng_cleanupA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[using="Type"] Theorem pcap_close_closedA :
    gia_laws FO GIOA fflagA -> fclose_stmt_o HO GIOA TP -> free_stmt_o HO GIOA -> free_null_stmt_o GIOA -> pcap_close_stmt HO FO sites GIOA TP.
  Proof.
    intros GL FCLOSE FREE FREENULL.
    exact (pcap_close_proofA HO FO sites GIOA TP fflagA GL FCLOSE FREE (ng_cleanup_proofA HO FO sites GIOA TP fflagA GL FCLOSE FREE FREENULL)).
  Qed.
End CANSEC1.
End TwB.
End F_pcap_close_allA.

(* [comment removed for export] *)
Module F_pcap_errA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.
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
Section Err.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis STRERROR_R : strerror_r_stmt GIOA.

  Definition pcap_strerror_proofA__stmt : Prop := pcap_strerror_stmt GIOA.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo e : ltac2:(SecDiet.SzSec.tyM 'pcap_strerror_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="FO fflagA GL STRERROR_R"] Lemma pcap_strerror_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_strerror_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros PRE -> He.
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    unfold PCAP_L0_STACK in BU. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    unfold PCAP_STRERROR_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
    carve_frame 32%nat ST.
    do 10 zstep.
    rewrite ETP.
    (* [comment removed for export] *)
    assert (FW : Forall (client_ivA FL CL) [(bv_unsigned sp - 32, bv_unsigned sp)]%Z)
      by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G0 : GIOA L RNG s CL FB FL mm) by (eapply (gl_client_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FW]);
      assert (AGa : agrees_on (client_keeps FL CL (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ CL [] _ FL []); [exact G' | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    clear G' MU WM FW.
    name_sp sp (-32)%Z.
    eapply evtF_cut.
    { eapply STRERROR_R with (L := L) (s := s) (CL := CL) (FB := FB) (FL := FL) (lo := lo) (e := e); [| reflexivity | reflexivity | reflexivity | exact He].
      split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    intros ms' PO. cbv beta in PO. destruct PO as (av1 & m2 & rest & E & EA & MI1 & ST1 & AG1 & G1 & RES).
    unfold hpost_regs in E. destruct_exs E. subst ms' av1. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x85e70)) with (Z_to_bv 64 0x85e70) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lazymatch type of FR with rw_cells _ _ ?A ?cs =>
      assert (FR2 : rw_cells asegs m2 A cs) by (eapply keeps_rw_cells_stack; [exact AG1 | exact FR | lia]) end.
    clear FR.
    zstep. if_true. do 6 zstep.
    release_frame FR2 ST1 (bv_unsigned sp).
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MI1|]. split; [exact ST1|].
    split. { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1 | lia | intros a Ha; exact Ha | apply incl_refl]. }
    split; [exact G1| exact RES].
  Qed.
  End Sz1.
  #[using="FO fflagA GL STRERROR_R"] Theorem pcap_strerror_proofA : ltac:(let t := eval cbv delta [pcap_strerror_proofA__stmt] in pcap_strerror_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo e. ltac2:(SecDiet.SzSec.closeP 'pcap_strerror_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Err.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
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
Section Err.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis STRERROR_R : strerror_r_stmt GIOA.

  Definition pcap_strerror_proofA__stmt : Prop := pcap_strerror_stmt GIOA.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo e : ltac2:(SecDiet.SzSec.tyM 'pcap_strerror_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="FO fflagA GL STRERROR_R"] Lemma pcap_strerror_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_strerror_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros PRE -> He.
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    unfold PCAP_L0_STACK in BU. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    unfold PCAP_STRERROR_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
    carve_frame 32%nat ST.
    do 10 zstep.
    rewrite ETP.
    (* [comment removed for export] *)
    assert (FW : Forall (client_ivA FL CL) [(bv_unsigned sp - 32, bv_unsigned sp)]%Z)
      by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G0 : GIOA L RNG s CL FB FL mm) by (eapply (gl_client_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FW]);
      assert (AGa : agrees_on (client_keeps FL CL (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ CL [] _ FL []); [exact G' | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    clear G' MU WM FW.
    name_sp sp (-32)%Z.
    eapply evtF_cut.
    { eapply STRERROR_R with (L := L) (s := s) (CL := CL) (FB := FB) (FL := FL) (lo := lo) (e := e); [| reflexivity | reflexivity | reflexivity | exact He].
      split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    intros ms' PO. cbv beta in PO. destruct PO as (av1 & m2 & rest & E & EA & MI1 & ST1 & AG1 & G1 & RES).
    unfold hpost_regs in E. destruct_exs E. subst ms' av1. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x85fd0)) with (Z_to_bv 64 0x85fd0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lazymatch type of FR with rw_cells _ _ ?A ?cs =>
      assert (FR2 : rw_cells asegs m2 A cs) by (eapply keeps_rw_cells_stack; [exact AG1 | exact FR | lia]) end.
    clear FR.
    zstep. if_true. do 6 zstep.
    release_frame FR2 ST1 (bv_unsigned sp).
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MI1|]. split; [exact ST1|].
    split. { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1 | lia | intros a Ha; exact Ha | apply incl_refl]. }
    split; [exact G1| exact RES].
  Qed.
  End Sz1.
  #[using="FO fflagA GL STRERROR_R"] Theorem pcap_strerror_proofA : ltac:(let t := eval cbv delta [pcap_strerror_proofA__stmt] in pcap_strerror_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo e. ltac2:(SecDiet.SzSec.closeP 'pcap_strerror_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Err.
End CANSEC1.
End TwB.
End F_pcap_errA.

(* [comment removed for export] *)
Module F_pcap_pureA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition max_snaplen_proofA__stmt : Prop := max_snaplen_stmt.
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo dlt : ltac2:(SecDiet.SzSec.tyM 'max_snaplen_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma max_snaplen_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'max_snaplen_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros MI ST -> Hdlt.
 unfold MAX_SNAPLEN_ENTRY.
  pose proof (munch_refl [(bv_unsigned sp - 0, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 2 zstep. if_cases K; zify_cond K.
  { do 2 zstep. finish. unfold max_snaplen_for_dlt, DLT_DBUS. subst dlt. reflexivity. }
  do 2 zstep. if_cases K2; zify_cond K2.
  { do 2 zstep. finish. unfold max_snaplen_for_dlt, DLT_DBUS, DLT_USBPCAP, DLT_EBHSCR. subst dlt. reflexivity. }
  do 2 zstep. if_cases K3; zify_cond K3.
  { do 2 zstep. finish. unfold max_snaplen_for_dlt, DLT_DBUS, DLT_USBPCAP, DLT_EBHSCR, MAXIMUM_SNAPLEN.
    rewrite (proj2 (Z.eqb_neq _ _) K), (proj2 (Z.eqb_neq _ _) K3), (proj2 (Z.eqb_neq _ _) K2). reflexivity. }
  do 2 zstep. finish. unfold max_snaplen_for_dlt, DLT_DBUS, DLT_USBPCAP, DLT_EBHSCR.
  rewrite (proj2 (Z.eqb_neq _ _) K), (proj2 (Z.eqb_neq _ _) K2). subst dlt. reflexivity.
Qed.
End Sz1.
#[using="Type"] Theorem max_snaplen_proofA : ltac:(let t := eval cbv delta [max_snaplen_proofA__stmt] in max_snaplen_proofA__stmt in exact t).
Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo dlt. ltac2:(SecDiet.SzSec.closeP 'max_snaplen_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma s32_cases : forall z, (0 <= z < 2^32)%Z ->
  (0 <= z < 2^31 /\ s32 z = z)%Z \/ (2^31 <= z < 2^32 /\ s32 z = z - 2^32)%Z.
Proof.
  intros z Hz. unfold s32.
  destruct (Z_lt_ge_dec z (2^31)).
  - left. split; [lia|]. rewrite Z.mod_small by lia. lia.
  - right. split; [lia|]. replace (z + 2^31)%Z with ((z - 2^31) + 1 * 2^32)%Z by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition adjust_snapshot_proofA__stmt : Prop := adjust_snapshot_stmt.
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo lt snaplen : ltac2:(SecDiet.SzSec.tyM 'adjust_snapshot_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma adjust_snapshot_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'adjust_snapshot_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros MI ST -> Hlt -> Hsn.
 unfold PCAP_ADJUST_SNAPSHOT_ENTRY.
  destruct (s32_cases snaplen Hsn) as [[R1 E]|[R1 E]]; rewrite E.
  - (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K.
    + (* [comment removed for export] *)
      assert (snaplen = 0%Z) by lia. subst snaplen.
      zstep. eapply evtF_mono; [eapply max_snaplen_proofA; [exact MI | exact ST | reflexivity | lia]|].
      cbv beta. intros ms' PO. unfold leaf_post in *. destruct_exs PO. destruct PO as (-> & MU' & WM' & MI' & ST' & ->).
      repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
      split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. reflexivity.
    + pose proof (munch_refl [(bv_unsigned sp - 0, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
      do 2 zstep. finish. unfold pcapint_adjust_snapshot, INT_MAX.
      replace (snaplen =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      replace (2 ^ 31 - 1 <? snaplen)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K.
    + zstep. eapply evtF_mono; [eapply max_snaplen_proofA; [exact MI | exact ST | reflexivity | lia]|].
      cbv beta. intros ms' PO. unfold leaf_post in *. destruct_exs PO. destruct PO as (-> & MU' & WM' & MI' & ST' & ->).
      repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
      split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|].
      unfold pcapint_adjust_snapshot, INT_MAX. replace (2 ^ 31 - 1 <? snaplen)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite orb_true_r. reflexivity.
    + exfalso. lia.
Qed.
End Sz3.
#[using="Type"] Theorem adjust_snapshot_proofA : ltac:(let t := eval cbv delta [adjust_snapshot_proofA__stmt] in adjust_snapshot_proofA__stmt in exact t).
Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo lt snaplen. ltac2:(SecDiet.SzSec.closeP 'adjust_snapshot_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lt_tab : list byte := [11; 0; 0; 0; 12; 0; 0; 0; 15; 0; 0; 0; 16; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 19; 0; 0; 0].
#[using="Type"] Lemma swrap32_range_neg : forall x, (-2^31 <= x < 0)%Z -> bv_unsigned (Z_to_bv 64 (bv_swrap 32 x)) = (2^64 + x)%Z.
Proof.
  intros x Hx. rewrite swrap32_small by lia. rewrite unsigned_lit_wrap.
  replace x with ((2^64 + x) + (-1) * 2^64)%Z at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma swrap32_mid : forall x, (2^31 <= x < 2^32 + 2^31)%Z -> bv_swrap 32 x = (x - 2^32)%Z.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  replace (x + 2^31)%Z with ((x + 2^31 - 2^32) + 1 * 2^32)%Z by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Definition lt_out_of_table__stmt : Prop := forall lt, (11 <= lt < 2^32)%Z -> (lt < 100 \/ 107 <= lt)%Z ->
  bv_ltu (Z_to_bv 64 6) (Z_to_bv 64 (bv_swrap 32 (lt + -100))) = true.
Section Sz6.
Variables lt : ltac2:(SecDiet.SzSec.tyM 'lt_out_of_table__stmt "v" @lt).
#[using="Type"] Lemma lt_out_of_table__body : ltac2:(SecDiet.SzSec.bodyP 'lt_out_of_table__stmt "v").
Proof.
  intros H1 H2.
 unfold bv_ltu. rewrite (unsigned_lit 6) by lia. apply Z.ltb_lt.
  destruct (Z_lt_ge_dec lt 100).
  - rewrite swrap32_range_neg by lia. lia.
  - destruct (Z_lt_ge_dec lt (2^31 + 100)).
    + rewrite swrap32_small by lia. rewrite unsigned_lit by lia. lia.
    + rewrite swrap32_mid by lia. rewrite unsigned_lit_wrap.
      replace (lt + -100 - 2^32)%Z with ((2^64 + (lt - 100 - 2^32)) + (-1) * 2^64)%Z by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
End Sz6.
#[using="Type"] Lemma lt_out_of_table : ltac:(let t := eval cbv delta [lt_out_of_table__stmt] in lt_out_of_table__stmt in exact t).
Proof. intros lt. ltac2:(SecDiet.SzSec.closeP 'lt_out_of_table__body "v"). Qed.

(* [comment removed for export] *)
Local Ltac lt_hit :=
  zstep; if_false; do 3 zstep; if_false; do 4 zstep; if_false; do 7 zstep;
  lazymatch goal with UNP : unpoisoned _ 139264 _ |- _ => ck UNP 4%Z 0x88ea8%Z [11%Z; 12%Z] end;
  do 4 zstep;
  lazymatch goal with FR : rw_cells _ _ (bv_unsigned ?sp + -16) _, ST : stk _ _ _ _ |- _ => release_frame FR ST (bv_unsigned sp) end;
  finish; vm_compute; reflexivity.
Local Ltac lt_miss :=
  zstep; if_false; do 3 zstep; if_false; do 4 zstep; if_true; do 3 zstep;
  lazymatch goal with FR : rw_cells _ _ (bv_unsigned ?sp + -16) _, ST : stk _ _ _ _ |- _ => release_frame FR ST (bv_unsigned sp) end;
  finish; reflexivity.

Definition linktype_to_dlt_proofA__stmt : Prop := linktype_to_dlt_stmt.
Section Sz7.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo lt : ltac2:(SecDiet.SzSec.tyM 'linktype_to_dlt_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma linktype_to_dlt_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'linktype_to_dlt_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros MI ST BU LO RT UNP RSTK RIMG RISH -> Hlt.
 unfold LINKTYPE_TO_DLT_ENTRY. unfold LT_TABLE in UNP.
  assert (TAB : ro_cells asegs m 0x22000 [CB 28 lt_tab]).
  { apply (ro_cells_image asegs m); [exact MI | vm_compute; reflexivity | lia | cbn; lia]. }
  destruct RT as (_ & GOT & _ & _ & SHB & _).
  pose proof (bv_unsigned_in_range 64 sp) as RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  do 3 zstep.
  assert (CASES : (lt < 11 \/ (11 <= lt /\ (lt < 100 \/ 107 <= lt))
                   \/ lt = 100 \/ lt = 101 \/ lt = 102 \/ lt = 103 \/ lt = 104 \/ lt = 105 \/ lt = 106)%Z) by lia.
  destruct CASES as [C|[C|[->|[->|[->|[->|[->|[->| ->]]]]]]]].
  - (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K; [|exfalso; lia].
    do 3 zstep. release_frame FR ST (bv_unsigned sp). finish. unfold linktype_to_dlt.
    rewrite !(proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
  - (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K; [exfalso; lia|].
    do 3 zstep. rewrite ?(unsigned_lit lt) by lia. if_true_by (lt_out_of_table lt ltac:(lia) ltac:(lia)).
    do 3 zstep. release_frame FR ST (bv_unsigned sp). finish. unfold linktype_to_dlt.
    rewrite !(proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
  - lt_hit.
  - lt_hit.
  - lt_hit.
  - lt_hit.
  - lt_miss.
  - lt_miss.
  - lt_hit.
Qed.
End Sz7.
#[using="Type"] Theorem linktype_to_dlt_proofA : ltac:(let t := eval cbv delta [linktype_to_dlt_proofA__stmt] in linktype_to_dlt_proofA__stmt in exact t).
Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo lt. ltac2:(SecDiet.SzSec.closeP 'linktype_to_dlt_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition max_snaplen_proofA__stmt : Prop := max_snaplen_stmt.
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo dlt : ltac2:(SecDiet.SzSec.tyM 'max_snaplen_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma max_snaplen_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'max_snaplen_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI ST -> Hdlt. unfold MAX_SNAPLEN_ENTRY.
  pose proof (munch_refl [(bv_unsigned sp - 0, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 2 zstep. if_cases K; zify_cond K.
  { do 2 zstep. finish. unfold max_snaplen_for_dlt, DLT_DBUS. subst dlt. reflexivity. }
  do 2 zstep. if_cases K2; zify_cond K2.
  { do 2 zstep. finish. unfold max_snaplen_for_dlt, DLT_DBUS, DLT_USBPCAP, DLT_EBHSCR. subst dlt. reflexivity. }
  do 2 zstep. if_cases K3; zify_cond K3.
  { do 2 zstep. finish. unfold max_snaplen_for_dlt, DLT_DBUS, DLT_USBPCAP, DLT_EBHSCR, MAXIMUM_SNAPLEN.
    rewrite (proj2 (Z.eqb_neq _ _) K), (proj2 (Z.eqb_neq _ _) K3), (proj2 (Z.eqb_neq _ _) K2). reflexivity. }
  do 2 zstep. finish. unfold max_snaplen_for_dlt, DLT_DBUS, DLT_USBPCAP, DLT_EBHSCR.
  rewrite (proj2 (Z.eqb_neq _ _) K), (proj2 (Z.eqb_neq _ _) K2). subst dlt. reflexivity.
Qed.
End Sz1.
#[using="Type"] Theorem max_snaplen_proofA : ltac:(let t := eval cbv delta [max_snaplen_proofA__stmt] in max_snaplen_proofA__stmt in exact t).
Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo dlt. ltac2:(SecDiet.SzSec.closeP 'max_snaplen_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma s32_cases : forall z, (0 <= z < 2^32)%Z ->
  (0 <= z < 2^31 /\ s32 z = z)%Z \/ (2^31 <= z < 2^32 /\ s32 z = z - 2^32)%Z.
Proof.
  intros z Hz. unfold s32.
  destruct (Z_lt_ge_dec z (2^31)).
  - left. split; [lia|]. rewrite Z.mod_small by lia. lia.
  - right. split; [lia|]. replace (z + 2^31)%Z with ((z - 2^31) + 1 * 2^32)%Z by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition adjust_snapshot_proofA__stmt : Prop := adjust_snapshot_stmt.
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo lt snaplen : ltac2:(SecDiet.SzSec.tyM 'adjust_snapshot_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma adjust_snapshot_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'adjust_snapshot_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI ST -> Hlt -> Hsn. unfold PCAP_ADJUST_SNAPSHOT_ENTRY.
  destruct (s32_cases snaplen Hsn) as [[R1 E]|[R1 E]]; rewrite E.
  - (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K.
    + (* [comment removed for export] *)
      assert (snaplen = 0%Z) by lia. subst snaplen.
      zstep. eapply evtF_mono; [eapply max_snaplen_proofA; [exact MI | exact ST | reflexivity | lia]|].
      cbv beta. intros ms' PO. unfold leaf_post in *. destruct_exs PO. destruct PO as (-> & MU' & WM' & MI' & ST' & ->).
      repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
      split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. reflexivity.
    + pose proof (munch_refl [(bv_unsigned sp - 0, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
      do 2 zstep. finish. unfold pcapint_adjust_snapshot, INT_MAX.
      replace (snaplen =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      replace (2 ^ 31 - 1 <? snaplen)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K.
    + zstep. eapply evtF_mono; [eapply max_snaplen_proofA; [exact MI | exact ST | reflexivity | lia]|].
      cbv beta. intros ms' PO. unfold leaf_post in *. destruct_exs PO. destruct PO as (-> & MU' & WM' & MI' & ST' & ->).
      repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
      split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|].
      unfold pcapint_adjust_snapshot, INT_MAX. replace (2 ^ 31 - 1 <? snaplen)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite orb_true_r. reflexivity.
    + exfalso. lia.
Qed.
End Sz3.
#[using="Type"] Theorem adjust_snapshot_proofA : ltac:(let t := eval cbv delta [adjust_snapshot_proofA__stmt] in adjust_snapshot_proofA__stmt in exact t).
Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo lt snaplen. ltac2:(SecDiet.SzSec.closeP 'adjust_snapshot_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lt_tab : list byte := [11; 0; 0; 0; 12; 0; 0; 0; 15; 0; 0; 0; 16; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 19; 0; 0; 0].
#[using="Type"] Lemma swrap32_range_neg : forall x, (-2^31 <= x < 0)%Z -> bv_unsigned (Z_to_bv 64 (bv_swrap 32 x)) = (2^64 + x)%Z.
Proof.
  intros x Hx. rewrite swrap32_small by lia. rewrite unsigned_lit_wrap.
  replace x with ((2^64 + x) + (-1) * 2^64)%Z at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma swrap32_mid : forall x, (2^31 <= x < 2^32 + 2^31)%Z -> bv_swrap 32 x = (x - 2^32)%Z.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  replace (x + 2^31)%Z with ((x + 2^31 - 2^32) + 1 * 2^32)%Z by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Definition lt_out_of_table__stmt : Prop := forall lt, (11 <= lt < 2^32)%Z -> (lt < 100 \/ 107 <= lt)%Z ->
  bv_ltu (Z_to_bv 64 6) (Z_to_bv 64 (bv_swrap 32 (lt + -100))) = true.
Section Sz6.
Variables lt : ltac2:(SecDiet.SzSec.tyM 'lt_out_of_table__stmt "v" @lt).
#[using="Type"] Lemma lt_out_of_table__body : ltac2:(SecDiet.SzSec.bodyP 'lt_out_of_table__stmt "v").
Proof.
  intros H1 H2.
 unfold bv_ltu. rewrite (unsigned_lit 6) by lia. apply Z.ltb_lt.
  destruct (Z_lt_ge_dec lt 100).
  - rewrite swrap32_range_neg by lia. lia.
  - destruct (Z_lt_ge_dec lt (2^31 + 100)).
    + rewrite swrap32_small by lia. rewrite unsigned_lit by lia. lia.
    + rewrite swrap32_mid by lia. rewrite unsigned_lit_wrap.
      replace (lt + -100 - 2^32)%Z with ((2^64 + (lt - 100 - 2^32)) + (-1) * 2^64)%Z by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
End Sz6.
#[using="Type"] Lemma lt_out_of_table : ltac:(let t := eval cbv delta [lt_out_of_table__stmt] in lt_out_of_table__stmt in exact t).
Proof. intros lt. ltac2:(SecDiet.SzSec.closeP 'lt_out_of_table__body "v"). Qed.

(* [comment removed for export] *)
Local Ltac lt_hit :=
  zstep; if_false; do 3 zstep; if_false; do 4 zstep; if_false; do 7 zstep;
  lazymatch goal with UNP : unpoisoned _ 139264 _ |- _ => ck UNP 4%Z 0x89404%Z [11%Z; 12%Z] end;
  do 4 zstep;
  lazymatch goal with FR : rw_cells _ _ (bv_unsigned ?sp + -16) _, ST : stk _ _ _ _ |- _ => release_frame FR ST (bv_unsigned sp) end;
  finish; vm_compute; reflexivity.
Local Ltac lt_miss :=
  zstep; if_false; do 3 zstep; if_false; do 4 zstep; if_true; do 3 zstep;
  lazymatch goal with FR : rw_cells _ _ (bv_unsigned ?sp + -16) _, ST : stk _ _ _ _ |- _ => release_frame FR ST (bv_unsigned sp) end;
  finish; reflexivity.

Definition linktype_to_dlt_proofA__stmt : Prop := linktype_to_dlt_stmt.
Section Sz7.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo lt : ltac2:(SecDiet.SzSec.tyM 'linktype_to_dlt_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma linktype_to_dlt_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'linktype_to_dlt_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI ST BU LO RT UNP RSTK RIMG RISH -> Hlt. unfold LINKTYPE_TO_DLT_ENTRY. unfold LT_TABLE in UNP.
  assert (TAB : ro_cells asegs m 0x22000 [CB 28 lt_tab]).
  { apply (ro_cells_image asegs m); [exact MI | vm_compute; reflexivity | lia | cbn; lia]. }
  destruct RT as (_ & GOT & _ & _ & SHB & _).
  pose proof (bv_unsigned_in_range 64 sp) as RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  do 3 zstep.
  assert (CASES : (lt < 11 \/ (11 <= lt /\ (lt < 100 \/ 107 <= lt))
                   \/ lt = 100 \/ lt = 101 \/ lt = 102 \/ lt = 103 \/ lt = 104 \/ lt = 105 \/ lt = 106)%Z) by lia.
  destruct CASES as [C|[C|[->|[->|[->|[->|[->|[->| ->]]]]]]]].
  - (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K; [|exfalso; lia].
    do 3 zstep. release_frame FR ST (bv_unsigned sp). finish. unfold linktype_to_dlt.
    rewrite !(proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
  - (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K; [exfalso; lia|].
    do 3 zstep. rewrite ?(unsigned_lit lt) by lia. if_true_by (lt_out_of_table lt ltac:(lia) ltac:(lia)).
    do 3 zstep. release_frame FR ST (bv_unsigned sp). finish. unfold linktype_to_dlt.
    rewrite !(proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
  - lt_hit.
  - lt_hit.
  - lt_hit.
  - lt_hit.
  - lt_miss.
  - lt_miss.
  - lt_hit.
Qed.
End Sz7.
#[using="Type"] Theorem linktype_to_dlt_proofA : ltac:(let t := eval cbv delta [linktype_to_dlt_proofA__stmt] in linktype_to_dlt_proofA__stmt in exact t).
Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG lo lt. ltac2:(SecDiet.SzSec.closeP 'linktype_to_dlt_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End F_pcap_pureA.

(* [comment removed for export] *)
Module F_ngchk_failA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA.
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
Local Ltac ck_live OK pc := lazymatch constr:((OK, pc)) with (570500%Z, 569044%Z) => idtac | (570500%Z, 569156%Z) => idtac | (570500%Z, 569260%Z) => idtac | (570500%Z, 569524%Z) => idtac | (570500%Z, 570272%Z) => idtac | (570500%Z, 570328%Z) => idtac | (570500%Z, 570500%Z) => idtac | (570500%Z, 571416%Z) => idtac | (570928%Z, 568904%Z) => idtac | (570928%Z, 569028%Z) => idtac | (570928%Z, 569132%Z) => idtac | (570928%Z, 569424%Z) => idtac | (570928%Z, 570700%Z) => idtac | (570928%Z, 570756%Z) => idtac | (570928%Z, 570928%Z) => idtac | (570928%Z, 571344%Z) => idtac end.
Local Ltac ck_arm OK n ::=
  lazymatch n with
  | O => fail "ck_join: step budget exhausted before reaching the join point" OK
  | S ?n' =>
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 OK) _ _ _ _) =>
        apply evtF_done; lazymatch goal with |- ?q _ => tryif is_var q then unfold q else idtac end; cbn [ck_post]; repeat eexists; simp_regs;
        first [ reflexivity | fail 1 "ck_join: a register outside the clobber list changed before" OK ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; rewrite ?sxb_sval; ck_arm OK n'
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "Kck" in
        if_cases K; ck_zify K;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif ck_live OK pc then first [ ck_arm OK n' | exfalso; ck_lia ] else first [ exfalso; ck_lia | ck_arm OK n' ]
        | _ => first [ exfalso; ck_lia | ck_arm OK n' ]
        end
    end
  end.
(* [comment removed for export] *)
Local Ltac cjq_fold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQc" in pose (QQ := Q); change Q with QQ end).
Local Ltac ck_join_at UNP P N OK RS ::=
  ck_clear; cbv beta delta [mkR];
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
      let b := fresh "shb" in let RD := fresh "RDsh" in let CK := fresh "CKsh" in let SR := fresh "SRsh" in
      destruct (ck_part_rd m lo hi P N UNP ltac:(ck_lia) ltac:(ck_lia) ltac:(lia) ltac:(ck_lia)) as (b & RD & CK);
      ck_fp_at lo P;
      pose proof (sval_range b) as SR;
      eapply (evtF_cut segs RNG (fun ms' => ck_post RS (fun R' => ms' = MS R' F (Z_to_bv 64 OK) fc rv m ro) R));
      [ cjq_fold; ck_arm OK 16%nat
      | let ms' := fresh "ms'" in let H := fresh "Hck" in
        intros ms' H; cbn [ck_post] in H; destruct_exs H; subst ms'; simp_regs; clear RD CK SR; ck_clear; try clear b ]
    | unpoisoned ?m' _ _ => fail "ck_join: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
Section CANSEC1. Context {rc : runConstT}.
Section FailSeq.
  Variables (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (RNG : footprint) (SPA ERR : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis UNP : unpoisoned m ERR (ERR + 4).
  Hypothesis RSH : rng RNG (shad (ERR - ERR mod 8)) (nshad (4 + ERR mod 8)).
  Hypothesis RER : rng RNG ERR 4.
  Hypothesis ERR4 : (ERR mod 4 = 0)%Z.
  Hypothesis ERLO : (0x603000 <= ERR)%Z.
  Hypothesis ERHI : (ERR + 4 <= 2^47)%Z.
  Hypothesis HE : rw_cells asegs m ERR [C4 z64].

  Local Notation fail_post :=
    (fun ms' : machine_state => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 0) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7
                      s2 (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8b490) fc None m' (seg_rom asegs)
        /\ munch [(ERR, ERR + 4)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' ERR [C4 (Z_to_bv 64 1)]).

  Local Ltac seq_start := pose proof (munch_refl [(ERR, ERR + 4)]%Z m) as MU; pose proof (wmono_refl asegs m) as WM.
  Local Ltac seq_end := apply evtF_done; eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; assumption.

  #[using="MI UNP RSH RER ERR4 ERLO ERHI HE"] Lemma fail_seq_8ab98 :
    evtF asegs RNG fail_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8aecc) fc None m (seg_rom asegs)).
  Proof.
    seq_start.
    ck_join_at UNP ERR 4%Z 0x8b484%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.

  #[using="MI UNP RSH RER ERR4 ERLO ERHI HE"] Lemma fail_seq_8ac08 :
    evtF asegs RNG fail_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8af3c) fc None m (seg_rom asegs)).
  Proof.
    seq_start.
    ck_join_at UNP ERR 4%Z 0x8b484%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.

  #[using="MI UNP RSH RER ERR4 ERLO ERHI HE"] Lemma fail_seq_8ac70 :
    evtF asegs RNG fail_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8afa4) fc None m (seg_rom asegs)).
  Proof.
    seq_start.
    ck_join_at UNP ERR 4%Z 0x8b484%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.

  #[using="MI UNP RSH RER ERR4 ERLO ERHI HE"] Lemma fail_seq_8ad78 :
    evtF asegs RNG fail_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b0ac) fc None m (seg_rom asegs)).
  Proof.
    seq_start.
    ck_join_at UNP ERR 4%Z 0x8b484%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.

  #[using="MI UNP RSH RER ERR4 ERLO ERHI HE"] Lemma fail_seq_8b064 :
    evtF asegs RNG fail_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b398) fc None m (seg_rom asegs)).
  Proof.
    seq_start.
    ck_join_at UNP ERR 4%Z 0x8b484%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.

  #[using="MI UNP RSH RER ERR4 ERLO ERHI HE"] Lemma fail_seq_8b09c :
    evtF asegs RNG fail_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b3d0) fc None m (seg_rom asegs)).
  Proof.
    seq_start.
    ck_join_at UNP ERR 4%Z 0x8b484%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.

  #[using="MI UNP RSH RER ERR4 ERLO ERHI HE"] Lemma fail_seq_8b148 :
    evtF asegs RNG fail_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b47c) fc None m (seg_rom asegs)).
  Proof.
    seq_start.
    ck_join_at UNP ERR 4%Z 0x8b484%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.
End FailSeq.

Section NgcFail.
  Context {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.

  (* [comment removed for export] *)
  Definition ngc_failx__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 r26 t3 t4 t5 t6 : word)
      (scs fcs : list cell) (k0 k1 k2 : word) (msg : list Z) (junk3 : list byte) (pcX : Z),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [] mm ->
    In pcX [0x8aecc; 0x8af3c; 0x8afa4; 0x8b0ac; 0x8b398; 0x8b3d0; 0x8b47c]%Z ->
    rw_cells asegs mm SPA scs -> cells_size scs = 152%nat ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 z64] ->
    rw_cells asegs mm EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] ->
    (Z.of_nat (length msg) < 256)%Z -> Forall (fun z => 0 < z < 256)%Z msg ->
    implMG RNGx (fo_ret FO _ FF_NG_CHECK_HEADER (CH_Err msg)) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r26 (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 pcX) fc None mm (seg_rom asegs)).
  Section Sz8.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 r26 t3 t4 t5 t6 scs fcs k0 k1 k2 msg junk3 pcX : ltac2:(SecDiet.SzSec.tyM 'ngc_failx__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_failx__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_failx__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET.
 intros CTX INV PCX FRA Hscs FRC Hfcs HE HEB LEN3 RNG3.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU. unfold ngc_shadow in SHC.
    destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. cbn [map] in MGc.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rw_cells_merge asegs _ _ [C8 k0; C8 k1; C8 k2] fcs [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))] FRC) as FRCm.
    rewrite Hfcs in FRCm. cbn [app] in FRCm. clear FRC.
    (* [comment removed for export] *)
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll FND]. pose proof (Forall_inv FAll) as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR).
    cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll. change (Z.shiftr 64 3) with 8%Z in FSRNG, FSWR.
    pose proof (ablk_lin _ _ FBAND') as (_ & Fb0 & _ & _). band_ind FBAND' bF.
    assert (ICL : incl CL (CL ++ [])) by (apply incl_appl, incl_refl).
    assert (IFL : incl FL ((FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL)) by (apply incl_tl, incl_refl).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL)) as (MGLO & MGHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)) as (ERLO & ERHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)) as (EBLO & EBHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL) ltac:(lia)) as ERBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL) ltac:(lia)) as EBBAND.
    assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(ERR, ERR + 4); (EB, EB + 256)]%Z)
      by (apply Forall_cons; [exact ERBAND| apply Forall_cons; [exact EBBAND| apply Forall_nil]]).
    band_ind ERBAND bE.
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL (incl_refl _)) ltac:(lia)) as (kM & kMr & kM1 & kM2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL (incl_refl _)) ltac:(lia)) as (kE & kEr & kE1 & kE2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL (incl_refl _)) ltac:(lia)) as (kB & kBr & kB1 & kB2).
    cbn [fb_addr fb_size fst snd] in kM1, kM2, kE1, kE2, kB1, kB2.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000
                   /\ (Fb + 64 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 8 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    apply (rng_fp_le _ _ _ _ FP) in RSTK.
    pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G IFL AG FXB) as AGsh.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OERR G ICL IFL AGsh ltac:(lia)) as (_ & _ & _ & ERUNP & ERRNG & ERRSH & _).
    assert (FX : Forall (cobj_iv FL CL) [(ERR, ERR + 4)]%Z) by cobj_ivs.
    pose proof (munch_refl [(ERR, ERR + 4)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF.
    assert (SEQ : evtF asegs RNGx (fun ms' => exists m',
        ms' = MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 0) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r26 (Z_to_bv 64 Fb) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x8b490) fc None m' (seg_rom asegs)
        /\ munch [(ERR, ERR + 4)]%Z mm m' /\ wmono asegs mm m' /\ mem_inv asegs m' /\ rw_cells asegs m' ERR [C4 (Z_to_bv 64 1)])
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r26 (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 pcX) fc None mm (seg_rom asegs))).
    { cbn [In] in PCX. destruct PCX as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
      - eapply fail_seq_8ab98; eassumption || lia.
      - eapply fail_seq_8ac08; eassumption || lia.
      - eapply fail_seq_8ac70; eassumption || lia.
      - eapply fail_seq_8ad78; eassumption || lia.
      - eapply fail_seq_8b064; eassumption || lia.
      - eapply fail_seq_8b09c; eassumption || lia.
      - eapply fail_seq_8b148; eassumption || lia. }
    call SEQ.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m4 _) =>
      destruct (own_writes _ _ _ GL L RNGx sx CL [] FB FL [(FF_NG_CHECK_HEADER, Fb, 64%Z)] mm m4 [] [(ERR, ERR + 4)]%Z (bv_unsigned sp) (Forall_nil _) FX G MU WM ltac:(lia)) as [G4 AG4];
      assert (AGm4 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m4)
        by (eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG4|]; intros a (K & (N1 & _)); split; [exact K|]; split; [exact N1| exact I])
    end.
    apply evtF_done.
    lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?m4 _) =>
      eapply (ngc_exit FO GIOA TP fflagA GL FRET) with (fcs := [CB 32 (cells_bytes fcs)]) (r := CH_Err msg) (PB := []) (mm := m4);
        [ exact CTX | | eassumption | exact Hscs | exact FRCm | reflexivity | eassumption | ] end.
    - unfold ngc_inv, ngc_shadow. split; [exact FP|]. split; [exact G4|]. split; [exact OF|]. repeat (split; [assumption|]). assumption.
    - cbn [ngc_result]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exists junk3; assumption|]. split; [exact LEN3| exact RNG3].
  Qed.
  End Sz8.
  Lemma ngc_failx : ltac:(let t := eval cbv delta [ngc_failx__stmt] in ngc_failx__stmt in exact t).
  Proof using GL FRET. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 r26 t3 t4 t5 t6 scs fcs k0 k1 k2 msg junk3 pcX. ltac2:(SecDiet.SzSec.closeP 'ngc_failx__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcFail.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA.TwB.
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
Local Ltac ck_live OK pc := lazymatch constr:((OK, pc)) with (570460%Z, 569004%Z) => idtac | (570460%Z, 569116%Z) => idtac | (570460%Z, 569220%Z) => idtac | (570460%Z, 569484%Z) => idtac | (570460%Z, 570232%Z) => idtac | (570460%Z, 570288%Z) => idtac | (570460%Z, 570460%Z) => idtac | (570460%Z, 571376%Z) => idtac | (570888%Z, 568864%Z) => idtac | (570888%Z, 568988%Z) => idtac | (570888%Z, 569092%Z) => idtac | (570888%Z, 569384%Z) => idtac | (570888%Z, 570660%Z) => idtac | (570888%Z, 570716%Z) => idtac | (570888%Z, 570888%Z) => idtac | (570888%Z, 571304%Z) => idtac end.
Local Ltac ck_arm OK n ::=
  lazymatch n with
  | O => fail "ck_join: step budget exhausted before reaching the join point" OK
  | S ?n' =>
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 OK) _ _ _ _) =>
        apply evtF_done; lazymatch goal with |- ?q _ => tryif is_var q then unfold q else idtac end; cbn [ck_post]; repeat eexists; simp_regs;
        first [ reflexivity | fail 1 "ck_join: a register outside the clobber list changed before" OK ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; rewrite ?sxb_sval; ck_arm OK n'
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "Kck" in
        if_cases K; ck_zify K;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif ck_live OK pc then first [ ck_arm OK n' | exfalso; ck_lia ] else first [ exfalso; ck_lia | ck_arm OK n' ]
        | _ => first [ exfalso; ck_lia | ck_arm OK n' ]
        end
    end
  end.
(* [comment removed for export] *)
Local Ltac cjq_fold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQc" in pose (QQ := Q); change Q with QQ end).
Local Ltac ck_join_at UNP P N OK RS ::=
  ck_clear; cbv beta delta [mkR];
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
      let b := fresh "shb" in let RD := fresh "RDsh" in let CK := fresh "CKsh" in let SR := fresh "SRsh" in
      destruct (ck_part_rd m lo hi P N UNP ltac:(ck_lia) ltac:(ck_lia) ltac:(lia) ltac:(ck_lia)) as (b & RD & CK);
      ck_fp_at lo P;
      pose proof (sval_range b) as SR;
      eapply (evtF_cut segs RNG (fun ms' => ck_post RS (fun R' => ms' = MS R' F (Z_to_bv 64 OK) fc rv m ro) R));
      [ cjq_fold; ck_arm OK 16%nat
      | let ms' := fresh "ms'" in let H := fresh "Hck" in
        intros ms' H; cbn [ck_post] in H; destruct_exs H; subst ms'; simp_regs; clear RD CK SR; ck_clear; try clear b ]
    | unpoisoned ?m' _ _ => fail "ck_join: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
Section CANSEC1. Context {rc : runConstT}.
Section FailSeq.
  Variables (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (RNG : footprint) (SPA ERR : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis UNP : unpoisoned m ERR (ERR + 4).
  Hypothesis RSH : rng RNG (shad (ERR - ERR mod 8)) (nshad (4 + ERR mod 8)).
  Hypothesis RER : rng RNG ERR 4.
  Hypothesis ERR4 : (ERR mod 4 = 0)%Z.
  Hypothesis ERLO : (0x604000 <= ERR)%Z.
  Hypothesis ERHI : (ERR + 4 <= 2^47)%Z.
  Hypothesis HE : rw_cells asegs m ERR [C4 z64].

  Local Notation fail_post :=
    (fun ms' : machine_state => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 0) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7
                      s2 (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8b614) fc None m' (seg_rom asegs)
        /\ munch [(ERR, ERR + 4)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' ERR [C4 (Z_to_bv 64 1)]).

  Local Ltac seq_start := pose proof (munch_refl [(ERR, ERR + 4)]%Z m) as MU; pose proof (wmono_refl asegs m) as WM.
  Local Ltac seq_end := apply evtF_done; eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; assumption.

  #[using="MI UNP RSH RER ERR4 ERLO ERHI HE"] Lemma fail_seq_8ab98 :
    evtF asegs RNG fail_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8ae18) fc None m (seg_rom asegs)).
  Proof.
    seq_start.
    ck_join_at UNP ERR 4%Z 0x8b608%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.

  #[using="MI UNP RSH RER ERR4 ERLO ERHI HE"] Lemma fail_seq_8ac08 :
    evtF asegs RNG fail_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8ae94) fc None m (seg_rom asegs)).
  Proof.
    seq_start.
    ck_join_at UNP ERR 4%Z 0x8b608%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.

  #[using="MI UNP RSH RER ERR4 ERLO ERHI HE"] Lemma fail_seq_8ac70 :
    evtF asegs RNG fail_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 569084) fc None m (seg_rom asegs)).
  Proof.
    seq_start.
    ck_join_at UNP ERR 4%Z 0x8b608%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.

  #[using="MI UNP RSH RER ERR4 ERLO ERHI HE"] Lemma fail_seq_8ad78 :
    evtF asegs RNG fail_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b020) fc None m (seg_rom asegs)).
  Proof.
    seq_start.
    ck_join_at UNP ERR 4%Z 0x8b608%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.

  #[using="MI UNP RSH RER ERR4 ERLO ERHI HE"] Lemma fail_seq_8b064 :
    evtF asegs RNG fail_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b51c) fc None m (seg_rom asegs)).
  Proof.
    seq_start.
    ck_join_at UNP ERR 4%Z 0x8b608%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.

  #[using="MI UNP RSH RER ERR4 ERLO ERHI HE"] Lemma fail_seq_8b09c :
    evtF asegs RNG fail_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b554) fc None m (seg_rom asegs)).
  Proof.
    seq_start.
    ck_join_at UNP ERR 4%Z 0x8b608%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.

  #[using="MI UNP RSH RER ERR4 ERLO ERHI HE"] Lemma fail_seq_8b148 :
    evtF asegs RNG fail_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b600) fc None m (seg_rom asegs)).
  Proof.
    seq_start.
    ck_join_at UNP ERR 4%Z 0x8b608%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.
End FailSeq.

Section NgcFail.
  Context {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.

  (* [comment removed for export] *)
  Definition ngc_failx__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 r26 t3 t4 t5 t6 : word)
      (scs fcs : list cell) (k0 k1 k2 : word) (msg : list Z) (junk3 : list byte) (pcX : Z),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [] mm ->
    In pcX [0x8ae18; 0x8ae94; 569084; 0x8b020; 0x8b51c; 0x8b554; 0x8b600]%Z ->
    rw_cells asegs mm SPA scs -> cells_size scs = 152%nat ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 z64] ->
    rw_cells asegs mm EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] ->
    (Z.of_nat (length msg) < 256)%Z -> Forall (fun z => 0 < z < 256)%Z msg ->
    implMG RNGx (fo_ret FO _ FF_NG_CHECK_HEADER (CH_Err msg)) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r26 (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 pcX) fc None mm (seg_rom asegs)).
  Section Sz8.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 r26 t3 t4 t5 t6 scs fcs k0 k1 k2 msg junk3 pcX : ltac2:(SecDiet.SzSec.tyM 'ngc_failx__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_failx__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_failx__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET.
 intros CTX INV PCX FRA Hscs FRC Hfcs HE HEB LEN3 RNG3.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU. unfold ngc_shadow in SHC.
    destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. cbn [map] in MGc.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rw_cells_merge asegs _ _ [C8 k0; C8 k1; C8 k2] fcs [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))] FRC) as FRCm.
    rewrite Hfcs in FRCm. cbn [app] in FRCm. clear FRC.
    (* [comment removed for export] *)
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll FND]. pose proof (Forall_inv FAll) as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR).
    cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll. change (Z.shiftr 64 3) with 8%Z in FSRNG, FSWR.
    pose proof (ablk_lin _ _ FBAND') as (_ & Fb0 & _ & _). band_ind FBAND' bF.
    assert (ICL : incl CL (CL ++ [])) by (apply incl_appl, incl_refl).
    assert (IFL : incl FL ((FF_NG_CHECK_HEADER, Fb, 64%Z) :: FL)) by (apply incl_tl, incl_refl).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL)) as (MGLO & MGHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)) as (ERLO & ERHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)) as (EBLO & EBHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL) ltac:(lia)) as ERBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL) ltac:(lia)) as EBBAND.
    assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(ERR, ERR + 4); (EB, EB + 256)]%Z)
      by (apply Forall_cons; [exact ERBAND| apply Forall_cons; [exact EBBAND| apply Forall_nil]]).
    band_ind ERBAND bE.
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL (incl_refl _)) ltac:(lia)) as (kM & kMr & kM1 & kM2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL (incl_refl _)) ltac:(lia)) as (kE & kEr & kE1 & kE2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL (incl_refl _)) ltac:(lia)) as (kB & kBr & kB1 & kB2).
    cbn [fb_addr fb_size fst snd] in kM1, kM2, kE1, kE2, kB1, kB2.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000
                   /\ (Fb + 64 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 8 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    apply (rng_fp_le _ _ _ _ FP) in RSTK.
    pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G IFL AG FXB) as AGsh.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OERR G ICL IFL AGsh ltac:(lia)) as (_ & _ & _ & ERUNP & ERRNG & ERRSH & _).
    assert (FX : Forall (cobj_iv FL CL) [(ERR, ERR + 4)]%Z) by cobj_ivs.
    pose proof (munch_refl [(ERR, ERR + 4)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF.
    assert (SEQ : evtF asegs RNGx (fun ms' => exists m',
        ms' = MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 0) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r26 (Z_to_bv 64 Fb) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x8b614) fc None m' (seg_rom asegs)
        /\ munch [(ERR, ERR + 4)]%Z mm m' /\ wmono asegs mm m' /\ mem_inv asegs m' /\ rw_cells asegs m' ERR [C4 (Z_to_bv 64 1)])
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r26 (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 pcX) fc None mm (seg_rom asegs))).
    { cbn [In] in PCX. destruct PCX as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
      - eapply fail_seq_8ab98; eassumption || lia.
      - eapply fail_seq_8ac08; eassumption || lia.
      - eapply fail_seq_8ac70; eassumption || lia.
      - eapply fail_seq_8ad78; eassumption || lia.
      - eapply fail_seq_8b064; eassumption || lia.
      - eapply fail_seq_8b09c; eassumption || lia.
      - eapply fail_seq_8b148; eassumption || lia. }
    call SEQ.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m4 _) =>
      destruct (own_writes _ _ _ GL L RNGx sx CL [] FB FL [(FF_NG_CHECK_HEADER, Fb, 64%Z)] mm m4 [] [(ERR, ERR + 4)]%Z (bv_unsigned sp) (Forall_nil _) FX G MU WM ltac:(lia)) as [G4 AG4];
      assert (AGm4 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m4)
        by (eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG4|]; intros a (K & (N1 & _)); split; [exact K|]; split; [exact N1| exact I])
    end.
    apply evtF_done.
    lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?m4 _) =>
      eapply (ngc_exit FO GIOA TP fflagA GL FRET) with (fcs := [CB 32 (cells_bytes fcs)]) (r := CH_Err msg) (PB := []) (mm := m4);
        [ exact CTX | | eassumption | exact Hscs | exact FRCm | reflexivity | eassumption | ] end.
    - unfold ngc_inv, ngc_shadow. split; [exact FP|]. split; [exact G4|]. split; [exact OF|]. repeat (split; [assumption|]). assumption.
    - cbn [ngc_result]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exists junk3; assumption|]. split; [exact LEN3| exact RNG3].
  Qed.
  End Sz8.
  Lemma ngc_failx : ltac:(let t := eval cbv delta [ngc_failx__stmt] in ngc_failx__stmt in exact t).
  Proof using GL FRET. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 r26 t3 t4 t5 t6 scs fcs k0 k1 k2 msg junk3 pcX. ltac2:(SecDiet.SzSec.closeP 'ngc_failx__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcFail.
End CANSEC1.
End TwB.
End F_ngchk_failA.

(* [comment removed for export] *)
Module F_ngchk_kitA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcKit.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).

  (* [comment removed for export] *)
  Definition ngc_spo__stmt : Prop := forall ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx CLx mm budget,
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m -> fp_le RNG RNGx ->
    GIOA L RNGx sx CLx FB (NGFR Fb :: FL) mm -> stk asegs mm lo SPA -> mem_inv asegs mm -> budget <= PCAP_L2_STACK - 287 ->
    std_pre_o GIOA L RNGx (Z_to_bv 64 SPA) tp sx CLx FB (NGFR Fb :: FL) lo budget mm.
  Section Sz1.
  Variables ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx CLx mm budget : ltac2:(SecDiet.SzSec.tyM 'ngc_spo__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="Type"] Lemma ngc_spo__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_spo__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros CTX FP G ST MI HB.
    destruct CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SPAB & SPA32).
    unfold PCAP_L2_STACK in BU, HB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (E : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia). unfold std_pre_o. rewrite E.
    split; [exact G|]. split; [exact ST|]. split; [exact LO|]. split; [lia|]. split; [lia|]. split; [exact MI|]. split; [exact TPE|].
    split; [Z.div_mod_to_equations; lia|].
    split; [eapply rng_fp_le; eassumption|]. split; [eapply rng_fp_le; eassumption|]. split; eapply rng_fp_le; eassumption.
  Qed.
  End Sz1.
  #[using="Type"] Lemma ngc_spo : ltac:(let t := eval cbv delta [ngc_spo__stmt] in ngc_spo__stmt in exact t).
  Proof. intros ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx CLx mm budget. ltac2:(SecDiet.SzSec.closeP 'ngc_spo__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_ucaller__stmt : Prop := forall d' L (sp s0 ra : word) SPA mm trC X (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : cell),
    ucallerA (depth_check_header true) L mm sp s0 ra trC ->
    (bv_unsigned sp - 287 <= SPA <= bv_unsigned sp - 256) -> ATOP + 4096 <= SPA -> bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
    rw_cells asegs mm (bv_unsigned sp + -104) [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; C8 s0; C8 ra] ->
    cells_size [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] = 88%nat ->
    ACLIENT_LO <= X < ACLIENT_HI -> (S d' <= depth_check_header true)%nat ->
    ucallerA d' L mm (Z_to_bv 64 SPA) sp (Z_to_bv 64 X) (bv_unsigned ra :: trC).
  Section Sz2.
  Variables d' L sp s0 ra SPA mm trC X c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ltac2:(SecDiet.SzSec.tyM 'ngc_ucaller__stmt "vvvvvvvvvvvvvvvvvvvv" @d').
  #[using="Type"] Lemma ngc_ucaller__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_ucaller__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros UC SPAB LO SPT ALN FRs SZ HX HD.
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
  End Sz2.
  #[using="Type"] Lemma ngc_ucaller : ltac:(let t := eval cbv delta [ngc_ucaller__stmt] in ngc_ucaller__stmt in exact t).
  Proof. intros d' L sp s0 ra SPA mm trC X c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10. ltac2:(SecDiet.SzSec.closeP 'ngc_ucaller__body "vvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma ngc_keep_stack : forall (FLx : list fblock) (CLx : list cblk) SPA (Pn : Z -> Prop) m1 m2 A cs,
    agrees_on (fun a => client_keeps FLx CLx SPA a /\ Pn a) m1 m2 -> rw_cells asegs m1 A cs -> SPA <= A ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> Pn a) -> rw_cells asegs m2 A cs.
  Proof. intros FLx CLx SPA Pn m1 m2 A cs AG HC HA HP. eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. split; [left; lia| apply HP; exact Ha]. Qed.
  #[using="Type"] Lemma ngc_keep_frame : forall (FLx : list fblock) (CLx : list cblk) SPA Fb (Pn : Z -> Prop) m1 m2 A cs,
    agrees_on (fun a => client_keeps (NGFR Fb :: FLx) CLx SPA a /\ Pn a) m1 m2 -> rw_cells asegs m1 A cs ->
    Fb <= A -> A + Z.of_nat (cells_size cs) <= Fb + 64 ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> Pn a) -> rw_cells asegs m2 A cs.
  Proof.
    intros FLx CLx SPA Fb Pn m1 m2 A cs AG HC H1 H2 HP. eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. split; [| apply HP; exact Ha].
    right; right; left. apply Exists_cons_hd. cbn [fb_addr fb_size fst snd]. lia.
  Qed.
  #[using="Type"] Lemma ngc_keep_cobj : forall (FL FLx : list fblock) (CL CLx : list cblk) SPA (Pn : Z -> Prop) m1 m2 A n cs,
    agrees_on (fun a => client_keeps FLx CLx SPA a /\ Pn a) m1 m2 -> rw_cells asegs m1 A cs -> clocA FL CL A n ->
    incl CL CLx -> incl FL FLx -> Z.of_nat (cells_size cs) <= n ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> Pn a) -> rw_cells asegs m2 A cs.
  Proof.
    intros FL FLx CL CLx SPA Pn m1 m2 A n cs AG HC LOC IC IF Hn HP. eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. split; [| apply HP; exact Ha].
    eapply clocA_keeps; [eapply clocA_incl; [exact LOC| exact IC| exact IF]| lia].
  Qed.

  #[using="Type"] Lemma ngc_keep_block : forall (FLx : list fblock) (CLx : list cblk) SPA (Pn : Z -> Prop) m1 m2 A cs (b : cblk),
    agrees_on (fun a => client_keeps FLx CLx SPA a /\ Pn a) m1 m2 -> rw_cells asegs m1 A cs -> In b CLx ->
    cb_addr b <= A -> A + Z.of_nat (cells_size cs) <= cb_addr b + cb_size b ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> Pn a) -> rw_cells asegs m2 A cs.
  Proof.
    intros FLx CLx SPA Pn m1 m2 A cs b AG HC Hb H1 H2 HP. eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. split; [| apply HP; exact Ha].
    right; left. apply in_block_In. exists b. split; [exact Hb| lia].
  Qed.

  (* [comment removed for export] *)
  Definition ngc_uc_now__stmt : Prop := forall ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm,
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB mm ->
    ucallerA (depth_check_header true) L mm sp s0 ra trC.
  Section Sz7.
  Variables ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm : ltac2:(SecDiet.SzSec.tyM 'ngc_uc_now__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="FO fflagA GL"] Lemma ngc_uc_now__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_uc_now__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros CTX INV.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (ICL : incl CL (CL ++ PB)) by (apply incl_appl, incl_refl).
    assert (IFL : incl FL (NGFR Fb :: FL)) by (apply incl_tl, incl_refl).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)) as (ERLO & ERHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)) as (EBLO & EBHI).
    eapply ucaller_keep; [exact UC| exact TOP47|]. intros a Ha. apply (AG a); [lia|]. split; [left; lia|]. cbn [outside fst snd]. lia.
  Qed.
  End Sz7.
  #[using="FO fflagA GL"] Lemma ngc_uc_now : ltac:(let t := eval cbv delta [ngc_uc_now__stmt] in ngc_uc_now__stmt in exact t).
  Proof. intros ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm. ltac2:(SecDiet.SzSec.closeP 'ngc_uc_now__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_inv_keep__stmt : Prop := forall ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m
      RNGx sx PB mm RNGy sy PB' my RNGk sk mk (CLk : list cblk) (Pn : Z -> Prop),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB mm ->
    fp_le RNGx RNGy -> GIOA L RNGy sy (CL ++ PB') FB (NGFR Fb :: FL) my -> ps_outfile sy = ps_outfile sx ->
    mem_inv asegs my -> stk asegs my lo SPA ->
    agrees_on (fun a => client_keeps (NGFR Fb :: FL) CLk SPA a /\ Pn a) mm my -> incl CL CLk ->
    GIOA L RNGk sk CLk FB (NGFR Fb :: FL) mk ->      (* [comment removed for export] *)
    (forall a, ~ (EB <= a < EB + 256) -> ~ (ERR <= a < ERR + 4) -> Pn a) ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGy sy PB' my.
  Section Sz8.
  Variables ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm RNGy sy PB' my RNGk sk mk CLk Pn : ltac2:(SecDiet.SzSec.tyM 'ngc_inv_keep__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="FO fflagA GL"] Lemma ngc_inv_keep__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_inv_keep__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros CTX INV FPy Gy OFy MIy STy AGy ICk Gk HPn.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. pose proof (Forall_inv FAll) as (FBAND & FTOP & F64 & _ & _ & _ & _ & _).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64. pose proof (ablk_lin _ _ FBAND) as (FIMG & Fb0 & _ & _). unfold AIMG_HI in FIMG.
    assert (SHE : Z.shiftr Fb 3 + 2147450880 = Fb / 8 + 2147450880) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    band_ind FBAND bF.
    assert (ICL : incl CL (CL ++ PB)) by (apply incl_appl, incl_refl).
    assert (IFL : incl FL (NGFR Fb :: FL)) by (apply incl_tl, incl_refl).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)) as (ERLO & ERHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)) as (EBLO & EBHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL) ltac:(lia)) as ERBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL) ltac:(lia)) as EBBAND.
    band_ind ERBAND bE. band_ind EBBAND bB.
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL (incl_refl _)) ltac:(lia)) as (kE & kEr & kE1 & kE2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL (incl_refl _)) ltac:(lia)) as (kB & kBr & kB1 & kB2).
    cbn [fb_addr fb_size fst snd] in kE1, kE2, kB1, kB2.
    assert (PS : forall a, SPA <= a -> Pn a) by (intros a Ha; apply HPn; lia).
    split; [intros b j Hb; apply FPy, FP; exact Hb|]. split; [exact Gy|]. split; [rewrite OFy; exact OF|]. split; [exact MIy|]. split; [exact STy|].
    split; [eapply agrees_stk; [exact AGy| exact STG| intros a Ha; split; [left; lia| apply PS; lia]]|].
    split; [eapply ngc_keep_stack; [exact AGy| exact FR| lia| intros a Ha; apply PS; cbn [cells_size csize Nat.add] in Ha; lia]|].
    split.
    { eapply agrees_on_trans; [exact AG|]. eapply (ngc_keeps_callee FO GIOA fflagA GL) with (SPA := SPA) (Pn := Pn); [exact Gk| exact ICk| lia| lia| exact AGy|].
      intros a K (N1 & N2 & _) NF0. cbn [fst snd] in N1, N2. apply HPn; lia. }
    split.
    { destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. cbn [map] in MGc |- *.
      eapply ngc_keep_cobj; [exact AGy| exact MGc| exact (proj1 OMG)| exact ICk| exact IFL| cbn [cells_size csize Nat.add]; lia|].
      intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply HPn; lia. }
    unfold ngc_shadow in SHC |- *.
    eapply agrees_rw_cells; [exact AGy| exact SHC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. split.
    - right; right; right. apply Exists_cons_hd. cbn [fb_addr fb_size fst snd]. change (Z.shiftr 64 3) with 8. lia.
    - apply HPn; rewrite SHE in Ha; Z.div_mod_to_equations; lia.
  Qed.
  End Sz8.
  #[using="FO fflagA GL"] Lemma ngc_inv_keep : ltac:(let t := eval cbv delta [ngc_inv_keep__stmt] in ngc_inv_keep__stmt in exact t).
  Proof. intros ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm RNGy sy PB' my RNGk sk mk CLk Pn. ltac2:(SecDiet.SzSec.closeP 'ngc_inv_keep__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngc_cobj_now__stmt : Prop := forall ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm,
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB mm ->
    cobjA RNGx mm FL CL MG 4 /\ cobjA RNGx mm FL CL ERR 4 /\ cobjA RNGx mm FL CL EB 256.
  Section Sz9.
  Variables ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm : ltac2:(SecDiet.SzSec.tyM 'ngc_cobj_now__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="FO fflagA GL"] Lemma ngc_cobj_now__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_cobj_now__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros CTX INV.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    assert (ICL : incl CL (CL ++ PB)) by (apply incl_appl, incl_refl).
    assert (IFL : incl FL (NGFR Fb :: FL)) by (apply incl_tl, incl_refl).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL) ltac:(lia)) as ERBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL) ltac:(lia)) as EBBAND.
    assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(ERR, ERR + 4); (EB, EB + 256)]%Z)
      by (apply Forall_cons; [exact ERBAND| apply Forall_cons; [exact EBBAND| apply Forall_nil]]).
    pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G IFL AG FXB) as AGsh.
    split; [exact (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OMG G ICL IFL AGsh ltac:(lia))|].
    split; [exact (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OERR G ICL IFL AGsh ltac:(lia))|].
    exact (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G ICL IFL AGsh ltac:(lia)).
  Qed.
  End Sz9.
  #[using="FO fflagA GL"] Lemma ngc_cobj_now : ltac:(let t := eval cbv delta [ngc_cobj_now__stmt] in ngc_cobj_now__stmt in exact t).
  Proof. intros ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm. ltac2:(SecDiet.SzSec.closeP 'ngc_cobj_now__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma ngc_keeps_callee2 : forall L RNGg sg (CLg CLk FB : list cblk) fr FL m0 m1 m2 (CL : list cblk) SP SPA WX (Pn : Z -> Prop),
    GIOA L RNGg sg CLg FB (fr :: FL) m0 -> incl CL CLg -> incl CL CLk -> (ATOP <= SPA)%Z -> (SPA <= SP)%Z ->
    agrees_on (fun a => client_keeps (fr :: FL) CLk SPA a /\ Pn a) m1 m2 ->
    (forall a, client_keeps FL CL SP a -> outside WX a -> ~ (fb_addr fr <= a < fb_addr fr + fb_size fr)%Z -> Pn a) ->
    agrees_on (fun a => client_keeps FL CL SP a /\ outside WX a) m1 m2.
  Proof.
    intros L RNGg sg CLg CLk FB fr FL m0 m1 m2 CL SP SPA WX Pn G ICg ICk HA HS AG HP.
    eapply agrees_on_weaken; [exact AG|]. intros a (K & O). split.
    - eapply ngc_keeps_up; [exact K| exact HS| exact ICk| apply incl_tl, incl_refl].
    - apply HP; [exact K| exact O|]. assert (HSP : (ATOP <= SP)%Z) by lia. exact (proj1 (keeps_not_own_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ a G ICg HSP K)).
  Qed.

  Definition ngc_inv_keep2__stmt : Prop := forall ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m
      RNGx sx PB mm RNGy sy PB' my (CLk : list cblk) (Pn : Z -> Prop),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB mm ->
    fp_le RNGx RNGy -> GIOA L RNGy sy (CL ++ PB') FB (NGFR Fb :: FL) my -> ps_outfile sy = ps_outfile sx ->
    mem_inv asegs my -> stk asegs my lo SPA ->
    agrees_on (fun a => client_keeps (NGFR Fb :: FL) CLk SPA a /\ Pn a) mm my -> incl CL CLk ->
    (forall a, ~ (EB <= a < EB + 256) -> ~ (ERR <= a < ERR + 4) -> (forall b, In b PB -> ~ (cb_addr b <= a < cb_addr b + cb_size b)) -> ~ (SPA <= a < SPA + 152) -> Pn a) ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGy sy PB' my.
  Section Sz11.
  Variables ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm RNGy sy PB' my CLk Pn : ltac2:(SecDiet.SzSec.tyM 'ngc_inv_keep2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="FO fflagA GL"] Lemma ngc_inv_keep2__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_inv_keep2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros CTX INV FPy Gy OFy MIy STy AGy ICk HPn.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. pose proof (Forall_inv FAll) as (FBAND & FTOP & F64 & _ & _ & _ & _ & _).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64. pose proof (ablk_lin _ _ FBAND) as (FIMG & Fb0 & _ & _). unfold AIMG_HI in FIMG.
    assert (SHE : Z.shiftr Fb 3 + 2147450880 = Fb / 8 + 2147450880) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    band_ind FBAND bF.
    assert (ICL : incl CL (CL ++ PB)) by (apply incl_appl, incl_refl).
    assert (IFL : incl FL (NGFR Fb :: FL)) by (apply incl_tl, incl_refl).
    (* [comment removed for export] *)
    assert (PBF : forall b, In b PB -> (0 < cb_size b -> cb_addr b + cb_size b <= ATOP /\ ablk (cb_addr b) (cb_addr b + cb_size b))%Z).
    { intros b Hb Hs. destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; apply in_or_app; right; exact Hb)) as ((BAND & _ & TOP & _) & _). split; [exact TOP| exact BAND]. }
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)) as (ERLO & ERHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)) as (EBLO & EBHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL)) as (MGLO & MGHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL) ltac:(lia)) as ERBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL) ltac:(lia)) as EBBAND.
    band_ind ERBAND bE. band_ind EBBAND bB.
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL (incl_refl _)) ltac:(lia)) as (kE & kEr & kE1 & kE2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL (incl_refl _)) ltac:(lia)) as (kB & kBr & kB1 & kB2).
    cbn [fb_addr fb_size fst snd] in kE1, kE2, kB1, kB2.
    (* [comment removed for export] *)
    assert (NPB : forall a, (SPA <= a \/ Fb <= a < Fb + 64 \/ Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 8 \/ MG <= a < MG + 4)%Z ->
                  forall b, In b PB -> ~ (cb_addr b <= a < cb_addr b + cb_size b)%Z).
    { intros a Ha b Hb Hin. assert (Hs : (0 < cb_size b)%Z) by lia. destruct (PBF b Hb Hs) as (TOP & BAND).
      destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ b (NGFR Fb) G ltac:(apply in_or_app; left; apply in_or_app; right; exact Hb) ltac:(left; reflexivity) Hs) as (k & kr & k1 & k2).
      cbn [fb_addr fb_size fst snd] in k1, k2.
      destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) (incl_refl _) IFL) Hb ltac:(lia) Hs) as (kM & kMr & kM1 & kM2).
      pose proof (ablk_ind _ _ BAND) as (bb & bbr & bbhi & bblo & bbimg). rewrite SHE in Ha. Z.div_mod_to_equations. lia. }
    assert (PS : forall a, SPA + 152 <= a -> Pn a) by (intros a Ha; apply HPn; [lia| lia| apply NPB; left; lia| lia]).
    split; [intros b jj Hb; apply FPy, FP; exact Hb|]. split; [exact Gy|]. split; [rewrite OFy; exact OF|]. split; [exact MIy|]. split; [exact STy|].
    split; [eapply agrees_stk; [exact AGy| exact STG| intros a Ha; split; [left; lia| apply PS; lia]]|].
    split; [eapply ngc_keep_stack; [exact AGy| exact FR| lia| intros a Ha; apply PS; cbn [cells_size csize Nat.add] in Ha; lia]|].
    split.
    { eapply agrees_on_trans; [exact AG|]. eapply ngc_keeps_callee2 with (SPA := SPA) (Pn := Pn) (CLg := (CL ++ PB)%list); [exact G| exact ICL| exact ICk| lia| lia| exact AGy|].
      intros a K (N1 & N2 & _) NF0. cbn [fst snd] in N1, N2.
      assert (NSP : ~ (SPA <= a < SPA + 152)).
      { destruct K as [K|[K|[K|K]]]; [lia| | |].
        - pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; apply in_block_app; left; exact K)). lia.
        - apply in_frames_In in K as (fr & Hfr & Hr). destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAx _].
          pose proof (proj1 (Forall_forall _ _) FAx fr (IFL _ Hfr)) as (_ & TOPx & _). lia.
        - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G ltac:(eapply in_frame_sh_incl; [exact IFL| exact K])) as BD. unfold KLS in BD. lia. }
      apply HPn; [lia| lia| | exact NSP]. intros b Hb Hin.
      (* [comment removed for export] *)
      destruct K as [K|[K|[K|K]]].
      - apply (NPB a ltac:(left; lia) b Hb Hin).
      - apply in_block_In in K as (b' & Hb' & Hr').
        pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _).
        apply blocks_apart_app_inv in BA as (_ & _ & BX). specialize (BX b' b Hb' Hb). unfold apart in BX. lia.
      - assert (HbA : in_block ((CL ++ PB) ++ FB) a) by (apply in_block_In; exists b; split; [apply in_or_app; left; apply in_or_app; right; exact Hb| lia]).
        exact (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G ltac:(eapply in_frames_incl; [exact IFL| exact K]) HbA).
      - assert (Hs : (0 < cb_size b)%Z) by lia. destruct (PBF b Hb Hs) as (TOP & BAND).
        assert (SH : in_frame_sh (NGFR Fb :: FL) a) by (eapply in_frame_sh_incl; [exact IFL| exact K]).
        pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G SH) as BD.
        exact (ablk_clear_band _ _ a BAND ltac:(unfold KLS; lia) Hin). }
    split.
    { destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. cbn [map] in MGc |- *.
      eapply ngc_keep_cobj; [exact AGy| exact MGc| exact (proj1 OMG)| exact ICk| exact IFL| cbn [cells_size csize Nat.add]; lia|].
      intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply HPn; [lia| lia| apply NPB; right; right; right; lia| lia]. }
    unfold ngc_shadow in SHC |- *.
    eapply agrees_rw_cells; [exact AGy| exact SHC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. split.
    - right; right; right. apply Exists_cons_hd. cbn [fb_addr fb_size fst snd]. change (Z.shiftr 64 3) with 8. lia.
    - apply HPn; [rewrite SHE in Ha; Z.div_mod_to_equations; lia| rewrite SHE in Ha; Z.div_mod_to_equations; lia| apply NPB; right; right; left; lia| rewrite SHE in Ha; Z.div_mod_to_equations; lia].
  Qed.
  End Sz11.
  #[using="FO fflagA GL"] Lemma ngc_inv_keep2 : ltac:(let t := eval cbv delta [ngc_inv_keep2__stmt] in ngc_inv_keep2__stmt in exact t).
  Proof. intros ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm RNGy sy PB' my CLk Pn. ltac2:(SecDiet.SzSec.closeP 'ngc_inv_keep2__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcKit.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcKit.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).

  (* [comment removed for export] *)
  Definition ngc_spo__stmt : Prop := forall ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx CLx mm budget,
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m -> fp_le RNG RNGx ->
    GIOA L RNGx sx CLx FB (NGFR Fb :: FL) mm -> stk asegs mm lo SPA -> mem_inv asegs mm -> budget <= PCAP_L2_STACK - 287 ->
    std_pre_o GIOA L RNGx (Z_to_bv 64 SPA) tp sx CLx FB (NGFR Fb :: FL) lo budget mm.
  Section Sz1.
  Variables ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx CLx mm budget : ltac2:(SecDiet.SzSec.tyM 'ngc_spo__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="Type"] Lemma ngc_spo__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_spo__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros CTX FP G ST MI HB.
    destruct CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SPAB & SPA32).
    unfold PCAP_L2_STACK in BU, HB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (E : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia). unfold std_pre_o. rewrite E.
    split; [exact G|]. split; [exact ST|]. split; [exact LO|]. split; [lia|]. split; [lia|]. split; [exact MI|]. split; [exact TPE|].
    split; [Z.div_mod_to_equations; lia|].
    split; [eapply rng_fp_le; eassumption|]. split; [eapply rng_fp_le; eassumption|]. split; eapply rng_fp_le; eassumption.
  Qed.
  End Sz1.
  #[using="Type"] Lemma ngc_spo : ltac:(let t := eval cbv delta [ngc_spo__stmt] in ngc_spo__stmt in exact t).
  Proof. intros ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx CLx mm budget. ltac2:(SecDiet.SzSec.closeP 'ngc_spo__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_ucaller__stmt : Prop := forall d' L (sp s0 ra : word) SPA mm trC X (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : cell),
    ucallerA (depth_check_header true) L mm sp s0 ra trC ->
    (bv_unsigned sp - 287 <= SPA <= bv_unsigned sp - 256) -> ATOP + 4096 <= SPA -> bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
    rw_cells asegs mm (bv_unsigned sp + -104) [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; C8 s0; C8 ra] ->
    cells_size [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] = 88%nat ->
    ACLIENT_LO <= X < ACLIENT_HI -> (S d' <= depth_check_header true)%nat ->
    ucallerA d' L mm (Z_to_bv 64 SPA) sp (Z_to_bv 64 X) (bv_unsigned ra :: trC).
  Section Sz2.
  Variables d' L sp s0 ra SPA mm trC X c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ltac2:(SecDiet.SzSec.tyM 'ngc_ucaller__stmt "vvvvvvvvvvvvvvvvvvvv" @d').
  #[using="Type"] Lemma ngc_ucaller__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_ucaller__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros UC SPAB LO SPT ALN FRs SZ HX HD.
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
  End Sz2.
  #[using="Type"] Lemma ngc_ucaller : ltac:(let t := eval cbv delta [ngc_ucaller__stmt] in ngc_ucaller__stmt in exact t).
  Proof. intros d' L sp s0 ra SPA mm trC X c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10. ltac2:(SecDiet.SzSec.closeP 'ngc_ucaller__body "vvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma ngc_keep_stack : forall (FLx : list fblock) (CLx : list cblk) SPA (Pn : Z -> Prop) m1 m2 A cs,
    agrees_on (fun a => client_keeps FLx CLx SPA a /\ Pn a) m1 m2 -> rw_cells asegs m1 A cs -> SPA <= A ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> Pn a) -> rw_cells asegs m2 A cs.
  Proof. intros FLx CLx SPA Pn m1 m2 A cs AG HC HA HP. eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. split; [left; lia| apply HP; exact Ha]. Qed.
  #[using="Type"] Lemma ngc_keep_frame : forall (FLx : list fblock) (CLx : list cblk) SPA Fb (Pn : Z -> Prop) m1 m2 A cs,
    agrees_on (fun a => client_keeps (NGFR Fb :: FLx) CLx SPA a /\ Pn a) m1 m2 -> rw_cells asegs m1 A cs ->
    Fb <= A -> A + Z.of_nat (cells_size cs) <= Fb + 64 ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> Pn a) -> rw_cells asegs m2 A cs.
  Proof.
    intros FLx CLx SPA Fb Pn m1 m2 A cs AG HC H1 H2 HP. eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. split; [| apply HP; exact Ha].
    right; right; left. apply Exists_cons_hd. cbn [fb_addr fb_size fst snd]. lia.
  Qed.
  #[using="Type"] Lemma ngc_keep_cobj : forall (FL FLx : list fblock) (CL CLx : list cblk) SPA (Pn : Z -> Prop) m1 m2 A n cs,
    agrees_on (fun a => client_keeps FLx CLx SPA a /\ Pn a) m1 m2 -> rw_cells asegs m1 A cs -> clocA FL CL A n ->
    incl CL CLx -> incl FL FLx -> Z.of_nat (cells_size cs) <= n ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> Pn a) -> rw_cells asegs m2 A cs.
  Proof.
    intros FL FLx CL CLx SPA Pn m1 m2 A n cs AG HC LOC IC IF Hn HP. eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. split; [| apply HP; exact Ha].
    eapply clocA_keeps; [eapply clocA_incl; [exact LOC| exact IC| exact IF]| lia].
  Qed.

  #[using="Type"] Lemma ngc_keep_block : forall (FLx : list fblock) (CLx : list cblk) SPA (Pn : Z -> Prop) m1 m2 A cs (b : cblk),
    agrees_on (fun a => client_keeps FLx CLx SPA a /\ Pn a) m1 m2 -> rw_cells asegs m1 A cs -> In b CLx ->
    cb_addr b <= A -> A + Z.of_nat (cells_size cs) <= cb_addr b + cb_size b ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> Pn a) -> rw_cells asegs m2 A cs.
  Proof.
    intros FLx CLx SPA Pn m1 m2 A cs b AG HC Hb H1 H2 HP. eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. split; [| apply HP; exact Ha].
    right; left. apply in_block_In. exists b. split; [exact Hb| lia].
  Qed.

  (* [comment removed for export] *)
  Definition ngc_uc_now__stmt : Prop := forall ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm,
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB mm ->
    ucallerA (depth_check_header true) L mm sp s0 ra trC.
  Section Sz7.
  Variables ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm : ltac2:(SecDiet.SzSec.tyM 'ngc_uc_now__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="FO fflagA GL"] Lemma ngc_uc_now__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_uc_now__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros CTX INV.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (ICL : incl CL (CL ++ PB)) by (apply incl_appl, incl_refl).
    assert (IFL : incl FL (NGFR Fb :: FL)) by (apply incl_tl, incl_refl).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)) as (ERLO & ERHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)) as (EBLO & EBHI).
    eapply ucaller_keep; [exact UC| exact TOP47|]. intros a Ha. apply (AG a); [lia|]. split; [left; lia|]. cbn [outside fst snd]. lia.
  Qed.
  End Sz7.
  #[using="FO fflagA GL"] Lemma ngc_uc_now : ltac:(let t := eval cbv delta [ngc_uc_now__stmt] in ngc_uc_now__stmt in exact t).
  Proof. intros ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm. ltac2:(SecDiet.SzSec.closeP 'ngc_uc_now__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_inv_keep__stmt : Prop := forall ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m
      RNGx sx PB mm RNGy sy PB' my RNGk sk mk (CLk : list cblk) (Pn : Z -> Prop),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB mm ->
    fp_le RNGx RNGy -> GIOA L RNGy sy (CL ++ PB') FB (NGFR Fb :: FL) my -> ps_outfile sy = ps_outfile sx ->
    mem_inv asegs my -> stk asegs my lo SPA ->
    agrees_on (fun a => client_keeps (NGFR Fb :: FL) CLk SPA a /\ Pn a) mm my -> incl CL CLk ->
    GIOA L RNGk sk CLk FB (NGFR Fb :: FL) mk ->      (* [comment removed for export] *)
    (forall a, ~ (EB <= a < EB + 256) -> ~ (ERR <= a < ERR + 4) -> Pn a) ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGy sy PB' my.
  Section Sz8.
  Variables ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm RNGy sy PB' my RNGk sk mk CLk Pn : ltac2:(SecDiet.SzSec.tyM 'ngc_inv_keep__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="FO fflagA GL"] Lemma ngc_inv_keep__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_inv_keep__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros CTX INV FPy Gy OFy MIy STy AGy ICk Gk HPn.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. pose proof (Forall_inv FAll) as (FBAND & FTOP & F64 & _ & _ & _ & _ & _).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64. pose proof (ablk_lin _ _ FBAND) as (FIMG & Fb0 & _ & _). unfold AIMG_HI in FIMG.
    assert (SHE : Z.shiftr Fb 3 + 2147450880 = Fb / 8 + 2147450880) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    band_ind FBAND bF.
    assert (ICL : incl CL (CL ++ PB)) by (apply incl_appl, incl_refl).
    assert (IFL : incl FL (NGFR Fb :: FL)) by (apply incl_tl, incl_refl).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)) as (ERLO & ERHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)) as (EBLO & EBHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL) ltac:(lia)) as ERBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL) ltac:(lia)) as EBBAND.
    band_ind ERBAND bE. band_ind EBBAND bB.
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL (incl_refl _)) ltac:(lia)) as (kE & kEr & kE1 & kE2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL (incl_refl _)) ltac:(lia)) as (kB & kBr & kB1 & kB2).
    cbn [fb_addr fb_size fst snd] in kE1, kE2, kB1, kB2.
    assert (PS : forall a, SPA <= a -> Pn a) by (intros a Ha; apply HPn; lia).
    split; [intros b j Hb; apply FPy, FP; exact Hb|]. split; [exact Gy|]. split; [rewrite OFy; exact OF|]. split; [exact MIy|]. split; [exact STy|].
    split; [eapply agrees_stk; [exact AGy| exact STG| intros a Ha; split; [left; lia| apply PS; lia]]|].
    split; [eapply ngc_keep_stack; [exact AGy| exact FR| lia| intros a Ha; apply PS; cbn [cells_size csize Nat.add] in Ha; lia]|].
    split.
    { eapply agrees_on_trans; [exact AG|]. eapply (ngc_keeps_callee FO GIOA fflagA GL) with (SPA := SPA) (Pn := Pn); [exact Gk| exact ICk| lia| lia| exact AGy|].
      intros a K (N1 & N2 & _) NF0. cbn [fst snd] in N1, N2. apply HPn; lia. }
    split.
    { destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. cbn [map] in MGc |- *.
      eapply ngc_keep_cobj; [exact AGy| exact MGc| exact (proj1 OMG)| exact ICk| exact IFL| cbn [cells_size csize Nat.add]; lia|].
      intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply HPn; lia. }
    unfold ngc_shadow in SHC |- *.
    eapply agrees_rw_cells; [exact AGy| exact SHC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. split.
    - right; right; right. apply Exists_cons_hd. cbn [fb_addr fb_size fst snd]. change (Z.shiftr 64 3) with 8. lia.
    - apply HPn; rewrite SHE in Ha; Z.div_mod_to_equations; lia.
  Qed.
  End Sz8.
  #[using="FO fflagA GL"] Lemma ngc_inv_keep : ltac:(let t := eval cbv delta [ngc_inv_keep__stmt] in ngc_inv_keep__stmt in exact t).
  Proof. intros ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm RNGy sy PB' my RNGk sk mk CLk Pn. ltac2:(SecDiet.SzSec.closeP 'ngc_inv_keep__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngc_cobj_now__stmt : Prop := forall ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm,
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB mm ->
    cobjA RNGx mm FL CL MG 4 /\ cobjA RNGx mm FL CL ERR 4 /\ cobjA RNGx mm FL CL EB 256.
  Section Sz9.
  Variables ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm : ltac2:(SecDiet.SzSec.tyM 'ngc_cobj_now__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="FO fflagA GL"] Lemma ngc_cobj_now__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_cobj_now__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros CTX INV.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    assert (ICL : incl CL (CL ++ PB)) by (apply incl_appl, incl_refl).
    assert (IFL : incl FL (NGFR Fb :: FL)) by (apply incl_tl, incl_refl).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL) ltac:(lia)) as ERBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL) ltac:(lia)) as EBBAND.
    assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(ERR, ERR + 4); (EB, EB + 256)]%Z)
      by (apply Forall_cons; [exact ERBAND| apply Forall_cons; [exact EBBAND| apply Forall_nil]]).
    pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G IFL AG FXB) as AGsh.
    split; [exact (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OMG G ICL IFL AGsh ltac:(lia))|].
    split; [exact (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OERR G ICL IFL AGsh ltac:(lia))|].
    exact (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G ICL IFL AGsh ltac:(lia)).
  Qed.
  End Sz9.
  #[using="FO fflagA GL"] Lemma ngc_cobj_now : ltac:(let t := eval cbv delta [ngc_cobj_now__stmt] in ngc_cobj_now__stmt in exact t).
  Proof. intros ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm. ltac2:(SecDiet.SzSec.closeP 'ngc_cobj_now__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma ngc_keeps_callee2 : forall L RNGg sg (CLg CLk FB : list cblk) fr FL m0 m1 m2 (CL : list cblk) SP SPA WX (Pn : Z -> Prop),
    GIOA L RNGg sg CLg FB (fr :: FL) m0 -> incl CL CLg -> incl CL CLk -> (ATOP <= SPA)%Z -> (SPA <= SP)%Z ->
    agrees_on (fun a => client_keeps (fr :: FL) CLk SPA a /\ Pn a) m1 m2 ->
    (forall a, client_keeps FL CL SP a -> outside WX a -> ~ (fb_addr fr <= a < fb_addr fr + fb_size fr)%Z -> Pn a) ->
    agrees_on (fun a => client_keeps FL CL SP a /\ outside WX a) m1 m2.
  Proof.
    intros L RNGg sg CLg CLk FB fr FL m0 m1 m2 CL SP SPA WX Pn G ICg ICk HA HS AG HP.
    eapply agrees_on_weaken; [exact AG|]. intros a (K & O). split.
    - eapply ngc_keeps_up; [exact K| exact HS| exact ICk| apply incl_tl, incl_refl].
    - apply HP; [exact K| exact O|]. assert (HSP : (ATOP <= SP)%Z) by lia. exact (proj1 (keeps_not_own_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ a G ICg HSP K)).
  Qed.

  Definition ngc_inv_keep2__stmt : Prop := forall ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m
      RNGx sx PB mm RNGy sy PB' my (CLk : list cblk) (Pn : Z -> Prop),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB mm ->
    fp_le RNGx RNGy -> GIOA L RNGy sy (CL ++ PB') FB (NGFR Fb :: FL) my -> ps_outfile sy = ps_outfile sx ->
    mem_inv asegs my -> stk asegs my lo SPA ->
    agrees_on (fun a => client_keeps (NGFR Fb :: FL) CLk SPA a /\ Pn a) mm my -> incl CL CLk ->
    (forall a, ~ (EB <= a < EB + 256) -> ~ (ERR <= a < ERR + 4) -> (forall b, In b PB -> ~ (cb_addr b <= a < cb_addr b + cb_size b)) -> ~ (SPA <= a < SPA + 152) -> Pn a) ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGy sy PB' my.
  Section Sz11.
  Variables ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm RNGy sy PB' my CLk Pn : ltac2:(SecDiet.SzSec.tyM 'ngc_inv_keep2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="FO fflagA GL"] Lemma ngc_inv_keep2__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_inv_keep2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros CTX INV FPy Gy OFy MIy STy AGy ICk HPn.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. pose proof (Forall_inv FAll) as (FBAND & FTOP & F64 & _ & _ & _ & _ & _).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64. pose proof (ablk_lin _ _ FBAND) as (FIMG & Fb0 & _ & _). unfold AIMG_HI in FIMG.
    assert (SHE : Z.shiftr Fb 3 + 2147450880 = Fb / 8 + 2147450880) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    band_ind FBAND bF.
    assert (ICL : incl CL (CL ++ PB)) by (apply incl_appl, incl_refl).
    assert (IFL : incl FL (NGFR Fb :: FL)) by (apply incl_tl, incl_refl).
    (* [comment removed for export] *)
    assert (PBF : forall b, In b PB -> (0 < cb_size b -> cb_addr b + cb_size b <= ATOP /\ ablk (cb_addr b) (cb_addr b + cb_size b))%Z).
    { intros b Hb Hs. destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; apply in_or_app; right; exact Hb)) as ((BAND & _ & TOP & _) & _). split; [exact TOP| exact BAND]. }
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)) as (ERLO & ERHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)) as (EBLO & EBHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL)) as (MGLO & MGHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL) ltac:(lia)) as ERBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL) ltac:(lia)) as EBBAND.
    band_ind ERBAND bE. band_ind EBBAND bB.
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL (incl_refl _)) ltac:(lia)) as (kE & kEr & kE1 & kE2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL (incl_refl _)) ltac:(lia)) as (kB & kBr & kB1 & kB2).
    cbn [fb_addr fb_size fst snd] in kE1, kE2, kB1, kB2.
    (* [comment removed for export] *)
    assert (NPB : forall a, (SPA <= a \/ Fb <= a < Fb + 64 \/ Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 8 \/ MG <= a < MG + 4)%Z ->
                  forall b, In b PB -> ~ (cb_addr b <= a < cb_addr b + cb_size b)%Z).
    { intros a Ha b Hb Hin. assert (Hs : (0 < cb_size b)%Z) by lia. destruct (PBF b Hb Hs) as (TOP & BAND).
      destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ b (NGFR Fb) G ltac:(apply in_or_app; left; apply in_or_app; right; exact Hb) ltac:(left; reflexivity) Hs) as (k & kr & k1 & k2).
      cbn [fb_addr fb_size fst snd] in k1, k2.
      destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) (incl_refl _) IFL) Hb ltac:(lia) Hs) as (kM & kMr & kM1 & kM2).
      pose proof (ablk_ind _ _ BAND) as (bb & bbr & bbhi & bblo & bbimg). rewrite SHE in Ha. Z.div_mod_to_equations. lia. }
    assert (PS : forall a, SPA + 152 <= a -> Pn a) by (intros a Ha; apply HPn; [lia| lia| apply NPB; left; lia| lia]).
    split; [intros b jj Hb; apply FPy, FP; exact Hb|]. split; [exact Gy|]. split; [rewrite OFy; exact OF|]. split; [exact MIy|]. split; [exact STy|].
    split; [eapply agrees_stk; [exact AGy| exact STG| intros a Ha; split; [left; lia| apply PS; lia]]|].
    split; [eapply ngc_keep_stack; [exact AGy| exact FR| lia| intros a Ha; apply PS; cbn [cells_size csize Nat.add] in Ha; lia]|].
    split.
    { eapply agrees_on_trans; [exact AG|]. eapply ngc_keeps_callee2 with (SPA := SPA) (Pn := Pn) (CLg := (CL ++ PB)%list); [exact G| exact ICL| exact ICk| lia| lia| exact AGy|].
      intros a K (N1 & N2 & _) NF0. cbn [fst snd] in N1, N2.
      assert (NSP : ~ (SPA <= a < SPA + 152)).
      { destruct K as [K|[K|[K|K]]]; [lia| | |].
        - pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; apply in_block_app; left; exact K)). lia.
        - apply in_frames_In in K as (fr & Hfr & Hr). destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAx _].
          pose proof (proj1 (Forall_forall _ _) FAx fr (IFL _ Hfr)) as (_ & TOPx & _). lia.
        - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G ltac:(eapply in_frame_sh_incl; [exact IFL| exact K])) as BD. unfold KLS in BD. lia. }
      apply HPn; [lia| lia| | exact NSP]. intros b Hb Hin.
      (* [comment removed for export] *)
      destruct K as [K|[K|[K|K]]].
      - apply (NPB a ltac:(left; lia) b Hb Hin).
      - apply in_block_In in K as (b' & Hb' & Hr').
        pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _).
        apply blocks_apart_app_inv in BA as (_ & _ & BX). specialize (BX b' b Hb' Hb). unfold apart in BX. lia.
      - assert (HbA : in_block ((CL ++ PB) ++ FB) a) by (apply in_block_In; exists b; split; [apply in_or_app; left; apply in_or_app; right; exact Hb| lia]).
        exact (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G ltac:(eapply in_frames_incl; [exact IFL| exact K]) HbA).
      - assert (Hs : (0 < cb_size b)%Z) by lia. destruct (PBF b Hb Hs) as (TOP & BAND).
        assert (SH : in_frame_sh (NGFR Fb :: FL) a) by (eapply in_frame_sh_incl; [exact IFL| exact K]).
        pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G SH) as BD.
        exact (ablk_clear_band _ _ a BAND ltac:(unfold KLS; lia) Hin). }
    split.
    { destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. cbn [map] in MGc |- *.
      eapply ngc_keep_cobj; [exact AGy| exact MGc| exact (proj1 OMG)| exact ICk| exact IFL| cbn [cells_size csize Nat.add]; lia|].
      intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply HPn; [lia| lia| apply NPB; right; right; right; lia| lia]. }
    unfold ngc_shadow in SHC |- *.
    eapply agrees_rw_cells; [exact AGy| exact SHC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. split.
    - right; right; right. apply Exists_cons_hd. cbn [fb_addr fb_size fst snd]. change (Z.shiftr 64 3) with 8. lia.
    - apply HPn; [rewrite SHE in Ha; Z.div_mod_to_equations; lia| rewrite SHE in Ha; Z.div_mod_to_equations; lia| apply NPB; right; right; left; lia| rewrite SHE in Ha; Z.div_mod_to_equations; lia].
  Qed.
  End Sz11.
  #[using="FO fflagA GL"] Lemma ngc_inv_keep2 : ltac:(let t := eval cbv delta [ngc_inv_keep2__stmt] in ngc_inv_keep2__stmt in exact t).
  Proof. intros ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm RNGy sy PB' my CLk Pn. ltac2:(SecDiet.SzSec.closeP 'ngc_inv_keep2__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcKit.
End CANSEC1.
End TwB.
End F_ngchk_kitA.

(* [comment removed for export] *)
Module F_ngchk_ngiA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfHandleA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition ngc_spill (P EB Fb : Z) (j : list byte) : list cell :=
  [ C8 (Z_to_bv 64 (P + 24)); C8 (Z_to_bv 64 (Z.shiftr (P + 656) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 656));
    C8 (Z_to_bv 64 (Z.shiftr (P + 156) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 156)); C8 (Z_to_bv 64 (Z.shiftr (P + 24) 3 + 2147450880));
    C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 (P + 648)); C8 (Z_to_bv 64 P);
    C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb) ].
Remark ngc_spill_size : forall P EB Fb j, cells_size (ngc_spill P EB Fb j) = 128%nat.
Proof. intros. reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT}.
  (* [comment removed for export] *)
  Definition ngcells (P : Z) (np bsz buf sw maj min snap lt ext prec cln : cell) : list cell :=
    [ C8 (Z_to_bv 64 0); np; C4 (Z_to_bv 64 (-1)); bsz; buf; CB 12 (repeat (Z_to_bv 8 0) 12); C4 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (P + 648)); sw; CB 4 (repeat (Z_to_bv 8 0) 4); CB 8 z8; CB 16 (repeat (Z_to_bv 8 0) 16);
      maj; min; snap; lt; ext;
      CB 12 (repeat (Z_to_bv 8 0) 12); C8 (Z_to_bv 64 0); CB 28 (repeat (Z_to_bv 8 0) 28); prec;
      CB 48 fd_pad48; C8 (Z_to_bv 64 0); CB 304 (repeat (Z_to_bv 8 0) 304);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
      CB 72 (repeat (Z_to_bv 8 0) 72); CB 8 z8; C8 (Z_to_bv 64 0); CB 8 z8; cln ].
  #[using="Type"] Remark ngcells_size : forall P np bsz buf sw maj min snap lt ext prec cln,
    csize np = 8%nat -> csize bsz = 4%nat -> csize buf = 8%nat -> csize sw = 4%nat -> csize maj = 4%nat -> csize min = 4%nat ->
    csize snap = 4%nat -> csize lt = 4%nat -> csize ext = 4%nat -> csize prec = 4%nat -> csize cln = 8%nat ->
    cells_size (ngcells P np bsz buf sw maj min snap lt ext prec cln) = 648%nat.
  Proof. intros. cbn. lia. Qed.

  (* [comment removed for export] *)
  Definition ngcells0 (P : Z) : list cell :=
    ngcells P (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0))
              (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)).
  Definition ng0 : pcap_ng_sf := mkNg 0 0 0 0 [].
  Definition pad0 : list byte := repeat (Z_to_bv 8 0) 4.

  (* [comment removed for export] *)
  Definition blank_recell_ng__stmt : Prop := forall m P,
    rw_cells asegs m P ([CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 (-1)); CB 28 (repeat (Z_to_bv 8 0) 28);
                         C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); CB 128 (repeat (Z_to_bv 8 0) 128); C4 (Z_to_bv 64 (-1));
                         CB (Z.to_nat (PCAP_NG_SF_TOTAL - 188)) (repeat (Z_to_bv 8 0) (Z.to_nat (PCAP_NG_SF_TOTAL - 188)))]) ->
    rw_cells asegs m P (ngcells0 P ++ ng_cells ng0 0 pad0).
  Section Sz3.
  Variables m P : ltac2:(SecDiet.SzSec.tyM 'blank_recell_ng__stmt "vv" @m).
  #[using="Type"] Lemma blank_recell_ng__body : ltac2:(SecDiet.SzSec.bodyP 'blank_recell_ng__stmt "vv").
  Proof.
    intros Hc.
    destruct (rw_cells_cut _ _ _ 3 Hc) as [A X]. destruct (rw_cells_cut _ _ _ 1 X) as [B C]. clear Hc X.
    cbn [firstn skipn cells_size csize Nat.add] in A, B, C.
    unfold PCAP_NG_SF_TOTAL in C. change (Z.to_nat (680 - 188)) with 492%nat in C. unfold PCAP_PRIV_OFF in B.
    assert (A' : rw_cells asegs m P (firstn 7 (ngcells0 P))).
    { eapply rw_cells_recell; [exact A | cbn; repeat split; exact Logic.I | vm_compute; reflexivity]. }
    assert (C' : rw_cells asegs m (P + Z.of_nat 48 + Z.of_nat 8) (skipn 8 (ngcells0 P ++ ng_cells ng0 0 pad0))).
    { eapply rw_cells_recell; [exact C | cbn; repeat split; exact Logic.I | unfold fd_pad48, z8, pad0; vm_compute; reflexivity]. }
    pose proof (rw_cells_uncut _ _ _ _ _ A' B ltac:(cbn; lia)) as AB.
    pose proof (rw_cells_uncut _ _ _ _ _ AB C' ltac:(cbn; lia)) as ABC. exact ABC.
  Qed.
  End Sz3.
  #[using="Type"] Lemma blank_recell_ng : ltac:(let t := eval cbv delta [blank_recell_ng__stmt] in blank_recell_ng__stmt in exact t).
  Proof. intros m P. ltac2:(SecDiet.SzSec.closeP 'blank_recell_ng__body "vv"). Qed.

  Section Handle.
    Context {hptr : Type}.
    #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
    (* [comment removed for export] *)
    Definition ngc_p (f qs : hptr) (sw : bool) (BS0 MINOR : Z) (qb : hptr) (bufalloc : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) : pcapT :=
      mkPcap qs f BS0 bufalloc qb bufdata sw 1 MINOR 0 0 0 0 0 [] hdr0 (PrivNg sg i).
  End Handle.
  (* [comment removed for export] *)
  Definition ngc_hcells (P : Z) (sw : bool) (BS0 MINOR : Z) (B : Z) : list cell :=
    ngcells P (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 BS0)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 (Z.b2z sw))) (C4 (Z_to_bv 64 1)) (C4 (Z_to_bv 64 MINOR))
              (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  #[using="Type"] Lemma hcells_cut : forall mX P sw BS0 MINOR B,
    rw_cells asegs mX P (ngc_hcells P sw BS0 MINOR B) ->
    rw_cells asegs mX (P + 24) [C8 (Z_to_bv 64 B)]
    /\ rw_cells asegs mX (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z sw))].
  Proof.
    intros mX P sw BS0 MINOR B HC. unfold ngc_hcells, ngcells in HC.
    destruct (rw_cells_cut _ _ _ 4 HC) as [_ X]. destruct (rw_cells_cut _ _ _ 1 X) as [X1 X2]. destruct (rw_cells_cut _ _ _ 2 X2) as [_ X3]. destruct (rw_cells_cut _ _ _ 2 X3) as [X4 _].
    cbn [firstn skipn cells_size csize Nat.add app] in X1, X4. unfold PCAP_PRIV_OFF.
    split; [replace (P + 24)%Z with (P + Z.of_nat 24)%Z by lia; exact X1|].
    replace (P + 48)%Z with (P + Z.of_nat 24 + Z.of_nat 8 + Z.of_nat 16)%Z by lia. exact X4.
  Qed.
  #[using="Type"] Lemma hcells_cut20 : forall mX P sw BS0 MINOR B,
    rw_cells asegs mX P (ngc_hcells P sw BS0 MINOR B) -> rw_cells asegs mX (P + 20) [C4 (Z_to_bv 64 BS0); C8 (Z_to_bv 64 B)].
  Proof.
    intros mX P sw BS0 MINOR B HC. unfold ngc_hcells, ngcells in HC.
    destruct (rw_cells_cut _ _ _ 3 HC) as [_ X]. destruct (rw_cells_cut _ _ _ 2 X) as [X1 _]. cbn [firstn skipn cells_size csize Nat.add app] in X1.
    replace (P + 20)%Z with (P + Z.of_nat 20)%Z by lia. exact X1.
  Qed.
  #[using="Type"] Lemma ngcells_cut656 : forall mX P sg I pad,
    rw_cells asegs mX (P + 648) (ng_cells sg I pad) -> rw_cells asegs mX (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize sg))].
  Proof.
    intros mX P sg I pad HN. unfold ng_cells in HN. destruct (rw_cells_cut _ _ _ 1 HN) as [_ X]. destruct (rw_cells_cut _ _ _ 1 X) as [X1 _].
    cbn [firstn skipn cells_size csize Nat.add app] in X1. replace (P + 656)%Z with (P + 648 + Z.of_nat 8)%Z by lia. exact X1.
  Qed.
  #[using="Type"] Lemma ngcells_cut672 : forall mX P sg I pad,
    rw_cells asegs mX (P + 648) (ng_cells sg I pad) -> rw_cells asegs mX (P + 672) [C8 (Z_to_bv 64 I)].
  Proof.
    intros mX P sg I pad HN. unfold ng_cells in HN. destruct (rw_cells_cut _ _ _ 5 HN) as [_ X]. cbn [firstn skipn cells_size csize Nat.add app] in X.
    replace (P + 672)%Z with (P + 648 + Z.of_nat 24)%Z by lia. exact X.
  Qed.
  (* [comment removed for export] *)
  Definition hcells_rebuf__stmt : Prop := forall mX mY P sw BS0 MINOR B B',
    rw_cells asegs mX P (ngc_hcells P sw BS0 MINOR B) ->
    agrees_on (fun a => (P <= a < P + 24 \/ P + 32 <= a < P + 648)%Z) mX mY ->
    rw_cells asegs mY (P + 24) [C8 (Z_to_bv 64 B')] -> rw_cells asegs mY P (ngc_hcells P sw BS0 MINOR B').
  Section Sz8.
  Variables mX mY P sw BS0 MINOR B B' : ltac2:(SecDiet.SzSec.tyM 'hcells_rebuf__stmt "vvvvvvvv" @mX).
  #[using="Type"] Lemma hcells_rebuf__body : ltac2:(SecDiet.SzSec.bodyP 'hcells_rebuf__stmt "vvvvvvvv").
  Proof.
    intros HC AG HB.
 unfold ngc_hcells, ngcells in HC |- *.
    destruct (rw_cells_cut _ _ _ 4 HC) as [A X]. destruct (rw_cells_cut _ _ _ 1 X) as [_ C]. clear X. cbn [firstn skipn cells_size csize Nat.add app] in A, C.
    assert (A' : rw_cells asegs mY P [C8 z64; C8 z64; C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 BS0)]).
    { eapply agrees_rw_cells; [exact AG| exact A| intros a Ha; cbn in Ha; cbv beta; lia]. }
    lazymatch type of C with rw_cells _ _ ?AA ?cs => assert (C' : rw_cells asegs mY AA cs)
      by (eapply agrees_rw_cells; [exact AG| exact C| intros a Ha; cbn in Ha; cbv beta; lia]) end.
    replace (P + 24)%Z with (P + Z.of_nat 24)%Z in HB by lia.
    pose proof (rw_cells_uncut _ _ _ _ _ A' HB ltac:(cbn; lia)) as AB.
    exact (rw_cells_uncut _ _ _ _ _ AB C' ltac:(cbn; lia)).
  Qed.
  End Sz8.
  #[using="Type"] Lemma hcells_rebuf : ltac:(let t := eval cbv delta [hcells_rebuf__stmt] in hcells_rebuf__stmt in exact t).
  Proof. intros mX mY P sw BS0 MINOR B B'. ltac2:(SecDiet.SzSec.closeP 'hcells_rebuf__body "vvvvvvvv"). Qed.
End CANSEC1.

Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgiDefs.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).

  (* [comment removed for export] *)
  Definition ngi_inv (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock)
      (lo MG EB ERR SPA Fb : Z) (magic : list Z) (o : option hptr) (m : mem)
      (f qs : hptr) (P : Z) (sw : bool) (BS0 MINOR : Z)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem) (qb : hptr) (B ba : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) (I : Z)
      (pad bs e j : list byte) (ccs fcs : list cell) (k0 k1 k2 : word) : Prop :=
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx ((qs, P, 680) :: (qb, B, ba) :: IBLK i I sg) mm
    /\ rw_cells asegs mm SPA (ngc_spill P EB Fb j) /\ rw_cells asegs mm (SPA + 128) ccs /\ cells_size ccs = 24%nat
    /\ rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) /\ cells_size fcs = 32%nat
    /\ rw_cells asegs mm ERR [C4 z64] /\ rw_cells asegs mm EB [CB 256 e]
    /\ rw_cells asegs mm P (ngc_hcells P sw BS0 MINOR B) /\ rw_cells asegs mm (P + 648) (ng_cells sg I pad)
    /\ ng_user_tsresol sg = 1000000 /\ ng_max_blocksize sg = INITIAL_MAX_BLOCKSIZE /\ 0 <= ng_ifcount sg < 2^32 /\ 0 <= ng_ifaces_size sg < 2^32
    /\ ifaces_ok (ngc_p f qs sw BS0 MINOR qb ba bufdata sg i) I mm
    /\ rw_cells asegs mm B [CB (Z.to_nat ba) bs] /\ firstn (length bufdata) bs = map b8 bufdata
    /\ Z.of_nat (length bufdata) <= ba /\ 1 <= ba < 2^32 /\ BS0 <= ba /\ Forall (fun z => 0 <= z < 256) bufdata.

  (* [comment removed for export] *)
  Definition ngc_inv_own__stmt : Prop := forall ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m
      RNGx sx PB mm my W,
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB mm ->
    Forall (own_ivA [NGFR Fb] PB (bv_unsigned sp)) W -> munch W mm my -> wmono asegs mm my -> mem_inv asegs my -> stk asegs my lo SPA ->
    (forall a, SPA + 152 <= a < bv_unsigned sp \/ MG <= a < MG + 4 \/ Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 8 -> outside W a) ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB my.
  Section Sz9.
  Variables ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm my W : ltac2:(SecDiet.SzSec.tyM 'ngc_inv_own__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_inv_own__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_inv_own__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL.
 intros CTX INV FWs MU WM MIy STy OUT.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (FXs : Forall (cobj_iv FL CL) []) by apply Forall_nil.
    rewrite <- (app_nil_r W) in MU.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ my _ _ _ FWs FXs G MU WM ltac:(lia)) as [Gy AGy].
    rewrite app_nil_r in MU.
    assert (AGS : agrees_on (fun a => outside W a) mm my) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    split; [exact FP|]. split; [exact Gy|]. split; [exact OF|]. split; [exact MIy|]. split; [exact STy|].
    split. { eapply agrees_stk; [exact AGS| exact STG|]. intros a Ha. apply OUT. left. lia. }
    split. { eapply agrees_rw_cells; [exact AGS| exact FR|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT. left. lia. }
    split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AGy|]. intros a (K & _). split; [exact K| exact Logic.I]. }
    split. { destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. cbn [map] in MGc |- *.
             eapply agrees_rw_cells; [exact AGS| exact MGc|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT. right; left. lia. }
    eapply agrees_rw_cells; [exact AGS| exact SHC|]. intros a Ha. unfold ngc_shadow in Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT. right; right. lia.
  Qed.
  End Sz9.
  Lemma ngc_inv_own : ltac:(let t := eval cbv delta [ngc_inv_own__stmt] in ngc_inv_own__stmt in exact t).
  Proof using GL. intros ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm my W. ltac2:(SecDiet.SzSec.closeP 'ngc_inv_own__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgiDefs.
End CANSEC2.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition ngc_spill (P EB Fb : Z) (j : list byte) : list cell :=
  [ C8 (Z_to_bv 64 (P + 24)); C8 (Z_to_bv 64 (Z.shiftr (P + 656) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 656));
    C8 (Z_to_bv 64 (Z.shiftr (P + 156) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 156)); C8 (Z_to_bv 64 (Z.shiftr (P + 24) 3 + 2147450880));
    C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 (P + 648)); C8 (Z_to_bv 64 P);
    C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb) ].
Remark ngc_spill_size : forall P EB Fb j, cells_size (ngc_spill P EB Fb j) = 128%nat.
Proof. intros. reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT}.
  (* [comment removed for export] *)
  Definition ngcells (P : Z) (np bsz buf sw maj min snap lt ext prec cln : cell) : list cell :=
    [ C8 (Z_to_bv 64 0); np; C4 (Z_to_bv 64 (-1)); bsz; buf; CB 12 (repeat (Z_to_bv 8 0) 12); C4 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (P + 648)); sw; CB 4 (repeat (Z_to_bv 8 0) 4); CB 8 z8; CB 16 (repeat (Z_to_bv 8 0) 16);
      maj; min; snap; lt; ext;
      CB 12 (repeat (Z_to_bv 8 0) 12); C8 (Z_to_bv 64 0); CB 28 (repeat (Z_to_bv 8 0) 28); prec;
      CB 48 fd_pad48; C8 (Z_to_bv 64 0); CB 304 (repeat (Z_to_bv 8 0) 304);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
      CB 72 (repeat (Z_to_bv 8 0) 72); CB 8 z8; C8 (Z_to_bv 64 0); CB 8 z8; cln ].
  #[using="Type"] Remark ngcells_size : forall P np bsz buf sw maj min snap lt ext prec cln,
    csize np = 8%nat -> csize bsz = 4%nat -> csize buf = 8%nat -> csize sw = 4%nat -> csize maj = 4%nat -> csize min = 4%nat ->
    csize snap = 4%nat -> csize lt = 4%nat -> csize ext = 4%nat -> csize prec = 4%nat -> csize cln = 8%nat ->
    cells_size (ngcells P np bsz buf sw maj min snap lt ext prec cln) = 648%nat.
  Proof. intros. cbn. lia. Qed.

  (* [comment removed for export] *)
  Definition ngcells0 (P : Z) : list cell :=
    ngcells P (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0))
              (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)).
  Definition ng0 : pcap_ng_sf := mkNg 0 0 0 0 [].
  Definition pad0 : list byte := repeat (Z_to_bv 8 0) 4.

  (* [comment removed for export] *)
  Definition blank_recell_ng__stmt : Prop := forall m P,
    rw_cells asegs m P ([CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 (-1)); CB 28 (repeat (Z_to_bv 8 0) 28);
                         C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); CB 128 (repeat (Z_to_bv 8 0) 128); C4 (Z_to_bv 64 (-1));
                         CB (Z.to_nat (PCAP_NG_SF_TOTAL - 188)) (repeat (Z_to_bv 8 0) (Z.to_nat (PCAP_NG_SF_TOTAL - 188)))]) ->
    rw_cells asegs m P (ngcells0 P ++ ng_cells ng0 0 pad0).
  Section Sz3.
  Variables m P : ltac2:(SecDiet.SzSec.tyM 'blank_recell_ng__stmt "vv" @m).
  #[using="Type"] Lemma blank_recell_ng__body : ltac2:(SecDiet.SzSec.bodyP 'blank_recell_ng__stmt "vv").
  Proof.
    intros Hc.
    destruct (rw_cells_cut _ _ _ 3 Hc) as [A X]. destruct (rw_cells_cut _ _ _ 1 X) as [B C]. clear Hc X.
    cbn [firstn skipn cells_size csize Nat.add] in A, B, C.
    unfold PCAP_NG_SF_TOTAL in C. change (Z.to_nat (680 - 188)) with 492%nat in C. unfold PCAP_PRIV_OFF in B.
    assert (A' : rw_cells asegs m P (firstn 7 (ngcells0 P))).
    { eapply rw_cells_recell; [exact A | cbn; repeat split; exact Logic.I | vm_compute; reflexivity]. }
    assert (C' : rw_cells asegs m (P + Z.of_nat 48 + Z.of_nat 8) (skipn 8 (ngcells0 P ++ ng_cells ng0 0 pad0))).
    { eapply rw_cells_recell; [exact C | cbn; repeat split; exact Logic.I | unfold fd_pad48, z8, pad0; vm_compute; reflexivity]. }
    pose proof (rw_cells_uncut _ _ _ _ _ A' B ltac:(cbn; lia)) as AB.
    pose proof (rw_cells_uncut _ _ _ _ _ AB C' ltac:(cbn; lia)) as ABC. exact ABC.
  Qed.
  End Sz3.
  #[using="Type"] Lemma blank_recell_ng : ltac:(let t := eval cbv delta [blank_recell_ng__stmt] in blank_recell_ng__stmt in exact t).
  Proof. intros m P. ltac2:(SecDiet.SzSec.closeP 'blank_recell_ng__body "vv"). Qed.

  Section Handle.
    Context {hptr : Type}.
    #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
    (* [comment removed for export] *)
    Definition ngc_p (f qs : hptr) (sw : bool) (BS0 MINOR : Z) (qb : hptr) (bufalloc : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) : pcapT :=
      mkPcap qs f BS0 bufalloc qb bufdata sw 1 MINOR 0 0 0 0 0 [] hdr0 (PrivNg sg i).
  End Handle.
  (* [comment removed for export] *)
  Definition ngc_hcells (P : Z) (sw : bool) (BS0 MINOR : Z) (B : Z) : list cell :=
    ngcells P (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 BS0)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 (Z.b2z sw))) (C4 (Z_to_bv 64 1)) (C4 (Z_to_bv 64 MINOR))
              (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  #[using="Type"] Lemma hcells_cut : forall mX P sw BS0 MINOR B,
    rw_cells asegs mX P (ngc_hcells P sw BS0 MINOR B) ->
    rw_cells asegs mX (P + 24) [C8 (Z_to_bv 64 B)]
    /\ rw_cells asegs mX (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z sw))].
  Proof.
    intros mX P sw BS0 MINOR B HC. unfold ngc_hcells, ngcells in HC.
    destruct (rw_cells_cut _ _ _ 4 HC) as [_ X]. destruct (rw_cells_cut _ _ _ 1 X) as [X1 X2]. destruct (rw_cells_cut _ _ _ 2 X2) as [_ X3]. destruct (rw_cells_cut _ _ _ 2 X3) as [X4 _].
    cbn [firstn skipn cells_size csize Nat.add app] in X1, X4. unfold PCAP_PRIV_OFF.
    split; [replace (P + 24)%Z with (P + Z.of_nat 24)%Z by lia; exact X1|].
    replace (P + 48)%Z with (P + Z.of_nat 24 + Z.of_nat 8 + Z.of_nat 16)%Z by lia. exact X4.
  Qed.
  #[using="Type"] Lemma hcells_cut20 : forall mX P sw BS0 MINOR B,
    rw_cells asegs mX P (ngc_hcells P sw BS0 MINOR B) -> rw_cells asegs mX (P + 20) [C4 (Z_to_bv 64 BS0); C8 (Z_to_bv 64 B)].
  Proof.
    intros mX P sw BS0 MINOR B HC. unfold ngc_hcells, ngcells in HC.
    destruct (rw_cells_cut _ _ _ 3 HC) as [_ X]. destruct (rw_cells_cut _ _ _ 2 X) as [X1 _]. cbn [firstn skipn cells_size csize Nat.add app] in X1.
    replace (P + 20)%Z with (P + Z.of_nat 20)%Z by lia. exact X1.
  Qed.
  #[using="Type"] Lemma ngcells_cut656 : forall mX P sg I pad,
    rw_cells asegs mX (P + 648) (ng_cells sg I pad) -> rw_cells asegs mX (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize sg))].
  Proof.
    intros mX P sg I pad HN. unfold ng_cells in HN. destruct (rw_cells_cut _ _ _ 1 HN) as [_ X]. destruct (rw_cells_cut _ _ _ 1 X) as [X1 _].
    cbn [firstn skipn cells_size csize Nat.add app] in X1. replace (P + 656)%Z with (P + 648 + Z.of_nat 8)%Z by lia. exact X1.
  Qed.
  #[using="Type"] Lemma ngcells_cut672 : forall mX P sg I pad,
    rw_cells asegs mX (P + 648) (ng_cells sg I pad) -> rw_cells asegs mX (P + 672) [C8 (Z_to_bv 64 I)].
  Proof.
    intros mX P sg I pad HN. unfold ng_cells in HN. destruct (rw_cells_cut _ _ _ 5 HN) as [_ X]. cbn [firstn skipn cells_size csize Nat.add app] in X.
    replace (P + 672)%Z with (P + 648 + Z.of_nat 24)%Z by lia. exact X.
  Qed.
  (* [comment removed for export] *)
  Definition hcells_rebuf__stmt : Prop := forall mX mY P sw BS0 MINOR B B',
    rw_cells asegs mX P (ngc_hcells P sw BS0 MINOR B) ->
    agrees_on (fun a => (P <= a < P + 24 \/ P + 32 <= a < P + 648)%Z) mX mY ->
    rw_cells asegs mY (P + 24) [C8 (Z_to_bv 64 B')] -> rw_cells asegs mY P (ngc_hcells P sw BS0 MINOR B').
  Section Sz8.
  Variables mX mY P sw BS0 MINOR B B' : ltac2:(SecDiet.SzSec.tyM 'hcells_rebuf__stmt "vvvvvvvv" @mX).
  #[using="Type"] Lemma hcells_rebuf__body : ltac2:(SecDiet.SzSec.bodyP 'hcells_rebuf__stmt "vvvvvvvv").
  Proof.
    intros HC AG HB.
 unfold ngc_hcells, ngcells in HC |- *.
    destruct (rw_cells_cut _ _ _ 4 HC) as [A X]. destruct (rw_cells_cut _ _ _ 1 X) as [_ C]. clear X. cbn [firstn skipn cells_size csize Nat.add app] in A, C.
    assert (A' : rw_cells asegs mY P [C8 z64; C8 z64; C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 BS0)]).
    { eapply agrees_rw_cells; [exact AG| exact A| intros a Ha; cbn in Ha; cbv beta; lia]. }
    lazymatch type of C with rw_cells _ _ ?AA ?cs => assert (C' : rw_cells asegs mY AA cs)
      by (eapply agrees_rw_cells; [exact AG| exact C| intros a Ha; cbn in Ha; cbv beta; lia]) end.
    replace (P + 24)%Z with (P + Z.of_nat 24)%Z in HB by lia.
    pose proof (rw_cells_uncut _ _ _ _ _ A' HB ltac:(cbn; lia)) as AB.
    exact (rw_cells_uncut _ _ _ _ _ AB C' ltac:(cbn; lia)).
  Qed.
  End Sz8.
  #[using="Type"] Lemma hcells_rebuf : ltac:(let t := eval cbv delta [hcells_rebuf__stmt] in hcells_rebuf__stmt in exact t).
  Proof. intros mX mY P sw BS0 MINOR B B'. ltac2:(SecDiet.SzSec.closeP 'hcells_rebuf__body "vvvvvvvv"). Qed.
End CANSEC1.

Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgiDefs.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).

  (* [comment removed for export] *)
  Definition ngi_inv (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock)
      (lo MG EB ERR SPA Fb : Z) (magic : list Z) (o : option hptr) (m : mem)
      (f qs : hptr) (P : Z) (sw : bool) (BS0 MINOR : Z)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem) (qb : hptr) (B ba : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) (I : Z)
      (pad bs e j : list byte) (ccs fcs : list cell) (k0 k1 k2 : word) : Prop :=
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx ((qs, P, 680) :: (qb, B, ba) :: IBLK i I sg) mm
    /\ rw_cells asegs mm SPA (ngc_spill P EB Fb j) /\ rw_cells asegs mm (SPA + 128) ccs /\ cells_size ccs = 24%nat
    /\ rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) /\ cells_size fcs = 32%nat
    /\ rw_cells asegs mm ERR [C4 z64] /\ rw_cells asegs mm EB [CB 256 e]
    /\ rw_cells asegs mm P (ngc_hcells P sw BS0 MINOR B) /\ rw_cells asegs mm (P + 648) (ng_cells sg I pad)
    /\ ng_user_tsresol sg = 1000000 /\ ng_max_blocksize sg = INITIAL_MAX_BLOCKSIZE /\ 0 <= ng_ifcount sg < 2^32 /\ 0 <= ng_ifaces_size sg < 2^32
    /\ ifaces_ok (ngc_p f qs sw BS0 MINOR qb ba bufdata sg i) I mm
    /\ rw_cells asegs mm B [CB (Z.to_nat ba) bs] /\ firstn (length bufdata) bs = map b8 bufdata
    /\ Z.of_nat (length bufdata) <= ba /\ 1 <= ba < 2^32 /\ BS0 <= ba /\ Forall (fun z => 0 <= z < 256) bufdata.

  (* [comment removed for export] *)
  Definition ngc_inv_own__stmt : Prop := forall ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m
      RNGx sx PB mm my W,
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB mm ->
    Forall (own_ivA [NGFR Fb] PB (bv_unsigned sp)) W -> munch W mm my -> wmono asegs mm my -> mem_inv asegs my -> stk asegs my lo SPA ->
    (forall a, SPA + 152 <= a < bv_unsigned sp \/ MG <= a < MG + 4 \/ Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 8 -> outside W a) ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB my.
  Section Sz9.
  Variables ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm my W : ltac2:(SecDiet.SzSec.tyM 'ngc_inv_own__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_inv_own__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_inv_own__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL.
 intros CTX INV FWs MU WM MIy STy OUT.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (FXs : Forall (cobj_iv FL CL) []) by apply Forall_nil.
    rewrite <- (app_nil_r W) in MU.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ my _ _ _ FWs FXs G MU WM ltac:(lia)) as [Gy AGy].
    rewrite app_nil_r in MU.
    assert (AGS : agrees_on (fun a => outside W a) mm my) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    split; [exact FP|]. split; [exact Gy|]. split; [exact OF|]. split; [exact MIy|]. split; [exact STy|].
    split. { eapply agrees_stk; [exact AGS| exact STG|]. intros a Ha. apply OUT. left. lia. }
    split. { eapply agrees_rw_cells; [exact AGS| exact FR|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT. left. lia. }
    split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AGy|]. intros a (K & _). split; [exact K| exact Logic.I]. }
    split. { destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. cbn [map] in MGc |- *.
             eapply agrees_rw_cells; [exact AGS| exact MGc|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT. right; left. lia. }
    eapply agrees_rw_cells; [exact AGS| exact SHC|]. intros a Ha. unfold ngc_shadow in Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT. right; right. lia.
  Qed.
  End Sz9.
  Lemma ngc_inv_own : ltac:(let t := eval cbv delta [ngc_inv_own__stmt] in ngc_inv_own__stmt in exact t).
  Proof using GL. intros ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic o m RNGx sx PB mm my W. ltac2:(SecDiet.SzSec.closeP 'ngc_inv_own__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgiDefs.
End CANSEC2.
End TwB.
End F_ngchk_ngiA.

(* [comment removed for export] *)
Module F_ngchk_fail3A.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA.
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
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgcFail3.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).

  Definition ngc_fail3__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 : word)
      (j : list byte) (ccs fcs : list cell) (k0 k1 k2 : word) (msg : list Z) (junk3 : list byte)
      (i : option hptr) (sg : pcap_ng_sf) (qs qb : hptr) (P B I nb : Z),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx ((qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) mm ->
    match i with Some _ => True | None => I = 0%Z end ->
    rw_cells asegs mm SPA (ngc_spill P EB Fb j) -> rw_cells asegs mm (SPA + 128) ccs -> cells_size ccs = 24%nat ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 z64] ->
    rw_cells asegs mm EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] ->
    (Z.of_nat (length msg) < 256)%Z -> Forall (fun z => 0 < z < 256)%Z msg ->
    rw_cells asegs mm (P + 24) [C8 (Z_to_bv 64 B)] -> rw_cells asegs mm (P + 672) [C8 (Z_to_bv 64 I)] ->
    implMG RNGx (mbind (match i with Some qi => pfree HO qi | None => mret tt end)
                   (fun _ => mbind (pfree HO qb) (fun _ => mbind (pfree HO qs) (fun _ => fo_ret FO _ FF_NG_CHECK_HEADER (CH_Err msg))))) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b43c) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 j ccs fcs k0 k1 k2 msg junk3 i sg qs qb P B I nb : ltac2:(SecDiet.SzSec.tyM 'ngc_fail3__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_fail3__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_fail3__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET FREE FREENULL.
 intros CTX INV HI FRA0 FCUR Hccs FRC Hfcs HE HEB LEN3 RNG3 HPB HPI.
    destruct (rw_cells_forget _ _ _ _ FCUR) as [jc FCUR']. rewrite Hccs in FCUR'. clear FCUR.
    pose proof (rw_cells_uncut _ _ _ _ _ FRA0 FCUR' ltac:(cbn; lia)) as FRA. unfold ngc_spill in FRA. cbn [app] in FRA. clear FRA0 FCUR'.
    set (scs := [C8 (Z_to_bv 64 (P + 24)); C8 (Z_to_bv 64 (Z.shiftr (P + 656) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 656));
                 C8 (Z_to_bv 64 (Z.shiftr (P + 156) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 156)); C8 (Z_to_bv 64 (Z.shiftr (P + 24) 3 + 2147450880));
                 C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 (P + 648)); C8 (Z_to_bv 64 P);
                 C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb); CB 24 jc]) in *.
    assert (Hscs : cells_size scs = 152%nat) by reflexivity.
    (* [comment removed for export] *)
    assert (REST2 : forall (RNGy : footprint) (sy : PState H hptr) (my : mem) (ray u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word),
      ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGy sy [(qs, P, 680%Z); (qb, B, nb)] my ->
      rw_cells asegs my SPA scs ->
      rw_cells asegs my Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) ->
      rw_cells asegs my ERR [C4 z64] ->
      rw_cells asegs my EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] ->
      rw_cells asegs my (P + 24) [C8 (Z_to_bv 64 B)] ->
      implMG RNGy (mbind (pfree HO qb) (fun _ => mbind (pfree HO qs) (fun _ => fo_ret FO _ FF_NG_CHECK_HEADER (CH_Err msg)))) sy
        (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
        (MS (mkR ray (Z_to_bv 64 SPA) gp tp u0 u1 u2 sp (Z_to_bv 64 SPA) b0 b1 b2 b3 b4 b5 b6 b7
                 (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880))
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) u3 u4 u5 u6)
            F (Z_to_bv 64 0x8b45c) fc None my (seg_rom asegs))).
    { intros RNGy sy my ray u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 INVy FRAy FRCy HEy HEBy HPBy.
      subst scs. clear FRA.
      ngc_setup GL CTX INVy.
      assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
      pose proof TR as (_ & _ & _ & _ & _ & _ & _ & _ & TRF1 & TRF2 & TRF3 & _).
      assert (UCy : ucallerA (depth_check_header true) L my sp s0 ra trC) by (eapply (ngc_uc_now FO GIOA TP fflagA GL); [exact CTX| exact INVy]).
      assert (HinPy : In (qs, P, 680%Z) ((CL ++ [(qs, P, 680%Z); (qb, B, nb)]) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
      assert (HinBy : In (qb, B, nb) ((CL ++ [(qs, P, 680%Z); (qb, B, nb)]) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinPy) as ((PBAND & _ & PTOP & P16) & P0 & PUNPy & PRNGy & PSRNGy & _). cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0, PUNPy, PRNGy, PSRNGy.
      band_ind PBAND bP.
      pose proof (munch_refl ([] : list (Z * Z)) my) as MU. pose proof (wmono_refl asegs my) as WM.
      ienterG.
      ck0_at PUNPy (P + 24)%Z.
      zstep. zstep. zstep. if_false.
      zstep. zstep. zstep.
      apply evtF_done. subst POSTQ. eapply implMG_bind.
      { eapply FREE with (L := L) (s := sy) (C1 := CL ++ [(qs, P, 680%Z)]) (C2 := []) (FB := FB) (FL := NGFR Fb :: FL) (q := qb) (A := B) (n := nb) (lo := lo);
          [ rewrite <- app_assoc; cbn [app]; eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G| exact ST| exact MI| unfold FREE_STACK, PCAP_L2_STACK; lia]
          | reflexivity
          | eapply unw_of_ucaller;
            [ eapply (ngc_ucaller 0%nat) with (X := 0x8b474%Z); [exact UCy| exact SPAB| lia| exact SPT| exact ALN| exact FR| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_ng_check_header; lia]
            | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite ESPA; lia | rewrite unsigned_lit by lia; exact TRF2 | exact RSTK ] ]. }
      intros [] sz RNGz msz PO. cbv beta in PO. destruct PO as (FPz & a0v & mz & E & OFz & MIz & STz & AGz & Gz). rewrite ESPA in *. post_regs E.
      rewrite app_nil_r in Gz, AGz.
      assert (AGzT : agrees_on (fun a => client_keeps (NGFR Fb :: FL) (CL ++ [(qs, P, 680%Z)]) SPA a /\ True) my mz)
        by (eapply agrees_on_weaken; [exact AGz| intros a (K & _); exact K]).
      assert (INVz : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGz sz [(qs, P, 680%Z)] mz).
      { eapply (ngc_inv_keep FO GIOA TP fflagA GL) with (Pn := fun _ : Z => True) (CLk := (CL ++ [(qs, P, 680%Z)])%list);
          [exact CTX| exact INVy| exact FPz| exact Gz| exact OFz| exact MIz| exact STz| exact AGzT| apply incl_appl, incl_refl| exact Gz| intros; exact Logic.I]. }
      (* [comment removed for export] *)
      lazymatch type of FRAy with rw_cells _ _ _ ?cs => assert (FRAz : rw_cells asegs mz SPA cs)
        by (eapply ngc_keep_stack; [exact AGzT| exact FRAy| lia| intros; exact Logic.I]) end.
      assert (FRCz : rw_cells asegs mz Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]))
        by (eapply ngc_keep_frame; [exact AGzT| exact FRCy| lia| rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia| intros; exact Logic.I]).
      assert (HEz : rw_cells asegs mz ERR [C4 z64])
        by (eapply ngc_keep_cobj; [exact AGzT| exact HEy| exact (proj1 OERR)| apply incl_appl, incl_refl| exact IFL| cbn [cells_size csize Nat.add]; lia| intros; exact Logic.I]).
      assert (HEBz : rw_cells asegs mz EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3])
        by (eapply ngc_keep_cobj; [exact AGzT| exact HEBy| exact (proj1 OEB)| apply incl_appl, incl_refl| exact IFL| cbn [cells_size csize]; lia| intros; exact Logic.I]).
      pose proof INVz as (FPzz & _ & _ & _ & _ & _ & FRz & _ & _ & _).
      assert (UCz : ucallerA (depth_check_header true) L mz sp s0 ra trC) by (eapply (ngc_uc_now FO GIOA TP fflagA GL); [exact CTX| exact INVz]).
      clear MU WM RDsh ACCsh. clear FRAy FRCy HEy HEBy HPBy MGc SHC FR STG ST MI.
      pose proof (munch_refl ([] : list (Z * Z)) mz) as MU. pose proof (wmono_refl asegs mz) as WM.
      ienterG.
      zstep. zstep.
      apply evtF_done. subst POSTQ. eapply implMG_bind.
      { eapply FREE with (L := L) (s := sz) (C1 := CL) (C2 := []) (FB := FB) (FL := NGFR Fb :: FL) (q := qs) (A := P) (n := 680%Z) (lo := lo);
          [ eapply (ngc_spo GIOA TP); [exact CTX| exact FPzz| exact Gz| exact STz| exact MIz| unfold FREE_STACK, PCAP_L2_STACK; lia]
          | reflexivity
          | eapply unw_of_ucaller;
            [ eapply (ngc_ucaller 0%nat) with (X := 0x8b47c%Z); [exact UCz| exact SPAB| lia| exact SPT| exact ALN| exact FRz| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_ng_check_header; lia]
            | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite ESPA; lia | rewrite unsigned_lit by lia; exact TRF3 | exact (rng_fp_le _ _ _ _ FPz RSTK) ] ]. }
      intros [] sw RNGw msw PO. cbv beta in PO. destruct PO as (FPw & a0w & mw & E & OFw & MIw & STw & AGw & Gw). rewrite ESPA in *. post_regs E.
      assert (AGwT : agrees_on (fun a => client_keeps (NGFR Fb :: FL) (CL ++ []) SPA a /\ True) mz mw)
        by (eapply agrees_on_weaken; [exact AGw| intros a (K & _); exact K]).
      assert (INVw : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGw sw [] mw).
      { eapply (ngc_inv_keep FO GIOA TP fflagA GL) with (Pn := fun _ : Z => True) (CLk := (CL ++ [])%list);
          [exact CTX| exact INVz| exact FPw| exact Gw| exact OFw| exact MIw| exact STw| exact AGwT| apply incl_appl, incl_refl| exact Gw| intros; exact Logic.I]. }
      eapply (ngc_failx FO GIOA TP fflagA GL FRET) with (pcX := 0x8b47c%Z) (msg := msg) (junk3 := junk3) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2);
        [ exact CTX | exact INVw | do 6 right; left; reflexivity
        | eapply ngc_keep_stack; [exact AGwT| exact FRAz| lia| intros; exact Logic.I]
        | reflexivity
        | eapply ngc_keep_frame; [exact AGwT| exact FRCz| lia| rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia| intros; exact Logic.I]
        | exact Hfcs
        | eapply ngc_keep_cobj; [exact AGwT| exact HEz| exact (proj1 OERR)| apply incl_appl, incl_refl| exact IFL| cbn [cells_size csize Nat.add]; lia| intros; exact Logic.I]
        | eapply ngc_keep_cobj; [exact AGwT| exact HEBz| exact (proj1 OEB)| apply incl_appl, incl_refl| exact IFL| cbn [cells_size csize]; lia| intros; exact Logic.I]
        | exact LEN3 | exact RNG3 ]. }
    subst scs.
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof TR as (_ & _ & _ & _ & _ & _ & _ & _ & TRF1 & TRF2 & TRF3 & _).
    assert (UCm : ucallerA (depth_check_header true) L mm sp s0 ra trC) by (eapply (ngc_uc_now FO GIOA TP fflagA GL); [exact CTX| exact INV]).
    (* [comment removed for export] *)
    assert (HinP : In (qs, P, 680%Z) ((CL ++ (qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) ++ FB))
      by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP) as ((PBAND & _ & PTOP & P16) & P0 & PUNP & PRNG & PSRNG & _).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0, PUNP, PRNG, PSRNG. band_ind PBAND bP.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    do 2 zstep.
    ck0 PUNP; ck_go.
    zstep. zstep.
    destruct i as [qi|]; cbn [IBLK app] in G, INV |- *.
    - (* [comment removed for export] *)
      apply evtF_done. subst POSTQ. eapply implMG_bind.
      { eapply FREE with (L := L) (s := sx) (C1 := (CL ++ [(qs, P, 680%Z); (qb, B, nb)])%list) (C2 := []) (FB := FB) (FL := NGFR Fb :: FL) (q := qi) (A := I) (n := (40 * ng_ifaces_size sg)%Z) (lo := lo);
          [ rewrite <- app_assoc; cbn [app]; eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G| exact ST| exact MI| unfold FREE_STACK, PCAP_L2_STACK; lia]
          | reflexivity
          | eapply unw_of_ucaller;
            [ eapply (ngc_ucaller 0%nat) with (X := 0x8b45c%Z); [exact UCm| exact SPAB| lia| exact SPT| exact ALN| exact FR| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_ng_check_header; lia]
            | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite ESPA; lia | rewrite unsigned_lit by lia; exact TRF1 | exact RSTK ] ]. }
      intros [] sy RNGy msy PO. cbv beta in PO. destruct PO as (FPy & a0y & my & E & OFy & MIy & STy & AGy & Gy). rewrite ESPA in *. post_regs E.
      rewrite app_nil_r in Gy, AGy.
      assert (AGyT : agrees_on (fun a => client_keeps (NGFR Fb :: FL) (CL ++ [(qs, P, 680%Z); (qb, B, nb)]) SPA a /\ True) mm my)
        by (eapply agrees_on_weaken; [exact AGy| intros a (K & _); exact K]).
      eapply REST2.
      + eapply (ngc_inv_keep FO GIOA TP fflagA GL) with (Pn := fun _ : Z => True) (CLk := (CL ++ [(qs, P, 680%Z); (qb, B, nb)])%list);
          [exact CTX| exact INV| exact FPy| exact Gy| exact OFy| exact MIy| exact STy| exact AGyT| apply incl_appl, incl_refl| exact Gy| intros; exact Logic.I].
      + eapply ngc_keep_stack; [exact AGyT| exact FRA| lia| intros; exact Logic.I].
      + eapply ngc_keep_frame; [exact AGyT| exact FRC| lia| rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia| intros; exact Logic.I].
      + eapply ngc_keep_cobj; [exact AGyT| exact HE| exact (proj1 OERR)| apply incl_appl, incl_refl| exact IFL| cbn [cells_size csize Nat.add]; lia| intros; exact Logic.I].
      + eapply ngc_keep_cobj; [exact AGyT| exact HEB| exact (proj1 OEB)| apply incl_appl, incl_refl| exact IFL| cbn [cells_size csize]; lia| intros; exact Logic.I].
      + eapply ngc_keep_block with (b := (qs, P, 680%Z)); [exact AGyT| exact HPB| apply in_or_app; right; left; reflexivity| cbn [cb_addr fst snd]; lia| cbn [cb_addr cb_size fst snd cells_size csize Nat.add]; lia| intros; exact Logic.I].
    - (* [comment removed for export] *)
      subst I.
      eapply evtF_cut.
      { eapply FREENULL with (L := L) (s := sx) (CL := (CL ++ [(qs, P, 680%Z); (qb, B, nb)])%list) (FB := FB) (FL := NGFR Fb :: FL) (lo := lo);
          [ eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G| exact ST| exact MI| unfold FREE_STACK, PCAP_L2_STACK; lia]
          | reflexivity
          | eapply unw_of_ucaller;
            [ eapply (ngc_ucaller 0%nat) with (X := 0x8b45c%Z); [exact UCm| exact SPAB| lia| exact SPT| exact ALN| exact FR| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_ng_check_header; lia]
            | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite ESPA; lia | rewrite unsigned_lit by lia; exact TRF1 | exact RSTK ] ]. }
      intros msy PO. cbv beta in PO. destruct PO as (a0y & my & E & MIy & STy & AGy & Gy). rewrite ESPA in *. post_regs E.
      assert (AGyT : agrees_on (fun a => client_keeps (NGFR Fb :: FL) (CL ++ [(qs, P, 680%Z); (qb, B, nb)]) SPA a /\ True) mm my)
        by (eapply agrees_on_weaken; [exact AGy| intros a (K & _); exact K]).
      apply evtF_done. subst POSTQ. apply implMG_retb.
      eapply REST2.
      + eapply (ngc_inv_keep FO GIOA TP fflagA GL) with (Pn := fun _ : Z => True) (CLk := (CL ++ [(qs, P, 680%Z); (qb, B, nb)])%list);
          [exact CTX| exact INV| intros b jj Hb; exact Hb| exact Gy| reflexivity| exact MIy| exact STy| exact AGyT| apply incl_appl, incl_refl| exact Gy| intros; exact Logic.I].
      + eapply ngc_keep_stack; [exact AGyT| exact FRA| lia| intros; exact Logic.I].
      + eapply ngc_keep_frame; [exact AGyT| exact FRC| lia| rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia| intros; exact Logic.I].
      + eapply ngc_keep_cobj; [exact AGyT| exact HE| exact (proj1 OERR)| apply incl_appl, incl_refl| exact IFL| cbn [cells_size csize Nat.add]; lia| intros; exact Logic.I].
      + eapply ngc_keep_cobj; [exact AGyT| exact HEB| exact (proj1 OEB)| apply incl_appl, incl_refl| exact IFL| cbn [cells_size csize]; lia| intros; exact Logic.I].
      + eapply ngc_keep_block with (b := (qs, P, 680%Z)); [exact AGyT| exact HPB| apply in_or_app; right; left; reflexivity| cbn [cb_addr fst snd]; lia| cbn [cb_addr cb_size fst snd cells_size csize Nat.add]; lia| intros; exact Logic.I].
  Qed.
  End Sz1.
  Lemma ngc_fail3 : ltac:(let t := eval cbv delta [ngc_fail3__stmt] in ngc_fail3__stmt in exact t).
  Proof using GL FRET FREE FREENULL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 j ccs fcs k0 k1 k2 msg junk3 i sg qs qb P B I nb. ltac2:(SecDiet.SzSec.closeP 'ngc_fail3__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcFail3.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngchk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.F_ngchk_ngiA.TwB.
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
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgcFail3.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation NGFR Fb := (FF_NG_CHECK_HEADER, Fb, 64%Z).

  Definition ngc_fail3__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 : word)
      (j : list byte) (ccs fcs : list cell) (k0 k1 k2 : word) (msg : list Z) (junk3 : list byte)
      (i : option hptr) (sg : pcap_ng_sf) (qs qb : hptr) (P B I nb : Z),
    ngc_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx ((qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) mm ->
    match i with Some _ => True | None => I = 0%Z end ->
    rw_cells asegs mm SPA (ngc_spill P EB Fb j) -> rw_cells asegs mm (SPA + 128) ccs -> cells_size ccs = 24%nat ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) -> cells_size fcs = 32%nat ->
    rw_cells asegs mm ERR [C4 z64] ->
    rw_cells asegs mm EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] ->
    (Z.of_nat (length msg) < 256)%Z -> Forall (fun z => 0 < z < 256)%Z msg ->
    rw_cells asegs mm (P + 24) [C8 (Z_to_bv 64 B)] -> rw_cells asegs mm (P + 672) [C8 (Z_to_bv 64 I)] ->
    implMG RNGx (mbind (match i with Some qi => pfree HO qi | None => mret tt end)
                   (fun _ => mbind (pfree HO qb) (fun _ => mbind (pfree HO qs) (fun _ => fo_ret FO _ FF_NG_CHECK_HEADER (CH_Err msg))))) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8b5c0) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 j ccs fcs k0 k1 k2 msg junk3 i sg qs qb P B I nb : ltac2:(SecDiet.SzSec.tyM 'ngc_fail3__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_fail3__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_fail3__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET FREE FREENULL.
 intros CTX INV HI FRA0 FCUR Hccs FRC Hfcs HE HEB LEN3 RNG3 HPB HPI.
    destruct (rw_cells_forget _ _ _ _ FCUR) as [jc FCUR']. rewrite Hccs in FCUR'. clear FCUR.
    pose proof (rw_cells_uncut _ _ _ _ _ FRA0 FCUR' ltac:(cbn; lia)) as FRA. unfold ngc_spill in FRA. cbn [app] in FRA. clear FRA0 FCUR'.
    set (scs := [C8 (Z_to_bv 64 (P + 24)); C8 (Z_to_bv 64 (Z.shiftr (P + 656) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 656));
                 C8 (Z_to_bv 64 (Z.shiftr (P + 156) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 156)); C8 (Z_to_bv 64 (Z.shiftr (P + 24) 3 + 2147450880));
                 C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 (P + 648)); C8 (Z_to_bv 64 P);
                 C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 EB); CB 24 j; C8 (Z_to_bv 64 Fb); CB 24 jc]) in *.
    assert (Hscs : cells_size scs = 152%nat) by reflexivity.
    (* [comment removed for export] *)
    assert (REST2 : forall (RNGy : footprint) (sy : PState H hptr) (my : mem) (ray u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word),
      ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGy sy [(qs, P, 680%Z); (qb, B, nb)] my ->
      rw_cells asegs my SPA scs ->
      rw_cells asegs my Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]) ->
      rw_cells asegs my ERR [C4 z64] ->
      rw_cells asegs my EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] ->
      rw_cells asegs my (P + 24) [C8 (Z_to_bv 64 B)] ->
      implMG RNGy (mbind (pfree HO qb) (fun _ => mbind (pfree HO qs) (fun _ => fo_ret FO _ FF_NG_CHECK_HEADER (CH_Err msg)))) sy
        (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
        (MS (mkR ray (Z_to_bv 64 SPA) gp tp u0 u1 u2 sp (Z_to_bv 64 SPA) b0 b1 b2 b3 b4 b5 b6 b7
                 (Z_to_bv 64 Fb) (Z_to_bv 64 ERR) (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880))
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) u3 u4 u5 u6)
            F (Z_to_bv 64 0x8b5e0) fc None my (seg_rom asegs))).
    { intros RNGy sy my ray u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 INVy FRAy FRCy HEy HEBy HPBy.
      subst scs. clear FRA.
      ngc_setup GL CTX INVy.
      assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
      pose proof (ngc_tr_a3 _ _ _ _ TR) as (_ & _ & _ & _ & _ & _ & _ & _ & TRF1 & TRF2 & TRF3 & _).
      assert (UCy : ucallerA (depth_check_header true) L my sp s0 ra trC) by (eapply (ngc_uc_now FO GIOA TP fflagA GL); [exact CTX| exact INVy]).
      assert (HinPy : In (qs, P, 680%Z) ((CL ++ [(qs, P, 680%Z); (qb, B, nb)]) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
      assert (HinBy : In (qb, B, nb) ((CL ++ [(qs, P, 680%Z); (qb, B, nb)]) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinPy) as ((PBAND & _ & PTOP & P16) & P0 & PUNPy & PRNGy & PSRNGy & _). cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0, PUNPy, PRNGy, PSRNGy.
      band_ind PBAND bP.
      pose proof (munch_refl ([] : list (Z * Z)) my) as MU. pose proof (wmono_refl asegs my) as WM.
      ienterG.
      ck0_at PUNPy (P + 24)%Z.
      zstep. zstep. zstep. if_false.
      zstep. zstep. zstep.
      apply evtF_done. subst POSTQ. eapply implMG_bind.
      { eapply FREE with (L := L) (s := sy) (C1 := CL ++ [(qs, P, 680%Z)]) (C2 := []) (FB := FB) (FL := NGFR Fb :: FL) (q := qb) (A := B) (n := nb) (lo := lo);
          [ rewrite <- app_assoc; cbn [app]; eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G| exact ST| exact MI| unfold FREE_STACK, PCAP_L2_STACK; lia]
          | reflexivity
          | eapply unw_of_ucaller;
            [ eapply (ngc_ucaller 0%nat) with (X := 0x8b5f8%Z); [exact UCy| exact SPAB| lia| exact SPT| exact ALN| exact FR| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_ng_check_header; lia]
            | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite ESPA; lia | rewrite unsigned_lit by lia; exact TRF2 | exact RSTK ] ]. }
      intros [] sz RNGz msz PO. cbv beta in PO. destruct PO as (FPz & a0v & mz & E & OFz & MIz & STz & AGz & Gz). rewrite ESPA in *. post_regs E.
      rewrite app_nil_r in Gz, AGz.
      assert (AGzT : agrees_on (fun a => client_keeps (NGFR Fb :: FL) (CL ++ [(qs, P, 680%Z)]) SPA a /\ True) my mz)
        by (eapply agrees_on_weaken; [exact AGz| intros a (K & _); exact K]).
      assert (INVz : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGz sz [(qs, P, 680%Z)] mz).
      { eapply (ngc_inv_keep FO GIOA TP fflagA GL) with (Pn := fun _ : Z => True) (CLk := (CL ++ [(qs, P, 680%Z)])%list);
          [exact CTX| exact INVy| exact FPz| exact Gz| exact OFz| exact MIz| exact STz| exact AGzT| apply incl_appl, incl_refl| exact Gz| intros; exact Logic.I]. }
      (* [comment removed for export] *)
      lazymatch type of FRAy with rw_cells _ _ _ ?cs => assert (FRAz : rw_cells asegs mz SPA cs)
        by (eapply ngc_keep_stack; [exact AGzT| exact FRAy| lia| intros; exact Logic.I]) end.
      assert (FRCz : rw_cells asegs mz Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_NG_CHECK_HEADER Fb))]))
        by (eapply ngc_keep_frame; [exact AGzT| exact FRCy| lia| rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia| intros; exact Logic.I]).
      assert (HEz : rw_cells asegs mz ERR [C4 z64])
        by (eapply ngc_keep_cobj; [exact AGzT| exact HEy| exact (proj1 OERR)| apply incl_appl, incl_refl| exact IFL| cbn [cells_size csize Nat.add]; lia| intros; exact Logic.I]).
      assert (HEBz : rw_cells asegs mz EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3])
        by (eapply ngc_keep_cobj; [exact AGzT| exact HEBy| exact (proj1 OEB)| apply incl_appl, incl_refl| exact IFL| cbn [cells_size csize]; lia| intros; exact Logic.I]).
      pose proof INVz as (FPzz & _ & _ & _ & _ & _ & FRz & _ & _ & _).
      assert (UCz : ucallerA (depth_check_header true) L mz sp s0 ra trC) by (eapply (ngc_uc_now FO GIOA TP fflagA GL); [exact CTX| exact INVz]).
      clear MU WM RDsh ACCsh. clear FRAy FRCy HEy HEBy HPBy MGc SHC FR STG ST MI.
      pose proof (munch_refl ([] : list (Z * Z)) mz) as MU. pose proof (wmono_refl asegs mz) as WM.
      ienterG.
      zstep. zstep.
      apply evtF_done. subst POSTQ. eapply implMG_bind.
      { eapply FREE with (L := L) (s := sz) (C1 := CL) (C2 := []) (FB := FB) (FL := NGFR Fb :: FL) (q := qs) (A := P) (n := 680%Z) (lo := lo);
          [ eapply (ngc_spo GIOA TP); [exact CTX| exact FPzz| exact Gz| exact STz| exact MIz| unfold FREE_STACK, PCAP_L2_STACK; lia]
          | reflexivity
          | eapply unw_of_ucaller;
            [ eapply (ngc_ucaller 0%nat) with (X := 0x8b600%Z); [exact UCz| exact SPAB| lia| exact SPT| exact ALN| exact FRz| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_ng_check_header; lia]
            | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite ESPA; lia | rewrite unsigned_lit by lia; exact TRF3 | exact (rng_fp_le _ _ _ _ FPz RSTK) ] ]. }
      intros [] sw RNGw msw PO. cbv beta in PO. destruct PO as (FPw & a0w & mw & E & OFw & MIw & STw & AGw & Gw). rewrite ESPA in *. post_regs E.
      assert (AGwT : agrees_on (fun a => client_keeps (NGFR Fb :: FL) (CL ++ []) SPA a /\ True) mz mw)
        by (eapply agrees_on_weaken; [exact AGw| intros a (K & _); exact K]).
      assert (INVw : ngc_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] o m RNGw sw [] mw).
      { eapply (ngc_inv_keep FO GIOA TP fflagA GL) with (Pn := fun _ : Z => True) (CLk := (CL ++ [])%list);
          [exact CTX| exact INVz| exact FPw| exact Gw| exact OFw| exact MIw| exact STw| exact AGwT| apply incl_appl, incl_refl| exact Gw| intros; exact Logic.I]. }
      eapply (ngc_failx FO GIOA TP fflagA GL FRET) with (pcX := 0x8b600%Z) (msg := msg) (junk3 := junk3) (fcs := fcs) (k0 := k0) (k1 := k1) (k2 := k2);
        [ exact CTX | exact INVw | do 6 right; left; reflexivity
        | eapply ngc_keep_stack; [exact AGwT| exact FRAz| lia| intros; exact Logic.I]
        | reflexivity
        | eapply ngc_keep_frame; [exact AGwT| exact FRCz| lia| rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia| intros; exact Logic.I]
        | exact Hfcs
        | eapply ngc_keep_cobj; [exact AGwT| exact HEz| exact (proj1 OERR)| apply incl_appl, incl_refl| exact IFL| cbn [cells_size csize Nat.add]; lia| intros; exact Logic.I]
        | eapply ngc_keep_cobj; [exact AGwT| exact HEBz| exact (proj1 OEB)| apply incl_appl, incl_refl| exact IFL| cbn [cells_size csize]; lia| intros; exact Logic.I]
        | exact LEN3 | exact RNG3 ]. }
    subst scs.
    ngc_setup GL CTX INV.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (ngc_tr_a3 _ _ _ _ TR) as (_ & _ & _ & _ & _ & _ & _ & _ & TRF1 & TRF2 & TRF3 & _).
    assert (UCm : ucallerA (depth_check_header true) L mm sp s0 ra trC) by (eapply (ngc_uc_now FO GIOA TP fflagA GL); [exact CTX| exact INV]).
    (* [comment removed for export] *)
    assert (HinP : In (qs, P, 680%Z) ((CL ++ (qs, P, 680%Z) :: (qb, B, nb) :: IBLK i I sg) ++ FB))
      by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP) as ((PBAND & _ & PTOP & P16) & P0 & PUNP & PRNG & PSRNG & _).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0, PUNP, PRNG, PSRNG. band_ind PBAND bP.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    do 2 zstep.
    ck0 PUNP; ck_go.
    zstep. zstep.
    destruct i as [qi|]; cbn [IBLK app] in G, INV |- *.
    - (* [comment removed for export] *)
      apply evtF_done. subst POSTQ. eapply implMG_bind.
      { eapply FREE with (L := L) (s := sx) (C1 := (CL ++ [(qs, P, 680%Z); (qb, B, nb)])%list) (C2 := []) (FB := FB) (FL := NGFR Fb :: FL) (q := qi) (A := I) (n := (40 * ng_ifaces_size sg)%Z) (lo := lo);
          [ rewrite <- app_assoc; cbn [app]; eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G| exact ST| exact MI| unfold FREE_STACK, PCAP_L2_STACK; lia]
          | reflexivity
          | eapply unw_of_ucaller;
            [ eapply (ngc_ucaller 0%nat) with (X := 0x8b5e0%Z); [exact UCm| exact SPAB| lia| exact SPT| exact ALN| exact FR| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_ng_check_header; lia]
            | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite ESPA; lia | rewrite unsigned_lit by lia; exact TRF1 | exact RSTK ] ]. }
      intros [] sy RNGy msy PO. cbv beta in PO. destruct PO as (FPy & a0y & my & E & OFy & MIy & STy & AGy & Gy). rewrite ESPA in *. post_regs E.
      rewrite app_nil_r in Gy, AGy.
      assert (AGyT : agrees_on (fun a => client_keeps (NGFR Fb :: FL) (CL ++ [(qs, P, 680%Z); (qb, B, nb)]) SPA a /\ True) mm my)
        by (eapply agrees_on_weaken; [exact AGy| intros a (K & _); exact K]).
      eapply REST2.
      + eapply (ngc_inv_keep FO GIOA TP fflagA GL) with (Pn := fun _ : Z => True) (CLk := (CL ++ [(qs, P, 680%Z); (qb, B, nb)])%list);
          [exact CTX| exact INV| exact FPy| exact Gy| exact OFy| exact MIy| exact STy| exact AGyT| apply incl_appl, incl_refl| exact Gy| intros; exact Logic.I].
      + eapply ngc_keep_stack; [exact AGyT| exact FRA| lia| intros; exact Logic.I].
      + eapply ngc_keep_frame; [exact AGyT| exact FRC| lia| rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia| intros; exact Logic.I].
      + eapply ngc_keep_cobj; [exact AGyT| exact HE| exact (proj1 OERR)| apply incl_appl, incl_refl| exact IFL| cbn [cells_size csize Nat.add]; lia| intros; exact Logic.I].
      + eapply ngc_keep_cobj; [exact AGyT| exact HEB| exact (proj1 OEB)| apply incl_appl, incl_refl| exact IFL| cbn [cells_size csize]; lia| intros; exact Logic.I].
      + eapply ngc_keep_block with (b := (qs, P, 680%Z)); [exact AGyT| exact HPB| apply in_or_app; right; left; reflexivity| cbn [cb_addr fst snd]; lia| cbn [cb_addr cb_size fst snd cells_size csize Nat.add]; lia| intros; exact Logic.I].
    - (* [comment removed for export] *)
      subst I.
      eapply evtF_cut.
      { eapply FREENULL with (L := L) (s := sx) (CL := (CL ++ [(qs, P, 680%Z); (qb, B, nb)])%list) (FB := FB) (FL := NGFR Fb :: FL) (lo := lo);
          [ eapply (ngc_spo GIOA TP); [exact CTX| exact FP| exact G| exact ST| exact MI| unfold FREE_STACK, PCAP_L2_STACK; lia]
          | reflexivity
          | eapply unw_of_ucaller;
            [ eapply (ngc_ucaller 0%nat) with (X := 0x8b5e0%Z); [exact UCm| exact SPAB| lia| exact SPT| exact ALN| exact FR| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_ng_check_header; lia]
            | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite ESPA; lia | rewrite unsigned_lit by lia; exact TRF1 | exact RSTK ] ]. }
      intros msy PO. cbv beta in PO. destruct PO as (a0y & my & E & MIy & STy & AGy & Gy). rewrite ESPA in *. post_regs E.
      assert (AGyT : agrees_on (fun a => client_keeps (NGFR Fb :: FL) (CL ++ [(qs, P, 680%Z); (qb, B, nb)]) SPA a /\ True) mm my)
        by (eapply agrees_on_weaken; [exact AGy| intros a (K & _); exact K]).
      apply evtF_done. subst POSTQ. apply implMG_retb.
      eapply REST2.
      + eapply (ngc_inv_keep FO GIOA TP fflagA GL) with (Pn := fun _ : Z => True) (CLk := (CL ++ [(qs, P, 680%Z); (qb, B, nb)])%list);
          [exact CTX| exact INV| intros b jj Hb; exact Hb| exact Gy| reflexivity| exact MIy| exact STy| exact AGyT| apply incl_appl, incl_refl| exact Gy| intros; exact Logic.I].
      + eapply ngc_keep_stack; [exact AGyT| exact FRA| lia| intros; exact Logic.I].
      + eapply ngc_keep_frame; [exact AGyT| exact FRC| lia| rewrite !cells_size_app, Hfcs; cbn [cells_size csize Nat.add]; lia| intros; exact Logic.I].
      + eapply ngc_keep_cobj; [exact AGyT| exact HE| exact (proj1 OERR)| apply incl_appl, incl_refl| exact IFL| cbn [cells_size csize Nat.add]; lia| intros; exact Logic.I].
      + eapply ngc_keep_cobj; [exact AGyT| exact HEB| exact (proj1 OEB)| apply incl_appl, incl_refl| exact IFL| cbn [cells_size csize]; lia| intros; exact Logic.I].
      + eapply ngc_keep_block with (b := (qs, P, 680%Z)); [exact AGyT| exact HPB| apply in_or_app; right; left; reflexivity| cbn [cb_addr fst snd]; lia| cbn [cb_addr cb_size fst snd cells_size csize Nat.add]; lia| intros; exact Logic.I].
  Qed.
  End Sz1.
  Lemma ngc_fail3 : ltac:(let t := eval cbv delta [ngc_fail3__stmt] in ngc_fail3__stmt in exact t).
  Proof using GL FRET FREE FREENULL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 r23 r24 t3 t4 t5 t6 j ccs fcs k0 k1 k2 msg junk3 i sg qs qb P B I nb. ltac2:(SecDiet.SzSec.closeP 'ngc_fail3__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgcFail3.
End CANSEC1.
End TwB.
End F_ngchk_fail3A.
