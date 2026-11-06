(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame Tac SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MM_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_afree_s.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto ABase AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma run_free_hooks_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 32 ->
  mem_inv asegs m ->
  rw_cells asegs m AFHOOK [C8 (Z_to_bv 64 0)] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x647ac) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI HK RIMG RTLS RSTK. unfold AFHOOK in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 32%nat ST.
  do 4 step.                                   (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  step. step. step.                            (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  step. step. step.                            (* [comment removed for export] *)
  step. zstep. step. step. if_lit.            (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  do 5 step.                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma run_free_hooks_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 32 ->
  mem_inv asegs m ->
  rw_cells asegs m AFHOOK [C8 (Z_to_bv 64 0)] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x64814) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI HK RIMG RTLS RSTK. unfold AFHOOK in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 32%nat ST.
  do 4 step.                                   (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  step. step. step.                            (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  step. step. step.                            (* [comment removed for export] *)
  step. zstep. step. step. if_lit.            (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  do 5 step.                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed.
End CANSEC1.
End TwB.
End F_afree_s.

(* [comment removed for export] *)
Module F_amalloc_iseg.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition icptA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk1 junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x56430) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 n)
                  (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x5641c) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
                  (Z_to_bv 64 0x5641c) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
                  s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x56474) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2128)
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2112) [CB 2040 junk1]
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition icptA_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2128 - 16 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
  rw_cells asegs m 0xaf2d8 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xaf2fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0xa54a0 [C8 (Z_to_bv 64 0x140128); C8 (Z_to_bv 64 0xabdf8); C8 (Z_to_bv 64 0xae5f8);
                             C8 (Z_to_bv 64 0xaf2e8); C8 (Z_to_bv 64 0xaf2f0); C8 (Z_to_bv 64 0xaf2e0)] ->
  rw_cells asegs m 0x14014a [C1 (Z_to_bv 8 1)] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (icptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x56178) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 34).
Variable n : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 35).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 36).
#[using="Type"] Lemma icptA_spec__body : ltac:(let T := type of (fun (h : icptA_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, lo))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> NR INI MCS GOT CF34 RIMG RTLS RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2128 - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  step.                                                          (* [comment removed for export] *)
  carve_frame 2128%nat ST.
  (* [comment removed for export] *)
  cb_split3 FR 16%nat 2040%nat 72%nat.
  (* [comment removed for export] *)
  repeat match type of FR with context [CB _ ?j] => lazymatch j with firstn _ _ => idtac | skipn _ _ => idtac end;
           let x := fresh "jkf" in set (x := j) in FR; clearbody x end. rw_split FR 1%nat FRa FR'. rw_split FR' 1%nat FRt FRs.
  do 8 step.                                                     (* [comment removed for export] *)
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. carve_frame 16%nat ST.
  do 5 step. lstep. step. step. step. if_lit.                    (* [comment removed for export] *)
  do 4 step. release_frame FR ST (bv_unsigned sp + -2128).
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                             (* [comment removed for export] *)
  step. sstep. step.                                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. lstep. step. step.                                 (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. step.                                              (* [comment removed for export] *)
  step. step. lstep. step.                                       (* [comment removed for export] *)
  step. step. lstep. step. step.                                 (* [comment removed for export] *)
  step. zstep. zstep. zstep. step.                               (* [comment removed for export] *)
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615. rewrite land_ones_l by lia.
  sstep.                                                         (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. zstep. step. step. step. step.                          (* [comment removed for export] *)
  rw_split FRa 1%nat FRa1 FRa2. apply rw_cells_C8_to_C4C4_zero in FRa2. rw_join FRa1 FRa2 FRA.
  apply evtF_done. unfold icptA_post. do 10 eexists. eexists. eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FRA|]. split; [exact FRt|]. exact FRs.
Qed.
End Zd1.
#[using="Type"] Lemma icptA_spec : ltac:(let t := eval cbv delta [icptA_spec__stmt] in icptA_spec__stmt in exact t).
Proof. exact icptA_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition icptB_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (s0v : word) (F : bvmap 5 word) (fc : bv 32)
    (n lo : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR (Z_to_bv 64 0x56488) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2
                  s0v s1
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 1) (Z_to_bv 64 1) a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x33bd4) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2144, bv_unsigned sp - 2128)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2144)
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [C8 s0v; C8 (Z_to_bv 64 0x56488)].

#[using="Type"] Lemma icptB_spec : forall RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n lo : Z),
  stk asegs m lo (bv_unsigned sp + -2128) -> ATOP <= lo -> lo <= bv_unsigned sp - 2144 ->
  mem_inv asegs m ->
  s1 = Z_to_bv 64 n ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (icptB_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sp F fc n lo t0 t1 t2 a6 a7 t3 t4 t5 t6 m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x56478) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> RIMG RTLS RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp - 2128)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 3 step.                                                     (* [comment removed for export] *)
  do 7 step.                                                     (* [comment removed for export] *)
  apply evtF_done. unfold icptB_post, AINSTANCE. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact FR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma icptC_spec : forall RNG sp gp tp t0 t1 t2 s0x s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s0i : word) (F : bvmap 5 word) fc (m : amem) (UB lo : Z) (junk2 : list byte),
  stk asegs m lo (bv_unsigned sp + -2144) -> ATOP <= lo -> lo <= bv_unsigned sp - 2144 ->
  mem_inv asegs m ->
  0 < UB < 2^64 ->
  rw_cells asegs m (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x56488)] ->
  (exists csA, rw_cells asegs m (bv_unsigned sp + -2128) csA /\ cells_size csA = 16%nat) ->
  (exists csT, rw_cells asegs m (bv_unsigned sp + -2112) csT /\ cells_size csT = 2040%nat) ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists m',
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom asegs)
      /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 0x33bd8) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 s0x s1 (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x33bd8) fc None m (seg_rom asegs)).
Proof.
  intros until junk2. intros ST CEIL LO MI UBR FR16 [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RTLS RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  step. if_cases K0; zify_cond K0. { exfalso. lia. }             (* [comment removed for export] *)
  do 4 step.                                                     (* [comment removed for export] *)
  zstep. do 7 step. zstep. step.                                 (* [comment removed for export] *)
  release_frame FR16 ST (bv_unsigned sp + -2128).
  pose proof (rw_cells_forget asegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  release_frame FRA' ST (bv_unsigned sp + -2112).
  pose proof (rw_cells_forget asegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  release_frame FRT' ST (bv_unsigned sp + -72).
  release_frame FRS ST (bv_unsigned sp).
  apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact ST.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition icptA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk1 junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x56498) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 n)
                  (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x56484) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
                  (Z_to_bv 64 0x56484) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
                  s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x564dc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2128)
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2112) [CB 2040 junk1]
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition icptA_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2128 - 16 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
  rw_cells asegs m 0xaf6d8 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xaf6fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0xa5880 [C8 (Z_to_bv 64 0x140528); C8 (Z_to_bv 64 0xac1f8); C8 (Z_to_bv 64 0xae9f8);
                             C8 (Z_to_bv 64 0xaf6e8); C8 (Z_to_bv 64 0xaf6f0); C8 (Z_to_bv 64 0xaf6e0)] ->
  rw_cells asegs m 0x14054a [C1 (Z_to_bv 8 1)] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (icptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x561e0) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 34).
Variable n : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 35).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'icptA_spec__stmt 36).
#[using="Type"] Lemma icptA_spec__body : ltac:(let T := type of (fun (h : icptA_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, lo))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> NR INI MCS GOT CF34 RIMG RTLS RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2128 - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  step.                                                          (* [comment removed for export] *)
  carve_frame 2128%nat ST.
  (* [comment removed for export] *)
  cb_split3 FR 16%nat 2040%nat 72%nat.
  (* [comment removed for export] *)
  repeat match type of FR with context [CB _ ?j] => lazymatch j with firstn _ _ => idtac | skipn _ _ => idtac end;
           let x := fresh "jkf" in set (x := j) in FR; clearbody x end. rw_split FR 1%nat FRa FR'. rw_split FR' 1%nat FRt FRs.
  do 8 step.                                                     (* [comment removed for export] *)
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. carve_frame 16%nat ST.
  do 5 step. lstep. step. step. step. if_lit.                    (* [comment removed for export] *)
  do 4 step. release_frame FR ST (bv_unsigned sp + -2128).
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                             (* [comment removed for export] *)
  step. sstep. step.                                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. lstep. step. step.                                 (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. step.                                              (* [comment removed for export] *)
  step. step. lstep. step.                                       (* [comment removed for export] *)
  step. step. lstep. step. step.                                 (* [comment removed for export] *)
  step. zstep. zstep. zstep. step.                               (* [comment removed for export] *)
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615. rewrite land_ones_l by lia.
  sstep.                                                         (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. zstep. step. step. step. step.                          (* [comment removed for export] *)
  rw_split FRa 1%nat FRa1 FRa2. apply rw_cells_C8_to_C4C4_zero in FRa2. rw_join FRa1 FRa2 FRA.
  apply evtF_done. unfold icptA_post. do 10 eexists. eexists. eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FRA|]. split; [exact FRt|]. exact FRs.
Qed.
End Zd1.
#[using="Type"] Lemma icptA_spec : ltac:(let t := eval cbv delta [icptA_spec__stmt] in icptA_spec__stmt in exact t).
Proof. exact icptA_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition icptB_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (s0v : word) (F : bvmap 5 word) (fc : bv 32)
    (n lo : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR (Z_to_bv 64 0x564f0) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2
                  s0v s1
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 1) (Z_to_bv 64 1) a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x33c3c) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2144, bv_unsigned sp - 2128)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2144)
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [C8 s0v; C8 (Z_to_bv 64 0x564f0)].

#[using="Type"] Lemma icptB_spec : forall RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n lo : Z),
  stk asegs m lo (bv_unsigned sp + -2128) -> ATOP <= lo -> lo <= bv_unsigned sp - 2144 ->
  mem_inv asegs m ->
  s1 = Z_to_bv 64 n ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (icptB_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sp F fc n lo t0 t1 t2 a6 a7 t3 t4 t5 t6 m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x564e0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> RIMG RTLS RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp - 2128)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 3 step.                                                     (* [comment removed for export] *)
  do 7 step.                                                     (* [comment removed for export] *)
  apply evtF_done. unfold icptB_post, AINSTANCE. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact FR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma icptC_spec : forall RNG sp gp tp t0 t1 t2 s0x s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s0i : word) (F : bvmap 5 word) fc (m : amem) (UB lo : Z) (junk2 : list byte),
  stk asegs m lo (bv_unsigned sp + -2144) -> ATOP <= lo -> lo <= bv_unsigned sp - 2144 ->
  mem_inv asegs m ->
  0 < UB < 2^64 ->
  rw_cells asegs m (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x564f0)] ->
  (exists csA, rw_cells asegs m (bv_unsigned sp + -2128) csA /\ cells_size csA = 16%nat) ->
  (exists csT, rw_cells asegs m (bv_unsigned sp + -2112) csT /\ cells_size csT = 2040%nat) ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists m',
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom asegs)
      /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 0x33c40) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 s0x s1 (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x33c40) fc None m (seg_rom asegs)).
Proof.
  intros until junk2. intros ST CEIL LO MI UBR FR16 [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RTLS RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  step. if_cases K0; zify_cond K0. { exfalso. lia. }             (* [comment removed for export] *)
  do 4 step.                                                     (* [comment removed for export] *)
  zstep. do 7 step. zstep. step.                                 (* [comment removed for export] *)
  release_frame FR16 ST (bv_unsigned sp + -2128).
  pose proof (rw_cells_forget asegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  release_frame FRA' ST (bv_unsigned sp + -2112).
  pose proof (rw_cells_forget asegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  release_frame FRT' ST (bv_unsigned sp + -72).
  release_frame FRS ST (bv_unsigned sp).
  apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact ST.
Qed.
End CANSEC1.
End TwB.
End F_amalloc_iseg.

(* [comment removed for export] *)
Module F_ammap.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition rmap_entry := 0x721e8.
End CANSEC1.
Notation RMAP_STACK := 400 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition rmap_cells (m : amem) : Prop :=
     rw_cells asegs m 0xa5490 [C8 (Z_to_bv 64 0x13e0a0)]
  /\ rw_cells asegs m 0x13e0a0 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m 0xa54a0 [C8 (Z_to_bv 64 0x140128); C8 (Z_to_bv 64 0xabdf8); C8 (Z_to_bv 64 0xae5f8);
                               C8 (Z_to_bv 64 0xaf2e8); C8 (Z_to_bv 64 0xaf2f0); C8 (Z_to_bv 64 0xaf2e0)]
  /\ rw_cells asegs m 0x14022c [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0x1401b8 [C8 (Z_to_bv 64 0)].

#[using="Type"] Lemma rmap_cells_frame : forall m m' W, rmap_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> rmap_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4 & R5) MU WM HW. unfold AIMG_HI in HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x603000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold rmap_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]).
Qed.

Definition rmap_post (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ addr + size <= ATOP
  /\ munch [(bv_unsigned sp - RMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z m m' /\ wmono asegs m m'
  /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' addr [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
  /\ rng RNG' addr size /\ rng RNG' (shad addr) (shlen size)
  /\ fp_bw RNG'                                   (* [comment removed for export] *)
  /\ rmap_cells m'.

#[using="Type"] Lemma page_round_up_mult : forall s, s mod 4096 = 0 -> 0 <= s -> page_round_up_Z s = s.
Proof. intros s Hs H0. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma land_align4096 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
  intros x Hx.
  replace 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity.
  replace (x - x mod 4096) with (Z.shiftl (Z.shiftr x 12) 12).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 64) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma land_align2p18 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709289472 = x - x mod 262144.
Proof.
  intros x Hx.
  replace 18446744073709289472 with (Z.ldiff (Z.ones 64) (Z.ones 18)) by reflexivity.
  replace (x - x mod 262144) with (Z.shiftl (Z.shiftr x 18) 18).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^18) with 262144. Z.div_mod_to_equations. lia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 64) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma adec_mmap_rw_Some : forall len rsp a, adec_mmap ATOP len 3 rsp = Some a ->
  exists ci, rsp = mkEffectU (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))] [] [] ci
          /\ a mod 4096 = 0 /\ 0 < a /\ a + mmap_len len <= ATOP.
Proof.
  intros len rsp a H. unfold adec_mmap in H. cbn [Z.eqb] in H.
  destruct (dec_mmap len [] rsp) as [[e|a']|] eqn:D; try discriminate. injection H as <-.      (* [comment removed for export] *)
  destruct (dec_mmap_Some _ _ _ _ D) as [E OK]. exists []. split; [exact E|].
  pose proof (mmap_addr_ok_true _ _ _ OK) as [(M1 & M2 & M3) _]. unfold page_size in M1. change (@alloc_ceiling _) with ATOP in M3. auto.
Qed.

Definition rmap_spec__stmt : Prop := forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAP_STACK ->
  mem_inv asegs m ->
  a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> 0x10000 <= bv_unsigned a3 < 2^47 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
  rmap_cells m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rmap_post RNG sp addr size lo m RNG' m' ->
      implS asegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmap_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 1).
Variable K : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 37).
Variable addr : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 38).
Variable size : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 39).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 40).
#[using="Type"] Lemma rmap_spec__body : ltac:(let T := type of (fun (h : rmap_spec__stmt) => h RNG R K Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m addr size lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (K, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (addr, (size, lo))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> NAME AAL SAL SPOS A0 ASZ RC RIMG RTLS RSTK UNR KONT. unfold AIMG_HI in A0.
  pose proof RC as RC0. (nd_pre RC0 5%nat; intros GPG PGSZ GOT DPM MLIM; nd_post).
  unfold rmap_entry in *. word_range sp SPR. word_range a3 A3R.
  pose proof (munch_refl [(bv_unsigned sp - RMAP_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _ _ _
            (fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               rmap_post RNG sp addr size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs))).
  2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
       (nd_pre PO 17%nat; intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PO ndR1__; nd_post; revert ndR1__; intros ->).
       eapply KONT. exact PO. }
  (* [comment removed for export] *)
  iprefix.
  carve_frame 32%nat ST.                                       (* [comment removed for export] *)
  step. step. step. step. step.                                (* [comment removed for export] *)
  step. step. step. step. step.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  carve_frame 96%nat ST.
  step. step. step. step. step. step. step.                    (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. if_lit.                                          (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS ASZ A0; Z.div_mod_to_equations; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  setreg 18 (Z_to_bv 64 addr) ltac:(rewrite land_align4096 by lia; f_equal; clear -AAL A0 ASZ SPOS; Z.div_mod_to_equations; lia).
  step. step. step. step. step.                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carve_frame 272%nat ST.
  step. step. step. step. step. step. step. step.              (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 NAME. lia. }   (* [comment removed for export] *)
  step. step. step. lstep.                                     (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step.        (* [comment removed for export] *)
  release_frame FR1 ST (bv_unsigned sp + -128).
  step. setreg 13 (Z_to_bv 64 50) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)
  step. step. step. step. step.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  icallk rt_mmap_stubP; [reflexivity|].
  intros a RNG' ms' (rsp & HF & Hdec & ->).
  (nd_pre (adec_mmap_rw_Some _ _ _ Hdec) 2%nat; intros ci ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 3%nat; intros AM1 AM2 AM3; nd_post).
  pose proof (page_round_up_mult size SAL ltac:(clear -SPOS; lia)) as PRU. unfold mmap_len in *. rewrite PRU in AM3. rewrite PRU.
  pose proof (fstepS_mmap_grant addr size 50 _ RNG RNG' HF (eq_refl : Z.land 50 MAP_NORESERVE = 0)) as GR. cbn [eff_ret] in GR.
  rewrite (unsigned_lit a) in GR by (clear -AM2 AM3 SPOS; lia). rewrite (unsigned_lit size) in GR by (clear -SPOS ASZ A0; lia).
  rewrite PRU in GR. specialize (GR ltac:(unfold page_size; exact AM1)). destruct GR as [GR1 GR2].
  pose proof HF as HF0. fstepS_transport HF.
  destruct (Z.eq_dec a addr) as [->|NE]. 2: { apply evtF_done. left. split; [exact NE|]. split; [exact AM2| atop_facts; exact AM3]. }
  unfold rt_regs. cbn [eff_ret]. rewrite eff_mem_zeros.
  replace (ret_pc (Z_to_bv 64 434268)) with (Z_to_bv 64 434268 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  apply (munch_weaken _ [(bv_unsigned sp - RMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z) in MU.
  2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
  sys_mem_zeros.
  (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS A0. lia. }   (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS A0. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. if_lit.                                                (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. step. step. step. if_lit. step.                        (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step.        (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -128) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp + -32) end.
  (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. clear -K3 A0 ASZ SPOS. lia. }   (* [comment removed for export] *)
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -32) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold rmap_post. destruct HF0 as [[FPLE _] [_ BW]].
  split; [exact FPLE|]. split; [exact AM3|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|]. split; [exact BW|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed.
End Zd1.
#[using="Type"] Lemma rmap_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAP_STACK ->
  mem_inv asegs m ->
  a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> 0x10000 <= bv_unsigned a3 < 2^47 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
  rmap_cells m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rmap_post RNG sp addr size lo m RNG' m' ->
      implS asegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmap_entry) fc None m (seg_rom asegs)).
Proof. exact rmap_spec__body. Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition rmap_entry := 0x72250.
End CANSEC1.
Notation RMAP_STACK := 400 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition rmap_cells (m : amem) : Prop :=
     rw_cells asegs m 0xa5870 [C8 (Z_to_bv 64 0x13e4a0)]
  /\ rw_cells asegs m 0x13e4a0 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m 0xa5880 [C8 (Z_to_bv 64 0x140528); C8 (Z_to_bv 64 0xac1f8); C8 (Z_to_bv 64 0xae9f8);
                               C8 (Z_to_bv 64 0xaf6e8); C8 (Z_to_bv 64 0xaf6f0); C8 (Z_to_bv 64 0xaf6e0)]
  /\ rw_cells asegs m 0x14062c [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0x1405b8 [C8 (Z_to_bv 64 0)].

#[using="Type"] Lemma rmap_cells_frame : forall m m' W, rmap_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> rmap_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4 & R5) MU WM HW. unfold AIMG_HI in HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x604000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold rmap_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]).
Qed.

Definition rmap_post (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ addr + size <= ATOP
  /\ munch [(bv_unsigned sp - RMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z m m' /\ wmono asegs m m'
  /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' addr [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
  /\ rng RNG' addr size /\ rng RNG' (shad addr) (shlen size)
  /\ fp_bw RNG'                                   (* [comment removed for export] *)
  /\ rmap_cells m'.

#[using="Type"] Lemma page_round_up_mult : forall s, s mod 4096 = 0 -> 0 <= s -> page_round_up_Z s = s.
Proof. intros s Hs H0. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma land_align4096 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
  intros x Hx.
  replace 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity.
  replace (x - x mod 4096) with (Z.shiftl (Z.shiftr x 12) 12).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 64) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma land_align2p18 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709289472 = x - x mod 262144.
Proof.
  intros x Hx.
  replace 18446744073709289472 with (Z.ldiff (Z.ones 64) (Z.ones 18)) by reflexivity.
  replace (x - x mod 262144) with (Z.shiftl (Z.shiftr x 18) 18).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^18) with 262144. Z.div_mod_to_equations. lia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 64) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma adec_mmap_rw_Some : forall len rsp a, adec_mmap ATOP len 3 rsp = Some a ->
  exists ci, rsp = mkEffectU (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))] [] [] ci
          /\ a mod 4096 = 0 /\ 0 < a /\ a + mmap_len len <= ATOP.
Proof.
  intros len rsp a H. unfold adec_mmap in H. cbn [Z.eqb] in H.
  destruct (dec_mmap len [] rsp) as [[e|a']|] eqn:D; try discriminate. injection H as <-.      (* [comment removed for export] *)
  destruct (dec_mmap_Some _ _ _ _ D) as [E OK]. exists []. split; [exact E|].
  pose proof (mmap_addr_ok_true _ _ _ OK) as [(M1 & M2 & M3) _]. unfold page_size in M1. change (@alloc_ceiling _) with ATOP in M3. auto.
Qed.

Definition rmap_spec__stmt : Prop := forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAP_STACK ->
  mem_inv asegs m ->
  a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> 0x10000 <= bv_unsigned a3 < 2^47 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
  rmap_cells m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rmap_post RNG sp addr size lo m RNG' m' ->
      implS asegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmap_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 1).
Variable K : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 37).
Variable addr : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 38).
Variable size : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 39).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'rmap_spec__stmt 40).
#[using="Type"] Lemma rmap_spec__body : ltac:(let T := type of (fun (h : rmap_spec__stmt) => h RNG R K Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m addr size lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (K, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (addr, (size, lo))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> NAME AAL SAL SPOS A0 ASZ RC RIMG RTLS RSTK UNR KONT. unfold AIMG_HI in A0.
  pose proof RC as RC0. (nd_pre RC0 5%nat; intros GPG PGSZ GOT DPM MLIM; nd_post).
  unfold rmap_entry in *. word_range sp SPR. word_range a3 A3R.
  pose proof (munch_refl [(bv_unsigned sp - RMAP_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _ _ _
            (fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               rmap_post RNG sp addr size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs))).
  2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
       (nd_pre PO 17%nat; intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PO ndR1__; nd_post; revert ndR1__; intros ->).
       eapply KONT. exact PO. }
  (* [comment removed for export] *)
  iprefix.
  carve_frame 32%nat ST.                                       (* [comment removed for export] *)
  step. step. step. step. step.                                (* [comment removed for export] *)
  step. step. step. step. step.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  carve_frame 96%nat ST.
  step. step. step. step. step. step. step.                    (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. if_lit.                                          (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS ASZ A0; Z.div_mod_to_equations; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  setreg 18 (Z_to_bv 64 addr) ltac:(rewrite land_align4096 by lia; f_equal; clear -AAL A0 ASZ SPOS; Z.div_mod_to_equations; lia).
  step. step. step. step. step.                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carve_frame 272%nat ST.
  step. step. step. step. step. step. step. step.              (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 NAME. lia. }   (* [comment removed for export] *)
  step. step. step. lstep.                                     (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step.        (* [comment removed for export] *)
  release_frame FR1 ST (bv_unsigned sp + -128).
  step. setreg 13 (Z_to_bv 64 50) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)
  step. step. step. step. step.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  icallk rt_mmap_stubP; [reflexivity|].
  intros a RNG' ms' (rsp & HF & Hdec & ->).
  (nd_pre (adec_mmap_rw_Some _ _ _ Hdec) 2%nat; intros ci ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 3%nat; intros AM1 AM2 AM3; nd_post).
  pose proof (page_round_up_mult size SAL ltac:(clear -SPOS; lia)) as PRU. unfold mmap_len in *. rewrite PRU in AM3. rewrite PRU.
  pose proof (fstepS_mmap_grant addr size 50 _ RNG RNG' HF (eq_refl : Z.land 50 MAP_NORESERVE = 0)) as GR. cbn [eff_ret] in GR.
  rewrite (unsigned_lit a) in GR by (clear -AM2 AM3 SPOS; lia). rewrite (unsigned_lit size) in GR by (clear -SPOS ASZ A0; lia).
  rewrite PRU in GR. specialize (GR ltac:(unfold page_size; exact AM1)). destruct GR as [GR1 GR2].
  pose proof HF as HF0. fstepS_transport HF.
  destruct (Z.eq_dec a addr) as [->|NE]. 2: { apply evtF_done. left. split; [exact NE|]. split; [exact AM2| atop_facts; exact AM3]. }
  unfold rt_regs. cbn [eff_ret]. rewrite eff_mem_zeros.
  replace (ret_pc (Z_to_bv 64 434372)) with (Z_to_bv 64 434372 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  apply (munch_weaken _ [(bv_unsigned sp - RMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z) in MU.
  2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
  sys_mem_zeros.
  (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS A0. lia. }   (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS A0. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. if_lit.                                                (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. step. step. step. if_lit. step.                        (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step.        (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -128) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp + -32) end.
  (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. clear -K3 A0 ASZ SPOS. lia. }   (* [comment removed for export] *)
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -32) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold rmap_post. destruct HF0 as [[FPLE _] [_ BW]].
  split; [exact FPLE|]. split; [exact AM3|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|]. split; [exact BW|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed.
End Zd1.
#[using="Type"] Lemma rmap_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAP_STACK ->
  mem_inv asegs m ->
  a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> 0x10000 <= bv_unsigned a3 < 2^47 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
  rmap_cells m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rmap_post RNG sp addr size lo m RNG' m' ->
      implS asegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmap_entry) fc None m (seg_rom asegs)).
Proof. exact rmap_spec__body. Qed.
End CANSEC2.
End TwB.
End F_ammap.

(* [comment removed for export] *)
Module F_aqchunk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. (nd_pre HP 3%nat; intros [lo' hi'] HI [H1 H2]; nd_post). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
(* [comment removed for export] *)
Local Ltac fp_base8 := lazymatch goal with |- (?a <= ?b /\ _)%Z => let X := leftmost a in let Y := leftmost b in first [ constr_eq X Y | is_Zlit X; is_Zlit Y ] end.
Local Ltac fp_find8s := first [ apply Exists_cons_hd; cbn [fst snd]; fp_base8; split; lia | apply Exists_cons_tl; fp_find8s ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8s | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section QChunk.
Variable DI : ADepotIface.

(* [comment removed for export] *)
Definition qchunk_post (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n S lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) t0 t1 t2 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xab270) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 S)
                  (Z_to_bv 64 hm) (Z_to_bv 64 n) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x37ff4) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 1072, bv_unsigned sp); (hm + 16, hm + 24); (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)] /\ 0 < id < 2^31
    /\ ADEPOT DI L m'.

Definition qchunk_spec__stmt : Prop := forall (L : alayout) (t hm S : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx b1 actx lo sz pc : Z) (uw top bot : word) (tb : list word) (tr : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 - ADEPOT_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 hm -> a3 = Z_to_bv 64 S ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> 0 <= n < 2^32 ->
  AIMG_HI <= hm -> hm + 24 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] -> rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 top; C8 bot] ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr -> In (pc :: tr) (al_U L) ->
  bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  (* [comment removed for export] *)
  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) -> tclr (al_nodes L) 1048576 -> tclr (al_store L) 8388608 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG hm 24 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  evtF asegs RNG (qchunk_post L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n S lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x37e7c) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 0).
Variable t : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 1).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 2).
Variable S : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 3).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 38).
Variable n : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 39).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 40).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 41).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 42).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 43).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 44).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 45).
Variable uw : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 46).
Variable top : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 47).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 48).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 49).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 50).
#[using="Type"] Lemma qchunk_spec__body : ltac:(let T := type of (fun (h : qchunk_spec__stmt) => h L t hm S RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n ctx b1 actx lo sz pc uw top bot tb tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (t, (hm, (S, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (ctx, (b1, (actx, (lo, (sz, (pc, (uw, (top, (bot, (tb, tr))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI TP -> -> -> HD UW B1 N H0 H1 TI TK T88 TSD CT CT8 TT CX0 C0 C1 T0 T1 SO TB LTB SZ SZB TR TU SPS STOP
         DEP N0 N1 R0 R1 DHN DHR DHT DHC DTN DTS DCN DCS XTNO XTST RIMG RTLS RSTK RS RCTX RT RH RND RSR. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE, AQUAR_Q, ATSDI, ATSDK, ATP88, ATSD in *.
  pose proof (munch_refl [(bv_unsigned sp - 1072, bv_unsigned sp); (hm + 16, hm + 24); (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 1072, bv_unsigned sp)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  carve_frame 48%nat ST.
  do 7 step.                                   (* [comment removed for export] *)
  step. lstep. step. step. if_lit.             (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  box RT. box RH. box RS.
  step. call_sp get_current_thread_spec;
    [exact ST | exact CEIL | lia | exact MI | exact TP | exact TI | exact TK | exact T88 | exact TSD | exact CT | lia | exact C1 | solve_rng | ].
  unbox RT. unbox RH. unbox RS. rename POST into ST. try rename MI0 into MI.
  step. if_cases K0; zify_cond K0; [exfalso; lia|].          (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  rw_split SO 1%nat SOa SOb. apply rw_cells_C4C4_to_C8 in SOb; [|lia].
  step. lstep. step. step.                     (* [comment removed for export] *)
  box RT. box RH. box RCTX.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (DEP1 : ADEPOT DI L mm)
      by (eapply (adi_frame DI); [exact DEP| exact MU0| exact WM0|];
          constructor; [| constructor]; cbn [fst snd]; intros a Ha; unfold AIMG_HI in *; lia) end.
  clear MU0 WM0 DEP.
  step. call_sp (adi_put DI L);
    [exact ST | exact CEIL | lia | exact MI | exact TP | reflexivity | reflexivity | exact SZ | exact SZB | exact TB | exact LTB | exact TR | exact TU
    | lia | lia | exact DEP1 | exact N0 | exact N1 | exact R0 | exact R1 | solve_rng | solve_rng | ].
  unbox RT. unbox RH. unbox RCTX. try rename MI0 into MI. clear DEP1.
  match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
  match goal with H : ADEPOT DI L ?mm |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into DEP2 end.
  match goal with H : 0 < ?i < 2 ^ 31 |- _ => rename H into ID; rename i into id end.
  zstep. zstep. zstep. zstep.                  (* [comment removed for export] *)
  rewrite Z.lor_0_l. rewrite (Z.mod_small id 4294967296) by lia.
  snapshot [(hm + 16, hm + 24)]%Z MU1 WM1.
  step.                                        (* [comment removed for export] *)
  zstep. lstep. lstep. zstep. zstep.           (* [comment removed for export] *)
  zstep. zstep. rewrite Z.lor_0_l.             (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  do 8 step.                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold qchunk_post. finish.
  - exact UW.
  - lia.
  - lia.
  - eapply (adi_frame DI); [exact DEP2| exact MU1| exact WM1|].
    constructor; [|constructor]. cbn [fst snd]. intros a Ha. unfold AIMG_HI in *. lia.
Qed.
End Zd1.
#[using="Type"] Lemma qchunk_spec : ltac:(let t := eval cbv delta [qchunk_spec__stmt] in qchunk_spec__stmt in exact t).
Proof. exact qchunk_spec__body. Qed.
End QChunk.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. (nd_pre HP 3%nat; intros [lo' hi'] HI [H1 H2]; nd_post). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
(* [comment removed for export] *)
Local Ltac fp_base8 := lazymatch goal with |- (?a <= ?b /\ _)%Z => let X := leftmost a in let Y := leftmost b in first [ constr_eq X Y | is_Zlit X; is_Zlit Y ] end.
Local Ltac fp_find8s := first [ apply Exists_cons_hd; cbn [fst snd]; fp_base8; split; lia | apply Exists_cons_tl; fp_find8s ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8s | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section QChunk.
Variable DI : ADepotIface.

(* [comment removed for export] *)
Definition qchunk_post (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n S lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) t0 t1 t2 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xab670) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 S)
                  (Z_to_bv 64 hm) (Z_to_bv 64 n) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3805c) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 1072, bv_unsigned sp); (hm + 16, hm + 24); (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)] /\ 0 < id < 2^31
    /\ ADEPOT DI L m'.

Definition qchunk_spec__stmt : Prop := forall (L : alayout) (t hm S : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx b1 actx lo sz pc : Z) (uw top bot : word) (tb : list word) (tr : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 - ADEPOT_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 hm -> a3 = Z_to_bv 64 S ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> 0 <= n < 2^32 ->
  AIMG_HI <= hm -> hm + 24 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] -> rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 top; C8 bot] ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr -> In (pc :: tr) (al_U L) ->
  bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  (* [comment removed for export] *)
  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) -> tclr (al_nodes L) 1048576 -> tclr (al_store L) 8388608 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG hm 24 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  evtF asegs RNG (qchunk_post L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n S lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x37ee4) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 0).
Variable t : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 1).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 2).
Variable S : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 3).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 38).
Variable n : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 39).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 40).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 41).
Variable actx : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 42).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 43).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 44).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 45).
Variable uw : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 46).
Variable top : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 47).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 48).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 49).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'qchunk_spec__stmt 50).
#[using="Type"] Lemma qchunk_spec__body : ltac:(let T := type of (fun (h : qchunk_spec__stmt) => h L t hm S RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n ctx b1 actx lo sz pc uw top bot tb tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (t, (hm, (S, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (ctx, (b1, (actx, (lo, (sz, (pc, (uw, (top, (bot, (tb, tr))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI TP -> -> -> HD UW B1 N H0 H1 TI TK T88 TSD CT CT8 TT CX0 C0 C1 T0 T1 SO TB LTB SZ SZB TR TU SPS STOP
         DEP N0 N1 R0 R1 DHN DHR DHT DHC DTN DTS DCN DCS XTNO XTST RIMG RTLS RSTK RS RCTX RT RH RND RSR. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE, AQUAR_Q, ATSDI, ATSDK, ATP88, ATSD in *.
  pose proof (munch_refl [(bv_unsigned sp - 1072, bv_unsigned sp); (hm + 16, hm + 24); (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 1072, bv_unsigned sp)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  carve_frame 48%nat ST.
  do 7 step.                                   (* [comment removed for export] *)
  step. lstep. step. step. if_lit.             (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  box RT. box RH. box RS.
  step. call_sp get_current_thread_spec;
    [exact ST | exact CEIL | lia | exact MI | exact TP | exact TI | exact TK | exact T88 | exact TSD | exact CT | lia | exact C1 | solve_rng | ].
  unbox RT. unbox RH. unbox RS. rename POST into ST. try rename MI0 into MI.
  step. if_cases K0; zify_cond K0; [exfalso; lia|].          (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  rw_split SO 1%nat SOa SOb. apply rw_cells_C4C4_to_C8 in SOb; [|lia].
  step. lstep. step. step.                     (* [comment removed for export] *)
  box RT. box RH. box RCTX.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (DEP1 : ADEPOT DI L mm)
      by (eapply (adi_frame DI); [exact DEP| exact MU0| exact WM0|];
          constructor; [| constructor]; cbn [fst snd]; intros a Ha; unfold AIMG_HI in *; lia) end.
  clear MU0 WM0 DEP.
  step. call_sp (adi_put DI L);
    [exact ST | exact CEIL | lia | exact MI | exact TP | reflexivity | reflexivity | exact SZ | exact SZB | exact TB | exact LTB | exact TR | exact TU
    | lia | lia | exact DEP1 | exact N0 | exact N1 | exact R0 | exact R1 | solve_rng | solve_rng | ].
  unbox RT. unbox RH. unbox RCTX. try rename MI0 into MI. clear DEP1.
  match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
  match goal with H : ADEPOT DI L ?mm |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into DEP2 end.
  match goal with H : 0 < ?i < 2 ^ 31 |- _ => rename H into ID; rename i into id end.
  zstep. zstep. zstep. zstep.                  (* [comment removed for export] *)
  rewrite Z.lor_0_l. rewrite (Z.mod_small id 4294967296) by lia.
  snapshot [(hm + 16, hm + 24)]%Z MU1 WM1.
  step.                                        (* [comment removed for export] *)
  zstep. lstep. lstep. zstep. zstep.           (* [comment removed for export] *)
  zstep. zstep. rewrite Z.lor_0_l.             (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  do 8 step.                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold qchunk_post. finish.
  - exact UW.
  - lia.
  - lia.
  - eapply (adi_frame DI); [exact DEP2| exact MU1| exact WM1|].
    constructor; [|constructor]. cbn [fst snd]. intros a Ha. unfold AIMG_HI in *. lia.
Qed.
End Zd1.
#[using="Type"] Lemma qchunk_spec : ltac:(let t := eval cbv delta [qchunk_spec__stmt] in qchunk_spec__stmt in exact t).
Proof. exact qchunk_spec__body. Qed.
End QChunk.
End CANSEC1.
End TwB.
End F_aqchunk.
