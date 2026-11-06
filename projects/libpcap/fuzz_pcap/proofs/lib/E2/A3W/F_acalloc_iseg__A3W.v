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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2 F_memsetZ.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MM_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_acalloc_iseg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2 F_memsetZ. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memsetZ.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition ACALLOC_SYM : Z := 0x5617c.    (* [comment removed for export] *)
Definition ACALLOC_PC : Z := 0x56650.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cicptA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (nm sz lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk0 junk1 junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x56664) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 sz)
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 0x56650) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
                  (Z_to_bv 64 nm) (Z_to_bv 64 0x56650) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89))
                  s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x566a8) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2160, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2144)
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [CB 8 junk0]
    /\ rw_cells asegs m' (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2120) [CB 2040 junk1]
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition cicptA_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nm sz lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2144 - 16 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 nm -> a1 = Z_to_bv 64 sz -> 0 <= nm < 2^64 -> 0 <= sz < 2^64 ->
  rw_cells asegs m 0xaf2d8 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xaf2fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0xa54a0 [C8 (Z_to_bv 64 0x140128); C8 (Z_to_bv 64 0xabdf8); C8 (Z_to_bv 64 0xae5f8);
                             C8 (Z_to_bv 64 0xaf2e8); C8 (Z_to_bv 64 0xaf2f0); C8 (Z_to_bv 64 0xaf2e0)] ->
  rw_cells asegs m 0x14014a [C1 (Z_to_bv 8 1)] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (cicptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc nm sz lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ACALLOC_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 34).
Variable nm : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 35).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 36).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 37).
#[using="Type"] Lemma cicptA_spec__body : ltac:(let T := type of (fun (h : cicptA_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nm sz lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (nm, (sz, lo)))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> NMR SZR INI MCS GOT CF34 RIMG RTLS RSTK. atop_facts. unfold ACALLOC_SYM.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2160, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  step.                                                          (* [comment removed for export] *)
  carve_frame 2144%nat ST.
  (* [comment removed for export] *)
  lazymatch type of FR with rw_cells ?segs ?mm ?A [CB ?n ?junk] =>
    apply (rw_cells_split_CB segs mm A [] n junk [] [8; 16; 2040; 80]%nat) in FR; [| cbn; lia]; cbn [app mk_CB_cells] in FR end.
  (* [comment removed for export] *)
  repeat match type of FR with context [CB _ ?j] => lazymatch j with firstn _ _ => idtac | skipn _ _ => idtac end;
           let x := fresh "jkf" in set (x := j) in FR; clearbody x end.
  rw_split FR 1%nat FRp FR'. rw_split FR' 1%nat FRa FR''. rw_split FR'' 1%nat FRt FRs.
  do 9 step.                                                     (* [comment removed for export] *)
  zstep. zstep. step. step. step.                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. carve_frame 16%nat ST.
  do 5 step. lstep. step. step. step. if_lit.                    (* [comment removed for export] *)
  do 4 step. release_frame FR ST (bv_unsigned sp + -2144).
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
  apply evtF_done. unfold cicptA_post. do 13 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FRp|]. split; [exact FRA|]. split; [exact FRt|]. exact FRs.
Qed.
End Zd1.
#[using="Type"] Lemma cicptA_spec : ltac:(let t := eval cbv delta [cicptA_spec__stmt] in cicptA_spec__stmt in exact t).
Proof. exact cicptA_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cicptB_post (sp gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (s3v : word) (F : bvmap 5 word) (fc : bv 32)
    (nm sz lo : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists m' (fr0 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x566c0) (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp t0 t1 t2
                  (Z_to_bv 64 (nm * sz)) (Z_to_bv 64 (bv_unsigned sp + -2136))
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (nm * sz)) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 1) (Z_to_bv 64 0) a6 a7
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x345e0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2192, bv_unsigned sp - 2144)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2192)
    /\ rw_cells asegs m' (bv_unsigned sp + -2192) [CB 8 fr0; C8 s3v; C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 sz); C8 sp; C8 (Z_to_bv 64 0x566c0)].

Definition cicptB_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nm sz lo : Z),
  stk asegs m lo (bv_unsigned sp + -2144) -> ATOP <= lo -> lo <= bv_unsigned sp - 2192 ->
  mem_inv asegs m ->
  s1 = Z_to_bv 64 sz -> s2 = Z_to_bv 64 nm -> 1 <= nm -> 1 <= sz -> nm * sz < 2^64 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (cicptB_post sp gp tp s4 s5 s6 s7 s8 s9 s10 s11 s3 F fc nm sz lo t0 t1 t2 a6 a7 t3 t4 t5 t6 m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x566ac) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 7).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 8).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 9).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 10).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 11).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 12).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 13).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 14).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 15).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 16).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 17).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 18).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 19).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 20).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 21).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 22).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 23).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 24).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 25).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 26).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 27).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 28).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 29).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 30).
Variable F : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 31).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 32).
Variable m : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 33).
Variable nm : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 34).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 35).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 36).
#[using="Type"] Lemma cicptB_spec__body : ltac:(let T := type of (fun (h : cicptB_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nm sz lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (nm, (sz, lo))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> NM SZ OV RIMG RTLS RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2192, bv_unsigned sp - 2144)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. step. step. step.                                (* [comment removed for export] *)
  carve_frame 48%nat ST.
  do 6 step.                                                     (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 SZ OV NM. nia. }      (* [comment removed for export] *)
  zstep.                                                         (* [comment removed for export] *)
  rewrite (Z.mul_comm sz nm).
  replace (Z.shiftr (nm * sz) 64) with 0
    by (rewrite Z.shiftr_div_pow2 by (clear; lia); symmetry; apply Z.div_small; split; [apply Z.mul_nonneg_nonneg; clear -NM SZ; lia | exact OV]).
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. rewrite (Z.mul_comm sz nm).                             (* [comment removed for export] *)
  do 9 step.                                                     (* [comment removed for export] *)
  apply evtF_done. unfold cicptB_post, AINSTANCE. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact FR.
Qed.
End Zd2.
#[using="Type"] Lemma cicptB_spec : ltac:(let t := eval cbv delta [cicptB_spec__stmt] in cicptB_spec__stmt in exact t).
Proof. exact cicptB_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cicptC_post (rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (UB n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch [(UB, UB + n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].

Definition cicptC_spec__stmt : Prop := forall RNG sp gp tp t0 t1 t2 s1x a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s6v s3i s2i s1i s0i : word) (F : bvmap 5 word) fc (m : amem) (UB n SB lo : Z) (fr0 junk2 uj : list byte),
  stk asegs m lo (bv_unsigned sp + -2192) -> ATOP <= lo -> lo <= bv_unsigned sp - 2192 ->
  mem_inv asegs m ->
  0 < UB -> 1 <= n -> UB + n <= lo ->
  0 <= SB -> SB <= UB -> UB < SB + 137438953472 -> SB + 137438953472 < 2^64 ->
  rw_cells asegs m (AINSTANCE + 32) [C8 (Z_to_bv 64 SB)] ->
  rw_cells asegs m 0xa54d0 [C8 (Z_to_bv 64 0xa7360)] ->
  rw_cells asegs m 0xa7358 [C8 (Z_to_bv 64 0x9e6a0); C8 (Z_to_bv 64 0x9ead4)] ->
  rw_cells asegs m UB [CB (Z.to_nat n) uj] ->
  rw_cells asegs m (bv_unsigned sp + -2192) [CB 8 fr0; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 (Z_to_bv 64 0x566c0)] ->
  (exists csP, rw_cells asegs m (bv_unsigned sp + -2144) csP /\ cells_size csP = 8%nat) ->
  (exists csA, rw_cells asegs m (bv_unsigned sp + -2136) csA /\ cells_size csA = 16%nat) ->
  (exists csT, rw_cells asegs m (bv_unsigned sp + -2120) csT /\ cells_size csT = 2040%nat) ->
  rw_cells asegs m (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG UB n ->
  evtF asegs RNG (cicptC_post rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 F fc UB n lo m)
    (MS (mkR (Z_to_bv 64 0x345e4) (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp t0 t1 t2 (Z_to_bv 64 n) s1x (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x345e4) fc None m (seg_rom asegs)).
Section Zd3.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 0).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 1).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 2).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 3).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 4).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 5).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 6).
Variable s1x : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 7).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 8).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 9).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 10).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 11).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 12).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 13).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 14).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 15).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 16).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 17).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 18).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 19).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 20).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 21).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 22).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 23).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 24).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 25).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 26).
Variable rav : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 27).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 28).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 29).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 30).
Variable s3v : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 31).
Variable s4v : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 32).
Variable s5v : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 33).
Variable s6v : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 34).
Variable s3i : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 35).
Variable s2i : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 36).
Variable s1i : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 37).
Variable s0i : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 38).
Variable F : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 39).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 40).
Variable m : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 41).
Variable UB : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 42).
Variable n : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 43).
Variable SB : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 44).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 45).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 46).
Variable junk2 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 47).
Variable uj : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 48).
#[using="Type"] Lemma cicptC_spec__body : ltac:(let T := type of (fun (h : cicptC_spec__stmt) => h RNG sp gp tp t0 t1 t2 s1x a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rav s0v s1v s2v s3v s4v s5v s6v s3i s2i s1i s0i F fc m UB n SB lo fr0 junk2 uj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (sp, (gp, (tp, (t0, (t1, (t2, (s1x, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (rav, (s0v, (s1v, (s2v, (s3v, (s4v, (s5v, (s6v, (s3i, (s2i, (s1i, (s0i, (F, (fc, (m, (UB, (n, (SB, (lo, (fr0, (junk2, uj))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI UB0 N1 UBLO SB0 SB1 SB2 SB3 INST GOT80 REAL UJ FR48 [csP [FRP SZP]] [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RTLS RSTK RU. atop_facts.
  unfold AINSTANCE in *. change (700312 + 32) with 700344 in INST. word_range sp SPR.
  pose proof (munch_refl [(UB, UB + n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (rw_cells_forget asegs _ _ _ FRP) as [jP FRP']. rewrite SZP in FRP'. clear FRP.
  pose proof (rw_cells_forget asegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  pose proof (rw_cells_forget asegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 UB0 UBLO SPR LO. lia. }                 (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 SB0 SB1 SB3 UB0 UBLO SPR LO. lia. }     (* [comment removed for export] *)
  zstep. zstep.                                                  (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. clear -K2 SB0 SB1 SB2 SB3 UB0 UBLO SPR LO. lia. }   (* [comment removed for export] *)
  step. step. step.                                              (* [comment removed for export] *)
  step. step. step.                                              (* [comment removed for export] *)
  step. call (memset_specZ RNG UB 0 n uj).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ _ [CB _ _] => exact UJ
       | |- rng _ _ _ => exact RU
       | |- _ => clear -UB0 N1 UBLO SPR LO; lia
       end.
  rename POST into UZ.
  step. step.                                                    (* [comment removed for export] *)
  do 7 step.                                                     (* [comment removed for export] *)
  zstep. do 8 step. zstep. step.                                 (* [comment removed for export] *)
  release_frame FR48 ST (bv_unsigned sp + -2144).
  release_frame FRP' ST (bv_unsigned sp + -2136).
  release_frame FRA' ST (bv_unsigned sp + -2120).
  release_frame FRT' ST (bv_unsigned sp + -80).
  release_frame FRS ST (bv_unsigned sp).
  apply evtF_done. unfold cicptC_post. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact UZ].
Qed.
End Zd3.
#[using="Type"] Lemma cicptC_spec : ltac:(let t := eval cbv delta [cicptC_spec__stmt] in cicptC_spec__stmt in exact t).
Proof. exact cicptC_spec__body. Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memsetZ.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition ACALLOC_SYM : Z := 0x561e4.    (* [comment removed for export] *)
Definition ACALLOC_PC : Z := 0x566b8.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cicptA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (nm sz lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk0 junk1 junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x566cc) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 sz)
                  (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 0x566b8) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
                  (Z_to_bv 64 nm) (Z_to_bv 64 0x566b8) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89))
                  s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x56710) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2160, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2144)
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [CB 8 junk0]
    /\ rw_cells asegs m' (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2120) [CB 2040 junk1]
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition cicptA_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nm sz lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2144 - 16 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 nm -> a1 = Z_to_bv 64 sz -> 0 <= nm < 2^64 -> 0 <= sz < 2^64 ->
  rw_cells asegs m 0xaf6d8 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xaf6fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0xa5880 [C8 (Z_to_bv 64 0x140528); C8 (Z_to_bv 64 0xac1f8); C8 (Z_to_bv 64 0xae9f8);
                             C8 (Z_to_bv 64 0xaf6e8); C8 (Z_to_bv 64 0xaf6f0); C8 (Z_to_bv 64 0xaf6e0)] ->
  rw_cells asegs m 0x14054a [C1 (Z_to_bv 8 1)] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (cicptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc nm sz lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ACALLOC_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 34).
Variable nm : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 35).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 36).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'cicptA_spec__stmt 37).
#[using="Type"] Lemma cicptA_spec__body : ltac:(let T := type of (fun (h : cicptA_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nm sz lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (nm, (sz, lo)))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> NMR SZR INI MCS GOT CF34 RIMG RTLS RSTK. atop_facts. unfold ACALLOC_SYM.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2160, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  step.                                                          (* [comment removed for export] *)
  carve_frame 2144%nat ST.
  (* [comment removed for export] *)
  lazymatch type of FR with rw_cells ?segs ?mm ?A [CB ?n ?junk] =>
    apply (rw_cells_split_CB segs mm A [] n junk [] [8; 16; 2040; 80]%nat) in FR; [| cbn; lia]; cbn [app mk_CB_cells] in FR end.
  (* [comment removed for export] *)
  repeat match type of FR with context [CB _ ?j] => lazymatch j with firstn _ _ => idtac | skipn _ _ => idtac end;
           let x := fresh "jkf" in set (x := j) in FR; clearbody x end.
  rw_split FR 1%nat FRp FR'. rw_split FR' 1%nat FRa FR''. rw_split FR'' 1%nat FRt FRs.
  do 9 step.                                                     (* [comment removed for export] *)
  zstep. zstep. step. step. step.                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. carve_frame 16%nat ST.
  do 5 step. lstep. step. step. step. if_lit.                    (* [comment removed for export] *)
  do 4 step. release_frame FR ST (bv_unsigned sp + -2144).
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
  apply evtF_done. unfold cicptA_post. do 13 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FRp|]. split; [exact FRA|]. split; [exact FRt|]. exact FRs.
Qed.
End Zd1.
#[using="Type"] Lemma cicptA_spec : ltac:(let t := eval cbv delta [cicptA_spec__stmt] in cicptA_spec__stmt in exact t).
Proof. exact cicptA_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cicptB_post (sp gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (s3v : word) (F : bvmap 5 word) (fc : bv 32)
    (nm sz lo : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists m' (fr0 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x56728) (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp t0 t1 t2
                  (Z_to_bv 64 (nm * sz)) (Z_to_bv 64 (bv_unsigned sp + -2136))
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (nm * sz)) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 1) (Z_to_bv 64 0) a6 a7
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x34648) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2192, bv_unsigned sp - 2144)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2192)
    /\ rw_cells asegs m' (bv_unsigned sp + -2192) [CB 8 fr0; C8 s3v; C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 sz); C8 sp; C8 (Z_to_bv 64 0x56728)].

Definition cicptB_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nm sz lo : Z),
  stk asegs m lo (bv_unsigned sp + -2144) -> ATOP <= lo -> lo <= bv_unsigned sp - 2192 ->
  mem_inv asegs m ->
  s1 = Z_to_bv 64 sz -> s2 = Z_to_bv 64 nm -> 1 <= nm -> 1 <= sz -> nm * sz < 2^64 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (cicptB_post sp gp tp s4 s5 s6 s7 s8 s9 s10 s11 s3 F fc nm sz lo t0 t1 t2 a6 a7 t3 t4 t5 t6 m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x56714) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 7).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 8).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 9).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 10).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 11).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 12).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 13).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 14).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 15).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 16).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 17).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 18).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 19).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 20).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 21).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 22).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 23).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 24).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 25).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 26).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 27).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 28).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 29).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 30).
Variable F : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 31).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 32).
Variable m : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 33).
Variable nm : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 34).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 35).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'cicptB_spec__stmt 36).
#[using="Type"] Lemma cicptB_spec__body : ltac:(let T := type of (fun (h : cicptB_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nm sz lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (nm, (sz, lo))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> NM SZ OV RIMG RTLS RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2192, bv_unsigned sp - 2144)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. step. step. step.                                (* [comment removed for export] *)
  carve_frame 48%nat ST.
  do 6 step.                                                     (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 SZ OV NM. nia. }      (* [comment removed for export] *)
  zstep.                                                         (* [comment removed for export] *)
  rewrite (Z.mul_comm sz nm).
  replace (Z.shiftr (nm * sz) 64) with 0
    by (rewrite Z.shiftr_div_pow2 by (clear; lia); symmetry; apply Z.div_small; split; [apply Z.mul_nonneg_nonneg; clear -NM SZ; lia | exact OV]).
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. rewrite (Z.mul_comm sz nm).                             (* [comment removed for export] *)
  do 9 step.                                                     (* [comment removed for export] *)
  apply evtF_done. unfold cicptB_post, AINSTANCE. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact FR.
Qed.
End Zd2.
#[using="Type"] Lemma cicptB_spec : ltac:(let t := eval cbv delta [cicptB_spec__stmt] in cicptB_spec__stmt in exact t).
Proof. exact cicptB_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cicptC_post (rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (UB n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch [(UB, UB + n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].

Definition cicptC_spec__stmt : Prop := forall RNG sp gp tp t0 t1 t2 s1x a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s6v s3i s2i s1i s0i : word) (F : bvmap 5 word) fc (m : amem) (UB n SB lo : Z) (fr0 junk2 uj : list byte),
  stk asegs m lo (bv_unsigned sp + -2192) -> ATOP <= lo -> lo <= bv_unsigned sp - 2192 ->
  mem_inv asegs m ->
  0 < UB -> 1 <= n -> UB + n <= lo ->
  0 <= SB -> SB <= UB -> UB < SB + 137438953472 -> SB + 137438953472 < 2^64 ->
  rw_cells asegs m (AINSTANCE + 32) [C8 (Z_to_bv 64 SB)] ->
  rw_cells asegs m 0xa58b0 [C8 (Z_to_bv 64 0xa7740)] ->
  rw_cells asegs m 0xa7738 [C8 (Z_to_bv 64 0x9ea84); C8 (Z_to_bv 64 0x9eeb8)] ->
  rw_cells asegs m UB [CB (Z.to_nat n) uj] ->
  rw_cells asegs m (bv_unsigned sp + -2192) [CB 8 fr0; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 (Z_to_bv 64 0x56728)] ->
  (exists csP, rw_cells asegs m (bv_unsigned sp + -2144) csP /\ cells_size csP = 8%nat) ->
  (exists csA, rw_cells asegs m (bv_unsigned sp + -2136) csA /\ cells_size csA = 16%nat) ->
  (exists csT, rw_cells asegs m (bv_unsigned sp + -2120) csT /\ cells_size csT = 2040%nat) ->
  rw_cells asegs m (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG UB n ->
  evtF asegs RNG (cicptC_post rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 F fc UB n lo m)
    (MS (mkR (Z_to_bv 64 0x3464c) (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp t0 t1 t2 (Z_to_bv 64 n) s1x (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3464c) fc None m (seg_rom asegs)).
Section Zd3.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 0).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 1).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 2).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 3).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 4).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 5).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 6).
Variable s1x : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 7).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 8).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 9).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 10).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 11).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 12).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 13).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 14).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 15).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 16).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 17).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 18).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 19).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 20).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 21).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 22).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 23).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 24).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 25).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 26).
Variable rav : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 27).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 28).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 29).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 30).
Variable s3v : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 31).
Variable s4v : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 32).
Variable s5v : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 33).
Variable s6v : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 34).
Variable s3i : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 35).
Variable s2i : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 36).
Variable s1i : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 37).
Variable s0i : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 38).
Variable F : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 39).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 40).
Variable m : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 41).
Variable UB : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 42).
Variable n : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 43).
Variable SB : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 44).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 45).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 46).
Variable junk2 : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 47).
Variable uj : ltac2:(SecDietF.SzSecF.ty 'cicptC_spec__stmt 48).
#[using="Type"] Lemma cicptC_spec__body : ltac:(let T := type of (fun (h : cicptC_spec__stmt) => h RNG sp gp tp t0 t1 t2 s1x a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rav s0v s1v s2v s3v s4v s5v s6v s3i s2i s1i s0i F fc m UB n SB lo fr0 junk2 uj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (sp, (gp, (tp, (t0, (t1, (t2, (s1x, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (rav, (s0v, (s1v, (s2v, (s3v, (s4v, (s5v, (s6v, (s3i, (s2i, (s1i, (s0i, (F, (fc, (m, (UB, (n, (SB, (lo, (fr0, (junk2, uj))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI UB0 N1 UBLO SB0 SB1 SB2 SB3 INST GOT80 REAL UJ FR48 [csP [FRP SZP]] [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RTLS RSTK RU. atop_facts.
  unfold AINSTANCE in *. change (701336 + 32) with 701368 in INST. word_range sp SPR.
  pose proof (munch_refl [(UB, UB + n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (rw_cells_forget asegs _ _ _ FRP) as [jP FRP']. rewrite SZP in FRP'. clear FRP.
  pose proof (rw_cells_forget asegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  pose proof (rw_cells_forget asegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 UB0 UBLO SPR LO. lia. }                 (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 SB0 SB1 SB3 UB0 UBLO SPR LO. lia. }     (* [comment removed for export] *)
  zstep. zstep.                                                  (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. clear -K2 SB0 SB1 SB2 SB3 UB0 UBLO SPR LO. lia. }   (* [comment removed for export] *)
  step. step. step.                                              (* [comment removed for export] *)
  step. step. step.                                              (* [comment removed for export] *)
  step. call (memset_specZ RNG UB 0 n uj).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ _ [CB _ _] => exact UJ
       | |- rng _ _ _ => exact RU
       | |- _ => clear -UB0 N1 UBLO SPR LO; lia
       end.
  rename POST into UZ.
  step. step.                                                    (* [comment removed for export] *)
  do 7 step.                                                     (* [comment removed for export] *)
  zstep. do 8 step. zstep. step.                                 (* [comment removed for export] *)
  release_frame FR48 ST (bv_unsigned sp + -2144).
  release_frame FRP' ST (bv_unsigned sp + -2136).
  release_frame FRA' ST (bv_unsigned sp + -2120).
  release_frame FRT' ST (bv_unsigned sp + -80).
  release_frame FRS ST (bv_unsigned sp).
  apply evtF_done. unfold cicptC_post. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact UZ].
Qed.
End Zd3.
#[using="Type"] Lemma cicptC_spec : ltac:(let t := eval cbv delta [cicptC_spec__stmt] in cicptC_spec__stmt in exact t).
Proof. exact cicptC_spec__body. Qed.
End CANSEC1.
End TwB.
End F_acalloc_iseg.

(* [comment removed for export] *)
Module ACalloc_iface.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_acalloc_iseg.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition ACALLOC_STACK : Z := 4096.

Section Stmts.
Variable CI : list (Z * Z).
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

Definition amalloc_postU (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (n lo : Z) (m : amem) (ub : list byte)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ match snd r with
       | None => False
       | Some p => exists A,
           a0 = Z_to_bv 64 A /\ ablock_range A n
           /\ AHEAP L RNG' (fst r) (HB p A n :: LB) m'
           /\ rw_cells asegs m' A [CB (Z.to_nat n) ub]
           /\ rng RNG' A n /\ rng RNG' (shad A) (shlen (n + 7))
           /\ (is_primary n = false -> A = aptr_addr (fst r) p)
       end.

#[using="Type"] Lemma amalloc_postU_post : forall L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m ub r RNG' ms',
  amalloc_postU L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m ub r RNG' ms' ->
  amalloc_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms'.
Proof.
  intros until ms'. intros (FP & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & MI & ST & HP & R).
  split; [exact FP|]. exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
  split; [exact E|]. split; [exact MI|]. split; [exact ST|]. split; [exact HP|].
  destruct (snd r) as [p|]; [| exact R]. (nd_pre R 8%nat; intros A R1 R2 R3 R4 R5 R6 R7; nd_post).
  exists A, ub. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|]. split; [exact R6| exact R7].
Qed.

(* [comment removed for export] *)
Definition acalloc_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (nm sz n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  AHEAP L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - ACALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 nm -> a1 = Z_to_bv 64 sz -> 1 <= nm -> 1 <= sz -> n = nm * sz -> 1 <= n <= AREQMAX -> is_primary n = true ->
  aunw m L RNG lo ACALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> ACALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (acalloc ATOP RESV st nm sz))
        (epostF (amalloc_postU L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m (repeat (Z_to_bv 8 0) (Z.to_nat n))))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ACALLOC_SYM) fc None m (seg_rom asegs)).
End Stmts.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_acalloc_iseg.TwB.   (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition ACALLOC_STACK : Z := 4096.

Section Stmts.
Variable CI : list (Z * Z).
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

Definition amalloc_postU (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (n lo : Z) (m : amem) (ub : list byte)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ match snd r with
       | None => False
       | Some p => exists A,
           a0 = Z_to_bv 64 A /\ ablock_range A n
           /\ AHEAP L RNG' (fst r) (HB p A n :: LB) m'
           /\ rw_cells asegs m' A [CB (Z.to_nat n) ub]
           /\ rng RNG' A n /\ rng RNG' (shad A) (shlen (n + 7))
           /\ (is_primary n = false -> A = aptr_addr (fst r) p)
       end.

#[using="Type"] Lemma amalloc_postU_post : forall L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m ub r RNG' ms',
  amalloc_postU L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m ub r RNG' ms' ->
  amalloc_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms'.
Proof.
  intros until ms'. intros (FP & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & MI & ST & HP & R).
  split; [exact FP|]. exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
  split; [exact E|]. split; [exact MI|]. split; [exact ST|]. split; [exact HP|].
  destruct (snd r) as [p|]; [| exact R]. (nd_pre R 8%nat; intros A R1 R2 R3 R4 R5 R6 R7; nd_post).
  exists A, ub. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|]. split; [exact R6| exact R7].
Qed.

(* [comment removed for export] *)
Definition acalloc_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (nm sz n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  AHEAP L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - ACALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 nm -> a1 = Z_to_bv 64 sz -> 1 <= nm -> 1 <= sz -> n = nm * sz -> 1 <= n <= AREQMAX -> is_primary n = true ->
  aunw m L RNG lo ACALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> ACALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (acalloc ATOP RESV st nm sz))
        (epostF (amalloc_postU L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m (repeat (Z_to_bv 8 0) (Z.to_nat n))))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ACALLOC_SYM) fc None m (seg_rom asegs)).
End Stmts.
End CANSEC1.
End TwB.
End ACalloc_iface.

(* [comment removed for export] *)
Module F_ammapz.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac split_for_access_post H ::= split_junk_name H.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition mmapz_entry := 0x69b64.
End CANSEC1.
Notation MMAPZ_STACK := 320 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition mmapz_post (RNG : footprint) (sp : word) (a size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG' /\ fp_bw RNG'
  /\ a mod 4096 = 0 /\ 0 < a /\ a + size <= ATOP
  /\ munch [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp); (a, a + size)]%Z m m' /\ wmono asegs m m'
  /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' a [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
  /\ rng RNG' a size /\ rng RNG' (shad a) (shlen size)
  /\ rmap_cells m'.

Definition mmapz_spec__stmt : Prop := forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - MMAPZ_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 size -> size mod 4096 = 0 -> 0 < size -> size < 2^40 -> bv_unsigned a1 <> 0 ->
  rmap_cells m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a, FRESH a = true -> 0 < a -> a + size <= ATOP -> AIMG_HI <= a /\ (a + size <= bv_unsigned sp - 48 \/ bv_unsigned sp <= a)) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + size <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (* [comment removed for export] *)
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> mmapz_post RNG sp a size lo m RNG' m' ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 size 3 34) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 mmapz_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 1).
Variable K : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 3).
Variable FRESH : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 38).
Variable size : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 39).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 40).
#[using="Type"] Lemma mmapz_spec__body : ltac:(let T := type of (fun (h : mmapz_spec__stmt) => h RNG R K Q FRESH ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m size lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (K, (Q, (FRESH, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (size, lo))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> SAL SPOS SZ NAME RC RIMG RTLS RSTK FROK UNR KONT.
  pose proof RC as RC0. (nd_pre RC0 5%nat; intros GPG PGSZ GOT DPM MLIM; nd_post). word_range a1 A1R.
  unfold AIMG_HI, mmapz_entry in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _ _ _
            (fun a RNG' ms' => (FRESH a = false /\ 0 < a /\ a mod 4096 = 0 /\ a + size <= ATOP /\ fp_le RNG RNG')
                            \/ FRESH a = true /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               mmapz_post RNG sp a size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs))).
  2: { intros a RNG' ms' [(NF & P1 & P2 & P3 & P4)|[FR PO]]; [apply UNR; assumption|].
       (nd_pre PO 17%nat; intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PO ndR1__; nd_post; revert ndR1__; intros ->).
       eapply KONT; [exact FR | exact PO]. }
  (* [comment removed for export] *)
  iprefix.
  carve_frame 48%nat ST.
  step. step. step. step. step.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 9 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS SZ; Z.div_mod_to_equations; lia).
  step. step. step. step. step.                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carve_frame 272%nat ST.
  step. step. step. step. step. step. step. step.              (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 NAME A1R. lia. }   (* [comment removed for export] *)
  step. step. step. lstep.                                     (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step.        (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -48).
  step. setreg 13 (Z_to_bv 64 34) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)
  step. step. step. step. step.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  icallk rt_mmap_stubP; [reflexivity|].
  intros a RNG' ms' (rsp & HF & Hdec & ->).
  (nd_pre (adec_mmap_rw_Some _ _ _ Hdec) 2%nat; intros ci ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 3%nat; intros AM1 AM2 AM3; nd_post).
  pose proof (page_round_up_mult size SAL ltac:(clear -SPOS; lia)) as PRU. unfold mmap_len in *. rewrite PRU in AM3. rewrite PRU.
  pose proof (fstepS_mmap_grant 0 size 34 _ RNG RNG' HF (eq_refl : Z.land 34 MAP_NORESERVE = 0)) as GR. cbn [eff_ret] in GR.
  rewrite (unsigned_lit a) in GR by (clear -AM2 AM3 SPOS; lia). rewrite (unsigned_lit size) in GR by (clear -SPOS SZ; lia).
  rewrite PRU in GR. specialize (GR ltac:(unfold page_size; exact AM1)). destruct GR as [GR1 GR2].
  pose proof HF as HF0. destruct HF0 as [[FPLE _] [_ BW]].
  destruct (FRESH a) eqn:HFR.
  2: { fstepS_transport HF. apply evtF_done. left. split; [reflexivity|]. split; [exact AM2|]. split; [exact AM1|]. split; [atop_facts; exact AM3| exact FPLE]. }
  destruct (FROK a HFR AM2 AM3) as [AIM AFR].
  fstepS_transport HF.
  unfold rt_regs. cbn [eff_ret]. rewrite eff_mem_zeros.
  replace (ret_pc (Z_to_bv 64 433132)) with (Z_to_bv 64 433132 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  apply (munch_weaken _ [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp); (a, a + size)]%Z) in MU.
  2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
  sys_mem_zeros.
  (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS. lia. }   (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 a) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 a) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. if_lit.                                                (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. step. step. step. if_lit. step.                        (* [comment removed for export] *)
  step. step. step. step. step. step. step.                    (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -48) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold mmapz_post.
  split; [exact FPLE|]. split; [exact BW|]. split; [exact AM1|]. split; [exact AM2|]. split; [exact AM3|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed.
End Zd1.
#[using="Type"] Lemma mmapz_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - MMAPZ_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 size -> size mod 4096 = 0 -> 0 < size -> size < 2^40 -> bv_unsigned a1 <> 0 ->
  rmap_cells m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a, FRESH a = true -> 0 < a -> a + size <= ATOP -> AIMG_HI <= a /\ (a + size <= bv_unsigned sp - 48 \/ bv_unsigned sp <= a)) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + size <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (* [comment removed for export] *)
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> mmapz_post RNG sp a size lo m RNG' m' ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 size 3 34) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 mmapz_entry) fc None m (seg_rom asegs)).
Proof. exact mmapz_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation RMAPD_STACK := 368 (only parsing).   (* [comment removed for export] *)
Definition rmapd_post (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ addr + size <= ATOP
  /\ munch [(bv_unsigned sp - RMAPD_STACK, bv_unsigned sp); (addr, addr + size)]%Z m m' /\ wmono asegs m m'
  /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' addr [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
  /\ rng RNG' addr size /\ rng RNG' (shad addr) (shlen size)
  /\ fp_bw RNG'
  /\ rmap_cells m'.
Definition rmapd_entry := 0x72334.
Definition rmapd_spec__stmt : Prop := forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAPD_STACK ->
  mem_inv asegs m ->
  a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 0 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
  rmap_cells m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rmapd_post RNG sp addr size lo m RNG' m' ->
      implS asegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmapd_entry) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 1).
Variable K : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 37).
Variable addr : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 38).
Variable size : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 39).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 40).
#[using="Type"] Lemma rmapd_spec__body : ltac:(let T := type of (fun (h : rmapd_spec__stmt) => h RNG R K Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m addr size lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (K, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (addr, (size, lo))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> -> AAL SAL SPOS A0 ASZ RC RIMG RTLS RSTK UNR KONT. unfold AIMG_HI in A0.
  pose proof RC as RC0. (nd_pre RC0 5%nat; intros GPG PGSZ GOT DPM MLIM; nd_post).
  unfold rmapd_entry in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - RMAPD_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _ _ _
            (fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               rmapd_post RNG sp addr size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs))).
  2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
       (nd_pre PO 17%nat; intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PO ndR1__; nd_post; revert ndR1__; intros ->).
       eapply KONT. exact PO. }
  (* [comment removed for export] *)
  iprefix.
  step. step. step. step.                                      (* [comment removed for export] *)
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
  step. if_lit.                                                (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step.        (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -96).
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
  apply (munch_weaken _ [(bv_unsigned sp - RMAPD_STACK, bv_unsigned sp); (addr, addr + size)]%Z) in MU.
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
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -96) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold rmapd_post. destruct HF0 as [[FPLE _] [_ BW]].
  split; [exact FPLE|]. split; [exact AM3|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|]. split; [exact BW|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed.
End Zd2.
#[using="Type"] Lemma rmapd_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAPD_STACK ->
  mem_inv asegs m ->
  a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 0 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
  rmap_cells m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rmapd_post RNG sp addr size lo m RNG' m' ->
      implS asegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmapd_entry) fc None m (seg_rom asegs)).
Proof. exact rmapd_spec__body. Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac split_for_access_post H ::= split_junk_name H.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition mmapz_entry := 0x69bcc.
End CANSEC1.
Notation MMAPZ_STACK := 320 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition mmapz_post (RNG : footprint) (sp : word) (a size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG' /\ fp_bw RNG'
  /\ a mod 4096 = 0 /\ 0 < a /\ a + size <= ATOP
  /\ munch [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp); (a, a + size)]%Z m m' /\ wmono asegs m m'
  /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' a [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
  /\ rng RNG' a size /\ rng RNG' (shad a) (shlen size)
  /\ rmap_cells m'.

Definition mmapz_spec__stmt : Prop := forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - MMAPZ_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 size -> size mod 4096 = 0 -> 0 < size -> size < 2^40 -> bv_unsigned a1 <> 0 ->
  rmap_cells m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a, FRESH a = true -> 0 < a -> a + size <= ATOP -> AIMG_HI <= a /\ (a + size <= bv_unsigned sp - 48 \/ bv_unsigned sp <= a)) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + size <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (* [comment removed for export] *)
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> mmapz_post RNG sp a size lo m RNG' m' ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 size 3 34) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 mmapz_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 1).
Variable K : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 3).
Variable FRESH : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 38).
Variable size : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 39).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'mmapz_spec__stmt 40).
#[using="Type"] Lemma mmapz_spec__body : ltac:(let T := type of (fun (h : mmapz_spec__stmt) => h RNG R K Q FRESH ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m size lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (K, (Q, (FRESH, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (size, lo))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> SAL SPOS SZ NAME RC RIMG RTLS RSTK FROK UNR KONT.
  pose proof RC as RC0. (nd_pre RC0 5%nat; intros GPG PGSZ GOT DPM MLIM; nd_post). word_range a1 A1R.
  unfold AIMG_HI, mmapz_entry in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _ _ _
            (fun a RNG' ms' => (FRESH a = false /\ 0 < a /\ a mod 4096 = 0 /\ a + size <= ATOP /\ fp_le RNG RNG')
                            \/ FRESH a = true /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               mmapz_post RNG sp a size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs))).
  2: { intros a RNG' ms' [(NF & P1 & P2 & P3 & P4)|[FR PO]]; [apply UNR; assumption|].
       (nd_pre PO 17%nat; intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PO ndR1__; nd_post; revert ndR1__; intros ->).
       eapply KONT; [exact FR | exact PO]. }
  (* [comment removed for export] *)
  iprefix.
  carve_frame 48%nat ST.
  step. step. step. step. step.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 9 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS SZ; Z.div_mod_to_equations; lia).
  step. step. step. step. step.                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carve_frame 272%nat ST.
  step. step. step. step. step. step. step. step.              (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 NAME A1R. lia. }   (* [comment removed for export] *)
  step. step. step. lstep.                                     (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step.        (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -48).
  step. setreg 13 (Z_to_bv 64 34) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)
  step. step. step. step. step.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  icallk rt_mmap_stubP; [reflexivity|].
  intros a RNG' ms' (rsp & HF & Hdec & ->).
  (nd_pre (adec_mmap_rw_Some _ _ _ Hdec) 2%nat; intros ci ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 3%nat; intros AM1 AM2 AM3; nd_post).
  pose proof (page_round_up_mult size SAL ltac:(clear -SPOS; lia)) as PRU. unfold mmap_len in *. rewrite PRU in AM3. rewrite PRU.
  pose proof (fstepS_mmap_grant 0 size 34 _ RNG RNG' HF (eq_refl : Z.land 34 MAP_NORESERVE = 0)) as GR. cbn [eff_ret] in GR.
  rewrite (unsigned_lit a) in GR by (clear -AM2 AM3 SPOS; lia). rewrite (unsigned_lit size) in GR by (clear -SPOS SZ; lia).
  rewrite PRU in GR. specialize (GR ltac:(unfold page_size; exact AM1)). destruct GR as [GR1 GR2].
  pose proof HF as HF0. destruct HF0 as [[FPLE _] [_ BW]].
  destruct (FRESH a) eqn:HFR.
  2: { fstepS_transport HF. apply evtF_done. left. split; [reflexivity|]. split; [exact AM2|]. split; [exact AM1|]. split; [atop_facts; exact AM3| exact FPLE]. }
  destruct (FROK a HFR AM2 AM3) as [AIM AFR].
  fstepS_transport HF.
  unfold rt_regs. cbn [eff_ret]. rewrite eff_mem_zeros.
  replace (ret_pc (Z_to_bv 64 433236)) with (Z_to_bv 64 433236 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  apply (munch_weaken _ [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp); (a, a + size)]%Z) in MU.
  2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
  sys_mem_zeros.
  (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS. lia. }   (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 a) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 a) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. if_lit.                                                (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. step. step. step. if_lit. step.                        (* [comment removed for export] *)
  step. step. step. step. step. step. step.                    (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -48) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold mmapz_post.
  split; [exact FPLE|]. split; [exact BW|]. split; [exact AM1|]. split; [exact AM2|]. split; [exact AM3|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed.
End Zd1.
#[using="Type"] Lemma mmapz_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - MMAPZ_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 size -> size mod 4096 = 0 -> 0 < size -> size < 2^40 -> bv_unsigned a1 <> 0 ->
  rmap_cells m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a, FRESH a = true -> 0 < a -> a + size <= ATOP -> AIMG_HI <= a /\ (a + size <= bv_unsigned sp - 48 \/ bv_unsigned sp <= a)) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + size <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (* [comment removed for export] *)
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> mmapz_post RNG sp a size lo m RNG' m' ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 size 3 34) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 mmapz_entry) fc None m (seg_rom asegs)).
Proof. exact mmapz_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation RMAPD_STACK := 368 (only parsing).   (* [comment removed for export] *)
Definition rmapd_post (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ addr + size <= ATOP
  /\ munch [(bv_unsigned sp - RMAPD_STACK, bv_unsigned sp); (addr, addr + size)]%Z m m' /\ wmono asegs m m'
  /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' addr [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
  /\ rng RNG' addr size /\ rng RNG' (shad addr) (shlen size)
  /\ fp_bw RNG'
  /\ rmap_cells m'.
Definition rmapd_entry := 0x7239c.
Definition rmapd_spec__stmt : Prop := forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAPD_STACK ->
  mem_inv asegs m ->
  a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 0 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
  rmap_cells m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rmapd_post RNG sp addr size lo m RNG' m' ->
      implS asegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmapd_entry) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 1).
Variable K : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 37).
Variable addr : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 38).
Variable size : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 39).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'rmapd_spec__stmt 40).
#[using="Type"] Lemma rmapd_spec__body : ltac:(let T := type of (fun (h : rmapd_spec__stmt) => h RNG R K Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m addr size lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (K, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (addr, (size, lo))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> -> AAL SAL SPOS A0 ASZ RC RIMG RTLS RSTK UNR KONT. unfold AIMG_HI in A0.
  pose proof RC as RC0. (nd_pre RC0 5%nat; intros GPG PGSZ GOT DPM MLIM; nd_post).
  unfold rmapd_entry in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - RMAPD_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _ _ _
            (fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               rmapd_post RNG sp addr size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs))).
  2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
       (nd_pre PO 17%nat; intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PO ndR1__; nd_post; revert ndR1__; intros ->).
       eapply KONT. exact PO. }
  (* [comment removed for export] *)
  iprefix.
  step. step. step. step.                                      (* [comment removed for export] *)
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
  step. if_lit.                                                (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step.        (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -96).
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
  apply (munch_weaken _ [(bv_unsigned sp - RMAPD_STACK, bv_unsigned sp); (addr, addr + size)]%Z) in MU.
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
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -96) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold rmapd_post. destruct HF0 as [[FPLE _] [_ BW]].
  split; [exact FPLE|]. split; [exact AM3|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|]. split; [exact BW|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed.
End Zd2.
#[using="Type"] Lemma rmapd_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAPD_STACK ->
  mem_inv asegs m ->
  a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 0 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
  rmap_cells m ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rmapd_post RNG sp addr size lo m RNG' m' ->
      implS asegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmapd_entry) fc None m (seg_rom asegs)).
Proof. exact rmapd_spec__body. Qed.
End CANSEC2.
End TwB.
End F_ammapz.

(* [comment removed for export] *)
Module F_aensure.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.
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
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition ensure_entry := 0x36ba4.
End CANSEC1.
Notation ENSURE_STACK := 448 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition m3_cells (L : alayout) (m : amem) : Prop :=
     poison_cells m /\ rmap_cells m
  /\ rw_cells asegs m 0xade60 [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xade64 [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells asegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))]
  /\ rw_cells asegs m (al_ctx L + 152) [C8 (Z_to_bv 64 (al_t L))]
  /\ rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 (al_space_beg L))]                      (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaafc0 [C4 (Z_to_bv 64 4294967295)]                            (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaafc8 [C8 (Z_to_bv 64 (al_space_beg L + K_SPACE_SIZE))]       (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaafd0 [C1 (Z_to_bv 8 0)].                                      (* [comment removed for export] *)

#[using="Type"] Lemma m3_cells_frame : forall L m m' W, m3_cells L m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => ((AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= ATPv + -88 \/ ATPv + -80 <= fst iv)) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv)) W -> m3_cells L m'.
Proof.
  intros L m m' W (PC & RC & C1' & C2 & C3 & C4' & C5 & C6 & C7 & C8' & C9) MU WM HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x603000 -> 0x10000 <= A -> disjoint_from W A k).   (* [comment removed for export] *)
  { clear -HW. intros A k Hk HA HA0. unfold AIMG_HI, AIMG_LO in HW. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  assert (DC : disjoint_from W (al_ctx L + 152) 8).
  { clear -HW. unfold AIMG_HI, AIMG_LO in HW. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  assert (DT : disjoint_from W (ATPv + -88) 8).      (* [comment removed for export] *)
  { clear -HW. unfold AIMG_HI, AIMG_LO in HW. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  (nd_pre PC 7%nat; intros P1 P2 P3 P4 P5 P6 P7; nd_post). (nd_pre RC 5%nat; intros Q1 Q2 Q3 Q4 Q5; nd_post).
  split; [unfold poison_cells; repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; apply D; lia])|].
  split; [unfold rmap_cells; repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; apply D; lia])|].
  unfold ATP88, ATSD in *.
  repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; first [exact DC | exact DT | apply D; lia]]).
Qed.

#[using="Type"] Lemma m3_cells_frame_rc : forall L m m' W, m3_cells L m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => ((AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= ATPv + -88 \/ ATPv + -80 <= fst iv)) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv)) W -> rmap_cells m'.
Proof. intros L m m' W MC MU WM HW. exact (proj1 (proj2 (m3_cells_frame L m m' W MC MU WM HW))). Qed.

(* [comment removed for export] *)
Definition ensure_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c nf lo : Z) (sj : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let FA := afreearr L c in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists new sj',
     (   (4 * nf <= mfa /\ new = mfa /\ st2 = st /\ RNG' = RNG)
      \/ (mfa < 4 * nf /\ new = rup (4 * nf) K_FREEARR_MAP /\ st2 = put_cls c (cls_set_mapped_free_array new r) st
          /\ rw_cells asegs m' (FA + mfa) [CB (Z.to_nat (new - mfa)) (repeat (Z_to_bv 8 0) (Z.to_nat (new - mfa)))]
          /\ fill_at m' (shad (FA + mfa)) (shlen (new - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (new - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (new - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf <= new <= K_FREEARR_MAX /\ mfa <= new /\ new mod K_FREEARR_MAP = 0
  /\ munch [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp); (FA + mfa, FA + new); (shad (FA + mfa), shad (FA + mfa) + shlen (new - mfa));
            (al_t L + 2800, al_t L + 3168); (aregion_info L c + 24, aregion_info L c + 32)]%Z m m'
  /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' (aregion_info L c + 16)
       [C8 (Z_to_bv 64 (c_num_freed r)); C8 (Z_to_bv 64 new); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
        C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)]
  /\ u64arr asegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ azero m' (shad (FA + new)) (shlen (K_FREEARR_MAX - new))
  /\ m3_cells L m'.

#[using="Type"] Lemma rup18_facts : forall x, 0 <= x -> x <= rup x 262144 <= x + 262143 /\ rup x 262144 mod 262144 = 0 /\ (x mod 262144 = 0 -> rup x 262144 = x).
Proof. intros x Hx. unfold rup. Z.div_mod_to_equations. lia. Qed.

Definition ensure_spec__stmt : Prop := forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c nf lo : Z) (sj : list word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ENSURE_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 RI -> a2 = Z_to_bv 64 (aregion L c) -> a3 = Z_to_bv 64 nf ->
  m3_cells L m ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 (c_num_freed r)); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 0 <= nf -> 4 * nf <= K_FREEARR_MAX ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      ensure_ret L RNG sp st c nf lo sj m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (k st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (ensure_free_array st c nf k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ensure_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 37).
Variable L : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 38).
Variable st : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 39).
Variable c : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 40).
Variable nf : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 41).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 42).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 43).
Let mfa := c_mapped_free_array (get_cls st c).
Let new := rup (4 * nf) 262144.
Let FAM := al_space_beg L + c * 4294967296 + 3758096384 + mfa.
#[using="mfa new FAM"] Lemma ensure_spec__body : ltac:(let T := type of (fun (h : ensure_spec__stmt) => h RNG R k Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c nf lo sj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (L, (st, (c, (nf, (lo, sj)))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC REG STATS LSJ AZ SBE HC MFA MFAM NF NF4 SP1 SP2 SP3 CX0 CX1 T0 T1 TCX SCX TSP RIMG RTLS RSTK RCTX RT RRI CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. (nd_pre MC0 11%nat; intros PC RC TI TK T88 TSD CT ISB IREL ISE IPRE; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, ensure_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  chg (c_mapped_free_array (get_cls st c)) mfa.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  iprefix.
  carve_frame 48%nat ST.
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  rewrite RIE in REG |- *. rewrite FAE in AZ.
  step.                                                        (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  step. if_cases KE; zify_cond KE.                             (* [comment removed for export] *)
  { (* [comment removed for export] *)
    assert (KE' : 4 * nf <= mfa) by (rewrite Z.shiftl_mul_pow2, Z.mod_small in KE by (clear -NF NF4; lia); clear -KE; lia). clear KE.
    step. step. step. step. step. step. step. step.            (* [comment removed for export] *)
    lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -48) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
    apply evtF_done. unfold ensure_free_array.
    replace (nf * 4 <=? c_mapped_free_array (get_cls st c)) with true by (symmetry; apply Z.leb_le; fold mfa; clear -KE'; lia).
    eapply KONT. unfold ensure_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold mfa. split; [apply fp_le_refl|].
    exists mfa, sj. split; [left; split; [exact KE'| split; [reflexivity| split; reflexivity]]|].
    split; [clear -KE' MFA NF4; lia|]. split; [clear; lia|]. split; [exact MFAM|].
    rewrite FAE, RIE.
    split. { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. } split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [assumption|]. split; [exact LSJ|].
    split.
    - eapply azero_frame; [exact AZ | exact MU | exact WM |]. intros Hp. cbn [disjoint_from].
      assert (SHR : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)
                    /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (536870912 - mfa) <= 0x10007fff8000).
      { rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MFA. Z.div_mod_to_equations. lia. }
      clear -SHR CEIL LO. split; [lia| exact I].
    - eapply m3_cells_frame; [exact MC | exact MU | exact WM |].
      apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX1; unfold AIMG_HI, AIMG_LO; lia | apply Forall_nil]. }
  (* [comment removed for export] *)
  assert (KE' : mfa < 4 * nf) by (rewrite Z.shiftl_mul_pow2, Z.mod_small in KE by (clear -NF NF4; lia); clear -KE; lia). clear KE.
  (pose proof (rup18_facts (4 * nf) ltac:(clear -NF; lia)) as ndP__; nd_pre ndP__ 3%nat; intros RU1 RU2 RU3; nd_post).
  chg (rup (4 * nf) 262144) new.
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 new) ltac:(rewrite Z.shiftl_mul_pow2, land_align2p18 by (clear -NF NF4; lia); f_equal;
                                   subst new; unfold rup; clear -NF NF4; Z.div_mod_to_equations; lia).
  zstep. zstep. step. if_cases KC; zify_cond KC. { exfalso. clear -KC RU1 RU2 NF4. Z.div_mod_to_equations. lia. }   (* [comment removed for export] *)
  lstep.                                                       (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  unfold aregion, K_REGION. change (2^32) with 4294967296.
  setreg 9 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) ltac:(f_equal; clear; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. zstep. step. step. step. step.                         (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply evtF_done. unfold ensure_free_array.
  replace (nf * 4 <=? c_mapped_free_array (get_cls st c)) with false by (symmetry; apply Z.leb_gt; fold mfa; clear -KE'; lia).
  replace (rup (nf * 4) K_FREEARR_MAP) with new by (subst new; unfold K_FREEARR_MAP; f_equal; clear; lia).
  replace (K_FREEARR_MAX <? new) with false by (symmetry; apply Z.ltb_ge; unfold K_FREEARR_MAX; clear -KC; lia).
  cbv iota. unfold ev. rewrite aembed_vis. cbn [aev_tree]. unfold PROT_RW, F_FIXED.
  unfold region_beg, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296. rewrite SBE. fold mfa.
  chg (al_space_beg L + c * 4294967296 + 3758096384 + mfa) FAM.
  assert (FAM8 : FAM mod 4096 = 0 /\ 0x10007fff8000 <= FAM /\ FAM + (new - mfa) <= al_space_beg L + 137438953472 /\ (new - mfa) mod 4096 = 0 /\ 0 < new - mfa).
  { subst FAM. clear -SP1 SP3 HC MFA MFAM KE' RU1 RU2 KC NF. Z.div_mod_to_equations. lia. }
  (nd_pre FAM8 5%nat; intros FA1 FA2 FA3 FA4 FA5; nd_post).
  assert (FA0 : al_space_beg L + 4096 <= FAM) by (unfold FAM; clear -HC MFA; lia).
  name_sp sp (-48).
  eapply rmap_spec with (addr := FAM) (size := new - mfa) (lo := lo).
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite Hsp; eassumption
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- rmap_cells _ => eapply m3_cells_frame_rc; [exact MC | exact MU | exact WM | apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX1; unfold AIMG_HI, AIMG_LO; lia | apply Forall_nil]]
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => reflexivity
       | |- _ mod 4096 = 0 => assumption
       | |- 0 < _ - _ => exact FA5
       end.
  all: try (unfold AIMG_HI; clear -FA1 FA2 FA3 FA4 FA5 SP2 CEIL LO; rewrite ?unsigned_lit by lia; lia).
  { (* [comment removed for export] *)
    intros a RNG' ms' NE P1 P2. unfold fixed_answer_ok, is_err, TWO64.
    replace (2 ^ 64 - 4096 <? a) with false by (symmetry; apply Z.ltb_ge; clear -P2 FA5; atop_facts; lia).
    replace (a =? FAM) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [negb orb]. rewrite aembed_aundef_. apply implF_ret_unr. }
  (* [comment removed for export] *)
  intros RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RP.
  (nd_pre RP 11%nat; intros FPLE _ MU2 WM2 MI2 ST2 ZNEW GR1 GR2 BW RC2; nd_post). unname_sp.
  (* [comment removed for export] *)
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RTLS. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI.
  (* [comment removed for export] *)
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO FA2 FA3 SP2; lia).
  xport REG MU2 WM2 ltac:(clear -SPR CEIL LO FA2 FA3 SP2 HC; lia).
  xport STATS MU2 WM2 ltac:(rewrite LSJ; ub TSP; clear -SPR CEIL LO FA0 FA2 FA3 SP2 T0 T1 Y; lia).
  clear ST. rename ST2 into ST.
  assert (AZ2 : azero m2 (shad FAM) (shlen (536870912 - mfa))).
  { eapply azero_frame; [eapply azero_frame; [exact AZ | exact MU | exact WM |] | exact MU2 | exact WM2 |];
      intros _; cbn [disjoint_from]; subst FAM; rewrite ?shad_div, ?shlen_div; unfold ASHOFF;
      clear -SPR CEIL LO SP1 SP2 HC MFA KC RU1 KE'; Z.div_mod_to_equations; lia. }
  assert (MUF : munch [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp); (FAM, FAM + (new - mfa)); (shad FAM, shad FAM + shlen (new - mfa));
                       (al_t L + 2800, al_t L + 3168); (al_space_beg L + 137438953472 + c * 128 + 24, al_space_beg L + 137438953472 + c * 128 + 32)]%Z m m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
  clear MU MU2. pose proof (wmono_trans _ _ _ _ WM WM2) as WMF. clear WM WM2.
  assert (WOK : Forall (fun iv => ((AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= ATPv + -88 \/ ATPv + -80 <= fst iv)) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv))
           [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp); (FAM, FAM + (new - mfa)); (shad FAM, shad FAM + shlen (new - mfa));
            (al_t L + 2800, al_t L + 3168); (al_space_beg L + 137438953472 + c * 128 + 24, al_space_beg L + 137438953472 + c * 128 + 32)]%Z).
  { ub TCX. ub SCX. unfold AIMG_HI, AIMG_LO.
    do 5 (apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX0 CX1 T0 T1 TIC SP1 SP2 HC MFA FA0 FA2 FA3 KC Y Y0;
                              with_band CX0 ltac:(rewrite ?shad_div, ?shlen_div; unfold ASHOFF; split; Z.div_mod_to_equations; lia) |]). apply Forall_nil. }   (* [comment removed for export] *)
  pose proof (m3_cells_frame L m m2 _ MC MUF WMF WOK) as MC2.
  clear TI TK T88 TSD CT ISB IREL ISE IPRE.
  pose proof MC2 as MC2'. (nd_pre MC2' 11%nat; intros PC2 _ TI TK T88 TSD CT ISB IREL ISE IPRE; nd_post). unfold ATP88, ATSD in T88, TSD.
  (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 224324)) with (Z_to_bv 64 224324 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 FA2 FA3 SP2. rewrite ?unsigned_lit in K1 by lia. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. }                                                (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  pose proof (azero_cb m2 _ _ (shlen (new - mfa)) AZ2 ltac:(rewrite !shlen_div; clear -MFA KC KE' RU1; Z.div_mod_to_equations; lia)) as SHCB.
  clear AZ2.
  assert (SHF : 0x2008fff7000 <= shad FAM /\ shad FAM + shlen (new - mfa) <= 0x10007fff8000 /\ 0 < shlen (new - mfa)).
  { rewrite shad_div, shlen_div. unfold ASHOFF. clear -FA2 FA3 FA4 FA5 SP2. Z.div_mod_to_equations. lia. }
  (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
  step. (nd_pre (sclr_int _ _ CX0 ltac:(clear -CXI; lia) ltac:(clear -CX1; lia)) 4%nat; intros kC9 CB9 CB9a CB9b; nd_post). (nd_pre (sclr_int _ _ T0 ltac:(clear -TIC; lia) ltac:(clear -T1; lia)) 4%nat; intros kT9 TB9 TB9a TB9b; nd_post).   (* [comment removed for export] *)
  call_sp (poison_shadow_spec RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FAM (new - mfa) 250 lo).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => first [assumption | unfold ablk; right; clear -FA2 FA3 SP2; lia]   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => exact PC2
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => exact SHCB
       | |- rng _ (shad _) _ => exact GR2
       | |- rng _ _ _ => solve_rng
       end.
  all: try (atop_facts; clear -FA1 FA2 FA3 FA4 FA5 SP2 CEIL LO KC RU1 KE' MFA; rewrite ?shlen_div; first [lia | Z.div_mod_to_equations; lia]).
  all: try clear kC9 CB9 CB9a CB9b kT9 TB9 TB9a TB9b.
  (* [comment removed for export] *)
  step. (nd_pre (sclr_int _ _ T0 ltac:(clear -TIC; lia) ltac:(clear -T1; lia)) 4%nat; intros kT9 TB9 TB9a TB9b; nd_post).   (* [comment removed for export] *)
  call_sp (thread_stats_spec RNG' (al_ctx L) (al_t L) lo).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ _ _ => assumption
       | |- rng _ _ _ => solve_rng
       end.
  all: try (unfold AIMG_HI; clear -CEIL LO CX0 CX1 T0 T1 CXI TIC; lia).
  all: match goal with |- ?G => idtac "REMT" G end.
  all: try clear kT9 TB9 TB9a TB9b.
  aload STATS 10 (al_t L + 2800 + 80). aload STATS 9 (al_t L + 2800 + 72).
  zstep. zstep.                                                (* [comment removed for export] *)
  snapshot [(al_t L + 2800, al_t L + 3168)]%Z MUs WMs.
  box CT. box ZNEW. box REG.
  lazymatch goal with P : rw_cells asegs _ (shad FAM) _ |- _ => rename P into SHPO end. box SHPO.   (* [comment removed for export] *)
  astore STATS 9. astore STATS 10.
  carry SHPO MUs WMs ltac:(with_band T0 ltac:(lia)).
  carry REG MUs WMs ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 Y; lia).
  carry CT MUs WMs ltac:(ub TCX; clear -HC CX0 CX1 T0 T1 Y; lia).
  carry ZNEW MUs WMs ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 FA0 FA2 FA3 FA5 Y; lia).
  clear MUs WMs.
  snapshot [(al_space_beg L + 137438953472 + c * 128 + 24, al_space_beg L + 137438953472 + c * 128 + 32)]%Z MUr WMr.
  box CT. box ZNEW. box STATS.
  step. step.                                                  (* [comment removed for export] *)
  carry CT MUr WMr ltac:(ub SCX; clear -HC CX0 CX1 SP1 SP2 Y; lia).
  carry ZNEW MUr WMr ltac:(clear -HC SP1 SP2 FA0 FA2 FA3 FA5; lia).
  carry STATS MUr WMr ltac:(rewrite ?upd_length, LSJ; ub TSP; clear -HC T0 T1 SP1 SP2 Y; lia).
  clear MUr WMr.
  step. step.                                                  (* [comment removed for export] *)
  step. step. step. step. step. step. step.                    (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -48) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done.
  unfold fixed_answer_ok, is_err, TWO64. rewrite Z.eqb_refl.
  replace (2 ^ 64 - 4096 <? FAM) with false by (symmetry; apply Z.ltb_ge; clear -FA3 FA5 SP2; lia). cbn [negb orb].
  eapply KONT. unfold ensure_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold mfa. split; [exact FPLE|].
  lazymatch goal with |- context [u64arr asegs _ _ ?ws] => idtac | H : u64arr asegs _ (al_t L + 2800) ?ws |- _ => exists new, ws end.
  rewrite FAE, RIE. fold FAM.
  split. { right. split; [exact KE'|]. split; [subst new; f_equal; clear; lia|]. split; [reflexivity|].
           split; [exact ZNEW|]. split; [assumption|]. split; [exact GR1|]. split; [exact GR2| exact BW]. }
  split; [clear -RU1 KC; lia|]. split; [clear -RU1 KE'; lia|]. split; [exact RU2|].
  split. { eapply munch_weaken; [| exact MUF]. unfold sub_fp, FAM. cbn [outside]. clear. intros x Hx. lia. }
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [assumption|]. split; [assumption|]. split; [rewrite ?upd_length; exact LSJ|].
  split.
  { pose proof (azero_split m _ _ (shlen (new - mfa)) AZ ltac:(rewrite !shlen_div; clear -MFA KC KE' RU1; Z.div_mod_to_equations; lia)) as AZT.
    replace (shad FAM + shlen (new - mfa)) with (shad (FAM + (new - mfa))) in AZT by (apply shad_add_shlen; clear -FA1; Z.div_mod_to_equations; lia).
    replace (shlen (536870912 - mfa) - shlen (new - mfa)) with (shlen (536870912 - new)) in AZT by (rewrite !shlen_div; clear -FA4 MFAM RU2 MFA; Z.div_mod_to_equations; lia).
    replace (al_space_beg L + c * 4294967296 + 3758096384 + new) with (FAM + (new - mfa)) by (unfold FAM; clear; lia).
    eapply azero_frame; [exact AZT | exact MUF | exact WMF |]. intros Hp. cbn [disjoint_from].
    pose proof (shad_add_shlen FAM (new - mfa) ltac:(clear -FA1; Z.div_mod_to_equations; lia)) as SE.
    assert (SHT : shad (FAM + (new - mfa)) + shlen (536870912 - new) <= 0x10007fff8000).
    { rewrite shad_div, shlen_div. unfold ASHOFF, FAM. clear -SP2 KC RU1 MFA HC KE'. Z.div_mod_to_equations. lia. }
    clear -SE SHT SHF1 SHF2 SHF3 CEIL LO FA2 FA3 FA5 T0 SP1 SP2 HC. with_band T0 ltac:(repeat split; lia). }   (* [comment removed for export] *)
  eapply m3_cells_frame; [exact MC | eassumption | eassumption | exact WOK].
Qed.
End Zd1.
#[using="Type"] Lemma ensure_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c nf lo : Z) (sj : list word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ENSURE_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 RI -> a2 = Z_to_bv 64 (aregion L c) -> a3 = Z_to_bv 64 nf ->
  m3_cells L m ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 (c_num_freed r)); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 0 <= nf -> 4 * nf <= K_FREEARR_MAX ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      ensure_ret L RNG sp st c nf lo sj m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (k st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (ensure_free_array st c nf k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ensure_entry) fc None m (seg_rom asegs)).
Proof. exact ensure_spec__body. Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition ensure_entry := 0x36c0c.
End CANSEC1.
Notation ENSURE_STACK := 448 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition m3_cells (L : alayout) (m : amem) : Prop :=
     poison_cells m /\ rmap_cells m
  /\ rw_cells asegs m 0xae260 [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xae264 [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells asegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))]
  /\ rw_cells asegs m (al_ctx L + 152) [C8 (Z_to_bv 64 (al_t L))]
  /\ rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 (al_space_beg L))]                      (* [comment removed for export] *)
  /\ rw_cells asegs m 0xab3c0 [C4 (Z_to_bv 64 4294967295)]                            (* [comment removed for export] *)
  /\ rw_cells asegs m 0xab3c8 [C8 (Z_to_bv 64 (al_space_beg L + K_SPACE_SIZE))]       (* [comment removed for export] *)
  /\ rw_cells asegs m 0xab3d0 [C1 (Z_to_bv 8 0)].                                      (* [comment removed for export] *)

#[using="Type"] Lemma m3_cells_frame : forall L m m' W, m3_cells L m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => ((AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= ATPv + -88 \/ ATPv + -80 <= fst iv)) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv)) W -> m3_cells L m'.
Proof.
  intros L m m' W (PC & RC & C1' & C2 & C3 & C4' & C5 & C6 & C7 & C8' & C9) MU WM HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x604000 -> 0x10000 <= A -> disjoint_from W A k).   (* [comment removed for export] *)
  { clear -HW. intros A k Hk HA HA0. unfold AIMG_HI, AIMG_LO in HW. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  assert (DC : disjoint_from W (al_ctx L + 152) 8).
  { clear -HW. unfold AIMG_HI, AIMG_LO in HW. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  assert (DT : disjoint_from W (ATPv + -88) 8).      (* [comment removed for export] *)
  { clear -HW. unfold AIMG_HI, AIMG_LO in HW. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  (nd_pre PC 7%nat; intros P1 P2 P3 P4 P5 P6 P7; nd_post). (nd_pre RC 5%nat; intros Q1 Q2 Q3 Q4 Q5; nd_post).
  split; [unfold poison_cells; repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; apply D; lia])|].
  split; [unfold rmap_cells; repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; apply D; lia])|].
  unfold ATP88, ATSD in *.
  repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; first [exact DC | exact DT | apply D; lia]]).
Qed.

#[using="Type"] Lemma m3_cells_frame_rc : forall L m m' W, m3_cells L m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => ((AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= ATPv + -88 \/ ATPv + -80 <= fst iv)) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv)) W -> rmap_cells m'.
Proof. intros L m m' W MC MU WM HW. exact (proj1 (proj2 (m3_cells_frame L m m' W MC MU WM HW))). Qed.

(* [comment removed for export] *)
Definition ensure_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c nf lo : Z) (sj : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let FA := afreearr L c in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists new sj',
     (   (4 * nf <= mfa /\ new = mfa /\ st2 = st /\ RNG' = RNG)
      \/ (mfa < 4 * nf /\ new = rup (4 * nf) K_FREEARR_MAP /\ st2 = put_cls c (cls_set_mapped_free_array new r) st
          /\ rw_cells asegs m' (FA + mfa) [CB (Z.to_nat (new - mfa)) (repeat (Z_to_bv 8 0) (Z.to_nat (new - mfa)))]
          /\ fill_at m' (shad (FA + mfa)) (shlen (new - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (new - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (new - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf <= new <= K_FREEARR_MAX /\ mfa <= new /\ new mod K_FREEARR_MAP = 0
  /\ munch [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp); (FA + mfa, FA + new); (shad (FA + mfa), shad (FA + mfa) + shlen (new - mfa));
            (al_t L + 2800, al_t L + 3168); (aregion_info L c + 24, aregion_info L c + 32)]%Z m m'
  /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' (aregion_info L c + 16)
       [C8 (Z_to_bv 64 (c_num_freed r)); C8 (Z_to_bv 64 new); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
        C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)]
  /\ u64arr asegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ azero m' (shad (FA + new)) (shlen (K_FREEARR_MAX - new))
  /\ m3_cells L m'.

#[using="Type"] Lemma rup18_facts : forall x, 0 <= x -> x <= rup x 262144 <= x + 262143 /\ rup x 262144 mod 262144 = 0 /\ (x mod 262144 = 0 -> rup x 262144 = x).
Proof. intros x Hx. unfold rup. Z.div_mod_to_equations. lia. Qed.

Definition ensure_spec__stmt : Prop := forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c nf lo : Z) (sj : list word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ENSURE_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 RI -> a2 = Z_to_bv 64 (aregion L c) -> a3 = Z_to_bv 64 nf ->
  m3_cells L m ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 (c_num_freed r)); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 0 <= nf -> 4 * nf <= K_FREEARR_MAX ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      ensure_ret L RNG sp st c nf lo sj m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (k st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (ensure_free_array st c nf k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ensure_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 37).
Variable L : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 38).
Variable st : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 39).
Variable c : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 40).
Variable nf : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 41).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 42).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'ensure_spec__stmt 43).
Let mfa := c_mapped_free_array (get_cls st c).
Let new := rup (4 * nf) 262144.
Let FAM := al_space_beg L + c * 4294967296 + 3758096384 + mfa.
#[using="mfa new FAM"] Lemma ensure_spec__body : ltac:(let T := type of (fun (h : ensure_spec__stmt) => h RNG R k Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c nf lo sj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (L, (st, (c, (nf, (lo, sj)))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC REG STATS LSJ AZ SBE HC MFA MFAM NF NF4 SP1 SP2 SP3 CX0 CX1 T0 T1 TCX SCX TSP RIMG RTLS RSTK RCTX RT RRI CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. (nd_pre MC0 11%nat; intros PC RC TI TK T88 TSD CT ISB IREL ISE IPRE; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, ensure_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  chg (c_mapped_free_array (get_cls st c)) mfa.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  iprefix.
  carve_frame 48%nat ST.
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  rewrite RIE in REG |- *. rewrite FAE in AZ.
  step.                                                        (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  step. if_cases KE; zify_cond KE.                             (* [comment removed for export] *)
  { (* [comment removed for export] *)
    assert (KE' : 4 * nf <= mfa) by (rewrite Z.shiftl_mul_pow2, Z.mod_small in KE by (clear -NF NF4; lia); clear -KE; lia). clear KE.
    step. step. step. step. step. step. step. step.            (* [comment removed for export] *)
    lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -48) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
    apply evtF_done. unfold ensure_free_array.
    replace (nf * 4 <=? c_mapped_free_array (get_cls st c)) with true by (symmetry; apply Z.leb_le; fold mfa; clear -KE'; lia).
    eapply KONT. unfold ensure_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold mfa. split; [apply fp_le_refl|].
    exists mfa, sj. split; [left; split; [exact KE'| split; [reflexivity| split; reflexivity]]|].
    split; [clear -KE' MFA NF4; lia|]. split; [clear; lia|]. split; [exact MFAM|].
    rewrite FAE, RIE.
    split. { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. } split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [assumption|]. split; [exact LSJ|].
    split.
    - eapply azero_frame; [exact AZ | exact MU | exact WM |]. intros Hp. cbn [disjoint_from].
      assert (SHR : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)
                    /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (536870912 - mfa) <= 0x10007fff8000).
      { rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MFA. Z.div_mod_to_equations. lia. }
      clear -SHR CEIL LO. split; [lia| exact I].
    - eapply m3_cells_frame; [exact MC | exact MU | exact WM |].
      apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX1; unfold AIMG_HI, AIMG_LO; lia | apply Forall_nil]. }
  (* [comment removed for export] *)
  assert (KE' : mfa < 4 * nf) by (rewrite Z.shiftl_mul_pow2, Z.mod_small in KE by (clear -NF NF4; lia); clear -KE; lia). clear KE.
  (pose proof (rup18_facts (4 * nf) ltac:(clear -NF; lia)) as ndP__; nd_pre ndP__ 3%nat; intros RU1 RU2 RU3; nd_post).
  chg (rup (4 * nf) 262144) new.
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 new) ltac:(rewrite Z.shiftl_mul_pow2, land_align2p18 by (clear -NF NF4; lia); f_equal;
                                   subst new; unfold rup; clear -NF NF4; Z.div_mod_to_equations; lia).
  zstep. zstep. step. if_cases KC; zify_cond KC. { exfalso. clear -KC RU1 RU2 NF4. Z.div_mod_to_equations. lia. }   (* [comment removed for export] *)
  lstep.                                                       (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  unfold aregion, K_REGION. change (2^32) with 4294967296.
  setreg 9 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) ltac:(f_equal; clear; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. zstep. step. step. step. step.                         (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply evtF_done. unfold ensure_free_array.
  replace (nf * 4 <=? c_mapped_free_array (get_cls st c)) with false by (symmetry; apply Z.leb_gt; fold mfa; clear -KE'; lia).
  replace (rup (nf * 4) K_FREEARR_MAP) with new by (subst new; unfold K_FREEARR_MAP; f_equal; clear; lia).
  replace (K_FREEARR_MAX <? new) with false by (symmetry; apply Z.ltb_ge; unfold K_FREEARR_MAX; clear -KC; lia).
  cbv iota. unfold ev. rewrite aembed_vis. cbn [aev_tree]. unfold PROT_RW, F_FIXED.
  unfold region_beg, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296. rewrite SBE. fold mfa.
  chg (al_space_beg L + c * 4294967296 + 3758096384 + mfa) FAM.
  assert (FAM8 : FAM mod 4096 = 0 /\ 0x10007fff8000 <= FAM /\ FAM + (new - mfa) <= al_space_beg L + 137438953472 /\ (new - mfa) mod 4096 = 0 /\ 0 < new - mfa).
  { subst FAM. clear -SP1 SP3 HC MFA MFAM KE' RU1 RU2 KC NF. Z.div_mod_to_equations. lia. }
  (nd_pre FAM8 5%nat; intros FA1 FA2 FA3 FA4 FA5; nd_post).
  assert (FA0 : al_space_beg L + 4096 <= FAM) by (unfold FAM; clear -HC MFA; lia).
  name_sp sp (-48).
  eapply rmap_spec with (addr := FAM) (size := new - mfa) (lo := lo).
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite Hsp; eassumption
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- rmap_cells _ => eapply m3_cells_frame_rc; [exact MC | exact MU | exact WM | apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX1; unfold AIMG_HI, AIMG_LO; lia | apply Forall_nil]]
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => reflexivity
       | |- _ mod 4096 = 0 => assumption
       | |- 0 < _ - _ => exact FA5
       end.
  all: try (unfold AIMG_HI; clear -FA1 FA2 FA3 FA4 FA5 SP2 CEIL LO; rewrite ?unsigned_lit by lia; lia).
  { (* [comment removed for export] *)
    intros a RNG' ms' NE P1 P2. unfold fixed_answer_ok, is_err, TWO64.
    replace (2 ^ 64 - 4096 <? a) with false by (symmetry; apply Z.ltb_ge; clear -P2 FA5; atop_facts; lia).
    replace (a =? FAM) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [negb orb]. rewrite aembed_aundef_. apply implF_ret_unr. }
  (* [comment removed for export] *)
  intros RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RP.
  (nd_pre RP 11%nat; intros FPLE _ MU2 WM2 MI2 ST2 ZNEW GR1 GR2 BW RC2; nd_post). unname_sp.
  (* [comment removed for export] *)
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RTLS. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI.
  (* [comment removed for export] *)
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO FA2 FA3 SP2; lia).
  xport REG MU2 WM2 ltac:(clear -SPR CEIL LO FA2 FA3 SP2 HC; lia).
  xport STATS MU2 WM2 ltac:(rewrite LSJ; ub TSP; clear -SPR CEIL LO FA0 FA2 FA3 SP2 T0 T1 Y; lia).
  clear ST. rename ST2 into ST.
  assert (AZ2 : azero m2 (shad FAM) (shlen (536870912 - mfa))).
  { eapply azero_frame; [eapply azero_frame; [exact AZ | exact MU | exact WM |] | exact MU2 | exact WM2 |];
      intros _; cbn [disjoint_from]; subst FAM; rewrite ?shad_div, ?shlen_div; unfold ASHOFF;
      clear -SPR CEIL LO SP1 SP2 HC MFA KC RU1 KE'; Z.div_mod_to_equations; lia. }
  assert (MUF : munch [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp); (FAM, FAM + (new - mfa)); (shad FAM, shad FAM + shlen (new - mfa));
                       (al_t L + 2800, al_t L + 3168); (al_space_beg L + 137438953472 + c * 128 + 24, al_space_beg L + 137438953472 + c * 128 + 32)]%Z m m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
  clear MU MU2. pose proof (wmono_trans _ _ _ _ WM WM2) as WMF. clear WM WM2.
  assert (WOK : Forall (fun iv => ((AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= ATPv + -88 \/ ATPv + -80 <= fst iv)) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv))
           [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp); (FAM, FAM + (new - mfa)); (shad FAM, shad FAM + shlen (new - mfa));
            (al_t L + 2800, al_t L + 3168); (al_space_beg L + 137438953472 + c * 128 + 24, al_space_beg L + 137438953472 + c * 128 + 32)]%Z).
  { ub TCX. ub SCX. unfold AIMG_HI, AIMG_LO.
    do 5 (apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX0 CX1 T0 T1 TIC SP1 SP2 HC MFA FA0 FA2 FA3 KC Y Y0;
                              with_band CX0 ltac:(rewrite ?shad_div, ?shlen_div; unfold ASHOFF; split; Z.div_mod_to_equations; lia) |]). apply Forall_nil. }   (* [comment removed for export] *)
  pose proof (m3_cells_frame L m m2 _ MC MUF WMF WOK) as MC2.
  clear TI TK T88 TSD CT ISB IREL ISE IPRE.
  pose proof MC2 as MC2'. (nd_pre MC2' 11%nat; intros PC2 _ TI TK T88 TSD CT ISB IREL ISE IPRE; nd_post). unfold ATP88, ATSD in T88, TSD.
  (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 224428)) with (Z_to_bv 64 224428 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 FA2 FA3 SP2. rewrite ?unsigned_lit in K1 by lia. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. }                                                (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  pose proof (azero_cb m2 _ _ (shlen (new - mfa)) AZ2 ltac:(rewrite !shlen_div; clear -MFA KC KE' RU1; Z.div_mod_to_equations; lia)) as SHCB.
  clear AZ2.
  assert (SHF : 0x2008fff7000 <= shad FAM /\ shad FAM + shlen (new - mfa) <= 0x10007fff8000 /\ 0 < shlen (new - mfa)).
  { rewrite shad_div, shlen_div. unfold ASHOFF. clear -FA2 FA3 FA4 FA5 SP2. Z.div_mod_to_equations. lia. }
  (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
  step. (nd_pre (sclr_int _ _ CX0 ltac:(clear -CXI; lia) ltac:(clear -CX1; lia)) 4%nat; intros kC9 CB9 CB9a CB9b; nd_post). (nd_pre (sclr_int _ _ T0 ltac:(clear -TIC; lia) ltac:(clear -T1; lia)) 4%nat; intros kT9 TB9 TB9a TB9b; nd_post).   (* [comment removed for export] *)
  call_sp (poison_shadow_spec RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FAM (new - mfa) 250 lo).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => first [assumption | unfold ablk; right; clear -FA2 FA3 SP2; lia]   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => exact PC2
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => exact SHCB
       | |- rng _ (shad _) _ => exact GR2
       | |- rng _ _ _ => solve_rng
       end.
  all: try (atop_facts; clear -FA1 FA2 FA3 FA4 FA5 SP2 CEIL LO KC RU1 KE' MFA; rewrite ?shlen_div; first [lia | Z.div_mod_to_equations; lia]).
  all: try clear kC9 CB9 CB9a CB9b kT9 TB9 TB9a TB9b.
  (* [comment removed for export] *)
  step. (nd_pre (sclr_int _ _ T0 ltac:(clear -TIC; lia) ltac:(clear -T1; lia)) 4%nat; intros kT9 TB9 TB9a TB9b; nd_post).   (* [comment removed for export] *)
  call_sp (thread_stats_spec RNG' (al_ctx L) (al_t L) lo).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ _ _ => assumption
       | |- rng _ _ _ => solve_rng
       end.
  all: try (unfold AIMG_HI; clear -CEIL LO CX0 CX1 T0 T1 CXI TIC; lia).
  all: match goal with |- ?G => idtac "REMT" G end.
  all: try clear kT9 TB9 TB9a TB9b.
  aload STATS 10 (al_t L + 2800 + 80). aload STATS 9 (al_t L + 2800 + 72).
  zstep. zstep.                                                (* [comment removed for export] *)
  snapshot [(al_t L + 2800, al_t L + 3168)]%Z MUs WMs.
  box CT. box ZNEW. box REG.
  lazymatch goal with P : rw_cells asegs _ (shad FAM) _ |- _ => rename P into SHPO end. box SHPO.   (* [comment removed for export] *)
  astore STATS 9. astore STATS 10.
  carry SHPO MUs WMs ltac:(with_band T0 ltac:(lia)).
  carry REG MUs WMs ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 Y; lia).
  carry CT MUs WMs ltac:(ub TCX; clear -HC CX0 CX1 T0 T1 Y; lia).
  carry ZNEW MUs WMs ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 FA0 FA2 FA3 FA5 Y; lia).
  clear MUs WMs.
  snapshot [(al_space_beg L + 137438953472 + c * 128 + 24, al_space_beg L + 137438953472 + c * 128 + 32)]%Z MUr WMr.
  box CT. box ZNEW. box STATS.
  step. step.                                                  (* [comment removed for export] *)
  carry CT MUr WMr ltac:(ub SCX; clear -HC CX0 CX1 SP1 SP2 Y; lia).
  carry ZNEW MUr WMr ltac:(clear -HC SP1 SP2 FA0 FA2 FA3 FA5; lia).
  carry STATS MUr WMr ltac:(rewrite ?upd_length, LSJ; ub TSP; clear -HC T0 T1 SP1 SP2 Y; lia).
  clear MUr WMr.
  step. step.                                                  (* [comment removed for export] *)
  step. step. step. step. step. step. step.                    (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -48) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done.
  unfold fixed_answer_ok, is_err, TWO64. rewrite Z.eqb_refl.
  replace (2 ^ 64 - 4096 <? FAM) with false by (symmetry; apply Z.ltb_ge; clear -FA3 FA5 SP2; lia). cbn [negb orb].
  eapply KONT. unfold ensure_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold mfa. split; [exact FPLE|].
  lazymatch goal with |- context [u64arr asegs _ _ ?ws] => idtac | H : u64arr asegs _ (al_t L + 2800) ?ws |- _ => exists new, ws end.
  rewrite FAE, RIE. fold FAM.
  split. { right. split; [exact KE'|]. split; [subst new; f_equal; clear; lia|]. split; [reflexivity|].
           split; [exact ZNEW|]. split; [assumption|]. split; [exact GR1|]. split; [exact GR2| exact BW]. }
  split; [clear -RU1 KC; lia|]. split; [clear -RU1 KE'; lia|]. split; [exact RU2|].
  split. { eapply munch_weaken; [| exact MUF]. unfold sub_fp, FAM. cbn [outside]. clear. intros x Hx. lia. }
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [assumption|]. split; [assumption|]. split; [rewrite ?upd_length; exact LSJ|].
  split.
  { pose proof (azero_split m _ _ (shlen (new - mfa)) AZ ltac:(rewrite !shlen_div; clear -MFA KC KE' RU1; Z.div_mod_to_equations; lia)) as AZT.
    replace (shad FAM + shlen (new - mfa)) with (shad (FAM + (new - mfa))) in AZT by (apply shad_add_shlen; clear -FA1; Z.div_mod_to_equations; lia).
    replace (shlen (536870912 - mfa) - shlen (new - mfa)) with (shlen (536870912 - new)) in AZT by (rewrite !shlen_div; clear -FA4 MFAM RU2 MFA; Z.div_mod_to_equations; lia).
    replace (al_space_beg L + c * 4294967296 + 3758096384 + new) with (FAM + (new - mfa)) by (unfold FAM; clear; lia).
    eapply azero_frame; [exact AZT | exact MUF | exact WMF |]. intros Hp. cbn [disjoint_from].
    pose proof (shad_add_shlen FAM (new - mfa) ltac:(clear -FA1; Z.div_mod_to_equations; lia)) as SE.
    assert (SHT : shad (FAM + (new - mfa)) + shlen (536870912 - new) <= 0x10007fff8000).
    { rewrite shad_div, shlen_div. unfold ASHOFF, FAM. clear -SP2 KC RU1 MFA HC KE'. Z.div_mod_to_equations. lia. }
    clear -SE SHT SHF1 SHF2 SHF3 CEIL LO FA2 FA3 FA5 T0 SP1 SP2 HC. with_band T0 ltac:(repeat split; lia). }   (* [comment removed for export] *)
  eapply m3_cells_frame; [exact MC | eassumption | eassumption | exact WOK].
Qed.
End Zd1.
#[using="Type"] Lemma ensure_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c nf lo : Z) (sj : list word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ENSURE_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 RI -> a2 = Z_to_bv 64 (aregion L c) -> a3 = Z_to_bv 64 nf ->
  m3_cells L m ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 (c_num_freed r)); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 0 <= nf -> 4 * nf <= K_FREEARR_MAX ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      ensure_ret L RNG sp st c nf lo sj m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (k st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (ensure_free_array st c nf k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ensure_entry) fc None m (seg_rom asegs)).
Proof. exact ensure_spec__body. Qed.
End CANSEC2.
End TwB.
End F_aensure.

(* [comment removed for export] *)
Module F_amaybe.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation MAYBE_STACK := 80 (only parsing).
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition maybe_entry : Z := 0x36d24.

Definition maybe_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - MAYBE_STACK, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition maybe_release_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (c lo nf mfa au mu : Z) (w80 w88 : word),
  let RI := aregion_info L c in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - MAYBE_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 0 ->
  m3_cells L m ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 80) [C8 w80] -> rw_cells asegs m (RI + 88) [C8 w88] ->
  1 <= c < K_NUM_CLASSES ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG RI 128 ->
  evtF asegs RNG (maybe_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 maybe_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 34).
Variable L : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 35).
Variable c : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 36).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 37).
Variable nf : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 38).
Variable mfa : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 39).
Variable au : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 40).
Variable mu : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 41).
Variable w80 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 42).
Variable w88 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 43).
#[using="Type"] Lemma maybe_release_spec__body : ltac:(let T := type of (fun (h : maybe_release_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L c lo nf mfa au mu w80 w88) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (L, (c, (lo, (nf, (mfa, (au, (mu, (w80, w88)))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI -> -> -> MC REG R80 R88 HC SP1 SP2 RIMG RTLS RSTK RRI.
  pose proof MC as MC0. (nd_pre MC0 11%nat; intros _ RC _ _ _ _ _ ISB IREL ISE IPRE; nd_post).
  pose proof RC as RC0. (nd_pre RC0 3%nat; intros GPG PGSZ _; nd_post). clear MC RC ISB IPRE.
  unfold AINSTANCE, K_NUM_CLASSES, K_SPACE_SIZE, K_SPACE_EXTRA, maybe_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128)
    by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 80%nat ST.
  do 10 step.                                                  (* [comment removed for export] *)
  do 4 step.                                                   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. zstep.                                                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac tail RIE SP1 SP2 HC :=
    step; step; step;                                          (* [comment removed for export] *)
    zstep;                                                     (* [comment removed for export] *)
    lazymatch type of RIE with ?ri = _ =>
      setreg 22%Z (Z_to_bv 64 ri) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia)
    end;
    step; if_lit;                                              (* [comment removed for export] *)
    step;                                                      (* [comment removed for export] *)
    zstep;                                                     (* [comment removed for export] *)
    step;
    let K1 := fresh "K" in
    if_cases K1;
    [ (* [comment removed for export] *)
      step; step; zstep; zstep;                                (* [comment removed for export] *)
      step;
      let K2 := fresh "K" in
      if_cases K2;
      [ do 11 step                                             (* [comment removed for export] *)
      | step; if_lit;                                          (* [comment removed for export] *)
        step;                                                  (* [comment removed for export] *)
        step; if_lit;                                          (* [comment removed for export] *)
        do 11 step ]
    | do 12 step ].                                            (* [comment removed for export] *)
  step. if_cases K31; zify_cond K31.
  - (* [comment removed for export] *)
    step. step.                                                (* [comment removed for export] *)
    tail RIE SP1 SP2 HC.
    all: release_frame FR ST (bv_unsigned sp); unfold maybe_post; finish.
  - step.                                                      (* [comment removed for export] *)
    step. if_cases K16; zify_cond K16.
    + (* [comment removed for export] *)
      do 9 zstep.
      tail RIE SP1 SP2 HC.
      all: release_frame FR ST (bv_unsigned sp); unfold maybe_post; finish.
    + zstep. step.                                             (* [comment removed for export] *)
      tail RIE SP1 SP2 HC.
      all: release_frame FR ST (bv_unsigned sp); unfold maybe_post; finish.
Qed.
End Zd1.
#[using="Type"] Lemma maybe_release_spec : ltac:(let t := eval cbv delta [maybe_release_spec__stmt] in maybe_release_spec__stmt in exact t).
Proof. exact maybe_release_spec__body. Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation MAYBE_STACK := 80 (only parsing).
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition maybe_entry : Z := 0x36d8c.

Definition maybe_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - MAYBE_STACK, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition maybe_release_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (c lo nf mfa au mu : Z) (w80 w88 : word),
  let RI := aregion_info L c in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - MAYBE_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 0 ->
  m3_cells L m ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 80) [C8 w80] -> rw_cells asegs m (RI + 88) [C8 w88] ->
  1 <= c < K_NUM_CLASSES ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG RI 128 ->
  evtF asegs RNG (maybe_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 maybe_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 34).
Variable L : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 35).
Variable c : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 36).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 37).
Variable nf : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 38).
Variable mfa : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 39).
Variable au : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 40).
Variable mu : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 41).
Variable w80 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 42).
Variable w88 : ltac2:(SecDietF.SzSecF.ty 'maybe_release_spec__stmt 43).
#[using="Type"] Lemma maybe_release_spec__body : ltac:(let T := type of (fun (h : maybe_release_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L c lo nf mfa au mu w80 w88) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (L, (c, (lo, (nf, (mfa, (au, (mu, (w80, w88)))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI -> -> -> MC REG R80 R88 HC SP1 SP2 RIMG RTLS RSTK RRI.
  pose proof MC as MC0. (nd_pre MC0 11%nat; intros _ RC _ _ _ _ _ ISB IREL ISE IPRE; nd_post).
  pose proof RC as RC0. (nd_pre RC0 3%nat; intros GPG PGSZ _; nd_post). clear MC RC ISB IPRE.
  unfold AINSTANCE, K_NUM_CLASSES, K_SPACE_SIZE, K_SPACE_EXTRA, maybe_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128)
    by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 80%nat ST.
  do 10 step.                                                  (* [comment removed for export] *)
  do 4 step.                                                   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. zstep.                                                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac tail RIE SP1 SP2 HC :=
    step; step; step;                                          (* [comment removed for export] *)
    zstep;                                                     (* [comment removed for export] *)
    lazymatch type of RIE with ?ri = _ =>
      setreg 22%Z (Z_to_bv 64 ri) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia)
    end;
    step; if_lit;                                              (* [comment removed for export] *)
    step;                                                      (* [comment removed for export] *)
    zstep;                                                     (* [comment removed for export] *)
    step;
    let K1 := fresh "K" in
    if_cases K1;
    [ (* [comment removed for export] *)
      step; step; zstep; zstep;                                (* [comment removed for export] *)
      step;
      let K2 := fresh "K" in
      if_cases K2;
      [ do 11 step                                             (* [comment removed for export] *)
      | step; if_lit;                                          (* [comment removed for export] *)
        step;                                                  (* [comment removed for export] *)
        step; if_lit;                                          (* [comment removed for export] *)
        do 11 step ]
    | do 12 step ].                                            (* [comment removed for export] *)
  step. if_cases K31; zify_cond K31.
  - (* [comment removed for export] *)
    step. step.                                                (* [comment removed for export] *)
    tail RIE SP1 SP2 HC.
    all: release_frame FR ST (bv_unsigned sp); unfold maybe_post; finish.
  - step.                                                      (* [comment removed for export] *)
    step. if_cases K16; zify_cond K16.
    + (* [comment removed for export] *)
      do 9 zstep.
      tail RIE SP1 SP2 HC.
      all: release_frame FR ST (bv_unsigned sp); unfold maybe_post; finish.
    + zstep. step.                                             (* [comment removed for export] *)
      tail RIE SP1 SP2 HC.
      all: release_frame FR ST (bv_unsigned sp); unfold maybe_post; finish.
Qed.
End Zd1.
#[using="Type"] Lemma maybe_release_spec : ltac:(let t := eval cbv delta [maybe_release_spec__stmt] in maybe_release_spec__stmt in exact t).
Proof. exact maybe_release_spec__body. Qed.
End CANSEC1.
End TwB.
End F_amaybe.
