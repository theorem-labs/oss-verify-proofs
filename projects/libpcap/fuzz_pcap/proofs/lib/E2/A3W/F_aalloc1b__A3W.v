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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepotKit__A3W.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFakeProbe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_aalloc1b.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition allocA_pre_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x33ea8) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x38388) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 128)
    /\ (exists j0, rw_cells asegs m' (bv_unsigned sp - 128)
         [CB 8 j0 (* [comment removed for export] *); C8 (Z_to_bv 64 1) (* [comment removed for export] *); C8 (Z_to_bv 64 16) (* [comment removed for export] *);
          C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

Definition allocA_pre_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S ctx t lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 176 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n -> is_primary n = true -> 0 < S < 2^64 ->
  allocA_cells m ctx t ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (allocA_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n S t lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 34).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 35).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 36).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 37).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 39).
#[using="Type"] Lemma allocA_pre_spec__body : ltac:(let T := type of (fun (h : allocA_pre_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n S ctx t lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (S, (ctx, (t, lo)))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI TP -> -> -> -> -> -> N PRIM0 HS AC C0 C1 T0 T1 TAL CT2 RIMG RTLS RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  (nd_pre AC 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, AINITED, ATSDI, ATSDK, ATP88, ATSD, ARSSLIM, allocate_entry in *.
  (pose proof (prim_facts n N PRIM0) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR0 RSR RSM NSR; nd_post).
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 128%nat ST.
  do 14 step.                                       (* [comment removed for export] *)
  do 6 step.                                        (* [comment removed for export] *)
  step. callp asan_inited_spec; [exact INI|]. step. if_lit.     (* [comment removed for export] *)
  step. callp rss_spec; [exact RSS|]. step. if_lit.             (* [comment removed for export] *)
  step. if_cases KS; zify_cond KS. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. step. if_lit.                                      (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                    (* [comment removed for export] *)
  step. step. zstep. zstep. zstep. step. zstep. zstep. zstep.    (* [comment removed for export] *)
  lstep. zstep. zstep. zstep.                               (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. zstep. zstep. step. if_lit.                              (* [comment removed for export] *)
  step. zstep. step. step.                                       (* [comment removed for export] *)
  callp rz_ladder_spec; [lia|].                                  (* [comment removed for export] *)
  lstep. step. step. zstep. zstep.                        (* [comment removed for export] *)
  step. call_sp rz2log16_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  step. lstep. step. zstep.                                      (* [comment removed for export] *)
  step. call_sp rz2log2048_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  callp rz_clamp_spec; [lia| exact RLR0 |].   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.        (* [comment removed for export] *)
  change ((Z.b2z (8 <? 9) + -1) mod 18446744073709551616) with 0. rewrite Z.land_0_l, Z.add_0_r.
  rewrite land_align8 by lia.
  setreg 10 (Z_to_bv 64 (rounded_size n)) ltac:(f_equal; rewrite rounded_size_align; lia).
  zstep. step. if_cases KA; zify_cond KA. { exfalso. apply KA. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. exact RSM. }   (* [comment removed for export] *)
  step. zstep.                                                   (* [comment removed for export] *)
  replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  zstep. zstep.                                                  (* [comment removed for export] *)
  first [rewrite (sllw_rz_gen2 n) | rewrite (sllw_rz_gen n)].   (* [comment removed for export] *)
  step. zstep.                                                   (* [comment removed for export] *)
  zstep. replace (8 <? 65537) with true by reflexivity. cbn [Z.b2z].   (* [comment removed for export] *)
  zstep.                                                         (* [comment removed for export] *)
  rewrite <- NS.
  zstep. zstep. zstep. zstep. step. zstep.                       (* [comment removed for export] *)
  replace (needed_size n <? 65537) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  change ((Z.land 1 1 + -1) mod 18446744073709551616) with 0. change (Z.land 1 1) with 1. rewrite Z.land_0_l, Z.add_0_l.
  step. if_cases KB; zify_cond KB. { exfalso. lia. }            (* [comment removed for export] *)
  step. if_cases KC; zify_cond KC. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_cases KD; zify_cond KD. 2: { exfalso. lia. }   (* [comment removed for export] *)
  box RT.
  step. call_sp get_current_thread_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  unbox RT. rename POST into ST.
  step. step. if_cases KE; zify_cond KE. { exfalso. lia. }      (* [comment removed for export] *)
  zstep. step. step. step.                                       (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  apply evtF_done. unfold allocA_pre_post. do 12 eexists. split; [reflexivity|].
  repeat lazymatch goal with |- _ /\ _ => split end.
  all: try assumption. all: eexists; eassumption.
Qed.
End Zd1.
#[using="Type"] Lemma allocA_pre_spec : ltac:(let t := eval cbv delta [allocA_pre_spec__stmt] in allocA_pre_spec__stmt in exact t).
Proof. exact allocA_pre_spec__body. Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition allocA_pre_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x33f10) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x383f0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 128)
    /\ (exists j0, rw_cells asegs m' (bv_unsigned sp - 128)
         [CB 8 j0 (* [comment removed for export] *); C8 (Z_to_bv 64 1) (* [comment removed for export] *); C8 (Z_to_bv 64 16) (* [comment removed for export] *);
          C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

Definition allocA_pre_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S ctx t lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 176 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n -> is_primary n = true -> 0 < S < 2^64 ->
  allocA_cells m ctx t ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (allocA_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n S t lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 34).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 35).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 36).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 37).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec__stmt 39).
#[using="Type"] Lemma allocA_pre_spec__body : ltac:(let T := type of (fun (h : allocA_pre_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n S ctx t lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (S, (ctx, (t, lo)))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI TP -> -> -> -> -> -> N PRIM0 HS AC C0 C1 T0 T1 TAL CT2 RIMG RTLS RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  (nd_pre AC 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, AINITED, ATSDI, ATSDK, ATP88, ATSD, ARSSLIM, allocate_entry in *.
  (pose proof (prim_facts n N PRIM0) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR0 RSR RSM NSR; nd_post).
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 128%nat ST.
  do 14 step.                                       (* [comment removed for export] *)
  do 6 step.                                        (* [comment removed for export] *)
  step. callp asan_inited_spec; [exact INI|]. step. if_lit.     (* [comment removed for export] *)
  step. callp rss_spec; [exact RSS|]. step. if_lit.             (* [comment removed for export] *)
  step. if_cases KS; zify_cond KS. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. step. if_lit.                                      (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                    (* [comment removed for export] *)
  step. step. zstep. zstep. zstep. step. zstep. zstep. zstep.    (* [comment removed for export] *)
  lstep. zstep. zstep. zstep.                               (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. zstep. zstep. step. if_lit.                              (* [comment removed for export] *)
  step. zstep. step. step.                                       (* [comment removed for export] *)
  callp rz_ladder_spec; [lia|].                                  (* [comment removed for export] *)
  lstep. step. step. zstep. zstep.                        (* [comment removed for export] *)
  step. call_sp rz2log16_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  step. lstep. step. zstep.                                      (* [comment removed for export] *)
  step. call_sp rz2log2048_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  callp rz_clamp_spec; [lia| exact RLR0 |].   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.        (* [comment removed for export] *)
  change ((Z.b2z (8 <? 9) + -1) mod 18446744073709551616) with 0. rewrite Z.land_0_l, Z.add_0_r.
  rewrite land_align8 by lia.
  setreg 10 (Z_to_bv 64 (rounded_size n)) ltac:(f_equal; rewrite rounded_size_align; lia).
  zstep. step. if_cases KA; zify_cond KA. { exfalso. apply KA. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. exact RSM. }   (* [comment removed for export] *)
  step. zstep.                                                   (* [comment removed for export] *)
  replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  zstep. zstep.                                                  (* [comment removed for export] *)
  first [rewrite (sllw_rz_gen2 n) | rewrite (sllw_rz_gen n)].   (* [comment removed for export] *)
  step. zstep.                                                   (* [comment removed for export] *)
  zstep. replace (8 <? 65537) with true by reflexivity. cbn [Z.b2z].   (* [comment removed for export] *)
  zstep.                                                         (* [comment removed for export] *)
  rewrite <- NS.
  zstep. zstep. zstep. zstep. step. zstep.                       (* [comment removed for export] *)
  replace (needed_size n <? 65537) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  change ((Z.land 1 1 + -1) mod 18446744073709551616) with 0. change (Z.land 1 1) with 1. rewrite Z.land_0_l, Z.add_0_l.
  step. if_cases KB; zify_cond KB. { exfalso. lia. }            (* [comment removed for export] *)
  step. if_cases KC; zify_cond KC. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_cases KD; zify_cond KD. 2: { exfalso. lia. }   (* [comment removed for export] *)
  box RT.
  step. call_sp get_current_thread_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  unbox RT. rename POST into ST.
  step. step. if_cases KE; zify_cond KE. { exfalso. lia. }      (* [comment removed for export] *)
  zstep. step. step. step.                                       (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  apply evtF_done. unfold allocA_pre_post. do 12 eexists. split; [reflexivity|].
  repeat lazymatch goal with |- _ /\ _ => split end.
  all: try assumption. all: eexists; eassumption.
Qed.
End Zd1.
#[using="Type"] Lemma allocA_pre_spec : ltac:(let t := eval cbv delta [allocA_pre_spec__stmt] in allocA_pre_spec__stmt in exact t).
Proof. exact allocA_pre_spec__body. Qed.
End CANSEC1.
End TwB.
End F_aalloc1b.

(* [comment removed for export] *)
Module F_aalloc1s.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aalloc1b.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition allocA_pre_postS (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x33ea8) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 0) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x38388) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 128)
    /\ (exists j0, rw_cells asegs m' (bv_unsigned sp - 128)
         [CB 8 j0 (* [comment removed for export] *); C8 (Z_to_bv 64 1) (* [comment removed for export] *); C8 (Z_to_bv 64 16) (* [comment removed for export] *);
          C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

Definition allocA_pre_spec_sec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S ctx t lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 176 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= AREQMAX -> is_primary n = false -> 0 < S < 2^64 ->
  allocA_cells m ctx t ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (allocA_pre_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n S t lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 34).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 35).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 36).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 37).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 39).
#[using="Type"] Lemma allocA_pre_spec_sec__body : ltac:(let T := type of (fun (h : allocA_pre_spec_sec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n S ctx t lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (S, (ctx, (t, lo)))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI TP -> -> -> -> -> -> N PRIM0 HS AC C0 C1 T0 T1 TAL CT2 RIMG RTLS RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  (nd_pre AC 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, AINITED, ATSDI, ATSDK, ATP88, ATSD, ARSSLIM, AREQMAX, allocate_entry in *.
  (pose proof (sec_facts n ltac:(unfold AREQMAX; lia) PRIM0) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post).
  pose proof (rz_log_big n NB) as RL7. assert (RLR0 : 0 <= rz_log n <= 7) by (rewrite RL7; lia).
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 128%nat ST.
  do 14 step.                                       (* [comment removed for export] *)
  do 6 step.                                        (* [comment removed for export] *)
  step. callp asan_inited_spec; [exact INI|]. step. if_lit.     (* [comment removed for export] *)
  step. callp rss_spec; [exact RSS|]. step. if_lit.             (* [comment removed for export] *)
  step. if_cases KS; zify_cond KS. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. step. if_lit.                                      (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                    (* [comment removed for export] *)
  step. step. zstep. zstep. zstep. step. zstep. zstep. zstep.    (* [comment removed for export] *)
  lstep. zstep. zstep. zstep.                               (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. zstep. zstep. step. if_lit.                              (* [comment removed for export] *)
  step. zstep. step. step.                                       (* [comment removed for export] *)
  callp rz_ladder_spec; [lia|].                                  (* [comment removed for export] *)
  lstep. step. step. zstep. zstep.                        (* [comment removed for export] *)
  step. call_sp rz2log16_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  step. lstep. step. zstep.                                      (* [comment removed for export] *)
  step. call_sp rz2log2048_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  callp rz_clamp_spec; [lia| exact RLR0 |].   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.        (* [comment removed for export] *)
  change ((Z.b2z (8 <? 9) + -1) mod 18446744073709551616) with 0. rewrite Z.land_0_l, Z.add_0_r.
  rewrite land_align8 by lia.
  setreg 10 (Z_to_bv 64 (rounded_size n)) ltac:(f_equal; rewrite rounded_size_align; lia).
  zstep. step. if_cases KA; zify_cond KA. { exfalso. apply KA. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. exact RSM. }   (* [comment removed for export] *)
  step. zstep.                                                   (* [comment removed for export] *)
  replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  zstep. zstep.                                                  (* [comment removed for export] *)
  first [rewrite (sllw_rz_gen2 n) | rewrite (sllw_rz_gen n)].   (* [comment removed for export] *)
  step. zstep.                                                   (* [comment removed for export] *)
  zstep. replace (8 <? 65537) with true by reflexivity. cbn [Z.b2z].   (* [comment removed for export] *)
  zstep.                                                         (* [comment removed for export] *)
  rewrite RZ.
  zstep. zstep. zstep. zstep. step. zstep.                       (* [comment removed for export] *)
  replace (rounded_size n + 2048 <? 65537) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  change (Z.land 1 0) with 0. change ((0 + -1) mod 18446744073709551616) with 18446744073709551615.
  change (Z.land 18446744073709551615 2048) with 2048.
  setreg 19 (Z_to_bv 64 (needed_size n)) ltac:(f_equal; lia). setreg 20 (Z_to_bv 64 (rz_size n)) ltac:(f_equal; lia).
  step. if_cases KB; zify_cond KB. { exfalso. lia. }            (* [comment removed for export] *)
  step. if_cases KC; zify_cond KC. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_cases KD; zify_cond KD. 2: { exfalso. lia. }   (* [comment removed for export] *)
  box RT.
  step. call_sp get_current_thread_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  unbox RT. rename POST into ST.
  step. step. if_cases KE; zify_cond KE. { exfalso. lia. }      (* [comment removed for export] *)
  zstep. step. step. step.                                       (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  apply evtF_done. unfold allocA_pre_postS. do 12 eexists. split; [reflexivity|].
  repeat lazymatch goal with |- _ /\ _ => split end.
  all: try assumption. all: eexists; eassumption.
Qed.
End Zd1.
#[using="Type"] Lemma allocA_pre_spec_sec : ltac:(let t := eval cbv delta [allocA_pre_spec_sec__stmt] in allocA_pre_spec_sec__stmt in exact t).
Proof. exact allocA_pre_spec_sec__body. Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aalloc1b.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition allocA_pre_postS (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x33f10) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 0) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x383f0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 128)
    /\ (exists j0, rw_cells asegs m' (bv_unsigned sp - 128)
         [CB 8 j0 (* [comment removed for export] *); C8 (Z_to_bv 64 1) (* [comment removed for export] *); C8 (Z_to_bv 64 16) (* [comment removed for export] *);
          C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

Definition allocA_pre_spec_sec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S ctx t lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 176 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= AREQMAX -> is_primary n = false -> 0 < S < 2^64 ->
  allocA_cells m ctx t ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (allocA_pre_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n S t lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 34).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 35).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 36).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 37).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocA_pre_spec_sec__stmt 39).
#[using="Type"] Lemma allocA_pre_spec_sec__body : ltac:(let T := type of (fun (h : allocA_pre_spec_sec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n S ctx t lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (S, (ctx, (t, lo)))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI TP -> -> -> -> -> -> N PRIM0 HS AC C0 C1 T0 T1 TAL CT2 RIMG RTLS RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  (nd_pre AC 8%nat; intros INI RSS IMAX TI TK T88 TSD CT; nd_post).
  unfold AIMG_HI, AINSTANCE, AINITED, ATSDI, ATSDK, ATP88, ATSD, ARSSLIM, AREQMAX, allocate_entry in *.
  (pose proof (sec_facts n ltac:(unfold AREQMAX; lia) PRIM0) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post).
  pose proof (rz_log_big n NB) as RL7. assert (RLR0 : 0 <= rz_log n <= 7) by (rewrite RL7; lia).
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 128%nat ST.
  do 14 step.                                       (* [comment removed for export] *)
  do 6 step.                                        (* [comment removed for export] *)
  step. callp asan_inited_spec; [exact INI|]. step. if_lit.     (* [comment removed for export] *)
  step. callp rss_spec; [exact RSS|]. step. if_lit.             (* [comment removed for export] *)
  step. if_cases KS; zify_cond KS. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. step. if_lit.                                      (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                    (* [comment removed for export] *)
  step. step. zstep. zstep. zstep. step. zstep. zstep. zstep.    (* [comment removed for export] *)
  lstep. zstep. zstep. zstep.                               (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. zstep. zstep. step. if_lit.                              (* [comment removed for export] *)
  step. zstep. step. step.                                       (* [comment removed for export] *)
  callp rz_ladder_spec; [lia|].                                  (* [comment removed for export] *)
  lstep. step. step. zstep. zstep.                        (* [comment removed for export] *)
  step. call_sp rz2log16_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  step. lstep. step. zstep.                                      (* [comment removed for export] *)
  step. call_sp rz2log2048_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  callp rz_clamp_spec; [lia| exact RLR0 |].   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.        (* [comment removed for export] *)
  change ((Z.b2z (8 <? 9) + -1) mod 18446744073709551616) with 0. rewrite Z.land_0_l, Z.add_0_r.
  rewrite land_align8 by lia.
  setreg 10 (Z_to_bv 64 (rounded_size n)) ltac:(f_equal; rewrite rounded_size_align; lia).
  zstep. step. if_cases KA; zify_cond KA. { exfalso. apply KA. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. exact RSM. }   (* [comment removed for export] *)
  step. zstep.                                                   (* [comment removed for export] *)
  replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  zstep. zstep.                                                  (* [comment removed for export] *)
  first [rewrite (sllw_rz_gen2 n) | rewrite (sllw_rz_gen n)].   (* [comment removed for export] *)
  step. zstep.                                                   (* [comment removed for export] *)
  zstep. replace (8 <? 65537) with true by reflexivity. cbn [Z.b2z].   (* [comment removed for export] *)
  zstep.                                                         (* [comment removed for export] *)
  rewrite RZ.
  zstep. zstep. zstep. zstep. step. zstep.                       (* [comment removed for export] *)
  replace (rounded_size n + 2048 <? 65537) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  change (Z.land 1 0) with 0. change ((0 + -1) mod 18446744073709551616) with 18446744073709551615.
  change (Z.land 18446744073709551615 2048) with 2048.
  setreg 19 (Z_to_bv 64 (needed_size n)) ltac:(f_equal; lia). setreg 20 (Z_to_bv 64 (rz_size n)) ltac:(f_equal; lia).
  step. if_cases KB; zify_cond KB. { exfalso. lia. }            (* [comment removed for export] *)
  step. if_cases KC; zify_cond KC. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_cases KD; zify_cond KD. 2: { exfalso. lia. }   (* [comment removed for export] *)
  box RT.
  step. call_sp get_current_thread_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  unbox RT. rename POST into ST.
  step. step. if_cases KE; zify_cond KE. { exfalso. lia. }      (* [comment removed for export] *)
  zstep. step. step. step.                                       (* [comment removed for export] *)
  step.                                                          (* [comment removed for export] *)
  apply evtF_done. unfold allocA_pre_postS. do 12 eexists. split; [reflexivity|].
  repeat lazymatch goal with |- _ /\ _ => split end.
  all: try assumption. all: eexists; eassumption.
Qed.
End Zd1.
#[using="Type"] Lemma allocA_pre_spec_sec : ltac:(let t := eval cbv delta [allocA_pre_spec_sec__stmt] in allocA_pre_spec_sec__stmt in exact t).
Proof. exact allocA_pre_spec_sec__body. Qed.
End CANSEC1.
End TwB.
End F_aalloc1s.

(* [comment removed for export] *)
Module F_aunwind2.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepotKit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac alia_t1 := zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac solve_acc_with_t1 H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); alia_t1
      end
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz)); alia_t1
      end
  end.
Local Ltac acc_hint ::= lazymatch goal with |- acc_in ?RNG _ => match goal with H : rng RNG _ _ |- _ => solve_acc_with_t1 H end end.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Module RLF.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 head_may_be_arith (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h _ =>
        (match Constr.Unsafe.kind h with
         | Constr.Unsafe.Constant _ _ =>
             List.exist (fun r => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h r)
               [reference:(not); reference:(iff); reference:(Z.le); reference:(Z.lt); reference:(Z.ge); reference:(Z.gt);
                reference:(lt); reference:(ge); reference:(gt); reference:(N.le); reference:(N.lt); reference:(Z.divide)]
         | Constr.Unsafe.Ind _ _ =>
             List.exist (fun r => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h r) [reference:(and); reference:(or); reference:(eq); reference:(le)]
         | _ => true
         end)
    | _ => true
    end.
  Ltac2 is_local (id : ident) : bool := match Env.get [id] with None => true | Some _ => false end.
  (* [comment removed for export] *)
  Ltac2 meets_s (xs : ident list) (vs : ident FSet.t) : bool := List.exist (fun x => FSet.mem x vs) xs.
  Ltac2 add_all (s : ident FSet.t) (xs : ident list) : ident FSet.t := List.fold_left (fun s x => FSet.add x s) s xs.
  Ltac2 rec close_s (cand : (ident * ident list) list) (vs : ident FSet.t) (n : int) : ident FSet.t :=
    if Int.le n 0 then vs else
    let vs' := List.fold_left (fun acc c => let (_, hv) := c in if meets_s hv vs then add_all acc hv else acc) vs cand in
    if Int.equal (FSet.cardinal vs') (FSet.cardinal vs) then vs else close_s cand vs' (Int.sub n 1).
  Ltac2 drop_list (n : int) : ident list :=
    let cand := List.map_filter (fun h => let (id, body, ty) := h in
                  match body with
                  | Some _ => None
                  | None => if is_local id then (if head_may_be_arith ty then (if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.RL.arith ty then Some (id, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.RL.vars ty) else None) else None) else None
                  end) (Control.hyps ()) in
    let vs := close_s cand (add_all (FSet.empty FSet.Tags.ident_tag) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.RL.vars (Control.goal ()))) n in
    List.map_filter (fun c => let (id, hv) := c in if meets_s hv vs then None else Some id) cand.
  Ltac2 prune (nd : bool) (n : int) : unit :=
    let drop := drop_list n in
    match drop with [] => () | _ :: _ => Std.clear drop end;
    if Bool.neg nd then () else
    let disj := List.map_filter (fun h => let (id, body, ty) := h in
                  match body with
                  | Some _ => None
                  | None => if is_local id then (if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.RL.has_or ty then Some id else None) else None
                  end) (Control.hyps ()) in
    match disj with [] => () | _ :: _ => Std.clear disj end.
  Ltac2 prune2 () : unit := Control.enter (fun () => prune true 2).
  Ltac2 prune2d () : unit := Control.enter (fun () => prune false 2).
End RLF.
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.rl_prune ::= ltac2:(RLF.prune2 ()).
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.rl_prune_d ::= ltac2:(RLF.prune2d ()).
(* [comment removed for export] *)
Local Ltac solve_acc1 ::= solve_acc1_rl.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Notation unwind_impl_W sp S t :=
  ([(bv_unsigned sp - 160, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 2056); (S + 2056, S + 2064); (t + 3168, t + 3169)]%Z) (only parsing).

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma unwind_fast_spec0 : forall RNG (raf sp gp tp t0 t1 t2 s0f s1f a0 a1 a2 a3 a4 a5 a6 a7 s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (S pc bp top bot lo : Z) (tb : list word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= S ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 pc -> a2 = Z_to_bv 64 bp -> a3 = Z_to_bv 64 top -> a4 = Z_to_bv 64 bot -> a5 = Z_to_bv 64 30 ->
  rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (exists szj, rw_cells asegs m (S + 8) [C4 szj]) -> u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  0 <= bot -> bot < bp -> top - 16 <= bp -> bot < top -> 4096 <= top <= 2^47 -> bp < 2^47 -> S + 2072 <= bp -> 0 <= pc < 2^64 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bp - lo) ->
  evtF asegs RNG (unwind_fast_post S pc top sp raf s0f s1f s2f s3f s4f s5f s6f gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo tb [] m)
    (MS (mkR raf sp gp tp t0 t1 t2 s0f s1f a0 a1 a2 a3 a4 a5 a6 a7 s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x76f6c) fc None m (seg_rom asegs)).
Proof.
  intros until tb. intros ST CEIL LO SPS MI -> -> -> -> -> -> GPG PG [szj SZC] TB LTB B0 BB BT BT2 TOP BP47 SB PC RIMG RTLS RR.
  unfold GOT_PGSZ, APGSZ in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 2056)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 64%nat ST.
  do 9 step.                                   (* [comment removed for export] *)
  step. do 3 zstep.                            (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  do 3 step.                                   (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  step. zstep.                                 (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u64arr_store_ok asegs mm (S + 16) tb 0 (wa (S + 16)) TB ltac:(lia) ltac:(f_equal; lia)) as SOK end.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
    pose proof (u64arr_write asegs mm (S + 16) tb 0 (Z_to_bv 64 pc) TB ltac:(lia)) as TB2;
    rewrite Z.mul_0_r, Z.add_0_r in TB2 end.
  clear TB. store_done. rename TB2 into TB. cbn [Z.to_nat upd] in TB.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite Z.shiftr_div_pow2 in K0 by lia. Z.div_mod_to_equations. lia. }
  step. if_cases K1; zify_cond K1. { exfalso. lia. }     (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. lia. }     (* [comment removed for export] *)
  zstep. step. if_cases K3; zify_cond K3. 2: { exfalso. lia. }   (* [comment removed for export] *)
  do 10 step.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. unfold unwind_fast_post.
  do 6 eexists. eexists. exists (upd tb 0 (Z_to_bv 64 pc)). split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [cbn [length]; exact SZC|]. split; [exact TB|]. split; [rewrite upd_length; exact LTB|].
  destruct tb as [|w0 tb0]; [cbn in LTB; lia|]. cbn [upd firstn map length]. rewrite unsigned_lit by lia. reflexivity.
Qed.

Definition unwind_impl_spec0__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (S pc bp ctx t top bot lo : Z) (tb : list word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 160 -> bv_unsigned sp <= S ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 pc -> a2 = Z_to_bv 64 bp -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 30 ->
  (* [comment removed for export] *)
  rw_cells asegs m AINITED [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  (exists szj, rw_cells asegs m (S + 8) [C4 szj]) -> u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  (exists bpj, rw_cells asegs m (S + 2056) [C8 bpj]) ->
  (* [comment removed for export] *)
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  0 <= bot -> bot < bp -> top - 16 <= bp -> bot < top -> 4096 <= top <= 2^47 -> bp < 2^47 -> S + 2080 <= bp -> 0 <= pc < 2^64 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (unwind_impl_post S pc bp t ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [] m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5e3a0) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 34).
Variable S : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 35).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 36).
Variable bp : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 37).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 38).
Variable t : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 39).
Variable top : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 40).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 41).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 42).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 43).
#[using="Type"] Lemma unwind_impl_spec0__body : ltac:(let T := type of (fun (h : unwind_impl_spec0__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S pc bp ctx t top bot lo tb) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (S, (pc, (bp, (ctx, (t, (top, (bot, (lo, tb)))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO SPS MI TP -> -> -> -> -> -> INI TI TK T88 TSD CT GPG PG TT SW UW [szj SZC] TB LTB [bpj BPJ]
         C0 C1 T0 T1 CT2 B0 BB BT BT2 TOP BP47 SB PC RIMG RTLS RR RCTX RT. unfold sclr, iclr, KLS, AIMG_LO in *.   (* [comment removed for export] *)
  unfold AIMG_HI, AINITED, ATSDI, ATSDK, ATP88, ATSD, GOT_PGSZ, APGSZ in *.
  pose proof (munch_refl (unwind_impl_W sp S t) m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 80%nat ST.
  do 11 step.                                       (* [comment removed for export] *)
  do 6 step.                                        (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  step. callp asan_inited_spec; [exact INI|]. step. if_lit.        (* [comment removed for export] *)
  box RT.   (* [comment removed for export] *)
  step. call_sp get_current_thread_spec;
    [exact ST | exact CEIL | lia | exact MI | exact TP | exact TI | exact TK | exact T88 | exact TSD | exact CT | lia | exact C1 | solve_rng | ].
  unbox RT. rename POST into ST. try rename MI0 into MI.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI end.
  step. if_cases K; zify_cond K; [exfalso; lia|].     (* [comment removed for export] *)
  zstep. lstep. step. step.                           (* [comment removed for export] *)
  step. if_lit.                                       (* [comment removed for export] *)
  step. step. callp stack_top_spec; [exact MI | reflexivity | exact TT | exact SW | lia | lia | lia | lia | exact T1 |].
  do 3 step. callp stack_bottom_spec; [exact MI | reflexivity | exact TT | exact SW | lia | lia | lia | lia | exact T1 |].
  step. step. if_lit.                                 (* [comment removed for export] *)
  do 8 step.                                          (* [comment removed for export] *)
  step.                                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 64%nat ST.
  do 8 step.                                          (* [comment removed for export] *)
  do 6 zstep.                                         (* [comment removed for export] *)
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615.
  rewrite (land_ones_l bp) by lia.
  step.                                               (* [comment removed for export] *)
  step. if_lit. step. if_lit. step. if_lit.           (* [comment removed for export] *)
  do 5 step.                                          (* [comment removed for export] *)
  do 8 step.                                          (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -80).
  step.                                               (* [comment removed for export] *)
  name_sp sp (-80). rewrite <- Hsp in ST.
  eapply evtF_cut.
  { eapply unwind_fast_spec0;
    [ exact ST | exact CEIL | | | exact MI | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | exact GPG | exact PG | eexists; exact SZC | exact TB | exact LTB | | | | | | | | exact PC
    | exact RIMG | exact RTLS | ].
    all: try lia. exact RR. }
  cbv beta. unfold unwind_fast_post.
  lazymatch goal with |- forall ms', _ -> evtF _ _ _ _ => idtac end.
  lazymatch type of MU with munch _ _ ?mcur => post_call asegs mcur end.
  unname_sp.
  rename PC0 into ST. rename PC1 into SZ'. rename PC2 into TB'. rename PC3 into LTB'. rename POST into TR'.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI' end.
  (* [comment removed for export] *)
  step.                                               (* [comment removed for export] *)
  do 12 step.                                         (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. unfold unwind_impl_post. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact SZ'|]. split; [exact TB'|]. split; [exact LTB'|]. split; [exact TR'|].
  split; assumption.
Qed.
End Zd1.
#[using="Type"] Lemma unwind_impl_spec0 : ltac:(let t := eval cbv delta [unwind_impl_spec0__stmt] in unwind_impl_spec0__stmt in exact t).
Proof. exact unwind_impl_spec0__body. Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac alia_t1 := zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac solve_acc_with_t1 H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); alia_t1
      end
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz)); alia_t1
      end
  end.
Local Ltac acc_hint ::= lazymatch goal with |- acc_in ?RNG _ => match goal with H : rng RNG _ _ |- _ => solve_acc_with_t1 H end end.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Module RLF.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 head_may_be_arith (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h _ =>
        (match Constr.Unsafe.kind h with
         | Constr.Unsafe.Constant _ _ =>
             List.exist (fun r => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h r)
               [reference:(not); reference:(iff); reference:(Z.le); reference:(Z.lt); reference:(Z.ge); reference:(Z.gt);
                reference:(lt); reference:(ge); reference:(gt); reference:(N.le); reference:(N.lt); reference:(Z.divide)]
         | Constr.Unsafe.Ind _ _ =>
             List.exist (fun r => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h r) [reference:(and); reference:(or); reference:(eq); reference:(le)]
         | _ => true
         end)
    | _ => true
    end.
  Ltac2 is_local (id : ident) : bool := match Env.get [id] with None => true | Some _ => false end.
  (* [comment removed for export] *)
  Ltac2 meets_s (xs : ident list) (vs : ident FSet.t) : bool := List.exist (fun x => FSet.mem x vs) xs.
  Ltac2 add_all (s : ident FSet.t) (xs : ident list) : ident FSet.t := List.fold_left (fun s x => FSet.add x s) s xs.
  Ltac2 rec close_s (cand : (ident * ident list) list) (vs : ident FSet.t) (n : int) : ident FSet.t :=
    if Int.le n 0 then vs else
    let vs' := List.fold_left (fun acc c => let (_, hv) := c in if meets_s hv vs then add_all acc hv else acc) vs cand in
    if Int.equal (FSet.cardinal vs') (FSet.cardinal vs) then vs else close_s cand vs' (Int.sub n 1).
  Ltac2 drop_list (n : int) : ident list :=
    let cand := List.map_filter (fun h => let (id, body, ty) := h in
                  match body with
                  | Some _ => None
                  | None => if is_local id then (if head_may_be_arith ty then (if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.RL.arith ty then Some (id, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.RL.vars ty) else None) else None) else None
                  end) (Control.hyps ()) in
    let vs := close_s cand (add_all (FSet.empty FSet.Tags.ident_tag) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.RL.vars (Control.goal ()))) n in
    List.map_filter (fun c => let (id, hv) := c in if meets_s hv vs then None else Some id) cand.
  Ltac2 prune (nd : bool) (n : int) : unit :=
    let drop := drop_list n in
    match drop with [] => () | _ :: _ => Std.clear drop end;
    if Bool.neg nd then () else
    let disj := List.map_filter (fun h => let (id, body, ty) := h in
                  match body with
                  | Some _ => None
                  | None => if is_local id then (if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.RL.has_or ty then Some id else None) else None
                  end) (Control.hyps ()) in
    match disj with [] => () | _ :: _ => Std.clear disj end.
  Ltac2 prune2 () : unit := Control.enter (fun () => prune true 2).
  Ltac2 prune2d () : unit := Control.enter (fun () => prune false 2).
End RLF.
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.rl_prune ::= ltac2:(RLF.prune2 ()).
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.rl_prune_d ::= ltac2:(RLF.prune2d ()).
(* [comment removed for export] *)
Local Ltac solve_acc1 ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.solve_acc1_rl.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Notation unwind_impl_W sp S t :=
  ([(bv_unsigned sp - 160, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 2056); (S + 2056, S + 2064); (t + 3168, t + 3169)]%Z) (only parsing).

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma unwind_fast_spec0 : forall RNG (raf sp gp tp t0 t1 t2 s0f s1f a0 a1 a2 a3 a4 a5 a6 a7 s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (S pc bp top bot lo : Z) (tb : list word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= S ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 pc -> a2 = Z_to_bv 64 bp -> a3 = Z_to_bv 64 top -> a4 = Z_to_bv 64 bot -> a5 = Z_to_bv 64 30 ->
  rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (exists szj, rw_cells asegs m (S + 8) [C4 szj]) -> u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  0 <= bot -> bot < bp -> top - 16 <= bp -> bot < top -> 4096 <= top <= 2^47 -> bp < 2^47 -> S + 2072 <= bp -> 0 <= pc < 2^64 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bp - lo) ->
  evtF asegs RNG (unwind_fast_post S pc top sp raf s0f s1f s2f s3f s4f s5f s6f gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo tb [] m)
    (MS (mkR raf sp gp tp t0 t1 t2 s0f s1f a0 a1 a2 a3 a4 a5 a6 a7 s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x76fd4) fc None m (seg_rom asegs)).
Proof.
  intros until tb. intros ST CEIL LO SPS MI -> -> -> -> -> -> GPG PG [szj SZC] TB LTB B0 BB BT BT2 TOP BP47 SB PC RIMG RTLS RR.
  unfold GOT_PGSZ, APGSZ in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 2056)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 64%nat ST.
  do 9 step.                                   (* [comment removed for export] *)
  step. do 3 zstep.                            (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  do 3 step.                                   (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  step. zstep.                                 (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u64arr_store_ok asegs mm (S + 16) tb 0 (wa (S + 16)) TB ltac:(lia) ltac:(f_equal; lia)) as SOK end.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
    pose proof (u64arr_write asegs mm (S + 16) tb 0 (Z_to_bv 64 pc) TB ltac:(lia)) as TB2;
    rewrite Z.mul_0_r, Z.add_0_r in TB2 end.
  clear TB. store_done. rename TB2 into TB. cbn [Z.to_nat upd] in TB.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite Z.shiftr_div_pow2 in K0 by lia. Z.div_mod_to_equations. lia. }
  step. if_cases K1; zify_cond K1. { exfalso. lia. }     (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. lia. }     (* [comment removed for export] *)
  zstep. step. if_cases K3; zify_cond K3. 2: { exfalso. lia. }   (* [comment removed for export] *)
  do 10 step.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. unfold unwind_fast_post.
  do 6 eexists. eexists. exists (upd tb 0 (Z_to_bv 64 pc)). split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [cbn [length]; exact SZC|]. split; [exact TB|]. split; [rewrite upd_length; exact LTB|].
  destruct tb as [|w0 tb0]; [cbn in LTB; lia|]. cbn [upd firstn map length]. rewrite unsigned_lit by lia. reflexivity.
Qed.

Definition unwind_impl_spec0__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (S pc bp ctx t top bot lo : Z) (tb : list word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 160 -> bv_unsigned sp <= S ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 pc -> a2 = Z_to_bv 64 bp -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 30 ->
  (* [comment removed for export] *)
  rw_cells asegs m AINITED [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  (exists szj, rw_cells asegs m (S + 8) [C4 szj]) -> u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  (exists bpj, rw_cells asegs m (S + 2056) [C8 bpj]) ->
  (* [comment removed for export] *)
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  0 <= bot -> bot < bp -> top - 16 <= bp -> bot < top -> 4096 <= top <= 2^47 -> bp < 2^47 -> S + 2080 <= bp -> 0 <= pc < 2^64 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (unwind_impl_post S pc bp t ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [] m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5e408) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 34).
Variable S : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 35).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 36).
Variable bp : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 37).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 38).
Variable t : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 39).
Variable top : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 40).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 41).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 42).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec0__stmt 43).
#[using="Type"] Lemma unwind_impl_spec0__body : ltac:(let T := type of (fun (h : unwind_impl_spec0__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S pc bp ctx t top bot lo tb) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (S, (pc, (bp, (ctx, (t, (top, (bot, (lo, tb)))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO SPS MI TP -> -> -> -> -> -> INI TI TK T88 TSD CT GPG PG TT SW UW [szj SZC] TB LTB [bpj BPJ]
         C0 C1 T0 T1 CT2 B0 BB BT BT2 TOP BP47 SB PC RIMG RTLS RR RCTX RT. unfold sclr, iclr, KLS, AIMG_LO in *.   (* [comment removed for export] *)
  unfold AIMG_HI, AINITED, ATSDI, ATSDK, ATP88, ATSD, GOT_PGSZ, APGSZ in *.
  pose proof (munch_refl (unwind_impl_W sp S t) m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 80%nat ST.
  do 11 step.                                       (* [comment removed for export] *)
  do 6 step.                                        (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  step. callp asan_inited_spec; [exact INI|]. step. if_lit.        (* [comment removed for export] *)
  box RT.   (* [comment removed for export] *)
  step. call_sp get_current_thread_spec;
    [exact ST | exact CEIL | lia | exact MI | exact TP | exact TI | exact TK | exact T88 | exact TSD | exact CT | lia | exact C1 | solve_rng | ].
  unbox RT. rename POST into ST. try rename MI0 into MI.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI end.
  step. if_cases K; zify_cond K; [exfalso; lia|].     (* [comment removed for export] *)
  zstep. lstep. step. step.                           (* [comment removed for export] *)
  step. if_lit.                                       (* [comment removed for export] *)
  step. step. callp stack_top_spec; [exact MI | reflexivity | exact TT | exact SW | lia | lia | lia | lia | exact T1 |].
  do 3 step. callp stack_bottom_spec; [exact MI | reflexivity | exact TT | exact SW | lia | lia | lia | lia | exact T1 |].
  step. step. if_lit.                                 (* [comment removed for export] *)
  do 8 step.                                          (* [comment removed for export] *)
  step.                                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 64%nat ST.
  do 8 step.                                          (* [comment removed for export] *)
  do 6 zstep.                                         (* [comment removed for export] *)
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615.
  rewrite (land_ones_l bp) by lia.
  step.                                               (* [comment removed for export] *)
  step. if_lit. step. if_lit. step. if_lit.           (* [comment removed for export] *)
  do 5 step.                                          (* [comment removed for export] *)
  do 8 step.                                          (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -80).
  step.                                               (* [comment removed for export] *)
  name_sp sp (-80). rewrite <- Hsp in ST.
  eapply evtF_cut.
  { eapply unwind_fast_spec0;
    [ exact ST | exact CEIL | | | exact MI | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | exact GPG | exact PG | eexists; exact SZC | exact TB | exact LTB | | | | | | | | exact PC
    | exact RIMG | exact RTLS | ].
    all: try lia. exact RR. }
  cbv beta. unfold unwind_fast_post.
  lazymatch goal with |- forall ms', _ -> evtF _ _ _ _ => idtac end.
  lazymatch type of MU with munch _ _ ?mcur => post_call asegs mcur end.
  unname_sp.
  rename PC0 into ST. rename PC1 into SZ'. rename PC2 into TB'. rename PC3 into LTB'. rename POST into TR'.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI' end.
  (* [comment removed for export] *)
  step.                                               (* [comment removed for export] *)
  do 12 step.                                         (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. unfold unwind_impl_post. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact SZ'|]. split; [exact TB'|]. split; [exact LTB'|]. split; [exact TR'|].
  split; assumption.
Qed.
End Zd1.
#[using="Type"] Lemma unwind_impl_spec0 : ltac:(let t := eval cbv delta [unwind_impl_spec0__stmt] in unwind_impl_spec0__stmt in exact t).
Proof. exact unwind_impl_spec0__body. Qed.
End CANSEC1.
End TwB.
End F_aunwind2.

(* [comment removed for export] *)
Module F_tlsga.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition AFSDESC : Z := 0xa61b8.      (* [comment removed for export] *)
Definition AREAL_TLSGA : Z := 0xa7288.  (* [comment removed for export] *)
Definition ATLSGA : Z := 0x9f398.       (* [comment removed for export] *)
Definition ADTLSF : Z := 0x6d630.        (* [comment removed for export] *)
Definition ATLSGA_ICPT : Z := 0x495f8.   (* [comment removed for export] *)
Definition ADTV : Z := (ATPv + 288).         (* [comment removed for export] *)
Definition ADTLSV : Z := (ATPv + 8).       (* [comment removed for export] *)
Definition AVERB : Z := 0x13e098.        (* [comment removed for export] *)
Definition ACF137 : Z := 0x1401b1.       (* [comment removed for export] *)

(* [comment removed for export] *)
End CANSEC1.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma musl_tlsga_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (fsw : word),
  tp = Z_to_bv 64 ATP ->
  rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)] ->
  rw_cells asegs m (ATPv + -8) [C8 (Z_to_bv 64 ADTV); C8 fsw] ->
  rw_cells asegs m (ADTV + 8) [C8 (Z_to_bv 64 (ATP + 0x800))] ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => exists a1' a2',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ATP) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AFSDESC) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATLSGA) fc None m (seg_rom asegs)).
Proof.
  intros until fsw. intros -> DESC DTVP DTV1 RIMG RTLS.
  unfold AFSDESC, ATP, ADTV, ATLSGA in *. lit_in DTVP; lit_in DTV1.
  replace (ATPv + 288 + 8) with (ATPv + 296) in DTV1 by (clear; lia).     (* [comment removed for export] *)
  do 9 zstep.
  replace (Z_to_bv 64 (18446744073709549568 + (ATPv + 2048))) with (Z_to_bv 64 ATPv)      (* [comment removed for export] *)
    by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64);
        replace (18446744073709549568 + (ATPv + 2048)) with (ATPv + 1 * 2^64) by (clear; lia); rewrite Z.mod_add by lia; reflexivity).
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dtls_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

#[using="Type"] Lemma dtls_fast_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo B v : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 AFSDESC ->
  rt_got m ->
  rw_cells asegs m ACF137 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa5500 [C8 (Z_to_bv 64 AVERB)] ->
  rw_cells asegs m AVERB [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)] ->
  rw_cells asegs m 0xa61c8 [C8 (Z_to_bv 64 8)] ->
  rw_cells asegs m ADTLSV [C8 (Z_to_bv 64 B)] ->
  rw_cells asegs m (B + 24) [C8 (Z_to_bv 64 v)] ->
  iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->            (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG B 4096 ->
  evtF asegs RNG (dtls_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ADTLSF) fc None m (seg_rom asegs)).
Proof.
  intros until v. intros MI ST LO CEIL -> -> G50 CF GB0 VERB DESC G08 DV BD BLO BHI V RIMG RTLS RSTK RB. destruct BLO as [BLO _].   (* [comment removed for export] *)
  unfold GOT_CFLAGS, ACFLAGS, ACF137, AVERB, AFSDESC, ADTLSV, ADTLSF, ATP, AIMG_HI in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 144%nat ST.
  do 14 zstep.                              (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep; rewrite zxb_lit by lia.            (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; clear - K; lia|].   (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep; lits.                       (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  rewrite (Z.add_comm 8 ATPv).              (* [comment removed for export] *)
  zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2; lia|].   (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. if_cases K3; zify_cond K3; [exfalso; clear - K3 V BHI; lia|].      (* [comment removed for export] *)
  zstep. if_cases K4; zify_cond K4; [| exfalso; clear - K4 BLO; lia].      (* [comment removed for export] *)
  zstep. if_cases K5; zify_cond K5; [exfalso; clear - K5 BLO; lia|].        (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. zstep. if_cases K6; zify_cond K6; [| exfalso; clear - K6; lia].   (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases K7; zify_cond K7; [exfalso; clear - K7 V; lia|].          (* [comment removed for export] *)
  do 16 zstep.                              (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tlsga_cells (m : amem) (t B v : Z) (fsw : word) : Prop :=
     rw_cells asegs m AREAL_TLSGA [C8 (Z_to_bv 64 ATLSGA)]
  /\ rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]
  /\ rw_cells asegs m (ATPv + -8) [C8 (Z_to_bv 64 ADTV); C8 fsw]
  /\ rw_cells asegs m (ADTV + 8) [C8 (Z_to_bv 64 (ATP + 0x800))]
  /\ rt_got m
  /\ rw_cells asegs m ACF137 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xa5500 [C8 (Z_to_bv 64 AVERB)]
  /\ rw_cells asegs m AVERB [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0xa61c8 [C8 (Z_to_bv 64 8)]
  /\ rw_cells asegs m ADTLSV [C8 (Z_to_bv 64 B)]
  /\ rw_cells asegs m (B + 24) [C8 (Z_to_bv 64 v)]
  /\ (exists tb te : word, rw_cells asegs m (t + 48) [C8 tb; C8 te]).

Definition tlsga_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ATP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition tlsga_icpt_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo ctx t B v : Z) (fsw : word),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 AFSDESC ->
  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v fsw ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->     (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  evtF asegs RNG (tlsga_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATLSGA_ICPT) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 34).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 35).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 36).
Variable t : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 37).
Variable B : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 38).
Variable v : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 39).
Variable fsw : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 40).
#[using="Type"] Lemma tlsga_icpt_spec__body : ltac:(let T := type of (fun (h : tlsga_icpt_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ctx t B v fsw) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (lo, (ctx, (t, (B, (v, fsw))))))))))))))))))))))))))))))))))))))))) as _.
 intros MI ST LO CEIL TP A0 INI TI TK T88 TSD CT
         (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48))
         C0 C1 T0 T1 BLO BHI V RIMG RTLS RSTK RCTX RT RB.
  subst a0.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *)
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ATLSGA_ICPT, ATLSGA in *.
  lit_in DTVP; lit_in DTV1.
  carve_frame 32%nat ST.
  do 5 zstep.                               (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. call_sp tryinit_spec;
    first [exact MI| exact ST| exact INI| exact RIMG| unfold KHIGH; lia| solve_rng | idtac].
  rename PC into ST. clear POST.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI1 end.
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  callp musl_tlsga_spec; first [exact TP| exact DESC| exact DTVP| exact DTV1| exact RIMG | exact RTLS| idtac].
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; clear - K; lia|].   (* [comment removed for export] *)
  (* [comment removed for export] *)
  box RT; box RB.
  zstep. call_sp get_current_thread_spec;
    first [exact ST| exact MI1| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| exact RIMG | exact RTLS| exact RCTX
          | atop_facts; lia| solve_rng | idtac].
  unbox RT; unbox RB. rename POST into ST.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2 T0; lia|].        (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. call_sp dtls_fast_spec;
    first [exact MI2| exact ST| exact TP| reflexivity| exact G50| exact CF| exact GB0| exact VERB| exact DESC
          | exact G08| exact DV| exact BD| exact RIMG | exact RTLS| exact RB| exact BLO| unfold AIMG_HI; lia| solve_rng | idtac].
  rename POST into ST.
  do 7 zstep.                               (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). subst tp. finish.
Qed.
End Zd1.
#[using="Type"] Lemma tlsga_icpt_spec : ltac:(let t := eval cbv delta [tlsga_icpt_spec__stmt] in tlsga_icpt_spec__stmt in exact t).
Proof. exact tlsga_icpt_spec__body. Qed.
End CANSEC2.
(* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition AFSDESC : Z := 0xa6598.      (* [comment removed for export] *)
Definition AREAL_TLSGA : Z := 0xa7668.  (* [comment removed for export] *)
Definition ATLSGA : Z := 0x9f77c.       (* [comment removed for export] *)
Definition ADTLSF : Z := 0x6d698.        (* [comment removed for export] *)
Definition ATLSGA_ICPT : Z := 0x49660.   (* [comment removed for export] *)
Definition ADTV : Z := (ATPv + 288).         (* [comment removed for export] *)
Definition ADTLSV : Z := (ATPv + 8).       (* [comment removed for export] *)
Definition AVERB : Z := 0x13e498.        (* [comment removed for export] *)
Definition ACF137 : Z := 0x1405b1.       (* [comment removed for export] *)

(* [comment removed for export] *)
End CANSEC1.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma musl_tlsga_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (fsw : word),
  tp = Z_to_bv 64 ATP ->
  rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)] ->
  rw_cells asegs m (ATPv + -8) [C8 (Z_to_bv 64 ADTV); C8 fsw] ->
  rw_cells asegs m (ADTV + 8) [C8 (Z_to_bv 64 (ATP + 0x800))] ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => exists a1' a2',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ATP) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AFSDESC) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATLSGA) fc None m (seg_rom asegs)).
Proof.
  intros until fsw. intros -> DESC DTVP DTV1 RIMG RTLS.
  unfold AFSDESC, ATP, ADTV, ATLSGA in *. lit_in DTVP; lit_in DTV1.
  replace (ATPv + 288 + 8) with (ATPv + 296) in DTV1 by (clear; lia).     (* [comment removed for export] *)
  do 9 zstep.
  replace (Z_to_bv 64 (18446744073709549568 + (ATPv + 2048))) with (Z_to_bv 64 ATPv)      (* [comment removed for export] *)
    by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64);
        replace (18446744073709549568 + (ATPv + 2048)) with (ATPv + 1 * 2^64) by (clear; lia); rewrite Z.mod_add by lia; reflexivity).
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dtls_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

#[using="Type"] Lemma dtls_fast_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo B v : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 AFSDESC ->
  rt_got m ->
  rw_cells asegs m ACF137 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa58e0 [C8 (Z_to_bv 64 AVERB)] ->
  rw_cells asegs m AVERB [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)] ->
  rw_cells asegs m 0xa65a8 [C8 (Z_to_bv 64 8)] ->
  rw_cells asegs m ADTLSV [C8 (Z_to_bv 64 B)] ->
  rw_cells asegs m (B + 24) [C8 (Z_to_bv 64 v)] ->
  iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->            (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG B 4096 ->
  evtF asegs RNG (dtls_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ADTLSF) fc None m (seg_rom asegs)).
Proof.
  intros until v. intros MI ST LO CEIL -> -> G50 CF GB0 VERB DESC G08 DV BD BLO BHI V RIMG RTLS RSTK RB. destruct BLO as [BLO _].   (* [comment removed for export] *)
  unfold GOT_CFLAGS, ACFLAGS, ACF137, AVERB, AFSDESC, ADTLSV, ADTLSF, ATP, AIMG_HI in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 144%nat ST.
  do 14 zstep.                              (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep; rewrite zxb_lit by lia.            (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; clear - K; lia|].   (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep; lits.                       (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  rewrite (Z.add_comm 8 ATPv).              (* [comment removed for export] *)
  zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2; lia|].   (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. if_cases K3; zify_cond K3; [exfalso; clear - K3 V BHI; lia|].      (* [comment removed for export] *)
  zstep. if_cases K4; zify_cond K4; [| exfalso; clear - K4 BLO; lia].      (* [comment removed for export] *)
  zstep. if_cases K5; zify_cond K5; [exfalso; clear - K5 BLO; lia|].        (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. zstep. if_cases K6; zify_cond K6; [| exfalso; clear - K6; lia].   (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases K7; zify_cond K7; [exfalso; clear - K7 V; lia|].          (* [comment removed for export] *)
  do 16 zstep.                              (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tlsga_cells (m : amem) (t B v : Z) (fsw : word) : Prop :=
     rw_cells asegs m AREAL_TLSGA [C8 (Z_to_bv 64 ATLSGA)]
  /\ rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]
  /\ rw_cells asegs m (ATPv + -8) [C8 (Z_to_bv 64 ADTV); C8 fsw]
  /\ rw_cells asegs m (ADTV + 8) [C8 (Z_to_bv 64 (ATP + 0x800))]
  /\ rt_got m
  /\ rw_cells asegs m ACF137 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xa58e0 [C8 (Z_to_bv 64 AVERB)]
  /\ rw_cells asegs m AVERB [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0xa65a8 [C8 (Z_to_bv 64 8)]
  /\ rw_cells asegs m ADTLSV [C8 (Z_to_bv 64 B)]
  /\ rw_cells asegs m (B + 24) [C8 (Z_to_bv 64 v)]
  /\ (exists tb te : word, rw_cells asegs m (t + 48) [C8 tb; C8 te]).

Definition tlsga_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ATP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition tlsga_icpt_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo ctx t B v : Z) (fsw : word),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 AFSDESC ->
  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v fsw ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->     (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  evtF asegs RNG (tlsga_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATLSGA_ICPT) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 34).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 35).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 36).
Variable t : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 37).
Variable B : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 38).
Variable v : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 39).
Variable fsw : ltac2:(SecDietF.SzSecF.ty 'tlsga_icpt_spec__stmt 40).
#[using="Type"] Lemma tlsga_icpt_spec__body : ltac:(let T := type of (fun (h : tlsga_icpt_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ctx t B v fsw) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (lo, (ctx, (t, (B, (v, fsw))))))))))))))))))))))))))))))))))))))))) as _.
 intros MI ST LO CEIL TP A0 INI TI TK T88 TSD CT
         (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48))
         C0 C1 T0 T1 BLO BHI V RIMG RTLS RSTK RCTX RT RB.
  subst a0.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *)
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ATLSGA_ICPT, ATLSGA in *.
  lit_in DTVP; lit_in DTV1.
  carve_frame 32%nat ST.
  do 5 zstep.                               (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. call_sp tryinit_spec;
    first [exact MI| exact ST| exact INI| exact RIMG| unfold KHIGH; lia| solve_rng | idtac].
  rename PC into ST. clear POST.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI1 end.
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  callp musl_tlsga_spec; first [exact TP| exact DESC| exact DTVP| exact DTV1| exact RIMG | exact RTLS| idtac].
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; clear - K; lia|].   (* [comment removed for export] *)
  (* [comment removed for export] *)
  box RT; box RB.
  zstep. call_sp get_current_thread_spec;
    first [exact ST| exact MI1| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| exact RIMG | exact RTLS| exact RCTX
          | atop_facts; lia| solve_rng | idtac].
  unbox RT; unbox RB. rename POST into ST.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2 T0; lia|].        (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. call_sp dtls_fast_spec;
    first [exact MI2| exact ST| exact TP| reflexivity| exact G50| exact CF| exact GB0| exact VERB| exact DESC
          | exact G08| exact DV| exact BD| exact RIMG | exact RTLS| exact RB| exact BLO| unfold AIMG_HI; lia| solve_rng | idtac].
  rename POST into ST.
  do 7 zstep.                               (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). subst tp. finish.
Qed.
End Zd1.
#[using="Type"] Lemma tlsga_icpt_spec : ltac:(let t := eval cbv delta [tlsga_icpt_spec__stmt] in tlsga_icpt_spec__stmt in exact t).
Proof. exact tlsga_icpt_spec__body. Qed.
End CANSEC2.
(* [comment removed for export] *)
End TwB.
End F_tlsga.

(* [comment removed for export] *)
Module AFake_sm0.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_tlsga OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_m2s_b.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFakeProbe. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFakeProbe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition ASTKMALLOC0 : Z := 0x3f278.

(* [comment removed for export] *)
Definition sm0_W (sp fs flag F : Z) : list (Z * Z) :=
  [(sp - 208, sp); (fs, fs + 8); (flag, flag + 1); (F + 24, F + 32); (F + 56, F + 64); (shad F, shad F + 8)].

Definition sm0_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs h j flag F : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sm0_W (bv_unsigned sp) fs flag F) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fs [C8 (Z_to_bv 64 (h + j + 1))]
    /\ rw_cells asegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells asegs m' (F + 24) [C8 sp]
    /\ rw_cells asegs m' (F + 56) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
#[using="Type"] Lemma sm0_probe : forall RNG (Q : machine_state -> Prop) (d : nat) (k j fs h : Z)
    (x1 x2 gp tp x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) fc (m1 : amem),
  Z.of_nat d = j - k -> 0 <= k -> j < 16384 -> 0 <= h < 2^64 ->
  mem_inv asegs m1 -> 0 <= fs -> fs + 11571200 <= 2^64 -> rng RNG fs 11571200 ->
  (forall i, k <= i < j -> rw_cells asegs m1 (fs + 4096 + Z.land (h + i) 16383) [C1 (Z_to_bv 8 1)]) ->
  rw_cells asegs m1 (fs + 4096 + Z.land (h + j) 16383) [C1 (Z_to_bv 8 0)] ->
  evtF asegs RNG Q
    (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (16384 - j)) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + j)) (Z_to_bv 64 16383) x14
             (Z_to_bv 64 (fs + 4096 + Z.land (h + j) 16383)) (Z_to_bv 64 (Z.land (h + j) 16383)) (Z_to_bv 64 0)
             x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 0x3f374) fc None m1 (seg_rom asegs)) ->
  evtF asegs RNG Q
    (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (16384 - k)) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + k)) (Z_to_bv 64 16383) x14
             x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 0x3f2fc) fc None m1 (seg_rom asegs)).
Proof.
  intros RNG Q d. induction d as [|d IH]; intros k j fs h x1 x2 gp tp x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m1 HD K0 J128 HB MI FS0 FS1 RFS LIVE FREE KONT.
  - assert (k = j) by lia. subst k.
    assert (PB : 0 <= Z.land (h + j) 16383 < 16384) by (change 16383 with (Z.ones 14); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    zstep. rewrite land_mod64 by (clear; lia).             (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    remember (fs + 4096 + Z.land (h + j) 16383) as fa eqn:EFA.      (* [comment removed for export] *)
    assert (FAB : fs + 4096 <= fa < fs + 20480) by (subst fa; clear -PB; lia).
    zstep; rewrite zxb_lit by (clear; lia).             (* [comment removed for export] *)
    zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].      (* [comment removed for export] *)
    exact KONT.
  - assert (KJ : k < j) by lia.
    assert (PB : 0 <= Z.land (h + k) 16383 < 16384) by (change 16383 with (Z.ones 14); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    pose proof (LIVE k ltac:(lia)) as LK.
    zstep. rewrite land_mod64 by (clear; lia).             (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    remember (fs + 4096 + Z.land (h + k) 16383) as fa eqn:EFA.
    assert (FAB : fs + 4096 <= fa < fs + 20480) by (subst fa; clear -PB; lia).
    zstep; rewrite zxb_lit by (clear; lia).             (* [comment removed for export] *)
    zstep. if_cases Kd; zify_cond Kd; [exfalso; clear - Kd; lia|].      (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    setreg 10 (Z_to_bv 64 (16384 - (k + 1))) ltac:(rewrite swrap32_smallF by (clear -K0 KJ J128; lia); f_equal; clear; lia).
    zstep.                                              (* [comment removed for export] *)
    setreg 12 (Z_to_bv 64 (h + (k + 1))) ltac:(f_equal; clear; lia).
    zstep. if_cases Ke; zify_cond Ke; [| exfalso; rewrite ?Z.mod_small in Ke by (clear -K0 KJ J128; lia); clear -Ke K0 KJ J128; lia].      (* [comment removed for export] *)
    subst fa.
    eapply (IH (k + 1) j fs h); try eassumption; try (clear -HD K0 KJ; lia).
    intros i Hi. apply LIVE. clear -Hi. lia.
Qed.

#[using="Type"] Lemma stack_malloc0_cspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h j pos flag F : Z) (j24 j56 sh0 : word),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->     (* [comment removed for export] *)
  (* [comment removed for export] *)
  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->            (* [comment removed for export] *)
  rw_cells asegs m fs [C8 (Z_to_bv 64 h)] -> 0 <= h < 2^64 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells asegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  0 <= j < 16384 ->
  (forall k, 0 <= k < j -> rw_cells asegs m (fs + 4096 + Z.land (h + k) 16383) [C1 (Z_to_bv 8 1)]) ->
  pos = Z.land (h + j) 16383 -> flag = fs + 4096 + pos -> F = fs + 36864 + pos * 64 ->
  rw_cells asegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (F + 24) [C8 j24] -> rw_cells asegs m (F + 56) [C8 j56] ->
  rw_cells asegs m (shad F) [C8 sh0] ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (sm0_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs h j flag F m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom asegs)).
Proof.
  intros until sh0.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY C0 C1 T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC JB LIVE POS FLAG FF FL0 F24 F56 SH0
         RIMG RTLS RSTK RCTX RT RB RFS RSH.
  (pose proof (ablk_lin _ _ FLO) as ndP__; nd_pre ndP__ 4%nat; intros FLOL _ _ _; nd_post). unfold AIMG_HI in FLOL.   (* [comment removed for export] *)
  pose proof TC as TC0. (nd_pre TC 12%nat; intros REAL DESC DTVP DTV1 G50 CF GB0 VERB G08 DV BD (tb & te & T48); nd_post).
  pose proof (munch_refl (sm0_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm0_W in MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC0 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 16384).
  { subst pos. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 8 <= fs \/ fs + 11571200 <= shad F).   (* [comment removed for export] *)
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  (* [comment removed for export] *)
  assert (LDJ : forall i, 0 <= i < j -> disjoint_from (sm0_W (bv_unsigned sp) fs flag F) (fs + 4096 + Z.land (h + i) 16383) 1).
  { intros i Hi. unfold sm0_W. cbn [disjoint_from fst snd].
    assert (PI : 0 <= Z.land (h + i) 16383 < 16384 /\ Z.land (h + i) 16383 <> pos).
    { subst pos. change 16383 with (Z.ones 14). rewrite !Z.land_ones by lia. change (2^14) with 16384. clear -Hi JB. Z.div_mod_to_equations. lia. }
    clear -PI PB FLAG FF LO CEIL LO0 SHD FLOL FHI. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.                               (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  box RCTX; box RT; box RB.   (* [comment removed for export] *)
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | exact RTLS | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].   (* [comment removed for export] *)
  zstep; rewrite zxb_lit by lia.            (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].      (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep; lits.                              (* [comment removed for export] *)
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].      (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.               (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (16384 - 0)) ltac:(reflexivity). setreg 12 (Z_to_bv 64 (h + 0)) ltac:(f_equal; clear; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LIVE' : forall i, 0 <= i < j -> rw_cells asegs mm (fs + 4096 + Z.land (h + i) 16383) [Cells.C1 (Z_to_bv 8 1)])
      by (intros i Hi; eapply rw_cells_transport; [exact (LIVE i Hi) | exact MU | exact WM | exact (LDJ i Hi)]) end.
  eapply (sm0_probe RNG _ (Z.to_nat j) 0 j fs h); try eassumption; try (clear -JB HB FLOL FHI; lia).
  { rewrite <- POS, <- FLAG. exact FL0. }
  rewrite <- POS, <- FLAG.
  (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (fs + 36864 + Z.shiftl pos 6)] =>
    replace (fs + 36864 + Z.shiftl pos 6) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^6) with 64; lia) end.
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)   (* [comment removed for export] *)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  assert (RSF : rng RNG (shad F) 8).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep.                                    (* [comment removed for export] *)
  do 6 zstep.                               (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_tlsga.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_m2s_b.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFakeProbe.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition ASTKMALLOC0 : Z := 0x3f2e0.

(* [comment removed for export] *)
Definition sm0_W (sp fs flag F : Z) : list (Z * Z) :=
  [(sp - 208, sp); (fs, fs + 8); (flag, flag + 1); (F + 24, F + 32); (F + 56, F + 64); (shad F, shad F + 8)].

Definition sm0_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs h j flag F : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sm0_W (bv_unsigned sp) fs flag F) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fs [C8 (Z_to_bv 64 (h + j + 1))]
    /\ rw_cells asegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells asegs m' (F + 24) [C8 sp]
    /\ rw_cells asegs m' (F + 56) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
#[using="Type"] Lemma sm0_probe : forall RNG (Q : machine_state -> Prop) (d : nat) (k j fs h : Z)
    (x1 x2 gp tp x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) fc (m1 : amem),
  Z.of_nat d = j - k -> 0 <= k -> j < 16384 -> 0 <= h < 2^64 ->
  mem_inv asegs m1 -> 0 <= fs -> fs + 11571200 <= 2^64 -> rng RNG fs 11571200 ->
  (forall i, k <= i < j -> rw_cells asegs m1 (fs + 4096 + Z.land (h + i) 16383) [C1 (Z_to_bv 8 1)]) ->
  rw_cells asegs m1 (fs + 4096 + Z.land (h + j) 16383) [C1 (Z_to_bv 8 0)] ->
  evtF asegs RNG Q
    (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (16384 - j)) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + j)) (Z_to_bv 64 16383) x14
             (Z_to_bv 64 (fs + 4096 + Z.land (h + j) 16383)) (Z_to_bv 64 (Z.land (h + j) 16383)) (Z_to_bv 64 0)
             x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 0x3f3dc) fc None m1 (seg_rom asegs)) ->
  evtF asegs RNG Q
    (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (16384 - k)) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + k)) (Z_to_bv 64 16383) x14
             x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 0x3f364) fc None m1 (seg_rom asegs)).
Proof.
  intros RNG Q d. induction d as [|d IH]; intros k j fs h x1 x2 gp tp x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m1 HD K0 J128 HB MI FS0 FS1 RFS LIVE FREE KONT.
  - assert (k = j) by lia. subst k.
    assert (PB : 0 <= Z.land (h + j) 16383 < 16384) by (change 16383 with (Z.ones 14); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    zstep. rewrite land_mod64 by (clear; lia).             (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    remember (fs + 4096 + Z.land (h + j) 16383) as fa eqn:EFA.      (* [comment removed for export] *)
    assert (FAB : fs + 4096 <= fa < fs + 20480) by (subst fa; clear -PB; lia).
    zstep; rewrite zxb_lit by (clear; lia).             (* [comment removed for export] *)
    zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].      (* [comment removed for export] *)
    exact KONT.
  - assert (KJ : k < j) by lia.
    assert (PB : 0 <= Z.land (h + k) 16383 < 16384) by (change 16383 with (Z.ones 14); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    pose proof (LIVE k ltac:(lia)) as LK.
    zstep. rewrite land_mod64 by (clear; lia).             (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    remember (fs + 4096 + Z.land (h + k) 16383) as fa eqn:EFA.
    assert (FAB : fs + 4096 <= fa < fs + 20480) by (subst fa; clear -PB; lia).
    zstep; rewrite zxb_lit by (clear; lia).             (* [comment removed for export] *)
    zstep. if_cases Kd; zify_cond Kd; [exfalso; clear - Kd; lia|].      (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    setreg 10 (Z_to_bv 64 (16384 - (k + 1))) ltac:(rewrite swrap32_smallF by (clear -K0 KJ J128; lia); f_equal; clear; lia).
    zstep.                                              (* [comment removed for export] *)
    setreg 12 (Z_to_bv 64 (h + (k + 1))) ltac:(f_equal; clear; lia).
    zstep. if_cases Ke; zify_cond Ke; [| exfalso; rewrite ?Z.mod_small in Ke by (clear -K0 KJ J128; lia); clear -Ke K0 KJ J128; lia].      (* [comment removed for export] *)
    subst fa.
    eapply (IH (k + 1) j fs h); try eassumption; try (clear -HD K0 KJ; lia).
    intros i Hi. apply LIVE. clear -Hi. lia.
Qed.

#[using="Type"] Lemma stack_malloc0_cspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h j pos flag F : Z) (j24 j56 sh0 : word),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->     (* [comment removed for export] *)
  (* [comment removed for export] *)
  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->            (* [comment removed for export] *)
  rw_cells asegs m fs [C8 (Z_to_bv 64 h)] -> 0 <= h < 2^64 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells asegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  0 <= j < 16384 ->
  (forall k, 0 <= k < j -> rw_cells asegs m (fs + 4096 + Z.land (h + k) 16383) [C1 (Z_to_bv 8 1)]) ->
  pos = Z.land (h + j) 16383 -> flag = fs + 4096 + pos -> F = fs + 36864 + pos * 64 ->
  rw_cells asegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (F + 24) [C8 j24] -> rw_cells asegs m (F + 56) [C8 j56] ->
  rw_cells asegs m (shad F) [C8 sh0] ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (sm0_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs h j flag F m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom asegs)).
Proof.
  intros until sh0.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY C0 C1 T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC JB LIVE POS FLAG FF FL0 F24 F56 SH0
         RIMG RTLS RSTK RCTX RT RB RFS RSH.
  (pose proof (ablk_lin _ _ FLO) as ndP__; nd_pre ndP__ 4%nat; intros FLOL _ _ _; nd_post). unfold AIMG_HI in FLOL.   (* [comment removed for export] *)
  pose proof TC as TC0. (nd_pre TC 12%nat; intros REAL DESC DTVP DTV1 G50 CF GB0 VERB G08 DV BD (tb & te & T48); nd_post).
  pose proof (munch_refl (sm0_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm0_W in MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC0 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 16384).
  { subst pos. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 8 <= fs \/ fs + 11571200 <= shad F).   (* [comment removed for export] *)
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  (* [comment removed for export] *)
  assert (LDJ : forall i, 0 <= i < j -> disjoint_from (sm0_W (bv_unsigned sp) fs flag F) (fs + 4096 + Z.land (h + i) 16383) 1).
  { intros i Hi. unfold sm0_W. cbn [disjoint_from fst snd].
    assert (PI : 0 <= Z.land (h + i) 16383 < 16384 /\ Z.land (h + i) 16383 <> pos).
    { subst pos. change 16383 with (Z.ones 14). rewrite !Z.land_ones by lia. change (2^14) with 16384. clear -Hi JB. Z.div_mod_to_equations. lia. }
    clear -PI PB FLAG FF LO CEIL LO0 SHD FLOL FHI. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.                               (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  box RCTX; box RT; box RB.   (* [comment removed for export] *)
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | exact RTLS | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].   (* [comment removed for export] *)
  zstep; rewrite zxb_lit by lia.            (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].      (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep; lits.                              (* [comment removed for export] *)
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].      (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.               (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (16384 - 0)) ltac:(reflexivity). setreg 12 (Z_to_bv 64 (h + 0)) ltac:(f_equal; clear; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LIVE' : forall i, 0 <= i < j -> rw_cells asegs mm (fs + 4096 + Z.land (h + i) 16383) [Cells.C1 (Z_to_bv 8 1)])
      by (intros i Hi; eapply rw_cells_transport; [exact (LIVE i Hi) | exact MU | exact WM | exact (LDJ i Hi)]) end.
  eapply (sm0_probe RNG _ (Z.to_nat j) 0 j fs h); try eassumption; try (clear -JB HB FLOL FHI; lia).
  { rewrite <- POS, <- FLAG. exact FL0. }
  rewrite <- POS, <- FLAG.
  (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (fs + 36864 + Z.shiftl pos 6)] =>
    replace (fs + 36864 + Z.shiftl pos 6) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^6) with 64; lia) end.
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)   (* [comment removed for export] *)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  assert (RSF : rng RNG (shad F) 8).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep.                                    (* [comment removed for export] *)
  do 6 zstep.                               (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.
End CANSEC1.
End TwB.
End AFake_sm0.

(* [comment removed for export] *)
Module AFake_sm1.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_tlsga OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_m2s_b.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFakeProbe. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFakeProbe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition ASTKMALLOC1 : Z := 0x3f3ec.

(* [comment removed for export] *)
Definition sm1_W (sp fs flag F : Z) : list (Z * Z) :=
  [(sp - 208, sp); (fs + 8, fs + 16); (flag, flag + 1); (F + 24, F + 32); (F + 120, F + 128); (shad F, shad F + 16)].

Definition sm1_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs h j flag F : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sm1_W (bv_unsigned sp) fs flag F) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (fs + 8) [C8 (Z_to_bv 64 (h + j + 1))]
    /\ rw_cells asegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells asegs m' (F + 24) [C8 sp]
    /\ rw_cells asegs m' (F + 120) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
#[using="Type"] Lemma sm1_probe : forall RNG (Q : machine_state -> Prop) (d : nat) (k j fs h : Z)
    (x1 x2 gp tp x5 x6 x7 x8 x9 x11 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) fc (m1 : amem),
  Z.of_nat d = j - k -> 0 <= k -> j < 8192 -> 0 <= h < 2^64 ->
  mem_inv asegs m1 -> 0 <= fs -> fs + 11571200 <= 2^64 -> rng RNG fs 11571200 ->
  (forall i, k <= i < j -> rw_cells asegs m1 (fs + 20480 + Z.land (h + i) 8191) [C1 (Z_to_bv 8 1)]) ->
  rw_cells asegs m1 (fs + 20480 + Z.land (h + j) 8191) [C1 (Z_to_bv 8 0)] ->
  evtF asegs RNG Q
    (MS (mkR x1 x2 gp tp (Z_to_bv 64 0) x6 x7 x8 x9 (Z_to_bv 64 (8192 - j)) x11 (Z_to_bv 64 (h + j)) (Z_to_bv 64 (fs + 20480)) (Z_to_bv 64 8191)
             (Z_to_bv 64 (fs + 20480 + Z.land (h + j) 8191)) x16 (Z_to_bv 64 (Z.land (h + j) 8191))
             x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 0x3f4f8) fc None m1 (seg_rom asegs)) ->
  evtF asegs RNG Q
    (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (8192 - k)) x11 (Z_to_bv 64 (h + k)) (Z_to_bv 64 (fs + 20480)) (Z_to_bv 64 8191)
             x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 0x3f480) fc None m1 (seg_rom asegs)).
Proof.
  intros RNG Q d. induction d as [|d IH]; intros k j fs h x1 x2 gp tp x5 x6 x7 x8 x9 x11 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m1 HD K0 J128 HB MI FS0 FS1 RFS LIVE FREE KONT.
  - assert (k = j) by lia. subst k.
    assert (PB : 0 <= Z.land (h + j) 8191 < 8192) by (change 8191 with (Z.ones 13); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    zstep. rewrite land_mod64 by (clear; lia).             (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    remember (fs + 20480 + Z.land (h + j) 8191) as fa eqn:EFA.      (* [comment removed for export] *)
    assert (FAB : fs + 20480 <= fa < fs + 28672) by (subst fa; clear -PB; lia).
    zstep; rewrite zxb_lit by (clear; lia).             (* [comment removed for export] *)
    zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].      (* [comment removed for export] *)
    exact KONT.
  - assert (KJ : k < j) by lia.
    assert (PB : 0 <= Z.land (h + k) 8191 < 8192) by (change 8191 with (Z.ones 13); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    pose proof (LIVE k ltac:(lia)) as LK.
    zstep. rewrite land_mod64 by (clear; lia).             (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    remember (fs + 20480 + Z.land (h + k) 8191) as fa eqn:EFA.
    assert (FAB : fs + 20480 <= fa < fs + 28672) by (subst fa; clear -PB; lia).
    zstep; rewrite zxb_lit by (clear; lia).             (* [comment removed for export] *)
    zstep. if_cases Kd; zify_cond Kd; [exfalso; clear - Kd; lia|].      (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    setreg 10 (Z_to_bv 64 (8192 - (k + 1))) ltac:(rewrite swrap32_smallF by (clear -K0 KJ J128; lia); f_equal; clear; lia).
    zstep.                                              (* [comment removed for export] *)
    setreg 12 (Z_to_bv 64 (h + (k + 1))) ltac:(f_equal; clear; lia).
    zstep. if_cases Ke; zify_cond Ke; [| exfalso; rewrite ?Z.mod_small in Ke by (clear -K0 KJ J128; lia); clear -Ke K0 KJ J128; lia].      (* [comment removed for export] *)
    subst fa.
    eapply (IH (k + 1) j fs h); try eassumption; try (clear -HD K0 KJ; lia).
    intros i Hi. apply LIVE. clear -Hi. lia.
Qed.

#[using="Type"] Lemma stack_malloc1_cspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h j pos flag F : Z) (j24 j120 sh0 sh1 : word),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->     (* [comment removed for export] *)
  (* [comment removed for export] *)
  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->            (* [comment removed for export] *)
  rw_cells asegs m (fs + 8) [C8 (Z_to_bv 64 h)] -> 0 <= h < 2^64 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells asegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  0 <= j < 8192 ->
  (forall k, 0 <= k < j -> rw_cells asegs m (fs + 20480 + Z.land (h + k) 8191) [C1 (Z_to_bv 8 1)]) ->
  pos = Z.land (h + j) 8191 -> flag = fs + 20480 + pos -> F = fs + 1085440 + pos * 128 ->
  rw_cells asegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (F + 24) [C8 j24] -> rw_cells asegs m (F + 120) [C8 j120] ->
  rw_cells asegs m (shad F) [C8 sh0; C8 sh1] ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (sm1_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs h j flag F m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC1) fc None m (seg_rom asegs)).
Proof.
  intros until sh1.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY C0 C1 T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC JB LIVE POS FLAG FF FL0 F24 F120 SH0
         RIMG RTLS RSTK RCTX RT RB RFS RSH.
  (pose proof (ablk_lin _ _ FLO) as ndP__; nd_pre ndP__ 4%nat; intros FLOL _ _ _; nd_post). unfold AIMG_HI in FLOL.   (* [comment removed for export] *)
  pose proof TC as TC0. (nd_pre TC 12%nat; intros REAL DESC DTVP DTV1 G50 CF GB0 VERB G08 DV BD (tb & te & T48); nd_post).
  pose proof (munch_refl (sm1_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm1_W in MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC1 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 8192).
  { subst pos. change 8191 with (Z.ones 13). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 16 <= fs \/ fs + 11571200 <= shad F).   (* [comment removed for export] *)
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  (* [comment removed for export] *)
  assert (LDJ : forall i, 0 <= i < j -> disjoint_from (sm1_W (bv_unsigned sp) fs flag F) (fs + 20480 + Z.land (h + i) 8191) 1).
  { intros i Hi. unfold sm1_W. cbn [disjoint_from fst snd].
    assert (PI : 0 <= Z.land (h + i) 8191 < 8192 /\ Z.land (h + i) 8191 <> pos).
    { subst pos. change 8191 with (Z.ones 13). rewrite !Z.land_ones by lia. change (2^13) with 8192. clear -Hi JB. Z.div_mod_to_equations. lia. }
    clear -PI PB FLAG FF LO CEIL LO0 SHD FLOL FHI. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.                               (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  box RCTX; box RT; box RB.   (* [comment removed for export] *)
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | exact RTLS | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].   (* [comment removed for export] *)
  zstep; rewrite zxb_lit by lia.            (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].      (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep; lits.                              (* [comment removed for export] *)
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].      (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.               (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (8192 - 0)) ltac:(reflexivity). setreg 12 (Z_to_bv 64 (h + 0)) ltac:(f_equal; clear; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LIVE' : forall i, 0 <= i < j -> rw_cells asegs mm (fs + 20480 + Z.land (h + i) 8191) [Cells.C1 (Z_to_bv 8 1)])
      by (intros i Hi; eapply rw_cells_transport; [exact (LIVE i Hi) | exact MU | exact WM | exact (LDJ i Hi)]) end.
  eapply (sm1_probe RNG _ (Z.to_nat j) 0 j fs h); try eassumption; try (clear -JB HB FLOL FHI; lia).
  { rewrite <- POS, <- FLAG. exact FL0. }
  rewrite <- POS, <- FLAG.
  (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (fs + 36864 + (1048576 + Z.shiftl pos 7))] =>
    replace (fs + 36864 + (1048576 + Z.shiftl pos 7)) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^7) with 128; lia) end.
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)   (* [comment removed for export] *)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  assert (RSF : rng RNG (shad F) 16).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep. zstep.                             (* [comment removed for export] *)
  do 6 zstep.                               (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_tlsga.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_m2s_b.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFakeProbe.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition ASTKMALLOC1 : Z := 0x3f454.

(* [comment removed for export] *)
Definition sm1_W (sp fs flag F : Z) : list (Z * Z) :=
  [(sp - 208, sp); (fs + 8, fs + 16); (flag, flag + 1); (F + 24, F + 32); (F + 120, F + 128); (shad F, shad F + 16)].

Definition sm1_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs h j flag F : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sm1_W (bv_unsigned sp) fs flag F) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (fs + 8) [C8 (Z_to_bv 64 (h + j + 1))]
    /\ rw_cells asegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells asegs m' (F + 24) [C8 sp]
    /\ rw_cells asegs m' (F + 120) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
#[using="Type"] Lemma sm1_probe : forall RNG (Q : machine_state -> Prop) (d : nat) (k j fs h : Z)
    (x1 x2 gp tp x5 x6 x7 x8 x9 x11 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) fc (m1 : amem),
  Z.of_nat d = j - k -> 0 <= k -> j < 8192 -> 0 <= h < 2^64 ->
  mem_inv asegs m1 -> 0 <= fs -> fs + 11571200 <= 2^64 -> rng RNG fs 11571200 ->
  (forall i, k <= i < j -> rw_cells asegs m1 (fs + 20480 + Z.land (h + i) 8191) [C1 (Z_to_bv 8 1)]) ->
  rw_cells asegs m1 (fs + 20480 + Z.land (h + j) 8191) [C1 (Z_to_bv 8 0)] ->
  evtF asegs RNG Q
    (MS (mkR x1 x2 gp tp (Z_to_bv 64 0) x6 x7 x8 x9 (Z_to_bv 64 (8192 - j)) x11 (Z_to_bv 64 (h + j)) (Z_to_bv 64 (fs + 20480)) (Z_to_bv 64 8191)
             (Z_to_bv 64 (fs + 20480 + Z.land (h + j) 8191)) x16 (Z_to_bv 64 (Z.land (h + j) 8191))
             x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 0x3f560) fc None m1 (seg_rom asegs)) ->
  evtF asegs RNG Q
    (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (8192 - k)) x11 (Z_to_bv 64 (h + k)) (Z_to_bv 64 (fs + 20480)) (Z_to_bv 64 8191)
             x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 0x3f4e8) fc None m1 (seg_rom asegs)).
Proof.
  intros RNG Q d. induction d as [|d IH]; intros k j fs h x1 x2 gp tp x5 x6 x7 x8 x9 x11 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m1 HD K0 J128 HB MI FS0 FS1 RFS LIVE FREE KONT.
  - assert (k = j) by lia. subst k.
    assert (PB : 0 <= Z.land (h + j) 8191 < 8192) by (change 8191 with (Z.ones 13); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    zstep. rewrite land_mod64 by (clear; lia).             (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    remember (fs + 20480 + Z.land (h + j) 8191) as fa eqn:EFA.      (* [comment removed for export] *)
    assert (FAB : fs + 20480 <= fa < fs + 28672) by (subst fa; clear -PB; lia).
    zstep; rewrite zxb_lit by (clear; lia).             (* [comment removed for export] *)
    zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].      (* [comment removed for export] *)
    exact KONT.
  - assert (KJ : k < j) by lia.
    assert (PB : 0 <= Z.land (h + k) 8191 < 8192) by (change 8191 with (Z.ones 13); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    pose proof (LIVE k ltac:(lia)) as LK.
    zstep. rewrite land_mod64 by (clear; lia).             (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    remember (fs + 20480 + Z.land (h + k) 8191) as fa eqn:EFA.
    assert (FAB : fs + 20480 <= fa < fs + 28672) by (subst fa; clear -PB; lia).
    zstep; rewrite zxb_lit by (clear; lia).             (* [comment removed for export] *)
    zstep. if_cases Kd; zify_cond Kd; [exfalso; clear - Kd; lia|].      (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    setreg 10 (Z_to_bv 64 (8192 - (k + 1))) ltac:(rewrite swrap32_smallF by (clear -K0 KJ J128; lia); f_equal; clear; lia).
    zstep.                                              (* [comment removed for export] *)
    setreg 12 (Z_to_bv 64 (h + (k + 1))) ltac:(f_equal; clear; lia).
    zstep. if_cases Ke; zify_cond Ke; [| exfalso; rewrite ?Z.mod_small in Ke by (clear -K0 KJ J128; lia); clear -Ke K0 KJ J128; lia].      (* [comment removed for export] *)
    subst fa.
    eapply (IH (k + 1) j fs h); try eassumption; try (clear -HD K0 KJ; lia).
    intros i Hi. apply LIVE. clear -Hi. lia.
Qed.

#[using="Type"] Lemma stack_malloc1_cspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h j pos flag F : Z) (j24 j120 sh0 sh1 : word),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->     (* [comment removed for export] *)
  (* [comment removed for export] *)
  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->            (* [comment removed for export] *)
  rw_cells asegs m (fs + 8) [C8 (Z_to_bv 64 h)] -> 0 <= h < 2^64 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells asegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  0 <= j < 8192 ->
  (forall k, 0 <= k < j -> rw_cells asegs m (fs + 20480 + Z.land (h + k) 8191) [C1 (Z_to_bv 8 1)]) ->
  pos = Z.land (h + j) 8191 -> flag = fs + 20480 + pos -> F = fs + 1085440 + pos * 128 ->
  rw_cells asegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (F + 24) [C8 j24] -> rw_cells asegs m (F + 120) [C8 j120] ->
  rw_cells asegs m (shad F) [C8 sh0; C8 sh1] ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (sm1_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs h j flag F m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC1) fc None m (seg_rom asegs)).
Proof.
  intros until sh1.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY C0 C1 T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC JB LIVE POS FLAG FF FL0 F24 F120 SH0
         RIMG RTLS RSTK RCTX RT RB RFS RSH.
  (pose proof (ablk_lin _ _ FLO) as ndP__; nd_pre ndP__ 4%nat; intros FLOL _ _ _; nd_post). unfold AIMG_HI in FLOL.   (* [comment removed for export] *)
  pose proof TC as TC0. (nd_pre TC 12%nat; intros REAL DESC DTVP DTV1 G50 CF GB0 VERB G08 DV BD (tb & te & T48); nd_post).
  pose proof (munch_refl (sm1_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm1_W in MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC1 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 8192).
  { subst pos. change 8191 with (Z.ones 13). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 16 <= fs \/ fs + 11571200 <= shad F).   (* [comment removed for export] *)
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  (* [comment removed for export] *)
  assert (LDJ : forall i, 0 <= i < j -> disjoint_from (sm1_W (bv_unsigned sp) fs flag F) (fs + 20480 + Z.land (h + i) 8191) 1).
  { intros i Hi. unfold sm1_W. cbn [disjoint_from fst snd].
    assert (PI : 0 <= Z.land (h + i) 8191 < 8192 /\ Z.land (h + i) 8191 <> pos).
    { subst pos. change 8191 with (Z.ones 13). rewrite !Z.land_ones by lia. change (2^13) with 8192. clear -Hi JB. Z.div_mod_to_equations. lia. }
    clear -PI PB FLAG FF LO CEIL LO0 SHD FLOL FHI. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.                               (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  box RCTX; box RT; box RB.   (* [comment removed for export] *)
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | exact RTLS | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].   (* [comment removed for export] *)
  zstep; rewrite zxb_lit by lia.            (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].      (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep; lits.                              (* [comment removed for export] *)
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].      (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.               (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (8192 - 0)) ltac:(reflexivity). setreg 12 (Z_to_bv 64 (h + 0)) ltac:(f_equal; clear; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LIVE' : forall i, 0 <= i < j -> rw_cells asegs mm (fs + 20480 + Z.land (h + i) 8191) [Cells.C1 (Z_to_bv 8 1)])
      by (intros i Hi; eapply rw_cells_transport; [exact (LIVE i Hi) | exact MU | exact WM | exact (LDJ i Hi)]) end.
  eapply (sm1_probe RNG _ (Z.to_nat j) 0 j fs h); try eassumption; try (clear -JB HB FLOL FHI; lia).
  { rewrite <- POS, <- FLAG. exact FL0. }
  rewrite <- POS, <- FLAG.
  (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (fs + 36864 + (1048576 + Z.shiftl pos 7))] =>
    replace (fs + 36864 + (1048576 + Z.shiftl pos 7)) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^7) with 128; lia) end.
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)   (* [comment removed for export] *)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  assert (RSF : rng RNG (shad F) 16).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep. zstep.                             (* [comment removed for export] *)
  do 6 zstep.                               (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.
End CANSEC1.
End TwB.
End AFake_sm1.

(* [comment removed for export] *)
Module AFake_sm7.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_tlsga OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_m2s_b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFakeProbe. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFakeProbe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition ASTKMALLOC7 : Z := 0x3f57c.
Definition SM7_STACK : Z := 224.

(* [comment removed for export] *)
Definition sm7_W (sp fs flag F size : Z) : list (Z * Z) :=
  [(sp - 224, sp); (fs + 56, fs + 64); (flag, flag + 1); (F + 24, F + 32); (F + 8184, F + 8192); (shad F, shad F + shlen size)].

Definition sm7_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs h j flag F size : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sm7_W (bv_unsigned sp) fs flag F size) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (fs + 56) [C8 (Z_to_bv 64 (h + j + 1))]
    /\ rw_cells asegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells asegs m' (F + 24) [C8 sp]
    /\ rw_cells asegs m' (F + 8184) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells asegs m' (shad F) [CB (Z.to_nat (shlen size)) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen size)))].

(* [comment removed for export] *)
#[using="Type"] Lemma sm7_probe : forall RNG (Q : machine_state -> Prop) (d : nat) (k j fs h : Z)
    (x1 x2 gp tp x5 x6 x7 x8 x9 x11 x13 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) fc (m1 : amem),
  Z.of_nat d = j - k -> 0 <= k -> j < 128 -> 0 <= h < 2^64 ->
  mem_inv asegs m1 -> 0 <= fs -> fs + 11571200 <= 2^64 -> rng RNG fs 11571200 ->
  (forall i, k <= i < j -> rw_cells asegs m1 (fs + 36608 + Z.land (h + i) 127) [C1 (Z_to_bv 8 1)]) ->
  rw_cells asegs m1 (fs + 36608 + Z.land (h + j) 127) [C1 (Z_to_bv 8 0)] ->
  evtF asegs RNG Q
    (MS (mkR x1 x2 gp tp (Z_to_bv 64 0) x6 x7 x8 x9 (Z_to_bv 64 (128 - j)) x11 (Z_to_bv 64 (h + j)) (Z_to_bv 64 (fs + 36608 + Z.land (h + j) 127))
             (Z_to_bv 64 (fs + 36608)) (Z_to_bv 64 127) x16 (Z_to_bv 64 (Z.land (h + j) 127)) x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 0x3f664) fc None m1 (seg_rom asegs)) ->
  evtF asegs RNG Q
    (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (128 - k)) x11 (Z_to_bv 64 (h + k)) x13
             (Z_to_bv 64 (fs + 36608)) (Z_to_bv 64 127) x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 0x3f618) fc None m1 (seg_rom asegs)).
Proof.
  intros RNG Q d. induction d as [|d IH]; intros k j fs h x1 x2 gp tp x5 x6 x7 x8 x9 x11 x13 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m1 HD K0 J128 HB MI FS0 FS1 RFS LIVE FREE KONT.
  - assert (k = j) by lia. subst k.
    assert (PB : 0 <= Z.land (h + j) 127 < 128) by (change 127 with (Z.ones 7); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    zstep. rewrite land_mod64 by (clear; lia).             (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    remember (fs + 36608 + Z.land (h + j) 127) as fa eqn:EFA.      (* [comment removed for export] *)
    assert (FAB : fs + 36608 <= fa < fs + 36736) by (subst fa; clear -PB; lia).
    zstep; rewrite zxb_lit by (clear; lia).             (* [comment removed for export] *)
    zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].      (* [comment removed for export] *)
    exact KONT.
  - assert (KJ : k < j) by lia.
    assert (PB : 0 <= Z.land (h + k) 127 < 128) by (change 127 with (Z.ones 7); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    pose proof (LIVE k ltac:(lia)) as LK.
    zstep. rewrite land_mod64 by (clear; lia).             (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    remember (fs + 36608 + Z.land (h + k) 127) as fa eqn:EFA.
    assert (FAB : fs + 36608 <= fa < fs + 36736) by (subst fa; clear -PB; lia).
    zstep; rewrite zxb_lit by (clear; lia).             (* [comment removed for export] *)
    zstep. if_cases Kd; zify_cond Kd; [exfalso; clear - Kd; lia|].      (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    setreg 10 (Z_to_bv 64 (128 - (k + 1))) ltac:(rewrite swrap32_smallF by (clear -K0 KJ J128; lia); f_equal; clear; lia).
    zstep.                                              (* [comment removed for export] *)
    setreg 12 (Z_to_bv 64 (h + (k + 1))) ltac:(f_equal; clear; lia).
    zstep. if_cases Ke; zify_cond Ke; [| exfalso; rewrite ?Z.mod_small in Ke by (clear -K0 KJ J128; lia); clear -Ke K0 KJ J128; lia].      (* [comment removed for export] *)
    subst fa.
    eapply (IH (k + 1) j fs h); try eassumption; try (clear -HD K0 KJ; lia).
    intros i Hi. apply LIVE. clear -Hi. lia.
Qed.

#[using="Type"] Lemma stack_malloc7_cspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h j pos flag F size : Z) (j24 j8184 : word) (shj : list byte),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 224 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 size ->
  (* [comment removed for export] *)
  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  poison_cells m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->
  (* [comment removed for export] *)
  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells asegs m (fs + 56) [C8 (Z_to_bv 64 h)] -> 0 <= h < 2^64 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells asegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  0 <= j < 128 ->
  (forall k, 0 <= k < j -> rw_cells asegs m (fs + 36608 + Z.land (h + k) 127) [C1 (Z_to_bv 8 1)]) ->
  pos = Z.land (h + j) 127 -> flag = fs + 36608 + pos -> F = fs + 7376896 + pos * 8192 ->
  rw_cells asegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (F + 24) [C8 j24] -> rw_cells asegs m (F + 8184) [C8 j8184] ->
  size mod 8 = 0 -> 0 < size <= 8192 ->
  rw_cells asegs m (shad F) [CB (Z.to_nat (shlen size)) shj] ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (sm7_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs h j flag F size m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC7) fc None m (seg_rom asegs)).
Proof.
  intros until shj.
  intros MI ST LO CEIL TP -> INI TI TK T88 TSD CT TC PC C0 C1 T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC JB LIVE POS FLAG FF FL0 F24 F8184 SAL SPOS SHJ
         RIMG RTLS RSTK RCTX RT RB RFS RSH.
  (pose proof (ablk_lin _ _ FLO) as ndP__; nd_pre ndP__ 4%nat; intros FLOL _ _ _; nd_post). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. (nd_pre TC 12%nat; intros REAL DESC DTVP DTV1 G50 CF GB0 VERB G08 DV BD (tb & te & T48); nd_post).
  pose proof PC as PC0. (nd_pre PC0 7%nat; intros GOT GOTMS REALM SHB LAY CANP THR; nd_post).
  pose proof (munch_refl (sm7_W (bv_unsigned sp) fs flag F size) m) as MU. unfold sm7_W in MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC7 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 128).
  { subst pos. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHL : shlen size = size / 8) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  pose proof atop_range as ATR.
  assert (SHD : shad F + shlen size <= fs \/ fs + 11571200 <= shad F).   (* [comment removed for export] *)
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. rewrite SHF, SHL. clear - FLOB FHI FF PB ATR SPOS. Z.div_mod_to_equations. lia. }
  assert (SHR : 0x800b8600 <= shad F /\ shad F + shlen size <= 0x10007fff8000).
  { rewrite SHF, SHL. clear -FLOL FHI FF PB ATR SPOS. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (LDJ : forall i, 0 <= i < j -> disjoint_from (sm7_W (bv_unsigned sp) fs flag F size) (fs + 36608 + Z.land (h + i) 127) 1).
  { intros i Hi. unfold sm7_W. cbn [disjoint_from fst snd].
    assert (PI : 0 <= Z.land (h + i) 127 < 128 /\ Z.land (h + i) 127 <> pos).
    { subst pos. change 127 with (Z.ones 7). rewrite !Z.land_ones by lia. change (2^7) with 128. clear -Hi JB. Z.div_mod_to_equations. lia. }
    clear -PI PB FLAG FF LO CEIL LO0 SHD FLOL FHI. lia. }
  carve_frame 48%nat ST.
  do 6 zstep.                               (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | exact RTLS | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].   (* [comment removed for export] *)
  zstep; rewrite zxb_lit by lia.            (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].      (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep; lits.                              (* [comment removed for export] *)
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].      (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.               (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (128 - 0)) ltac:(reflexivity). setreg 12 (Z_to_bv 64 (h + 0)) ltac:(f_equal; clear; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LIVE' : forall i, 0 <= i < j -> rw_cells asegs mm (fs + 36608 + Z.land (h + i) 127) [Cells.C1 (Z_to_bv 8 1)])
      by (intros i Hi; eapply rw_cells_transport; [exact (LIVE i Hi) | exact MU | exact WM | exact (LDJ i Hi)]) end.
  eapply (sm7_probe RNG _ (Z.to_nat j) 0 j fs h); try eassumption; try (clear -JB HB FLOL FHI; lia).
  { rewrite <- POS, <- FLAG. exact FL0. }
  rewrite <- POS, <- FLAG.
  (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (fs + 36864 + (7340032 + Z.shiftl pos 13))] =>
    replace (fs + 36864 + (7340032 + Z.shiftl pos 13)) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^13) with 8192; lia) end.
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  assert (RSF : rng RNG (shad F) (shlen size)).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF, SHL. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB SPOS SAL. Z.div_mod_to_equations. lia. }
  assert (FBLK : ablk F (F + size)) by (eapply ablk_sub; [exact FLO | clear -FF PB; lia | clear -FF PB SPOS; lia]).
  zstep.                                    (* [comment removed for export] *)
  call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F size 0 lo shj);
    first [ eassumption | reflexivity
          | (unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split | |- rt_got _ => assumption | |- rt_real_mem _ => assumption | |- rt_shbase _ => assumption | |- rt_layout _ => assumption end))
          | idtac ].
  1: (clear -LO; lia).
  1: (clear -FF FAL; Z.div_mod_to_equations; lia).
  1: (clear -SPOS; lia).
  1: (clear -FHI FF PB SPOS ATR; lia).
  1: (clear; lia). 1: (clear; lia).
  1: (intros _; rewrite SHL; clear -SPOS; Z.div_mod_to_equations; lia).
  zstep.                                    (* [comment removed for export] *)
  do 7 zstep.                               (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_tlsga.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_m2s_b.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFakeProbe.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition ASTKMALLOC7 : Z := 0x3f5e4.
Definition SM7_STACK : Z := 224.

(* [comment removed for export] *)
Definition sm7_W (sp fs flag F size : Z) : list (Z * Z) :=
  [(sp - 224, sp); (fs + 56, fs + 64); (flag, flag + 1); (F + 24, F + 32); (F + 8184, F + 8192); (shad F, shad F + shlen size)].

Definition sm7_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs h j flag F size : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sm7_W (bv_unsigned sp) fs flag F size) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (fs + 56) [C8 (Z_to_bv 64 (h + j + 1))]
    /\ rw_cells asegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells asegs m' (F + 24) [C8 sp]
    /\ rw_cells asegs m' (F + 8184) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells asegs m' (shad F) [CB (Z.to_nat (shlen size)) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen size)))].

(* [comment removed for export] *)
#[using="Type"] Lemma sm7_probe : forall RNG (Q : machine_state -> Prop) (d : nat) (k j fs h : Z)
    (x1 x2 gp tp x5 x6 x7 x8 x9 x11 x13 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) fc (m1 : amem),
  Z.of_nat d = j - k -> 0 <= k -> j < 128 -> 0 <= h < 2^64 ->
  mem_inv asegs m1 -> 0 <= fs -> fs + 11571200 <= 2^64 -> rng RNG fs 11571200 ->
  (forall i, k <= i < j -> rw_cells asegs m1 (fs + 36608 + Z.land (h + i) 127) [C1 (Z_to_bv 8 1)]) ->
  rw_cells asegs m1 (fs + 36608 + Z.land (h + j) 127) [C1 (Z_to_bv 8 0)] ->
  evtF asegs RNG Q
    (MS (mkR x1 x2 gp tp (Z_to_bv 64 0) x6 x7 x8 x9 (Z_to_bv 64 (128 - j)) x11 (Z_to_bv 64 (h + j)) (Z_to_bv 64 (fs + 36608 + Z.land (h + j) 127))
             (Z_to_bv 64 (fs + 36608)) (Z_to_bv 64 127) x16 (Z_to_bv 64 (Z.land (h + j) 127)) x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 0x3f6cc) fc None m1 (seg_rom asegs)) ->
  evtF asegs RNG Q
    (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (128 - k)) x11 (Z_to_bv 64 (h + k)) x13
             (Z_to_bv 64 (fs + 36608)) (Z_to_bv 64 127) x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 0x3f680) fc None m1 (seg_rom asegs)).
Proof.
  intros RNG Q d. induction d as [|d IH]; intros k j fs h x1 x2 gp tp x5 x6 x7 x8 x9 x11 x13 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m1 HD K0 J128 HB MI FS0 FS1 RFS LIVE FREE KONT.
  - assert (k = j) by lia. subst k.
    assert (PB : 0 <= Z.land (h + j) 127 < 128) by (change 127 with (Z.ones 7); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    zstep. rewrite land_mod64 by (clear; lia).             (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    remember (fs + 36608 + Z.land (h + j) 127) as fa eqn:EFA.      (* [comment removed for export] *)
    assert (FAB : fs + 36608 <= fa < fs + 36736) by (subst fa; clear -PB; lia).
    zstep; rewrite zxb_lit by (clear; lia).             (* [comment removed for export] *)
    zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].      (* [comment removed for export] *)
    exact KONT.
  - assert (KJ : k < j) by lia.
    assert (PB : 0 <= Z.land (h + k) 127 < 128) by (change 127 with (Z.ones 7); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    pose proof (LIVE k ltac:(lia)) as LK.
    zstep. rewrite land_mod64 by (clear; lia).             (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    remember (fs + 36608 + Z.land (h + k) 127) as fa eqn:EFA.
    assert (FAB : fs + 36608 <= fa < fs + 36736) by (subst fa; clear -PB; lia).
    zstep; rewrite zxb_lit by (clear; lia).             (* [comment removed for export] *)
    zstep. if_cases Kd; zify_cond Kd; [exfalso; clear - Kd; lia|].      (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    setreg 10 (Z_to_bv 64 (128 - (k + 1))) ltac:(rewrite swrap32_smallF by (clear -K0 KJ J128; lia); f_equal; clear; lia).
    zstep.                                              (* [comment removed for export] *)
    setreg 12 (Z_to_bv 64 (h + (k + 1))) ltac:(f_equal; clear; lia).
    zstep. if_cases Ke; zify_cond Ke; [| exfalso; rewrite ?Z.mod_small in Ke by (clear -K0 KJ J128; lia); clear -Ke K0 KJ J128; lia].      (* [comment removed for export] *)
    subst fa.
    eapply (IH (k + 1) j fs h); try eassumption; try (clear -HD K0 KJ; lia).
    intros i Hi. apply LIVE. clear -Hi. lia.
Qed.

#[using="Type"] Lemma stack_malloc7_cspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h j pos flag F size : Z) (j24 j8184 : word) (shj : list byte),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 224 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 size ->
  (* [comment removed for export] *)
  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  poison_cells m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->
  (* [comment removed for export] *)
  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells asegs m (fs + 56) [C8 (Z_to_bv 64 h)] -> 0 <= h < 2^64 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells asegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  0 <= j < 128 ->
  (forall k, 0 <= k < j -> rw_cells asegs m (fs + 36608 + Z.land (h + k) 127) [C1 (Z_to_bv 8 1)]) ->
  pos = Z.land (h + j) 127 -> flag = fs + 36608 + pos -> F = fs + 7376896 + pos * 8192 ->
  rw_cells asegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (F + 24) [C8 j24] -> rw_cells asegs m (F + 8184) [C8 j8184] ->
  size mod 8 = 0 -> 0 < size <= 8192 ->
  rw_cells asegs m (shad F) [CB (Z.to_nat (shlen size)) shj] ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (sm7_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs h j flag F size m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC7) fc None m (seg_rom asegs)).
Proof.
  intros until shj.
  intros MI ST LO CEIL TP -> INI TI TK T88 TSD CT TC PC C0 C1 T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC JB LIVE POS FLAG FF FL0 F24 F8184 SAL SPOS SHJ
         RIMG RTLS RSTK RCTX RT RB RFS RSH.
  (pose proof (ablk_lin _ _ FLO) as ndP__; nd_pre ndP__ 4%nat; intros FLOL _ _ _; nd_post). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. (nd_pre TC 12%nat; intros REAL DESC DTVP DTV1 G50 CF GB0 VERB G08 DV BD (tb & te & T48); nd_post).
  pose proof PC as PC0. (nd_pre PC0 7%nat; intros GOT GOTMS REALM SHB LAY CANP THR; nd_post).
  pose proof (munch_refl (sm7_W (bv_unsigned sp) fs flag F size) m) as MU. unfold sm7_W in MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC7 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 128).
  { subst pos. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHL : shlen size = size / 8) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  pose proof atop_range as ATR.
  assert (SHD : shad F + shlen size <= fs \/ fs + 11571200 <= shad F).   (* [comment removed for export] *)
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. rewrite SHF, SHL. clear - FLOB FHI FF PB ATR SPOS. Z.div_mod_to_equations. lia. }
  assert (SHR : 0x800b8800 <= shad F /\ shad F + shlen size <= 0x10007fff8000).
  { rewrite SHF, SHL. clear -FLOL FHI FF PB ATR SPOS. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (LDJ : forall i, 0 <= i < j -> disjoint_from (sm7_W (bv_unsigned sp) fs flag F size) (fs + 36608 + Z.land (h + i) 127) 1).
  { intros i Hi. unfold sm7_W. cbn [disjoint_from fst snd].
    assert (PI : 0 <= Z.land (h + i) 127 < 128 /\ Z.land (h + i) 127 <> pos).
    { subst pos. change 127 with (Z.ones 7). rewrite !Z.land_ones by lia. change (2^7) with 128. clear -Hi JB. Z.div_mod_to_equations. lia. }
    clear -PI PB FLAG FF LO CEIL LO0 SHD FLOL FHI. lia. }
  carve_frame 48%nat ST.
  do 6 zstep.                               (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | exact RTLS | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].   (* [comment removed for export] *)
  zstep; rewrite zxb_lit by lia.            (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].      (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep; lits.                              (* [comment removed for export] *)
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].      (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.               (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (128 - 0)) ltac:(reflexivity). setreg 12 (Z_to_bv 64 (h + 0)) ltac:(f_equal; clear; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LIVE' : forall i, 0 <= i < j -> rw_cells asegs mm (fs + 36608 + Z.land (h + i) 127) [Cells.C1 (Z_to_bv 8 1)])
      by (intros i Hi; eapply rw_cells_transport; [exact (LIVE i Hi) | exact MU | exact WM | exact (LDJ i Hi)]) end.
  eapply (sm7_probe RNG _ (Z.to_nat j) 0 j fs h); try eassumption; try (clear -JB HB FLOL FHI; lia).
  { rewrite <- POS, <- FLAG. exact FL0. }
  rewrite <- POS, <- FLAG.
  (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (fs + 36864 + (7340032 + Z.shiftl pos 13))] =>
    replace (fs + 36864 + (7340032 + Z.shiftl pos 13)) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^13) with 8192; lia) end.
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  assert (RSF : rng RNG (shad F) (shlen size)).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF, SHL. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB SPOS SAL. Z.div_mod_to_equations. lia. }
  assert (FBLK : ablk F (F + size)) by (eapply ablk_sub; [exact FLO | clear -FF PB; lia | clear -FF PB SPOS; lia]).
  zstep.                                    (* [comment removed for export] *)
  call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F size 0 lo shj);
    first [ eassumption | reflexivity
          | (unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split | |- rt_got _ => assumption | |- rt_real_mem _ => assumption | |- rt_shbase _ => assumption | |- rt_layout _ => assumption end))
          | idtac ].
  1: (clear -LO; lia).
  1: (clear -FF FAL; Z.div_mod_to_equations; lia).
  1: (clear -SPOS; lia).
  1: (clear -FHI FF PB SPOS ATR; lia).
  1: (clear; lia). 1: (clear; lia).
  1: (intros _; rewrite SHL; clear -SPOS; Z.div_mod_to_equations; lia).
  zstep.                                    (* [comment removed for export] *)
  do 7 zstep.                               (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.
End CANSEC1.
End TwB.
End AFake_sm7.
