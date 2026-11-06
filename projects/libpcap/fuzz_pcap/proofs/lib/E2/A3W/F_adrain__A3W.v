(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StrwF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanEmbed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_adrain.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.
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
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition drain_post (gfull : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb gnb gfst glst gqb lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (t + 80, t + 112); (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32); (glst, glst + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0xab308 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0xab310 [C8 (Z_to_bv 64 (gnb + nb)); C8 (Z_to_bv 64 (if gfull then gfst else fst)); C8 (Z_to_bv 64 lst);
                                   C8 (Z_to_bv 64 (gqb + qb))]
    /\ (if gfull then rw_cells asegs m' glst [C8 (Z_to_bv 64 fst)] else True).

Definition drain_norecycle_spec__stmt : Prop := forall (gfull : bool) (t glst : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst lst qb gnb gfst gqb gnx lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 (t + 80) ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 < nb < 2^63 -> 0 <= qb -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  rw_cells asegs m AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m AQ_GCACHE [C8 (Z_to_bv 64 gnb); C8 (Z_to_bv 64 gfst); C8 (Z_to_bv 64 glst); C8 (Z_to_bv 64 gqb)] ->
  0 <= gnb < 2^62 -> 0 <= gqb -> gqb + qb <= Q_MAX -> 0 <= gfst < 2^64 -> 0 <= glst < 2^64 ->
  rw_cells asegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX)] ->
  (if gfull then 0 < gnb /\ rw_cells asegs m glst [C8 (Z_to_bv 64 gnx)] /\ AIMG_HI <= glst /\ glst + Q_BATCH_BYTES <= ATOP
                 /\ (t + 4096 <= glst \/ glst + Q_BATCH_BYTES <= t)
   else gnb = 0) ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> (if gfull then rng RNG glst Q_BATCH_BYTES else True) ->
  evtF asegs RNG (drain_post gfull ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t nb fst lst qb gnb gfst glst gqb lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x358fc) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable gfull : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 0).
Variable t : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 1).
Variable glst : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 2).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 37).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 38).
Variable fst : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 39).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 40).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 41).
Variable gnb : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 42).
Variable gfst : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 43).
Variable gqb : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 44).
Variable gnx : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 45).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 46).
#[using="Type"] Lemma drain_norecycle_spec__body : ltac:(let T := type of (fun (h : drain_norecycle_spec__stmt) => h gfull t glst RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nb fst lst qb gnb gfst gqb gnx lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (gfull, (t, (glst, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (nb, (fst, (lst, (qb, (gnb, (gfst, (gqb, (gnx, lo))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> QC NB QB FST LST MX GC GNB GQB GQ GFST GLST QM GFULL T0 T1 RIMG RTLS RSTK RT RGL. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH_BYTES, Q_MAX, AQUAR_Q, AQ_MUTEX, AQ_GCACHE, AQ_MAX, AINSTANCE in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 80, t + 112); (0xab308, 0xab308 + 4);
                          (0xab310, 0xab310 + 32); (glst, glst + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 48%nat ST.
  destruct gfull.
  - (nd_pre GFULL 5%nat; intros GNB1 GLB GL0 GL1 DTG; nd_post).
    do 6 step.                                 (* [comment removed for export] *)
    zstep. step. zstep. step.                  (* [comment removed for export] *)
    apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in MX. change (0 + 256 * 0) with 0 in MX.
    amo_step. lits.                            (* [comment removed for export] *)
    do 4 zstep.                                (* [comment removed for export] *)
    amo_step.                                  (* [comment removed for export] *)
    step. if_lit.                              (* [comment removed for export] *)
    zstep. step. if_lit.                       (* [comment removed for export] *)
    zstep. step. if_cases K0; zify_cond K0; [exfalso; lia|].   (* [comment removed for export] *)
    step. step. if_cases K1; zify_cond K1; [exfalso; lia|].    (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2; [exfalso; lia|].    (* [comment removed for export] *)
    step. step. step. zstep.                   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    step. step. step.                          (* [comment removed for export] *)
    step. step. zstep. step. step.             (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    apply (rw_C4_to_C1x4 _ _ 1 0 ltac:(lia) ltac:(lia)) in MX.
    step.                                      (* [comment removed for export] *)
    step. step. step. if_cases K3; zify_cond K3; [|exfalso; lia].   (* [comment removed for export] *)
    do 7 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold drain_post. finish.
  - pose proof GFULL as GNB0. clear GFULL.
    do 6 step.                                 (* [comment removed for export] *)
    zstep. step. zstep. step.                  (* [comment removed for export] *)
    apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in MX. change (0 + 256 * 0) with 0 in MX.
    amo_step. lits.                            (* [comment removed for export] *)
    do 4 zstep.                                (* [comment removed for export] *)
    amo_step.                                  (* [comment removed for export] *)
    step. if_lit.                              (* [comment removed for export] *)
    zstep. step. if_lit.                       (* [comment removed for export] *)
    zstep. step. if_cases K0; zify_cond K0; [exfalso; lia|].   (* [comment removed for export] *)
    step. step. if_cases K1; zify_cond K1; [exfalso; lia|].    (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2; [|exfalso; lia].    (* [comment removed for export] *)
    step. step. step. step. step. step.        (* [comment removed for export] *)
    step. step. step.                          (* [comment removed for export] *)
    step. step. zstep. step. step.             (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    apply (rw_C4_to_C1x4 _ _ 1 0 ltac:(lia) ltac:(lia)) in MX.
    step.                                      (* [comment removed for export] *)
    step. step. step. if_cases K3; zify_cond K3; [|exfalso; lia].   (* [comment removed for export] *)
    do 7 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold drain_post. finish.
    subst gnb. exact GC.
Qed.
End Zd1.
#[using="Type"] Lemma drain_norecycle_spec : ltac:(let t := eval cbv delta [drain_norecycle_spec__stmt] in drain_norecycle_spec__stmt in exact t).
Proof. exact drain_norecycle_spec__body. Qed.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
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
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition drain_post (gfull : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb gnb gfst glst gqb lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (t + 80, t + 112); (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32); (glst, glst + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0xab708 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0xab710 [C8 (Z_to_bv 64 (gnb + nb)); C8 (Z_to_bv 64 (if gfull then gfst else fst)); C8 (Z_to_bv 64 lst);
                                   C8 (Z_to_bv 64 (gqb + qb))]
    /\ (if gfull then rw_cells asegs m' glst [C8 (Z_to_bv 64 fst)] else True).

Definition drain_norecycle_spec__stmt : Prop := forall (gfull : bool) (t glst : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst lst qb gnb gfst gqb gnx lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 (t + 80) ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 < nb < 2^63 -> 0 <= qb -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  rw_cells asegs m AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m AQ_GCACHE [C8 (Z_to_bv 64 gnb); C8 (Z_to_bv 64 gfst); C8 (Z_to_bv 64 glst); C8 (Z_to_bv 64 gqb)] ->
  0 <= gnb < 2^62 -> 0 <= gqb -> gqb + qb <= Q_MAX -> 0 <= gfst < 2^64 -> 0 <= glst < 2^64 ->
  rw_cells asegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX)] ->
  (if gfull then 0 < gnb /\ rw_cells asegs m glst [C8 (Z_to_bv 64 gnx)] /\ AIMG_HI <= glst /\ glst + Q_BATCH_BYTES <= ATOP
                 /\ (t + 4096 <= glst \/ glst + Q_BATCH_BYTES <= t)
   else gnb = 0) ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> (if gfull then rng RNG glst Q_BATCH_BYTES else True) ->
  evtF asegs RNG (drain_post gfull ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t nb fst lst qb gnb gfst glst gqb lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x35964) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable gfull : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 0).
Variable t : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 1).
Variable glst : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 2).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 37).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 38).
Variable fst : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 39).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 40).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 41).
Variable gnb : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 42).
Variable gfst : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 43).
Variable gqb : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 44).
Variable gnx : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 45).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'drain_norecycle_spec__stmt 46).
#[using="Type"] Lemma drain_norecycle_spec__body : ltac:(let T := type of (fun (h : drain_norecycle_spec__stmt) => h gfull t glst RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nb fst lst qb gnb gfst gqb gnx lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (gfull, (t, (glst, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (nb, (fst, (lst, (qb, (gnb, (gfst, (gqb, (gnx, lo))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> QC NB QB FST LST MX GC GNB GQB GQ GFST GLST QM GFULL T0 T1 RIMG RTLS RSTK RT RGL. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH_BYTES, Q_MAX, AQUAR_Q, AQ_MUTEX, AQ_GCACHE, AQ_MAX, AINSTANCE in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 80, t + 112); (0xab708, 0xab708 + 4);
                          (0xab710, 0xab710 + 32); (glst, glst + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 48%nat ST.
  destruct gfull.
  - (nd_pre GFULL 5%nat; intros GNB1 GLB GL0 GL1 DTG; nd_post).
    do 6 step.                                 (* [comment removed for export] *)
    zstep. step. zstep. step.                  (* [comment removed for export] *)
    apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in MX. change (0 + 256 * 0) with 0 in MX.
    amo_step. lits.                            (* [comment removed for export] *)
    do 4 zstep.                                (* [comment removed for export] *)
    amo_step.                                  (* [comment removed for export] *)
    step. if_lit.                              (* [comment removed for export] *)
    zstep. step. if_lit.                       (* [comment removed for export] *)
    zstep. step. if_cases K0; zify_cond K0; [exfalso; lia|].   (* [comment removed for export] *)
    step. step. if_cases K1; zify_cond K1; [exfalso; lia|].    (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2; [exfalso; lia|].    (* [comment removed for export] *)
    step. step. step. zstep.                   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    step. step. step.                          (* [comment removed for export] *)
    step. step. zstep. step. step.             (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    apply (rw_C4_to_C1x4 _ _ 1 0 ltac:(lia) ltac:(lia)) in MX.
    step.                                      (* [comment removed for export] *)
    step. step. step. if_cases K3; zify_cond K3; [|exfalso; lia].   (* [comment removed for export] *)
    do 7 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold drain_post. finish.
  - pose proof GFULL as GNB0. clear GFULL.
    do 6 step.                                 (* [comment removed for export] *)
    zstep. step. zstep. step.                  (* [comment removed for export] *)
    apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in MX. change (0 + 256 * 0) with 0 in MX.
    amo_step. lits.                            (* [comment removed for export] *)
    do 4 zstep.                                (* [comment removed for export] *)
    amo_step.                                  (* [comment removed for export] *)
    step. if_lit.                              (* [comment removed for export] *)
    zstep. step. if_lit.                       (* [comment removed for export] *)
    zstep. step. if_cases K0; zify_cond K0; [exfalso; lia|].   (* [comment removed for export] *)
    step. step. if_cases K1; zify_cond K1; [exfalso; lia|].    (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2; [|exfalso; lia].    (* [comment removed for export] *)
    step. step. step. step. step. step.        (* [comment removed for export] *)
    step. step. step.                          (* [comment removed for export] *)
    step. step. zstep. step. step.             (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    apply (rw_C4_to_C1x4 _ _ 1 0 ltac:(lia) ltac:(lia)) in MX.
    step.                                      (* [comment removed for export] *)
    step. step. step. if_cases K3; zify_cond K3; [|exfalso; lia].   (* [comment removed for export] *)
    do 7 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold drain_post. finish.
    subst gnb. exact GC.
Qed.
End Zd1.
#[using="Type"] Lemma drain_norecycle_spec : ltac:(let t := eval cbv delta [drain_norecycle_spec__stmt] in drain_norecycle_spec__stmt in exact t).
Proof. exact drain_norecycle_spec__body. Qed.

End CANSEC1.
End TwB.
End F_adrain.

(* [comment removed for export] *)
Module F_aenqueue.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.
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
Notation acache24 t := (t + 2128) (only parsing).       (* [comment removed for export] *)
Notation acache_stats t := (t + 2784) (only parsing).

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition enq_new_post (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb hm n nx bsz cnt24 b lo : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (t + 80, t + 112); (acache24 t, acache24 t + 4); (acache_stats t, acache_stats t + 8);
              (lst, lst + 8); (b, b + 8192)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 (nb + 1)); C8 (Z_to_bv 64 (if full then fst else b)); C8 (Z_to_bv 64 b);
                                 C8 (Z_to_bv 64 (qb + (n + 8192)))]
    /\ rw_cells asegs m' (acache24 t) [C4 (Z_to_bv 64 (cnt24 - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells asegs m' (acache_stats t) [C8 stj'])
    /\ rw_cells asegs m' b [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (n + 8192)); C8 (Z_to_bv 64 1)]
    /\ u64arr asegs m' (b + 24) [Z_to_bv 64 hm]
    /\ (exists bs, rw_cells asegs m' (b + 24 + 8 * 1) [CB (Z.to_nat (8192 - 24 - 8 * 1)) bs])
    /\ (if full then rw_cells asegs m' lst [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] else True).

Definition enqueue_new_spec__stmt : Prop := forall (full : bool) (t lst b : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz cnt24 spacebeg lo : Z) (maxc csz stj idxw : word) (chunks : list word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 (t + 80) -> a1 = Z_to_bv 64 (t + 208) -> a3 = Z_to_bv 64 hm -> a4 = Z_to_bv 64 n ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + Q_BATCH_BYTES < 2^63 -> 0 <= n -> 0 <= hm < 2^64 -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 Q_BATCH)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ AIMG_HI <= lst /\ lst + Q_BATCH_BYTES <= ATOP
   else nb = 0) ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (acache24 t) [C4 (Z_to_bv 64 cnt24); C4 maxc; C8 csz] ->
  u32arr asegs m (acache24 t + 16) chunks -> length chunks = 16%nat ->
  0 < cnt24 <= 16 -> nth_error chunks (Z.to_nat (cnt24 - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  b = spacebeg + K_BATCH_CLASS * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat Q_BATCH_BYTES) bs]) ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> 0 < spacebeg -> AIMG_HI <= b -> b + Q_BATCH_BYTES <= ATOP ->
  (t + 4096 <= b \/ b + Q_BATCH_BYTES <= t) -> (t + 4096 <= lst \/ lst + Q_BATCH_BYTES <= t \/ lst = 0) -> (b + Q_BATCH_BYTES <= lst \/ lst + Q_BATCH_BYTES <= b) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG b Q_BATCH_BYTES -> (if full then rng RNG lst Q_BATCH_BYTES else True) ->
  evtF asegs RNG (enq_new_post full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t nb fst lst qb hm n nx bsz cnt24 b lo maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x381a4) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable full : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 0).
Variable t : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 1).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 2).
Variable b : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 3).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 38).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 39).
Variable fst : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 40).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 41).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 42).
Variable n : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 43).
Variable nx : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 44).
Variable bsz : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 45).
Variable cnt24 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 46).
Variable spacebeg : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 47).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 48).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 49).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 50).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 51).
Variable idxw : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 52).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 53).
#[using="Type"] Lemma enqueue_new_spec__body : ltac:(let T := type of (fun (h : enqueue_new_spec__stmt) => h full t lst b RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nb fst qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (full, (t, (lst, (b, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (nb, (fst, (qb, (hm, (n, (nx, (bsz, (cnt24, (spacebeg, (lo, (maxc, (csz, (stj, (idxw, chunks)))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> -> -> QC NB QB QBN N HM FST LST FULL SB CR CH LCH CNT NTH IXS STS HB BJ T0 T1 TAL SBP B0 B1 DTB DTL DBL RIMG RTLS RSTK RT RB RL. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES, K_BATCH_CLASS in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8);
              (lst, lst + 8); (b, b + 8192)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR. word_range idxw IXR.
  destruct BJ as [junkb BJ]. pose proof (stk_of_cb _ _ _ _ BJ ltac:(lia)) as TB. clear BJ junkb.
  carve_frame 64%nat ST.
  destruct full.
  - (* [comment removed for export] *)
    (nd_pre FULL 6%nat; intros NB1 LB NX BSZ L0 L1; nd_post).
    do 8 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. step. step. if_cases K1; zify_cond K1; [exfalso; lia|].   (* [comment removed for export] *)
    (* [comment removed for export] *)
    lstep.                                     (* [comment removed for export] *)
    step. if_cases K2; zify_cond K2; [exfalso; lia|].        (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    replace (Z.shiftr (Z.shiftl (cnt24 + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt24 + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.                        (* [comment removed for export] *)
    pose proof (u32arr_read asegs _ _ chunks (cnt24 + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt24 + -1))) CH ltac:(replace (cnt24 + -1) with (cnt24 - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.        (* [comment removed for export] *)
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
    amo_stepA AMO.                             (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. zstep. zstep. zstep.          (* [comment removed for export] *)
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3; zify_cond K3; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. zstep.                         (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.                    (* [comment removed for export] *)
    step. if_cases K4; zify_cond K4; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. zstep. step.                   (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. step.                         (* [comment removed for export] *)
    do 9 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_new_post. finish.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
  - (* [comment removed for export] *)
    pose proof FULL as NB0. clear FULL.
    do 8 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [|exfalso; lia].        (* [comment removed for export] *)
    (* [comment removed for export] *)
    lstep.                                     (* [comment removed for export] *)
    step. if_cases K2'; zify_cond K2'; [exfalso; lia|].        (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    replace (Z.shiftr (Z.shiftl (cnt24 + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt24 + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.                        (* [comment removed for export] *)
    pose proof (u32arr_read asegs _ _ chunks (cnt24 + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt24 + -1))) CH ltac:(replace (cnt24 + -1) with (cnt24 - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.        (* [comment removed for export] *)
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
    amo_stepA AMO.                             (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. zstep. zstep. zstep.          (* [comment removed for export] *)
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3'; zify_cond K3'; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. zstep.                         (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.                    (* [comment removed for export] *)
    step. if_cases K4; zify_cond K4; [|exfalso; lia].        (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. step.                         (* [comment removed for export] *)
    do 9 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_new_post. finish.
    + subst nb. exact QC.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
Qed.
End Zd1.
#[using="Type"] Lemma enqueue_new_spec : ltac:(let t := eval cbv delta [enqueue_new_spec__stmt] in enqueue_new_spec__stmt in exact t).
Proof. exact enqueue_new_spec__body. Qed.

(* [comment removed for export] *)
Definition enq_append_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (C nb fst lst qb hm n nx bsz cnt lo : Z) (hs : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (C + 24, C + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' C [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 (qb + n))]
    /\ rw_cells asegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 (bsz + n)); C8 (Z_to_bv 64 (cnt + 1))]
    /\ u64arr asegs m' (lst + 24) (hs ++ [Z_to_bv 64 hm])
    /\ (exists bs, rw_cells asegs m' (lst + 24 + 8 * (cnt + 1)) [CB (Z.to_nat (8192 - 24 - 8 * (cnt + 1))) bs]).

#[using="Type"] Lemma enqueue_append_spec : forall (C lst cnt : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz lo : Z) (hs : list word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 C -> a3 = Z_to_bv 64 hm -> a4 = Z_to_bv 64 n ->
  rw_cells asegs m C [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 < nb < 2^63 -> 0 <= qb -> qb + n < 2^63 -> 0 <= n -> 0 <= hm < 2^64 -> 0 <= fst < 2^64 ->
  rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 cnt)] ->
  0 <= cnt < Q_BATCH -> 0 <= bsz -> bsz + n < 2^63 -> 0 <= nx < 2^64 ->
  u64arr asegs m (lst + 24) hs -> length hs = Z.to_nat cnt ->
  (exists bs, rw_cells asegs m (lst + 24 + 8 * cnt) [CB (Z.to_nat (Q_BATCH_BYTES - 24 - 8 * cnt)) bs]) ->
  iclr C 32 -> C + 32 <= ATOP -> AIMG_HI <= lst -> lst + Q_BATCH_BYTES <= ATOP ->        (* [comment removed for export] *)
  (C + 32 <= lst \/ lst + Q_BATCH_BYTES <= C) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG C 32 -> rng RNG lst Q_BATCH_BYTES ->
  evtF asegs RNG (enq_append_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C nb fst lst qb hm n nx bsz cnt lo hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x381a4) fc None m (seg_rom asegs)).
Proof.
  intros until hs. intros ST CEIL LO MI -> -> -> QC NB QB QBN N HM FST LB CNT BSZ BSZN NX LA LEN LJ C0 C1 L0 L1 DJ RIMG RTLS RSTK RC RL. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (C + 24, C + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  destruct LJ as [junkt LJ]. pose proof (stk_of_cb _ _ _ _ LJ ltac:(lia)) as TJ. clear LJ junkt.
  carve_frame 64%nat ST.
  do 8 step.                                   (* [comment removed for export] *)
  step. step. if_cases K0; zify_cond K0; [exfalso; lia|].   (* [comment removed for export] *)
  step. step. step. step. if_cases K1; zify_cond K1; [|exfalso; lia].   (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2; [exfalso; lia|].          (* [comment removed for export] *)
  step. zstep.                                 (* [comment removed for export] *)
  replace (Z.shiftl cnt 3) with (8 * cnt) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep. zstep. zstep.                         (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (stk_split asegs mm (lst + 24 + 8 * cnt) (lst + 24 + 8 * cnt + 8) _ TJ ltac:(lia)) as [TJ0 TJ1];
    destruct (stk_cb mm _ _ TJ0 ltac:(lia)) as [junk8 E8] end.
  clear TJ TJ0. replace (Z.to_nat (lst + 24 + 8 * cnt + 8 - (lst + 24 + 8 * cnt))) with 8%nat in E8 by lia.
  replace (lst + 24 + 8 * cnt) with (lst + 8 * cnt + 24) in E8 by lia.
  step.                                        (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  step. zstep. step.                           (* [comment removed for export] *)
  do 9 step.                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold enq_append_post. finish.
  - eapply u64arr_snoc; [exact LA|]. rewrite LEN. replace (lst + 24 + 8 * Z.of_nat (Z.to_nat cnt)) with (lst + 8 * cnt + 24) by lia. exact E8.
  - lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TJ1 ltac:(lia)) as [bs Hbs] end.
    exists bs. replace (lst + 24 + 8 * cnt + (8192 - 24 - 8 * cnt) - (lst + 24 + 8 * cnt + 8)) with (8192 - 24 - 8 * (cnt + 1)) in Hbs by lia.
    replace (lst + 24 + 8 * cnt + 8) with (lst + 24 + 8 * (cnt + 1)) in Hbs by lia. exact Hbs.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
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
Notation acache24 t := (t + 2128) (only parsing).       (* [comment removed for export] *)
Notation acache_stats t := (t + 2784) (only parsing).

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition enq_new_post (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb hm n nx bsz cnt24 b lo : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (t + 80, t + 112); (acache24 t, acache24 t + 4); (acache_stats t, acache_stats t + 8);
              (lst, lst + 8); (b, b + 8192)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 (nb + 1)); C8 (Z_to_bv 64 (if full then fst else b)); C8 (Z_to_bv 64 b);
                                 C8 (Z_to_bv 64 (qb + (n + 8192)))]
    /\ rw_cells asegs m' (acache24 t) [C4 (Z_to_bv 64 (cnt24 - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells asegs m' (acache_stats t) [C8 stj'])
    /\ rw_cells asegs m' b [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (n + 8192)); C8 (Z_to_bv 64 1)]
    /\ u64arr asegs m' (b + 24) [Z_to_bv 64 hm]
    /\ (exists bs, rw_cells asegs m' (b + 24 + 8 * 1) [CB (Z.to_nat (8192 - 24 - 8 * 1)) bs])
    /\ (if full then rw_cells asegs m' lst [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] else True).

Definition enqueue_new_spec__stmt : Prop := forall (full : bool) (t lst b : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz cnt24 spacebeg lo : Z) (maxc csz stj idxw : word) (chunks : list word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 (t + 80) -> a1 = Z_to_bv 64 (t + 208) -> a3 = Z_to_bv 64 hm -> a4 = Z_to_bv 64 n ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + Q_BATCH_BYTES < 2^63 -> 0 <= n -> 0 <= hm < 2^64 -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 Q_BATCH)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ AIMG_HI <= lst /\ lst + Q_BATCH_BYTES <= ATOP
   else nb = 0) ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (acache24 t) [C4 (Z_to_bv 64 cnt24); C4 maxc; C8 csz] ->
  u32arr asegs m (acache24 t + 16) chunks -> length chunks = 16%nat ->
  0 < cnt24 <= 16 -> nth_error chunks (Z.to_nat (cnt24 - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  b = spacebeg + K_BATCH_CLASS * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat Q_BATCH_BYTES) bs]) ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> 0 < spacebeg -> AIMG_HI <= b -> b + Q_BATCH_BYTES <= ATOP ->
  (t + 4096 <= b \/ b + Q_BATCH_BYTES <= t) -> (t + 4096 <= lst \/ lst + Q_BATCH_BYTES <= t \/ lst = 0) -> (b + Q_BATCH_BYTES <= lst \/ lst + Q_BATCH_BYTES <= b) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG b Q_BATCH_BYTES -> (if full then rng RNG lst Q_BATCH_BYTES else True) ->
  evtF asegs RNG (enq_new_post full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t nb fst lst qb hm n nx bsz cnt24 b lo maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3820c) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable full : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 0).
Variable t : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 1).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 2).
Variable b : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 3).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 38).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 39).
Variable fst : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 40).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 41).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 42).
Variable n : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 43).
Variable nx : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 44).
Variable bsz : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 45).
Variable cnt24 : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 46).
Variable spacebeg : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 47).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 48).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 49).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 50).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 51).
Variable idxw : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 52).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'enqueue_new_spec__stmt 53).
#[using="Type"] Lemma enqueue_new_spec__body : ltac:(let T := type of (fun (h : enqueue_new_spec__stmt) => h full t lst b RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nb fst qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (full, (t, (lst, (b, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (nb, (fst, (qb, (hm, (n, (nx, (bsz, (cnt24, (spacebeg, (lo, (maxc, (csz, (stj, (idxw, chunks)))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> -> -> QC NB QB QBN N HM FST LST FULL SB CR CH LCH CNT NTH IXS STS HB BJ T0 T1 TAL SBP B0 B1 DTB DTL DBL RIMG RTLS RSTK RT RB RL. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES, K_BATCH_CLASS in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8);
              (lst, lst + 8); (b, b + 8192)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR. word_range idxw IXR.
  destruct BJ as [junkb BJ]. pose proof (stk_of_cb _ _ _ _ BJ ltac:(lia)) as TB. clear BJ junkb.
  carve_frame 64%nat ST.
  destruct full.
  - (* [comment removed for export] *)
    (nd_pre FULL 6%nat; intros NB1 LB NX BSZ L0 L1; nd_post).
    do 8 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. step. step. if_cases K1; zify_cond K1; [exfalso; lia|].   (* [comment removed for export] *)
    (* [comment removed for export] *)
    lstep.                                     (* [comment removed for export] *)
    step. if_cases K2; zify_cond K2; [exfalso; lia|].        (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    replace (Z.shiftr (Z.shiftl (cnt24 + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt24 + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.                        (* [comment removed for export] *)
    pose proof (u32arr_read asegs _ _ chunks (cnt24 + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt24 + -1))) CH ltac:(replace (cnt24 + -1) with (cnt24 - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.        (* [comment removed for export] *)
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
    amo_stepA AMO.                             (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. zstep. zstep. zstep.          (* [comment removed for export] *)
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3; zify_cond K3; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. zstep.                         (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.                    (* [comment removed for export] *)
    step. if_cases K4; zify_cond K4; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. zstep. step.                   (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. step.                         (* [comment removed for export] *)
    do 9 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_new_post. finish.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
  - (* [comment removed for export] *)
    pose proof FULL as NB0. clear FULL.
    do 8 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [|exfalso; lia].        (* [comment removed for export] *)
    (* [comment removed for export] *)
    lstep.                                     (* [comment removed for export] *)
    step. if_cases K2'; zify_cond K2'; [exfalso; lia|].        (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    replace (Z.shiftr (Z.shiftl (cnt24 + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt24 + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.                        (* [comment removed for export] *)
    pose proof (u32arr_read asegs _ _ chunks (cnt24 + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt24 + -1))) CH ltac:(replace (cnt24 + -1) with (cnt24 - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.        (* [comment removed for export] *)
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
    amo_stepA AMO.                             (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. zstep. zstep. zstep.          (* [comment removed for export] *)
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3'; zify_cond K3'; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. zstep.                         (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.                    (* [comment removed for export] *)
    step. if_cases K4; zify_cond K4; [|exfalso; lia].        (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. step.                         (* [comment removed for export] *)
    do 9 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_new_post. finish.
    + subst nb. exact QC.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
Qed.
End Zd1.
#[using="Type"] Lemma enqueue_new_spec : ltac:(let t := eval cbv delta [enqueue_new_spec__stmt] in enqueue_new_spec__stmt in exact t).
Proof. exact enqueue_new_spec__body. Qed.

(* [comment removed for export] *)
Definition enq_append_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (C nb fst lst qb hm n nx bsz cnt lo : Z) (hs : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (C + 24, C + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' C [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 (qb + n))]
    /\ rw_cells asegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 (bsz + n)); C8 (Z_to_bv 64 (cnt + 1))]
    /\ u64arr asegs m' (lst + 24) (hs ++ [Z_to_bv 64 hm])
    /\ (exists bs, rw_cells asegs m' (lst + 24 + 8 * (cnt + 1)) [CB (Z.to_nat (8192 - 24 - 8 * (cnt + 1))) bs]).

#[using="Type"] Lemma enqueue_append_spec : forall (C lst cnt : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz lo : Z) (hs : list word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 C -> a3 = Z_to_bv 64 hm -> a4 = Z_to_bv 64 n ->
  rw_cells asegs m C [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 < nb < 2^63 -> 0 <= qb -> qb + n < 2^63 -> 0 <= n -> 0 <= hm < 2^64 -> 0 <= fst < 2^64 ->
  rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 cnt)] ->
  0 <= cnt < Q_BATCH -> 0 <= bsz -> bsz + n < 2^63 -> 0 <= nx < 2^64 ->
  u64arr asegs m (lst + 24) hs -> length hs = Z.to_nat cnt ->
  (exists bs, rw_cells asegs m (lst + 24 + 8 * cnt) [CB (Z.to_nat (Q_BATCH_BYTES - 24 - 8 * cnt)) bs]) ->
  iclr C 32 -> C + 32 <= ATOP -> AIMG_HI <= lst -> lst + Q_BATCH_BYTES <= ATOP ->        (* [comment removed for export] *)
  (C + 32 <= lst \/ lst + Q_BATCH_BYTES <= C) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG C 32 -> rng RNG lst Q_BATCH_BYTES ->
  evtF asegs RNG (enq_append_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C nb fst lst qb hm n nx bsz cnt lo hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3820c) fc None m (seg_rom asegs)).
Proof.
  intros until hs. intros ST CEIL LO MI -> -> -> QC NB QB QBN N HM FST LB CNT BSZ BSZN NX LA LEN LJ C0 C1 L0 L1 DJ RIMG RTLS RSTK RC RL. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (C + 24, C + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  destruct LJ as [junkt LJ]. pose proof (stk_of_cb _ _ _ _ LJ ltac:(lia)) as TJ. clear LJ junkt.
  carve_frame 64%nat ST.
  do 8 step.                                   (* [comment removed for export] *)
  step. step. if_cases K0; zify_cond K0; [exfalso; lia|].   (* [comment removed for export] *)
  step. step. step. step. if_cases K1; zify_cond K1; [|exfalso; lia].   (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2; [exfalso; lia|].          (* [comment removed for export] *)
  step. zstep.                                 (* [comment removed for export] *)
  replace (Z.shiftl cnt 3) with (8 * cnt) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep. zstep. zstep.                         (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (stk_split asegs mm (lst + 24 + 8 * cnt) (lst + 24 + 8 * cnt + 8) _ TJ ltac:(lia)) as [TJ0 TJ1];
    destruct (stk_cb mm _ _ TJ0 ltac:(lia)) as [junk8 E8] end.
  clear TJ TJ0. replace (Z.to_nat (lst + 24 + 8 * cnt + 8 - (lst + 24 + 8 * cnt))) with 8%nat in E8 by lia.
  replace (lst + 24 + 8 * cnt) with (lst + 8 * cnt + 24) in E8 by lia.
  step.                                        (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  step. zstep. step.                           (* [comment removed for export] *)
  do 9 step.                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold enq_append_post. finish.
  - eapply u64arr_snoc; [exact LA|]. rewrite LEN. replace (lst + 24 + 8 * Z.of_nat (Z.to_nat cnt)) with (lst + 8 * cnt + 24) by lia. exact E8.
  - lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TJ1 ltac:(lia)) as [bs Hbs] end.
    exists bs. replace (lst + 24 + 8 * cnt + (8192 - 24 - 8 * cnt) - (lst + 24 + 8 * cnt + 8)) with (8192 - 24 - 8 * (cnt + 1)) in Hbs by lia.
    replace (lst + 24 + 8 * cnt + 8) with (lst + 24 + 8 * (cnt + 1)) in Hbs by lia. exact Hbs.
Qed.
End CANSEC1.
End TwB.
End F_aenqueue.

(* [comment removed for export] *)
Module F_aenqueueR.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.
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


Notation acache24 t := (t + 2128) (only parsing).       (* [comment removed for export] *)
Notation acache_stats t := (t + 2784) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition enq_to_refill_post (ra sp gp tp s0 s1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x382f8) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2
                  (Z_to_bv 64 (acache24 t)) (Z_to_bv 64 (t + 208))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (acache24 t)) (Z_to_bv 64 0xaaf98) (Z_to_bv 64 K_BATCH_CLASS) a4 a5 a6 a7
                  (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a2 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x38ad8) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="Type"] Lemma enqueue_to_refill_spec : forall (full : bool) (t lst : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz lo : Z) (maxc csz : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 (t + 80) -> a1 = Z_to_bv 64 (t + 208) -> a3 = Z_to_bv 64 hm -> a4 = Z_to_bv 64 n ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= lst < 2^64 ->
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 Q_BATCH)]
             /\ AIMG_HI <= lst /\ lst + Q_BATCH_BYTES <= ATOP /\ rng RNG lst Q_BATCH_BYTES
   else nb = 0) ->
  (* [comment removed for export] *)
  rw_cells asegs m (acache24 t) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 ->
  (t + 4096 <= lst \/ lst + Q_BATCH_BYTES <= t \/ lst = 0) ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (enq_to_refill_post ra sp gp tp s0 s1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x381a4) fc None m (seg_rom asegs)).
Proof.
  intros until csz. intros ST CEIL LO MI -> -> -> -> QC NB LST FULL CR T0 T1 TAL DTL RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES, K_BATCH_CLASS in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 64%nat ST.
  destruct full.
  - (* [comment removed for export] *)
    (nd_pre FULL 5%nat; intros NB1 LB L0 L1 RL; nd_post).
    do 8 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. step. step. if_cases K1; zify_cond K1; [exfalso; lia|].   (* [comment removed for export] *)
    lstep.                                     (* [comment removed for export] *)
    step. if_cases K2; zify_cond K2; [|exfalso; lia].        (* [comment removed for export] *)
    zstep. step. step.                         (* [comment removed for export] *)
    step. step. step. step. step. step.        (* [comment removed for export] *)
    step. step. step.                          (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    unfold enq_to_refill_post. finish. exact FR.
  - (* [comment removed for export] *)
    pose proof FULL as NB0. clear FULL.
    do 8 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [|exfalso; lia].        (* [comment removed for export] *)
    lstep.                                     (* [comment removed for export] *)
    step. if_cases K2'; zify_cond K2'; [|exfalso; lia].      (* [comment removed for export] *)
    zstep. step. step.
    step. step. step. step. step. step.
    step. step. step.
    step.
    unfold enq_to_refill_post. finish. exact FR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition enq_from_refill_post (full : bool) (vra sp gp tp v0 v1 v2 v3 v4 v5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb hm n nx bsz cnt b lo : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc vra) fc None m' (seg_rom asegs)
    /\ munch [(t + 80, t + 112); (acache24 t, acache24 t + 4); (acache_stats t, acache_stats t + 8);
              (lst, lst + 8); (b, b + 8192)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + 64)
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 (nb + 1)); C8 (Z_to_bv 64 (if full then fst else b)); C8 (Z_to_bv 64 b);
                                 C8 (Z_to_bv 64 (qb + (n + 8192)))]
    /\ rw_cells asegs m' (acache24 t) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells asegs m' (acache_stats t) [C8 stj'])
    /\ rw_cells asegs m' b [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (n + 8192)); C8 (Z_to_bv 64 1)]
    /\ u64arr asegs m' (b + 24) [Z_to_bv 64 hm]
    /\ (exists bs, rw_cells asegs m' (b + 24 + 8 * 1) [CB (Z.to_nat (8192 - 24 - 8 * 1)) bs])
    /\ (if full then rw_cells asegs m' lst [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] else True).

Definition enqueue_from_refill_spec__stmt : Prop := forall (full : bool) (t lst b : Z) RNG
    (ra0 sp gp tp t0 t1 t2 vra v0 v1 v2 v3 v4 v5 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz cnt spacebeg lo : Z) (maxc csz stj idxw : word) (chunks : list word) (j0 : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 64 < 2^64 ->
  mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp) [CB 8 j0; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + Q_BATCH_BYTES < 2^63 -> 0 <= n -> 0 <= hm < 2^64 -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 Q_BATCH)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ AIMG_HI <= lst /\ lst + Q_BATCH_BYTES <= ATOP
   else nb = 0) ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (acache24 t) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache24 t + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  b = spacebeg + K_BATCH_CLASS * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat Q_BATCH_BYTES) bs]) ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> 0 < spacebeg -> AIMG_HI <= b -> b + Q_BATCH_BYTES <= ATOP ->
  (t + 4096 <= b \/ b + Q_BATCH_BYTES <= t) -> (t + 4096 <= lst \/ lst + Q_BATCH_BYTES <= t \/ lst = 0) -> (b + Q_BATCH_BYTES <= lst \/ lst + Q_BATCH_BYTES <= b) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG (bv_unsigned sp) 64 -> rng RNG t 4096 -> rng RNG b Q_BATCH_BYTES -> (if full then rng RNG lst Q_BATCH_BYTES else True) ->
  evtF asegs RNG (enq_from_refill_post full vra sp gp tp v0 v1 v2 v3 v4 v5 s6 s7 s8 s9 s10 s11 F fc t nb fst lst qb hm n nx bsz cnt b lo maxc csz m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 (Z_to_bv 64 (acache24 t)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x382f8) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable full : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 0).
Variable t : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 1).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 2).
Variable b : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 3).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 4).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 11).
Variable vra : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 12).
Variable v0 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 13).
Variable v1 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 14).
Variable v2 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 15).
Variable v3 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 16).
Variable v4 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 17).
Variable v5 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 18).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 19).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 20).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 21).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 22).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 23).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 24).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 25).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 26).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 27).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 28).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 29).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 30).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 31).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 32).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 33).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 34).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 35).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 36).
Variable F : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 37).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 38).
Variable m : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 39).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 40).
Variable fst : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 41).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 42).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 43).
Variable n : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 44).
Variable nx : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 45).
Variable bsz : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 46).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 47).
Variable spacebeg : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 48).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 49).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 50).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 51).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 52).
Variable idxw : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 53).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 54).
Variable j0 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 55).
#[using="Type"] Lemma enqueue_from_refill_spec__body : ltac:(let T := type of (fun (h : enqueue_from_refill_spec__stmt) => h full t lst b RNG ra0 sp gp tp t0 t1 t2 vra v0 v1 v2 v3 v4 v5 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nb fst qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (full, (t, (lst, (b, (RNG, (ra0, (sp, (gp, (tp, (t0, (t1, (t2, (vra, (v0, (v1, (v2, (v3, (v4, (v5, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s4, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (nb, (fst, (qb, (hm, (n, (nx, (bsz, (cnt, (spacebeg, (lo, (maxc, (csz, (stj, (idxw, (chunks, j0)))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO SP64 MI FR QC NB QB QBN N HM FST LST FULL SB CR CH LCH CNT NTH IXS STS HB BJ T0 T1 TAL SBP B0 B1 DTB DTL DBL RIMG RTLS RSTK RT RB RL. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES, K_BATCH_CLASS in *.
  pose proof (munch_refl [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR. word_range idxw IXR.
  destruct BJ as [junkb BJ]. pose proof (stk_of_cb _ _ _ _ BJ ltac:(lia)) as TB. clear BJ junkb.
  (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  step. if_cases KR; zify_cond KR; [exfalso; lia|].          (* [comment removed for export] *)
  step. step. step.                            (* [comment removed for export] *)
  lstep.                                       (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  destruct full.
  - (* [comment removed for export] *)
    (nd_pre FULL 6%nat; intros NB1 LB NX BSZ L0 L1; nd_post).
    (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.                        (* [comment removed for export] *)
    pose proof (u32arr_read asegs _ _ chunks (cnt + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.        (* [comment removed for export] *)
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
    amo_stepA AMO.                             (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. zstep. zstep. zstep.          (* [comment removed for export] *)
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3; zify_cond K3; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. zstep.                         (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.                    (* [comment removed for export] *)
    step. if_cases K4; zify_cond K4; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. zstep. step.                   (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. step.                         (* [comment removed for export] *)
    do 9 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp + 64).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_from_refill_post. finish.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
  - (* [comment removed for export] *)
    pose proof FULL as NB0. clear FULL.
    zstep. zstep.                              (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.                        (* [comment removed for export] *)
    pose proof (u32arr_read asegs _ _ chunks (cnt + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.        (* [comment removed for export] *)
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
    amo_stepA AMO.                             (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. zstep. zstep. zstep.          (* [comment removed for export] *)
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3'; zify_cond K3'; [exfalso; lia|].      (* [comment removed for export] *)
    step. step. zstep.                         (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.                    (* [comment removed for export] *)
    step. if_cases K4; zify_cond K4; [|exfalso; lia].        (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. step.                         (* [comment removed for export] *)
    do 9 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp + 64).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_from_refill_post. finish.
    + subst nb. exact QC.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
Qed.
End Zd1.
#[using="Type"] Lemma enqueue_from_refill_spec : ltac:(let t := eval cbv delta [enqueue_from_refill_spec__stmt] in enqueue_from_refill_spec__stmt in exact t).
Proof. exact enqueue_from_refill_spec__body. Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Notation acache24 t := (t + 2128) (only parsing).       (* [comment removed for export] *)
Notation acache_stats t := (t + 2784) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition enq_to_refill_post (ra sp gp tp s0 s1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x38360) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2
                  (Z_to_bv 64 (acache24 t)) (Z_to_bv 64 (t + 208))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (acache24 t)) (Z_to_bv 64 0xab398) (Z_to_bv 64 K_BATCH_CLASS) a4 a5 a6 a7
                  (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a2 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x38b40) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="Type"] Lemma enqueue_to_refill_spec : forall (full : bool) (t lst : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz lo : Z) (maxc csz : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 (t + 80) -> a1 = Z_to_bv 64 (t + 208) -> a3 = Z_to_bv 64 hm -> a4 = Z_to_bv 64 n ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= lst < 2^64 ->
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 Q_BATCH)]
             /\ AIMG_HI <= lst /\ lst + Q_BATCH_BYTES <= ATOP /\ rng RNG lst Q_BATCH_BYTES
   else nb = 0) ->
  (* [comment removed for export] *)
  rw_cells asegs m (acache24 t) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 ->
  (t + 4096 <= lst \/ lst + Q_BATCH_BYTES <= t \/ lst = 0) ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (enq_to_refill_post ra sp gp tp s0 s1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3820c) fc None m (seg_rom asegs)).
Proof.
  intros until csz. intros ST CEIL LO MI -> -> -> -> QC NB LST FULL CR T0 T1 TAL DTL RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES, K_BATCH_CLASS in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 64%nat ST.
  destruct full.
  - (* [comment removed for export] *)
    (nd_pre FULL 5%nat; intros NB1 LB L0 L1 RL; nd_post).
    do 8 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. step. step. if_cases K1; zify_cond K1; [exfalso; lia|].   (* [comment removed for export] *)
    lstep.                                     (* [comment removed for export] *)
    step. if_cases K2; zify_cond K2; [|exfalso; lia].        (* [comment removed for export] *)
    zstep. step. step.                         (* [comment removed for export] *)
    step. step. step. step. step. step.        (* [comment removed for export] *)
    step. step. step.                          (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    unfold enq_to_refill_post. finish. exact FR.
  - (* [comment removed for export] *)
    pose proof FULL as NB0. clear FULL.
    do 8 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [|exfalso; lia].        (* [comment removed for export] *)
    lstep.                                     (* [comment removed for export] *)
    step. if_cases K2'; zify_cond K2'; [|exfalso; lia].      (* [comment removed for export] *)
    zstep. step. step.
    step. step. step. step. step. step.
    step. step. step.
    step.
    unfold enq_to_refill_post. finish. exact FR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition enq_from_refill_post (full : bool) (vra sp gp tp v0 v1 v2 v3 v4 v5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb hm n nx bsz cnt b lo : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc vra) fc None m' (seg_rom asegs)
    /\ munch [(t + 80, t + 112); (acache24 t, acache24 t + 4); (acache_stats t, acache_stats t + 8);
              (lst, lst + 8); (b, b + 8192)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + 64)
    /\ rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 (nb + 1)); C8 (Z_to_bv 64 (if full then fst else b)); C8 (Z_to_bv 64 b);
                                 C8 (Z_to_bv 64 (qb + (n + 8192)))]
    /\ rw_cells asegs m' (acache24 t) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells asegs m' (acache_stats t) [C8 stj'])
    /\ rw_cells asegs m' b [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (n + 8192)); C8 (Z_to_bv 64 1)]
    /\ u64arr asegs m' (b + 24) [Z_to_bv 64 hm]
    /\ (exists bs, rw_cells asegs m' (b + 24 + 8 * 1) [CB (Z.to_nat (8192 - 24 - 8 * 1)) bs])
    /\ (if full then rw_cells asegs m' lst [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] else True).

Definition enqueue_from_refill_spec__stmt : Prop := forall (full : bool) (t lst b : Z) RNG
    (ra0 sp gp tp t0 t1 t2 vra v0 v1 v2 v3 v4 v5 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz cnt spacebeg lo : Z) (maxc csz stj idxw : word) (chunks : list word) (j0 : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 64 < 2^64 ->
  mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp) [CB 8 j0; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + Q_BATCH_BYTES < 2^63 -> 0 <= n -> 0 <= hm < 2^64 -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 Q_BATCH)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ AIMG_HI <= lst /\ lst + Q_BATCH_BYTES <= ATOP
   else nb = 0) ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (acache24 t) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache24 t + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  b = spacebeg + K_BATCH_CLASS * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat Q_BATCH_BYTES) bs]) ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> 0 < spacebeg -> AIMG_HI <= b -> b + Q_BATCH_BYTES <= ATOP ->
  (t + 4096 <= b \/ b + Q_BATCH_BYTES <= t) -> (t + 4096 <= lst \/ lst + Q_BATCH_BYTES <= t \/ lst = 0) -> (b + Q_BATCH_BYTES <= lst \/ lst + Q_BATCH_BYTES <= b) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG (bv_unsigned sp) 64 -> rng RNG t 4096 -> rng RNG b Q_BATCH_BYTES -> (if full then rng RNG lst Q_BATCH_BYTES else True) ->
  evtF asegs RNG (enq_from_refill_post full vra sp gp tp v0 v1 v2 v3 v4 v5 s6 s7 s8 s9 s10 s11 F fc t nb fst lst qb hm n nx bsz cnt b lo maxc csz m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 (Z_to_bv 64 (acache24 t)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38360) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable full : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 0).
Variable t : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 1).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 2).
Variable b : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 3).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 4).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 11).
Variable vra : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 12).
Variable v0 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 13).
Variable v1 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 14).
Variable v2 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 15).
Variable v3 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 16).
Variable v4 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 17).
Variable v5 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 18).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 19).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 20).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 21).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 22).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 23).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 24).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 25).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 26).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 27).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 28).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 29).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 30).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 31).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 32).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 33).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 34).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 35).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 36).
Variable F : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 37).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 38).
Variable m : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 39).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 40).
Variable fst : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 41).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 42).
Variable hm : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 43).
Variable n : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 44).
Variable nx : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 45).
Variable bsz : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 46).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 47).
Variable spacebeg : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 48).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 49).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 50).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 51).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 52).
Variable idxw : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 53).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 54).
Variable j0 : ltac2:(SecDietF.SzSecF.ty 'enqueue_from_refill_spec__stmt 55).
#[using="Type"] Lemma enqueue_from_refill_spec__body : ltac:(let T := type of (fun (h : enqueue_from_refill_spec__stmt) => h full t lst b RNG ra0 sp gp tp t0 t1 t2 vra v0 v1 v2 v3 v4 v5 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nb fst qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (full, (t, (lst, (b, (RNG, (ra0, (sp, (gp, (tp, (t0, (t1, (t2, (vra, (v0, (v1, (v2, (v3, (v4, (v5, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s4, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (nb, (fst, (qb, (hm, (n, (nx, (bsz, (cnt, (spacebeg, (lo, (maxc, (csz, (stj, (idxw, (chunks, j0)))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO SP64 MI FR QC NB QB QBN N HM FST LST FULL SB CR CH LCH CNT NTH IXS STS HB BJ T0 T1 TAL SBP B0 B1 DTB DTL DBL RIMG RTLS RSTK RT RB RL. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES, K_BATCH_CLASS in *.
  pose proof (munch_refl [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR. word_range idxw IXR.
  destruct BJ as [junkb BJ]. pose proof (stk_of_cb _ _ _ _ BJ ltac:(lia)) as TB. clear BJ junkb.
  (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  step. if_cases KR; zify_cond KR; [exfalso; lia|].          (* [comment removed for export] *)
  step. step. step.                            (* [comment removed for export] *)
  lstep.                                       (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  destruct full.
  - (* [comment removed for export] *)
    (nd_pre FULL 6%nat; intros NB1 LB NX BSZ L0 L1; nd_post).
    (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.                        (* [comment removed for export] *)
    pose proof (u32arr_read asegs _ _ chunks (cnt + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.        (* [comment removed for export] *)
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
    amo_stepA AMO.                             (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. zstep. zstep. zstep.          (* [comment removed for export] *)
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3; zify_cond K3; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. zstep.                         (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.                    (* [comment removed for export] *)
    step. if_cases K4; zify_cond K4; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. zstep. step.                   (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. step.                         (* [comment removed for export] *)
    do 9 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp + 64).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_from_refill_post. finish.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
  - (* [comment removed for export] *)
    pose proof FULL as NB0. clear FULL.
    zstep. zstep.                              (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.                        (* [comment removed for export] *)
    pose proof (u32arr_read asegs _ _ chunks (cnt + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.        (* [comment removed for export] *)
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
    amo_stepA AMO.                             (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. zstep. zstep. zstep.          (* [comment removed for export] *)
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3'; zify_cond K3'; [exfalso; lia|].      (* [comment removed for export] *)
    step. step. zstep.                         (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.                    (* [comment removed for export] *)
    step. if_cases K4; zify_cond K4; [|exfalso; lia].        (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. step.                         (* [comment removed for export] *)
    do 9 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp + 64).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_from_refill_post. finish.
    + subst nb. exact QC.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
Qed.
End Zd1.
#[using="Type"] Lemma enqueue_from_refill_spec : ltac:(let t := eval cbv delta [enqueue_from_refill_spec__stmt] in enqueue_from_refill_spec__stmt in exact t).
Proof. exact enqueue_from_refill_spec__body. Qed.
End CANSEC1.
End TwB.
End F_aenqueueR.

(* [comment removed for export] *)
Module F_aintal.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF StrwF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.
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
Definition imemset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a4 a5 a6 a7 : word) (A n : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3' t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].

Section IMemset.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem).
  Hypothesis MI0 : mem_inv asegs m.
  Hypothesis AB : bv_unsigned a0 + bv_unsigned a2 < 2^64 /\ 0 < bv_unsigned a2.
  Hypothesis RR : rng RNG (bv_unsigned a0) (bv_unsigned a2).

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Notation POST := (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a4 a5 a6 a7 (bv_unsigned a0) (bv_unsigned a2) m).
  Notation ST pc mm x11 x12 x13 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Ltac with_arr tac :=
    lazymatch goal with
    | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
    end.
  (* [comment removed for export] *)
  Ltac fin_with cover :=
    zstep;
    with_arr ltac:(fun segs ARR FIL LEN A cb =>
      let E := fresh "E" in
      pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
      rewrite LEN in E; rewrite E in ARR;
      apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
    unfold imemset_post; finish; subst; assumption.

  (* [comment removed for export] *)
  Lemma imemset_bloop : forall (K : nat) (i : Z) (m1 : amem) (bs : list byte) (Q : Z -> Prop),
    Z.to_nat (n - i) = K ->
    u8arr asegs m1 A bs -> filled (Z_to_bv 8 0) bs Q -> length bs = Z.to_nat n ->
    mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
    (forall j, 0 <= j < i -> Q j) -> 0 <= i < n ->
    forall x13, x13 = Z_to_bv 64 (A + i) ->
    evtF asegs RNG POST (ST 0x67ab0 m1 (Z_to_bv 64 0) (Z_to_bv 64 (A + n)) x13).
  Proof using AB RR.
    pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
    induction K as [K IH] using lt_wf_ind; intros i m1 bs Q HK ARR FIL LEN MI MU WM HQ Hi x13 ->.
    mst i 1%nat ltac:(reflexivity).
    zstep. zstep. if_cases KK; zify_cond KK.
    - (* [comment removed for export] *)
      eapply (IH (Z.to_nat (n - (i + 1))) ltac:(lia) (i + 1) _ _ _ eq_refl ARR FIL LEN MI MU WM); [|lia|f_equal; lia].
      intros j Hj. destruct (Z_lt_le_dec j i); [left; apply HQ; lia| right; lia].
    - zstep. fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j i); [left; apply HQ; lia| right; lia]).
  Qed.

  (* [comment removed for export] *)
  Lemma imemset_wloop : forall (K : nat) (i : Z) (m1 : amem) (bs : list byte) (Q : Z -> Prop),
    Z.to_nat (n - i) = K ->
    u8arr asegs m1 A bs -> filled (Z_to_bv 8 0) bs Q -> length bs = Z.to_nat n ->
    mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
    (forall j, 0 <= j < i -> Q j) -> 0 <= i < n -> (exists q, i = 16 * q) -> (exists q, n = 16 * q) ->
    forall x13, x13 = Z_to_bv 64 (A + i) ->
    evtF asegs RNG POST (ST 0x67ae4 m1 (Z_to_bv 64 0) (Z_to_bv 64 (A + n)) x13).
  Proof using AB RR.
    pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
    induction K as [K IH] using lt_wf_ind; intros i m1 bs Q HK ARR FIL LEN MI MU WM HQ Hi [qi Hqi] [qn Hqn] x13 ->.
    mst i 8%nat ltac:(reflexivity).
    mst (i + 8)%Z 8%nat ltac:(reflexivity).
    zstep. zstep. if_cases KK; zify_cond KK.
    - eapply (IH (Z.to_nat (n - (i + 16))) ltac:(lia) (i + 16) _ _ _ eq_refl ARR FIL LEN MI MU WM); [|lia| exists (qi + 1); lia| exists qn; lia| f_equal; lia].
      intros j Hj. destruct (Z_lt_le_dec j i); [left; left; apply HQ; lia|]. destruct (Z_lt_le_dec j (i + 8)); [left; right; lia| right; lia].
    - fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j i); [left; left; apply HQ; lia|];
                      destruct (Z_lt_le_dec j (i + 8)); [left; right; lia| right; lia]).
  Qed.

  Lemma imemset_body : forall junk,
    rw_cells asegs m A [CB (Z.to_nat n) junk] ->
    evtF asegs RNG POST (ST 0x67a98 m (Z_to_bv 64 0) a2 a3).
  Proof using AB MI0 RR.
    intros junk DST. pose proof MI0 as MI.
    pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
    pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
    pose proof (filled_init (Z_to_bv 8 0) junk) as FIL.
    zstep. zstep.
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
      do 7 zstep. zstep.
      assert (HA : A mod 16 = 0 /\ n mod 16 = 0).
      { rewrite Z.land_lor_distr_l in K0. apply Z.lor_eq_0_iff in K0. destruct K0 as [Kn KA].
        change 15 with (Z.ones 4) in Kn, KA. rewrite Z.land_ones in Kn, KA by lia. change (2^4) with 16 in Kn, KA. lia. }
      eapply (imemset_wloop (Z.to_nat (n - 0)) 0 m _ _ eq_refl ARR FIL LEN MI MU WM); [intros j Hj; lia| lia| exists 0; lia| exists (n / 16); lia| symmetry; apply Z_to_bv_plus0].
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
      zstep. zstep.
      eapply (imemset_bloop (Z.to_nat (n - 0)) 0 m _ _ eq_refl ARR FIL LEN MI MU WM); [intros j Hj; lia| lia| symmetry; apply Z_to_bv_plus0].
  Qed.
End IMemset.

#[using="Type"] Lemma imemset_spec : forall (A n : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (junk : list byte),
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 n -> 0 <= A -> 0 < n -> A + n < 2^64 ->
  rw_cells asegs m A [CB (Z.to_nat n) junk] ->
  mem_inv asegs m ->
  rng RNG A n ->
  evtF asegs RNG (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a4 a5 a6 a7 A n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x67a98) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros -> -> -> HA Hn HAn DST MI RR.
  pose proof (imemset_body RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MI) as H.
  rewrite !unsigned_lit in H by lia. apply (H ltac:(lia) RR junk DST).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ia_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=   (* [comment removed for export] *)
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xaf800) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xaf800 (0xaf800 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).

Definition internal_allocator_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (ia : bool) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
  (ia = true -> forall j, 0 <= j < AIA_MAP1_LEN / 8 -> bytes_at asegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rw_cells asegs m 0xa5490 [C8 (Z_to_bv 64 0x13e0a0)] -> rw_cells asegs m 0x13e0a0 [C8 (Z_to_bv 64 4096)] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ia_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x61e84) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 34).
Variable ia : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 35).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 36).
#[using="Type"] Lemma internal_allocator_spec__body : ltac:(let T := type of (fun (h : internal_allocator_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ia lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (ia, lo))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI FL IA Z2 PG1 PG2 RIMG RTLS RSTK.
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  do 6 step.                                   (* [comment removed for export] *)
  step. zstep.                                 (* [comment removed for export] *)
  destruct ia.
  - (* [comment removed for export] *)
    lstep. step. step. if_lit.                 (* [comment removed for export] *)
    step. zstep.                               (* [comment removed for export] *)
    do 7 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold ia_post. finish.
    + eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros q Hq; lia.
    + intros j Hj. pose proof (Z2 eq_refl j ltac:(lia)) as B. eapply bytes_at_agree; [exact B|].
      intros i Hi. apply MU. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
  - (* [comment removed for export] *)
    apply (munch_weaken _ [(bv_unsigned sp - 48, bv_unsigned sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4)]%Z) in MU.
    2:{ unfold sub_fp; cbn [outside]; intros q Hq; lia. }
    clear Z2.
    lstep. step. step. if_lit.                 (* [comment removed for export] *)
    do 8 zstep.                                (* [comment removed for export] *)
    apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in FL. change (0 + 256 * 0) with 0 in FL.
    amo_step. lits.                            (* [comment removed for export] *)
    do 4 zstep.                                (* [comment removed for export] *)
    amo_step.                                  (* [comment removed for export] *)
    step. if_lit.                              (* [comment removed for export] *)
    zstep. zstep. step. if_lit.                (* [comment removed for export] *)
    apply (rw_C4_to_C1x4 _ _ 0 1 ltac:(lia) ltac:(lia)) in FL.
    lstep. step. if_lit.                       (* [comment removed for export] *)
    step. step. zstep. zstep. zstep. step. step.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    carve_frame 40%nat IA.
    step. call (imemset_spec 0x130808 40); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact FR0| assumption|].
    rename POST into Z1.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm 0xaf800 0xaf808 (718848 + 528392) IA ltac:(lia)) as [IA0 IA1] end.
    clear IA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_cb mm 0xaf800 0xaf808 IA0 ltac:(lia)) as [junk1 FR1] end.
    clear IA0. change (Z.to_nat (0xaf808 - 0xaf800)) with 8%nat in FR1.
    step.
    (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm 0xaf808 0xef808 (718848 + 528392) IA1 ltac:(lia)) as [IA2 IA3] end.
    clear IA1.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_cb mm 0xaf808 0xef808 IA2 ltac:(lia)) as [junk2 DST2] end.
    clear IA2. change (0xef808 - 0xaf808) with 0x40000 in DST2.
    step. call (imemset_spec 0xaf808 0x40000); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST2| assumption|].
    rename POST into Z2.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (MAP : forall j, 0 <= j < 32768 -> bytes_at asegs mm (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0)))
        by (intros j Hj; apply (cb_zero_le8 _ _ _ _ Z2); lia);
      pose proof (stk_of_cb mm 0xaf808 0x40000 _ Z2 ltac:(lia)) as IA2 end.
    clear Z2. box MAP. snapshot [(0xef840, 0x130808); (0x13e088, 0x13e08c)]%Z MUm WMm.
    (* [comment removed for export] *)
    zstep. zstep. step. step. step.            (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm 0xef808 0xef840 (718848 + 528392) IA3 ltac:(lia)) as [IAg IA4];
      destruct (stk_split asegs mm 0xef840 0xf05c0 (718848 + 528392) IA4 ltac:(lia)) as [IA5 IA6];
      destruct (stk_cb mm 0xef840 0xf05c0 IA5 ltac:(lia)) as [junk3 DST3] end.
    clear IA3 IA4 IA5. change (0xf05c0 - 0xef840) with 0xd80 in DST3.
    step. call (imemset_spec 0xef840 0xd80); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST3| assumption|].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_of_cb mm 0xef840 0xd80 _ POST ltac:(lia)) as IA5 end.
    clear POST.
    (* [comment removed for export] *)
    step. zstep. zstep. zstep. step.           (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_cb mm 0xf05c0 (718848 + 528392) IA6 ltac:(lia)) as [junk4 DST4] end.
    clear IA6. change (718848 + 528392 - 0xf05c0) with 0x40248 in DST4.
    step. call (imemset_spec 0xf05c0 0x40248); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST4| assumption|].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_of_cb mm 0xf05c0 0x40248 _ POST ltac:(lia)) as IA6 end.
    clear POST.
    (* [comment removed for export] *)
    step. step. step. step. if_lit.            (* [comment removed for export] *)
    zstep. zstep. zstep. step.                 (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm 0xf05c0 0xf05d0 (0xf05c0 + 0x40248) IA6 ltac:(lia)) as [IA7 IA8];
      destruct (stk_cb mm 0xf05c0 0xf05d0 IA7 ltac:(lia)) as [junk5 FR5] end.
    clear IA6 IA7. change (Z.to_nat (0xf05d0 - 0xf05c0)) with 16%nat in FR5.
    step. step.                                (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep.                               (* [comment removed for export] *)
    do 7 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (stk_of_rw_cells asegs mm _ _ FR1) as Q0; cbn [cells_size csize Nat.add] in Q0;
      pose proof (stk_of_rw_cells asegs mm _ _ FR5) as Q5; cbn [cells_size csize Nat.add] in Q5;
      pose proof (stk_of_cb mm _ _ _ Z1 ltac:(lia)) as Q1 end.
    assert (IA : stk asegs m1 0xaf800 (0xaf800 + 0x81030)).
    { eapply stk_merge3; [exact Q0| exact IA2| | lia| lia].
      eapply stk_merge3; [exact IAg| exact IA5| | lia| lia].
      eapply stk_merge3; [exact Q5| exact IA8| exact Q1| lia| lia]. }
    unfold ia_post. finish.
    intros j Hj. unbox MAP. eapply bytes_at_agree; [apply (MAP j); lia|].
    intros i Hi. apply MUm. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
Qed.
End Zd1.
#[using="Type"] Lemma internal_allocator_spec : ltac:(let t := eval cbv delta [internal_allocator_spec__stmt] in internal_allocator_spec__stmt in exact t).
Proof. exact internal_allocator_spec__body. Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StrwF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB.
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
Definition imemset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a4 a5 a6 a7 : word) (A n : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3' t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].

Section IMemset.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem).
  Hypothesis MI0 : mem_inv asegs m.
  Hypothesis AB : bv_unsigned a0 + bv_unsigned a2 < 2^64 /\ 0 < bv_unsigned a2.
  Hypothesis RR : rng RNG (bv_unsigned a0) (bv_unsigned a2).

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Notation POST := (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a4 a5 a6 a7 (bv_unsigned a0) (bv_unsigned a2) m).
  Notation ST pc mm x11 x12 x13 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Ltac with_arr tac :=
    lazymatch goal with
    | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
    end.
  (* [comment removed for export] *)
  Ltac fin_with cover :=
    zstep;
    with_arr ltac:(fun segs ARR FIL LEN A cb =>
      let E := fresh "E" in
      pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
      rewrite LEN in E; rewrite E in ARR;
      apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
    unfold imemset_post; finish; subst; assumption.

  (* [comment removed for export] *)
  Lemma imemset_bloop : forall (K : nat) (i : Z) (m1 : amem) (bs : list byte) (Q : Z -> Prop),
    Z.to_nat (n - i) = K ->
    u8arr asegs m1 A bs -> filled (Z_to_bv 8 0) bs Q -> length bs = Z.to_nat n ->
    mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
    (forall j, 0 <= j < i -> Q j) -> 0 <= i < n ->
    forall x13, x13 = Z_to_bv 64 (A + i) ->
    evtF asegs RNG POST (ST 0x67b18 m1 (Z_to_bv 64 0) (Z_to_bv 64 (A + n)) x13).
  Proof using AB RR.
    pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
    induction K as [K IH] using lt_wf_ind; intros i m1 bs Q HK ARR FIL LEN MI MU WM HQ Hi x13 ->.
    mst i 1%nat ltac:(reflexivity).
    zstep. zstep. if_cases KK; zify_cond KK.
    - (* [comment removed for export] *)
      eapply (IH (Z.to_nat (n - (i + 1))) ltac:(lia) (i + 1) _ _ _ eq_refl ARR FIL LEN MI MU WM); [|lia|f_equal; lia].
      intros j Hj. destruct (Z_lt_le_dec j i); [left; apply HQ; lia| right; lia].
    - zstep. fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j i); [left; apply HQ; lia| right; lia]).
  Qed.

  (* [comment removed for export] *)
  Lemma imemset_wloop : forall (K : nat) (i : Z) (m1 : amem) (bs : list byte) (Q : Z -> Prop),
    Z.to_nat (n - i) = K ->
    u8arr asegs m1 A bs -> filled (Z_to_bv 8 0) bs Q -> length bs = Z.to_nat n ->
    mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
    (forall j, 0 <= j < i -> Q j) -> 0 <= i < n -> (exists q, i = 16 * q) -> (exists q, n = 16 * q) ->
    forall x13, x13 = Z_to_bv 64 (A + i) ->
    evtF asegs RNG POST (ST 0x67b4c m1 (Z_to_bv 64 0) (Z_to_bv 64 (A + n)) x13).
  Proof using AB RR.
    pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
    induction K as [K IH] using lt_wf_ind; intros i m1 bs Q HK ARR FIL LEN MI MU WM HQ Hi [qi Hqi] [qn Hqn] x13 ->.
    mst i 8%nat ltac:(reflexivity).
    mst (i + 8)%Z 8%nat ltac:(reflexivity).
    zstep. zstep. if_cases KK; zify_cond KK.
    - eapply (IH (Z.to_nat (n - (i + 16))) ltac:(lia) (i + 16) _ _ _ eq_refl ARR FIL LEN MI MU WM); [|lia| exists (qi + 1); lia| exists qn; lia| f_equal; lia].
      intros j Hj. destruct (Z_lt_le_dec j i); [left; left; apply HQ; lia|]. destruct (Z_lt_le_dec j (i + 8)); [left; right; lia| right; lia].
    - fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j i); [left; left; apply HQ; lia|];
                      destruct (Z_lt_le_dec j (i + 8)); [left; right; lia| right; lia]).
  Qed.

  Lemma imemset_body : forall junk,
    rw_cells asegs m A [CB (Z.to_nat n) junk] ->
    evtF asegs RNG POST (ST 0x67b00 m (Z_to_bv 64 0) a2 a3).
  Proof using AB MI0 RR.
    intros junk DST. pose proof MI0 as MI.
    pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
    pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
    pose proof (filled_init (Z_to_bv 8 0) junk) as FIL.
    zstep. zstep.
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
      do 7 zstep. zstep.
      assert (HA : A mod 16 = 0 /\ n mod 16 = 0).
      { rewrite Z.land_lor_distr_l in K0. apply Z.lor_eq_0_iff in K0. destruct K0 as [Kn KA].
        change 15 with (Z.ones 4) in Kn, KA. rewrite Z.land_ones in Kn, KA by lia. change (2^4) with 16 in Kn, KA. lia. }
      eapply (imemset_wloop (Z.to_nat (n - 0)) 0 m _ _ eq_refl ARR FIL LEN MI MU WM); [intros j Hj; lia| lia| exists 0; lia| exists (n / 16); lia| symmetry; apply Z_to_bv_plus0].
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
      zstep. zstep.
      eapply (imemset_bloop (Z.to_nat (n - 0)) 0 m _ _ eq_refl ARR FIL LEN MI MU WM); [intros j Hj; lia| lia| symmetry; apply Z_to_bv_plus0].
  Qed.
End IMemset.

#[using="Type"] Lemma imemset_spec : forall (A n : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (junk : list byte),
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 n -> 0 <= A -> 0 < n -> A + n < 2^64 ->
  rw_cells asegs m A [CB (Z.to_nat n) junk] ->
  mem_inv asegs m ->
  rng RNG A n ->
  evtF asegs RNG (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a4 a5 a6 a7 A n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x67b00) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros -> -> -> HA Hn HAn DST MI RR.
  pose proof (imemset_body RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MI) as H.
  rewrite !unsigned_lit in H by lia. apply (H ltac:(lia) RR junk DST).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ia_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=   (* [comment removed for export] *)
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xafc00) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xafc00 (0xafc00 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).

Definition internal_allocator_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (ia : bool) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
  (ia = true -> forall j, 0 <= j < AIA_MAP1_LEN / 8 -> bytes_at asegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rw_cells asegs m 0xa5870 [C8 (Z_to_bv 64 0x13e4a0)] -> rw_cells asegs m 0x13e4a0 [C8 (Z_to_bv 64 4096)] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ia_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x61eec) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 34).
Variable ia : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 35).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'internal_allocator_spec__stmt 36).
#[using="Type"] Lemma internal_allocator_spec__body : ltac:(let T := type of (fun (h : internal_allocator_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ia lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (ia, lo))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI FL IA Z2 PG1 PG2 RIMG RTLS RSTK.
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  do 6 step.                                   (* [comment removed for export] *)
  step. zstep.                                 (* [comment removed for export] *)
  destruct ia.
  - (* [comment removed for export] *)
    lstep. step. step. if_lit.                 (* [comment removed for export] *)
    step. zstep.                               (* [comment removed for export] *)
    do 7 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold ia_post. finish.
    + eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros q Hq; lia.
    + intros j Hj. pose proof (Z2 eq_refl j ltac:(lia)) as B. eapply bytes_at_agree; [exact B|].
      intros i Hi. apply MU. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
  - (* [comment removed for export] *)
    apply (munch_weaken _ [(bv_unsigned sp - 48, bv_unsigned sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4)]%Z) in MU.
    2:{ unfold sub_fp; cbn [outside]; intros q Hq; lia. }
    clear Z2.
    lstep. step. step. if_lit.                 (* [comment removed for export] *)
    do 8 zstep.                                (* [comment removed for export] *)
    apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in FL. change (0 + 256 * 0) with 0 in FL.
    amo_step. lits.                            (* [comment removed for export] *)
    do 4 zstep.                                (* [comment removed for export] *)
    amo_step.                                  (* [comment removed for export] *)
    step. if_lit.                              (* [comment removed for export] *)
    zstep. zstep. step. if_lit.                (* [comment removed for export] *)
    apply (rw_C4_to_C1x4 _ _ 0 1 ltac:(lia) ltac:(lia)) in FL.
    lstep. step. if_lit.                       (* [comment removed for export] *)
    step. step. zstep. zstep. zstep. step. step.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    carve_frame 40%nat IA.
    step. call (imemset_spec 0x130c08 40); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact FR0| assumption|].
    rename POST into Z1.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm 0xafc00 0xafc08 (719872 + 528392) IA ltac:(lia)) as [IA0 IA1] end.
    clear IA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_cb mm 0xafc00 0xafc08 IA0 ltac:(lia)) as [junk1 FR1] end.
    clear IA0. change (Z.to_nat (0xafc08 - 0xafc00)) with 8%nat in FR1.
    step.
    (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm 0xafc08 0xefc08 (719872 + 528392) IA1 ltac:(lia)) as [IA2 IA3] end.
    clear IA1.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_cb mm 0xafc08 0xefc08 IA2 ltac:(lia)) as [junk2 DST2] end.
    clear IA2. change (0xefc08 - 0xafc08) with 0x40000 in DST2.
    step. call (imemset_spec 0xafc08 0x40000); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST2| assumption|].
    rename POST into Z2.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (MAP : forall j, 0 <= j < 32768 -> bytes_at asegs mm (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0)))
        by (intros j Hj; apply (cb_zero_le8 _ _ _ _ Z2); lia);
      pose proof (stk_of_cb mm 0xafc08 0x40000 _ Z2 ltac:(lia)) as IA2 end.
    clear Z2. box MAP. snapshot [(0xefc40, 0x130c08); (0x13e488, 0x13e48c)]%Z MUm WMm.
    (* [comment removed for export] *)
    zstep. zstep. step. step. step.            (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm 0xefc08 0xefc40 (719872 + 528392) IA3 ltac:(lia)) as [IAg IA4];
      destruct (stk_split asegs mm 0xefc40 0xf09c0 (719872 + 528392) IA4 ltac:(lia)) as [IA5 IA6];
      destruct (stk_cb mm 0xefc40 0xf09c0 IA5 ltac:(lia)) as [junk3 DST3] end.
    clear IA3 IA4 IA5. change (0xf09c0 - 0xefc40) with 0xd80 in DST3.
    step. call (imemset_spec 0xefc40 0xd80); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST3| assumption|].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_of_cb mm 0xefc40 0xd80 _ POST ltac:(lia)) as IA5 end.
    clear POST.
    (* [comment removed for export] *)
    step. zstep. zstep. zstep. step.           (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_cb mm 0xf09c0 (719872 + 528392) IA6 ltac:(lia)) as [junk4 DST4] end.
    clear IA6. change (719872 + 528392 - 0xf09c0) with 0x40248 in DST4.
    step. call (imemset_spec 0xf09c0 0x40248); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST4| assumption|].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_of_cb mm 0xf09c0 0x40248 _ POST ltac:(lia)) as IA6 end.
    clear POST.
    (* [comment removed for export] *)
    step. step. step. step. if_lit.            (* [comment removed for export] *)
    zstep. zstep. zstep. step.                 (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm 0xf09c0 0xf09d0 (0xf09c0 + 0x40248) IA6 ltac:(lia)) as [IA7 IA8];
      destruct (stk_cb mm 0xf09c0 0xf09d0 IA7 ltac:(lia)) as [junk5 FR5] end.
    clear IA6 IA7. change (Z.to_nat (0xf09d0 - 0xf09c0)) with 16%nat in FR5.
    step. step.                                (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep.                               (* [comment removed for export] *)
    do 7 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (stk_of_rw_cells asegs mm _ _ FR1) as Q0; cbn [cells_size csize Nat.add] in Q0;
      pose proof (stk_of_rw_cells asegs mm _ _ FR5) as Q5; cbn [cells_size csize Nat.add] in Q5;
      pose proof (stk_of_cb mm _ _ _ Z1 ltac:(lia)) as Q1 end.
    assert (IA : stk asegs m1 0xafc00 (0xafc00 + 0x81030)).
    { eapply stk_merge3; [exact Q0| exact IA2| | lia| lia].
      eapply stk_merge3; [exact IAg| exact IA5| | lia| lia].
      eapply stk_merge3; [exact Q5| exact IA8| exact Q1| lia| lia]. }
    unfold ia_post. finish.
    intros j Hj. unbox MAP. eapply bytes_at_agree; [apply (MAP j); lia|].
    intros i Hi. apply MUm. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
Qed.
End Zd1.
#[using="Type"] Lemma internal_allocator_spec : ltac:(let t := eval cbv delta [internal_allocator_spec__stmt] in internal_allocator_spec__stmt in exact t).
Proof. exact internal_allocator_spec__body. Qed.
End CANSEC1.
End TwB.
End F_aintal.

(* [comment removed for export] *)
Module F_afree_iseg.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aintal.
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
Definition ficptA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk1 junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x562d0) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 p)
                  (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x562bc) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
                  (Z_to_bv 64 0x562bc) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
                  s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x56314) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2176, bv_unsigned sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2128)
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2112) [CB 2040 junk1]
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xaf800 (0xaf800 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).

Definition ficptA_spec__stmt : Prop := forall (p : Z) (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2176 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 p -> 0 <= p < 2^47 ->
  rw_cells asegs m 0xaf2fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0xa54a0 [C8 (Z_to_bv 64 0x140128); C8 (Z_to_bv 64 0xabdf8); C8 (Z_to_bv 64 0xae5f8);
                             C8 (Z_to_bv 64 0xaf2e8); C8 (Z_to_bv 64 0xaf2f0); C8 (Z_to_bv 64 0xaf2e0)] ->
  rw_cells asegs m 0x14014a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa5490 [C8 (Z_to_bv 64 0x13e0a0)] -> rw_cells asegs m 0x13e0a0 [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ficptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable p : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 0).
Variable ia : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 1).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 2).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 3).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 4).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 5).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 6).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 7).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 8).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 9).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 10).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 11).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 12).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 13).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 14).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 15).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 16).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 17).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 18).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 19).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 20).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 21).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 22).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 23).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 24).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 25).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 26).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 27).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 28).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 29).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 30).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 31).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 32).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 33).
Variable F : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 34).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 35).
Variable m : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 36).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 37).
#[using="Type"] Lemma ficptA_spec__body : ltac:(let T := type of (fun (h : ficptA_spec__stmt) => h p ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (p, (ia, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, lo)))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> PR MCS GOT CF34 PG1 PG2 FL IA Z2 RIMG RTLS RSTK.
  unfold AFREE_SYM, AFREE_PC, AIA_BASE, AIA_SIZE, AIA_FLAG, AIA_MAP1, AIA_MAP1_LEN in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2176, bv_unsigned sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 2176, bv_unsigned sp)]%Z m) as MU0.
  step.                                                          (* [comment removed for export] *)
  carve_frame 2128%nat ST.
  cb_split3 FR 16%nat 2040%nat 72%nat.
  (* [comment removed for export] *)
  repeat match type of FR with context [CB _ ?j] => lazymatch j with firstn _ _ => idtac | skipn _ _ => idtac end;
           let x := fresh "jkf" in set (x := j) in FR; clearbody x end. rw_split FR 1%nat FRa FR'. rw_split FR' 1%nat FRt FRs.
  do 8 step.                                                     (* [comment removed for export] *)
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (Z2' : ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs mm (718856 + 8 * j) (le8 (Z_to_bv 64 0)))
      by (intros Hia j Hj; eapply bytes_at_agree; [exact (Z2 Hia j Hj)|];
          intros i Hi; apply MU0; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; lia) end.
  clear Z2 MU0.
  step. call_sp internal_allocator_spec;
    [exact ST| exact CEIL| lia| exact MI| exact FL| exact IA| exact Z2'| exact PG1| exact PG2| solve_rng|].
  try rename MI0 into MI. clear Z2'.
  match goal with H : stk asegs ?mm lo _ |- _ => rename H into ST end.
  match goal with H : stk asegs ?mm 718848 _ |- _ => rename H into IA' end.
  match goal with H : rw_cells asegs ?mm 1302664 _ |- _ => rename H into FL' end.
  match goal with H : forall j, _ -> bytes_at asegs _ _ _ |- _ => rename H into MAP end.
  snapshot [(bv_unsigned sp - 2176, bv_unsigned sp)]%Z MU1 WM1.
  (* [comment removed for export] *)
  zstep. setreg 11%Z (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  step. if_lit.                                (* [comment removed for export] *)
  zstep.                                       (* [comment removed for export] *)
  remember (Z.shiftr p 32) as j eqn:Hj.
  assert (JR : 0 <= j < 32768) by (subst j; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  zstep. rewrite (Z.shiftl_mul_pow2 j 3) by lia. change (2^3) with 8. zstep.   (* [comment removed for export] *)
  pose proof (bytes_at_read8 _ _ _ (MAP j JR)) as RD.
  replace (718856 + 8 * j) with (718848 + j * 8 + 8) in RD by lia.
  step. clear RD.                              (* [comment removed for export] *)
  step. step. if_lit.                          (* [comment removed for export] *)
  clear Hj JR.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.           (* [comment removed for export] *)
  step. sstep. step.                           (* [comment removed for export] *)
  step. step. lstep. step. step.               (* [comment removed for export] *)
  step. step. if_lit.                          (* [comment removed for export] *)
  step. step. step.                            (* [comment removed for export] *)
  step. step. lstep. step.                     (* [comment removed for export] *)
  step. step. lstep. step. step.               (* [comment removed for export] *)
  step. zstep. zstep. zstep. step.             (* [comment removed for export] *)
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615. rewrite land_ones_l by lia.
  sstep.                                       (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  zstep. zstep. step. step. step. step.        (* [comment removed for export] *)
  rw_split FRa 1%nat FRa1 FRa2. apply rw_cells_C8_to_C4C4_zero in FRa2. rw_join FRa1 FRa2 FRA.
  apply evtF_done. unfold ficptA_post. do 10 eexists. eexists. eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FRA|]. split; [exact FRt|]. split; [exact FRs|]. split; [exact FL'|]. split; [exact IA'|].
  intros j0 Hj0. eapply bytes_at_agree; [exact (MAP j0 Hj0)|].
  intros i Hi. apply MU1. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
Qed.
End Zd1.
#[using="Type"] Lemma ficptA_spec : ltac:(let t := eval cbv delta [ficptA_spec__stmt] in ficptA_spec__stmt in exact t).
Proof. exact ficptA_spec__body. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ficptD_spec : forall RNG sp gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v spv : word) (F : bvmap 5 word) fc (m : amem) (lo : Z) (junk2 : list byte),
  stk asegs m lo (bv_unsigned sp + -2128) -> ATOP <= lo -> lo <= bv_unsigned sp - 2128 ->
  mem_inv asegs m ->
  (exists csA, rw_cells asegs m (bv_unsigned sp + -2128) csA /\ cells_size csA = 16%nat) ->
  (exists csT, rw_cells asegs m (bv_unsigned sp + -2112) csT /\ cells_size csT = 2040%nat) ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 spv; CB 8 junk2; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' =>
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m (seg_rom asegs)
      /\ stk asegs m lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 0x5632c) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7
              s2x s3x s4x s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5632c) fc None m (seg_rom asegs)).
Proof.
  intros until junk2. intros ST CEIL LO MI [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RTLS RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. do 7 step. zstep. step.                                 (* [comment removed for export] *)
  pose proof (rw_cells_forget asegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  release_frame FRA' ST (bv_unsigned sp + -2112).
  pose proof (rw_cells_forget asegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  release_frame FRT' ST (bv_unsigned sp + -72).
  release_frame FRS ST (bv_unsigned sp).
  apply evtF_done. split; [|exact ST].
  reflexivity.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aintal.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition ficptA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk1 junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x56338) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 p)
                  (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x56324) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
                  (Z_to_bv 64 0x56324) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
                  s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x5637c) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2176, bv_unsigned sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2128)
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2112) [CB 2040 junk1]
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xafc00 (0xafc00 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).

Definition ficptA_spec__stmt : Prop := forall (p : Z) (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2176 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 p -> 0 <= p < 2^47 ->
  rw_cells asegs m 0xaf6fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0xa5880 [C8 (Z_to_bv 64 0x140528); C8 (Z_to_bv 64 0xac1f8); C8 (Z_to_bv 64 0xae9f8);
                             C8 (Z_to_bv 64 0xaf6e8); C8 (Z_to_bv 64 0xaf6f0); C8 (Z_to_bv 64 0xaf6e0)] ->
  rw_cells asegs m 0x14054a [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa5870 [C8 (Z_to_bv 64 0x13e4a0)] -> rw_cells asegs m 0x13e4a0 [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ficptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable p : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 0).
Variable ia : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 1).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 2).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 3).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 4).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 5).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 6).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 7).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 8).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 9).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 10).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 11).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 12).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 13).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 14).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 15).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 16).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 17).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 18).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 19).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 20).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 21).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 22).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 23).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 24).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 25).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 26).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 27).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 28).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 29).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 30).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 31).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 32).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 33).
Variable F : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 34).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 35).
Variable m : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 36).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'ficptA_spec__stmt 37).
#[using="Type"] Lemma ficptA_spec__body : ltac:(let T := type of (fun (h : ficptA_spec__stmt) => h p ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (p, (ia, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, lo)))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> PR MCS GOT CF34 PG1 PG2 FL IA Z2 RIMG RTLS RSTK.
  unfold AFREE_SYM, AFREE_PC, AIA_BASE, AIA_SIZE, AIA_FLAG, AIA_MAP1, AIA_MAP1_LEN in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2176, bv_unsigned sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 2176, bv_unsigned sp)]%Z m) as MU0.
  step.                                                          (* [comment removed for export] *)
  carve_frame 2128%nat ST.
  cb_split3 FR 16%nat 2040%nat 72%nat.
  (* [comment removed for export] *)
  repeat match type of FR with context [CB _ ?j] => lazymatch j with firstn _ _ => idtac | skipn _ _ => idtac end;
           let x := fresh "jkf" in set (x := j) in FR; clearbody x end. rw_split FR 1%nat FRa FR'. rw_split FR' 1%nat FRt FRs.
  do 8 step.                                                     (* [comment removed for export] *)
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (Z2' : ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs mm (719880 + 8 * j) (le8 (Z_to_bv 64 0)))
      by (intros Hia j Hj; eapply bytes_at_agree; [exact (Z2 Hia j Hj)|];
          intros i Hi; apply MU0; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; lia) end.
  clear Z2 MU0.
  step. call_sp internal_allocator_spec;
    [exact ST| exact CEIL| lia| exact MI| exact FL| exact IA| exact Z2'| exact PG1| exact PG2| solve_rng|].
  try rename MI0 into MI. clear Z2'.
  match goal with H : stk asegs ?mm lo _ |- _ => rename H into ST end.
  match goal with H : stk asegs ?mm 719872 _ |- _ => rename H into IA' end.
  match goal with H : rw_cells asegs ?mm 1303688 _ |- _ => rename H into FL' end.
  match goal with H : forall j, _ -> bytes_at asegs _ _ _ |- _ => rename H into MAP end.
  snapshot [(bv_unsigned sp - 2176, bv_unsigned sp)]%Z MU1 WM1.
  (* [comment removed for export] *)
  zstep. setreg 11%Z (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  step. if_lit.                                (* [comment removed for export] *)
  zstep.                                       (* [comment removed for export] *)
  remember (Z.shiftr p 32) as j eqn:Hj.
  assert (JR : 0 <= j < 32768) by (subst j; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  zstep. rewrite (Z.shiftl_mul_pow2 j 3) by lia. change (2^3) with 8. zstep.   (* [comment removed for export] *)
  pose proof (bytes_at_read8 _ _ _ (MAP j JR)) as RD.
  replace (719880 + 8 * j) with (719872 + j * 8 + 8) in RD by lia.
  step. clear RD.                              (* [comment removed for export] *)
  step. step. if_lit.                          (* [comment removed for export] *)
  clear Hj JR.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.           (* [comment removed for export] *)
  step. sstep. step.                           (* [comment removed for export] *)
  step. step. lstep. step. step.               (* [comment removed for export] *)
  step. step. if_lit.                          (* [comment removed for export] *)
  step. step. step.                            (* [comment removed for export] *)
  step. step. lstep. step.                     (* [comment removed for export] *)
  step. step. lstep. step. step.               (* [comment removed for export] *)
  step. zstep. zstep. zstep. step.             (* [comment removed for export] *)
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615. rewrite land_ones_l by lia.
  sstep.                                       (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  zstep. zstep. step. step. step. step.        (* [comment removed for export] *)
  rw_split FRa 1%nat FRa1 FRa2. apply rw_cells_C8_to_C4C4_zero in FRa2. rw_join FRa1 FRa2 FRA.
  apply evtF_done. unfold ficptA_post. do 10 eexists. eexists. eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FRA|]. split; [exact FRt|]. split; [exact FRs|]. split; [exact FL'|]. split; [exact IA'|].
  intros j0 Hj0. eapply bytes_at_agree; [exact (MAP j0 Hj0)|].
  intros i Hi. apply MU1. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
Qed.
End Zd1.
#[using="Type"] Lemma ficptA_spec : ltac:(let t := eval cbv delta [ficptA_spec__stmt] in ficptA_spec__stmt in exact t).
Proof. exact ficptA_spec__body. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ficptD_spec : forall RNG sp gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v spv : word) (F : bvmap 5 word) fc (m : amem) (lo : Z) (junk2 : list byte),
  stk asegs m lo (bv_unsigned sp + -2128) -> ATOP <= lo -> lo <= bv_unsigned sp - 2128 ->
  mem_inv asegs m ->
  (exists csA, rw_cells asegs m (bv_unsigned sp + -2128) csA /\ cells_size csA = 16%nat) ->
  (exists csT, rw_cells asegs m (bv_unsigned sp + -2112) csT /\ cells_size csT = 2040%nat) ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 spv; CB 8 junk2; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' =>
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m (seg_rom asegs)
      /\ stk asegs m lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 0x56394) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7
              s2x s3x s4x s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x56394) fc None m (seg_rom asegs)).
Proof.
  intros until junk2. intros ST CEIL LO MI [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RTLS RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. do 7 step. zstep. step.                                 (* [comment removed for export] *)
  pose proof (rw_cells_forget asegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  release_frame FRA' ST (bv_unsigned sp + -2112).
  pose proof (rw_cells_forget asegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  release_frame FRT' ST (bv_unsigned sp + -72).
  release_frame FRS ST (bv_unsigned sp).
  apply evtF_done. split; [|exact ST].
  reflexivity.
Qed.
End CANSEC1.
End TwB.
End F_afree_iseg.

(* [comment removed for export] *)
Module F_aput.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition putA_post (sp gp tp s7 s8 s9 s10 s11 ra s0 s1 s2 s3 s4 s5 s6 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2
                  (Z_to_bv 64 0xab270) (Z_to_bv 64 (t + 80))
                  (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 (rup n 8)) (Z_to_bv 64 253) (Z_to_bv 64 0) a4 a5 a6 a7
                  (Z_to_bv 64 n) a3 a2 (Z_to_bv 64 hm) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3817c) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -80)
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="Type"] Lemma putA_spec : forall (t hm n : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo stb b1 ctx : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 80 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 (t + 80) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->
  rw_cells asegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xa54a8 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xabe24 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 stb); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
  0 <= n <= Q_MAX -> AIMG_HI <= hm -> hm + 16 <= ATOP ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG hm 16 ->
  evtF asegs RNG (putA_post sp gp tp s7 s8 s9 s10 s11 ra s0 s1 s2 s3 s4 s5 s6 a2 a3 F fc t hm n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x37ff4) fc None m (seg_rom asegs)).
Proof.
  intros until ctx. intros ST CEIL LO MI -> -> -> -> QK GF FL HD N H0 H1 RIMG RTLS RSTK RH.
  unfold AIMG_HI, AQUAR_Q, AQ_MAX, AFLAGS, Q_MAX, Q_MIN, Q_CACHE in *.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 80%nat ST.
  do 9 step.                                   (* [comment removed for export] *)
  step. step. step.                            (* [comment removed for export] *)
  step. step. step. if_lit.                    (* [comment removed for export] *)
  step. step. if_cases K0; zify_cond K0; [|exfalso; lia].   (* [comment removed for export] *)
  step. step. step.                            (* [comment removed for export] *)
  step. step. lstep. step. if_lit.             (* [comment removed for export] *)
  lstep. lstep. zstep. zstep. zstep.           (* [comment removed for export] *)
  rewrite Z.lor_0_l.
  zstep. zstep.                                (* [comment removed for export] *)
  change 18446744073709551608 with (2^64 - 2^3). rewrite land_align_down by lia.
  setreg 11%Z (Z_to_bv 64 (rup n 8)) ltac:(f_equal; unfold rup; Z.div_mod_to_equations; lia).
  step. step.                                  (* [comment removed for export] *)
  unfold putA_post. finish.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition putA_post (sp gp tp s7 s8 s9 s10 s11 ra s0 s1 s2 s3 s4 s5 s6 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2
                  (Z_to_bv 64 0xab670) (Z_to_bv 64 (t + 80))
                  (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 (rup n 8)) (Z_to_bv 64 253) (Z_to_bv 64 0) a4 a5 a6 a7
                  (Z_to_bv 64 n) a3 a2 (Z_to_bv 64 hm) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x381e4) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -80)
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="Type"] Lemma putA_spec : forall (t hm n : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo stb b1 ctx : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 80 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 (t + 80) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->
  rw_cells asegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xa5888 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xac224 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 stb); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
  0 <= n <= Q_MAX -> AIMG_HI <= hm -> hm + 16 <= ATOP ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG hm 16 ->
  evtF asegs RNG (putA_post sp gp tp s7 s8 s9 s10 s11 ra s0 s1 s2 s3 s4 s5 s6 a2 a3 F fc t hm n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3805c) fc None m (seg_rom asegs)).
Proof.
  intros until ctx. intros ST CEIL LO MI -> -> -> -> QK GF FL HD N H0 H1 RIMG RTLS RSTK RH.
  unfold AIMG_HI, AQUAR_Q, AQ_MAX, AFLAGS, Q_MAX, Q_MIN, Q_CACHE in *.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 80%nat ST.
  do 9 step.                                   (* [comment removed for export] *)
  step. step. step.                            (* [comment removed for export] *)
  step. step. step. if_lit.                    (* [comment removed for export] *)
  step. step. if_cases K0; zify_cond K0; [|exfalso; lia].   (* [comment removed for export] *)
  step. step. step.                            (* [comment removed for export] *)
  step. step. lstep. step. if_lit.             (* [comment removed for export] *)
  lstep. lstep. zstep. zstep. zstep.           (* [comment removed for export] *)
  rewrite Z.lor_0_l.
  zstep. zstep.                                (* [comment removed for export] *)
  change 18446744073709551608 with (2^64 - 2^3). rewrite land_align_down by lia.
  setreg 11%Z (Z_to_bv 64 (rup n 8)) ltac:(f_equal; unfold rup; Z.div_mod_to_equations; lia).
  step. step.                                  (* [comment removed for export] *)
  unfold putA_post. finish.
Qed.
End CANSEC1.
End TwB.
End F_aput.
