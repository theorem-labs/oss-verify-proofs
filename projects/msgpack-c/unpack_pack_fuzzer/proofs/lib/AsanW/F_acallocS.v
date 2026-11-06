(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require SysStepF StepF ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require ZBridge.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg AProto ABase ABytes AKit AKit2 AModelFacts APrimFacts ASecFacts ARep ARepKit ARepFrame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_alarge.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
Module F_acallocS.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ZBridge.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammapz.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_alarge.F_alarge.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Notation CALLOCS_STACK := 512 (only parsing).

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Lemma calloc_sec_spec : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R))
    (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx t PA nres nsec lo : Z) (sj : list word) (sorted : Z) (jstats jbsl jglob jslot : list byte),
  let size := needed_size n in let ms := sec_map_size n in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CALLOCS_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  ra = Z_to_bv 64 0x3cf68 ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  large_cells ctx t PA m ->

  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->

  rw_cells asegs m 0xd64c8 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xd64d8 [C1 (Z_to_bv 8 sorted)] ->
  rw_cells asegs m 0xd64e0 [CB 32 jstats] ->
  rw_cells asegs m 0xd6500 [CB 512 jbsl] ->
  rw_cells asegs m 0xd6700 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xd6718 [CB 16 jglob] ->

  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> PA mod 4096 = 0 ->
  0 <= nsec <= nres -> nres mod 16384 = 0 -> nres <= 1048576 ->
  (nsec < nres -> rw_cells asegs m (PA + 8 * nsec) [CB 8 jslot]) ->
  (PA + 8388608 <= t \/ t + 4096 <= PA) -> (PA + 8388608 <= ctx \/ ctx + 4096 <= PA) ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  AIMG_HI <= ctx -> iclr t 4096 ->

  (forall a, FRESH a = true ->
        ablk a (a + ms) /\ a + ms <= ATOP
     /\ (a + ms <= t \/ t + 4096 <= a) /\ (a + ms <= ctx \/ ctx + 4096 <= a) /\ (a + ms <= PA \/ PA + 8388608 <= a)
     /\ fill_at m (shad a) (ms / 8) 0) ->

  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ms <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->

  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec <> nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono asegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec nres lo m1 RNG' m') ->
      stk asegs m' lo (bv_unsigned sp) ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x3cf68) fc None m' (seg_rom asegs))) ->

  (forall a, FRESH a = true -> nsec = nres -> nres + 16384 <= 1048576 ->
      K a = ebind (enode (NMmap (PA + 8 * nres) 131072 3 50) (adec_mmap ATOP 131072 3)) (K2 a)) ->
  (forall a RNG' ms', FRESH a = true -> nsec = nres -> 1048576 < nres + 16384 -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall a r RNG' ms', r <> PA + 8 * nres -> 0 < r -> r + 131072 <= ATOP -> implS asegs RNG' (K2 a r) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec = nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono asegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec (nres + 16384) lo m1 RNG' m') ->
      stk asegs m' lo (bv_unsigned sp) ->
      implS asegs RNG' (K2 a (PA + 8 * nres)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x3cf68) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 ms 3 34) (adec_mmap ATOP ms 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x41420) fc None m (seg_rom asegs)).
Proof.
  intros until jslot. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> N PRIM LC CX0 CX1 T0 T1 CT2 STATS LSJ INS SRT JST JBS MTX JGL
         PA0 PA1 PAL NSR NRM NRB0 JSL DPT DPC RIMG RSTK RCTX RT RPA CXI TIC FROK UNR KONT1 SHAPE2 UNR3 UNR2 KONT2. band_lin.
  pose proof (sec_facts n N PRIM) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
  unfold AIMG_HI, AREQMAX, AINSTANCE in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  box JSL.
  iprefix.
  carve_frame 48%nat ST.
  do 7 step.
  do 3 zstep.
  replace (needed_size n <? 1) with false by (symmetry; apply Z.ltb_ge; clear -NSE RSR N; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small (needed_size n)) by (clear -NSE RSR N MSR MSB; lia). rewrite zb_lxor_ones by (clear -NSE RSR N MSR MSB; lia).
  step. if_cases K0; zify_cond K0. 2: { exfalso. clear -K0 NSE RSR MSR MSB N. lia. }
  step. step. step. if_lit.
  step. step. if_lit.
  step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 NSE RSR NB. lia. }
  zstep. zstep. step. step.
  step.
  apply evtF_done.

  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LC' : large_cells ctx t PA mm) by
      (eapply (large_cells_frame ctx t PA m mm); [exact LC | exact MU | exact WM | exact CXI |];
       apply Forall_cons; [cbn [fst snd]; left; unfold AIMG_HI, AIMG_LO; clear -SPR CEIL LO CX1 CXI; lia | apply Forall_nil]);
    assert (FROK' : forall a, FRESH a = true ->
        ablk a (a + sec_map_size n) /\ (a + sec_map_size n <= t \/ t + 4096 <= a) /\ (a + sec_map_size n <= ctx \/ ctx + 4096 <= a)
        /\ (a + sec_map_size n <= PA \/ PA + 8388608 <= a) /\ fill_at mm (shad a) (sec_map_size n / 8) 0) by
      (intros a' Ha'; destruct (FROK a' Ha') as (Y1 & Y1' & Y2 & Y3 & Y4 & Y5); split; [exact Y1|]; split; [exact Y2|]; split; [exact Y3|]; split; [exact Y4|];
       eapply fill_frame; [exact Y5 | exact MU | exact WM |]; intros _; cbn [disjoint_from]; split; [| exact I];
       rewrite shad_div; unfold ASHOFF; clear -SPR CEIL LO Y1 Y1' MSB; Z.div_mod_to_equations; lia)
  end.
  clear LC FROK.
  unbox JSL.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JSL' : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot]) by
      (intros Hlt; specialize (JSL Hlt); box JSL; carry JSL MU WM ltac:(clear -SPR CEIL LO PA0 PA1 NSR NRB0 Hlt; lia); exact JSL) end.
  clear JSL.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (large_spec RNG K K2 Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm n ctx t PA nres nsec lo sj sorted jstats jbsl jglob jslot) end.
  all: try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- forall x, _ => first [exact SHAPE2 | exact UNR3 | exact UNR | exact UNR2 | exact FROK' | exact JSL' | idtac]
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
       | |- mem_inv _ _ => assumption
       | |- large_cells _ _ _ _ => exact LC'
       | |- u64arr _ _ _ _ => exact STATS
       | |- rw_cells _ _ _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- @eq bool _ _ => exact PRIM
       | |- @eq nat _ _ => exact LSJ
       | |- _ \/ _ => assumption
       | |- rng _ _ _ => first [assumption | rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia]
       | |- _ => first [assumption | rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); unfold AREQMAX; clear -SPR CEIL LO N PA0 PA1 PAL NSR NRM NRB0 CX0 CX1 T0 T1; lia]
       end.
  all: match goal with |- implS _ _ _ _ _ => idtac | |- forall x, _ => idtac | |- ?G => idtac "REM-LARGE" G end.

  all: intros a' RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR HNS LP.
  all: pose proof LP as LP0; destruct LP0 as (FPLE & BW & A0 & A1 & A2 & MUL & WML & MIL & STL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NRB' & _); unfold AINSTANCE in A2, MUL.
  all: pose proof (ablk_lin _ _ A1) as (AL1 & AL2 & AL3 & AL4); unfold AIMG_HI in AL1.
  all: rewrite ?unsigned_lit in MUL by (clear -SPR CEIL LO; lia).
  all: rewrite ?unsigned_lit in STL by (clear -SPR CEIL LO; lia).
  all: assert (SHB : 0 <= shad a' /\ shad a' + sec_map_size n / 8 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; clear -A1 A2 MSB AL1 AL2 AL3; Z.div_mod_to_equations; lia).
  all: xport FR MUL WML ltac:(unfold AINSTANCE; clear -SPR CEIL LO A0 A1 A2 T0 T1 PA0 PA1 NSR NRB0 NRB' MSB SHB AL1 AL2 AL3; lia).
  all: apply (rng_fp_le _ _ _ _ FPLE) in RSTK; apply (rng_fp_le _ _ _ _ FPLE) in RIMG.
  all: iprefix.
  all: replace (ret_pc (Z_to_bv 64 0x414c8)) with (Z_to_bv 64 0x414c8 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  all: step; step; step; if_lit.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: release_frame FR STL (bv_unsigned sp).
  all: replace (ret_pc (Z_to_bv 64 0x3cf68)) with (Z_to_bv 64 0x3cf68 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  all: apply evtF_done.
  1: eapply (KONT1 a' RNG' m'); [exact HFR | exact HNS | | exact STL].
  2: eapply (KONT2 a' RNG' m'); [exact HFR | exact HNS | | exact STL].
  all: lazymatch type of MU with munch _ _ ?mm => exists mm end.
  all: replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by (clear; lia).
  all: split; [exact MU|]; split; [exact WM| exact LP].
Qed.
End CANSEC1.
End F_acallocS.

Module F_acallocS_x.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ZBridge.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammapz.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_alarge.F_alarge.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_alarge.ASecNull_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_alarge.F_mmapz_tol.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_alarge.F_large_x.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Notation CALLOCS_STACK := 512 (only parsing).

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Lemma calloc_sec_spec_x : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R))
    (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx t PA nres nsec lo : Z) (sj : list word) (sorted : Z) (jstats jbsl jglob jslot : list byte),
  let size := needed_size n in let ms := sec_map_size n in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CALLOCS_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  ra = Z_to_bv 64 0x3cf68 ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  large_cells ctx t PA m ->

  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->

  rw_cells asegs m 0xd64c8 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xd64d8 [C1 (Z_to_bv 8 sorted)] ->
  rw_cells asegs m 0xd64e0 [CB 32 jstats] ->
  rw_cells asegs m 0xd6500 [CB 512 jbsl] ->
  rw_cells asegs m 0xd6700 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xd6718 [CB 16 jglob] ->

  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> PA mod 4096 = 0 ->
  0 <= nsec <= nres -> nres mod 16384 = 0 -> nres <= 1048576 ->
  (nsec < nres -> rw_cells asegs m (PA + 8 * nsec) [CB 8 jslot]) ->
  (PA + 8388608 <= t \/ t + 4096 <= PA) -> (PA + 8388608 <= ctx \/ ctx + 4096 <= PA) ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  AIMG_HI <= ctx -> iclr t 4096 ->

  (forall a, FRESH a = true ->
        ablk a (a + ms) /\ a + ms <= ATOP
     /\ (a + ms <= t \/ t + 4096 <= a) /\ (a + ms <= ctx \/ ctx + 4096 <= a) /\ (a + ms <= PA \/ PA + 8388608 <= a)
     /\ fill_at m (shad a) (ms / 8) 0) ->

  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ms <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->

  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec <> nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono asegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec nres lo m1 RNG' m') ->
      stk asegs m' lo (bv_unsigned sp) ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x3cf68) fc None m' (seg_rom asegs))) ->

  (forall a, FRESH a = true -> nsec = nres -> nres + 16384 <= 1048576 ->
      K a = ebind (enode (NMmap (PA + 8 * nres) 131072 3 50) (adec_mmap ATOP 131072 3)) (K2 a)) ->
  (forall a RNG' ms', FRESH a = true -> nsec = nres -> 1048576 < nres + 16384 -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall a r RNG' ms', r <> PA + 8 * nres -> 0 < r -> r + 131072 <= ATOP -> implS asegs RNG' (K2 a r) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec = nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono asegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec (nres + 16384) lo m1 RNG' m') ->
      stk asegs m' lo (bv_unsigned sp) ->
      implS asegs RNG' (K2 a (PA + 8 * nres)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x3cf68) fc None m' (seg_rom asegs))) ->

  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono asegs m m1
                  /\ large_null_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) lo m1 RNG' m') ->
      stk asegs m' lo (bv_unsigned sp) ->
      implS asegs RNG' (K (TWO64 - 12)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x3cf68) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 ms 3 34) (adec_mmap_tol ATOP ms)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x41420) fc None m (seg_rom asegs)).
Proof.
  intros until jslot. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> N PRIM LC CX0 CX1 T0 T1 CT2 STATS LSJ INS SRT JST JBS MTX JGL
         PA0 PA1 PAL NSR NRM NRB0 JSL DPT DPC RIMG RSTK RCTX RT RPA CXI TIC FROK UNR KONT1 SHAPE2 UNR3 UNR2 KONT2 KONTN. band_lin.
  pose proof (sec_facts n N PRIM) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
  unfold AIMG_HI, AREQMAX, AINSTANCE in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  box JSL.
  iprefix.
  carve_frame 48%nat ST.
  do 7 step.
  do 3 zstep.
  replace (needed_size n <? 1) with false by (symmetry; apply Z.ltb_ge; clear -NSE RSR N; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small (needed_size n)) by (clear -NSE RSR N MSR MSB; lia). rewrite zb_lxor_ones by (clear -NSE RSR N MSR MSB; lia).
  step. if_cases K0; zify_cond K0. 2: { exfalso. clear -K0 NSE RSR MSR MSB N. lia. }
  step. step. step. if_lit.
  step. step. if_lit.
  step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 NSE RSR NB. lia. }
  zstep. zstep. step. step.
  step.
  apply evtF_done.

  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LC' : large_cells ctx t PA mm) by
      (eapply (large_cells_frame ctx t PA m mm); [exact LC | exact MU | exact WM | exact CXI |];
       apply Forall_cons; [cbn [fst snd]; left; unfold AIMG_HI, AIMG_LO; clear -SPR CEIL LO CX1 CXI; lia | apply Forall_nil]);
    assert (FROK' : forall a, FRESH a = true ->
        ablk a (a + sec_map_size n) /\ (a + sec_map_size n <= t \/ t + 4096 <= a) /\ (a + sec_map_size n <= ctx \/ ctx + 4096 <= a)
        /\ (a + sec_map_size n <= PA \/ PA + 8388608 <= a) /\ fill_at mm (shad a) (sec_map_size n / 8) 0) by
      (intros a' Ha'; destruct (FROK a' Ha') as (Y1 & Y1' & Y2 & Y3 & Y4 & Y5); split; [exact Y1|]; split; [exact Y2|]; split; [exact Y3|]; split; [exact Y4|];
       eapply fill_frame; [exact Y5 | exact MU | exact WM |]; intros _; cbn [disjoint_from]; split; [| exact I];
       rewrite shad_div; unfold ASHOFF; clear -SPR CEIL LO Y1 Y1' MSB; Z.div_mod_to_equations; lia)
  end.
  clear LC FROK.
  unbox JSL.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JSL' : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot]) by
      (intros Hlt; specialize (JSL Hlt); box JSL; carry JSL MU WM ltac:(clear -SPR CEIL LO PA0 PA1 NSR NRB0 Hlt; lia); exact JSL) end.
  clear JSL.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (large_x RNG _ K K2 Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm n ctx t PA nres nsec lo sj sorted jstats jbsl jglob jslot) end.
  all: try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- forall x, _ => first [exact SHAPE2 | exact UNR3 | exact UNR | exact UNR2 | exact FROK' | exact JSL' | idtac]
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
       | |- mem_inv _ _ => assumption
       | |- large_cells _ _ _ _ => exact LC'
       | |- u64arr _ _ _ _ => exact STATS
       | |- rw_cells _ _ _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- @eq bool _ _ => exact PRIM
       | |- @eq nat _ _ => exact LSJ
       | |- _ \/ _ => assumption
       | |- rng _ _ _ => first [assumption | rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia]
       | |- _ => first [assumption | rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); unfold AREQMAX; clear -SPR CEIL LO N PA0 PA1 PAL NSR NRM NRB0 CX0 CX1 T0 T1; lia]
       end.
  all: match goal with |- implS _ _ _ _ _ => idtac | |- forall x, _ => idtac | |- ?G => idtac "REM-LARGE" G end.

  3: { intros RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' LN.
       pose proof LN as (FPLE & MUL & WML & MIL & STL).
       rewrite ?unsigned_lit in MUL by (clear -SPR CEIL LO; lia). rewrite ?unsigned_lit in STL by (clear -SPR CEIL LO; lia).
       xport FR MUL WML ltac:(clear -SPR CEIL LO; lia).
       apply (rng_fp_le _ _ _ _ FPLE) in RSTK; apply (rng_fp_le _ _ _ _ FPLE) in RIMG.
       iprefix.
       replace (ret_pc (Z_to_bv 64 0x414c8)) with (Z_to_bv 64 0x414c8 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
       step; step; step; if_lit.
       step.
       do 8 step.
       release_frame FR STL (bv_unsigned sp).
       replace (ret_pc (Z_to_bv 64 0x3cf68)) with (Z_to_bv 64 0x3cf68 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
       apply evtF_done.
       eapply (KONTN RNG' m'); [| exact STL].
       lazymatch type of MU with munch _ _ ?mm => exists mm end.
       replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by (clear; lia).
       split; [exact MU|]; split; [exact WM| exact LN]. }

  all: intros a' RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR HNS LP.
  all: pose proof LP as LP0; destruct LP0 as (FPLE & BW & A0 & A1 & A2 & MUL & WML & MIL & STL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NRB' & _); unfold AINSTANCE in A2, MUL.
  all: pose proof (ablk_lin _ _ A1) as (AL1 & AL2 & AL3 & AL4); unfold AIMG_HI in AL1.
  all: rewrite ?unsigned_lit in MUL by (clear -SPR CEIL LO; lia).
  all: rewrite ?unsigned_lit in STL by (clear -SPR CEIL LO; lia).
  all: assert (SHB : 0 <= shad a' /\ shad a' + sec_map_size n / 8 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; clear -A1 A2 MSB AL1 AL2 AL3; Z.div_mod_to_equations; lia).
  all: xport FR MUL WML ltac:(unfold AINSTANCE; clear -SPR CEIL LO A0 A1 A2 T0 T1 PA0 PA1 NSR NRB0 NRB' MSB SHB AL1 AL2 AL3; lia).
  all: apply (rng_fp_le _ _ _ _ FPLE) in RSTK; apply (rng_fp_le _ _ _ _ FPLE) in RIMG.
  all: iprefix.
  all: replace (ret_pc (Z_to_bv 64 0x414c8)) with (Z_to_bv 64 0x414c8 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  all: step; step; step; if_lit.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: release_frame FR STL (bv_unsigned sp).
  all: replace (ret_pc (Z_to_bv 64 0x3cf68)) with (Z_to_bv 64 0x3cf68 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  all: apply evtF_done.
  1: eapply (KONT1 a' RNG' m'); [exact HFR | exact HNS | | exact STL].
  2: eapply (KONT2 a' RNG' m'); [exact HFR | exact HNS | | exact STL].
  all: lazymatch type of MU with munch _ _ ?mm => exists mm end.
  all: replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by (clear; lia).
  all: split; [exact MU|]; split; [exact WM| exact LP].
Qed.
End CANSEC1.
End F_acallocS_x.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.

Module F_acallocS.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ZBridge.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammapz.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_alarge.TwinB.F_alarge.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Notation CALLOCS_STACK := 512 (only parsing).

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Lemma calloc_sec_spec : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R))
    (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx t PA nres nsec lo : Z) (sj : list word) (sorted : Z) (jstats jbsl jglob jslot : list byte),
  let size := needed_size n in let ms := sec_map_size n in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CALLOCS_STACK ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  ra = Z_to_bv 64 0x3d8f8 ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  large_cells ctx t PA m ->

  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->

  rw_cells bsegs m 0xd8688 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells bsegs m 0xd8698 [C1 (Z_to_bv 8 sorted)] ->
  rw_cells bsegs m 0xd86a0 [CB 32 jstats] ->
  rw_cells bsegs m 0xd86c0 [CB 512 jbsl] ->
  rw_cells bsegs m 0xd88c0 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0xd88d8 [CB 16 jglob] ->

  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> PA mod 4096 = 0 ->
  0 <= nsec <= nres -> nres mod 16384 = 0 -> nres <= 1048576 ->
  (nsec < nres -> rw_cells bsegs m (PA + 8 * nsec) [CB 8 jslot]) ->
  (PA + 8388608 <= t \/ t + 4096 <= PA) -> (PA + 8388608 <= ctx \/ ctx + 4096 <= PA) ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  AIMG_HI <= ctx -> iclr t 4096 ->

  (forall a, FRESH a = true ->
        ablk a (a + ms) /\ a + ms <= ATOP
     /\ (a + ms <= t \/ t + 4096 <= a) /\ (a + ms <= ctx \/ ctx + 4096 <= a) /\ (a + ms <= PA \/ PA + 8388608 <= a)
     /\ fill_at m (shad a) (ms / 8) 0) ->

  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ms <= ATOP -> fp_le RNG RNG' ->
      implS bsegs RNG' (K a) (epostF Q) ms') ->

  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec <> nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono bsegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec nres lo m1 RNG' m') ->
      stk bsegs m' lo (bv_unsigned sp) ->
      implS bsegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x3d8f8) fc None m' (seg_rom bsegs))) ->

  (forall a, FRESH a = true -> nsec = nres -> nres + 16384 <= 1048576 ->
      K a = ebind (enode (NMmap (PA + 8 * nres) 131072 3 50) (adec_mmap ATOP 131072 3)) (K2 a)) ->
  (forall a RNG' ms', FRESH a = true -> nsec = nres -> 1048576 < nres + 16384 -> implS bsegs RNG' (K a) (epostF Q) ms') ->
  (forall a r RNG' ms', r <> PA + 8 * nres -> 0 < r -> r + 131072 <= ATOP -> implS bsegs RNG' (K2 a r) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec = nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono bsegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec (nres + 16384) lo m1 RNG' m') ->
      stk bsegs m' lo (bv_unsigned sp) ->
      implS bsegs RNG' (K2 a (PA + 8 * nres)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x3d8f8) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap 0 ms 3 34) (adec_mmap ATOP ms 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x41db0) fc None m (seg_rom bsegs)).
Proof.
  intros until jslot. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> N PRIM LC CX0 CX1 T0 T1 CT2 STATS LSJ INS SRT JST JBS MTX JGL
         PA0 PA1 PAL NSR NRM NRB0 JSL DPT DPC RIMG RSTK RCTX RT RPA CXI TIC FROK UNR KONT1 SHAPE2 UNR3 UNR2 KONT2. band_lin.
  pose proof (sec_facts n N PRIM) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
  unfold AIMG_HI, AREQMAX, AINSTANCE in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  box JSL.
  iprefix.
  carve_frame 48%nat ST.
  do 7 step.
  do 3 zstep.
  replace (needed_size n <? 1) with false by (symmetry; apply Z.ltb_ge; clear -NSE RSR N; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small (needed_size n)) by (clear -NSE RSR N MSR MSB; lia). rewrite zb_lxor_ones by (clear -NSE RSR N MSR MSB; lia).
  step. if_cases K0; zify_cond K0. 2: { exfalso. clear -K0 NSE RSR MSR MSB N. lia. }
  step. step. step. if_lit.
  step. step. if_lit.
  step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 NSE RSR NB. lia. }
  zstep. zstep. step. step.
  step.
  apply evtF_done.

  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LC' : large_cells ctx t PA mm) by
      (eapply (large_cells_frame ctx t PA m mm); [exact LC | exact MU | exact WM | exact CXI |];
       apply Forall_cons; [cbn [fst snd]; left; unfold AIMG_HI, AIMG_LO; clear -SPR CEIL LO CX1 CXI; lia | apply Forall_nil]);
    assert (FROK' : forall a, FRESH a = true ->
        ablk a (a + sec_map_size n) /\ (a + sec_map_size n <= t \/ t + 4096 <= a) /\ (a + sec_map_size n <= ctx \/ ctx + 4096 <= a)
        /\ (a + sec_map_size n <= PA \/ PA + 8388608 <= a) /\ fill_at mm (shad a) (sec_map_size n / 8) 0) by
      (intros a' Ha'; destruct (FROK a' Ha') as (Y1 & Y1' & Y2 & Y3 & Y4 & Y5); split; [exact Y1|]; split; [exact Y2|]; split; [exact Y3|]; split; [exact Y4|];
       eapply fill_frame; [exact Y5 | exact MU | exact WM |]; intros _; cbn [disjoint_from]; split; [| exact I];
       rewrite shad_div; unfold ASHOFF; clear -SPR CEIL LO Y1 Y1' MSB; Z.div_mod_to_equations; lia)
  end.
  clear LC FROK.
  unbox JSL.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JSL' : nsec < nres -> rw_cells bsegs mm (PA + 8 * nsec) [CB 8 jslot]) by
      (intros Hlt; specialize (JSL Hlt); box JSL; carry JSL MU WM ltac:(clear -SPR CEIL LO PA0 PA1 NSR NRB0 Hlt; lia); exact JSL) end.
  clear JSL.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (large_spec RNG K K2 Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm n ctx t PA nres nsec lo sj sorted jstats jbsl jglob jslot) end.
  all: try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- forall x, _ => first [exact SHAPE2 | exact UNR3 | exact UNR | exact UNR2 | exact FROK' | exact JSL' | idtac]
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
       | |- mem_inv _ _ => assumption
       | |- large_cells _ _ _ _ => exact LC'
       | |- u64arr _ _ _ _ => exact STATS
       | |- rw_cells _ _ _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- @eq bool _ _ => exact PRIM
       | |- @eq nat _ _ => exact LSJ
       | |- _ \/ _ => assumption
       | |- rng _ _ _ => first [assumption | rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia]
       | |- _ => first [assumption | rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); unfold AREQMAX; clear -SPR CEIL LO N PA0 PA1 PAL NSR NRM NRB0 CX0 CX1 T0 T1; lia]
       end.
  all: match goal with |- implS _ _ _ _ _ => idtac | |- forall x, _ => idtac | |- ?G => idtac "REM-LARGE" G end.

  all: intros a' RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR HNS LP.
  all: pose proof LP as LP0; destruct LP0 as (FPLE & BW & A0 & A1 & A2 & MUL & WML & MIL & STL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NRB' & _); unfold AINSTANCE in A2, MUL.
  all: pose proof (ablk_lin _ _ A1) as (AL1 & AL2 & AL3 & AL4); unfold AIMG_HI in AL1.
  all: rewrite ?unsigned_lit in MUL by (clear -SPR CEIL LO; lia).
  all: rewrite ?unsigned_lit in STL by (clear -SPR CEIL LO; lia).
  all: assert (SHB : 0 <= shad a' /\ shad a' + sec_map_size n / 8 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; clear -A1 A2 MSB AL1 AL2 AL3; Z.div_mod_to_equations; lia).
  all: xport FR MUL WML ltac:(unfold AINSTANCE; clear -SPR CEIL LO A0 A1 A2 T0 T1 PA0 PA1 NSR NRB0 NRB' MSB SHB AL1 AL2 AL3; lia).
  all: apply (rng_fp_le _ _ _ _ FPLE) in RSTK; apply (rng_fp_le _ _ _ _ FPLE) in RIMG.
  all: iprefix.
  all: replace (ret_pc (Z_to_bv 64 0x41e58)) with (Z_to_bv 64 0x41e58 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  all: step; step; step; if_lit.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: release_frame FR STL (bv_unsigned sp).
  all: replace (ret_pc (Z_to_bv 64 0x3d8f8)) with (Z_to_bv 64 0x3d8f8 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  all: apply evtF_done.
  1: eapply (KONT1 a' RNG' m'); [exact HFR | exact HNS | | exact STL].
  2: eapply (KONT2 a' RNG' m'); [exact HFR | exact HNS | | exact STL].
  all: lazymatch type of MU with munch _ _ ?mm => exists mm end.
  all: replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by (clear; lia).
  all: split; [exact MU|]; split; [exact WM| exact LP].
Qed.
End CANSEC1.
End F_acallocS.

Module F_acallocS_x.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ZBridge.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammapz.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_alarge.TwinB.F_alarge.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_alarge.TwinB.ASecNull_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_alarge.TwinB.F_mmapz_tol.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_alarge.TwinB.F_large_x.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Notation CALLOCS_STACK := 512 (only parsing).

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Lemma calloc_sec_spec_x : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R))
    (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx t PA nres nsec lo : Z) (sj : list word) (sorted : Z) (jstats jbsl jglob jslot : list byte),
  let size := needed_size n in let ms := sec_map_size n in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CALLOCS_STACK ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  ra = Z_to_bv 64 0x3d8f8 ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  large_cells ctx t PA m ->

  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->

  rw_cells bsegs m 0xd8688 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells bsegs m 0xd8698 [C1 (Z_to_bv 8 sorted)] ->
  rw_cells bsegs m 0xd86a0 [CB 32 jstats] ->
  rw_cells bsegs m 0xd86c0 [CB 512 jbsl] ->
  rw_cells bsegs m 0xd88c0 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0xd88d8 [CB 16 jglob] ->

  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> PA mod 4096 = 0 ->
  0 <= nsec <= nres -> nres mod 16384 = 0 -> nres <= 1048576 ->
  (nsec < nres -> rw_cells bsegs m (PA + 8 * nsec) [CB 8 jslot]) ->
  (PA + 8388608 <= t \/ t + 4096 <= PA) -> (PA + 8388608 <= ctx \/ ctx + 4096 <= PA) ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  AIMG_HI <= ctx -> iclr t 4096 ->

  (forall a, FRESH a = true ->
        ablk a (a + ms) /\ a + ms <= ATOP
     /\ (a + ms <= t \/ t + 4096 <= a) /\ (a + ms <= ctx \/ ctx + 4096 <= a) /\ (a + ms <= PA \/ PA + 8388608 <= a)
     /\ fill_at m (shad a) (ms / 8) 0) ->

  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ms <= ATOP -> fp_le RNG RNG' ->
      implS bsegs RNG' (K a) (epostF Q) ms') ->

  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec <> nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono bsegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec nres lo m1 RNG' m') ->
      stk bsegs m' lo (bv_unsigned sp) ->
      implS bsegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x3d8f8) fc None m' (seg_rom bsegs))) ->

  (forall a, FRESH a = true -> nsec = nres -> nres + 16384 <= 1048576 ->
      K a = ebind (enode (NMmap (PA + 8 * nres) 131072 3 50) (adec_mmap ATOP 131072 3)) (K2 a)) ->
  (forall a RNG' ms', FRESH a = true -> nsec = nres -> 1048576 < nres + 16384 -> implS bsegs RNG' (K a) (epostF Q) ms') ->
  (forall a r RNG' ms', r <> PA + 8 * nres -> 0 < r -> r + 131072 <= ATOP -> implS bsegs RNG' (K2 a r) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec = nres ->
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono bsegs m m1
                  /\ large_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) a n ctx t PA nres nsec (nres + 16384) lo m1 RNG' m') ->
      stk bsegs m' lo (bv_unsigned sp) ->
      implS bsegs RNG' (K2 a (PA + 8 * nres)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x3d8f8) fc None m' (seg_rom bsegs))) ->

  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      (exists m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 /\ wmono bsegs m m1
                  /\ large_null_post RNG (Z_to_bv 64 (bv_unsigned sp - 48)) lo m1 RNG' m') ->
      stk bsegs m' lo (bv_unsigned sp) ->
      implS bsegs RNG' (K (TWO64 - 12)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x3d8f8) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap 0 ms 3 34) (adec_mmap_tol ATOP ms)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x41db0) fc None m (seg_rom bsegs)).
Proof.
  intros until jslot. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> N PRIM LC CX0 CX1 T0 T1 CT2 STATS LSJ INS SRT JST JBS MTX JGL
         PA0 PA1 PAL NSR NRM NRB0 JSL DPT DPC RIMG RSTK RCTX RT RPA CXI TIC FROK UNR KONT1 SHAPE2 UNR3 UNR2 KONT2 KONTN. band_lin.
  pose proof (sec_facts n N PRIM) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
  unfold AIMG_HI, AREQMAX, AINSTANCE in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  box JSL.
  iprefix.
  carve_frame 48%nat ST.
  do 7 step.
  do 3 zstep.
  replace (needed_size n <? 1) with false by (symmetry; apply Z.ltb_ge; clear -NSE RSR N; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small (needed_size n)) by (clear -NSE RSR N MSR MSB; lia). rewrite zb_lxor_ones by (clear -NSE RSR N MSR MSB; lia).
  step. if_cases K0; zify_cond K0. 2: { exfalso. clear -K0 NSE RSR MSR MSB N. lia. }
  step. step. step. if_lit.
  step. step. if_lit.
  step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 NSE RSR NB. lia. }
  zstep. zstep. step. step.
  step.
  apply evtF_done.

  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LC' : large_cells ctx t PA mm) by
      (eapply (large_cells_frame ctx t PA m mm); [exact LC | exact MU | exact WM | exact CXI |];
       apply Forall_cons; [cbn [fst snd]; left; unfold AIMG_HI, AIMG_LO; clear -SPR CEIL LO CX1 CXI; lia | apply Forall_nil]);
    assert (FROK' : forall a, FRESH a = true ->
        ablk a (a + sec_map_size n) /\ (a + sec_map_size n <= t \/ t + 4096 <= a) /\ (a + sec_map_size n <= ctx \/ ctx + 4096 <= a)
        /\ (a + sec_map_size n <= PA \/ PA + 8388608 <= a) /\ fill_at mm (shad a) (sec_map_size n / 8) 0) by
      (intros a' Ha'; destruct (FROK a' Ha') as (Y1 & Y1' & Y2 & Y3 & Y4 & Y5); split; [exact Y1|]; split; [exact Y2|]; split; [exact Y3|]; split; [exact Y4|];
       eapply fill_frame; [exact Y5 | exact MU | exact WM |]; intros _; cbn [disjoint_from]; split; [| exact I];
       rewrite shad_div; unfold ASHOFF; clear -SPR CEIL LO Y1 Y1' MSB; Z.div_mod_to_equations; lia)
  end.
  clear LC FROK.
  unbox JSL.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JSL' : nsec < nres -> rw_cells bsegs mm (PA + 8 * nsec) [CB 8 jslot]) by
      (intros Hlt; specialize (JSL Hlt); box JSL; carry JSL MU WM ltac:(clear -SPR CEIL LO PA0 PA1 NSR NRB0 Hlt; lia); exact JSL) end.
  clear JSL.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (large_x RNG _ K K2 Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm n ctx t PA nres nsec lo sj sorted jstats jbsl jglob jslot) end.
  all: try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- forall x, _ => first [exact SHAPE2 | exact UNR3 | exact UNR | exact UNR2 | exact FROK' | exact JSL' | idtac]
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
       | |- mem_inv _ _ => assumption
       | |- large_cells _ _ _ _ => exact LC'
       | |- u64arr _ _ _ _ => exact STATS
       | |- rw_cells _ _ _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- @eq bool _ _ => exact PRIM
       | |- @eq nat _ _ => exact LSJ
       | |- _ \/ _ => assumption
       | |- rng _ _ _ => first [assumption | rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia]
       | |- _ => first [assumption | rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); unfold AREQMAX; clear -SPR CEIL LO N PA0 PA1 PAL NSR NRM NRB0 CX0 CX1 T0 T1; lia]
       end.
  all: match goal with |- implS _ _ _ _ _ => idtac | |- forall x, _ => idtac | |- ?G => idtac "REM-LARGE" G end.

  3: { intros RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' LN.
       pose proof LN as (FPLE & MUL & WML & MIL & STL).
       rewrite ?unsigned_lit in MUL by (clear -SPR CEIL LO; lia). rewrite ?unsigned_lit in STL by (clear -SPR CEIL LO; lia).
       xport FR MUL WML ltac:(clear -SPR CEIL LO; lia).
       apply (rng_fp_le _ _ _ _ FPLE) in RSTK; apply (rng_fp_le _ _ _ _ FPLE) in RIMG.
       iprefix.
       replace (ret_pc (Z_to_bv 64 0x41e58)) with (Z_to_bv 64 0x41e58 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
       step; step; step; if_lit.
       step.
       do 8 step.
       release_frame FR STL (bv_unsigned sp).
       replace (ret_pc (Z_to_bv 64 0x3d8f8)) with (Z_to_bv 64 0x3d8f8 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
       apply evtF_done.
       eapply (KONTN RNG' m'); [| exact STL].
       lazymatch type of MU with munch _ _ ?mm => exists mm end.
       replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by (clear; lia).
       split; [exact MU|]; split; [exact WM| exact LN]. }

  all: intros a' RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR HNS LP.
  all: pose proof LP as LP0; destruct LP0 as (FPLE & BW & A0 & A1 & A2 & MUL & WML & MIL & STL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NRB' & _); unfold AINSTANCE in A2, MUL.
  all: pose proof (ablk_lin _ _ A1) as (AL1 & AL2 & AL3 & AL4); unfold AIMG_HI in AL1.
  all: rewrite ?unsigned_lit in MUL by (clear -SPR CEIL LO; lia).
  all: rewrite ?unsigned_lit in STL by (clear -SPR CEIL LO; lia).
  all: assert (SHB : 0 <= shad a' /\ shad a' + sec_map_size n / 8 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; clear -A1 A2 MSB AL1 AL2 AL3; Z.div_mod_to_equations; lia).
  all: xport FR MUL WML ltac:(unfold AINSTANCE; clear -SPR CEIL LO A0 A1 A2 T0 T1 PA0 PA1 NSR NRB0 NRB' MSB SHB AL1 AL2 AL3; lia).
  all: apply (rng_fp_le _ _ _ _ FPLE) in RSTK; apply (rng_fp_le _ _ _ _ FPLE) in RIMG.
  all: iprefix.
  all: replace (ret_pc (Z_to_bv 64 0x41e58)) with (Z_to_bv 64 0x41e58 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  all: step; step; step; if_lit.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: step.
  all: release_frame FR STL (bv_unsigned sp).
  all: replace (ret_pc (Z_to_bv 64 0x3d8f8)) with (Z_to_bv 64 0x3d8f8 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  all: apply evtF_done.
  1: eapply (KONT1 a' RNG' m'); [exact HFR | exact HNS | | exact STL].
  2: eapply (KONT2 a' RNG' m'); [exact HFR | exact HNS | | exact STL].
  all: lazymatch type of MU with munch _ _ ?mm => exists mm end.
  all: replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by (clear; lia).
  all: split; [exact MU|]; split; [exact WM| exact LP].
Qed.
End CANSEC1.
End F_acallocS_x.
End TwinB.
