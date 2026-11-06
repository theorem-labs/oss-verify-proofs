(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LMeasure.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_mmapN.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_map.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_pop1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_loops.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_refillA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_zone.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_pop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kitL.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module RTW_p_refill.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_depot_n2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_mmapN.RTW_sec_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_map OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1.RTW_p_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_loops OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1.RTW_p_efa OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_refillA.RTW_p_pop2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1.RTW_p_gfa OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1.RTW_p_refillw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_zone OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_refillA.RTW_p_absf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_pop OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_lib.RTW_sec_alloc5 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_q_needs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_refillA OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1.RTW_p_libo OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kitL.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

(* [comment removed for export] *)
Local Ltac djlr := first [left; lia | right; lia | lia].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac djlrk K := first [left; K; lia | right; K; lia | K; lia].
(* [comment removed for export] *)
Ltac subfpk K :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; repeat match goal with H' : ~ _ |- _ => clear H' end; first [exact Cq| K; lia] end ].


(* [comment removed for export] *)
(* [comment removed for export] *)
Section RW.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (st : rtstate) (cls lo : Z).
  Let S := st_spacebeg st.
  Let t := st_t st.
  Let P := acache st.
  Let pc := pcaddr st cls.
  Let CH := pc + 16.
  Let stt := P + 2560.
  Let Rc := rinfo st cls.
  Let RB := rbeg st cls.
  Let FA := fabeg st cls.
  Let r := rg st cls.
  Let alloc := r_allocated r.
  Let mapped := r_mapped r.
  Let fam := r_mapped_fa r.
  Let nf := num_freed st cls.
  Let n := nrefill cls.
  Let exhb := r_exhausted r.
  Let usz := Z.min 262144 (3758096384 - mapped).
  Hypothesis HR : RTREP st m.
  Hypothesis WF : RTWF st.
  Hypothesis HM : RTMODEL st mo.
  Hypothesis HG : GWIN st m mo (mkG G R).
  Hypothesis Hc : 1 <= cls <= 30.
  Hypothesis HC0 : cch st cls = [].
  Hypothesis TP : tp = wz ATP.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + AREFILL_STACK <= bv_unsigned sp.

  Let ENTRY := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz pc) (wz A_ALLOC) (wz cls) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AREFILL) fc None m (seg_rom asegs).
  Let RET (rv : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte) :=
    MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz rv) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom asegs).
  (* [comment removed for export] *)
  Let XST (q : Z) (x5 x6 x7 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) (m1 : word -> option byte) :=
    MS (mkR (wz 0x370a0) (wz (bv_unsigned sp + -32 + -128 + -64)) gp tp x5 x6 x7 (wz Rc) (wz stt) (wz 0) (wz (KFREEARRAY_OFF + 1)) (wz cls) (wz (mapped + 262144)) (wz q) x15 x16 x17
             (wz RB) (wz 262144) (wz mapped) (wz (csize cls)) (wz n) (wz MTX_LOCKED) x24 x25 s10 s11 x28 x29 x30 x31)
       F (wz 0x373b4) fc None m1 (seg_rom asegs).

  Lemma refill_walk : forall (pop um fm spin : bool) (Q : machine_state -> Model -> lghost -> Prop) (jr je js : list byte),
    let q := n - nf in
    let total := alloc + csize cls * q in
    let mapped' := mapped + (if um then 262144 else 0) in
    let Nv := if pop then (mapped' - alloc) / csize cls else 0 in
    let nm := (4 * (nf + Nv) + 262143) / 262144 * 262144 in
    let fam' := if fm then nm else fam in
    let base := nf + Nv - n in
    let U := RB + mapped in
    let Ufa := FA + fam in
    let D := FA + 4 * nf in
    let mo1 := if um then mm_commit (wz U) (wz 262144) mo else mo in
    let G1 := if um then (SH U, SH U + 32768) :: G else G in
    let R1 := R - (if um then LUMP else 0) in
    let mo2 := if fm then mm_commit (wz Ufa) (wz 262144) mo1 else mo1 in
    let G2 := if fm then (SH Ufa, SH Ufa + 32768) :: G1 else G1 in
    let R2 := R1 - (if fm then LUMP else 0) in
    rw_cells asegs m (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 (if exhb then 1 else 0)); CB 3 je; CB 56 js] ->
    pop = (nf <? n) -> um = pop && (mapped <? total) -> fm = pop && (fam <? 4 * (nf + Nv)) ->
    (if um then LUMP else 0) + (if fm then LUMP else 0) <= R ->
    (* [comment removed for export] *)
    (pop = true -> um = true -> exhb = true -> mapped = KFREEARRAY_OFF ->
     forall x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (m' : word -> option byte),
       mem_inv asegs m' -> munch (WTOT lo (bv_unsigned sp) P pc t Rc U usz FA nf) m m' -> wmono asegs m m' -> stk asegs m' lo (bv_unsigned sp) ->
       rw_cells asegs m' Rc [C8 (wz 0); C8 (wz 0); C8 (Z_to_bv 64 nf)] -> rw_cells asegs m' (Rc + 24) [C8 (Z_to_bv 64 fam)] ->
       rw_cells asegs m' (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 1); CB 3 je; CB 56 js] ->
       pch_at st cls m' 0 -> pco_at st m' ->
       LSCPS asegs Q (RET 0 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m') mo (mkG G R)) ->
    (* [comment removed for export] *)
    (pop = true -> um = true -> exhb = false -> mapped = KFREEARRAY_OFF ->
     forall x5 x6 x7 x15 x16 x17 x18 x24 x25 x28 x29 x30 x31 (m1 : word -> option byte) (jR jG : list byte) (tj1 tj2 sa : word),
       mem_inv asegs m1 -> munch (WTOT lo (bv_unsigned sp) P pc t Rc U usz FA nf) m m1 -> wmono asegs m m1 -> stk asegs m1 lo (bv_unsigned sp + -32 + -128 + -64) ->
       rw_cells asegs m1 (bv_unsigned sp + -32) (refill_frame jR s1 s0 ra) ->
       rw_cells asegs m1 (bv_unsigned sp + -32 + -128) (gfa_frame jG s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 (wz n) (wz pc) (wz 0x36d24)) ->
       rw_cells asegs m1 (bv_unsigned sp + -32 + -128 + -64) (pop_frame (wz n) (wz CH) (wz FA) (wz 2305843009213693952) x18 (wz A_ALLOC) (wz Rc) (wz 0x370a0)) ->
       rw_cells asegs m1 Rc [C8 (wz MTX_LOCKED); C8 (wz 0); C8 (Z_to_bv 64 nf)] -> rw_cells asegs m1 (Rc + 24) [C8 (Z_to_bv 64 fam)] ->
       rw_cells asegs m1 (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 0); CB 3 je; CB 56 js] ->
       rw_cells asegs m1 (t + 2872) [C8 tj1; C8 tj2] -> rw_cells asegs m1 (stt + 24) [C8 sa] ->
       pch_at st cls m1 0 -> pco_at st m1 ->
       LSCPS asegs Q (XST q x5 x6 x7 x15 x16 x17 x24 x25 x28 x29 x30 x31 m1) mo (mkG G R)) ->
    (* [comment removed for export] *)
    True ->
    True ->
    (* [comment removed for export] *)
    ((um = true -> mapped + 262144 <= KFREEARRAY_OFF) ->
     forall x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (m' : word -> option byte) (js' : list byte) (fa : list Z),
       mem_inv asegs m' -> munch (WTOT lo (bv_unsigned sp) P pc t Rc U usz FA nf) m m' -> wmono asegs m m' -> stk asegs m' lo (bv_unsigned sp) ->
       rw_cells asegs m' Rc [C8 (wz 0); C8 (wz 0); C8 (Z_to_bv 64 base)] -> rw_cells asegs m' (Rc + 24) [C8 (Z_to_bv 64 fam')] ->
       rw_cells asegs m' (Rc + 32) [C8 (Z_to_bv 64 (alloc + Nv * csize cls)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped'); C8 (Z_to_bv 64 0); CB 4 jr;
                                  C1 (Z_to_bv 8 (if pop then 0 else if exhb then 1 else 0)); CB 3 je; CB 56 js'] ->
       stk asegs m' FA (FA + fam') ->
       u32arr asegs m' D (fill_vals alloc (csize cls) (Z.to_nat Nv)) ->
       (if um then stk asegs m' U (U + 262144) /\ rw_cells asegs m' (SH U) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))] else True) ->
       (if fm then rw_cells asegs m' (SH Ufa) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))] else True) ->
       length fa = Z.to_nat n -> (forall i, 0 <= i < n -> nthz fa i 0 = nthz (r_fa r ++ newc cls (ncarved st cls) Nv) (base + i) 0) ->
       u32arr asegs m' CH (wl fa) ->
       pch_at st cls m' n -> pco_at st m' ->
       LSCPS asegs Q (RET 1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m') mo2 (mkG G2 R2)) ->
    LSCPS asegs Q ENTRY mo (mkG G R).
  Proof.
    intros pop um fm spin Q jr je js. cbv zeta. intros RIb EPOP EUM EFM HRR.
    (* [comment removed for export] *)
    assert (Hcls : 0 <= cls < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct LO as [HCE LO2]. pose proof HCE as HCEn. idtac. unfold AREFILL_STACK in LO2.
    pose proof (t_range st WF) as [TRo TRc]. (nelimp (oclr_lin _ _ TRo ltac:(lia)) 3%nat; intros TRa TRb TRi). unfold KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_LO, AIMG_HI in TRb, TRi. assert (TR : 4096 <= t /\ t + 4096 <= alloc_ceiling) by (split; assumption).
    pose proof (ctx_range st WF) as [CRo CRc]. (nelimp (oclr_lin _ _ CRo ltac:(lia)) 3%nat; intros CRa CRb CRi). unfold KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_LO, AIMG_HI in CRb, CRi. assert (CR : 4096 <= st_ctx st /\ st_ctx st + 160 <= alloc_ceiling) by (split; assumption).
    (nelimp (cls_facts st WF cls Hc) 14%nat; intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14).
    assert (G1 : 17594333495296 <= RB) by exact C1. assert (G2 : st_pbase st <= RB) by exact C2. assert (G3 : RB + 4294967296 <= ris st) by exact C3.
    assert (G4 : ris st + 4096 <= st_pbase st + 137439023104) by exact C4. assert (G5 : st_pbase st + 137439023104 <= alloc_ceiling) by exact C5.
    assert (G6 : 0 <= alloc <= mapped) by exact C6. assert (G7 : mapped <= 3758096384) by exact C7. assert (G8 : 0 <= nf) by exact C8.
    assert (G9 : 4 * nf <= fam) by exact C9. assert (G10 : fam <= 536870912) by exact C10.
    assert (G11 : hideP (RB mod 8 = 0)) by exact C11. assert (G12 : hideP (mapped mod 8 = 0)) by exact C12.
    assert (EFA : FA = RB + 3758096384) by exact C13. assert (ERC : Rc = ris st + 128 * cls) by exact C14.
    clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14.
    (nelimp (S_range st WF) 3%nat; intros SR1' SR2' SR3'). assert (SR1 : st_pbase st <= S) by exact SR1'. assert (SR2 : S + 137438953472 + 4096 <= st_pbase st + 137439023104) by exact SR2'.
    assert (SR3 : hideP (S mod 4096 = 0)) by exact SR3'. clear SR1' SR2' SR3'.
    assert (SAL : hideP (S mod 65536 = 0)) by exact (wb_S_align st (wf_base_ok st WF)).
    (nelimp (P_range st WF) 3%nat; intros PR1' PR2' PR3'). assert (PR1 : 17594333495296 <= st_pbase st) by exact PR1'. assert (PR2 : st_pbase st + 137439023104 <= alloc_ceiling) by exact PR2'.
    assert (PR3 : hideP (st_pbase st mod 4096 = 0)) by exact PR3'. clear PR1' PR2' PR3'.
    assert (ERB : RB = S + cls * 4294967296) by (unfold RB; rewrite (rbeg_val st); reflexivity).
    assert (ERIS : ris st = S + 137438953472) by reflexivity.
    pose proof (wf_class_ok st WF cls Hcls) as WC.
    assert (MA : hideP (mapped mod 262144 = 0)) by exact (wc_mapped_align st cls WC). assert (FAL : hideP (fam mod 262144 = 0)) by exact (wc_fa_align st cls WC).
    assert (FA0 : 0 <= fam) by exact (wc_fa_nonneg st cls WC). assert (RES : mapped <= alloc + csize cls + 262144) by exact (wc_residue st cls WC).
    pose proof (cmaxcount_range cls ltac:(lia)) as [CMR CME']. assert (CME : cmaxcount cls = 2 * n) by exact CME'. clear CME'.
    pose proof (nrefill_eq cls ltac:(lia)) as [_ NR']. assert (NR : 1 <= n <= 8) by exact NR'. clear NR'.
    (nelimp (slack_ok' cls Hc) 3%nat; intros SL1' _ _). assert (SL1 : 64 + 2 * (n * csize cls) - 2 * csize cls <= 2048) by exact SL1'. clear SL1'.
    pose proof (csize_pos cls ltac:(lia)) as CP. pose proof (csize_le64k' cls Hc) as CL.
    assert (PCB : pc = P + 80 * cls /\ P = t + 208 /\ CH = pc + 16 /\ stt = P + 2560) by (repeat split; reflexivity).
    (nelim PCB 4%nat; intros EPC EP ECH ESTT).
    assert (E32 : bv_unsigned (wz (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (unfold wz; apply unsigned_lit; clear -RSP LO2 HCEn; lia).
    assert (E160 : bv_unsigned (wz (bv_unsigned sp + -32 + -128)) = bv_unsigned sp + -32 + -128) by (unfold wz; apply unsigned_lit; clear -RSP LO2 HCEn; lia).
    pose proof E32 as E32'. unfold wz in E32'.
    assert (E224 : bv_unsigned (wz (bv_unsigned sp + -32 + -128 + -64)) = bv_unsigned sp + -32 + -128 + -64) by (unfold wz; apply unsigned_lit; clear -RSP LO2 HCEn; lia).
    (* [comment removed for export] *)
    assert (TDJ : hideP (t + 4096 <= st_pbase st \/ st_pbase st + 137439023104 <= t)).
    { pose proof (loose_vs_prim st WF t 4096 (wb_t_loose st (wf_base_ok st WF))) as H0. assert (H : st_pbase st + 137439023104 <= t \/ t + 4096 <= st_pbase st) by exact H0. unfold hideP. clear -H. lia. }
    assert (CDJ : hideP (st_ctx st + 160 <= st_pbase st \/ st_pbase st + 137439023104 <= st_ctx st)).
    { (nelim (wb_ctx_loose st (wf_base_ok st WF)) 5%nat; intros b k Hin B1 B2). pose proof (loose_vs_prim st WF b k Hin) as H0. assert (H : st_pbase st + 137439023104 <= b \/ b + k <= st_pbase st) by exact H0. unfold hideP. clear -H B1 B2. lia. }
    (* [comment removed for export] *)
    assert (RCT : hideP (t + 4096 <= Rc \/ Rc + 128 <= t)) by (unfold hideP in TDJ |- *; clear -TDJ G2 G3 G4 ERC Hc; destruct TDJ; [left| right]; lia).
    assert (RCC : hideP (st_ctx st + 160 <= Rc \/ Rc + 128 <= st_ctx st)) by (unfold hideP in CDJ |- *; clear -CDJ G2 G3 G4 ERC Hc; destruct CDJ; [left| right]; lia).
    assert (RBT : hideP (t + 4096 <= RB \/ RB + 4294967296 <= t)) by (unfold hideP in TDJ |- *; clear -TDJ G2 G3 G4; destruct TDJ; [left| right]; lia).
    assert (RBC : hideP (st_ctx st + 160 <= RB \/ RB + 4294967296 <= st_ctx st)) by (unfold hideP in CDJ |- *; clear -CDJ G2 G3 G4; destruct CDJ; [left| right]; lia).
    (* [comment removed for export] *)
    (nelim (refill_cells st m cls HR WF Hc HC0) 18%nat; intros jr0 je0 js0 tj1 tj2 sa AC32' AC40 AC48' AC56 RIa' RI24' _ TST' SA' VFA' EN' _).
    assert (AC32 : ro_cells asegs m 0xa6c38 [C8 (Z_to_bv 64 S)]) by exact AC32'. assert (AC48 : ro_cells asegs m 0xa6c48 [C8 (Z_to_bv 64 (ris st))]) by exact AC48'.
    assert (RIa : rw_cells asegs m Rc [C8 (wz 0); C8 (wz 0); C8 (Z_to_bv 64 nf)]) by exact RIa'. assert (RI24 : rw_cells asegs m (Rc + 24) [C8 (Z_to_bv 64 fam)]) by exact RI24'.
    assert (TST : rw_cells asegs m (t + 2872) [C8 tj1; C8 tj2]) by exact TST'. assert (SA : rw_cells asegs m (stt + 24) [C8 sa]) by (replace (stt + 24) with (st_t st + 2768 + 24) by (rewrite ESTT, EP; unfold t; clear; lia); exact SA').
    assert (VFA : stk asegs m FA (FA + fam)) by exact VFA'. assert (EN : forall i, 0 <= i < nf -> rw_cells asegs m (FA + 4 * i) [W4 (nthz (r_fa r) i 0)]) by exact EN'.
    clear AC32' AC48' RIa' RI24' TST' SA' VFA' EN'.
    pose proof (leafc_of_RTREP st m HR) as LC. pose proof (mmap_cells st m HR) as HC.
    pose proof (artcells_icpt m (rtrep_artcells st m HR)) as IC. pose proof (artcells_poison m (rtrep_artcells st m HR)) as PCz.
    intros KX1 KX _ _ K1.
    apply lscps_assume. intros NWX HOK HBINV.
    (* [comment removed for export] *)
    assert (LZS : forall x : word, SH RB <= bv_unsigned x < SH (RB + 2^32) -> lzf mo x = true).
    { intros x Hx. (nelimp HM 8%nat; intros _ _ _ _ _ _ LZ _). apply LZ. right. unfold KHIGHSHADOW_BEG, KHIGHMEM_BEG, AIMG_HI, SH, SHADOW_OFFSET in *. clear -Hx G1 G3 G4 G5. Z.div_mod_to_equations. lia. }
    assert (HVIS : forall x : word, SH RB <= bv_unsigned x < SH (RB + 2^32) -> lzf mo x = true -> in_winb G x = true -> m x <> None).
    { intros x Hx L Wx. apply (HG x (or_introl Wx) L). right. left. unfold KHIGHSHADOW_BEG, KHIGHMEM_BEG, AIMG_HI, SH, SHADOW_OFFSET in *. clear -Hx G1 G3 G4 G5. Z.div_mod_to_equations. lia. }
    assert (SITE : forall mo' A sz, LOK asegs mo' -> RTMODEL st mo' -> RB <= A -> A + sz <= RB + 4294967296 -> A mod 4096 = 0 -> 0 < sz -> mmap_fixed_site mo' A sz).
    { intros mo' A sz HO' HM' A1 A2 A3 A4. apply (prim_fixed_site mo' A sz HO' ltac:(unfold KHIGHMEM_BEG, AIMG_HI, CEIL; clear -A1 A2 A3 A4 G1 G2 G3 G4 G5; lia) st HM'); unfold PRIM_RES_SIZE, CEIL; clear -A1 A2 A3 A4 G1 G2 G3 G4 G5; lia. }
    (* [comment removed for export] *)
    eapply lscps_evt_then.
    { eapply (refill_pre ra sp gp tp); [exact HR| exact WF| exact Hc| exact HC0| exact MI| exact ST| exact HCE| lia]. }
    cbv beta. intros ms1 nelH_; (nelim nelH_ 20%nat; intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 jR m1 -> MU1 WM1 MI1 ST1 FRR PCH1 PCO1).
    unfold refill_call.
    assert (HI1 : Forall outI (WPRE lo (bv_unsigned sp) P)) by (unfold WPRE, outI; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_LO, AIMG_HI; clear -HCEn EP TR TRa TRb TRi TRi; lia).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (DJI : forall a sz, AIMG_LO <= a -> a + sz <= AIMG_HI -> disjoint_from (WPRE lo (bv_unsigned sp) P) a sz) by (intros a sz Ha0 Ha; unfold WPRE, AIMG_LO, AIMG_HI in *; cbn; clear -Ha0 Ha HCEn EP TR TRa TRb TRi TRi; split; [| split; [| exact I]]; lia).   (* [comment removed for export] *)
    assert (DJR : forall a sz, Rc <= a -> a + sz <= Rc + 128 -> disjoint_from (WPRE lo (bv_unsigned sp) P) a sz).
    { intros a sz H1 H2. unfold WPRE. cbn. unfold hideP in RCT. clear -H1 H2 RCT HCEn EP G3 G4 G5 ERC Hc TR TRa TRb TRi. split; [djlr| split; [| exact I]]. destruct RCT; [right| left]; lia. }
    assert (DJT : forall a sz, t + 2768 <= a -> a + sz <= t + 4096 -> disjoint_from (WPRE lo (bv_unsigned sp) P) a sz)
      by (intros a sz H1 H2; unfold WPRE; cbn; clear -H1 H2 HCEn EP TR TRa TRb TRi; split; [djlr| split; [djlr| exact I]]).
    assert (DJFA : forall a sz, RB <= a -> a + sz <= RB + 4294967296 -> disjoint_from (WPRE lo (bv_unsigned sp) P) a sz).
    { intros a sz H1 H2. unfold WPRE. cbn. unfold hideP in RBT. clear -H1 H2 RBT HCEn EP G2 G3 G4 G5 TR TRa TRb TRi. split; [djlr| split; [| exact I]]. destruct RBT; [right| left]; lia. }
    pose proof AC32 as AC32a. eapply (ro_cells_transport asegs _ m m1) in AC32a; [| exact MU1| apply DJI; unfold AIMG_LO, AIMG_HI; cbn; clear; lia].
    pose proof AC40 as AC40a. eapply (ro_cells_transport asegs _ m m1) in AC40a; [| exact MU1| apply DJI; unfold AIMG_LO, AIMG_HI; cbn; clear; lia].
    pose proof AC48 as AC48a. eapply (ro_cells_transport asegs _ m m1) in AC48a; [| exact MU1| apply DJI; unfold AIMG_LO, AIMG_HI; cbn; clear; lia].
    pose proof AC56 as AC56a. eapply (ro_cells_transport asegs _ m m1) in AC56a; [| exact MU1| apply DJI; unfold AIMG_LO, AIMG_HI; cbn; clear; lia].
    pose proof RIa as RIa1. eapply (rw_cells_transport asegs _ m m1) in RIa1; [| exact MU1| exact WM1| apply DJR; cbn; clear; lia].
    pose proof RI24 as RI241. eapply (rw_cells_transport asegs _ m m1) in RI241; [| exact MU1| exact WM1| apply DJR; cbn; clear; lia].
    pose proof RIb as RIb1. eapply (rw_cells_transport asegs _ m m1) in RIb1; [| exact MU1| exact WM1| apply DJR; cbn; clear; lia].
    pose proof TST as TST1. eapply (rw_cells_transport asegs _ m m1) in TST1; [| exact MU1| exact WM1| apply DJT; cbn; clear; lia].
    pose proof SA as SA1. eapply (rw_cells_transport asegs _ m m1) in SA1; [| exact MU1| exact WM1| apply DJT; cbn; clear -ESTT EP; lia].
    pose proof VFA as VFA1. eapply (stk_transport_disjoint asegs _ m m1) in VFA1; [| exact MU1| exact WM1| apply DJFA; clear -EFA G9 G10 G8; lia].
    (* [comment removed for export] *)
    eapply lscps_evt_then.
    { eapply (gfa_A (wz 0x36d24) (wz (bv_unsigned sp + -32)) gp tp) with (lo := lo) (RIS := ris st) (S := S);
        [exact MI1| rewrite E32; exact ST1| exact HCE| rewrite E32; clear -LO2; lia| exact AC32a| exact AC48a| exact RIa1| exact ERC| unfold KHIGHMEM_BEG, AIMG_HI; clear -G1 G3; lia| idtac; clear -G4 G5; lia
        | unfold hideP in SR3; rewrite ERIS; rewrite Z.add_mod, SR3 by (clear; lia); reflexivity| exact Hc| unfold KHIGHMEM_BEG, AIMG_HI; clear -SR1 PR1; lia| idtac; clear -SR2 PR2; lia]. }
    cbv beta. intros ms2 nelH_; (nelim nelH_ 24%nat; intros y5 y6 y7 y10 y15 y16 y17 y21 y22 y24 y25 y28 y29 y30 y31 jG m2 -> MU2 WM2 MI2 ST2 FRG RIa2).
    rewrite E32 in MU2, ST2, FRG.
    replace (S + cls * 2 ^ 32 + KFREEARRAY_OFF) with FA by (unfold KFREEARRAY_OFF; rewrite EFA, ERB; clear; lia).
    change (pcaddr st cls + 16) with CH. change (acache st + 2560) with stt.
    assert (RC8 : hideP (Rc mod 8 = 0)).
    { unfold hideP in SR3 |- *. rewrite ERC, ERIS. clear -SR3. Z.div_mod_to_equations. lia. }
    assert (NF40 : nf < 2^40) by (clear -G9 G10; lia).
    pose proof (proj1 (rr_thread st m HR)) as VT0. assert (VT : stk asegs m t (t + 4096)) by exact VT0. clear VT0.
    destruct pop.
    2:{ (* [comment removed for export] *)
      assert (GE : n <= nf) by (symmetry in EPOP; apply Z.ltb_ge in EPOP; exact EPOP).
      cbn [andb] in EUM, EFM. subst um fm. clear KX1 KX HRR.
      eapply lscps_evt_then.
      { eapply gfa_have with (n := n) (nf := nf); [exact MI2| exact RIa2| unfold KHIGHMEM_BEG, AIMG_HI; clear -G1 G3 ERC Hc; lia| idtac; clear -G4 G5 ERC Hc; lia| exact NR| clear -GE NF40; lia]. }
      cbv beta. intros ms3 nelH_; (nelim nelH_ 6%nat; intros m3 -> MU3 WM3 MI3 RIa3).
      (* [comment removed for export] *)
      set (WH4 := [(lo, bv_unsigned sp + -32); (Rc, Rc + 24); (Rc + 72, Rc + 80); (CH, CH + 4 * n)]).
      assert (MU13 : munch WH4 m1 m3).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]]; subst WH4; subfpk ltac:(cut_to Cq). }
      pose proof (wmono_trans _ _ _ _ WM2 WM3) as WM13.
      assert (DJ4s : forall a sz, bv_unsigned sp + -32 <= a -> disjoint_from WH4 a sz).
      { intros a sz H1. subst WH4. clear -H1 HCEn LO2 G3 G4 G5 ERC EPC ECH EP TR TRa TRb TRi Hc NR. dj. }
      assert (DJ4r : forall a sz, Rc + 24 <= a -> a + sz <= Rc + 72 -> disjoint_from WH4 a sz).
      { intros a sz H1 H2. subst WH4. unfold hideP in RCT. clear -H1 H2 HCEn LO2 G3 G4 G5 ERC EPC ECH EP TR TRa TRb TRi Hc NR RCT.
        cbn. split; [djlr|]. split; [djlr|]. split; [djlr|]. split; [| exact I]. destruct RCT; [right| left]; lia. }
      assert (DJ4f : forall a sz, FA <= a -> a + sz <= FA + 536870912 -> disjoint_from WH4 a sz).
      { intros a sz H1 H2. subst WH4. unfold hideP in RBT. clear -H1 H2 HCEn LO2 G2 G3 G4 G5 ERC EFA EPC ECH EP TR TRa TRb TRi Hc NR RBT.
        cbn. split; [djlr|]. split; [djlr|]. split; [djlr|]. split; [| exact I]. destruct RBT; [right| left]; lia. }
      assert (DJ4p : forall c a sz, 0 <= c < 32 -> c <> cls -> P + 80 * c <= a -> a + sz <= P + 80 * c + 80 -> disjoint_from WH4 a sz).
      { intros c a sz Hc' NE H1 H2. subst WH4. unfold hideP in RCT. clear -Hc' NE H1 H2 HCEn LO2 G3 G4 G5 ERC EPC ECH EP TR TRa TRb TRi Hc NR RCT.
        cbn. split; [djlr|]. split; [destruct RCT; [left| right]; lia|]. split; [destruct RCT; [left| right]; lia|]. split; [| exact I].
        destruct (Z_lt_le_dec c cls); [left| right]; nia. }
      pose proof FRG as FRG3. eapply (rw_cells_transport asegs _ m2 m3) in FRG3; [| exact MU3| exact WM3| clear -HCEn LO2 G3 G4 G5 ERC Hc; dj].
      pose proof ST2 as ST3. eapply (stk_transport_disjoint asegs _ m2 m3) in ST3; [| exact MU3| exact WM3| clear -HCEn LO2 G3 G4 G5 ERC Hc; dj].
      pose proof RIb1 as RIb3. eapply (rw_cells_transport asegs _ m1 m2) in RIb3; [| exact MU2| exact WM2| clear -HCEn LO2 G3 G4 G5 ERC Hc; dj].
      eapply (rw_cells_transport asegs _ m2 m3) in RIb3; [| exact MU3| exact WM3| clear; dj].
      apply rinfo_split72 in RIb3.
      pose proof VT as VT3. eapply (stk_wmono_oclr m m3) in VT3; [| eapply wmono_trans; [exact WM1| exact WM13]| exact TRo| clear -TRc; pose proof ceil_lt64; lia].
      destruct (vis_carve m3 t (t + 4096) CH (Z.to_nat (4 * n)) VT3 ltac:(clear -EPC ECH EP Hc; lia) ltac:(clear -EPC ECH EP Hc NR; lia)) as [junk JK].
      destruct (p_u32arr_of_u8arr asegs m3 CH junk (Z.to_nat n) (u8arr_of_rw_cells asegs _ _ _ _ JK)) as (dpre & LD & DST). (* [comment removed for export] *)
      { destruct JK as [[WFj _] _]. cbn in WFj. clear -WFj NR. lia. }
      assert (EN3 : forall i, nf - n <= i < nf - n + Z.of_nat (Z.to_nat n) -> rw_cells asegs m3 (FA + 4 * i) [W4 (nthz (r_fa r) i 0)]).
      { intros i Hi. pose proof (EN i ltac:(clear -Hi GE NR; lia)) as E0.
        eapply (rw_cells_transport asegs _ m m1) in E0; [| exact MU1| exact WM1| apply DJFA; cbn; clear -Hi GE NR EFA G9 G10; lia].
        eapply (rw_cells_transport asegs _ m1 m3); [exact E0| exact MU13| exact WM13| apply DJ4f; cbn; clear -Hi GE NR G9 G10; lia]. }
      pose proof (u32arr_of_cells (Z.to_nat n) m3 FA (nf - n) (fun i => nthz (r_fa r) i 0) ltac:(clear -G1 EFA; lia) ltac:(clear -G3 G4 G5 EFA G9 G10 NR GE; lia) ltac:(clear -GE; lia) EN3) as FAU. cbv beta in FAU.
      set (fa := map (fun j => nthz (r_fa r) (nf - n + Z.of_nat j) 0) (seq 0 (Z.to_nat n))).
      assert (EWL : wl fa = map (fun j : nat => wz (nthz (r_fa r) (nf - n + Z.of_nat j) 0)) (seq 0 (Z.to_nat n))) by (subst fa; unfold wl; rewrite map_map; reflexivity).
      rewrite <- EWL in FAU.
      assert (FAS : Forall (fun z => 0 <= z < 2^31) fa).
      { subst fa. apply Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
        pose proof (fa_entry_small st cls (nf - n + Z.of_nat j) WF Hc ltac:(clear -Hj GE NR G8; unfold nf; lia)). clear -H. unfold r. lia. }
      eapply lscps_evt_then.
      { eapply gfa_tail with (lo := lo) (fa := fa) (dpre := dpre);
          [exact MI3| rewrite E32; exact ST3| exact HCE| rewrite E32; clear -LO2; lia| rewrite E32; exact FRG3| exact RIa3| exact RIb3
          | unfold KHIGHMEM_BEG, AIMG_HI; clear -G1 G3 ERC Hc; lia| idtac; clear -G4 G5 ERC Hc; lia| exact RC8
          | unfold KHIGHMEM_BEG, AIMG_HI; clear -G1 EFA; lia| clear -G3 ERC EFA Hc; lia| unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; clear -TR TRa TRi EPC ECH EP Hc NR; lia| idtac; clear -TR TRa TRb TRi EPC ECH EP Hc NR; lia
          | unfold hideP in RCT; clear -RCT EPC ECH EP Hc NR; destruct RCT; [left| right]; lia
          | unfold hideP in RBT; clear -RBT EPC ECH EP EFA Hc NR; destruct RBT; [left| right]; lia
          | exact NR| clear -GE; lia| clear -G9 G10 GE NR; lia
          | subst fa; rewrite length_map, length_seq; reflexivity| exact FAS| exact LD| exact FAU| exact DST]. }
      cbv beta. intros ms4 nelH_; (nelim nelH_ 25%nat; intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m4 sna' -> MU4 WM4 MI4 ST4 RIa4 RIb4 FAU4 CHU4).
      rewrite E32 in MU4, ST4.
      cbv beta delta [wz]. replace (ret_pc (Z_to_bv 64 224548)) with (Z_to_bv 64 224548 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      apply rinfo_join72 in RIb4.
      assert (MU14 : munch WH4 m1 m4) by (eapply munch_trans; [exact MU13| eapply munch_weaken; [| exact MU4]; subst WH4; subfpk ltac:(cut_to Cq)]).
      pose proof (wmono_trans _ _ _ _ WM13 WM4) as WM14.
      pose proof FRR as FRR4. eapply (rw_cells_transport asegs _ m1 m4) in FRR4; [| exact MU14| exact WM14| apply DJ4s; clear; lia].
      pose proof (PCH1 cls Hcls) as PCC. rewrite (proj2 (Z.eqb_neq cls 0)) in PCC by (clear -Hc; lia). rewrite HC0 in PCC. change (zlen (@nil Z)) with 0 in PCC.
      eapply (rw_cells_transport asegs _ m1 m4) in PCC; [| exact MU14| exact WM14| subst WH4; unfold hideP in RCT; clear -RCT HCEn LO2 G3 G4 G5 ERC EPC ECH EP TR TRa TRb TRi Hc NR].
      2:{ cbn. split; [djlr|]. split; [destruct RCT; [left| right]; lia|]. split; [destruct RCT; [left| right]; lia|]. split; [djlr| exact I]. }
      change (pcaddr st cls) with pc in PCC.
      eapply lscps_evt_then.
      { eapply (refill_ret sp gp tp) with (lo := lo) (r := 1); [exact MI4| exact ST4| exact HCE| clear -LO2; lia| exact FRR4| exact PCC
          | unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; clear -TR TRa TRi EPC EP Hc; lia| idtac; clear -TR TRa TRb TRi EPC EP Hc; lia| clear -NR; lia| clear; lia]. }
      cbv beta. intros ms5 nelH_; (nelim nelH_ 21%nat; intros w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m5 -> MU5 WM5 MI5 ST5 PCC5).
      cbn [Z.eqb Pos.eqb] in PCC5.
      (* [comment removed for export] *)
      assert (MUT : munch (WTOT lo (bv_unsigned sp) P pc t Rc (RB + mapped) usz FA nf) m m5).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_trans; [eapply munch_weaken; [| exact MU14]| eapply munch_weaken; [| exact MU5]]];
          unfold WTOT, WPRE, WREST; subst WH4; clear -HCEn LO2 ECH NR; subfp. }
      assert (MU15 : munch (WH4 ++ [(lo, bv_unsigned sp); (pc, pc + 4)]) m1 m5).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU14]| eapply munch_weaken; [| exact MU5]]; subst WH4; clear; subfp. }
      pose proof (wmono_trans _ _ _ _ WM14 WM5) as WM15.
      specialize (K1 ltac:(discriminate) w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m5 (le8 sna' ++ skipn 8 js) fa MI5 MUT
                     (wmono_trans _ _ _ _ WM1 WM15) ST5).
      rewrite !Z.sub_0_r in K1. apply K1; clear K1.
      - eapply (rw_cells_transport asegs _ m4 m5); [| exact MU5| exact WM5| clear -HCEn LO2 G3 G4 G5 ERC EPC EP TR TRa TRb TRi Hc RCT].
        + replace (nf + 0 - n) with (nf - n) by (clear; lia). exact RIa4.
        + unfold hideP in RCT. cbn. split; [djlr|]. split; [destruct RCT; [right| left]; lia| exact I].
      - eapply (rw_cells_transport asegs _ m1 m5); [exact RI241| exact MU15| exact WM15| subst WH4; unfold hideP in RCT; clear -RCT HCEn LO2 G3 G4 G5 ERC EPC ECH EP TR TRa TRb TRi Hc NR].
        cbn. split; [djlr|]. split; [djlr|]. split; [djlr|]. split; [destruct RCT; [right| left]; lia|]. split; [djlr|]. split; [destruct RCT; [right| left]; lia| exact I].
      - rewrite Z.mul_0_l, !Z.add_0_r. eapply (rw_cells_transport asegs _ m4 m5); [exact RIb4| exact MU5| exact WM5| clear -HCEn LO2 G3 G4 G5 ERC EPC EP TR TRa TRb TRi Hc RCT].
        unfold hideP in RCT. cbn. split; [djlr|]. split; [destruct RCT; [right| left]; lia| exact I].
      - eapply (stk_transport_disjoint asegs _ m1 m5); [exact VFA1| exact MU15| exact WM15| subst WH4; unfold hideP in RBT; clear -RBT HCEn LO2 G2 G3 G4 G5 ERC EFA EPC ECH EP TR TRa TRb TRi Hc NR G9 G10 FA0].
        cbn. split; [djlr|]. split; [djlr|]. split; [djlr|]. split; [destruct RBT; [right| left]; lia|]. split; [djlr|]. split; [destruct RBT; [right| left]; lia| exact I].
      - cbn [Z.to_nat fill_vals seq map rev]. apply u32arr_nil; clear -G1 EFA G3 G4 G5 G8 G9 G10; lia.
      - exact I.
      - exact I.
      - subst fa. rewrite length_map, length_seq. reflexivity.
      - intros i Hi. cbn [newc Z.to_nat seq map]. rewrite app_nil_r. subst fa. rewrite nthz_map_seq by (clear -Hi NR; lia). f_equal. clear -Hi NR. lia.
      - eapply (u32arr_transport asegs _ m4 m5); [exact CHU4| exact MU5| exact WM5|].
        subst fa. unfold wl. rewrite !length_map, length_seq. clear -HCEn LO2 EPC ECH EP TR TRa TRb TRi Hc NR. dj.
      - intros c Hc'. destruct (Z.eqb_spec c cls) as [->|NE].
        + rewrite (proj2 (Z.eqb_neq cls 0)) by (clear -Hc; lia). exact PCC5.
        + pose proof (PCH1 c Hc') as X. eapply (rw_cells_transport asegs _ m1 m5); [exact X| exact MU15| exact WM15|].
          unfold KNUMCLASSES in Hc'. cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. change (pcaddr st c) with (P + 80 * c).
          rewrite <- (app_nil_r [(lo, bv_unsigned sp); (pc, pc + 4)]) || idtac.
          subst WH4. unfold hideP in RCT. clear -RCT HCEn LO2 G3 G4 G5 ERC EPC ECH EP TR TRa TRb TRi Hc NR Hc' NE.
          cbn. split; [djlr|]. split; [destruct RCT; [left| right]; lia|]. split; [destruct RCT; [left| right]; lia|].
          split; [destruct (Z_lt_le_dec c cls); [left| right]; nia|]. split; [djlr|]. split; [destruct (Z_lt_le_dec c cls); [left| right]; nia| exact I].
      - intros c i Hc' Hi. destruct (Z.eq_dec c cls) as [->|NE]; [rewrite HC0 in Hi; change (zlen (@nil Z)) with 0 in Hi; exfalso; clear -Hi; lia|].
        pose proof (PCO1 c i Hc' Hi) as X. pose proof (wc_cache_max st c (wf_class_ok st WF c Hc')) as CM. pose proof (cmaxcount_le16 c) as CM16.
        eapply (rw_cells_transport asegs _ m1 m5); [exact X| exact MU15| exact WM15|].
        unfold KNUMCLASSES in Hc'. cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. change (pcaddr st c) with (P + 80 * c).
        subst WH4. unfold hideP in RCT. clear -RCT HCEn LO2 G3 G4 G5 ERC EPC ECH EP TR TRa TRb TRi Hc NR Hc' NE Hi CM CM16.
        cbn. split; [djlr|]. split; [destruct RCT; [left| right]; lia|]. split; [destruct RCT; [left| right]; lia|].
        split; [destruct (Z_lt_le_dec c cls); [left| right]; nia|]. split; [djlr|]. split; [destruct (Z_lt_le_dec c cls); [left| right]; nia| exact I]. }
    (* [comment removed for export] *)
    assert (LT : nf < n) by (symmetry in EPOP; apply Z.ltb_lt in EPOP; exact EPOP).
    cbn [andb] in EUM, EFM.
    (* [comment removed for export] *)
    assert (TAIL0 : forall (J : machine_state -> Prop) (m' : word -> option byte) (v5 v6 v7 v11 v12 v13 v14 v15 v16 v17 v18 v20 v21 v22 v24 v25 v26 v27 v28 v29 v30 v31 : word),
      (forall (Qx : machine_state -> Prop) ms, evt asegs Qx ms -> (forall ms', Qx ms' -> J ms') -> J ms) ->
      mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp + -32 + -128) ->
      rw_cells asegs m' (bv_unsigned sp + -32 + -128) (gfa_frame jG s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 (wz n) (wz pc) (wz 0x36d24)) ->
      rw_cells asegs m' (bv_unsigned sp + -32) (refill_frame jR s1 s0 ra) ->
      rw_cells asegs m' Rc [C8 (wz MTX_LOCKED); C8 (wz 0); C8 (Z_to_bv 64 nf)] ->
      rw_cells asegs m' pc [W4 0; W4 (cmaxcount cls); W8 (csize cls)] ->
      (forall (m'' : word -> option byte) (w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 : word),
         mem_inv asegs m'' -> munch [(lo, bv_unsigned sp); (Rc, Rc + 8); (pc, pc + 4)] m' m'' -> wmono asegs m' m'' -> stk asegs m'' lo (bv_unsigned sp) ->
         rw_cells asegs m'' Rc [C8 (wz 0); C8 (wz 0); C8 (Z_to_bv 64 nf)] -> rw_cells asegs m'' pc [W4 0; W4 (cmaxcount cls); W8 (csize cls)] ->
         J (RET 0 w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m'')) ->
      J (MS (mkR (wz 0x370a0) (wz (bv_unsigned (wz (bv_unsigned sp + -32)) + -128)) gp tp v5 v6 v7 (wz Rc) (wz A_ALLOC) (wz 0) v11 v12 v13 v14 v15 v16 v17
                  v18 (wz 2305843009213693952) v20 v21 v22 (wz MTX_LOCKED) v24 v25 v26 v27 v28 v29 v30 v31)
             F (ret_pc (wz 0x370a0)) fc None m' (seg_rom asegs))).
    { clear KX1 KX K1 HRR EUM EFM.
      intros J m' v5 v6 v7 v11 v12 v13 v14 v15 v16 v17 v18 v20 v21 v22 v24 v25 v26 v27 v28 v29 v30 v31 JE MI' ST' FRG' FRR' RIa' PCC' KJ.
      cbv beta delta [wz]. replace (ret_pc (Z_to_bv 64 225440)) with (Z_to_bv 64 225440 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      eapply JE.
      { eapply (gfa_fail (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp) with (lo := lo);
          [exact MI'| unfold wz in E32; rewrite E32; exact ST'| exact HCE| unfold wz in E32; rewrite E32; clear -LO2; lia| unfold wz in E32; rewrite E32; exact FRG'| exact RIa'
          | unfold KHIGHMEM_BEG, AIMG_HI; clear -G1 G3 ERC Hc; lia| idtac; clear -G4 G5 ERC Hc; lia| exact RC8]. }
      cbv beta. intros ms4 nelH_; (nelim nelH_ 21%nat; intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m4 -> MU4 WM4 MI4 ST4 RIa4).
      unfold wz in E32. rewrite E32 in MU4, ST4. cbv beta delta [wz].
      replace (ret_pc (Z_to_bv 64 224548)) with (Z_to_bv 64 224548 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof FRR' as FRR4. eapply (rw_cells_transport asegs _ m' m4) in FRR4; [| exact MU4| exact WM4| clear -HCEn LO2 G3 G4 G5 ERC Hc; dj].
      pose proof PCC' as PCC4. eapply (rw_cells_transport asegs _ m' m4) in PCC4; [| exact MU4| exact WM4| unfold hideP in RCT; clear -RCT HCEn LO2 G3 G4 G5 ERC EPC EP TR TRa TRb TRi Hc].
      2:{ cbn. split; [djlr|]. split; [destruct RCT; [left| right]; lia| exact I]. }
      eapply JE.
      { eapply (refill_ret sp gp tp) with (lo := lo) (r := 0); [exact MI4| exact ST4| exact HCE| clear -LO2; lia| exact FRR4| exact PCC4
          | unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; clear -TR TRa TRi EPC EP Hc; lia| idtac; clear -TR TRa TRb TRi EPC EP Hc; lia| clear -NR; lia| clear; lia]. }
      cbv beta. intros ms5 nelH_; (nelim nelH_ 21%nat; intros w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m5 -> MU5 WM5 MI5 ST5 PCC5).
      cbn [Z.eqb] in PCC5.
      apply KJ; [exact MI5| | eapply wmono_trans; [exact WM4| exact WM5]| exact ST5| | exact PCC5].
      - eapply munch_trans; [eapply munch_weaken; [| exact MU4]| eapply munch_weaken; [| exact MU5]]; clear; subfp.
      - eapply (rw_cells_transport asegs _ m4 m5); [exact RIa4| exact MU5| exact WM5| unfold hideP in RCT; clear -RCT HCEn LO2 G3 G4 G5 ERC EPC EP TR TRa TRb TRi Hc].
        cbn. split; [djlr|]. split; [destruct RCT; [right| left]; lia| exact I]. }
    (* [comment removed for export] *)
    eapply lscps_evt_then.
    { eapply gfa_need with (n := n) (nf := nf); [exact MI2| exact RIa2| unfold KHIGHMEM_BEG, AIMG_HI; clear -G1 G3 ERC Hc; lia| idtac; clear -G4 G5 ERC Hc; lia| exact NR| clear -LT G8; lia]. }
    cbv beta. intros ms3 ->.
    (* [comment removed for export] *)
    assert (HI2 : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(lo, bv_unsigned sp + -32); (Rc, Rc + 8)]) by (repeat constructor; cbn [fst]; unfold AIMG_HI; clear -HCEn G1 G3 ERC Hc; lia).
    assert (HC2 : mmap_consts m2) by (eapply mmap_consts_high; [exact MU2| exact HI2| eapply mmap_consts_out; [exact MU1| exact HI1| exact HC]]).
    assert (IC2 : icpt_cells m2) by (eapply icpt_cells_high'; [exact MU2| exact HI2| eapply icpt_cells_out; [exact MU1| exact HI1| exact IC]]).
    assert (PC2 : poison_cells m2) by (eapply poison_cells_high'; [exact MU2| exact HI2| eapply poison_cells_out; [exact MU1| exact HI1| exact PCz]]).
    pose proof (wb_ctx_t st (wf_base_ok st WF)) as CT0. assert (CT : st_ctx st + 160 <= t \/ t + 4096 <= st_ctx st) by exact CT0. clear CT0.
    assert (LC2 : leafc st m2).
    { assert (LC1 : leafc st m1).
      { eapply (leafc_munch st _ _ _ MU1 WM1); [| exact LC]. intros lo' hi' a b Hin Hab. unfold WPRE in Hin. cbn in Hin, Hab.
        unfold hideP in CDJ. clear -Hin Hab HCEn LO2 EP TR TRa TRb TRi CR CRa CRb CRi CT CDJ.
        destruct Hin as [E|[E|[]]]; injection E; intros; subst;
        (destruct Hab as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[]]]]]]]]]]; injection E'; intros; subst; (cut_on [HCEn CR TRi EP CT] blia)). }
      eapply (leafc_munch st _ _ _ MU2 WM2); [| exact LC1]. intros lo' hi' a b Hin Hab. cbn in Hin, Hab.
      unfold hideP in RCC. clear -Hin Hab HCEn LO2 TR TRa TRb TRi CR CRa CRb CRi RCC G1 G3 ERC Hc.
      destruct Hin as [E|[E|[]]]; injection E; intros; subst;
      (destruct Hab as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[]]]]]]]]]]; injection E'; intros; subst; lia). }
    pose proof AC32a as AC32b. eapply (ro_cells_transport asegs _ m1 m2) in AC32b; [| exact MU2| clear -HCEn G1 G3 ERC Hc; dj].
    pose proof AC40a as AC40b. eapply (ro_cells_transport asegs _ m1 m2) in AC40b; [| exact MU2| clear -HCEn G1 G3 ERC Hc; dj].
    pose proof AC56a as AC56b. eapply (ro_cells_transport asegs _ m1 m2) in AC56b; [| exact MU2| clear -HCEn G1 G3 ERC Hc; dj].
    pose proof RI241 as RI242. eapply (rw_cells_transport asegs _ m1 m2) in RI242; [| exact MU2| exact WM2| clear -HCEn G3 G4 G5 ERC Hc; dj].
    pose proof RIb1 as RIb2. eapply (rw_cells_transport asegs _ m1 m2) in RIb2; [| exact MU2| exact WM2| clear -HCEn G3 G4 G5 ERC Hc; dj].
    pose proof TST1 as TST2. eapply (rw_cells_transport asegs _ m1 m2) in TST2; [| exact MU2| exact WM2| unfold hideP in RCT; clear -RCT HCEn LO2 TR TRa TRb TRi G3 G4 G5 ERC Hc].
    2:{ cbn. split; [djlr|]. split; [destruct RCT; [left| right]; lia| exact I]. }
    pose proof SA1 as SA2. eapply (rw_cells_transport asegs _ m1 m2) in SA2; [| exact MU2| exact WM2| unfold hideP in RCT; clear -RCT HCEn LO2 TR TRa TRb TRi G3 G4 G5 ERC Hc EP ESTT].
    2:{ cbn. split; [djlr|]. split; [destruct RCT; [left| right]; lia| exact I]. }
    pose proof VFA1 as VFA2. eapply (stk_transport_disjoint asegs _ m1 m2) in VFA2; [| exact MU2| exact WM2| clear -HCEn G3 G4 G5 ERC EFA G9 G10 G8 Hc; dj].
    pose proof FRR as FRR2. eapply (rw_cells_transport asegs _ m1 m2) in FRR2; [| exact MU2| exact WM2| clear -HCEn LO2 G3 G4 G5 ERC Hc; dj].
    pose proof (PCH1 cls Hcls) as PCC1. rewrite (proj2 (Z.eqb_neq cls 0)) in PCC1 by (clear -Hc; lia). rewrite HC0 in PCC1. change (zlen (@nil Z)) with 0 in PCC1. change (pcaddr st cls) with pc in PCC1.
    pose proof PCC1 as PCC2. eapply (rw_cells_transport asegs _ m1 m2) in PCC2; [| exact MU2| exact WM2| unfold hideP in RCT; clear -RCT HCEn LO2 TR TRa TRb TRi G3 G4 G5 ERC Hc EP EPC].
    2:{ cbn. split; [djlr|]. split; [destruct RCT; [left| right]; lia| exact I]. }
    assert (RBU : hideP (RB mod 65536 = 0)).
    { unfold hideP in SAL |- *. rewrite ERB. clear -SAL. rewrite Z.add_mod, SAL by lia. replace 4294967296 with (65536 * 65536) by reflexivity.
      rewrite Z.mul_assoc, Z_mod_mult. reflexivity. }
    assert (SHB : hideP (2147450880 <= SH (RB + mapped) /\ SH (RB + mapped) + 32768 <= 17594333495296)).
    { unfold hideP, SH, SHADOW_OFFSET. clear -G1 G3 G4 G5 G6 G7. Z.div_mod_to_equations. lia. }
    assert (SHF : hideP (2147450880 <= SH FA /\ SH FA + 67108864 <= 17594333495296)).
    { unfold hideP, SH, SHADOW_OFFSET. clear -G1 G3 G4 G5 EFA. Z.div_mod_to_equations. lia. }
    assert (Hq : 0 <= n - nf <= 8 /\ csize cls * (n - nf) <= 262144) by (clear -LT NR G8 SL1 CP CL; nia).
    assert (HVIS2 : forall x : word, SH RB <= bv_unsigned x < SH (RB + 2^32) -> lzf mo x = true -> in_winb G x = true -> m2 x <> None).
    { intros x Hx L Wx. apply (GWIN_mem st m m2 mo (mkG G R) HG HOK (wmono_trans _ _ _ _ WM1 WM2) x (or_introl Wx) L). right. left.
      unfold KHIGHSHADOW_BEG, KHIGHMEM_BEG, AIMG_HI, SH, SHADOW_OFFSET in *. clear -Hx G1 G3 G4 G5. Z.div_mod_to_equations. lia. }
    replace (S + cls * 2 ^ 32 + KFREEARRAY_OFF) with FA by (unfold KFREEARRAY_OFF; rewrite EFA, ERB; clear; lia).
    eapply (populate_spec poison_shadow_ok) with (st := st) (c := cls) (q := n - nf) (alloc := alloc) (mapped := mapped) (nf := nf) (fam := fam) (lo := lo)
                                    (tj1 := tj1) (tj2 := tj2) (sa := sa) (jr := jr) (je := je) (js := js) (exhb := exhb) (um := um) (fm := fm) (spin := spin);
      [ exact HC2| exact IC2| exact PC2| exact LC2| exact WF| exact TP| exact MI2
      | rewrite E32, E160; exact ST2
      | rewrite E32, E160; unfold POP_STACK; split; [exact HCE| clear -LO2; lia]
      | exact AC32b| exact AC40b| exact AC56b| exact RIa2| exact RI242| exact RIb2| exact TST2| exact SA2
      | rewrite ESTT, EP; unfold t; clear; lia
      | change (2 ^ 32) with 4294967296; rewrite <- ERB; unfold KFREEARRAY_OFF; rewrite <- EFA; exact VFA2
      | change (2 ^ 32) with 4294967296; rewrite <- ERB; unfold hideP in RCT, RCC; unfold KHIGHMEM_BEG, AIMG_HI; split; [clear -G1 G3 ERC Hc; lia| split; [idtac; clear -G4 G5 ERC Hc; lia| split; [exact RCC| split; [exact RCT| clear -G3 ERC Hc; lia]]]]
      | unfold hideP in SAL; unfold KHIGHMEM_BEG, AIMG_HI; split; [clear -SR1 PR1; lia| split; [idtac; clear -SR2 PR2; lia| exact SAL]]
      | change (2 ^ 32) with 4294967296; rewrite <- ERB; unfold hideP in RBT, RBC; exact (conj RBC RBT)
      | exact Hc| exact Hq
      | unfold hideP in MA; unfold KFREEARRAY_OFF; clear -G6 G7 MA RES; repeat split; lia
      | clear -G8 LT NR G9; lia
      | unfold hideP in FAL; clear -FA0 FAL G10; repeat split; lia
      | change (2 ^ 32) with 4294967296; rewrite <- ERB; exact LZS
      | change (2 ^ 32) with 4294967296; rewrite <- ERB; exact HVIS2
      | change (2 ^ 32) with 4294967296; rewrite <- ERB; apply (SITE mo (RB + mapped) 262144 HOK HM); [clear -G6; lia| clear -G7; lia| unfold hideP in RBU, MA; clear -RBU MA; Z.div_mod_to_equations; lia| clear; lia]
      | change (2 ^ 32) with 4294967296; unfold KFREEARRAY_OFF; rewrite <- ERB, <- EFA; intros mo1 HF [->| ->];
          [ apply (SITE mo (FA + fam) 262144 HOK HM); [clear -EFA FA0; lia| clear -EFA HF; lia| unfold hideP in RBU, FAL; clear -RBU FAL EFA; Z.div_mod_to_equations; lia| clear; lia]
          | apply (SITE _ (FA + fam) 262144 (mm_commit_LOK asegs _ _ _ HOK));
            [ apply (RTMODEL_commit mo (RB + mapped) 262144 HOK ltac:(unfold KHIGHMEM_BEG, AIMG_HI, CEIL; clear -G1 G6 G7 G3 G4 G5; lia) st HM)
            | clear -EFA FA0; lia| clear -EFA HF; lia| unfold hideP in RBU, FAL; clear -RBU FAL EFA; Z.div_mod_to_equations; lia| clear; lia] ]
      | exact EUM| exact EFM| exact HRR
      | | | | | ].
    - (* [comment removed for export] *)
      intros Eexh Eum EXH u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 m3 MI3 MU3 WM3 ST3. rewrite E32, E160 in MU3, ST3.
      pose proof FRG as FRG3. eapply (rw_cells_transport asegs _ m2 m3) in FRG3; [| exact MU3| exact WM3| clear; dj].
      pose proof FRR2 as FRR3. eapply (rw_cells_transport asegs _ m2 m3) in FRR3; [| exact MU3| exact WM3| clear; dj].
      pose proof RIa2 as RIa3. eapply (rw_cells_transport asegs _ m2 m3) in RIa3; [| exact MU3| exact WM3| clear -HCEn LO2 G3 G4 G5 ERC Hc; dj].
      pose proof PCC2 as PCC3. eapply (rw_cells_transport asegs _ m2 m3) in PCC3; [| exact MU3| exact WM3| clear -HCEn LO2 TR TRa TRb TRi EPC EP Hc; dj].
      apply (TAIL0 (fun ms => LSCPS asegs Q ms mo (mkG G R)) m3); [intros Qx ms EV K; eapply lscps_evt_then; [exact EV| exact K]| exact MI3| exact ST3| exact FRG3| exact FRR3| exact RIa3| exact PCC3|].
      intros m5 w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 MI5 MU5 WM5 ST5 RIa5 PCC5.
      assert (MU25 : munch [(lo, bv_unsigned sp); (Rc, Rc + 8); (pc, pc + 4)] m2 m5).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU3]| exact MU5]. clear -LO2; subfp. }
      pose proof (wmono_trans _ _ _ _ WM3 WM5) as WM25.
      assert (MU15 : munch [(lo, bv_unsigned sp); (Rc, Rc + 8); (pc, pc + 4)] m1 m5).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU2]| exact MU25]. clear -LO2; subfp. }
      pose proof (wmono_trans _ _ _ _ WM2 WM25) as WM15.
      rewrite Eexh in RIb2, KX1.
      apply (KX1 eq_refl Eum eq_refl EXH); clear KX1 KX K1.
      + exact MI5.
      + eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU15]]; unfold WTOT, WPRE, WREST; clear; subfp.
      + eapply wmono_trans; [exact WM1| exact WM15].
      + exact ST5.
      + exact RIa5.
      + eapply (rw_cells_transport asegs _ m2 m5); [exact RI242| exact MU25| exact WM25| unfold hideP in RCT; clear -RCT HCEn LO2 G3 G4 G5 ERC EPC EP TR TRa TRb TRi Hc].
        cbn. split; [djlr|]. split; [djlr|]. split; [destruct RCT; [right| left]; lia| exact I].
      + eapply (rw_cells_transport asegs _ m2 m5); [exact RIb2| exact MU25| exact WM25| unfold hideP in RCT; clear -RCT HCEn LO2 G3 G4 G5 ERC EPC EP TR TRa TRb TRi Hc].
        cbn. split; [djlr|]. split; [djlr|]. split; [destruct RCT; [right| left]; lia| exact I].
      + intros c Hc'. destruct (Z.eqb_spec c cls) as [->|NE]; [rewrite (proj2 (Z.eqb_neq cls 0)) by (clear -Hc; lia); exact PCC5|].
        pose proof (PCH1 c Hc') as X. eapply (rw_cells_transport asegs _ m1 m5); [exact X| exact MU15| exact WM15|].
        unfold KNUMCLASSES in Hc'. cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. change (pcaddr st c) with (P + 80 * c).
        unfold hideP in RCT. clear -RCT HCEn LO2 G3 G4 G5 ERC EPC EP TR TRa TRb TRi Hc Hc' NE.
        cbn. split; [djlr|]. split; [destruct RCT; [left| right]; lia|]. split; [destruct (Z_lt_le_dec c cls); [left| right]; nia| exact I].
      + intros c i Hc' Hi. destruct (Z.eq_dec c cls) as [->|NE]; [rewrite HC0 in Hi; change (zlen (@nil Z)) with 0 in Hi; exfalso; clear -Hi; lia|].
        pose proof (PCO1 c i Hc' Hi) as X. pose proof (wc_cache_max st c (wf_class_ok st WF c Hc')) as CM. pose proof (cmaxcount_le16 c) as CM16.
        eapply (rw_cells_transport asegs _ m1 m5); [exact X| exact MU15| exact WM15|].
        unfold KNUMCLASSES in Hc'. cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. change (pcaddr st c) with (P + 80 * c).
        unfold hideP in RCT. clear -RCT HCEn LO2 G3 G4 G5 ERC EPC EP TR TRa TRb TRi Hc Hc' NE Hi CM CM16.
        cbn. split; [djlr|]. split; [destruct RCT; [left| right]; lia|]. split; [destruct (Z_lt_le_dec c cls); [left| right]; nia| exact I].
    - (* [comment removed for export] *)
      intros Eexh Eum EXH u5 u6 u7 u15 u16 u17 u28 u29 u30 u31 m3 MI3 MU3 WM3 ST3 FRP RIa3 RI243 RIb3 TST3 SA3. rewrite E32, E160 in MU3, ST3, FRP |- *.
      pose proof FRG as FRG3. eapply (rw_cells_transport asegs _ m2 m3) in FRG3; [| exact MU3| exact WM3| clear; dj].
      pose proof FRR2 as FRR3. eapply (rw_cells_transport asegs _ m2 m3) in FRR3; [| exact MU3| exact WM3| clear; dj].
      assert (MU13 : munch [(lo, bv_unsigned sp); (Rc, Rc + 8)] m1 m3).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]]; clear -LO2; subfp. }
      pose proof (wmono_trans _ _ _ _ WM2 WM3) as WM13.
      rewrite Eexh in KX.
      apply (KX eq_refl Eum eq_refl EXH u5 u6 u7 u15 u16 u17 y10 y24 y25 u28 u29 u30 u31 m3 jR jG tj1 tj2 sa); clear KX1 KX K1.
      + exact MI3.
      + eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU13]]; unfold WTOT, WPRE, WREST; clear; subfp.
      + eapply wmono_trans; [exact WM1| exact WM13].
      + exact ST3.
      + exact FRR3.
      + exact FRG3.
      + exact FRP.
      + exact RIa3.
      + exact RI243.
      + exact RIb3.
      + exact TST3.
      + exact SA3.
      + intros c Hc'. destruct (Z.eqb_spec c cls) as [->|NE].
        * rewrite (proj2 (Z.eqb_neq cls 0)) by (clear -Hc; lia). eapply (rw_cells_transport asegs _ m2 m3); [exact PCC2| exact MU3| exact WM3| clear -HCEn LO2 TR TRa TRb TRi EPC EP Hc; dj].
        * pose proof (PCH1 c Hc') as X. eapply (rw_cells_transport asegs _ m1 m3); [exact X| exact MU13| exact WM13|].
          unfold KNUMCLASSES in Hc'. cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. change (pcaddr st c) with (P + 80 * c).
          unfold hideP in RCT. clear -RCT HCEn LO2 G3 G4 G5 ERC EPC EP TR TRa TRb TRi Hc Hc' NE.
          cbn. split; [djlr|]. split; [destruct RCT; [left| right]; lia| exact I].
      + intros c i Hc' Hi. destruct (Z.eq_dec c cls) as [->|NE]; [rewrite HC0 in Hi; change (zlen (@nil Z)) with 0 in Hi; exfalso; clear -Hi; lia|].
        pose proof (PCO1 c i Hc' Hi) as X. pose proof (wc_cache_max st c (wf_class_ok st WF c Hc')) as CM. pose proof (cmaxcount_le16 c) as CM16.
        eapply (rw_cells_transport asegs _ m1 m3); [exact X| exact MU13| exact WM13|].
        unfold KNUMCLASSES in Hc'. cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. change (pcaddr st c) with (P + 80 * c).
        unfold hideP in RCT. clear -RCT HCEn LO2 G3 G4 G5 ERC EPC EP TR TRa TRb TRi Hc Hc' NE Hi CM CM16.
        cbn. split; [djlr|]. split; [destruct RCT; [left| right]; lia| exact I].
    - (* [comment removed for export] *) exact I.
    - (* [comment removed for export] *) exact I.
    - (* [comment removed for export] *)
      intros NEX u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 m3 tj1' tj2' sa' MI3 MU3 WM3 ST3 RIa3 RI243 RIb3 TST3 SA3 VFA3 FILL3 VU3 VF3.
      rewrite E32, E160 in MU3, ST3.
      change (2 ^ 32) with 4294967296 in MU3, VFA3, FILL3, VU3, VF3 |- *. unfold KFREEARRAY_OFF in MU3, VFA3, FILL3, VF3 |- *.
      rewrite <- ERB in MU3, VFA3, FILL3, VU3, VF3 |- *. rewrite <- EFA in MU3, VFA3, FILL3, VF3 |- *.
      set (Nv := (mapped + (if um then 262144 else 0) - alloc) / csize cls) in *.
      set (fam' := if fm then (4 * (nf + Nv) + 262143) / 262144 * 262144 else fam) in *.
      set (L := r_fa r ++ newc cls (ncarved st cls) Nv) in *.
      assert (NVB : 0 <= Nv <= 16385 /\ Nv * csize cls <= mapped + (if um then 262144 else 0) - alloc).
      { subst Nv. set (mp := mapped + (if um then 262144 else 0)) in *.
        assert (Hmp : alloc <= mp <= alloc + csize cls + 524288) by (subst mp; clear -G6 RES; destruct um; lia).
        clearbody mp. clear -Hmp CP. split; [split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; [lia|]]|].
        - assert (32 * 16384 <= csize cls * 16384) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
        - rewrite Z.mul_comm. pose proof (Z.mul_div_le (mp - alloc) (csize cls) ltac:(lia)). lia. }
      destruct NVB as [NVB NVS].
      assert (NvQ : n - nf <= Nv).
      { subst Nv. apply Z.div_le_lower_bound; [clear -CP; lia|]. destruct um.
        - clear -G6 Hq. lia.
        - symmetry in EUM. apply Z.ltb_ge in EUM. clear -EUM Hq. lia. }
      assert (MP7 : mapped + (if um then 262144 else 0) <= 3758096384) by (destruct um; [pose proof (NEX eq_refl); clear -H; unfold KFREEARRAY_OFF in *; lia| clear -G7; lia]).
      assert (FAM0 : fm = true -> fam = 0).
      { intros Efm. rewrite Efm in EFM. symmetry in EFM. apply Z.ltb_lt in EFM. unfold hideP in FAL. clear -EFM FAL FA0 NVB G8 LT NR. Z.div_mod_to_equations. nia. }
      assert (FAM' : 4 * (nf + Nv) <= fam' /\ fam' <= 536870912 /\ 0 <= fam').
      { subst fam'. destruct fm.
        - pose proof (FAM0 eq_refl). clear -H NVB G8 LT NR. Z.div_mod_to_equations. (cut_on [G8 NR LT NVB H0 H1] nia).
        - symmetry in EFM. apply Z.ltb_ge in EFM. clear -EFM G10 FA0. lia. }
      (nelim FAM' 3%nat; intros FM1 FM2 FM3).
      (* [comment removed for export] *)
      assert (DJP : forall a sz, (a + sz <= lo \/ bv_unsigned sp + -32 + -128 <= a) -> (a + sz <= Rc \/ Rc + 128 <= a) -> (a + sz <= t + 2768 \/ t + 2896 <= a) ->
                    (um = true -> a + sz <= RB + mapped \/ RB + mapped + 262144 <= a) -> (um = true -> a + sz <= SH (RB + mapped) \/ SH (RB + mapped) + 32768 <= a) ->
                    (a + sz <= FA + 4 * nf \/ FA + 4 * nf + 4 * Nv <= a) ->
                    (fm = true -> a + sz <= FA + fam \/ FA + fam + 262144 <= a) -> (fm = true -> a + sz <= SH (FA + fam) \/ SH (FA + fam) + 32768 <= a) ->
                    disjoint_from (pop_W lo (bv_unsigned sp + -32 + -128) Rc (st_t st) stt (RB + mapped) (FA + 4 * nf) Nv (FA + fam) um fm) a sz).
      { intros a sz D1 D2 D3 D4 D5 D6 D7 D8. unfold pop_W, prf_W. fold t. clear -D1 D2 D3 D4 D5 D6 D7 D8 ESTT EP.
        destruct um; destruct fm; try specialize (D4 eq_refl); try specialize (D5 eq_refl); try specialize (D7 eq_refl); try specialize (D8 eq_refl); cbn; repeat split; try exact I;
          (* [comment removed for export] *)
          first [ exact D1 | exact D4 | exact D5 | exact D6 | exact D7 | exact D8 | (clear - D2; lia) | (clear - D3 EP ESTT; lia) | (lia_on D1 D2 D3 EP D4 D5 D6 D7 D8) ]. }
      assert (SHFF : SH (FA + fam) + 32768 <= 17594333495296) by (unfold SH, SHADOW_OFFSET; clear -G1 G3 G4 G5 EFA FA0 G10; Z.div_mod_to_equations; lia).
      assert (SHFL : 2147450880 <= SH (FA + fam)) by (unfold SH, SHADOW_OFFSET; clear -G1 G3 G4 G5 EFA FA0 G10; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      cbv beta delta [wz]. replace (ret_pc (Z_to_bv 64 225440)) with (Z_to_bv 64 225440 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      eapply lscps_evt_then.
      { eapply gfa_ok with (n := n) (nf' := nf + Nv); [exact MI3| exact RIa3| unfold KHIGHMEM_BEG, AIMG_HI; clear -G1 G3 ERC Hc; lia| idtac; clear -G4 G5 ERC Hc; lia| exact NR| clear -NvQ NVB LT G8 NR; lia]. }
      cbv beta. intros ms4 nelH_; (nelim nelH_ 6%nat; intros m4 -> MU4 WM4 MI4 RIa4).
      set (WH6 := [(lo, bv_unsigned sp); (Rc, Rc + 24); (Rc + 72, Rc + 80); (pc, pc + 80)]).
      assert (DJ6r : forall a sz, Rc + 24 <= a -> a + sz <= Rc + 72 -> disjoint_from WH6 a sz).
      { intros a sz H1 H2. subst WH6. unfold hideP in RCT. clear -H1 H2 RCT HCEn LO2 G3 G4 G5 ERC EPC EP TR TRa TRb TRi Hc. cbn. split; [djlr|]. split; [djlr|]. split; [djlr|]. split; [| exact I]. destruct RCT; [right| left]; lia. }
      assert (DJ6f : forall a sz, RB <= a -> a + sz <= FA + 536870912 -> disjoint_from WH6 a sz).
      { intros a sz H1 H2. subst WH6. unfold hideP in RBT. clear -H1 H2 RBT HCEn LO2 G2 G3 G4 G5 ERC EFA EPC EP TR TRa TRb TRi Hc. cbn. split; [djlr|]. split; [djlr|]. split; [djlr|]. split; [| exact I]. destruct RBT; [right| left]; lia. }
      assert (DJ6h : forall a sz, 2147450880 <= a -> a + sz <= 17594333495296 -> disjoint_from WH6 a sz).
      { intros a sz H1 H2. subst WH6. clear -H1 H2 HCEn LO2 G1 G3 G4 G5 ERC EPC EP TR TRa TRb TRi Hc. cbn. split; [djlr|]. split; [djlr|]. split; [djlr|]. split; [djlr| exact I]. }
      assert (DJ6p : forall c a sz, 0 <= c < 32 -> c <> cls -> P + 80 * c <= a -> a + sz <= P + 80 * c + 80 -> disjoint_from WH6 a sz).
      { intros c a sz Hc' NE H1 H2. subst WH6. unfold hideP in RCT. clear -Hc' NE H1 H2 RCT HCEn LO2 G3 G4 G5 ERC EPC EP TR TRa TRb TRi Hc. cbn. split; [djlr|]. split; [destruct RCT; [left| right]; lia|]. split; [destruct RCT; [left| right]; lia|]. split; [| exact I]. destruct (Z_lt_le_dec c cls); [left| right]; nia. }
      (* [comment removed for export] *)
      pose proof FRG as FRG4. eapply (rw_cells_transport asegs _ m2 m3) in FRG4; [| exact MU3| exact WM3| apply DJP; cbn; unfold hideP in SHB; clear -SHB SHFF SHFL HCEn LO2 G1 G3 G4 G5 G6 G7 G8 G10 EFA FA0 ERC Hc TR TRa TRb TRi NVB LT NR NEX FAM0; try (intros EF; first [pose proof (FAM0 EF) as FZ| pose proof (NEX EF) as FZ]); right; unfold KFREEARRAY_OFF in *; lia].
      eapply (rw_cells_transport asegs _ m3 m4) in FRG4; [| exact MU4| exact WM4| clear -HCEn LO2 G3 G4 G5 ERC Hc; dj].
      pose proof ST3 as ST4. eapply (stk_transport_disjoint asegs _ m3 m4) in ST4; [| exact MU4| exact WM4| clear -HCEn LO2 G3 G4 G5 ERC Hc; dj].
      pose proof RIb3 as RIb4. eapply (rw_cells_transport asegs _ m3 m4) in RIb4; [| exact MU4| exact WM4| clear; dj]. apply rinfo_split72 in RIb4.
      pose proof VT as VT4. eapply (stk_wmono_oclr m m4) in VT4; [| eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| eapply wmono_trans; [exact WM3| exact WM4]]]| exact TRo| clear -TRc; pose proof ceil_lt64; lia].
      destruct (vis_carve m4 t (t + 4096) CH (Z.to_nat (4 * n)) VT4 ltac:(clear -EPC ECH EP Hc; lia) ltac:(clear -EPC ECH EP Hc NR; lia)) as [junk JK].
      destruct (p_u32arr_of_u8arr asegs m4 CH junk (Z.to_nat n) (u8arr_of_rw_cells asegs _ _ _ _ JK)) as (dpre & LD & DST). (* [comment removed for export] *)
      { destruct JK as [[WFj _] _]. cbn in WFj. clear -WFj NR. lia. }
      pose proof (wc_alloc_carved st cls WC) as AC. fold r alloc in AC. assert (EAL : alloc = ncarved st cls * csize cls) by exact AC. clear AC.
      assert (NC0 : 0 <= ncarved st cls) by (clear -EAL G6 CP; nia).
      pose proof FILL3 as FILL4. eapply (u32arr_transport asegs _ m3 m4) in FILL4; [| exact MU4| exact WM4| rewrite fill_vals_length, Z2Nat.id by (clear -NVB; lia); clear -G3 ERC EFA G8 Hc NVB LT NR; dj].
      assert (ENL : forall i, nf + Nv - n <= i < nf + Nv - n + Z.of_nat (Z.to_nat n) -> rw_cells asegs m4 (FA + 4 * i) [W4 (nthz L i 0)]).
      { intros i Hi. subst L. destruct (Z_lt_le_dec i nf) as [LTi|GEi].
        - rewrite nthz_app_l by (unfold nf, num_freed in LTi; fold r in LTi; clear -Hi LTi NvQ; lia).
          pose proof (EN i ltac:(clear -Hi LTi NvQ; lia)) as E0.
          eapply (rw_cells_transport asegs _ m m1) in E0; [| exact MU1| exact WM1| apply DJFA; cbn; clear -Hi LTi NvQ EFA G9 G10; lia].
          eapply (rw_cells_transport asegs _ m1 m2) in E0; [| exact MU2| exact WM2| clear -Hi LTi NvQ HCEn LO2 G3 G4 G5 G9 G10 ERC EFA Hc; dj].
          eapply (rw_cells_transport asegs _ m2 m3) in E0; [| exact MU3| exact WM3| apply DJP; cbn; unfold hideP in SHB, RBT; clear -Hi LTi NvQ SHB RBT SHFF SHFL HCEn LO2 G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 EFA FA0 ERC Hc TR TRa TRb TRi NVB LT NR NEX;
              [djlr| djlr| destruct RBT; [right| left]; lia| intros EU; pose proof (NEX EU) as NX; unfold KFREEARRAY_OFF in NX; djlrk ltac:(cut_to EFA NvQ Hi NX)| intros _; djlrk ltac:(cut_to G1 EFA SHB NvQ Hi)| djlr| intros _; djlr| intros _; djlr]].
          eapply (rw_cells_transport asegs _ m3 m4); [exact E0| exact MU4| exact WM4| clear -Hi LTi NvQ G3 G9 G10 ERC EFA Hc; dj].
        - assert (ZL : zlen (r_fa r) = nf) by reflexivity. rewrite nthz_app_r by (rewrite ZL; exact GEi). rewrite ZL.
          rewrite nthz_newc by (clear -Hi GEi NvQ; lia).
          replace (chunk_cptr cls (ncarved st cls + Nv - 1 - (i - nf))) with ((alloc + Z.of_nat (Z.to_nat Nv - 1 - Z.to_nat (i - nf)) * csize cls) / 16).
          2:{ unfold chunk_cptr. rewrite EAL. f_equal. clear -Hi GEi NvQ NVB NC0. rewrite <- Z.mul_add_distr_r. f_equal. lia. }
          replace (FA + 4 * i) with (FA + 4 * nf + 4 * (i - nf)) by (clear; lia).
          eapply (cells_of_u32arr _ _ _ (i - nf)); [exact FILL4| | clear -GEi; lia]. apply fill_vals_nth. clear -Hi GEi NvQ NVB. lia. }
      pose proof (u32arr_of_cells (Z.to_nat n) m4 FA (nf + Nv - n) (fun i => nthz L i 0) ltac:(clear -G1 EFA; lia) ltac:(clear -G3 G4 G5 EFA FM1 FM2 NR; lia) ltac:(clear -NvQ; lia) ENL) as FAU. cbv beta in FAU.
      set (fa := map (fun j => nthz L (nf + Nv - n + Z.of_nat j) 0) (seq 0 (Z.to_nat n))).
      assert (EWL : wl fa = map (fun j : nat => wz (nthz L (nf + Nv - n + Z.of_nat j) 0)) (seq 0 (Z.to_nat n))) by (subst fa; unfold wl; rewrite map_map; reflexivity).
      rewrite <- EWL in FAU.
      assert (LSM : forall i, 0 <= i < nf + Nv -> 0 <= nthz L i 0 < 2^31).
      { intros i Hi. subst L. destruct (Z_lt_le_dec i nf) as [LTi|GEi].
        - rewrite nthz_app_l by (unfold nf, num_freed in LTi; fold r in LTi; clear -Hi LTi; lia).
          pose proof (fa_entry_small st cls i WF Hc ltac:(clear -Hi LTi; unfold nf; lia)). clear -H. unfold r. lia.
        - assert (ZL : zlen (r_fa r) = nf) by reflexivity. rewrite nthz_app_r by (rewrite ZL; exact GEi). rewrite ZL. rewrite nthz_newc by (clear -Hi GEi; lia).
          pose proof (chunk_cptr_small cls (ncarved st cls + Nv - 1 - (i - nf)) Hc ltac:(clear -Hi GEi NC0; lia)). 
          assert ((ncarved st cls + Nv - 1 - (i - nf)) * csize cls + csize cls <= 3758096384).
          { replace ((ncarved st cls + Nv - 1 - (i - nf)) * csize cls + csize cls) with (ncarved st cls * csize cls + (Nv - (i - nf)) * csize cls) by (clear; lia).
            rewrite <- EAL. assert ((Nv - (i - nf)) * csize cls <= Nv * csize cls) by (apply Z.mul_le_mono_nonneg_r; clear -Hi GEi CP; lia). clear -H0 NVS MP7 G6. lia. }
          specialize (H H0). clear -H. lia. }
      assert (FAS : Forall (fun z => 0 <= z < 2^31) fa).
      { subst fa. apply Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj. apply LSM. clear -Hj NvQ NR LT G8. lia. }
      eapply lscps_evt_then.
      { eapply gfa_tail with (lo := lo) (fa := fa) (dpre := dpre);
          [exact MI4| rewrite ?E32, ?E32'; exact ST4| exact HCE| rewrite ?E32, ?E32'; clear -LO2; lia| rewrite ?E32, ?E32'; exact FRG4| exact RIa4| exact RIb4
          | unfold KHIGHMEM_BEG, AIMG_HI; clear -G1 G3 ERC Hc; lia| idtac; clear -G4 G5 ERC Hc; lia| exact RC8
          | unfold KHIGHMEM_BEG, AIMG_HI; clear -G1 EFA; lia| clear -G3 ERC EFA Hc; lia| unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; clear -TR TRa TRi EPC ECH EP Hc NR; lia| idtac; clear -TR TRa TRb TRi EPC ECH EP Hc NR; lia
          | unfold hideP in RCT; clear -RCT EPC ECH EP Hc NR; destruct RCT; [left| right]; lia
          | unfold hideP in RBT; clear -RBT EPC ECH EP EFA Hc NR; destruct RBT; [left| right]; lia
          | exact NR| clear -NvQ; lia| clear -FM1 FM2 NR NvQ; lia
          | subst fa; rewrite length_map, length_seq; reflexivity| exact FAS| exact LD| replace (nf + Nv - n - n + n) with (nf + Nv - n) by (clear; lia); exact FAU || exact FAU| exact DST]. }
      cbv beta. intros ms5 nelH_; (nelim nelH_ 25%nat; intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m5 sna' -> MU5 WM5 MI5 ST5 RIa5 RIb5 FAU5 CHU5).
      rewrite ?E32, ?E32' in MU5. rewrite ?E32, ?E32' in ST5.
      cbv beta delta [wz]. replace (ret_pc (Z_to_bv 64 224548)) with (Z_to_bv 64 224548 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      apply rinfo_join72 in RIb5.
      assert (MU35 : munch WH6 m3 m5).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU4]| eapply munch_weaken; [| exact MU5]]; subst WH6; clear -LO2 ECH NR; subfp. }
      pose proof (wmono_trans _ _ _ _ WM4 WM5) as WM35.
      pose proof FRR2 as FRR5. eapply (rw_cells_transport asegs _ m2 m3) in FRR5; [| exact MU3| exact WM3| apply DJP; cbn; unfold hideP in SHB; clear -SHB SHFF SHFL HCEn LO2 G1 G3 G4 G5 G6 G7 G8 G10 EFA FA0 ERC Hc TR TRa TRb TRi NVB LT NR NEX FAM0; try (intros EF; first [pose proof (FAM0 EF) as FZ| pose proof (NEX EF) as FZ]); right; unfold KFREEARRAY_OFF in *; lia].
      eapply (rw_cells_transport asegs _ m3 m4) in FRR5; [| exact MU4| exact WM4| clear -HCEn LO2 G3 G4 G5 ERC Hc; dj].
      eapply (rw_cells_transport asegs _ m4 m5) in FRR5; [| exact MU5| exact WM5| clear -HCEn LO2 G3 G4 G5 ERC EPC ECH EP TR TRa TRb TRi Hc NR; dj].
      pose proof PCC2 as PCC5. eapply (rw_cells_transport asegs _ m2 m3) in PCC5; [| exact MU3| exact WM3| apply DJP; cbn; unfold hideP in RCT, RBT, SHB; clear -RCT RBT SHB SHFF SHFL HCEn LO2 G1 G2 G3 G4 G5 G6 G7 G8 G10 EFA FA0 ERC EPC EP Hc TR TRa TRb TRi NVB LT NR FAM0;
          [djlr| destruct RCT; [left| right]; lia| djlr| intros _; destruct RBT; [left| right]; lia| intros _; djlrk ltac:(cut_to Hc TRb G1 G3 ERC EPC EP RBT SHB)| destruct RBT; [left| right]; lia
          | intros EF; pose proof (FAM0 EF) as FZ; destruct RBT; [left| right]; lia| intros _; djlrk ltac:(cut_to Hc TRb G1 G3 ERC EPC EP RBT SHFF SHFL)]].
      eapply (rw_cells_transport asegs _ m3 m4) in PCC5; [| exact MU4| exact WM4| unfold hideP in RCT; clear -RCT HCEn LO2 G3 G4 G5 ERC EPC EP TR TRa TRb TRi Hc; cbn; split; [destruct RCT; [left| right]; lia| exact I]].
      eapply (rw_cells_transport asegs _ m4 m5) in PCC5; [| exact MU5| exact WM5| unfold hideP in RCT; clear -RCT HCEn LO2 G3 G4 G5 ERC EPC ECH EP TR TRa TRb TRi Hc NR].
      2:{ cbn. split; [djlr|]. split; [destruct RCT; [left| right]; lia|]. split; [destruct RCT; [left| right]; lia|]. split; [djlr| exact I]. }
      eapply lscps_evt_then.
      { eapply (refill_ret sp gp tp) with (lo := lo) (r := 1); [exact MI5| exact ST5| exact HCE| clear -LO2; lia| exact FRR5| exact PCC5
          | unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; clear -TR TRa TRi EPC EP Hc; lia| idtac; clear -TR TRa TRb TRi EPC EP Hc; lia| clear -NR; lia| clear; lia]. }
      cbv beta. intros ms6 nelH_; (nelim nelH_ 21%nat; intros w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m6 -> MU6 WM6 MI6 ST6 PCC6).
      cbn [Z.eqb Pos.eqb] in PCC6.
      (* [comment removed for export] *)
      assert (MU36 : munch WH6 m3 m6).
      { eapply munch_trans; [exact MU35| eapply munch_weaken; [| exact MU6]]; subst WH6; clear; subfp. }
      pose proof (wmono_trans _ _ _ _ WM35 WM6) as WM36.
      pose proof (wmono_trans _ _ _ _ WM3 WM36) as WM26'. pose proof (wmono_trans _ _ _ _ WM2 WM26') as WM16. pose proof (wmono_trans _ _ _ _ WM1 WM16) as WM06.
      assert (USZ : um = true -> usz = 262144). { intros E. pose proof (NEX E) as X. unfold usz. clear -X. unfold KFREEARRAY_OFF in *. lia. }
      assert (MUT : munch (WTOT lo (bv_unsigned sp) P pc t Rc (RB + mapped) usz FA nf) m m6).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_trans; [eapply munch_weaken; [| exact MU3]| eapply munch_weaken; [| exact MU36]]]];
          unfold WTOT, WPRE, WREST, pop_W, prf_W; fold t; subst WH6.
        - clear; subfp.
        - clear -LO2; subfp.
        - pose proof FAM0 as F0. unfold hideP in SHF. clear -LO2 ESTT EP G8 G9 NVB FM1 FM2 F0 SHF EFA G3 ERC Hc USZ.
          destruct um; [pose proof (USZ eq_refl) as EU; clearbody usz; subst usz|]; (destruct fm; [pose proof (F0 eq_refl) as FZ; rewrite FZ, Z.add_0_r|]); subfpk ltac:(cut_to Cq EP G9 FZ FM1 FM2).
        - clear -ECH NR; subfp. }
      apply (K1 NEX w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m6 (le8 sna' ++ skipn 8 js) fa MI6 MUT WM06 ST6); clear KX1 KX K1.
      + eapply (rw_cells_transport asegs _ m5 m6); [exact RIa5| exact MU6| exact WM6| unfold hideP in RCT; clear -RCT HCEn LO2 G3 G4 G5 ERC EPC EP TR TRa TRb TRi Hc].
        cbn. split; [djlr|]. split; [destruct RCT; [right| left]; lia| exact I].
      + pose proof RI243 as X. eapply (rw_cells_transport asegs _ m3 m6); [exact X| exact MU36| exact WM36| apply DJ6r; cbn; clear; lia].
      + eapply (rw_cells_transport asegs _ m5 m6); [exact RIb5| exact MU6| exact WM6| unfold hideP in RCT; clear -RCT HCEn LO2 G3 G4 G5 ERC EPC EP TR TRa TRb TRi Hc].
        cbn. split; [djlr|]. split; [destruct RCT; [right| left]; lia| exact I].
      + eapply (stk_transport_disjoint asegs _ m3 m6); [exact VFA3| exact MU36| exact WM36| apply DJ6f; clear -EFA FM2 FM3; lia].
      + eapply (u32arr_transport asegs _ m3 m6); [exact FILL3| exact MU36| exact WM36| rewrite fill_vals_length, Z2Nat.id by (clear -NVB; lia); apply DJ6f; clear -EFA G8 NVB FM1 FM2; lia].
      + destruct um; [| exact I]. destruct VU3 as [VU3a VU3b]. split.
        * eapply (stk_transport_disjoint asegs _ m3 m6); [exact VU3a| exact MU36| exact WM36| apply DJ6f; clear -EFA G6 MP7; lia].
        * eapply (rw_cells_transport asegs _ m3 m6); [exact VU3b| exact MU36| exact WM36|].
          replace (Z.of_nat (cells_size [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))])) with 32768 by reflexivity.
          apply DJ6h; unfold hideP in SHB; clear -SHB; lia.
      + destruct fm; [| exact I].
        eapply (rw_cells_transport asegs _ m3 m6); [exact VF3| exact MU36| exact WM36|].
        replace (Z.of_nat (cells_size [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))])) with 32768 by reflexivity.
        apply DJ6h; [unfold SH, SHADOW_OFFSET; clear -G1 EFA FA0; Z.div_mod_to_equations; lia| clear -SHFF SHFL; lia].
      + subst fa. rewrite length_map, length_seq. reflexivity.
      + intros i Hi. subst fa. rewrite nthz_map_seq by (clear -Hi NR; lia). f_equal. clear -Hi NR. lia.
      + eapply (u32arr_transport asegs _ m5 m6); [exact CHU5| exact MU6| exact WM6|].
        subst fa. unfold wl. rewrite !length_map, length_seq. clear -HCEn LO2 EPC ECH EP TR TRa TRb TRi Hc NR. dj.
      + intros c Hc'. destruct (Z.eqb_spec c cls) as [->|NE]; [rewrite (proj2 (Z.eqb_neq cls 0)) by (clear -Hc; lia); exact PCC6|].
        pose proof (PCH1 c Hc') as X. unfold KNUMCLASSES in Hc'.
        eapply (rw_cells_transport asegs _ m1 m2) in X; [| exact MU2| exact WM2| unfold hideP in RCT; clear -RCT HCEn LO2 G3 G4 G5 ERC EPC EP TR TRa TRb TRi Hc Hc' NE].
        2:{ cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. change (pcaddr st c) with (P + 80 * c). cbn. split; [djlr|]. split; [destruct RCT; [left| right]; lia| exact I]. }
        eapply (rw_cells_transport asegs _ m2 m3) in X; [| exact MU3| exact WM3| apply DJP; cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; change (pcaddr st c) with (P + 80 * c);
             unfold hideP in RCT, RBT, SHB; clear -RCT RBT SHB SHFF SHFL HCEn LO2 G1 G2 G3 G4 G5 G6 G7 G8 G10 EFA FA0 ERC EPC EP Hc TR TRa TRb TRi Hc' NE NVB LT NR FAM0;
             [djlr| destruct RCT; [left| right]; lia| djlr| intros _; destruct RBT; [left| right]; lia| intros _; djlrk ltac:(cut_to TRb EP SHB Hc')| destruct RBT; [left| right]; lia
             | intros EF; pose proof (FAM0 EF) as FZ; destruct RBT; [left| right]; lia| intros _; djlrk ltac:(cut_to TRb EP SHFF SHFL Hc')]].
        eapply (rw_cells_transport asegs _ m3 m6); [exact X| exact MU36| exact WM36|].
        cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. change (pcaddr st c) with (P + 80 * c). apply (DJ6p c); clear -Hc' NE; lia.
      + intros c i Hc' Hi. destruct (Z.eq_dec c cls) as [->|NE]; [rewrite HC0 in Hi; change (zlen (@nil Z)) with 0 in Hi; exfalso; clear -Hi; lia|].
        pose proof (PCO1 c i Hc' Hi) as X. pose proof (wc_cache_max st c (wf_class_ok st WF c Hc')) as CM. pose proof (cmaxcount_le16 c) as CM16. unfold KNUMCLASSES in Hc'.
        eapply (rw_cells_transport asegs _ m1 m2) in X; [| exact MU2| exact WM2| unfold hideP in RCT; clear -RCT HCEn LO2 G3 G4 G5 ERC EPC EP TR TRa TRb TRi Hc Hc' NE Hi CM CM16].
        2:{ cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. change (pcaddr st c) with (P + 80 * c). cbn. split; [djlr|]. split; [destruct RCT; [left| right]; lia| exact I]. }
        eapply (rw_cells_transport asegs _ m2 m3) in X; [| exact MU3| exact WM3| apply DJP; cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; change (pcaddr st c) with (P + 80 * c);
             unfold hideP in RCT, RBT, SHB; clear -RCT RBT SHB SHFF SHFL HCEn LO2 G1 G2 G3 G4 G5 G6 G7 G8 G10 EFA FA0 ERC EPC EP Hc TR TRa TRb TRi Hc' NE Hi CM CM16 NVB LT NR FAM0;
             [djlr| destruct RCT; [left| right]; lia| djlr| intros _; destruct RBT; [left| right]; lia| intros _; djlrk ltac:(cut_to TRb EP SHB Hc' Hi CM CM16)| destruct RBT; [left| right]; lia
             | intros EF; pose proof (FAM0 EF) as FZ; destruct RBT; [left| right]; lia| intros _; djlrk ltac:(cut_to TRb EP SHFF SHFL Hc' Hi CM CM16)]].
        eapply (rw_cells_transport asegs _ m3 m6); [exact X| exact MU36| exact WM36|].
        cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. change (pcaddr st c) with (P + 80 * c). apply (DJ6p c); clear -Hc' NE Hi CM CM16; lia.
  Qed.
End RW.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem refill_spin_proof : refill_spec_spin.
Proof.
  unfold refill_spec_spin.
  intros ra sp gp tp x5 x6 x7 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc m mo g st0 cls lo.
  intros HRTS Hc HC0 HPRE -> -> -> -> TP HPV ST HCE LO2 MI KSPIN.
  destruct g as [G R]. cbn [g_res] in HPV. (nelim HRTS 6%nat; intros HR WF HM HG HFR HSW).
  destruct st0 as [z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5].
  set (st := mkRT z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5) in *.
  assert (Hcls : 0 <= cls < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  set (r := rg st cls) in *. set (nf := num_freed st cls) in *. set (n := nrefill cls) in *. set (S := csize cls).
  set (alloc := r_allocated r). set (mapped := r_mapped r) in *. set (fam := r_mapped_fa r).
  set (pop := nf <? n). set (um := pop && (mapped <? alloc + S * (n - nf))).
  set (Nv := if pop then (mapped + (if um then 262144 else 0) - alloc) / S else 0).
  set (fm := pop && (fam <? 4 * (nf + Nv))). set (nm := (4 * (nf + Nv) + 262143) / 262144 * 262144).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof HCE as HCEn. idtac. unfold AREFILL_STACK in LO2.
  (nelim (refill_cells st m cls HR WF Hc HC0) 14%nat; intros jr je js _ _ _ _ _ _ _ _ _ RIb _). fold r alloc mapped in RIb.
  assert (NAV : navail st cls = nf) by (unfold navail, avail_cptrs; fold r; rewrite HC0, app_nil_r; reflexivity).
  pose proof (nrefill_eq cls ltac:(lia)) as [_ NR]. fold n in NR.
  pose proof (wf_class_ok st WF cls Hcls) as WC.
  pose proof (wc_alloc_mapped st cls WC) as AM. pose proof (wc_fa_nonneg st cls WC) as FA0. pose proof (wc_fa_align st cls WC) as FAL. pose proof (wc_num_freed st cls WC) as NFF. pose proof (wc_residue st cls WC) as RES.
  fold r in AM, FA0, FAL, NFF, RES. fold alloc mapped in AM. fold fam in FA0, FAL, NFF. fold alloc mapped in RES. unfold num_freed in NFF. fold r nf in NFF. change (zlen (r_fa r)) with nf in NFF.
  pose proof (csize_pos cls ltac:(lia)) as CP. fold S in CP.
  assert (G8 : 0 <= nf) by (unfold nf, num_freed; apply zlen_nonneg).
  (* [comment removed for export] *)
  assert (FAM0 : fm = true -> fam = 0 /\ nm = 262144).
  { intros Efm. unfold fm in Efm. apply andb_true_iff in Efm as [Ep Ef]. apply Z.ltb_lt in Ef.
    assert (NVB : Nv <= 16385).
    { unfold Nv. rewrite Ep. apply Z.div_le_upper_bound; [lia|]. assert (32 * 16384 <= S * 16384) by (apply Z.mul_le_mono_nonneg_r; lia). destruct um; lia. }
    unfold pop in Ep. apply Z.ltb_lt in Ep.
    assert (fam = 0) by (clear -Ef FAL FA0 NVB G8 Ep NR; Z.div_mod_to_equations; nia). split; [exact H|]. unfold nm. clear -NVB G8 Ep NR H Ef. Z.div_mod_to_equations. nia. }
  assert (HRR : (if um then LUMP else 0) + (if fm then LUMP else 0) <= R).
  { pose proof (prov_cls_le st cls WF Hc) as PC.
    assert (PU : um = true -> LUMP <= provU st cls).
    { intros Eum. unfold um in Eum. apply andb_true_iff in Eum as [Ep Eu]. unfold pop in Ep. apply Z.ltb_lt in Ep. apply Z.ltb_lt in Eu.
      unfold LUMP. apply (lumpU_ok st cls WF Hc HC0); [exact Ep| exact Eu]. }
    assert (PF : fm = true -> LUMP <= provF st cls) by (intros Efm; destruct (FAM0 Efm) as [FZ _]; unfold LUMP; apply (lumpF_ok st cls WF Hc); exact FZ).
    pose proof (prov_classes_nonneg st). assert (0 <= provU st cls /\ 0 <= provF st cls) by (unfold provU, provF; lia).
    destruct um; destruct fm; try specialize (PU eq_refl); try specialize (PF eq_refl); lia. }
  apply lscps_assume. intros NWX HOK HBINV.
  eapply (refill_walk ra sp gp tp x5 x6 x7 s0 s1 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc m mo G R st cls lo
            HR WF HM HG Hc HC0 TP MI ST ltac:(split; [exact HCE| unfold AREFILL_STACK; clear -LO2; lia]) pop um fm true _ jr je js RIb eq_refl eq_refl eq_refl HRR).
  - (* [comment removed for export] *)
    intros Ep Eu _ EM. exfalso. unfold pop in Ep. apply Z.ltb_lt in Ep. rewrite NAV in HPRE. specialize (HPRE Ep). subst mapped r. unfold KFREEARRAY_OFF in *. clear -HPRE EM. lia.
  - intros Ep Eu _ EM. exfalso. unfold pop in Ep. apply Z.ltb_lt in Ep. rewrite NAV in HPRE. specialize (HPRE Ep). subst mapped r. unfold KFREEARRAY_OFF in *. clear -HPRE EM. lia.
  - (* [comment removed for export] *) exact I.
  - (* [comment removed for export] *) exact I.
  - (* [comment removed for export] *)
    intros NEX w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m' js' fa MI' MU' WM' ST' RIa' RI24' RIb' VFA' FILL' VU' VF' FL FN CHU' PCH' PCO'.
    apply lscps_done. unfold refill_post1, rt_post_std.
    exists w5, w6, w7, (wz 1), w11, w12, w13, w14, w15, w16, w17, w28, w29, w30, w31, m'.
    eexists (mkRT z1 z2 z3 (updz z4 cls (r_new z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5 cls n Nv nm um fm pop)) true
                   (updz z6 cls (skipn (Z.to_nat (nf + Nv - n)) (r_fa r ++ newc cls (ncarved st cls) Nv))) z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5).
    pose proof (csize_le64k' cls Hc) as CL. fold S in CL. (nelimp (slack_ok' cls Hc) 3%nat; intros SL _ _). fold n S in SL.
    assert (SQ : S * (n - nf) <= 262144).
    { assert (S * (n - nf) <= S * n) by (apply Z.mul_le_mono_nonneg_l; clear -CP NR G8; lia). clear -H CL SL CP NR. nia. }
    assert (NvQ : pop = true -> n - nf <= Nv).
    { intros Ep. unfold Nv. rewrite Ep. apply Z.div_le_lower_bound; [clear -CP; lia|]. unfold um. rewrite Ep. cbn [andb].
      destruct (Z.ltb_spec0 mapped (alloc + S * (n - nf))) as [LTm|GEm]; [clear -SQ AM LTm| clear -SQ AM GEm]; lia. }
    assert (HNv : 0 <= Nv /\ n <= nf + Nv).
    { unfold Nv in *. destruct pop eqn:Ep.
      - split; [apply Z.div_pos; [destruct um; lia| lia]| specialize (NvQ eq_refl); rewrite Ep in NvQ || idtac; lia].
      - unfold pop in Ep. apply Z.ltb_ge in Ep. lia. }
    assert (HPOP : pop = true -> nf < n /\ Nv = (r_mapped r + (if um then 262144 else 0) - r_allocated r) / S
        /\ um = (r_mapped r <? r_allocated r + (n - nf) * S) /\ (um = true -> r_mapped r + 262144 <= KFREEARRAY_OFF)
        /\ fm = (r_mapped_fa r <? 4 * (nf + Nv)) /\ nm = (4 * (nf + Nv) + 262143) / 262144 * 262144).
    { intros Ep. split; [unfold pop in Ep; apply Z.ltb_lt in Ep; exact Ep|]. split; [unfold Nv; rewrite Ep; reflexivity|].
      split; [unfold um; rewrite Ep; cbn [andb]; fold alloc mapped; rewrite (Z.mul_comm (n - nf) S); reflexivity|].
      split; [exact NEX|]. split; [unfold fm; rewrite Ep; reflexivity| reflexivity]. }
    assert (HHAVE : pop = false -> Nv = 0 /\ um = false /\ fm = false) by (intros Ep; unfold fm, Nv, um; rewrite Ep; cbn [andb]; repeat split; reflexivity).
    assert (NVB : Nv <= 16385).
    { unfold Nv. destruct pop; [| lia]. apply Z.div_le_upper_bound; [lia|]. assert (32 * 16384 <= S * 16384) by (apply Z.mul_le_mono_nonneg_r; lia). destruct um; lia. }
    pose proof (conj FL FN) as Hfa. clear FL FN RIb.
    split; [reflexivity|]. split; [exact MI'|]. split; [reflexivity|].
    split; [eapply rel_fins; (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [eapply RTS_fins; (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [exact ST'|].
    split; [eapply (cli_pres_fins z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5 cls) with (um := um); (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [eapply rt_frame_fins; (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [eapply gmono_fins with (lo := lo) (SP := bv_unsigned sp); (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    eapply budget_fins; (first [eassumption| exact I| idtac]); unfold CEIL; lia.
Qed.


End CeilWrap.
End RTW_p_refill.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep CJ_iface RT_art RT_kit RT_fp RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_mmapN.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_mmapN.RTW_sec_mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_kit RTW_p_map.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1.RTW_p_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_p_loops.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1.RTW_p_efa.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_p_pop1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_refillA.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_refillA.RTW_p_pop2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1.RTW_p_gfa.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1.RTW_p_refillw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_p_zone RTW_p_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_refillA.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_refillA.RTW_p_absf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_pop RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_lib.RTW_sec_alloc5.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_cost RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_q_needs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_p_refillA.
Import RTW_p_refill.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_nn_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_bandtac3 RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1.RTW_p_libo.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_kitL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

(* [comment removed for export] *)
Local Ltac djlr := first [left; lia | right; lia | lia].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Theorem refill_nn_proof : refill_nn_stmt.
Proof.
  unfold refill_nn_stmt, refill_room.
  intros ra sp gp tp x5 x6 x7 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc m mo g st0 cls lo.
  intros HRTS Hc HC0 -> -> -> -> TP HPV HPRE ST HCE LO2 MI.
  destruct g as [G R]. cbn [g_res] in HPV. destruct HRTS as (HR & WF & HM & HG & HFR & HSW).
  destruct st0 as [z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5].
  set (st := mkRT z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5) in *.
  assert (Hcls : 0 <= cls < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  set (r := rg st cls) in *. set (nf := num_freed st cls) in *. set (n := nrefill cls) in *. set (S := csize cls).
  set (alloc := r_allocated r). set (mapped := r_mapped r) in *. set (fam := r_mapped_fa r).
  set (pop := nf <? n). set (um := pop && (mapped <? alloc + S * (n - nf))).
  set (Nv := if pop then (mapped + (if um then 262144 else 0) - alloc) / S else 0).
  set (fm := pop && (fam <? 4 * (nf + Nv))). set (nm := (4 * (nf + Nv) + 262143) / 262144 * 262144).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof HCE as HCEn. idtac. unfold AREFILL_STACK in LO2.
  destruct (refill_cells st m cls HR WF Hc HC0) as (jr & je & js & _ & _ & _ & _ & _ & _ & _ & _ & _ & RIb & _). fold r alloc mapped in RIb.
  assert (NAV : navail st cls = nf) by (unfold navail, avail_cptrs; fold r; rewrite HC0, app_nil_r; reflexivity).
  pose proof (nrefill_eq cls ltac:(lia)) as [_ NR]. fold n in NR.
  pose proof (wf_class_ok st WF cls Hcls) as WC.
  pose proof (wc_alloc_mapped st cls WC) as AM. pose proof (wc_fa_nonneg st cls WC) as FA0. pose proof (wc_fa_align st cls WC) as FAL. pose proof (wc_num_freed st cls WC) as NFF. pose proof (wc_residue st cls WC) as RES.
  fold r in AM, FA0, FAL, NFF, RES. fold alloc mapped in AM. fold fam in FA0, FAL, NFF. fold alloc mapped in RES. unfold num_freed in NFF. fold r nf in NFF. change (zlen (r_fa r)) with nf in NFF.
  pose proof (csize_pos cls ltac:(lia)) as CP. fold S in CP.
  assert (G8 : 0 <= nf) by (unfold nf, num_freed; apply zlen_nonneg).
  (* [comment removed for export] *)
  assert (FAM0 : fm = true -> fam = 0 /\ nm = 262144).
  { intros Efm. unfold fm in Efm. apply andb_true_iff in Efm as [Ep Ef]. apply Z.ltb_lt in Ef.
    assert (NVB : Nv <= 16385).
    { unfold Nv. rewrite Ep. apply Z.div_le_upper_bound; [lia|]. assert (32 * 16384 <= S * 16384) by (apply Z.mul_le_mono_nonneg_r; lia). destruct um; lia. }
    unfold pop in Ep. apply Z.ltb_lt in Ep.
    assert (fam = 0) by (clear -Ef FAL FA0 NVB G8 Ep NR; Z.div_mod_to_equations; nia). split; [exact H|]. unfold nm. clear -NVB G8 Ep NR H Ef. Z.div_mod_to_equations. nia. }
  assert (HRR : (if um then LUMP else 0) + (if fm then LUMP else 0) <= R).
  { pose proof (prov_cls_le st cls WF Hc) as PC.
    assert (PU : um = true -> LUMP <= provU st cls).
    { intros Eum. unfold um in Eum. apply andb_true_iff in Eum as [Ep Eu]. unfold pop in Ep. apply Z.ltb_lt in Ep. apply Z.ltb_lt in Eu.
      unfold LUMP. apply (lumpU_ok st cls WF Hc HC0); [exact Ep| exact Eu]. }
    assert (PF : fm = true -> LUMP <= provF st cls) by (intros Efm; destruct (FAM0 Efm) as [FZ _]; unfold LUMP; apply (lumpF_ok st cls WF Hc); exact FZ).
    pose proof (prov_classes_nonneg st). assert (0 <= provU st cls /\ 0 <= provF st cls) by (unfold provU, provF; lia).
    destruct um; destruct fm; try specialize (PU eq_refl); try specialize (PF eq_refl); lia. }
  apply lscps_assume. intros NWX HOK HBINV.
  eapply (refill_walk ra sp gp tp x5 x6 x7 s0 s1 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc m mo G R st cls lo
            HR WF HM HG Hc HC0 TP MI ST ltac:(split; [exact HCE| unfold AREFILL_STACK; clear -LO2; lia]) pop um fm false _ jr je js RIb eq_refl eq_refl eq_refl HRR).
  - (* [comment removed for export] *)
    intros Ep Eu _ EM. exfalso. unfold pop in Ep. apply Z.ltb_lt in Ep. rewrite NAV in HPRE. specialize (HPRE Ep). subst mapped r. unfold KFREEARRAY_OFF in *. clear -HPRE EM. lia.
  - intros Ep Eu _ EM. exfalso. unfold pop in Ep. apply Z.ltb_lt in Ep. rewrite NAV in HPRE. specialize (HPRE Ep). subst mapped r. unfold KFREEARRAY_OFF in *. clear -HPRE EM. lia.
  - (* [comment removed for export] *) exact I.
  - (* [comment removed for export] *) exact I.
  - (* [comment removed for export] *)
    intros NEX w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m' js' fa MI' MU' WM' ST' RIa' RI24' RIb' VFA' FILL' VU' VF' FL FN CHU' PCH' PCO'.
    apply lscps_done. unfold refill2_post, rt_post_std.
    exists w5, w6, w7, (wz 1), w11, w12, w13, w14, w15, w16, w17, w28, w29, w30, w31, m'.
    eexists (mkRT z1 z2 z3 (updz z4 cls (r_new z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5 cls n Nv nm um fm pop)) true
                   (updz z6 cls (skipn (Z.to_nat (nf + Nv - n)) (r_fa r ++ newc cls (ncarved st cls) Nv))) z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5).
    pose proof (csize_le64k' cls Hc) as CL. fold S in CL. pose proof (slack_ok' cls Hc) as (SL & _ & _). fold n S in SL.
    assert (SQ : S * (n - nf) <= 262144).
    { assert (S * (n - nf) <= S * n) by (apply Z.mul_le_mono_nonneg_l; clear -CP NR G8; lia). clear -H CL SL CP NR. nia. }
    assert (NvQ : pop = true -> n - nf <= Nv).
    { intros Ep. unfold Nv. rewrite Ep. apply Z.div_le_lower_bound; [clear -CP; lia|]. unfold um. rewrite Ep. cbn [andb].
      destruct (Z.ltb_spec0 mapped (alloc + S * (n - nf))) as [LTm|GEm]; [clear -SQ AM LTm| clear -SQ AM GEm]; lia. }
    assert (HNv : 0 <= Nv /\ n <= nf + Nv).
    { unfold Nv in *. destruct pop eqn:Ep.
      - split; [apply Z.div_pos; [destruct um; lia| lia]| specialize (NvQ eq_refl); rewrite Ep in NvQ || idtac; lia].
      - unfold pop in Ep. apply Z.ltb_ge in Ep. lia. }
    assert (HPOP : pop = true -> nf < n /\ Nv = (r_mapped r + (if um then 262144 else 0) - r_allocated r) / S
        /\ um = (r_mapped r <? r_allocated r + (n - nf) * S) /\ (um = true -> r_mapped r + 262144 <= KFREEARRAY_OFF)
        /\ fm = (r_mapped_fa r <? 4 * (nf + Nv)) /\ nm = (4 * (nf + Nv) + 262143) / 262144 * 262144).
    { intros Ep. split; [unfold pop in Ep; apply Z.ltb_lt in Ep; exact Ep|]. split; [unfold Nv; rewrite Ep; reflexivity|].
      split; [unfold um; rewrite Ep; cbn [andb]; fold alloc mapped; rewrite (Z.mul_comm (n - nf) S); reflexivity|].
      split; [exact NEX|]. split; [unfold fm; rewrite Ep; reflexivity| reflexivity]. }
    assert (HHAVE : pop = false -> Nv = 0 /\ um = false /\ fm = false) by (intros Ep; unfold fm, Nv, um; rewrite Ep; cbn [andb]; repeat split; reflexivity).
    assert (NVB : Nv <= 16385).
    { unfold Nv. destruct pop; [| lia]. apply Z.div_le_upper_bound; [lia|]. assert (32 * 16384 <= S * 16384) by (apply Z.mul_le_mono_nonneg_r; lia). destruct um; lia. }
    pose proof (conj FL FN) as Hfa. clear FL FN RIb.
    split; [reflexivity|]. split; [exact MI'|]. split; [reflexivity|].
    split; [eapply rel_fins; (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [eapply RTS_fins; (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [exact ST'|].
    split; [eapply (cli_pres_fins z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5 cls) with (um := um); (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [eapply rt_frame_fins'; (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [eapply gmono_fins with (lo := lo) (SP := bv_unsigned sp); (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    eapply budget_fins; (first [eassumption| exact I| idtac]); unfold CEIL; lia.
Qed.

End CeilWrap.
