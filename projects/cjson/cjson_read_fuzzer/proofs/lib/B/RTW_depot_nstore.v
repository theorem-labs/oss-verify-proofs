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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LMeasure.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require InitMem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_depot_create.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.InitMem.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_depot_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_lock OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_depot_n2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma w4_of_bytes0 : forall m a, rw_cells bsegs m a [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] -> rw_cells bsegs m a [C4 (Z_to_bv 64 0)].
Proof. intros m a H. eapply rw_cells_recast; [exact H| cbn; tauto| reflexivity| reflexivity]. Qed.
Lemma bytes_of_w4_1 : forall m a, rw_cells bsegs m a [C4 (Z_to_bv 64 1)] -> rw_cells bsegs m a [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof. intros m a H. eapply rw_cells_recast; [exact H| cbn; tauto| reflexivity| reflexivity]. Qed.

Section TLMCREATE.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (mv : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (k lo : Z).
  Hypothesis HC : mmap_consts mv.
  Hypothesis MI0 : mem_inv bsegs mv.
  Hypothesis ST0 : stk bsegs mv lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + 352 <= bv_unsigned sp.
  Hypothesis HK : 0 <= k < 2^15.
  Hypothesis MU0 : rw_cells bsegs mv 0x58b8a0 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Hypothesis MAP0 : rw_cells bsegs mv (0x58b8a8 + 8 * k) [C8 (Z_to_bv 64 0)].

  Lemma tlm_create_spec : forall (P : machine_state -> Model -> lghost -> Prop),
    1048576 <= R -> mmap_placeable mo 1048576 ->
    (forall (a : word) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte),
       mmap_grant mo a 1048576 ->
       mem_inv bsegs m' ->
       munch [(lo, bv_unsigned sp); (bv_unsigned a, bv_unsigned a + 1048576); (0x58b8a0, 0x58b8a4); (0x58b8a8 + 8 * k, 0x58b8a8 + 8 * k + 8)] mv m' ->
       wmono bsegs mv m' -> stk bsegs m' lo (bv_unsigned sp) ->
       rw_cells bsegs m' (bv_unsigned a) [CB (Z.to_nat 1048576) (repeat (Z_to_bv 8 0) (Z.to_nat 1048576))] ->
       rw_cells bsegs m' 0x58b8a0 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
       rw_cells bsegs m' (0x58b8a8 + 8 * k) [C8 a] ->
       AIMG_HI <= bv_unsigned a -> bv_unsigned a + 1048576 <= alloc_ceiling -> bv_unsigned a mod 4096 = 0 ->
       LSCPS bsegs P (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (ret_pc ra) fc None m' (seg_rom bsegs)) (mm_add_map a (Z_to_bv 64 1048576) mo) (mkG G (R - 1048576))) ->
    LSCPS bsegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x58b8a0) (Z_to_bv 64 k) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x74bc8) fc None mv (seg_rom bsegs)) mo (mkG G R).
  Proof.
    intros P HRR HPL K.
    pose proof HC as HC0. destruct HC as (GOTP & PSC & GOTC & CF260 & CF144 & GOTS & DY). clear GOTC CF260 CF144 GOTS DY.
    hide GOTP. hide PSC.
    pose proof MI0 as MI. pose proof ST0 as ST. clear ST0. pose proof MU0 as MUW. pose proof MAP0 as MAP. clear MU0 MAP0.
    pose proof (munch_refl [(lo, bv_unsigned sp); (0x58b8a0, 0x58b8a4); (0x58b8a8 + 8 * k, 0x58b8a8 + 8 * k + 8)] mv) as MU. pose proof (wmono_refl bsegs mv) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
    apply lscps_assume. intros NWX HOK HBINV.
    apply lscps_step_evt.
    carve_frame 32%nat ST.
    do 5 lstep. (* [comment removed for export] *)
    lstep. lstep. fl. lstep. lstep. (* [comment removed for export] *)
    apply w4_of_bytes0 in MUW.
    amo_step. fl. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *)
    amo_step. fix_lit_store. fl. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    lstep. fl. lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    destruct (ex_intro (fun q => q = 0x58b8a0 + 8 * k) _ eq_refl) as [q Hq].
    replace (0x58b8a8 + 8 * k) with (q + 8) in MAP, MU by lia.
    setreg 9 (Z_to_bv 64 q) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    lstep. fl. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    recell GOTP MU. lstep. lstep. fl. clear GOTP. (* [comment removed for export] *)
    recell PSC MU. lstep. fl. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. fl. lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *) 
    lstep. lstep. fl. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    assert (E32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp - 32) by (rewrite unsigned_lit by lia; lia).
    apply evt_done. eapply mmapordie_spec with (lo := lo).
    { eapply (mmap_consts_munch _ mv _ HC0 MU); cbn; lia. }
    { exact MI. }
    { rewrite E32. exact ST. }
    { rewrite E32. lia. }
    { cbn; lia. } { lia. } { lia. } { exact HPL. }
    intros a x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m' GR MI' MU' WM' ST' ZNEW.
    rewrite E32 in MU', ST'.
    pose proof GR as (GA & GP & GC & GF). idtac. rewrite page_size_eq in GA.
    pose proof (grant_above_image mo a 1048576 HOK GR ltac:(lia)) as GI. unfold AIMG_HI in GI.
    pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. cbn in RA.
    eapply rw_cells_transport in FR; [| exact MU'| exact WM'| cbn; lia].
    eapply rw_cells_transport in MUW; [| exact MU'| exact WM'| cbn; lia].
    eapply rw_cells_transport in MAP; [| exact MU'| exact WM'| cbn; lia].
    apply (munch_weaken _ [(lo, bv_unsigned sp); (bv_unsigned a, bv_unsigned a + 1048576); (0x58b8a0, 0x58b8a4); (q + 8, q + 8 + 8)]) in MU. 2:{ unfold sub_fp; cbn; intros; lia. }
    apply (munch_weaken _ [(lo, bv_unsigned sp); (bv_unsigned a, bv_unsigned a + 1048576); (0x58b8a0, 0x58b8a4); (q + 8, q + 8 + 8)]) in MU'. 2:{ unfold sub_fp; cbn; intros; lia. }
    pose proof (munch_trans _ _ _ _ MU MU') as MU2. pose proof (wmono_trans bsegs _ _ _ WM WM') as WM2.
    clear MU MU' WM WM' MI ST. rename MU2 into MU. rename WM2 into WM. rename MI' into MI. rename ST' into ST.
    apply lscps_step_evt.
    replace (ret_pc (Z_to_bv 64 478316)) with (Z_to_bv 64 478316 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    apply bytes_of_w4_1 in MUW. lstep. (* [comment removed for export] *)
    do 4 lstep. lstep. lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    replace (q + 8 + 8) with (0x58b8a8 + 8 * k + 8) in MU by lia. replace (q + 8) with (0x58b8a8 + 8 * k) in MU, MAP by lia.
    apply evt_done. eapply K; [exact GR| exact MI| exact MU| exact WM| exact ST| exact ZNEW| exact MUW| exact MAP| unfold AIMG_HI; lia| idtac; lia| exact GA].
  Qed.
End TLMCREATE.

(* [comment removed for export] *)
Lemma land_align4 : forall x, 0 <= x < 2^64 -> x mod 4 = 0 -> Z.land x 18446744073709551612 = x.
Proof.
  intros x Hx Ha.
  replace 18446744073709551612 with (Z.lxor (Z.ones 64) (Z.ones 2)) by reflexivity.
  transitivity (Z.shiftl (Z.shiftr x 2) 2).
  2:{ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. }
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.lxor_spec, Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i 2) as [Hi3|Hi3].
  - rewrite (Z.testbit_neg_r (Z.shiftr x 2)) by lia. rewrite !Z.ones_spec_low by lia. cbn. apply andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (i - 2 + 2) with i by lia. rewrite (Z.ones_spec_high 2 i) by lia.
    destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
    + rewrite Z.ones_spec_low by lia. cbn. apply andb_true_r.
    + rewrite Z.ones_spec_high by lia. cbn.
      replace (Z.testbit x i) with false; [reflexivity|]. symmetry.
      destruct (Z.eq_dec x 0) as [->|Hx0]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia| lia].
Qed.

Section BICREATE.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (mv : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (bi AL lo : Z).
  Hypothesis HC : mmap_consts mv.
  Hypothesis MI0 : mem_inv bsegs mv.
  Hypothesis ST0 : stk bsegs mv lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + 352 <= bv_unsigned sp.
  Hypothesis HBI : 0x17b898 <= bi /\ bi + 16 <= 0x18b898 /\ bi mod 8 = 0.
  Hypothesis HAL : 0 <= AL /\ AL + 0x800000 < 2^64.
  Hypothesis DATA0 : rw_cells bsegs mv bi [C8 (Z_to_bv 64 0)].
  Hypothesis MTX0 : rw_cells bsegs mv (bi + 12) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Hypothesis ALC0 : rw_cells bsegs mv 0x17b890 [C8 (Z_to_bv 64 AL)].

  Lemma bi_create_spec : forall (P : machine_state -> Model -> lghost -> Prop),
    8388608 <= R -> mmap_placeable mo 8388608 ->
    (forall (a : word) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte),
       mmap_grant mo a 8388608 ->
       mem_inv bsegs m' ->
       munch [(lo, bv_unsigned sp); (bv_unsigned a, bv_unsigned a + 8388608); (bi, bi + 8); (bi + 12, bi + 16); (0x17b890, 0x17b898)] mv m' ->
       wmono bsegs mv m' -> stk bsegs m' lo (bv_unsigned sp) ->
       rw_cells bsegs m' (bv_unsigned a) [CB (Z.to_nat 8388608) (repeat (Z_to_bv 8 0) (Z.to_nat 8388608))] ->
       rw_cells bsegs m' bi [C8 a] ->
       rw_cells bsegs m' (bi + 12) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
       rw_cells bsegs m' 0x17b890 [C8 (Z_to_bv 64 (AL + 8388608))] ->
       AIMG_HI <= bv_unsigned a -> bv_unsigned a + 8388608 <= alloc_ceiling -> bv_unsigned a mod 4096 = 0 ->
       LSCPS bsegs P (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (ret_pc ra) fc None m' (seg_rom bsegs)) (mm_add_lazy a (Z_to_bv 64 8388608) mo)
             (mkG ((bv_unsigned a, bv_unsigned a + 8388608) :: G) (R - 8388608))) ->
    LSCPS bsegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 bi) (Z_to_bv 64 0x17b888) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x728b4) fc None mv (seg_rom bsegs)) mo (mkG G R).
  Proof.
    intros P HRR HPL K.
    pose proof HC as HC0. clear HC.
    pose proof MI0 as MI. pose proof ST0 as ST. clear ST0. pose proof MTX0 as MTX. pose proof DATA0 as DATA. pose proof ALC0 as ALC. clear MTX0 DATA0 ALC0.
    pose proof (munch_refl [(lo, bv_unsigned sp); (bi, bi + 8); (bi + 12, bi + 16); (0x17b890, 0x17b898)] mv) as MU. pose proof (wmono_refl bsegs mv) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
    destruct (ex_intro (fun q => q = bi + 12) _ eq_refl) as [q Hq]. rewrite <- Hq in MTX, MU.
    assert (ALQ : q mod 4 = 0) by lia. assert (PRQ : 0 <= q < 2^64) by lia.
    apply lscps_assume. intros NWX HOK HBINV.
    apply lscps_step_evt.
    carve_frame 32%nat ST.
    do 5 lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    setreg 8 (Z_to_bv 64 q) ltac:(f_equal; lia).
    lstep. lstep. (* [comment removed for export] *)
    setreg 12 (Z_to_bv 64 q) ltac:(f_equal; symmetry; apply land_align4; lia).
    lstep. (* [comment removed for export] *)
    apply w4_of_bytes0 in MTX.
    amo_zstep. fl. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *)
    amo_zstep2. fix_lit_store. fl. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    lstep. fl. lstep. if_lia. (* [comment removed for export] *)
    lstep. fl. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    lstep. fl. lstep. fl. (* [comment removed for export] *)
    amo_step. fix_lit_store. fl. (* [comment removed for export] *)
    replace (amo_val AMO_ADD (Z_to_bv 64 AL) (Z_to_bv 64 8388608)) with (Z_to_bv 64 (AL + 8388608) : word) in ALC
      by (cbn [amo_val]; rewrite lit_add_lit; reflexivity).
    lstep. lstep. fl. lstep. fl. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    assert (E32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp - 32) by (rewrite unsigned_lit by lia; lia).
    apply evt_done. eapply mmapnoreserve_open_spec with (lo := lo).
    { eapply (mmap_consts_munch _ mv _ HC0 MU); cbn; lia. }
    { exact MI. }
    { rewrite E32. exact ST. }
    { rewrite E32. lia. }
    { cbn; lia. } { lia. } { lia. } { exact HPL. }
    intros a x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m' GR MI' MU' WM' ST' ZNEW.
    rewrite E32 in MU', ST'.
    pose proof GR as (GA & GP & GC & GF). idtac. rewrite page_size_eq in GA.
    pose proof (grant_above_image mo a 8388608 HOK GR ltac:(lia)) as GI. unfold AIMG_HI in GI.
    pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. cbn in RA.
    eapply rw_cells_transport in FR; [| exact MU'| exact WM'| cbn; lia].
    eapply rw_cells_transport in MTX; [| exact MU'| exact WM'| cbn; lia].
    eapply rw_cells_transport in DATA; [| exact MU'| exact WM'| cbn; lia].
    eapply rw_cells_transport in ALC; [| exact MU'| exact WM'| cbn; lia].
    apply (munch_weaken _ [(lo, bv_unsigned sp); (bv_unsigned a, bv_unsigned a + 8388608); (bi, bi + 8); (q, q + 4); (0x17b890, 0x17b898)]) in MU. 2:{ unfold sub_fp; cbn; intros; lia. }
    apply (munch_weaken _ [(lo, bv_unsigned sp); (bv_unsigned a, bv_unsigned a + 8388608); (bi, bi + 8); (q, q + 4); (0x17b890, 0x17b898)]) in MU'. 2:{ unfold sub_fp; cbn; intros; lia. }
    pose proof (munch_trans _ _ _ _ MU MU') as MU2. pose proof (wmono_trans bsegs _ _ _ WM WM') as WM2.
    clear MU MU' WM WM' MI ST. rename MU2 into MU. rename WM2 into WM. rename MI' into MI. rename ST' into ST.
    apply lscps_step_evt.
    replace (ret_pc (Z_to_bv 64 469284)) with (Z_to_bv 64 469284 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    apply bytes_of_w4_1 in MTX. lstep. (* [comment removed for export] *)
    do 4 lstep. lstep. lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    replace (q + 4) with (bi + 16) in MU by lia. rewrite Hq in MU, MTX.
    apply evt_done. eapply K; [exact GR| exact MI| exact MU| exact WM| exact ST| exact ZNEW| exact DATA| exact MTX| exact ALC| unfold AIMG_HI; lia| idtac; lia| exact GA].
  Qed.
End BICREATE.


End CeilWrap.
End RTW_depot_create.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module RTW_depot_alloc.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_depot_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_lock OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_depot_n2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap RTW_depot_create.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition ssrep (m : word -> option byte) (T : Z) (sbl : list Z) : Prop :=
  rw_cells bsegs m 0x17b888 [C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 (8388608 * zlen sbl))]
  /\ (forall b, 0 <= b < 4096 -> exists sj : word,
        rw_cells bsegs m (0x17b898 + 16 * b) [C8 (Z_to_bv 64 (nthz sbl b 0)); C4 sj; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)])
  /\ (forall b, In b sbl -> stk bsegs m b (b + 8388608)).
Definition sswf (T : Z) (sbl : list Z) : Prop :=
  1 <= T /\ zlen sbl = (T - 1) / 1048576 + 1
  /\ (forall b, In b sbl -> 0x5ff000 <= b /\ b + 8388608 <= alloc_ceiling /\ b mod 4096 = 0).
(* [comment removed for export] *)
Definition ssfp (T : Z) (nb : list (Z * Z)) : list (Z * Z) :=
  (0x17b888, 0x17b898) :: (0x17b898 + 16 * (T / 1048576), 0x17b898 + 16 * (T / 1048576) + 32) :: nb.

Lemma disjoint_from_blocks : forall sbl a sz, (forall b, In b sbl -> a + sz <= b \/ b + 8388608 <= a) ->
  disjoint_from (map (fun b => (b, b + 8388608)) sbl) a sz.
Proof.
  induction sbl as [|b sbl IH]; intros a sz H; [exact I|]. cbn [map disjoint_from]. split.
  - destruct (H b ltac:(left; reflexivity)); lia.
  - apply IH. intros b' Hb'. apply H. right. exact Hb'.
Qed.

(* [comment removed for export] *)
Lemma ssrep_blocks_other : forall W m m' sbl B0 q,
  (forall b, 0 <= b < 4096 -> exists sj : word,
        rw_cells bsegs m (0x17b898 + 16 * b) [C8 (Z_to_bv 64 (nthz sbl b 0)); C4 sj; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) ->
  munch W m m' -> wmono bsegs m m' ->
  q = 0x17b888 + 16 * B0 ->
  (forall a sz, a + sz <= q + 16 \/ q + 48 <= a -> 0x17b898 <= a -> a + sz <= 0x18b898 -> disjoint_from W a sz) ->
  forall b, 0 <= b < 4096 -> b <> B0 -> b <> B0 + 1 -> exists sj : word,
        rw_cells bsegs m' (0x17b898 + 16 * b) [C8 (Z_to_bv 64 (nthz sbl b 0)); C4 sj; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
  intros W m m' sbl B0 q BL MU WM Hq HD b Hb N0 N1. destruct (BL b Hb) as (sj & H). exists sj.
  eapply rw_cells_transport; [exact H| exact MU| exact WM|]. apply HD; cbn; lia.
Qed.

Lemma nthz_app_l : forall (l1 l2 : list Z) i d, 0 <= i < zlen l1 -> nthz (l1 ++ l2) i d = nthz l1 i d.
Proof. intros l1 l2 i d Hi. unfold nthz, zlen in *. destruct (Z.ltb_spec0 i 0); [lia|]. rewrite app_nth1 by lia. reflexivity. Qed.
Lemma nthz_app_r1 : forall (l1 : list Z) x d, nthz (l1 ++ [x]) (zlen l1) d = x.
Proof. intros l1 x d. unfold nthz, zlen. destruct (Z.ltb_spec0 (Z.of_nat (length l1)) 0); [lia|]. rewrite Nat2Z.id, app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.
Lemma nthz_over : forall (l : list Z) i d, zlen l <= i -> nthz l i d = d.
Proof. intros l i d Hi. unfold nthz, zlen in *. destruct (Z.ltb_spec0 i 0); [reflexivity|]. apply nth_overflow. lia. Qed.
Lemma zlen_app1 : forall (l : list Z) x, zlen (l ++ [x]) = zlen l + 1.
Proof. intros. unfold zlen. rewrite length_app. cbn [length]. lia. Qed.

Ltac fixaddr v := match goal with |- rw_cells _ _ ?a _ => replace a with v by (cbn; lia) end.

(* [comment removed for export] *)
Lemma le4_of_u32 : forall jv : bv 32, Z_to_le_bytes 4 (bv_unsigned jv) = le4 (Z_to_bv 64 (bv_unsigned jv)).
Proof.
  intros jv. unfold le4. rewrite unsigned_lit; [reflexivity|].
  pose proof (bv_unsigned_in_range 32 jv) as RR. unfold bv_modulus in RR. cbn in RR. lia.
Qed.
Ltac amo_w_junk :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 (bv_unsigned ?jv))) _) =>
      rewrite (le4_of_u32 jv);
      let w := fresh "jw" in set (w := (Z_to_bv 64 (bv_unsigned jv) : word)) in *; clearbody w;
      mem_after_store
  end.

Section ALLOC.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (mv : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (T c IDX PK lo : Z) (sbl : list Z) (ij pk : word).
  Hypothesis HC : mmap_consts mv.
  Hypothesis MI0 : mem_inv bsegs mv.
  Hypothesis ST0 : stk bsegs mv lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + 368 <= bv_unsigned sp.
  Hypothesis SSR : ssrep mv T sbl.
  Hypothesis SSW : sswf T sbl.
  Hypothesis Hc : 1 <= c <= 256.
  Hypothesis HT : T + 2 * c < 2^32.
  Hypothesis HSB : zlen sbl < 4095.
  Hypothesis HIDX : bv_unsigned sp <= IDX /\ IDX + 8 < 2^64.
  Hypothesis HPK : bv_unsigned sp <= PK /\ PK + 8 < 2^64.
  Hypothesis HIP : IDX + 8 <= PK \/ PK + 8 <= IDX.
  Hypothesis IDXC : rw_cells bsegs mv IDX [C8 ij].
  Hypothesis PKC : rw_cells bsegs mv PK [C8 pk].
  (* [comment removed for export] *)
  Hypothesis HFS : forall a : word, mmap_grant mo a 8388608 -> 0x5ff000 <= bv_unsigned a.

  Lemma alloc_spec : forall (P : machine_state -> Model -> lghost -> Prop),
    8388608 <= R -> mmap_placeable mo 8388608 ->
    (forall (start : Z) (sbl' : list Z) (nb : list (Z * Z)) (m' : word -> option byte) (mo' : Model) (G' : list (Z * Z)) (R' : Z) (pk' : word)
            (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
       (start = T \/ (start = T + c /\ T mod 1048576 + c > 1048576)) -> start mod 1048576 + c <= 1048576 ->
       ssrep m' (start + c) sbl' -> sswf (start + c) sbl' -> start / 1048576 < zlen sbl' ->
       ((sbl' = sbl /\ nb = [] /\ mo' = mo /\ G' = G /\ R' = R)
        \/ (exists a : word, sbl' = sbl ++ [bv_unsigned a] /\ nb = [(bv_unsigned a, bv_unsigned a + 8388608)]
                             /\ mmap_grant mo a 8388608
                             /\ mo' = mm_add_lazy a (Z_to_bv 64 8388608) mo /\ G' = (bv_unsigned a, bv_unsigned a + 8388608) :: G /\ R' = R - 8388608
                             /\ rw_cells bsegs m' (bv_unsigned a) [CB (Z.to_nat 8388608) (repeat (Z_to_bv 8 0) (Z.to_nat 8388608))])) ->
       rw_cells bsegs m' IDX [C8 (Z_to_bv 64 start)] -> rw_cells bsegs m' PK [C8 pk'] ->
       mem_inv bsegs m' -> munch ((lo, bv_unsigned sp) :: (IDX, IDX + 8) :: (PK, PK + 8) :: ssfp T nb) mv m' -> wmono bsegs mv m' ->
       stk bsegs m' lo (bv_unsigned sp) ->
       LSCPS bsegs P (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 (nthz sbl' (start / 1048576) 0 + 8 * (start mod 1048576))) x11 x12 x13 x14 x15 x16 x17
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (ret_pc ra) fc None m' (seg_rom bsegs)) mo' (mkG G' R')) ->
    LSCPS bsegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x17b888) (Z_to_bv 64 c) (Z_to_bv 64 IDX) (Z_to_bv 64 PK) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x71ecc) fc None mv (seg_rom bsegs)) mo (mkG G R).
  Proof.
    intros P HRR HPL K.
    pose proof HC as HC0.
    pose proof MI0 as MI. pose proof ST0 as ST. clear ST0. pose proof IDXC as IDXW. pose proof PKC as PKW. clear IDXC PKC.
    (nelimp SSR 3%nat; intros TOT BLKS VIS). (nelimp SSW 3%nat; intros T1 LENS BR).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
    set (B0 := T / 1048576).
    assert (HB0 : 0 <= B0 /\ B0 <= zlen sbl) by (subst B0; Z.div_mod_to_equations; nia).
    destruct (ex_intro (fun q => q = 1554568 + 16 * B0) _ eq_refl) as [q Hq].
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (IDX, IDX + 8) :: (PK, PK + 8) :: ssfp T []) mv) as MU. pose proof (wmono_refl bsegs mv) as WM.
    unfold ssfp in MU. fold B0 in MU. replace (1554584 + 16 * B0) with (q + 16) in MU by lia.
    Local Ltac dj BR := cbn [disjoint_from]; repeat (split; [lia|]); first [exact I | apply disjoint_from_blocks; intros b' Hb'; destruct (BR b' Hb'); lia].
    destruct (BLKS B0 ltac:(lia)) as (sj0 & BE0). replace (1554584 + 16 * B0) with (q + 16) in BE0 by lia.
    destruct (BLKS (B0 + 1) ltac:(lia)) as (sj1 & BE1). replace (1554584 + 16 * (B0 + 1)) with (q + 32) in BE1 by lia.
    apply lscps_assume. intros NWX HOK HBINV.
    apply lscps_step_evt.
    carve_frame 16%nat ST.
    do 3 lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    amo_step. fix_lit_store. fl. (* [comment removed for export] *)
    replace (amo_val AMO_ADD (Z_to_bv 64 T) (Z_to_bv 64 c)) with (Z_to_bv 64 (T + c) : word) in TOT by (cbn [amo_val]; rewrite lit_add_lit; reflexivity).
    lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *)
    rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 20) with 1048576.
    replace (T / 1048576) with B0 by reflexivity.
    destruct (Z_le_gt_dec (T mod 1048576 + c) 1048576) as [NSTR|STR].
    - (* [comment removed for export] *)
      replace ((c + -1 + T) / 1048576) with B0 by (subst B0; Z.div_mod_to_equations; nia).
      lstep. if_lia. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296. rewrite (Z.div_small T 4294967296) by lia.
      lstep. if_lia. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      lstep. lstep. fl. (* [comment removed for export] *)
      setreg 12 (Z_to_bv 64 q) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
      lstep. (* [comment removed for export] *)
      destruct (Z.eq_dec (T mod 1048576) 0) as [TZ|TNZ].
      + (* [comment removed for export] *)
        assert (EB0 : B0 = zlen sbl) by (subst B0; rewrite LENS; Z.div_mod_to_equations; nia).
        rewrite (nthz_over sbl B0 0) in BE0 |- * by lia.
        lstep. if_lia. (* [comment removed for export] *)
        lstep. (* [comment removed for export] *)
        lstep. (* [comment removed for export] *)
        assert (E16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp - 16) by (rewrite unsigned_lit by lia; lia).
        apply evt_done. eapply bi_create_spec with (lo := lo) (AL := 8388608 * zlen sbl).
        { eapply (mmap_consts_munch _ mv _ HC0 MU); cbn [disjoint_from]; lia. }
        { exact MI. }
        { rewrite E16. exact ST. }
        { rewrite E16. lia. }
        { subst q. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }
        { eapply (rw_cells_take _ _ [_] [_; _; _; _; _]). exact BE0. }
        { replace (q + 16 + 12) with (q + 16 + Z.of_nat (cells_size [C8 (Z_to_bv 64 0); C4 sj0])) by (cbn; lia).
          eapply (rw_cells_drop _ _ [_; _] [_; _; _; _]). exact BE0. }
        { replace 1554576 with (1554568 + Z.of_nat (cells_size [C8 (Z_to_bv 64 (T + c))])) by (cbn; lia).
          eapply (rw_cells_drop _ _ [_] [_]). exact TOT. }
        { lia. } { exact HPL. }
        intros a x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m' GR MI' MU' WM' ST' ZNEW DATA MTX ALC GI GC GA.
        rewrite E16 in MU', ST'. idtac. unfold AIMG_HI in GI.
        pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. cbn in RA.
        (* [comment removed for export] *)
        eapply rw_cells_transport in FR; [| exact MU'| exact WM'| cbn; lia].
        eapply rw_cells_transport in IDXW; [| exact MU'| exact WM'| cbn; lia].
        eapply rw_cells_transport in PKW; [| exact MU'| exact WM'| cbn; lia].
        eapply rw_cells_transport in BE1; [| exact MU'| exact WM'| cbn; lia].
        assert (TOT1 : rw_cells bsegs m' 1554568 [C8 (Z_to_bv 64 (T + c))]).
        { eapply rw_cells_transport; [eapply (rw_cells_take _ _ [_] [_]); exact TOT| exact MU'| exact WM'| cbn; lia]. }
        assert (SJ : exists sj : word, rw_cells bsegs m' (q + 16 + 8) [C4 sj]).
        { exists sj0. eapply rw_cells_transport; [| exact MU'| exact WM'| cbn; lia].
          replace (q + 16 + 8) with (q + 16 + Z.of_nat (cells_size [C8 (Z_to_bv 64 0)])) by (cbn; lia).
          eapply (rw_cells_mid _ _ [_] [_] [_; _; _; _]). exact BE0. }
        clear BE0 TOT. destruct SJ as (sj0' & SJ0).
        assert (BE0 : rw_cells bsegs m' (q + 16) [C8 a; C4 sj0'; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
        { apply (rw_cells_app _ _ [_] [_; _; _; _; _]). split; [exact DATA|]. fixaddr (q + 16 + 8).
          apply (rw_cells_app _ _ [_] [_; _; _; _]). split; [exact SJ0|]. fixaddr (q + 16 + 12). exact MTX. }
        clear DATA SJ0 MTX.
        assert (TOT : rw_cells bsegs m' 1554568 [C8 (Z_to_bv 64 (T + c)); C8 (Z_to_bv 64 (8388608 * zlen (sbl ++ [bv_unsigned a])))]).
        { apply (rw_cells_app _ _ [_] [_]). split; [exact TOT1|]. fixaddr 1554576.
          rewrite zlen_app1. replace (8388608 * (zlen sbl + 1)) with (8388608 * zlen sbl + 8388608) by lia. exact ALC. }
        clear TOT1 ALC.
        apply (munch_weaken _ [(lo, bv_unsigned sp); (IDX, IDX + 8); (PK, PK + 8); (1554568, 1554584); (q + 16, q + 16 + 32); (bv_unsigned a, bv_unsigned a + 8388608)]) in MU.
        2:{ unfold sub_fp; cbn; intros; lia. }
        apply (munch_weaken _ [(lo, bv_unsigned sp); (IDX, IDX + 8); (PK, PK + 8); (1554568, 1554584); (q + 16, q + 16 + 32); (bv_unsigned a, bv_unsigned a + 8388608)]) in MU'.
        2:{ unfold sub_fp; cbn; intros; lia. }
        pose proof (munch_trans _ _ _ _ MU MU') as MU2. pose proof (wmono_trans bsegs _ _ _ WM WM') as WM2.
        clear MU MU' WM' MI ST. rename MU2 into MU. rename MI' into MI. rename ST' into ST.
        apply lscps_step_evt.
        replace (ret_pc (Z_to_bv 64 466912)) with (Z_to_bv 64 466912 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        lstep. (* [comment removed for export] *)
        lstep. lstep. (* [comment removed for export] *)
        setreg 8 (Z_to_bv 64 (8 * (T mod 1048576)))
          ltac:(f_equal; rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia; change (2^44) with 17592186044416; change (2^41) with 2199023255552;
                Z.div_mod_to_equations; lia).
        lstep. (* [comment removed for export] *)
        setreg 10 (Z_to_bv 64 (nthz (sbl ++ [bv_unsigned a]) (T / 1048576) 0 + 8 * (T mod 1048576)))
          ltac:(f_equal; change (T / 1048576) with B0; rewrite EB0, nthz_app_r1; reflexivity).
        lstep. lstep. lstep. (* [comment removed for export] *)
        lstep. (* [comment removed for export] *)
        release_frame FR ST (bv_unsigned sp).
        apply evt_done. eapply (K T (sbl ++ [bv_unsigned a]) [(bv_unsigned a, bv_unsigned a + 8388608)]);
          [lia| lia| | | rewrite zlen_app1; lia| | exact IDXW| exact PKW| exact MI| | exact WM2| exact ST].
        { split; [exact TOT| split].
          - intros b Hb. destruct (Z.eq_dec b B0) as [->|N0].
            { exists sj0'. replace (1554584 + 16 * B0) with (q + 16) by lia. rewrite EB0, nthz_app_r1.
              rewrite <- (Z_to_bv_bv_unsigned a) in BE0 at 1. exact BE0. }
            destruct (Z.eq_dec b (B0 + 1)) as [->|N1].
            { exists sj1. replace (1554584 + 16 * (B0 + 1)) with (q + 32) by lia. rewrite (nthz_over (sbl ++ _)) by (rewrite zlen_app1; lia).
              rewrite nthz_over in BE1 by lia. exact BE1. }
            assert (EN : nthz (sbl ++ [bv_unsigned a]) b 0 = nthz sbl b 0).
            { destruct (Z_lt_le_dec b (zlen sbl)); [apply nthz_app_l; lia| rewrite !nthz_over by (rewrite ?zlen_app1; lia); reflexivity]. }
            rewrite EN. eapply (ssrep_blocks_other _ mv _ sbl B0 q BLKS MU); [exact WM2| exact Hq| | lia| exact N0| exact N1].
            intros a' sz' Y1 Y2 Y3. cbn [disjoint_from]. lia.
          - intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|[<-|[]]].
            + (nelim (BR b Hb) 3%nat; intros R1 R2 R3). eapply stk_wmono_noseg; [exact (VIS b Hb)| exact WM2| unfold AIMG_HI; lia].
            + pose proof (stk_of_rw_cells bsegs m' _ _ ZNEW) as V.
              match type of V with stk _ _ _ ?h => replace h with (bv_unsigned a + 8388608) in V by (cbn -[Z.add Z.of_nat Z.to_nat]; rewrite ?Z2Nat.id by lia; cbn; lia) end. exact V. }
        { split; [lia|]. split; [rewrite zlen_app1, LENS; Z.div_mod_to_equations; nia|].
          intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|[<-|[]]]; [exact (BR b Hb)|]. pose proof (HFS a GR). lia. }
        { right. exists a. repeat (split; [first [reflexivity| assumption]|]). exact ZNEW. }
        { unfold ssfp. fold B0. replace (1554584 + 16 * B0) with (q + 16) by lia. exact MU. }
      + (* [comment removed for export] *)
        assert (EB0 : B0 = zlen sbl - 1) by (subst B0; rewrite LENS; Z.div_mod_to_equations; nia).
        assert (INB : In (nthz sbl B0 0) sbl) by (apply nthz_In; lia).
        (nelim (BR _ INB) 3%nat; intros D1 D2 D3).
        lstep. if_lia. (* [comment removed for export] *)
        lstep. lstep. (* [comment removed for export] *)
        setreg 8 (Z_to_bv 64 (8 * (T mod 1048576)))
          ltac:(f_equal; rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia; change (2^44) with 17592186044416; change (2^41) with 2199023255552;
                Z.div_mod_to_equations; lia).
        lstep. fl. (* [comment removed for export] *)
        lstep. lstep. lstep. (* [comment removed for export] *)
        lstep. (* [comment removed for export] *)
        release_frame FR ST (bv_unsigned sp).
        apply evt_done. eapply (K T sbl []); [lia| lia| | | lia| left; repeat split; reflexivity| exact IDXW| exact PKW| exact MI| | exact WM| exact ST].
        { split; [exact TOT| split].
          - intros b Hb. destruct (Z.eq_dec b B0) as [->|N0]; [exists sj0; replace (1554584 + 16 * B0) with (q + 16) by lia; exact BE0|].
            destruct (Z.eq_dec b (B0 + 1)) as [->|N1]; [exists sj1; replace (1554584 + 16 * (B0 + 1)) with (q + 32) by lia; exact BE1|].
            eapply (ssrep_blocks_other _ mv _ sbl B0 q BLKS MU WM Hq); [| lia| exact N0| exact N1].
            intros a' sz' Y1 Y2 Y3. cbn [disjoint_from]. lia.
          - intros b Hb. (nelim (BR b Hb) 3%nat; intros R1 R2 R3). eapply stk_wmono_noseg; [exact (VIS b Hb)| exact WM| unfold AIMG_HI; lia]. }
        { split; [lia|]. split; [|exact BR]. rewrite LENS. Z.div_mod_to_equations. nia. }
        { unfold ssfp. fold B0. replace (1554584 + 16 * B0) with (q + 16) by lia. exact MU. }
    - (* [comment removed for export] *)
      assert (EB1 : (c + -1 + T) / 1048576 = B0 + 1) by (subst B0; Z.div_mod_to_equations; nia).
      rewrite EB1.
      assert (TNZ : T mod 1048576 <> 0) by lia.
      assert (EB0 : B0 = zlen sbl - 1) by (subst B0; rewrite LENS; Z.div_mod_to_equations; nia).
      assert (ALq24 : (q + 24) mod 4 = 0) by (subst q; Z.div_mod_to_equations; lia).
      assert (ALq40 : (q + 40) mod 4 = 0) by (subst q; Z.div_mod_to_equations; lia).
      assert (PRq : 0 <= q /\ q + 48 < 2^64) by lia.
      lstep. if_lia. (* [comment removed for export] *)
      lstep. lstep. if_lia. (* [comment removed for export] *)
      lstep. fl. lstep. fl. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      setreg 7 (Z_to_bv 64 (T mod 1048576)) ltac:(f_equal; change 1048575 with (Z.ones 20); rewrite Z.land_ones by lia; reflexivity).
      lstep. lstep. lstep. lstep. (* [comment removed for export] *)
      setreg 5 (Z_to_bv 64 (q + 24)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
      set (inf := 1048576 - T mod 1048576) in *.
      amo_zstep2. amo_w_junk. fl. (* [comment removed for export] *)
      lstep. lstep. (* [comment removed for export] *)
      setreg 6 (Z_to_bv 64 (q + 32)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
      lstep. (* [comment removed for export] *)
      lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      amo_zstep2. amo_w_junk. fl. (* [comment removed for export] *)
      lstep. lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      amo_step. fix_lit_store. fl. (* [comment removed for export] *)
      replace (amo_val AMO_ADD (Z_to_bv 64 (T + c)) (Z_to_bv 64 c)) with (Z_to_bv 64 (T + c + c) : word) in TOT by (cbn [amo_val]; rewrite lit_add_lit; reflexivity).
      lstep. lstep. lstep. (* [comment removed for export] *)
      rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 20) with 1048576.
      replace ((T + c) / 1048576) with (B0 + 1) by (subst B0 inf; Z.div_mod_to_equations; nia).
      replace ((c + -1 + (T + c)) / 1048576) with (B0 + 1) by (subst B0 inf; Z.div_mod_to_equations; nia).
      lstep. if_lia. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296. rewrite (Z.div_small (T + c) 4294967296) by lia.
      lstep. if_lia. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      lstep. lstep. fl. (* [comment removed for export] *)
      setreg 12 (Z_to_bv 64 (q + 16)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
      rewrite (nthz_over sbl (B0 + 1) 0) in BE1 by lia.
      lstep. (* [comment removed for export] *)
      lstep. if_lia. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      assert (E16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp - 16) by (rewrite unsigned_lit by lia; lia).
      lazymatch goal with H : rw_cells _ _ (q + 32) [C8 _; C4 ?w; _; _; _; _] |- _ => rename w into sjB end.
      lazymatch goal with H : rw_cells _ _ (q + 16) [C8 _; C4 ?w; _; _; _; _] |- _ => rename w into sjA end.
      apply evt_done. eapply bi_create_spec with (lo := lo) (AL := 8388608 * zlen sbl).
      { eapply (mmap_consts_munch _ mv _ HC0 MU); cbn [disjoint_from]; lia. }
      { exact MI. }
      { rewrite E16. exact ST. }
      { rewrite E16. lia. }
      { subst q. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }
      { eapply (rw_cells_take _ _ [_] [_; _; _; _; _]). exact BE1. }
      { replace (q + 32 + 12) with (q + 32 + Z.of_nat (cells_size [C8 (Z_to_bv 64 0); C4 sjB])) by (cbn; lia).
        eapply (rw_cells_drop _ _ [_; _] [_; _; _; _]). exact BE1. }
      { replace 1554576 with (1554568 + Z.of_nat (cells_size [C8 (Z_to_bv 64 (T + c + c))])) by (cbn; lia).
        eapply (rw_cells_drop _ _ [_] [_]). exact TOT. }
      { lia. } { exact HPL. }
      intros a x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m' GR MI' MU' WM' ST' ZNEW DATA MTX ALC GI GC GA.
      rewrite E16 in MU', ST'. idtac. unfold AIMG_HI in GI.
      pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. cbn in RA.
      eapply rw_cells_transport in FR; [| exact MU'| exact WM'| cbn; lia].
      eapply rw_cells_transport in IDXW; [| exact MU'| exact WM'| cbn; lia].
      eapply rw_cells_transport in PKW; [| exact MU'| exact WM'| cbn; lia].
      eapply rw_cells_transport in BE0; [| exact MU'| exact WM'| cbn; lia].
      assert (TOT1 : rw_cells bsegs m' 1554568 [C8 (Z_to_bv 64 (T + c + c))]).
      { eapply rw_cells_transport; [eapply (rw_cells_take _ _ [_] [_]); exact TOT| exact MU'| exact WM'| cbn; lia]. }
      assert (SJ : exists sj : word, rw_cells bsegs m' (q + 32 + 8) [C4 sj]).
      { exists sjB. eapply rw_cells_transport; [| exact MU'| exact WM'| cbn; lia].
        replace (q + 32 + 8) with (q + 32 + Z.of_nat (cells_size [C8 (Z_to_bv 64 0)])) by (cbn; lia).
        eapply (rw_cells_mid _ _ [_] [_] [_; _; _; _]). exact BE1. }
      clear BE1 TOT. destruct SJ as (sjB' & SJB).
      assert (BE1 : rw_cells bsegs m' (q + 32) [C8 a; C4 sjB'; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
      { apply (rw_cells_app _ _ [_] [_; _; _; _; _]). split; [exact DATA|]. fixaddr (q + 32 + 8).
        apply (rw_cells_app _ _ [_] [_; _; _; _]). split; [exact SJB|]. fixaddr (q + 32 + 12). exact MTX. }
      clear DATA SJB MTX.
      assert (TOT : rw_cells bsegs m' 1554568 [C8 (Z_to_bv 64 (T + c + c)); C8 (Z_to_bv 64 (8388608 * zlen (sbl ++ [bv_unsigned a])))]).
      { apply (rw_cells_app _ _ [_] [_]). split; [exact TOT1|]. fixaddr 1554576.
        rewrite zlen_app1. replace (8388608 * (zlen sbl + 1)) with (8388608 * zlen sbl + 8388608) by lia. exact ALC. }
      clear TOT1 ALC.
      apply (munch_weaken _ [(lo, bv_unsigned sp); (IDX, IDX + 8); (PK, PK + 8); (1554568, 1554584); (q + 16, q + 16 + 32); (bv_unsigned a, bv_unsigned a + 8388608)]) in MU.
      2:{ unfold sub_fp; cbn; intros; lia. }
      apply (munch_weaken _ [(lo, bv_unsigned sp); (IDX, IDX + 8); (PK, PK + 8); (1554568, 1554584); (q + 16, q + 16 + 32); (bv_unsigned a, bv_unsigned a + 8388608)]) in MU'.
      2:{ unfold sub_fp; cbn; intros; lia. }
      pose proof (munch_trans _ _ _ _ MU MU') as MU2. pose proof (wmono_trans bsegs _ _ _ WM WM') as WM2.
      clear MU MU' WM' MI ST. rename MU2 into MU. rename MI' into MI. rename ST' into ST.
      apply lscps_step_evt.
      replace (ret_pc (Z_to_bv 64 466912)) with (Z_to_bv 64 466912 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      lstep. (* [comment removed for export] *)
      lstep. lstep. (* [comment removed for export] *)
      setreg 8 (Z_to_bv 64 (8 * ((T + c) mod 1048576)))
        ltac:(f_equal; rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia; change (2^44) with 17592186044416; change (2^41) with 2199023255552;
              Z.div_mod_to_equations; lia).
      lstep. (* [comment removed for export] *)
      setreg 10 (Z_to_bv 64 (nthz (sbl ++ [bv_unsigned a]) ((T + c) / 1048576) 0 + 8 * ((T + c) mod 1048576)))
        ltac:(f_equal; replace ((T + c) / 1048576) with (zlen sbl) by (subst inf; rewrite LENS; Z.div_mod_to_equations; nia); rewrite nthz_app_r1; reflexivity).
      lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. eapply (K (T + c) (sbl ++ [bv_unsigned a]) [(bv_unsigned a, bv_unsigned a + 8388608)]);
        [lia| subst inf; Z.div_mod_to_equations; lia| | | rewrite zlen_app1; subst inf; Z.div_mod_to_equations; nia| | exact IDXW| exact PKW| exact MI| | exact WM2| exact ST].
      { split; [exact TOT| split].
        - intros b Hb. destruct (Z.eq_dec b B0) as [->|N0].
          { exists sjA. replace (1554584 + 16 * B0) with (q + 16) by lia. rewrite nthz_app_l by lia. exact BE0. }
          destruct (Z.eq_dec b (B0 + 1)) as [->|N1].
          { exists sjB'. replace (1554584 + 16 * (B0 + 1)) with (q + 32) by lia. replace (B0 + 1) with (zlen sbl) by lia. rewrite nthz_app_r1.
            rewrite <- (Z_to_bv_bv_unsigned a) in BE1 at 1. exact BE1. }
          assert (EN : nthz (sbl ++ [bv_unsigned a]) b 0 = nthz sbl b 0).
          { destruct (Z_lt_le_dec b (zlen sbl)); [apply nthz_app_l; lia| rewrite !nthz_over by (rewrite ?zlen_app1; lia); reflexivity]. }
          rewrite EN. eapply (ssrep_blocks_other _ mv _ sbl B0 q BLKS MU); [exact WM2| exact Hq| | lia| exact N0| exact N1].
          intros a' sz' Y1 Y2 Y3. cbn [disjoint_from]. lia.
        - intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|[<-|[]]].
          + (nelim (BR b Hb) 3%nat; intros R1 R2 R3). eapply stk_wmono_noseg; [exact (VIS b Hb)| exact WM2| unfold AIMG_HI; lia].
          + pose proof (stk_of_rw_cells bsegs m' _ _ ZNEW) as V.
            match type of V with stk _ _ _ ?h => replace h with (bv_unsigned a + 8388608) in V by (cbn -[Z.add Z.of_nat Z.to_nat]; rewrite ?Z2Nat.id by lia; cbn; lia) end. exact V. }
      { split; [lia|]. split; [rewrite zlen_app1, LENS; subst inf; Z.div_mod_to_equations; nia|].
        intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|[<-|[]]]; [exact (BR b Hb)|]. pose proof (HFS a GR). lia. }
      { right. exists a. repeat (split; [first [reflexivity| assumption]|]). exact ZNEW. }
      { unfold ssfp. fold B0. replace (1554584 + 16 * B0) with (q + 16) by lia. exact MU. }
  Qed.
End ALLOC.


End CeilWrap.
(* [comment removed for export] *)
Ltac fixaddr v := match goal with |- rw_cells _ _ ?a _ => replace a with v by (cbn; lia) end.
Ltac amo_w_junk :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 (bv_unsigned ?jv))) _) =>
      rewrite (le4_of_u32 jv);
      let w := fresh "jw" in set (w := (Z_to_bv 64 (bv_unsigned jv) : word)) in *; clearbody w;
      mem_after_store
  end.
End RTW_depot_alloc.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module RTW_depot_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.InitMem.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_depot_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_lock OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_depot_n2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap RTW_depot_create OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_memcpy RTW_depot_alloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_hash.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma u8arr_of_stk : forall m lo hi, stk bsegs m lo hi -> lo <= hi ->
  exists bs, length bs = Z.to_nat (hi - lo) /\ u8arr bsegs m lo bs.
Proof.
  intros m lo hi ST LE. (nelim (stk_bytes bsegs m lo hi ST LE) 3%nat; intros bs L B). exists bs. split; [exact L|].
  split; [exact B|]. (nelim ST 3%nat; intros S1 S2 S3). split; [lia|]. split; [rewrite L; rewrite Z2Nat.id by lia; lia|].
  intros i Hi. rewrite L, Z2Nat.id in Hi by lia. apply S3. lia.
Qed.
Lemma stk_of_u8arr : forall m A bs, u8arr bsegs m A bs -> stk bsegs m A (A + Z.of_nat (length bs)).
Proof.
  intros m A bs H. pose proof (rw_cells_of_u8arr bsegs m A bs H) as C. pose proof (stk_of_rw_cells bsegs m _ _ C) as S.
  cbn [cells_size csize Nat.add] in S. rewrite Nat.add_0_r in S. exact S.
Qed.

(* [comment removed for export] *)
Lemma le8_split32 : forall z, 0 <= z < 2^32 -> le8 (Z_to_bv 64 z) = le4 (Z_to_bv 64 z) ++ le4 (Z_to_bv 64 0).
Proof.
  intros z Hz. rewrite <- store_bytes_8'. unfold le4. rewrite !unsigned_lit by lia.
  cbn [Z_to_le_bytes app]. rewrite !Z.shiftr_shiftr by lia.
  rewrite !Z.shiftr_0_l.
  rewrite !(Z.shiftr_div_pow2 z) by lia. cbn -[Z_to_bv Z.div].
  do 4 f_equal.
  rewrite !Z.div_small by lia. reflexivity.
Qed.
Lemma C8_as_C4s : forall m A z, 0 <= z < 2^32 ->
  rw_cells bsegs m A [C8 (Z_to_bv 64 z)] -> rw_cells bsegs m A [C4 (Z_to_bv 64 z); C4 (Z_to_bv 64 0)].
Proof.
  intros m A z Hz H. eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite !app_nil_r. symmetry. apply le8_split32. exact Hz.
Qed.
Lemma C4s_as_C8 : forall m A z, 0 <= z < 2^32 ->
  rw_cells bsegs m A [C4 (Z_to_bv 64 z); C4 (Z_to_bv 64 0)] -> rw_cells bsegs m A [C8 (Z_to_bv 64 z)].
Proof.
  intros m A z Hz H. eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite !app_nil_r. apply le8_split32. exact Hz.
Qed.

(* [comment removed for export] *)
Lemma land_align16 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551600 = x / 16 * 16.
Proof.
  intros x Hx.
  replace 18446744073709551600 with (Z.lxor (Z.ones 64) (Z.ones 4)) by reflexivity.
  replace (x / 16 * 16) with (Z.shiftl (Z.shiftr x 4) 4).
  2:{ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. }
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.lxor_spec, Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i 4) as [Hi3|Hi3].
  - rewrite (Z.testbit_neg_r (Z.shiftr x 4)) by lia. rewrite !Z.ones_spec_low by lia. cbn. apply andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (i - 4 + 4) with i by lia. rewrite (Z.ones_spec_high 4 i) by lia.
    destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
    + rewrite Z.ones_spec_low by lia. cbn. apply andb_true_r.
    + rewrite Z.ones_spec_high by lia. cbn.
      replace (Z.testbit x i) with false; [reflexivity|]. symmetry.
      destruct (Z.eq_dec x 0) as [->|Hx0]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia| lia].
Qed.
Lemma stored_index : forall x, 0 <= x < 2^32 -> Z.land (Z.shiftr x 16) 18446744073709551600 = 16 * (x / 1048576).
Proof.
  intros x Hx. rewrite land_align16 by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; nia).
  rewrite Z.shiftr_div_pow2 by lia. change (2^16) with 65536. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Lemma ssrep_high : forall W m m' T sbl, ssrep m T sbl -> sswf T sbl -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) W -> ssrep m' T sbl.
Proof.
  intros W m m' T sbl (TOT & BL & VIS) (T1 & LEN & BR) MU WM HW.
  pose proof (high_disjoint W HW) as D. unfold CEIL in D.
  split; [| split].
  - eapply rw_cells_transport; [exact TOT| exact MU| exact WM| apply D; cbn; lia].
  - intros b Hb. destruct (BL b Hb) as (sj & H). exists sj. eapply rw_cells_transport; [exact H| exact MU| exact WM| apply D; cbn; lia].
  - intros b Hb. (nelim (BR b Hb) 3%nat; intros R1 R2 R3). eapply stk_wmono_noseg; [exact (VIS b Hb)| exact WM| unfold AIMG_HI; lia].
Qed.

Section STORE.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (mv : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (T n ARGS PK P lo : Z) (sbl : list Z) (pk : word) (tr : list Z).
  Hypothesis HC : mmap_consts mv.
  Hypothesis MI0 : mem_inv bsegs mv.
  Hypothesis ST0 : stk bsegs mv lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + 432 <= bv_unsigned sp.
  Hypothesis SSR : ssrep mv T sbl.
  Hypothesis SSW : sswf T sbl.
  Hypothesis Hn : n = zlen tr /\ 1 <= n <= 30.
  Hypothesis HT : T + 64 < 2^31.
  Hypothesis HSB : zlen sbl < 4095.
  Hypothesis HARGS : bv_unsigned sp <= ARGS /\ ARGS + 16 < 2^64.
  Hypothesis HPK : bv_unsigned sp <= PK /\ PK + 8 < 2^64.
  Hypothesis HAP : ARGS + 16 <= PK \/ PK + 8 <= ARGS.
  Hypothesis ARGSC : rw_cells bsegs mv ARGS [C8 (Z_to_bv 64 P); C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 0)].
  Hypothesis PKC : rw_cells bsegs mv PK [C8 pk].
  Hypothesis HP : alloc_ceiling <= P /\ P + 8 * n <= 2^64 /\ (P + 8 * n <= lo \/ (bv_unsigned sp <= P /\ PK + 8 <= P /\ ARGS + 16 <= P)).
  Hypothesis TRC : cells_at bsegs mv P (trace_cells tr).
  Hypothesis HFS : forall a : word, mmap_grant mo a 8388608 -> 0x5ff000 <= bv_unsigned a.

  Lemma store_spec : forall (Pp : machine_state -> Model -> lghost -> Prop),
    8388608 <= R -> mmap_placeable mo 8388608 ->
    (forall (start : Z) (sbl' : list Z) (nb : list (Z * Z)) (m' : word -> option byte) (mo' : Model) (G' : list (Z * Z)) (R' : Z) (pk' : word)
            (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
       (start = T \/ (start = T + (n + 1) /\ T mod 1048576 + (n + 1) > 1048576)) -> start mod 1048576 + (n + 1) <= 1048576 ->
       ssrep m' (start + (n + 1)) sbl' -> sswf (start + (n + 1)) sbl' -> start / 1048576 < zlen sbl' ->
       ((sbl' = sbl /\ nb = [] /\ mo' = mo /\ G' = G /\ R' = R)
        \/ (exists a : word, sbl' = sbl ++ [bv_unsigned a] /\ nb = [(bv_unsigned a, bv_unsigned a + 8388608)]
                             /\ mmap_grant mo a 8388608
                             /\ mo' = mm_add_lazy a (Z_to_bv 64 8388608) mo /\ G' = (bv_unsigned a, bv_unsigned a + 8388608) :: G /\ R' = R - 8388608)) ->
       rw_cells bsegs m' ARGS [C8 (Z_to_bv 64 P); C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 0)] -> rw_cells bsegs m' PK [C8 pk'] ->
       mem_inv bsegs m' ->
       munch ((lo, bv_unsigned sp) :: (PK, PK + 8)
              :: (nthz sbl' (start / 1048576) 0 + 8 * (start mod 1048576), nthz sbl' (start / 1048576) 0 + 8 * (start mod 1048576) + 8 * (n + 1))
              :: ssfp T nb) mv m' ->
       wmono bsegs mv m' -> stk bsegs m' lo (bv_unsigned sp) ->
       LSCPS bsegs Pp (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 (start + 1)) x11 x12 x13 x14 x15 x16 x17
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                         F (ret_pc ra) fc None m' (seg_rom bsegs)) mo' (mkG G' R')) ->
    LSCPS bsegs Pp (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x17b888) (Z_to_bv 64 ARGS) (Z_to_bv 64 PK) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x71da8) fc None mv (seg_rom bsegs)) mo (mkG G R).
  Proof.
    intros Pp HRR HPL K.
    pose proof HC as HC0.
    pose proof MI0 as MI. pose proof ST0 as ST. clear ST0. pose proof ARGSC as ARGSW. pose proof PKC as PKW. clear ARGSC PKC.
    (nelimp SSR 3%nat; intros TOT BLKS VIS). (nelimp SSW 3%nat; intros T1 LENS BR).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
    pose proof (munch_refl [(lo, bv_unsigned sp); (PK, PK + 8)] mv) as MU. pose proof (wmono_refl bsegs mv) as WM.
    hide TOT.
    apply lscps_assume. intros NWX HOK HBINV.
    apply lscps_step_evt.
    carve_frame 64%nat ST.
    do 8 lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    rewrite (sx32_small n) by lia. rewrite (sx32_small 0) by lia.
    lstep. fl. rewrite Z.lor_0_r. lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. fl. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    assert (E64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp - 64) by (rewrite unsigned_lit by lia; lia).
    apply (rw_cells_app _ _ [_] [_; _; _; _; _; _; _]) in FR. destruct FR as [IDXC FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
    pose proof (ssrep_high _ mv _ T sbl SSR SSW MU WM ltac:(repeat constructor; cbn; lia)) as SSR1.
    apply evt_done. eapply alloc_spec with (lo := lo).
    { eapply (mmap_consts_munch _ mv _ HC0 MU); cbn [disjoint_from]; lia. }
    { exact MI. }
    { rewrite E64. exact ST. }
    { rewrite E64. lia. }
    { exact SSR1. }
    { exact SSW. }
    { lia. } { lia. } { exact HSB. }
    { rewrite E64. lia. } { rewrite E64. lia. } { lia. }
    { exact IDXC. } { exact PKW. } { exact HFS. } { exact HRR. } { exact HPL. }
    intros start sbl' nb m' mo' G' R' pk' x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HS1 HS2 SSR' SSW' HBF HALT IDXC' PKC' MI' MU' WM' ST'.
    rewrite E64 in MU', ST'.
    (* [comment removed for export] *)
    set (Bf := start / 1048576) in *.
    (nelim SSW' 3%nat; intros T1' LENS' BR').
    assert (HBf : 0 <= Bf < zlen sbl') by (subst Bf; split; [Z.div_mod_to_equations; lia| exact HBF]).
    assert (HBf2 : Bf = T / 1048576 \/ Bf = T / 1048576 + 1) by (subst Bf; Z.div_mod_to_equations; nia).
    destruct (ex_intro (fun blk => blk = nthz sbl' Bf 0) _ eq_refl) as [blk Hblk].
    assert (INB : In blk sbl') by (rewrite Hblk; apply nthz_In; lia).
    (nelim (BR' blk INB) 3%nat; intros Rb1 Rb2 Rb3).
    destruct (ex_intro (fun d => d = blk + 8 * (start mod 1048576)) _ eq_refl) as [d Hd].
    assert (Hdr : blk <= d /\ d + 8 * (n + 1) <= blk + 8388608 /\ d mod 8 = 0) by (subst d; Z.div_mod_to_equations; nia).
    rewrite <- Hblk in *. rewrite <- Hd.
    destruct (ex_intro (fun qf => qf = 1554584 + 16 * Bf) _ eq_refl) as [qf Hqf].
    (nelim SSR' 3%nat; intros TOT' BLKS' VIS').
    destruct (BLKS' Bf ltac:((lia_on Hn HT T1 HS1 T1' HBf HBf2 Rb1 Hd Hdr))) as (sjf & BEf). rewrite <- Hqf, <- Hblk in BEf.
    (* [comment removed for export] *)
    pose proof (VIS' blk INB) as VB.
    destruct (stk_split bsegs m' blk (d + 8 + 8 * n) (blk + 8388608) VB ltac:(lia)) as [S1 S2].
    destruct (stk_split bsegs m' blk (d + 8) (d + 8 + 8 * n) S1 ltac:(lia)) as [S1a S1b].
    destruct (stk_carve bsegs m' blk (d + 8) 8 S1a ltac:(cbn; lia)) as [S0 (hj & HDR)].
    replace (d + 8 - Z.of_nat 8) with d in S0, HDR by (cbn; lia).
    (nelim (u8arr_of_stk m' (d + 8) (d + 8 + 8 * n) S1b ltac:(lia)) 3%nat; intros dbs DLEN DARR).
    replace (d + 8 + 8 * n - (d + 8)) with (8 * n) in DLEN by lia.
    clear S1 S1a S1b VB.
    (* [comment removed for export] *)
    assert (NBF : forall iv, In iv nb -> 0x5ff000 <= fst iv /\ snd iv <= alloc_ceiling).
    { intros iv Hiv. destruct HALT as [(_ & -> & _)|(ua & _ & -> & GRa & _)]; [destruct Hiv|].
      destruct Hiv as [<-|[]]. cbn [fst snd]. pose proof (HFS ua GRa). (nelim GRa 4%nat; intros _ _ GC _). idtac. lia. }
    assert (DJ : forall a sz, bv_unsigned sp - 56 <= a -> a + sz <= 2^64 -> (a + sz <= PK \/ PK + 8 <= a) -> disjoint_from ((lo, bv_unsigned sp - 64) :: (bv_unsigned sp + -64, bv_unsigned sp + -64 + 8) :: (PK, PK + 8) :: ssfp T nb) a sz).
    { intros a sz A1 A2 A3. cbn [disjoint_from ssfp]. repeat (split; [(lia_on A1 A3 LO T1 T1' Rb1 HT)|]).
      clear - NBF A1 LO RSP. induction nb as [|[l h] nb IH]; [exact I|]. cbn. split.
      - destruct (NBF (l, h) ltac:(left; reflexivity)). cbn [fst snd] in *. lia.
      - apply IH. intros iv Hiv. apply NBF. right. exact Hiv. }
    eapply rw_cells_transport in FR; [| exact MU'| exact WM'| apply DJ; cbn; lia].
    eapply rw_cells_transport in ARGSW; [| exact MU'| exact WM'| apply DJ; cbn; lia].
    change (cells_at bsegs mv P (trace_cells tr)) with (ro_cells bsegs mv P (trace_cells tr)) in TRC.
    eapply ro_cells_transport in TRC; [| exact MU| rewrite trace_cells_size; cbn; lia].
    eapply ro_cells_transport in TRC; [| exact MU'|].
    2:{ rewrite trace_cells_size. (nelimp HP 3%nat; intros HP1 HP2 [HP3|HP3]); [| apply DJ; lia].
        cbn [disjoint_from ssfp]. repeat (split; [(lia_on Hn T1 T1' Rb1 Hdr HP3 LO HARGS HPK HP1 HT)|]).
        clear - NBF HP1 HP3 LO RSP Hn. induction nb as [|[l h] nb IH]; [exact I|]. cbn. split.
        - destruct (NBF (l, h) ltac:(left; reflexivity)). cbn [fst snd] in *. lia.
        - apply IH. intros iv Hiv. apply NBF. right. exact Hiv. }
    hide MU'. pose proof (wmono_trans bsegs _ _ _ WM WM') as WM01. clear MI ST WM WM'. rename MI' into MI. rename ST' into ST.
    pose proof (munch_refl [(lo, bv_unsigned sp); (PK, PK + 8); (d, d + 8 * (n + 1)); (qf, qf + 16)] m') as MU2. pose proof (wmono_refl bsegs m') as WM2.
    apply lscps_step_evt.
    replace (ret_pc (Z_to_bv 64 466464)) with (Z_to_bv 64 466464 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    lstep. sepM. if_lia. (* [comment removed for export] *)
    lstep. fl. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. fl. rewrite Z.lor_0_l. (* [comment removed for export] *)
    setreg 10 (Z_to_bv 64 d) ltac:(f_equal; exact eq_refl).
    sepM. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    setreg 12 (Z_to_bv 64 (8 * n)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    lstep. (* [comment removed for export] *)
    destruct TRC as [TWF TB].
    eapply (imemcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (d + 8) P (8 * n) (cells_bytes (trace_cells tr)));
      [lia| lia| lia| lia| exact TB| | exact DARR| exact DLEN| exact MI|].
    { rewrite (cells_bytes_length _ TWF). pose proof (trace_cells_size tr). lia. }
    intros m3 dbs2 x14' DARR2 DLEN2 MI3 MU3 WM3.
    replace (ret_pc (Z_to_bv 64 466496)) with (Z_to_bv 64 466496 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply rw_cells_transport in FR; [| exact MU3| exact WM3| cbn; lia].
    eapply rw_cells_transport in ARGSW; [| exact MU3| exact WM3| cbn; lia].
    eapply rw_cells_transport in IDXC'; [| exact MU3| exact WM3| cbn; lia].
    eapply rw_cells_transport in PKC'; [| exact MU3| exact WM3| cbn; lia].
    eapply rw_cells_transport in BEf; [| exact MU3| exact WM3| cbn; (lia_on Hn HT T1 HS1 T1' HBf2 Rb1 Hd Hdr Hqf)].
    eapply rw_cells_transport in TOT'; [| exact MU3| exact WM3| cbn; lia].
    lazymatch goal with H : rw_cells _ _ d [C8 ?v] |- _ => eapply rw_cells_transport in H; [| exact MU3| exact WM3| cbn; lia]; rename H into HDR' end.
    eapply (stk_wmono_noseg) in S0; [| exact WM3| unfold AIMG_HI; lia].
    eapply (stk_wmono_noseg) in S2; [| exact WM3| unfold AIMG_HI; lia].
    apply (munch_weaken _ [(lo, bv_unsigned sp); (PK, PK + 8); (d, d + 8 * (n + 1)); (qf, qf + 16)]) in MU3. 2:{ unfold sub_fp; cbn; intros; lia. }
    pose proof (munch_trans _ _ _ _ MU2 MU3) as MU4. pose proof (wmono_trans bsegs _ _ _ WM2 WM3) as WM4.
    eapply stk_wmono_noseg in ST; [| exact WM3| unfold AIMG_HI; lia].
    pose proof (wmono_trans bsegs _ _ _ WM01 WM3) as WM02. clear WM01. rename WM02 into WM01.
    clear MU2 MU3 WM2 WM3 MI. rename MU4 into MU2. rename WM4 into WM2. rename MI3 into MI.
    lstep. (* [comment removed for export] *)
    sepM. lstep. sepM. lstep. (* [comment removed for export] *)
    setreg 10 (Z_to_bv 64 (16 * Bf)) ltac:(f_equal; subst Bf; symmetry; apply stored_index; (lia_on Hn HT T1 HS1 T1' Rb1 Hd Hdr DLEN2)).
    lstep. lstep. (* [comment removed for export] *)
    setreg 10 (Z_to_bv 64 (qf + 8)) ltac:(f_equal; lia).
    assert (ALqf : (qf + 8) mod 4 = 0) by (rewrite Hqf; Z.div_mod_to_equations; lia).
    assert (PRqf : 0 <= qf /\ qf + 16 < 2^64) by (lia_on Hn HT T1 HS1 T1' HBf2 Rb1 Hd Hdr Hqf DLEN2).
    amo_zstep2. sepM. amo_w_junk. fl. (* [comment removed for export] *)
    lstep. lstep. sepM. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => apply (C8_as_C4s mc _ start) in IDXC'; [| (lia_on Hn HT T1 HS1 T1' HBf2 Rb1 Hd Hdr DLEN2 PRqf)] end.
    lstep. (* [comment removed for export] *)
    rewrite (sx32_small start) by (lia_on Hn HT T1 HS1 T1' Rb1 Hd Hdr DLEN2 PRqf).
    lstep. lstep. (* [comment removed for export] *)
    sepM. lstep. (* [comment removed for export] *)
    sepM. lstep. (* [comment removed for export] *)
    rewrite (swrap32_small (start + 1)) by (lia_on Hn HT T1 HS1 T1' Rb1 Hd Hdr DLEN2 PRqf).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (FRJ : rw_cells bsegs mc (bv_unsigned sp + -64) ([C4 (Z_to_bv 64 start); C4 (Z_to_bv 64 0)] ++ [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]));
      [apply rw_cells_app; split; [exact IDXC'|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; exact FR|] end.
    clear FR IDXC'. cbn [app] in FRJ. rename FRJ into FR.
    do 7 lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    apply evt_done.
    eapply (K start sbl' nb _ mo' G' R'); [exact HS1| exact HS2| | split; [exact T1'| split; [exact LENS'| exact BR']]| exact HBF| | exact ARGSW
      | match goal with H : rw_cells _ _ PK _ |- _ => exact H end| exact MI| | | exact ST].
    2:{ destruct HALT as [HL|(ua & E1 & E2 & E3 & E4 & E5 & E6 & E7 & _)]; [left; exact HL| right; exists ua; repeat (split; [assumption|]); assumption]. }
    { (* [comment removed for export] *)
      split; [exact TOT'| split].
      - intros b Hb. destruct (Z.eq_dec b Bf) as [->|NE].
        + rewrite <- Hqf, <- Hblk. lazymatch goal with H : rw_cells _ _ qf [C8 _; C4 ?w; _; _; _; _] |- _ => exists w; exact H end.
        + destruct (BLKS' b Hb) as (sj & H). exists sj. eapply rw_cells_transport; [exact H| exact MU2| exact WM2|].
          clear - Hqf NE LO RSP HPK Hdr Rb1 Hb. rewrite Hqf. cbn. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
      - intros b' Hb'. destruct (Z.eq_dec b' blk) as [->|NE].
        + apply (stk_merge bsegs m2 blk d); [exact S0| | lia].
          apply (stk_merge bsegs m2 d (d + 8)); [| | lia].
          { lazymatch goal with H : rw_cells _ m2 d [C8 ?v] |- _ => pose proof (stk_of_rw_cells bsegs m2 _ _ H) as X; cbn in X; exact X end. }
          apply (stk_merge bsegs m2 (d + 8) (d + 8 + 8 * n)); [| exact S2| lia].
          pose proof (stk_of_u8arr m2 _ _ DARR2) as X. rewrite DLEN2, Z2Nat.id in X by lia. exact X.
        + (nelim (BR' b' Hb') 3%nat; intros Q1 Q2 Q3). eapply stk_wmono_noseg; [exact (VIS' b' Hb')| exact WM2| unfold AIMG_HI; lia]. }
    { (* [comment removed for export] *)
      change (start / 1048576) with Bf. rewrite <- Hblk, <- Hd.
      unhide MU'.
      set (TG := (lo, bv_unsigned sp) :: (PK, PK + 8) :: (d, d + 8 * (n + 1)) :: ssfp T nb).
      assert (X1 : munch TG mv m). { clear - MU. eapply munch_weaken; [| exact MU]. unfold sub_fp, TG; intros x Hx; cbn [outside ssfp] in *; tauto. }
      assert (X2 : munch TG m m'). { clear - MU' LO RSP HPK. eapply munch_weaken; [| exact MU']. unfold sub_fp, TG; intros x Hx; cbn [outside ssfp] in Hx |- *.
        repeat match type of Hx with _ /\ _ => destruct Hx as [? Hx] end. repeat split; try assumption; lia. }
      assert (X3 : munch TG m' m2). { clear - MU2 Hqf HBf2 LO RSP HPK. eapply munch_weaken; [| exact MU2]. unfold sub_fp, TG; intros x Hx; cbn [outside ssfp] in Hx |- *.
        repeat match type of Hx with _ /\ _ => destruct Hx as [? Hx] end. repeat split; try assumption; try lia.
        all: rewrite Hqf; destruct HBf2 as [E|E]; rewrite E in *; lia. }
      subst TG. exact (munch_trans _ _ _ _ X1 (munch_trans _ _ _ _ X2 X3)). }
    { exact WM01. }
  Qed.
End STORE.


End CeilWrap.
End RTW_depot_store.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import InitMem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep CJ_iface RT_art RT_kit RT_fp RT_artF RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_depot_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_lock.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap.
Import RTW_depot_create.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_memcpy.
Import RTW_depot_alloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_hash.
Import RTW_depot_store.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma cf240_cell : forall st m, RTREP st m -> ro_cells bsegs m 0x13b5d8 [C4 (Z_to_bv 64 0)].
Proof.
  intros st m HR. pose proof (rr_consts st m HR) as HC.
  destruct HC as (_ & _ & _ & CF & _).
  apply (cells_at_C4_of_bytes m _ 0); [lia|]. intros i Hi. exists (nth (240 + i) (map zb cflags_bytes) (zb 0)). split.
  - replace (0x13b5d8 + Z.of_nat i) with (A_CFLAGS + Z.of_nat (240 + i)) by (unfold A_CFLAGS; lia). apply cflags_byte; [exact CF| lia].
  - change (zb 0) with ((fun z => zb z) 0). rewrite map_nth. unfold zb. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    do 4 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.

(* [comment removed for export] *)
Lemma ssrep_munch : forall W m m' T sbl, ssrep m T sbl -> sswf T sbl -> munch W m m' -> wmono bsegs m m' ->
  (forall a sz, 0x17b888 <= a -> a + sz <= 0x18b898 -> disjoint_from W a sz) -> ssrep m' T sbl.
Proof.
  intros W m m' T sbl (TOT & BL & VIS) (T1 & LEN & BR) MU WM D.
  split; [| split].
  - eapply rw_cells_transport; [exact TOT| exact MU| exact WM| apply D; cbn; lia].
  - intros b Hb. destruct (BL b Hb) as (sj & H). exists sj. eapply rw_cells_transport; [exact H| exact MU| exact WM| apply D; cbn; lia].
  - intros b Hb. destruct (BR b Hb) as (R1 & R2 & R3). eapply stk_wmono_noseg; [exact (VIS b Hb)| exact WM| unfold AIMG_HI; lia].
Qed.

Ltac fixaddr v := match goal with |- rw_cells _ _ ?a _ => replace a with v by (cbn; lia) end.
Ltac fixaddrH H v := match type of H with rw_cells _ _ ?a _ => replace a with v in H by (cbn; lia) end.
(* [comment removed for export] *)
Ltac djn := match goal with |- disjoint_from ?W ?a ?sz => let sz' := eval cbn in sz in change (disjoint_from W a sz) with (disjoint_from W a sz') end;
  cbn [disjoint_from ssfp].

(* [comment removed for export] *)
Lemma fresh_vs_mapped : forall mo (ua bm km : word) X k,
  mmap_grant mo ua 8388608 -> In (bm, km) (vm_maps (m_vmmaps mo)) ->
  bv_unsigned bm <= X -> X + k <= bv_unsigned bm + bv_unsigned km -> 0 < k ->
  X + k <= bv_unsigned ua \/ bv_unsigned ua + 8388608 <= X.
Proof.
  intros mo ua bm km X k (_ & _ & GC & GF) HIN HB1 HB2 Hk.
  rewrite region_free_app in GF. apply andb_true_iff in GF as [_ GF].
  pose proof (bv_unsigned_in_range 64 ua) as RA. change (bv_modulus 64) with (2^64) in RA. ceilb.
  pose proof (bv_unsigned_in_range 64 bm) as RB. change (bv_modulus 64) with (2^64) in RB.
  destruct (Z_lt_le_dec X (bv_unsigned ua + 8388608)); [| right; lia].
  destruct (Z_lt_le_dec (bv_unsigned ua) (X + k)); [| left; lia]. exfalso.
  set (x := Z.max X (bv_unsigned ua)).
  eapply (region_free_false_of _ ua (Z_to_bv 64 8388608) bm km (Z_to_bv 64 x) GF HIN); rewrite ?unsigned_lit by lia; lia.
Qed.

Section NSTORE.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (mv : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (T n ARGS ND P h lo : Z) (sbl : list Z) (tr : list Z) (ndj : list byte).
  Hypothesis HC : mmap_consts mv.
  Hypothesis CF240 : ro_cells bsegs mv 0x13b5d8 [C4 (Z_to_bv 64 0)].
  Hypothesis MI0 : mem_inv bsegs mv.
  Hypothesis ST0 : stk bsegs mv lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + 464 <= bv_unsigned sp.
  Hypothesis SSR : ssrep mv T sbl.
  Hypothesis SSW : sswf T sbl.
  Hypothesis Hn : n = zlen tr /\ 1 <= n <= 30.
  Hypothesis HT : T + 64 < 2^31.
  Hypothesis HSB : zlen sbl < 4095.
  Hypothesis HARGS : bv_unsigned sp <= ARGS /\ ARGS + 16 < 2^64.
  Hypothesis ARGSC : rw_cells bsegs mv ARGS [C8 (Z_to_bv 64 P); C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 0)].
  Hypothesis HP : alloc_ceiling <= P /\ P + 8 * n <= 2^64 /\ (P + 8 * n <= lo \/ (bv_unsigned sp <= P /\ ARGS + 16 <= P)).
  Hypothesis TRC : cells_at bsegs mv P (trace_cells tr).
  Hypothesis HND : 0x5ff000 <= ND /\ ND + 16 <= alloc_ceiling.
  Hypothesis NDC : rw_cells bsegs mv ND [CB 16 ndj].
  Hypothesis Hh : 0 <= h < 2^64.
  Hypothesis HFS : forall a : word, mmap_grant mo a 8388608 -> 0x5ff000 <= bv_unsigned a.
  (* [comment removed for export] *)
  Hypothesis HNDS : forall b, In b sbl -> ND + 16 <= b \/ b + 8388608 <= ND.
  Hypothesis HNDM : exists (bm km : word), In (bm, km) (vm_maps (m_vmmaps mo)) /\ bv_unsigned bm <= ND /\ ND + 16 <= bv_unsigned bm + bv_unsigned km.

  Ltac fin_tail K HS1 HS2 SSR' SSW' HBF HALT ARGSC' MU2 WM2 MU MU' Hblk Hd LO RSP Bf start sbl' nb mo' G' R' d n lo sp ND T :=
    lstep; lstep; lstep; lstep; (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with FRJ : rw_cells _ mm (bv_unsigned ?spv + -32) [CB 8 ?jj], PKC : rw_cells _ mm (bv_unsigned ?spv + -24) [C8 ?pkv],
                          FR : rw_cells _ mm (bv_unsigned ?spv + -16) [C8 ?s0v; C8 ?rav] |- _ =>
        let FRM := fresh "FRM" in
        assert (FRM : rw_cells bsegs mm (bv_unsigned spv + -32) ([CB 8 jj] ++ [C8 pkv] ++ [C8 s0v; C8 rav]));
        [ apply rw_cells_app; split; [exact FRJ|]; fixaddr (bv_unsigned spv + -24); apply (rw_cells_app _ _ [_] [_; _]); split; [exact PKC|];
          fixaddr (bv_unsigned spv + -16); exact FR
        | cbn [app] in FRM; clear FRJ PKC FR;
          lazymatch goal with ST : stk _ mm ?loq _ |- _ => release_frame FRM ST (bv_unsigned spv) end ]
      end
    end;
    apply evt_done;
    unhide MU; unhide MU';
    lazymatch type of MU with munch _ ?m0 ?m1 =>
    lazymatch type of MU' with munch _ _ ?m2 =>
    lazymatch goal with |- LSCPS _ _ (MS _ _ _ _ _ ?mm _) _ _ =>
      eapply (K start sbl' nb mm mo' G' R');
      [ exact HS1 | exact HS2
      | eapply (ssrep_munch _ m2 mm); [exact SSR'| exact SSW'| exact MU2| exact WM2| intros a' sz' A1 A2; cbn; lia]
      | exact SSW' | exact HBF | exact HALT
      | first [exact ARGSC' | eapply rw_cells_transport; [exact ARGSC'| exact MU2| exact WM2| cbn; lia]]
      | lazymatch goal with H : rw_cells _ mm ND _ |- _ => exact H end
      | assumption
      | change (start / 1048576) with Bf; rewrite <- Hblk, <- Hd;
        let TG := fresh "TG" in
        set (TG := (lo, bv_unsigned sp) :: (ND, ND + 16) :: (d, d + 8 * (n + 1)) :: ssfp T nb);
        let X1 := fresh "X1" in let X2 := fresh "X2" in let X3 := fresh "X3" in
        assert (X1 : munch TG m0 m1) by (clear - MU; eapply munch_weaken; [| exact MU]; unfold sub_fp, TG; intros x Hx; cbn [outside ssfp] in *; tauto);
        assert (X2 : munch TG m1 m2) by (clear - MU' LO RSP; eapply munch_weaken; [| exact MU']; unfold sub_fp, TG; intros x Hx; cbn [outside ssfp] in Hx |- *;
          repeat match type of Hx with _ /\ _ => destruct Hx as [? Hx] end; repeat split; try assumption; lia);
        assert (X3 : munch TG m2 mm) by (clear - MU2; eapply munch_weaken; [| exact MU2]; unfold sub_fp, TG; intros x Hx; cbn [outside ssfp] in *; tauto);
        subst TG; exact (munch_trans _ _ _ _ X1 (munch_trans _ _ _ _ X2 X3))
      | assumption
      | assumption ]
    end end end.

  Lemma nstore_spec : forall (Pp : machine_state -> Model -> lghost -> Prop),
    8388608 <= R -> mmap_placeable mo 8388608 ->
    (forall (start : Z) (sbl' : list Z) (nb : list (Z * Z)) (m' : word -> option byte) (mo' : Model) (G' : list (Z * Z)) (R' : Z) (lj : list byte)
            (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
       (start = T \/ (start = T + (n + 1) /\ T mod 1048576 + (n + 1) > 1048576)) -> start mod 1048576 + (n + 1) <= 1048576 ->
       ssrep m' (start + (n + 1)) sbl' -> sswf (start + (n + 1)) sbl' -> start / 1048576 < zlen sbl' ->
       ((sbl' = sbl /\ nb = [] /\ mo' = mo /\ G' = G /\ R' = R)
        \/ (exists a : word, sbl' = sbl ++ [bv_unsigned a] /\ nb = [(bv_unsigned a, bv_unsigned a + 8388608)]
                             /\ mmap_grant mo a 8388608
                             /\ mo' = mm_add_lazy a (Z_to_bv 64 8388608) mo /\ G' = (bv_unsigned a, bv_unsigned a + 8388608) :: G /\ R' = R - 8388608)) ->
       rw_cells bsegs m' ARGS [C8 (Z_to_bv 64 P); C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 0)] ->
       rw_cells bsegs m' ND [C8 (Z_to_bv 64 h); CB 4 lj; C4 (Z_to_bv 64 (start + 1))] ->
       mem_inv bsegs m' ->
       munch ((lo, bv_unsigned sp) :: (ND, ND + 16)
              :: (nthz sbl' (start / 1048576) 0 + 8 * (start mod 1048576), nthz sbl' (start / 1048576) 0 + 8 * (start mod 1048576) + 8 * (n + 1))
              :: ssfp T nb) mv m' ->
       wmono bsegs mv m' -> stk bsegs m' lo (bv_unsigned sp) ->
       LSCPS bsegs Pp (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                         F (ret_pc ra) fc None m' (seg_rom bsegs)) mo' (mkG G' R')) ->
    LSCPS bsegs Pp (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ND) a1 (Z_to_bv 64 ARGS) (Z_to_bv 64 h) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x740bc) fc None mv (seg_rom bsegs)) mo (mkG G R).
  Proof.
    intros Pp HRR HPL K.
    pose proof HC as HC0. destruct HC as (_ & _ & GOTC & _). hide GOTC. hide CF240.
    pose proof MI0 as MI. pose proof ST0 as ST. clear ST0. pose proof ARGSC as ARGSW. pose proof NDC as NDW. clear ARGSC NDC.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
    pose proof (munch_refl [(lo, bv_unsigned sp); (ND, ND + 16)] mv) as MU. pose proof (wmono_refl bsegs mv) as WM.
    change (cells_at bsegs mv P (trace_cells tr)) with (ro_cells bsegs mv P (trace_cells tr)) in TRC. hide TRC.
    apply lscps_assume. intros NWX HOK HBINV.
    apply lscps_step_evt.
    carve_frame 32%nat ST.
    do 3 lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. lstep. fl. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    assert (E32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (rewrite unsigned_lit by lia; lia).
    apply (rw_cells_app _ _ [_] [_; _; _]) in FR. destruct FR as [FRJ FR].
    apply (rw_cells_app _ _ [_] [_; _]) in FR. destruct FR as [PKC FR]. fixaddrH PKC (bv_unsigned sp + -24). fixaddrH FR (bv_unsigned sp + -16).
    pose proof (ssrep_munch _ mv _ T sbl SSR SSW MU WM ltac:(intros a sz A1 A2; cbn; lia)) as SSR1.
    unhide TRC.
    apply evt_done. eapply store_spec with (lo := lo) (tr := tr).
    { eapply (mmap_consts_munch _ mv _ HC0 MU); cbn [disjoint_from]; lia. }
    { exact MI. }
    { rewrite E32. exact ST. }
    { rewrite E32. lia. }
    { exact SSR1. }
    { exact SSW. }
    { exact Hn. } { exact HT. } { exact HSB. }
    { rewrite E32. lia. } { rewrite E32. lia. } { lia. }
    { exact ARGSW. } { exact PKC. }
    { rewrite E32. lia. }
    { eapply ro_cells_transport; [exact TRC| exact MU| rewrite trace_cells_size; cbn; lia]. }
    { exact HFS. } { exact HRR. } { exact HPL. }
    intros start sbl' nb m' mo' G' R' pk' x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HS1 HS2 SSR' SSW' HBF HALT ARGSC' PKC' MI' MU' WM' ST'.
    rewrite E32 in MU', ST'.
    set (Bf := start / 1048576) in *.
    pose proof SSW' as (T1' & LENS' & BR').
    assert (HBf : 0 <= Bf < zlen sbl') by (subst Bf; split; [Z.div_mod_to_equations; lia| exact HBF]).
    destruct (ex_intro (fun blk => blk = nthz sbl' Bf 0) _ eq_refl) as [blk Hblk].
    assert (INB : In blk sbl') by (rewrite Hblk; apply nthz_In; lia).
    destruct (BR' blk INB) as (Rb1 & Rb2 & Rb3).
    destruct (ex_intro (fun d => d = blk + 8 * (start mod 1048576)) _ eq_refl) as [d Hd].
    assert (Hdr : blk <= d /\ d + 8 * (n + 1) <= blk + 8388608) by (subst d; Z.div_mod_to_equations; nia).
    rewrite <- Hblk, <- Hd in MU'.
    (* [comment removed for export] *)
    destruct HNDM as (bm & km & HIN & HB1 & HB2).
    assert (NDD : ND + 16 <= blk \/ blk + 8388608 <= ND).
    { destruct HALT as [(-> & _)|(ua & -> & _ & GRa & _)]; [apply HNDS; exact INB|].
      apply in_app_iff in INB. destruct INB as [INB|[<-|[]]]; [apply HNDS; exact INB|].
      eapply fresh_vs_mapped; [exact GRa| exact HIN| exact HB1| exact HB2| lia]. }
    assert (NBF : forall iv, In iv nb -> 0x5ff000 <= fst iv /\ snd iv <= alloc_ceiling /\ (ND + 16 <= fst iv \/ snd iv <= ND)).
    { intros iv Hiv. destruct HALT as [(_ & -> & _)|(ua & _ & -> & GRa & _)]; [destruct Hiv|].
      destruct Hiv as [<-|[]]. cbn [fst snd]. pose proof (HFS ua GRa).
      pose proof (fresh_vs_mapped mo ua bm km ND 16 GRa HIN HB1 HB2 ltac:(lia)).
      destruct GRa as (_ & _ & GC & _). idtac. lia. }
    assert (DJ : forall a sz, (a + sz <= d \/ d + 8 * (n + 1) <= a) -> (ND <= a /\ a + sz <= ND + 16) ->
                 disjoint_from ((lo, bv_unsigned sp + -32) :: (bv_unsigned sp + -24, bv_unsigned sp + -24 + 8) :: (d, d + 8 * (n + 1)) :: ssfp T nb) a sz).
    { intros a sz A1 A2. cbn [disjoint_from ssfp]. repeat (split; [lia|]).
      clear - NBF A2. induction nb as [|[l' h'] nb IH]; [exact I|]. cbn. split.
      - destruct (NBF (l', h') ltac:(left; reflexivity)) as (_ & _ & X). cbn [fst snd] in X. lia.
      - apply IH. intros iv Hiv. apply NBF. right. exact Hiv. }
    eapply rw_cells_transport in NDW; [| exact MU'| exact WM'| match goal with |- disjoint_from ?W ?a ?sz => let sz' := eval cbn in sz in change (disjoint_from W a sz) with (disjoint_from W a sz') end; apply DJ; lia].
    eapply rw_cells_transport in FRJ; [| exact MU'| exact WM'|].
    2:{ djn. repeat (split; [lia|]). clear - NBF RSP LO. induction nb as [|[l' h'] nb IH]; [exact I|]. cbn. split.
        - destruct (NBF (l', h') ltac:(left; reflexivity)) as (X1 & X2 & _). cbn [fst snd] in X1, X2. lia.
        - apply IH. intros iv Hiv. apply NBF. right. exact Hiv. }
    eapply rw_cells_transport in FR; [| exact MU'| exact WM'|].
    2:{ djn. repeat (split; [lia|]). clear - NBF RSP LO. induction nb as [|[l' h'] nb IH]; [exact I|]. cbn. split.
        - destruct (NBF (l', h') ltac:(left; reflexivity)) as (X1 & X2 & _). cbn [fst snd] in X1, X2. lia.
        - apply IH. intros iv Hiv. apply NBF. right. exact Hiv. }
    unhide GOTC. unhide CF240.
    eapply ro_cells_transport in GOTC; [| exact MU| cbn; lia]. eapply ro_cells_transport in GOTC; [| exact MU'|].
    2:{ djn. repeat (split; [lia|]). clear - NBF. induction nb as [|[l' h'] nb IH]; [exact I|]. cbn. split.
        - destruct (NBF (l', h') ltac:(left; reflexivity)) as (X1 & X2 & _). cbn [fst snd] in X1, X2. lia.
        - apply IH. intros iv Hiv. apply NBF. right. exact Hiv. }
    eapply ro_cells_transport in CF240; [| exact MU| cbn; lia]. eapply ro_cells_transport in CF240; [| exact MU'|].
    2:{ djn. repeat (split; [lia|]). clear - NBF. induction nb as [|[l' h'] nb IH]; [exact I|]. cbn. split.
        - destruct (NBF (l', h') ltac:(left; reflexivity)) as (X1 & X2 & _). cbn [fst snd] in X1, X2. lia.
        - apply IH. intros iv Hiv. apply NBF. right. exact Hiv. }
    hide MU'. hide MU. pose proof (wmono_trans bsegs _ _ _ WM WM') as WM01. clear MI ST WM WM'. rename MI' into MI. rename ST' into ST.
    pose proof (munch_refl [(lo, bv_unsigned sp); (ND, ND + 16)] m') as MU2. pose proof (wmono_refl bsegs m') as WM2.
    apply lscps_step_evt.
    replace (ret_pc (Z_to_bv 64 475368)) with (Z_to_bv 64 475368 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lstep; (if_cases KP; zify_cond KP); [clear KP| clear KP].
    1:{ lstep. (* [comment removed for export] *)
        rename FR into FR0. carve_frame 16%nat ST.
        do 3 lstep. (* [comment removed for export] *)
        lstep. lstep. fl. (* [comment removed for export] *)
        lstep. fl. (* [comment removed for export] *)
        lstep. if_lia. (* [comment removed for export] *)
        lstep. lstep. lstep. lstep. (* [comment removed for export] *)
        release_frame FR ST (bv_unsigned sp + -32). rename FR0 into FR.
        fin_tail K HS1 HS2 SSR' SSW' HBF HALT ARGSC' MU2 WM2 MU MU' Hblk Hd LO RSP Bf start sbl' nb mo' G' R' d n lo sp ND T.
 }
    fin_tail K HS1 HS2 SSR' SSW' HBF HALT ARGSC' MU2 WM2 MU MU' Hblk Hd LO RSP Bf start sbl' nb mo' G' R' d n lo sp ND T.
  Qed.
End NSTORE.


End CeilWrap.
(* [comment removed for export] *)
Ltac fixaddr v := match goal with |- rw_cells _ _ ?a _ => replace a with v by (cbn; lia) end.
Ltac fixaddrH H v := match type of H with rw_cells _ _ ?a _ => replace a with v in H by (cbn; lia) end.
Ltac djn := match goal with |- disjoint_from ?W ?a ?sz => let sz' := eval cbn in sz in change (disjoint_from W a sz) with (disjoint_from W a sz') end;
  cbn [disjoint_from ssfp].
