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
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_lib2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_fz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_m_f1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_i1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_fz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition AFREE_ICPT : Z := 0x5449c.
Definition F1_DEPTH : Z := 2128 + 48.

Definition f1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (A lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (g8 : list byte),
    ms' = MS (mkR (wz 0x54630) (wz (bv_unsigned sp + -2128)) gp tp t0' t1' t2'
                  sp (wz A) (wz (bv_unsigned sp + -2128)) (wz PC0_FREE) sp (wz 0) (wz 1)
                  (wz TRACE_MAX_LEN) a6' a7'
                  (wz PC0_FREE) (wz 1) (wz (bv_unsigned sp + -2128)) (wz (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (wz AUNWIND_IMPL) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (A_IA_INSTANCE, A_IA_INSTANCE + A_IA_SIZE); (A_IA_INITED, A_IA_INITED + 4)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ RTREP (set_ia_inited st) m'
    /\ stk asegs m' lo (bv_unsigned sp + -2128)
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C4 (wz 0); C4 (wz 0)]
    /\ stk asegs m' (bv_unsigned sp + -2112) (bv_unsigned sp + -72)
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 g8]
    /\ rw_cells asegs m' (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section F1.
Hypothesis internal_allocator_proof : internal_allocator_spec.
Hypothesis get_malloc_ctx_size_proof : get_malloc_ctx_size_spec.
Hypothesis get_current_pc_proof : get_current_pc_spec.

Lemma free_f1_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (A lo : Z),
  RTREP st m -> RTWF st -> mem_inv asegs m -> a0 = wz A -> 0 <= A < 2^47 ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + F1_DEPTH <= bv_unsigned sp ->
  evt asegs (f1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st A lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz AFREE) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HR WF MI -> HA ST HCL LO. unfold f1_post.
  pose proof (munch_refl [(lo, bv_unsigned sp); (A_IA_INSTANCE, A_IA_INSTANCE + A_IA_SIZE); (A_IA_INITED, A_IA_INITED + 4)] m) as MU.
  pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0.
  pose proof (RTWF_ia' st WF) as WF1.
  (* [comment removed for export] *)
  pose proof (rr_consts st m HR) as HC0. (nelim HC0 5%nat; intros _ _ _ HCF _).
  pose proof (cflags_byte m 34 HCF ltac:(lia)) as CF34. change (nth 34 (map zb cflags_bytes) (zb 0)) with (zb 1) in CF34.
  change (cells_at asegs m (A_CFLAGS + Z.of_nat 34) [C1 (zb 1)]) with (ro_cells asegs m 0x13bdca [C1 (zb 1)]) in CF34. clear HCF.
  pose proof (rtrep_artcells st m HR) as HAC. unfold ARTCELLS in HAC.
  (nelim HAC 12%nat; intros _ _ _ _ _ _ _ _ _ _ GOTCF _).
  change (cells_at asegs m 0xa1f70 [C8 (Z_to_bv 64 0x13bda8)]) with (ro_cells asegs m 0xa1f70 [C8 (Z_to_bv 64 0x13bda8)]) in GOTCF.
  unfold AFREE, F1_DEPTH, PC0_FREE, AUNWIND_IMPL, TRACE_MAX_LEN, A_IA_INSTANCE, A_IA_SIZE, A_IA_INITED in *. leaf_prep.
  (* [comment removed for export] *)
  carve_frame 56%nat ST.
  destruct (stk_split asegs m lo (bv_unsigned sp + -2128) (bv_unsigned sp + -56) ST ltac:(lia)) as [STlo SThi].
  destruct (stk_split asegs m _ (bv_unsigned sp + -2112) _ SThi ltac:(lia)) as [STobj SThi2].
  (nelim (stk_carve asegs m _ _ 16 STobj ltac:(lia)) 3%nat; intros _ jo OBJ).
  replace (bv_unsigned sp + -2112 - Z.of_nat 16) with (bv_unsigned sp + -2128) in OBJ by lia.
  destruct (stk_split asegs m _ (bv_unsigned sp + -72) _ SThi2 ltac:(lia)) as [STbuf STbp].
  (nelim (stk_carve asegs m _ _ 16 STbp ltac:(lia)) 3%nat; intros _ jb BP).
  replace (bv_unsigned sp + -56 - Z.of_nat 16) with (bv_unsigned sp + -72) in BP by lia.
  clear SThi STobj SThi2 STbp ST. rename STlo into ST.
  lstep. (* [comment removed for export] *)
  do 8 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof HR as HR1. rtrep_high HR1 WF MU0 WM. clear MU0.
  callxp ltac:(eapply internal_allocator_proof; [exact HR1 | exact WF | eassumption | rewrite ?unsigned_lit by lia; exact ST | idtac; lia | rewrite ?unsigned_lit by lia; lia])
         ltac:(unfold leaf_post, A_IA_INSTANCE, A_IA_SIZE, A_IA_INITED).
  clear HR1. restk. rewrite ?unsigned_lit in ST by lia.
  cbv beta delta [wz] in *. match goal with H : ?x = Z_to_bv 64 _ |- _ => subst x end. match goal with H : RTREP (set_ia_inited st) _ |- _ => rename H into HR2 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(lo, bv_unsigned sp)] mx) as MU1; pose proof (wmono_refl asegs mx) as WM1 end.
  (* [comment removed for export] *)
  set (i := A / 2^32). assert (Hi : 0 <= i < 2^15) by (subst i; Z.div_mod_to_equations; lia).
  pose proof (rr_ia _ _ HR2 i Hi) as IA. unfold A_IA_MAP1 in IA. cbv beta delta [wz zb] in IA. set (p := 701576 + 8 * i) in IA.
  lstep. (* [comment removed for export] *)
  rewrite (Z.shiftr_div_pow2 A 47) by lia. rewrite (Z.div_small A (2^47)) by lia.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) rewrite (Z.shiftr_div_pow2 A 32) by lia. change (A / 2^32) with i.
  lstep. lstep. (* [comment removed for export] *)
  rewrite (Z.shiftl_mul_pow2 i 3) by lia. replace (701568 + i * 2^3) with (p + -8) by (subst p; lia).
  assert (HP : 701576 <= p /\ p + 8 <= 1230000) by (subst p; lia). clearbody p.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof HR2 as HR1. rtrep_high HR1 WF1 MU1 WM1.
  call get_malloc_ctx_size_proof; [exact HR1 | eassumption | intros; discriminate | rewrite ?unsigned_lit by lia; exact ST | idtac; lia | rewrite ?unsigned_lit by lia; lia | ].
  clear HR1. restk. rewrite ?unsigned_lit in ST by lia.
  match goal with H : ?x = wz _ |- _ => cbv beta delta [wz] in H; unfold TRACE_MAX_LEN in H; subst x end.
  lstep. lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof HR2 as HR1. rtrep_high HR1 WF1 MU1 WM1.
  call get_current_pc_proof; [exact HR1 | eassumption | intros; discriminate | rewrite ?unsigned_lit by lia; exact ST | idtac; lia | rewrite ?unsigned_lit by lia; lia | ].
  clear HR1. restk. rewrite ?unsigned_lit in ST by lia.
  match goal with H : ?x = Z_to_bv 64 _ |- _ => subst x end.
  lstep. lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof HR2 as HR1. rtrep_high HR1 WF1 MU1 WM1.
  call get_malloc_ctx_size_proof; [exact HR1 | eassumption | intros; discriminate | rewrite ?unsigned_lit by lia; exact ST | idtac; lia | rewrite ?unsigned_lit by lia; lia | ].
  clear HR1. restk. rewrite ?unsigned_lit in ST by lia.
  match goal with H : ?x = wz _ |- _ => cbv beta delta [wz] in H; unfold TRACE_MAX_LEN in H; subst x end.
  lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  change (bv_unsigned (zb 1)) with 1.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -72) _ |- _ =>
    change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with (Z.ones 64) in H;
    rewrite Z.land_comm, Z.land_ones, Z.mod_small, Z_to_bv_bv_unsigned in H by lia; rename H into BP' end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -2128) [C8 _; C8 _] |- _ =>
    pose proof (proj1 (rw_cells_app _ _ [C8 _] [C8 _]) H) as [OB1 OB2]; clear H;
    cbn [cells_size Cells.csize Nat.add] in OB2; apply c8_zero_c44 in OB2;
    pose proof (proj2 (rw_cells_app _ _ [C8 _] [C4 _; C4 _]) (conj OB1 OB2)) as OBJ' end.
  pose proof HR2 as HR3. rtrep_high HR3 WF1 MU1 WM1.
  apply evt_done. nexists 9%nat. eexists. eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; try assumption; try eassumption.
Qed.
End F1.


End CeilWrap.
End RTW_m_f1.

(* [comment removed for export] *)
Module RTW_m_r1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_i1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_fz RTW_m_f1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition AREALLOC_ICPT : Z := 0x54894.
Definition R1_DEPTH : Z := 2144 + 48.

Definition r1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (A n lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (g8 : list byte),
    ms' = MS (mkR (wz 0x54a2c) (wz (bv_unsigned sp + -2144)) gp tp t0' t1' t2'
                  sp (wz n) (wz (bv_unsigned sp + -2136)) (wz PC0_REALLOC) sp (wz 0) (wz 1)
                  (wz TRACE_MAX_LEN) a6' a7'
                  (wz A) (wz PC0_REALLOC) (wz 1) (wz (bv_unsigned sp + -2136)) (wz (bv_unsigned sp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (wz AUNWIND_IMPL) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (A_IA_INSTANCE, A_IA_INSTANCE + A_IA_SIZE); (A_IA_INITED, A_IA_INITED + 4)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ RTREP (set_ia_inited st) m'
    /\ stk asegs m' lo (bv_unsigned sp + -2144)
    /\ rw_cells asegs m' (bv_unsigned sp + -2136) [C8 (wz (bv_unsigned sp + -2136 + 16)); C4 (wz 0); C4 (wz 0)]
    /\ stk asegs m' (bv_unsigned sp + -2120) (bv_unsigned sp + -80)
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 sp; CB 8 g8]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section R1.
Hypothesis try_asan_init_proof : try_asan_init_spec.
Hypothesis internal_allocator_proof : internal_allocator_spec.
Hypothesis get_malloc_ctx_size_proof : get_malloc_ctx_size_spec.
Hypothesis get_current_pc_proof : get_current_pc_spec.

Lemma realloc_r1_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (A n lo : Z),
  RTREP st m -> RTWF st -> mem_inv asegs m -> a0 = wz A -> a1 = wz n -> 0 <= A < 2^47 ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + R1_DEPTH <= bv_unsigned sp ->
  evt asegs (r1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st A n lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz AREALLOC) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HR WF MI -> -> HA ST HCL LO. unfold r1_post.
  pose proof (munch_refl [(lo, bv_unsigned sp); (A_IA_INSTANCE, A_IA_INSTANCE + A_IA_SIZE); (A_IA_INITED, A_IA_INITED + 4)] m) as MU.
  pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0.
  pose proof (RTWF_ia' st WF) as WF1.
  (* [comment removed for export] *)
  pose proof (rr_consts st m HR) as HC0. (nelim HC0 5%nat; intros _ _ _ HCF _).
  pose proof (cflags_byte m 34 HCF ltac:(lia)) as CF34. change (nth 34 (map zb cflags_bytes) (zb 0)) with (zb 1) in CF34.
  change (cells_at asegs m (A_CFLAGS + Z.of_nat 34) [C1 (zb 1)]) with (ro_cells asegs m 0x13bdca [C1 (zb 1)]) in CF34. clear HCF.
  pose proof (rtrep_artcells st m HR) as HAC. unfold ARTCELLS in HAC.
  (nelim HAC 12%nat; intros _ _ _ _ _ _ _ _ _ _ GOTCF _).
  change (cells_at asegs m 0xa1f70 [C8 (Z_to_bv 64 0x13bda8)]) with (ro_cells asegs m 0xa1f70 [C8 (Z_to_bv 64 0x13bda8)]) in GOTCF.
  unfold AREALLOC, R1_DEPTH, PC0_REALLOC, AUNWIND_IMPL, TRACE_MAX_LEN, A_IA_INSTANCE, A_IA_SIZE, A_IA_INITED in *. leaf_prep.
  (* [comment removed for export] *)
  carve_frame 64%nat ST.
  destruct (stk_split asegs m lo (bv_unsigned sp + -2136) (bv_unsigned sp + -64) ST ltac:(lia)) as [STlo SThi].
  destruct (stk_split asegs m _ (bv_unsigned sp + -2120) _ SThi ltac:(lia)) as [STobj SThi2].
  (nelim (stk_carve asegs m _ _ 16 STobj ltac:(lia)) 3%nat; intros _ jo OBJ).
  replace (bv_unsigned sp + -2120 - Z.of_nat 16) with (bv_unsigned sp + -2136) in OBJ by lia.
  destruct (stk_split asegs m _ (bv_unsigned sp + -80) _ SThi2 ltac:(lia)) as [STbuf STbp].
  (nelim (stk_carve asegs m _ _ 16 STbp ltac:(lia)) 3%nat; intros _ jb BP).
  replace (bv_unsigned sp + -64 - Z.of_nat 16) with (bv_unsigned sp + -80) in BP by lia.
  destruct (stk_split asegs m lo (bv_unsigned sp + -2144) (bv_unsigned sp + -2136) STlo ltac:(lia)) as [ST' _].
  clear SThi STobj SThi2 STbp ST STlo. rename ST' into ST.
  lstep. (* [comment removed for export] *)
  do 9 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof HR as HR1. rtrep_high HR1 WF MU0 WM.
  call try_asan_init_proof; [exact HR1 | eassumption | intros; discriminate | rewrite ?unsigned_lit by lia; exact ST | idtac; lia | rewrite ?unsigned_lit by lia; lia | ].
  clear HR1. restk. rewrite ?unsigned_lit in ST by lia.
  match goal with H : ?x = wz 1 |- _ => cbv beta delta [wz] in H; subst x end.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof HR as HR1. rtrep_high HR1 WF MU0 WM. clear MU0.
  callxp ltac:(eapply internal_allocator_proof; [exact HR1 | exact WF | eassumption | rewrite ?unsigned_lit by lia; exact ST | idtac; lia | rewrite ?unsigned_lit by lia; lia])
         ltac:(unfold leaf_post, A_IA_INSTANCE, A_IA_SIZE, A_IA_INITED).
  clear HR1. restk. rewrite ?unsigned_lit in ST by lia.
  cbv beta delta [wz] in *. match goal with H : ?x = Z_to_bv 64 _ |- _ => subst x end. match goal with H : RTREP (set_ia_inited st) _ |- _ => rename H into HR2 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(lo, bv_unsigned sp)] mx) as MU1; pose proof (wmono_refl asegs mx) as WM1 end.
  (* [comment removed for export] *)
  set (i := A / 2^32). assert (Hi : 0 <= i < 2^15) by (subst i; Z.div_mod_to_equations; lia).
  pose proof (rr_ia _ _ HR2 i Hi) as IA. unfold A_IA_MAP1 in IA. cbv beta delta [wz zb] in IA. set (p := 701576 + 8 * i) in IA.
  lstep. (* [comment removed for export] *) pr 11.
  rewrite (Z.shiftr_div_pow2 A 47) by lia. rewrite (Z.div_small A (2^47)) by lia.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) rewrite (Z.shiftr_div_pow2 A 32) by lia. change (A / 2^32) with i.
  lstep. lstep. (* [comment removed for export] *)
  rewrite (Z.shiftl_mul_pow2 i 3) by lia. replace (701568 + i * 2^3) with (p + -8) by (subst p; lia).
  assert (HP : 701576 <= p /\ p + 8 <= 1230000) by (subst p; lia). clearbody p.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof HR2 as HR1. rtrep_high HR1 WF1 MU1 WM1.
  call get_malloc_ctx_size_proof; [exact HR1 | eassumption | intros; discriminate | rewrite ?unsigned_lit by lia; exact ST | idtac; lia | rewrite ?unsigned_lit by lia; lia | ].
  clear HR1. restk. rewrite ?unsigned_lit in ST by lia.
  match goal with H : ?x = wz _ |- _ => cbv beta delta [wz] in H; unfold TRACE_MAX_LEN in H; subst x end.
  lstep. lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof HR2 as HR1. rtrep_high HR1 WF1 MU1 WM1.
  call get_current_pc_proof; [exact HR1 | eassumption | intros; discriminate | rewrite ?unsigned_lit by lia; exact ST | idtac; lia | rewrite ?unsigned_lit by lia; lia | ].
  clear HR1. restk. rewrite ?unsigned_lit in ST by lia.
  match goal with H : ?x = Z_to_bv 64 _ |- _ => subst x end.
  lstep. lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof HR2 as HR1. rtrep_high HR1 WF1 MU1 WM1.
  call get_malloc_ctx_size_proof; [exact HR1 | eassumption | intros; discriminate | rewrite ?unsigned_lit by lia; exact ST | idtac; lia | rewrite ?unsigned_lit by lia; lia | ].
  clear HR1. restk. rewrite ?unsigned_lit in ST by lia.
  match goal with H : ?x = wz _ |- _ => cbv beta delta [wz] in H; unfold TRACE_MAX_LEN in H; subst x end.
  lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  change (bv_unsigned (zb 1)) with 1.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -80) _ |- _ =>
    change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with (Z.ones 64) in H;
    rewrite Z.land_comm, Z.land_ones, Z.mod_small, Z_to_bv_bv_unsigned in H by lia; rename H into BP' end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -2136) [C8 _; C8 _] |- _ =>
    pose proof (proj1 (rw_cells_app _ _ [C8 _] [C8 _]) H) as [OB1 OB2]; clear H;
    cbn [cells_size Cells.csize Nat.add] in OB2; apply c8_zero_c44 in OB2;
    pose proof (proj2 (rw_cells_app _ _ [C8 _] [C4 _; C4 _]) (conj OB1 OB2)) as OBJ' end.
  pose proof HR2 as HR3. rtrep_high HR3 WF1 MU1 WM1.
  apply evt_done. nexists 9%nat. eexists. eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; try assumption; try eassumption.
Qed.
End R1.


End CeilWrap.
End RTW_m_r1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_quarantine_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_quarantine_iface2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_lib4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_q1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_mallocN.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstateP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_unwind.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module RTW_m_free.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_quarantine_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_quarantine_iface2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_fz.RTW_m_lbz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_specs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_i1 RTW_m_f1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_d1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_q1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_fz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_alloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RT_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_unwind OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_dcore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
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
Lemma leafc_ia' : forall st m, leafc st m -> leafc (set_ia_inited st) m.
Proof. intros st m H. destruct st. exact H. Qed.
Lemma leafc_freeP' : forall st A n m, leafc st m -> leafc (st_freeP st A n) m.
Proof. intros st A n m H. destruct st. exact H. Qed.

Lemma wmono_trans' : forall m1 m2 m3, wmono asegs m1 m2 -> wmono asegs m2 m3 -> wmono asegs m1 m3.
Proof. intros m1 m2 m3 H1 H2 x Hx. apply H2, H1, Hx. Qed.

(* [comment removed for export] *)
Definition free_core_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (tr : list Z) (A n lo : Z) (errv : word) (m : word -> option byte) (g : lghost)
    : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (st' : rtstate),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' AERRNO [C4 errv]
    /\ cj_pres (st_sp0 st) (remove_first ck_eqb (A, n) (st_lb st)) (st_lf st) (bv_unsigned sp) m m'
    /\ gmono g g' /\ trs_put tr (st_trs st) (st_trs st')
    /\ RTS st' m' mo' g' /\ LOK asegs mo' /\ BINV mo' g'
    /\ st_sp0 st' = st_sp0 st /\ st_lb st' = remove_first ck_eqb (A, n) (st_lb st) /\ st_lf st' = st_lf st
    /\ st_apend st' = st_apend st /\ st_spend st' = st_spend st /\ st_qpend st' = st_qpend st
    /\ st_qtmp st' = [] /\ st_qcur st' = []
    /\ budget_ok st g st' g' cost_free.

Definition free_core_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (A n lo : Z) (errv : word) (tl : list Z),
  RTS st m mo g -> In (A, n) (st_lb st) -> st_qtmp st = [] -> st_qcur st = [] -> st_qpend st = [] -> st_apend st = [] ->
  bv_unsigned sp <= st_sp0 st ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  rw_cells asegs m AERRNO [C4 errv] ->
  mem_inv asegs m ->
  tp = wz ATP -> a0 = wz A ->
  rt_prov st + cost_free <= g_res g ->
  4096 <= bv_unsigned ra -> bv_unsigned ra <> PC0_FREE ->
  uwt m (bv_unsigned sp) (ASTACK_TOP (st_sp0 st)) PC0_FREE (bv_unsigned sp) (bv_unsigned s0) 2 tl ->
  trs_room (hook_tr PC0_FREE (st_sp0 st) (bv_unsigned sp) (bv_unsigned ra) tl) (st_trs st) ->
  LSCPS asegs (free_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st
                 (hook_tr PC0_FREE (st_sp0 st) (bv_unsigned sp) (bv_unsigned ra) tl) A n lo errv m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz AFREE) fc None m (seg_rom asegs)) mo g.

Section FREE.
Hypothesis internal_allocator_proof : internal_allocator_spec.
Hypothesis get_malloc_ctx_size_proof : get_malloc_ctx_size_spec.
Hypothesis get_current_pc_proof : get_current_pc_spec.
Hypothesis unwind_ok : unwind_spec.
Hypothesis depot_put_proof : depot_put_specS.   (* [comment removed for export] *)
Hypothesis quarantine_put_proof : quarantine_put_spec2.

Theorem free_core_proof : free_core_stmt.
Proof.
  unfold free_core_stmt. intros until tl. intros (HR & WF & HM & HG & HFR & HSWR) HIN HQT HQC HQP HAP SPB0 ST HCL LO ERR MI TP -> COST RA1 RA2 UWT ROOM.
  pose proof (wb_sp0 st (wf_base_ok st WF)) as SP0. unfold AMALLOC_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
  pose proof (bv_unsigned_in_range 64 ra) as RRA. unfold bv_modulus in RRA. cbn in RRA.
  pose proof (t_range st WF) as TR. olin TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all.
  assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact HIN).
  (nelimp (block_geom st WF A n HB) 10%nat; intros Gn GA GK GX GY GCE GL16 GH16 GEA _). unfold usz in GY. unfold KHIGHMEM_BEG, AIMG_HI in GK. olin_all.
  (nelimp (block_extra st WF A n HB) 5%nat; intros E8 EAB EABA EMB ERZ32). pose proof (rz_size_range n) as [RZ _].
  pose proof (fp_nonneg n ltac:(lia)) as FPN. unfold cost_free in COST.
  pose proof (stk_wr_at m lo (bv_unsigned sp) (bv_unsigned sp + -2128) 2128 ST ltac:(lia) ltac:(lia)) as WR0.
  change AERRNO with 6148524 in ERR.
  apply lscps_assume. intros NWX HO HBI. pose proof HR as HR0.
  (* [comment removed for export] *)
  (nelimp (set_ia_same st) 18%nat; intros Isp0 Ilb Ilf Itrs It Ictx Iqp Iqt Iqc Iap Isp Isec Iqth Idep Ifs Ipa Isb Ipb).
  set (st1 := set_ia_inited st) in *.
  pose proof (RTWF_ia' st WF) as WF1. pose proof (RTMODEL_ia' st mo HM) as HM1. pose proof (tpx_ok_of_RTWF st1 WF1) as HX1.
  change (set_ia_inited st) with st1 in WF1, HM1.
  pose proof (rt_prov_ia' st) as PV1. change (set_ia_inited st) with st1 in PV1.
  assert (HIN1 : In (A, n) (st_lb st1)) by (rewrite Ilb; exact HIN).
  assert (HB1 : In (A, n) (all_blocks st1)) by (unfold all_blocks; apply in_or_app; left; exact HIN1).
  pose proof (munch_refl [(lo, bv_unsigned sp); (701568, 701568 + 528432); (1285384, 1285384 + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  eapply lscps_step_evt.
  callxp ltac:(eapply (free_f1_spec internal_allocator_proof get_malloc_ctx_size_proof get_current_pc_proof) with (lo := lo) (st := st) (A := A);
              [exact HR| exact WF| exact MI| reflexivity| lia| exact ST| idtac; lia| unfold F1_DEPTH; lia])
         ltac:(unfold f1_post, A_IA_INSTANCE, A_IA_SIZE, A_IA_INITED; change (set_ia_inited st) with st1; clear ST).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -2128) _ |- _ => rename H into OBJ1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -72) _ |- _ => rename H into BP1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -56) _ |- _ => rename H into FR1 end.
  match goal with H : stk _ _ (bv_unsigned sp + -2112) _ |- _ => rename H into BUF1 end.
  match goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
  match goal with H : RTREP _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into HR1; rename mx into m1 end.
  change (set_ia_inited st) with st1 in HR1.
  pose proof WM as WM01.
  replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) in OBJ1 by lia.
  (* [comment removed for export] *)
  destruct (stk_split asegs m1 _ (bv_unsigned sp + -2112 + 8 * zlen (hook_tr PC0_FREE (st_sp0 st) (bv_unsigned sp) (bv_unsigned ra) tl)) _ BUF1) as [_ BUF2].
  { pose proof (hook_tr_facts PC0_FREE (st_sp0 st) (bv_unsigned sp) (bv_unsigned ra) tl m _ _ _ ltac:(unfold PC0_FREE; lia) ltac:(lia) UWT) as [L _].
    unfold TRACE_MAX_LEN in L. lia. }
  clear BUF1.
  (* [comment removed for export] *)
  assert (REC : bytes_at asegs m1 (bv_unsigned sp - 16) (le8 s0 ++ le8 ra)).
  { pose proof (rw_cells_drop m1 _ [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1) as [[_ RB] _].
    cbn [cells_size Cells.csize Nat.add cells_bytes cbytes] in RB. rewrite app_nil_r in RB.
    replace (bv_unsigned sp + -56 + Z.of_nat 40) with (bv_unsigned sp - 16) in RB by lia. exact RB. }
  assert (UWT1 : uwt m1 (bv_unsigned sp) (ASTACK_TOP (st_sp0 st)) PC0_FREE (bv_unsigned sp) (bv_unsigned s0) 2 tl).
  { eapply uwt_mem; [exact UWT|]. intros a Ha Ha'. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
  pose proof (hook_tr_facts PC0_FREE (st_sp0 st) (bv_unsigned sp) (bv_unsigned ra) tl m _ _ _ ltac:(unfold PC0_FREE; lia) ltac:(lia) UWT) as [TRL TRR].
  pose proof TRL as TRL30. unfold TRACE_MAX_LEN in TRL30.
  remember (hook_tr PC0_FREE (st_sp0 st) (bv_unsigned sp) (bv_unsigned ra) tl) as tr eqn:Etr.
  assert (CP01 : cli_pres st (bv_unsigned sp) m m1).
  { unfold cli_pres. eapply cj_pres_of_munch; [exact MU| exact WM|].
    intros a Ha HC. cbn. split; [| split; [| split; [| exact I]]].
    - intros Hin. apply (below_sp_not_client st WF (bv_unsigned sp) a); [unfold CEIL; lia| exact HC].
    - intros Hin. apply (wstatic_not_client st (bv_unsigned sp) a WF ltac:(unfold CEIL; lia)); [lia| exact HC].
    - intros Hin. apply (wstatic_not_client st (bv_unsigned sp) a WF ltac:(unfold CEIL; lia)); [lia| exact HC]. }
  assert (ES01 : errno_same m m1).
  { eapply errno_same_munch; [exact MU|]. unfold AERRNO, ATP. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  clear MU. pose proof (munch_refl [(lo, bv_unsigned sp); (st_t st + 3168, st_t st + 3168 + 1)] m1) as MU.
  pose proof (wmono_refl asegs m1) as WM1.
  (* [comment removed for export] *)
  pose proof (rw_cells_take m1 _ [C8 (Z_to_bv 64 (bv_unsigned sp + -2112))] [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] OBJ1) as OBa.
  pose proof (rw_cells_drop m1 _ [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 0)] [C4 (Z_to_bv 64 0)] OBJ1) as OBc.
  cbn [cells_size Cells.csize Nat.add] in OBc. replace (bv_unsigned sp + -2128 + Z.of_nat 12) with (bv_unsigned sp + -2116) in OBc by lia.
  (* [comment removed for export] *)
  assert (HG1 : GWIN st1 m1 mo g) by (apply GWIN_ia'; eapply GWIN_mem; [exact HG| exact HO| exact WM01]).
  sepM. callxp ltac:(eapply unwind_ok with (st := st1) (S := bv_unsigned sp + -2128) (pc0 := PC0_FREE) (bp := bv_unsigned sp) (rac := ra) (s0c := s0) (tl := tl) (lo := lo);
    [ exact (RTS_intro _ _ _ _ HR1 WF1 HM1 HG1 HFR (SWIN_ia' st g HSWR))
    | reflexivity| reflexivity| symmetry; apply Z_to_bv_bv_unsigned| reflexivity| reflexivity| reflexivity| exact TP
    | replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) by lia; exact OBJ1
    | eapply wr_at_weaken; [first [exact WR0| eapply wr_at_wmono; [exact WR0| exact WM01]]| lia| unfold BST_SIZE; lia]
    | rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| lia| unfold PC0_FREE; lia
    | exact REC| exact RA1| exact RA2
    | intros _; rewrite Isp0; exact UWT1
    | left; unfold BST_SIZE; lia
    | rewrite unsigned_lit by lia; exact ST1| idtac; lia| rewrite unsigned_lit by lia; unfold AUNWIND_STACK; lia| exact MI1 ])
    ltac:(unfold unwind_post, T_UNWINDING; rewrite !Isp0, !It, !unsigned_lit by lia; rewrite <- !Etr; clear BP1 OBJ1 ST1).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST2 end.
  match goal with H : RTREP st1 ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into HR2; rename mx into m2 end.
  match goal with H : rw_cells _ m2 (bv_unsigned sp + -2128 + 8) _ |- _ => rename H into SZ2 end.
  match goal with H : rw_cells _ m2 (bv_unsigned sp + -2128 + 16) _ |- _ => rename H into TRC2 end.
  match goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
  assert (CP12 : cli_pres st (bv_unsigned sp) m1 m2).
  { eapply (cli_pres_tpz st WF); [| exact MU| exact WM1|]; [unfold CEIL; lia|].
    unfold T_ACACHE, CEIL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  assert (ES02 : errno_same m m2).
  { eapply errno_same_trans; [exact ES01|].
    eapply errno_same_munch; [exact MU|]. unfold AERRNO, ATP. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  clear MU WM1.
  (* [comment removed for export] *)
  assert (SOBJ : rw_cells asegs m2 (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C8 (Z_to_bv 64 (zlen tr))]).
  { apply (proj2 (rw_cells_app m2 _ [C8 _] [C8 _])). split; [exact OBa|]. cbn [cells_size Cells.csize Nat.add].
    apply c44_c8; [lia|].
    apply (proj2 (rw_cells_app m2 _ [C4 _] [C4 _])). split; [exact SZ2|]. cbn [cells_size Cells.csize Nat.add].
    replace (bv_unsigned sp + -2128 + Z.of_nat 8 + Z.of_nat 4) with (bv_unsigned sp + -2116) by lia. exact OBc. }
  clear SZ2 OBa OBc.
  (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 10 lstep. (* [comment removed for export] *)
  apply evt_done. eapply lscps_bind.
  { pose proof (dealloc_core_proof depot_put_proof quarantine_put_proof) as DC. unfold dealloc_core_stmt in DC.
    eapply DC with (st := st1) (A := A) (n := n) (S := bv_unsigned sp + -2128) (tr := tr) (lo := lo); try reflexivity.
    - exact (RTS_intro _ _ _ _ HR2 WF1 HM1 ltac:(apply GWIN_ia'; eapply GWIN_mem; [exact HG| exact HO| exact WM01]) HFR ltac:(apply SWIN_ia'; exact HSWR)).
    - exact HIN1. - rewrite Iqt; exact HQT. - rewrite Iqc; exact HQC. - rewrite Iqp; exact HQP. - rewrite Iap; exact HAP.
    - exact TP.
    - replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) by lia. exact SOBJ.
    - replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2128 + 16) by lia. exact (proj1 TRC2).
    - exact TRL. - exact TRR. - rewrite Itrs. exact ROOM.
    - rewrite unsigned_lit by lia. lia. - unfold BST_SIZE. lia. - rewrite unsigned_lit, Isp0 by lia. lia.
    - rewrite PV1. unfold cost_free. lia.
    - rewrite unsigned_lit by lia. exact ST2. - idtac; lia. - rewrite unsigned_lit by lia. unfold ADEALLOC_STACK. lia.
    - exact MI2. }
  cbv beta. intros ms7 mo7 g7 PO.
  (nelim PO 36%nat; intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m7 st4 -> MI7 ST7 ES27 CP27 GM7 TP7 RTS4 HO7 HB7 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 BO27)
.
  rewrite unsigned_lit in ST7, CP27 by lia.
  replace (ret_pc (Z_to_bv 64 0x54644)) with (Z_to_bv 64 0x54644) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  unfold cli_pres in CP27. rewrite Q1, Q2, Q3, Isp0, Ilb, Ilf in CP27.
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP27) in FR1; [| left; cbn; lia].
  assert (WR7 : wr_at asegs m7 (bv_unsigned sp + -2128) 2128).
  { eapply cj_pres_wr_at; [exact CP27| first [exact WR0| eapply wr_at_wmono; [exact WR0| exact WM01]]| left; lia]. }
  eapply lscps_step_evt. cbv beta delta [wz] in *.
  (* [comment removed for export] *)
  lstep. do 7 lstep. lstep. lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  apply evt_done. apply lscps_done. unfold free_core_post.
  nexists 15%nat. exists m7, st4. split; [reflexivity|]. split; [exact MI7|].
  split.
  { eapply stk_merge; [exact ST7| | lia]. replace (bv_unsigned sp) with (bv_unsigned sp + -2128 + 2128) at 2 by lia.
    apply stk_of_wr_high; [exact WR7| unfold AIMG_HI; lia]. }
  split.
  { eapply rw_cells_same; [exact ERR|]. intros a Ha. cbn [cells_size Cells.csize Nat.add] in Ha.
    replace a with (AERRNO + (a - AERRNO)) by lia. apply ES27. unfold AERRNO, ATP in *. lia. }
  split.
  { unfold cli_pres in *.
    eapply cj_pres_trans; [eapply cj_pres_weaken; [exact CP01| lia| intros b Hb; eapply remove_first_In; exact Hb| auto]|].
    eapply cj_pres_trans; [eapply cj_pres_weaken; [exact CP12| lia| intros b Hb; eapply remove_first_In; exact Hb| auto]|].
    eapply cj_pres_weaken; [exact CP27| lia| auto| auto]. }
  split; [exact GM7|].
  split; [rewrite <- Itrs; exact TP7|].
  split; [exact RTS4|]. split; [exact HO7|]. split; [exact HB7|].
  split; [rewrite Q1; exact Isp0|]. split; [rewrite Q2, Ilb; reflexivity|]. split; [rewrite Q3; exact Ilf|].
  split; [rewrite Q4; exact Iap|]. split; [rewrite Q5; exact Isp|]. split; [rewrite Q6; exact Iqp|].
  split; [exact Q7|]. split; [exact Q8|].
  unfold budget_ok, cost_free in *. lia.
Qed.
End FREE.

(* [comment removed for export] *)
Section FREE_HUB.
Hypothesis internal_allocator_proof : internal_allocator_spec.
Hypothesis get_malloc_ctx_size_proof : get_malloc_ctx_size_spec.
Hypothesis get_current_pc_proof : get_current_pc_spec.
Hypothesis unwind_ok : unwind_spec.
Hypothesis depot_put_proof : depot_put_specS.   (* [comment removed for export] *)
Hypothesis quarantine_put_proof : quarantine_put_spec2.

Theorem art_free_proof : free_lscps_stmt ARTd.
Proof.
  unfold free_lscps_stmt. intros until tl. intros HART HINLB SPB0 ST HCL LO ERR MI TP HA0 COST [RA1 RA2] UWT ROOM.
  (nelim (ARTd_RTS _ _ _ _ _ _ _ _ _ HART) 12%nat; intros st RTS0 HO HB Esp0 Elb Elf Etrs HQ B0 BB HSPB).
  (nelim HQ 5%nat; intros Qap Qsp Qqp Qqt Qqc). pose proof (proj1 (proj2 RTS0)) as WF.
  assert (HIN : In (A, n) (st_lb st)) by (rewrite Elb; exact HINLB).
  subst sp0 LB LF TRS.
  eapply lscps_mono.
  { eapply (free_core_proof internal_allocator_proof get_malloc_ctx_size_proof get_current_pc_proof unwind_ok depot_put_proof quarantine_put_proof)
      with (st := st); try eassumption; unfold cost_free in *; lia. }
  cbv beta. intros ms' mo' g' PO.
  (nelim PO 36%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' st' -> MI' ST' ERR' CP' GM' TP' RTS' HO' HBI' E1 E2 E3 E4 E5 E6 E7 E8 BO').
  (nelim RTS' 6%nat; intros HR' WF' HM' HG' HF' HSW').
  unfold afree_post. nexists 15%nat. exists m', (st_trs st'). split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|].
  rewrite (cb_remove_first st A n WF HIN).
  split; [exact CP'|]. split; [exact GM'|]. split; [exact TP'|].
  eapply (ARTd_intro st'); [exact HR'| exact WF'| exact HM'| exact HO'| exact HBI'| exact HG'| exact HF'| exact E1| exact E2| exact E3| reflexivity| | unfold cost_free in *; lia| | exact HSPB| exact HSW'].
  - unfold QUIET. rewrite E4, E5, E6, E7, E8. repeat split; assumption.
  - unfold budget_ok, cost_free in *. lia.
Qed.
End FREE_HUB.


End CeilWrap.
End RTW_m_free.

(* [comment removed for export] *)
Module RTW_m_free0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_quarantine_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_specs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_i1 RTW_m_f1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_d1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_fz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_alloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_unwind OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma free_d0_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  mem_inv asegs m -> a0 = wz 0 ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 64 <= bv_unsigned sp ->
  evt asegs (fun ms' => exists (a0' a1' a2' a3' a4' a5' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AASAN_FREE) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI -> ST HCL LO.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold AASAN_FREE in *. leaf_prep.
  do 10 lstep. (* [comment removed for export] *)
  carve_frame 64%nat ST.
  do 9 lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  do 8 lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) in * by lia. try rewrite Z_to_bv_bv_unsigned.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => rename H into FR' end.
  release_frame FR' ST (bv_unsigned sp).
  finish; eassumption.
Qed.

Section FREE0.
Hypothesis internal_allocator_proof : internal_allocator_spec.
Hypothesis get_malloc_ctx_size_proof : get_malloc_ctx_size_spec.
Hypothesis get_current_pc_proof : get_current_pc_spec.
Hypothesis unwind_ok : unwind_spec.

Theorem art_free_null_proof : free_null_lscps_stmt ARTd.
Proof.
  unfold free_null_lscps_stmt. intros until tl. intros HART SPB0 ST HCL LO ERR MI TP -> [RA1 RA2] UWT.
  destruct (ARTd_RTS _ _ _ _ _ _ _ _ _ HART) as (st & (HR & WF & HM & HG & HFR & HSWR) & HO & HBI & Esp0 & Elb & Elf & Etrs & HQ & B0 & BB & HSPB).
  pose proof (wb_sp0 st (wf_base_ok st WF)) as SP0. rewrite Esp0 in SP0. unfold AMALLOC_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
  pose proof (bv_unsigned_in_range 64 ra) as RRA. unfold bv_modulus in RRA. cbn in RRA.
  pose proof (t_range st WF) as TR. olin TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all.
  pose proof (stk_wr_at m lo (bv_unsigned sp) (bv_unsigned sp + -2128) 2128 ST ltac:(lia) ltac:(lia)) as WR0.
  change AERRNO with 6148524 in ERR.
  (* [comment removed for export] *)
  pose proof (set_ia_same st) as (Isp0 & Ilb & Ilf & Itrs & It & Ictx & Iqp & Iqt & Iqc & Iap & Isp & Isec & Iqth & Idep & Ifs & Ipa & Isb & Ipb).
  set (st1 := set_ia_inited st) in *.
  pose proof (RTWF_ia' st WF) as WF1. pose proof (RTMODEL_ia' st mo HM) as HM1.
  change (set_ia_inited st) with st1 in WF1, HM1.
  pose proof (rt_prov_ia' st) as PV1. change (set_ia_inited st) with st1 in PV1.
  pose proof (munch_refl [(lo, bv_unsigned sp); (701568, 701568 + 528432); (1285384, 1285384 + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  eapply lscps_step_evt.
  callxp ltac:(eapply (free_f1_spec internal_allocator_proof get_malloc_ctx_size_proof get_current_pc_proof) with (lo := lo) (st := st) (A := 0);
              [exact HR| exact WF| exact MI| reflexivity| lia| exact ST| idtac; lia| unfold F1_DEPTH; lia])
         ltac:(unfold f1_post, A_IA_INSTANCE, A_IA_SIZE, A_IA_INITED; change (set_ia_inited st) with st1).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -2128) _ |- _ => rename H into OBJ1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -56) _ |- _ => rename H into FR1 end.
  match goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
  match goal with H : RTREP _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into HR1; rename mx into m1 end.
  change (set_ia_inited st) with st1 in HR1.
  pose proof WM as WM01.
  replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) in OBJ1 by lia.
  assert (REC : bytes_at asegs m1 (bv_unsigned sp - 16) (le8 s0 ++ le8 ra)).
  { pose proof (rw_cells_drop m1 _ [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1) as [[_ RB] _].
    cbn [cells_size Cells.csize Nat.add cells_bytes cbytes] in RB. rewrite app_nil_r in RB.
    replace (bv_unsigned sp + -56 + Z.of_nat 40) with (bv_unsigned sp - 16) in RB by lia. exact RB. }
  assert (UWT1 : uwt m1 (bv_unsigned sp) (ASTACK_TOP sp0) PC0_FREE (bv_unsigned sp) (bv_unsigned s0) 2 tl).
  { eapply uwt_mem; [exact UWT|]. intros a Ha Ha'. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
  pose proof (hook_tr_facts PC0_FREE sp0 (bv_unsigned sp) (bv_unsigned ra) tl m _ _ _ ltac:(unfold PC0_FREE; lia) ltac:(lia) UWT) as [TRL TRR].
  unfold TRACE_MAX_LEN in TRL.
  assert (CP01 : cli_pres st (bv_unsigned sp) m m1).
  { unfold cli_pres. eapply cj_pres_of_munch; [exact MU| exact WM|].
    intros a Ha HC. cbn. split; [| split; [| split; [| exact I]]].
    - intros Hin. apply (below_sp_not_client st WF (bv_unsigned sp) a); [unfold CEIL; lia| exact HC].
    - intros Hin. apply (wstatic_not_client st (bv_unsigned sp) a WF ltac:(unfold CEIL; lia)); [lia| exact HC].
    - intros Hin. apply (wstatic_not_client st (bv_unsigned sp) a WF ltac:(unfold CEIL; lia)); [lia| exact HC]. }
  assert (ES01 : errno_same m m1).
  { eapply errno_same_munch; [exact MU|]. unfold AERRNO, ATP. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  clear MU. pose proof (munch_refl [(lo, bv_unsigned sp); (st_t st + 3168, st_t st + 3168 + 1)] m1) as MU.
  pose proof (wmono_refl asegs m1) as WM1.
  (* [comment removed for export] *)
  assert (HG1 : GWIN st1 m1 mo g) by (apply GWIN_ia'; eapply GWIN_mem; [exact HG| exact HO| exact WM01]).
  callxp ltac:(eapply unwind_ok with (st := st1) (S := bv_unsigned sp + -2128) (pc0 := PC0_FREE) (bp := bv_unsigned sp) (rac := ra) (s0c := s0) (tl := tl) (lo := lo);
    [ exact (RTS_intro _ _ _ _ HR1 WF1 HM1 HG1 HFR (SWIN_ia' st g HSWR))
    | reflexivity| reflexivity| symmetry; apply Z_to_bv_bv_unsigned| reflexivity| reflexivity| reflexivity| exact TP
    | replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) by lia; exact OBJ1
    | eapply wr_at_weaken; [first [exact WR0| eapply wr_at_wmono; [exact WR0| exact WM01]]| lia| unfold BST_SIZE; lia]
    | rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| lia| unfold PC0_FREE; lia
    | exact REC| exact RA1| exact RA2
    | intros _; rewrite Isp0, Esp0; exact UWT1
    | left; unfold BST_SIZE; lia
    | rewrite unsigned_lit by lia; exact ST1| idtac; lia| rewrite unsigned_lit by lia; unfold AUNWIND_STACK; lia| exact MI1 ])
    ltac:(unfold unwind_post, T_UNWINDING; rewrite !Isp0, !Esp0, !It, !unsigned_lit by lia).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST2 end.
  match goal with H : RTREP st1 ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into HR2; rename mx into m2 end.
  match goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
  assert (CP12 : cli_pres st (bv_unsigned sp) m1 m2).
  { eapply (cli_pres_tpz st WF); [| exact MU| exact WM1|]; [unfold CEIL; lia|].
    unfold T_ACACHE, CEIL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  assert (ES02 : errno_same m m2).
  { eapply errno_same_trans; [exact ES01|].
    eapply errno_same_munch; [exact MU|]. unfold AERRNO, ATP. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  clear MU WM1.
  (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp + -2128 - 64, bv_unsigned sp + -2128)] m2) as MU. pose proof (wmono_refl asegs m2) as WM2.
  callxp ltac:(eapply free_d0_spec with (lo := lo); [exact MI2| reflexivity| rewrite unsigned_lit by lia; exact ST2| idtac; lia| rewrite unsigned_lit by lia; lia])
         ltac:(rewrite !unsigned_lit by lia).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST3 end.
  match goal with H : mem_inv _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI3; rename mx into m3 end.
  pose proof HR2 as HR3. rtrep_high HR3 WF1 MU WM2.
  assert (CP23 : cli_pres st (bv_unsigned sp) m2 m3).
  { eapply (cli_pres_tpz st WF); [| exact MU| exact WM2|]; [unfold CEIL; lia|]. constructor; [cbn [fst snd]; unfold CEIL; lia| constructor]. }
  assert (ES03 : errno_same m m3).
  { eapply errno_same_trans; [exact ES02|]. eapply errno_same_munch; [exact MU|]. constructor; [cbn [fst snd]; unfold AERRNO, ATP; lia| constructor]. }
  assert (HG3 : GWIN st1 m3 mo g) by (apply GWIN_ia'; eapply GWIN_mem; [exact HG| exact HO| exact WM01]).
  assert (WR3 : wr_at asegs m3 (bv_unsigned sp + -2128) 2128) by (first [exact WR0| eapply wr_at_wmono; [exact WR0| exact WM01]]).
  clear MU WM2.
  replace (ret_pc (Z_to_bv 64 0x54644)) with (Z_to_bv 64 0x54644) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (* [comment removed for export] *)
  lstep. do 7 lstep. lstep. lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  apply evt_done. apply lscps_done. unfold afree_null_post.
  do 15 eexists. exists m3. split; [reflexivity|]. split; [exact MI3|].
  split.
  { eapply stk_merge; [exact ST3| | lia]. replace (bv_unsigned sp) with (bv_unsigned sp + -2128 + 2128) at 2 by lia.
    apply stk_of_wr_high; [exact WR3| unfold AIMG_HI; lia]. }
  split; [exact ERR|].
  split.
  { unfold cli_pres in *. rewrite Esp0, Elb, Elf in CP01, CP12, CP23.
    eapply cj_pres_trans; [exact CP01|]. eapply cj_pres_trans; [exact CP12| exact CP23]. }
  split; [apply gmono_refl || (unfold gmono; auto)|].
  eapply (ARTd_intro st1); [exact HR3| exact WF1| exact HM1| exact HO| exact HBI| exact HG3| exact HFR
    | rewrite Isp0; exact Esp0| rewrite Ilb; exact Elb| rewrite Ilf; exact Elf| rewrite Itrs; exact Etrs
    | unfold QUIET in *; rewrite Iap, Isp, Iqp, Iqt, Iqc; exact HQ| exact B0| rewrite PV1; exact BB| exact HSPB| exact (SWIN_ia' st g HSWR)].
Qed.
End FREE0.


End CeilWrap.
End RTW_m_free0.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstate.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_iface2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_drv.
Module RTW_m_freeN.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_quarantine_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_quarantine_iface2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_fz.RTW_m_lbz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_specs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_i1 RTW_m_f1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_d1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_q1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_fz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_alloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RT_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_unwind OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_dcore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_dcore RTW_m_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstate.RT_fresh OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_iface2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_drv.
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

Definition fx_post (st : rtstate) (P : machine_state -> Model -> lghost -> Prop) : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' => P ms' mo' g' /\ (fresh_x24 st -> exists st'', RTREP st'' (ms_mem ms') /\ RTWF st'' /\ fresh_x24 st'').

Definition dealloc_core_fx_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (A n S : Z) (tr : list Z) (lo : Z),
  RTS st m mo g -> In (A, n) (st_lb st) -> st_qtmp st = [] -> st_qcur st = [] -> st_qpend st = [] -> st_apend st = [] ->
  a0 = wz A_ALLOC -> a1 = wz A -> a2 = wz 0 -> a3 = wz 0 -> a4 = wz S -> a5 = wz 1 -> tp = wz ATP ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (wz (S + 16)); C8 (wz (zlen tr))] -> cells_at asegs m (S + 16) (trace_cells tr) ->
  1 <= zlen tr <= TRACE_MAX_LEN -> Forall (fun pc => 0 <= pc < 2^64) tr -> trs_room tr (st_trs st) ->
  bv_unsigned sp <= S -> S + BST_SIZE <= 2^64 -> bv_unsigned sp <= st_sp0 st ->
  rt_prov st + cost_free <= g_res g ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + ADEALLOC_STACK <= bv_unsigned sp ->
  mem_inv asegs m ->
  LSCPS asegs (fx_post st (dealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st tr A n lo m g))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ADEALLOCATE) fc None m (seg_rom asegs)) mo g.

Definition free_core_fx_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (A n lo : Z) (errv : word) (tl : list Z),
  RTS st m mo g -> In (A, n) (st_lb st) -> st_qtmp st = [] -> st_qcur st = [] -> st_qpend st = [] -> st_apend st = [] ->
  bv_unsigned sp <= st_sp0 st ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  rw_cells asegs m AERRNO [C4 errv] ->
  mem_inv asegs m ->
  tp = wz ATP -> a0 = wz A ->
  rt_prov st + cost_free <= g_res g ->
  4096 <= bv_unsigned ra -> bv_unsigned ra <> PC0_FREE ->
  uwt m (bv_unsigned sp) (ASTACK_TOP (st_sp0 st)) PC0_FREE (bv_unsigned sp) (bv_unsigned s0) 2 tl ->
  trs_room (hook_tr PC0_FREE (st_sp0 st) (bv_unsigned sp) (bv_unsigned ra) tl) (st_trs st) ->
  LSCPS asegs (fx_post st (free_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st
                 (hook_tr PC0_FREE (st_sp0 st) (bv_unsigned sp) (bv_unsigned ra) tl) A n lo errv m g))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz AFREE) fc None m (seg_rom asegs)) mo g.

Section FREEN.
Hypothesis internal_allocator_proof : internal_allocator_spec.
Hypothesis get_malloc_ctx_size_proof : get_malloc_ctx_size_spec.
Hypothesis get_current_pc_proof : get_current_pc_spec.
Hypothesis unwind_ok : unwind_spec.
Hypothesis depot_put_proof : depot_put_specS.
Hypothesis quarantine_put_proof : quarantine_put_spec2.

Theorem dealloc_core_fx_proof : dealloc_core_fx_stmt.
Proof.
  unfold dealloc_core_fx_stmt. intros until lo. intros (HR & WF & HM & HG & HFR & HSWR) HIN HQT HQC HQP HAP -> -> -> -> -> -> TP SOBJ STR TRL TRR ROOM HS1 HS2 SPB0 COST ST HCL LO MI.
  pose proof (wb_sp0 st (wf_base_ok st WF)) as SP0. unfold ADEALLOC_STACK in LO. unfold BST_SIZE in HS2. unfold cost_free in COST.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
  pose proof (t_range st WF) as TR. olin TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all. pose proof TRL as TRL30. unfold TRACE_MAX_LEN in TRL30.
  assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact HIN).
  pose proof (block_geom st WF A n HB) as (Gn & GA & GK & GX & GY & GCE & GL16 & GH16 & GEA & _). unfold usz in GY. unfold KHIGHMEM_BEG, AIMG_HI in GK. olin_all.
  pose proof (block_extra st WF A n HB) as (E8 & EAB & EABA & EMB & ERZ32). pose proof (rz_size_range n) as [RZ _].
  pose proof (fp_nonneg n ltac:(lia)) as FPN. pose proof (tpx_ok_of_RTWF st WF) as HX. pose proof (proj1 HX) as CT.
  apply lscps_assume. intros NWX HO HBI.
  pose proof (wmono_refl asegs m) as WM01.
  eapply lscps_step_evt. cbv beta delta [wz] in *.
  (* [comment removed for export] *)
  pose proof (rr_live st m HR A n HIN) as RB2.
  assert (SHL2 : bprim n = true -> rw_cells asegs m (SH (b_lo A n)) (zcells (sh_live n))).
  { intros BP. destruct RB2 as (_ & _ & _ & _ & BS). unfold R_bshadow in BS. rewrite BP in BS. exact BS. }
  destruct (rr_live st m HR A n HIN) as ((b1 & cid & HC2 & HB1ok) & _ & _ & V2 & _).
  unfold hdr_cells, hdr_state_live, b_chunk_beg in HC2. replace (A - 16) with (A + -16) in HC2 by lia.
  destruct (vis_c8 m _ _ A V2 ltac:(lia) ltac:(lia)) as [uw UW2].
  destruct (rr_thread st m HR) as (TV2 & _).
  destruct (vis_c8 m _ _ (st_t st + 2824) TV2 ltac:(lia) ltac:(lia)) as [sj3 TS3].
  destruct (vis_c8 m _ _ (st_t st + 2832) TV2 ltac:(lia) ltac:(lia)) as [sj4 TS4].
  assert (TS2 : rw_cells asegs m (st_t st + 2824) [C8 sj3; C8 sj4]).
  { apply (proj2 (rw_cells_app m (st_t st + 2824) [C8 sj3] [C8 sj4])). split; [exact TS3|]. cbn [cells_size Cells.csize Nat.add].
    replace (st_t st + 2824 + Z.of_nat 8) with (st_t st + 2832) by lia. exact TS4. }
  clear TS3 TS4 TV2.
  pose proof (leafc_of_RTREP st m HR) as LC2.
  pose proof (t_vs_block st WF A n HB) as TB.
  destruct (wb_ctx_loose st (wf_base_ok st WF)) as (cb & ck & CL1 & CL2 & CL3).
  pose proof (loose_blockfree st WF cb ck CL1 A n HB) as CBF. pose proof (loose0_range st WF cb ck CL1) as (CR1 & CR2 & CR3 & CR4). unfold KHIGHMEM_BEG, AIMG_HI in CR1. olin_all.
  pose proof (munch_refl [(A + -16, A + -12); (A, A + 8); (st_t st + 2824, st_t st + 2840); (bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM2.
  (* [comment removed for export] *)
  sepM. callxp ltac:(eapply free_d1_spec with (st := st) (A := A) (n := n) (S := S) (lo := lo);
    [ exact LC2| exact WF| exact MI| exact TP| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
    | lia| exact GA| unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| lia| exact HB1ok
    | (lia_on GA GX GY GH16 TB)| (lia_on GA GX GY GH16 CL2 CL3 CBF)
    | exact ST| idtac; lia| lia
    | exact HC2| exact UW2| exact TS2 ])
    ltac:(unfold AQCHUNK, A_ALLOC, CHUNK_QUARANTINE; rewrite ?unsigned_lit by lia; clear TS2 UW2 HC2; clear V2 ST).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST3 end.
  match goal with H : mem_inv _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI3; rename mx into m3 end.
  match goal with H : rw_cells _ m3 (A + -16) _ |- _ => rename H into HC3 end.
  (* [comment removed for export] *)
  pose proof (st_freeP_same st A n) as (Fsp0 & Flb & Flf & Ftrs & Fap & Fsp & Fsec & Fqp & Fqt & Fqc & Fqth & Fqg & Fdep & Ffs & Ft & Fsb & Fpb & Fpa & Fctx & _).
  set (st2 := st_freeP st A n) in *.
  assert (WF2 : RTWF st2) by (apply RTWF_freeP'; [exact WF| exact HIN| exact HQP]).
  pose proof (RTMODEL_freeP' st A n mo HM) as HM2. change (st_freeP st A n) with st2 in HM2.
  pose proof (tpx_ok_of_RTWF st2 WF2) as HX2.
  pose proof (rt_prov_freeP' st A n HIN) as PV2. change (st_freeP st A n) with st2 in PV2.
  assert (TX0 : 0 <= (if is_cl24 n then CL24_TAX else 0)) by (unfold CL24_TAX; destruct (is_cl24 n); lia).
  assert (HINQ2 : In (A, n) (st_qpend st2)) by (rewrite Fqp; left; reflexivity).
  assert (HB2 : In (A, n) (all_blocks st2)) by (unfold all_blocks; rewrite !in_app_iff; right; right; exact HINQ2).
  assert (HR3 : RTREP st2 m3).
  { eapply (RTREP_freeP' st WF HX A n HIN _ m m3); [| exact MU| exact WM2| exact HR|].
    - unfold lbz_ok. unfold T_STATS, T_UNWINDING, CEIL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia.
    - eapply (R_block_to_pend st WF A n HB _); [| exact MU| exact WM2| exact RB2| | exact HB1ok].
      + repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia.
      + unfold b_chunk_beg, hdr_cells, hdr_state_quar. replace (A - 16) with (A + -16) by lia. exact HC3. }
  assert (CP23 : cli_pres st2 (bv_unsigned sp) m m3).
  { eapply (cli_pres_qz st2 WF2 A n (or_intror HINQ2) (bv_unsigned sp)); [unfold CEIL; lia| exact MU| exact WM2|].
    unfold lbzc_ok. rewrite Ft. unfold T_STATS, T_UNWINDING, CEIL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  assert (ES23 : errno_same m m3).
  { eapply errno_same_munch; [exact MU|]. unfold AERRNO, ATP. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  assert (LC3 : leafc st2 m3).
  { apply leafc_freeP'. eapply (leafc_keep st _ m m3 MU WM2); [| exact LC2]. olin_all. unfold AIMG_LO, AIMG_HI.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (lia_on GA GX GY GH16 ALx CT CL2 CL3 CBF OLx HCL LO CR3). }
  assert (SO3 : rw_cells asegs m3 S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 (zlen tr))]).
  { first [exact SOBJ| eapply rw_cells_transport; [exact SOBJ| exact MU| exact WM2|]; cbn; lia]. }
  assert (STR3 : cells_at asegs m3 (S + 16) (trace_cells tr)).
  { first [exact STR| eapply (ro_cells_transport asegs _ m m3); [exact STR| exact MU|]; cbn [disjoint_from]; rewrite trace_cells_size; (lia_on HS1 HCL LO SP0 TR GA GX GY GH16 ALx E8 CT TB CL2 CL3 CBF CR3 OLx1)]. }
  assert (SHL3 : bprim n = true -> rw_cells asegs m3 (SH (b_lo A n)) (zcells (sh_live n))).
  { intros BP. eapply rw_cells_transport; [exact (SHL2 BP)| exact MU| exact WM2|].
    rewrite zcells_size, sh_live_len by lia. apply (LZ_block_self_shadow st WF A n HB).
    unfold lbz_ok. unfold T_STATS, T_UNWINDING, CEIL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  clear MU WM2. try clear SOBJ. try clear STR. try clear HC2. try clear UW2. try clear TS2. try clear RB2. try clear V2. try clear LC2.
  (* [comment removed for export] *)
  destruct (rr_thread st2 m3 HR3) as (_ & (tj1 & tj2 & tj3 & tj4 & tj5 & TT) & _ & _ & TID & _).
  pose proof (rw_cells_merge asegs m3 (st_t st2) [C8 (wz (st_ctx st2))] _ [] ltac:(rewrite app_nil_r; exact TT)) as TT3.
  cbn [cells_size cells_bytes Cells.csize cbytes app Nat.add length] in TT3. clear TT.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m3) as MU. pose proof (wmono_refl asegs m3) as WM3.
  sepM. callxp ltac:(eapply free_q1_spec with (st := st2) (A := A) (n := n) (S := S) (lo := lo) (tr := tr);
    [ exact LC3| exact WF2| exact MI3| exact TP| reflexivity| reflexivity| reflexivity| reflexivity
    | lia| unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| lia| lia| lia
    | exact ST3| idtac; lia| lia
    | exact HC3| exact TT3| exact TID| exact SO3 ])
    ltac:(unfold ADEPOT_PUT, A_ALLOC; rewrite ?unsigned_lit by lia; clear TID; clear ST3).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST4 end.
  match goal with H : mem_inv _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI4; rename mx into m4 end.
  match goal with H : rw_cells _ m4 (bv_unsigned sp - 48) _ |- _ => rename H into FRQ4 end.
  pose proof HR3 as HR4. rtrep_high HR4 WF2 MU WM3.
  assert (CP34 : cli_pres st2 (bv_unsigned sp) m3 m4).
  { eapply (cli_pres_tpz st2 WF2); [| exact MU| exact WM3|]; [unfold CEIL; lia|]. constructor; [cbn [fst snd]; unfold CEIL; lia| constructor]. }
  assert (ES34 : errno_same m3 m4).
  { eapply errno_same_munch; [exact MU|]. constructor; [cbn [fst snd]; unfold AERRNO, ATP; lia| constructor]. }
  assert (STR4 : cells_at asegs m4 (S + 16) (trace_cells tr)).
  { first [exact STR3| eapply (ro_cells_transport asegs _ m3 m4); [exact STR3| exact MU|]; cbn [disjoint_from]; rewrite trace_cells_size; lia]. }
  assert (HG4 : GWIN st2 m4 mo g) by (apply GWIN_freeP'; eapply GWIN_mem; [exact HG| exact HO| exact WM01]).
  assert (SHL4 : bprim n = true -> rw_cells asegs m4 (SH (b_lo A n)) (zcells (sh_live n))).
  { intros BP. eapply rw_cells_transport; [exact (SHL3 BP)| exact MU| exact WM3|].
    rewrite zcells_size, sh_live_len by lia. apply (LZ_block_self_shadow st2 WF2 A n HB2).
    constructor; [unfold lbz_ok; cbn [fst snd]; right; right; unfold CEIL; lia| constructor]. }
  clear MU WM3. try clear STR3.
  (* [comment removed for export] *)
  apply evt_done. eapply lscps_bind.
  { pose proof depot_put_proof as DP. unfold depot_put_specS in DP.
    eapply DP with (lo := lo) (P := S + 16) (tr := tr) (st := st2); try reflexivity.
    - exact (RTS_intro _ _ _ _ HR4 WF2 HM2 HG4 HFR (SWIN_freeP' st A n g HSWR)).
    - exact TRL. - exact TRR.
    - exact STR4.
    - right. rewrite unsigned_lit by lia. lia.
    - idtac. lia.
    - unfold TRACE_MAX_LEN in TRL. lia.
    - exact TP.
    - rewrite Ftrs. exact ROOM.
    - lia.
    - rewrite unsigned_lit by lia. exact ST4. - idtac; lia. - rewrite unsigned_lit by lia. unfold ADEPOT_STACK. lia.
    - exact MI4. }
  cbv beta. intros ms5 mo5 g5 PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m5 & st3 & -> & MI5 & id & -> & Hid
                  & SBD & TP3 & RTS3 & ST5 & CP45 & RF45 & GM5 & BO45).
  rewrite unsigned_lit in ST5, CP45, RF45 by lia.
  replace (ret_pc (Z_to_bv 64 0x360e0)) with (Z_to_bv 64 0x360e0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  destruct RTS3 as (HR5 & WF3 & HM3 & HG5 & HF3 & HSW3).
  destruct SBD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & D26).
  assert (HINQ3 : In (A, n) (st_qpend st3)) by (rewrite D24; exact HINQ2).
  assert (HB3 : In (A, n) (all_blocks st3)) by (unfold all_blocks; rewrite !in_app_iff; right; right; exact HINQ3).
  pose proof (tpx_ok_of_RTWF st3 WF3) as HX3.
  assert (SHL5 : bprim n = true -> rw_cells asegs m5 (SH (b_lo A n)) (zcells (sh_live n))).
  { intros BP. destruct (proj2 (rr_quar st3 m5 HR5) A n HINQ3) as (_ & _ & _ & _ & BS5). unfold R_bshadow in BS5. rewrite BP in BS5.
    assert (SHB' : SH (b_lo A n) + sh_tot n <= SH CEIL).
    { unfold sh_tot. rewrite <- rt_SH_aligned_add by (Z.div_mod_to_equations; lia). apply rt_SH_mono. change (b_lo A n + asz n) with (b_hi A n). unfold CEIL. lia. }
    rewrite SH_CEIL in SHB'.
    pose proof (rt_SH_mono 0 (b_lo A n) ltac:(lia)) as SHB0'. change (SH 0) with 0x7fff8000 in SHB0'.
    eapply (rw_cells_rt_frame _ _ _ m4 m5 _ _ _ _ RF45 (SHL4 BP) BS5); [lia| rewrite zcells_size, sh_live_len by lia; lia| lia|].
    rewrite zcells_size, sh_live_len by lia. intros a Ha. split; [lia|].
    apply (band_notin_depot_fp st3 a WF3). unfold KLOWSHADOW_BEG, KHIGHMEM_BEG. lia. }
  (* [comment removed for export] *)
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP45) in FRQ4; [| left; cbn; lia].
  assert (ES45 : errno_same m4 m5).
  { eapply errno_same_rt_frame; [exact RF45| unfold AERRNO, ATP; lia|]. intros a Ha. apply (errno_notin_depot_fp st3 a WF3 Ha). }
  destruct (proj2 (rr_quar st3 m5 HR5) A n HINQ3) as ((b1' & cid' & HC5 & HB1ok') & _ & _ & V5 & _).
  unfold hdr_cells, hdr_state_quar, b_chunk_beg in HC5. replace (A - 16) with (A + -16) in HC5 by lia.
  destruct (vis_c8 m5 _ _ A V5 ltac:(lia) ltac:(lia)) as [fw UW5].
  apply lscps_assume. intros _ HO5 HB5.
  eapply lscps_step_evt. cbv beta delta [wz] in *.
  (* [comment removed for export] *)
  pose proof (munch_refl [(A, A + 8)] m5) as MU. pose proof (wmono_refl asegs m5) as WM5.
  rewrite <- D16.
  sepM. callxp ltac:(eapply free_q2_spec with (st := st3) (A := A) (n := n) (S := S) (id := id);
    [ exact MI5| reflexivity| exact Hid| lia| unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia
    | rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
    | exact HC5| exact UW5| rewrite unsigned_lit by lia; exact FRQ4 ])
    ltac:(unfold AQPUT, A_QUAR, A_ALLOC; rewrite !unsigned_lit by lia; clear UW5; clear V5).
  cbv beta delta [wz] in *.
  match goal with H : mem_inv _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI6; rename mx into m6 end.
  assert (SHB : SH (b_lo A n) + sh_tot n <= SH CEIL).
  { unfold sh_tot. rewrite <- rt_SH_aligned_add by (Z.div_mod_to_equations; (lia_on GA GX GY GH16 GEA E8 CT TB CL2 CL3 CBF H H0 H9 H19)). apply rt_SH_mono. change (b_lo A n + asz n) with (b_hi A n). unfold CEIL. lia. }
  rewrite SH_CEIL in SHB.
  pose proof (rt_SH_mono 0 (b_lo A n) ltac:(lia)) as SHB0. change (SH 0) with 0x7fff8000 in SHB0.   (* [comment removed for export] *)
  assert (HR6 : RTREP st3 m6).
  { eapply (lbz_all st3 WF3 HX3 A n HB3 [(A, A + 8)] ltac:(constructor; [unfold lbz_ok; cbn [fst snd]; left; lia| constructor]) m5 m6 MU WM5 HR5).
    unfold WOK_block, b_chunk_beg.
    split; [cbn; lia|]. split; [intros HRZ; cbn; specialize (ERZ32 HRZ); unfold b_alloc_beg in *; lia|].
    split; [intros EP; specialize (EMB EP); pose proof EMB as EMB'; unfold b_map_beg, SEC_RZ, SEC_HDR in EMB'; cbn; lia|].
    cbn. lia. }
  assert (CP56 : cli_pres st3 (bv_unsigned sp) m5 m6).
  { eapply (cli_pres_qz st3 WF3 A n (or_intror HINQ3) (bv_unsigned sp)); [unfold CEIL; lia| exact MU| exact WM5|].
    constructor; [| constructor]. unfold lbzc_ok. cbn [fst snd]. left. lia. }
  assert (ES56 : errno_same m5 m6).
  { eapply errno_same_munch; [exact MU|]. constructor; [cbn [fst snd]; unfold AERRNO, ATP; lia| constructor]. }
  assert (HG6 : GWIN st3 m6 mo5 g5) by (eapply GWIN_mem; [exact HG5| exact HO5| exact WM5]).
  match goal with H : stk _ m6 lo _ |- _ => rename H into ST6 end.
  match goal with H : rw_cells _ m6 (bv_unsigned sp - 48) _ |- _ => rename H into FRQ6 end.
  replace (bv_unsigned sp - 48 + 48) with (bv_unsigned sp) by lia.
  release_frame FRQ6 ST6 (bv_unsigned sp).
  assert (SHL6 : bprim n = true -> rw_cells asegs m6 (SH (b_lo A n)) (zcells (sh_live n))).
  { intros BP. eapply rw_cells_transport; [exact (SHL5 BP)| exact MU| exact WM5|].
    rewrite zcells_size, sh_live_len by lia. apply (LZ_block_self_shadow st3 WF3 A n HB3).
    constructor; [unfold lbz_ok; cbn [fst snd]; left; lia| constructor]. }
  clear MU WM5.
  (* [comment removed for export] *)
  apply evt_done. eapply lscps_bind.
  { pose proof quarantine_put_proof as QP. unfold quarantine_put_spec2 in QP.
    eapply QP with (lo := lo) (st := st3) (A := A) (n := n) (S := S); try reflexivity.
    - exact (RTS_intro _ _ _ _ HR6 WF3 HM3 HG6 HF3 HSW3).
    - exact HINQ3.
    - rewrite D25, Fqt. exact HQT.
    - rewrite D26, Fqc. exact HQC.
    - rewrite D22, Fap. exact HAP.   (* [comment removed for export] *)
    - exact SHL6.   (* [comment removed for export] *)
    - exact TP.
    - rewrite ?unsigned_lit by lia. rewrite D1, Fsp0. lia.   (* [comment removed for export] *)
    - unfold budget_ok in BO45. unfold cost_free. lia.
    - rewrite unsigned_lit by lia. exact ST6. - idtac; lia. - rewrite unsigned_lit by lia. unfold AQPUT_STACK. lia.
    - exact MI6. }
  cbv beta. intros ms7 mo7 g7 PO.
  destruct PO as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m7 & st4 & -> & MI7
                  & QR & RTS4 & ST7 & CP67 & ES67 & GM7 & BO67).
  rewrite unsigned_lit in ST7, CP67 by lia.
  destruct QR as (SQ & Eqp4 & Eqt4 & Eqc4 & FRESHK).
  destruct SQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & Q18).
  apply lscps_assume. intros _ HO7 HB7. try rewrite Z_to_bv_bv_unsigned.
  apply lscps_done. split.
  2:{ intros FX0. exists st4. destruct RTS4 as (HRx & WFx & _). cbn [MS ms_mem]. split; [exact HRx| split; [exact WFx|]].
      intros c Hc H24. apply FRESHK; [exact Hc| exact H24|]. specialize (FX0 c Hc H24).
      assert (SFr : st_regions (st_freeP st A n) = st_regions st) by (destruct st; reflexivity).
      assert (SFc : st_cache (st_freeP st A n) = st_cache st) by (destruct st; reflexivity).
      unfold fresh_cls, rg, cch in *. rewrite D4, D6. unfold st2. rewrite SFr, SFc. exact FX0. }
  unfold dealloc_post.
  do 15 eexists. exists m7, st4. split; [reflexivity|]. split; [exact MI7|]. split; [exact ST7|].
  split.
  { exact (errno_same_trans _ _ _ (errno_same_trans _ _ _ (errno_same_trans _ _ _ (errno_same_trans _ _ _ ES23 ES34) ES45) ES56) ES67). }
  split.
  { unfold cli_pres in *.
    rewrite Q1, Q16, Q10, D1, D21, D15. rewrite D1, D21, D15 in CP56, CP67.
    eapply cj_pres_trans; [exact CP23|]. eapply cj_pres_trans; [exact CP34|].
    eapply cj_pres_trans; [eapply cj_pres_weaken; [exact CP45| lia| auto| auto]|].
    eapply cj_pres_trans; [exact CP56| exact CP67]. }
  split; [eapply gmono_trans; [exact GM5| exact GM7]|].
  split; [rewrite Q6, <- Ftrs; exact TP3|].
  split; [exact RTS4|]. split; [exact HO7|]. split; [exact HB7|].
  split; [rewrite Q1, D1; exact Fsp0|].
  split; [rewrite Q16, D21; exact Flb|].
  split; [rewrite Q10, D15; exact Flf|].
  split; [rewrite Q17, D22; exact Fap|].
  split; [rewrite Q18, D23; exact Fsp|].
  split; [rewrite Eqp4, D24, Fqp; cbn [remove_first]; rewrite (proj2 (ck_eqb_eq _ _) eq_refl); reflexivity|].
  split; [exact Eqt4|]. split; [exact Eqc4|].
  unfold budget_ok, cost_free in *. lia.
Qed.

Theorem free_core_fx_proof : free_core_fx_stmt.
Proof.
  unfold free_core_fx_stmt. intros until tl. intros (HR & WF & HM & HG & HFR & HSWR) HIN HQT HQC HQP HAP SPB0 ST HCL LO ERR MI TP -> COST RA1 RA2 UWT ROOM.
  pose proof (wb_sp0 st (wf_base_ok st WF)) as SP0. unfold AMALLOC_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
  pose proof (bv_unsigned_in_range 64 ra) as RRA. unfold bv_modulus in RRA. cbn in RRA.
  pose proof (t_range st WF) as TR. olin TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all.
  assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact HIN).
  pose proof (block_geom st WF A n HB) as (Gn & GA & GK & GX & GY & GCE & GL16 & GH16 & GEA & _). unfold usz in GY. unfold KHIGHMEM_BEG, AIMG_HI in GK. olin_all.
  pose proof (block_extra st WF A n HB) as (E8 & EAB & EABA & EMB & ERZ32). pose proof (rz_size_range n) as [RZ _].
  pose proof (fp_nonneg n ltac:(lia)) as FPN. unfold cost_free in COST.
  pose proof (stk_wr_at m lo (bv_unsigned sp) (bv_unsigned sp + -2128) 2128 ST ltac:(lia) ltac:(lia)) as WR0.
  change AERRNO with 6148524 in ERR.
  apply lscps_assume. intros NWX HO HBI. pose proof HR as HR0.
  (* [comment removed for export] *)
  pose proof (set_ia_same st) as (Isp0 & Ilb & Ilf & Itrs & It & Ictx & Iqp & Iqt & Iqc & Iap & Isp & Isec & Iqth & Idep & Ifs & Ipa & Isb & Ipb).
  set (st1 := set_ia_inited st) in *.
  pose proof (RTWF_ia' st WF) as WF1. pose proof (RTMODEL_ia' st mo HM) as HM1. pose proof (tpx_ok_of_RTWF st1 WF1) as HX1.
  change (set_ia_inited st) with st1 in WF1, HM1.
  pose proof (rt_prov_ia' st) as PV1. change (set_ia_inited st) with st1 in PV1.
  assert (HIN1 : In (A, n) (st_lb st1)) by (rewrite Ilb; exact HIN).
  assert (HB1 : In (A, n) (all_blocks st1)) by (unfold all_blocks; apply in_or_app; left; exact HIN1).
  pose proof (munch_refl [(lo, bv_unsigned sp); (701568, 701568 + 528432); (1285384, 1285384 + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  eapply lscps_step_evt.
  sepM. callxp ltac:(eapply (free_f1_spec internal_allocator_proof get_malloc_ctx_size_proof get_current_pc_proof) with (lo := lo) (st := st) (A := A);
              [exact HR| exact WF| exact MI| reflexivity| lia| exact ST| idtac; lia| unfold F1_DEPTH; lia])
         ltac:(unfold f1_post, A_IA_INSTANCE, A_IA_SIZE, A_IA_INITED; change (set_ia_inited st) with st1; clear ST).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -2128) _ |- _ => rename H into OBJ1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -72) _ |- _ => rename H into BP1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -56) _ |- _ => rename H into FR1 end.
  match goal with H : stk _ _ (bv_unsigned sp + -2112) _ |- _ => rename H into BUF1 end.
  match goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
  match goal with H : RTREP _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into HR1; rename mx into m1 end.
  change (set_ia_inited st) with st1 in HR1.
  pose proof WM as WM01.
  replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) in OBJ1 by lia.
  (* [comment removed for export] *)
  destruct (stk_split asegs m1 _ (bv_unsigned sp + -2112 + 8 * zlen (hook_tr PC0_FREE (st_sp0 st) (bv_unsigned sp) (bv_unsigned ra) tl)) _ BUF1) as [_ BUF2].
  { pose proof (hook_tr_facts PC0_FREE (st_sp0 st) (bv_unsigned sp) (bv_unsigned ra) tl m _ _ _ ltac:(unfold PC0_FREE; lia) ltac:(lia) UWT) as [L _].
    unfold TRACE_MAX_LEN in L. lia. }
  clear BUF1.
  (* [comment removed for export] *)
  assert (REC : bytes_at asegs m1 (bv_unsigned sp - 16) (le8 s0 ++ le8 ra)).
  { pose proof (rw_cells_drop m1 _ [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1) as [[_ RB] _].
    cbn [cells_size Cells.csize Nat.add cells_bytes cbytes] in RB. rewrite app_nil_r in RB.
    replace (bv_unsigned sp + -56 + Z.of_nat 40) with (bv_unsigned sp - 16) in RB by lia. exact RB. }
  assert (UWT1 : uwt m1 (bv_unsigned sp) (ASTACK_TOP (st_sp0 st)) PC0_FREE (bv_unsigned sp) (bv_unsigned s0) 2 tl).
  { eapply uwt_mem; [exact UWT|]. intros a Ha Ha'. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
  pose proof (hook_tr_facts PC0_FREE (st_sp0 st) (bv_unsigned sp) (bv_unsigned ra) tl m _ _ _ ltac:(unfold PC0_FREE; lia) ltac:(lia) UWT) as [TRL TRR].
  pose proof TRL as TRL30. unfold TRACE_MAX_LEN in TRL30.
  remember (hook_tr PC0_FREE (st_sp0 st) (bv_unsigned sp) (bv_unsigned ra) tl) as tr eqn:Etr.
  assert (CP01 : cli_pres st (bv_unsigned sp) m m1).
  { unfold cli_pres. eapply cj_pres_of_munch; [exact MU| exact WM|].
    intros a Ha HC. cbn. split; [| split; [| split; [| exact I]]].
    - intros Hin. apply (below_sp_not_client st WF (bv_unsigned sp) a); [unfold CEIL; lia| exact HC].
    - intros Hin. apply (wstatic_not_client st (bv_unsigned sp) a WF ltac:(unfold CEIL; lia)); [lia| exact HC].
    - intros Hin. apply (wstatic_not_client st (bv_unsigned sp) a WF ltac:(unfold CEIL; lia)); [lia| exact HC]. }
  assert (ES01 : errno_same m m1).
  { eapply errno_same_munch; [exact MU|]. unfold AERRNO, ATP. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  clear MU. pose proof (munch_refl [(lo, bv_unsigned sp); (st_t st + 3168, st_t st + 3168 + 1)] m1) as MU.
  pose proof (wmono_refl asegs m1) as WM1.
  (* [comment removed for export] *)
  pose proof (rw_cells_take m1 _ [C8 (Z_to_bv 64 (bv_unsigned sp + -2112))] [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] OBJ1) as OBa.
  pose proof (rw_cells_drop m1 _ [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 0)] [C4 (Z_to_bv 64 0)] OBJ1) as OBc.
  cbn [cells_size Cells.csize Nat.add] in OBc. replace (bv_unsigned sp + -2128 + Z.of_nat 12) with (bv_unsigned sp + -2116) in OBc by lia.
  (* [comment removed for export] *)
  assert (HG1 : GWIN st1 m1 mo g) by (apply GWIN_ia'; eapply GWIN_mem; [exact HG| exact HO| exact WM01]).
  sepM. callxp ltac:(eapply unwind_ok with (st := st1) (S := bv_unsigned sp + -2128) (pc0 := PC0_FREE) (bp := bv_unsigned sp) (rac := ra) (s0c := s0) (tl := tl) (lo := lo);
    [ exact (RTS_intro _ _ _ _ HR1 WF1 HM1 HG1 HFR (SWIN_ia' st g HSWR))
    | reflexivity| reflexivity| symmetry; apply Z_to_bv_bv_unsigned| reflexivity| reflexivity| reflexivity| exact TP
    | replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) by lia; exact OBJ1
    | eapply wr_at_weaken; [first [exact WR0| eapply wr_at_wmono; [exact WR0| exact WM01]]| lia| unfold BST_SIZE; lia]
    | rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| lia| unfold PC0_FREE; lia
    | exact REC| exact RA1| exact RA2
    | intros _; rewrite Isp0; exact UWT1
    | left; unfold BST_SIZE; lia
    | rewrite unsigned_lit by lia; exact ST1| idtac; lia| rewrite unsigned_lit by lia; unfold AUNWIND_STACK; lia| exact MI1 ])
    ltac:(unfold unwind_post, T_UNWINDING; rewrite !Isp0, !It, !unsigned_lit by lia; rewrite <- !Etr; clear BP1 OBJ1; clear ST1).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST2 end.
  match goal with H : RTREP st1 ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into HR2; rename mx into m2 end.
  match goal with H : rw_cells _ m2 (bv_unsigned sp + -2128 + 8) _ |- _ => rename H into SZ2 end.
  match goal with H : rw_cells _ m2 (bv_unsigned sp + -2128 + 16) _ |- _ => rename H into TRC2 end.
  match goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
  assert (CP12 : cli_pres st (bv_unsigned sp) m1 m2).
  { eapply (cli_pres_tpz st WF); [| exact MU| exact WM1|]; [unfold CEIL; lia|].
    unfold T_ACACHE, CEIL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  assert (ES02 : errno_same m m2).
  { eapply errno_same_trans; [exact ES01|].
    eapply errno_same_munch; [exact MU|]. unfold AERRNO, ATP. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  clear MU WM1.
  (* [comment removed for export] *)
  assert (SOBJ : rw_cells asegs m2 (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C8 (Z_to_bv 64 (zlen tr))]).
  { apply (proj2 (rw_cells_app m2 _ [C8 _] [C8 _])). split; [exact OBa|]. cbn [cells_size Cells.csize Nat.add].
    apply c44_c8; [lia|].
    apply (proj2 (rw_cells_app m2 _ [C4 _] [C4 _])). split; [exact SZ2|]. cbn [cells_size Cells.csize Nat.add].
    replace (bv_unsigned sp + -2128 + Z.of_nat 8 + Z.of_nat 4) with (bv_unsigned sp + -2116) by lia. exact OBc. }
  clear SZ2 OBa OBc.
  (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 10 lstep. (* [comment removed for export] *)
  apply evt_done. eapply lscps_bind.
  { pose proof dealloc_core_fx_proof as DC. unfold dealloc_core_fx_stmt in DC.
    eapply DC with (st := st1) (A := A) (n := n) (S := bv_unsigned sp + -2128) (tr := tr) (lo := lo); try reflexivity.
    - exact (RTS_intro _ _ _ _ HR2 WF1 HM1 ltac:(apply GWIN_ia'; eapply GWIN_mem; [exact HG| exact HO| exact WM01]) HFR ltac:(apply SWIN_ia'; exact HSWR)).
    - exact HIN1. - rewrite Iqt; exact HQT. - rewrite Iqc; exact HQC. - rewrite Iqp; exact HQP. - rewrite Iap; exact HAP.
    - exact TP.
    - replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) by lia. exact SOBJ.
    - replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2128 + 16) by lia. exact (proj1 TRC2).
    - exact TRL. - exact TRR. - rewrite Itrs. exact ROOM.
    - rewrite unsigned_lit by lia. lia. - unfold BST_SIZE. lia. - rewrite unsigned_lit, Isp0 by lia. lia.
    - rewrite PV1. unfold cost_free. lia.
    - rewrite unsigned_lit by lia. exact ST2. - idtac; lia. - rewrite unsigned_lit by lia. unfold ADEALLOC_STACK. lia.
    - exact MI2. }
  cbv beta. intros ms7 mo7 g7 [PO FXD].
  destruct PO as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m7 & st4 & -> & MI7
                  & ST7 & ES27 & CP27 & GM7 & TP7 & RTS4 & HO7 & HB7 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & BO27).
  rewrite unsigned_lit in ST7, CP27 by lia.
  replace (ret_pc (Z_to_bv 64 0x54644)) with (Z_to_bv 64 0x54644) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  unfold cli_pres in CP27. rewrite Q1, Q2, Q3, Isp0, Ilb, Ilf in CP27.
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP27) in FR1; [| left; cbn; lia].
  assert (WR7 : wr_at asegs m7 (bv_unsigned sp + -2128) 2128).
  { eapply cj_pres_wr_at; [exact CP27| first [exact WR0| eapply wr_at_wmono; [exact WR0| exact WM01]]| left; lia]. }
  eapply lscps_step_evt. cbv beta delta [wz] in *.
  (* [comment removed for export] *)
  lstep. do 7 lstep. lstep. lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  apply evt_done. apply lscps_done. split.
  2:{ intros FX0. cbn [MS ms_mem] in FXD |- *. apply FXD. intros c Hc H24. specialize (FX0 c Hc H24).
      assert (SIr : st_regions (set_ia_inited st) = st_regions st) by (destruct st; reflexivity).
      assert (SIc : st_cache (set_ia_inited st) = st_cache st) by (destruct st; reflexivity).
      unfold fresh_cls, rg, cch in *. unfold st1. rewrite SIr, SIc. exact FX0. }
  unfold free_core_post.
  do 15 eexists. exists m7, st4. split; [reflexivity|]. split; [exact MI7|].
  split.
  { eapply stk_merge; [exact ST7| | lia]. replace (bv_unsigned sp) with (bv_unsigned sp + -2128 + 2128) at 2 by lia.
    apply stk_of_wr_high; [exact WR7| unfold AIMG_HI; lia]. }
  split.
  { eapply rw_cells_same; [exact ERR|]. intros a Ha. cbn [cells_size Cells.csize Nat.add] in Ha.
    replace a with (AERRNO + (a - AERRNO)) by lia. apply ES27. unfold AERRNO, ATP in *. lia. }
  split.
  { unfold cli_pres in *.
    eapply cj_pres_trans; [eapply cj_pres_weaken; [exact CP01| lia| intros b Hb; eapply remove_first_In; exact Hb| auto]|].
    eapply cj_pres_trans; [eapply cj_pres_weaken; [exact CP12| lia| intros b Hb; eapply remove_first_In; exact Hb| auto]|].
    eapply cj_pres_weaken; [exact CP27| lia| auto| auto]. }
  split; [exact GM7|].
  split; [rewrite <- Itrs; exact TP7|].
  split; [exact RTS4|]. split; [exact HO7|]. split; [exact HB7|].
  split; [rewrite Q1; exact Isp0|]. split; [rewrite Q2, Ilb; reflexivity|]. split; [rewrite Q3; exact Ilf|].
  split; [rewrite Q4; exact Iap|]. split; [rewrite Q5; exact Isp|]. split; [rewrite Q6; exact Iqp|].
  split; [exact Q7|]. split; [exact Q8|].
  unfold budget_ok, cost_free in *. lia.
Qed.

Theorem art2_free_proof : forall kd : nat, free_lscps_stmt (fun sp0 SPB LB LF TRS B m mo g => ARTd sp0 SPB LB LF TRS B m mo g /\ ADRVd kd m mo g).
Proof.
  intros kd. unfold free_lscps_stmt. intros until tl. intros [HART HDRV] HINLB SPB0 ST HCL LO ERR MI TP HA0 COST [RA1 RA2] UWT ROOM.
  destruct (ARTd_RTS _ _ _ _ _ _ _ _ _ HART) as (st & RTS0 & HO & HB & Esp0 & Elb & Elf & Etrs & HQ & B0 & BB & HSPB).
  destruct HQ as (Qap & Qsp & Qqp & Qqt & Qqc). pose proof (proj1 (proj2 RTS0)) as WF.
  assert (HIN : In (A, n) (st_lb st)) by (rewrite Elb; exact HINLB).
  subst sp0 LB LF TRS.
  eapply lscps_mono.
  { eapply free_core_fx_proof
      with (st := st); try eassumption; unfold cost_free in *; lia. }
  cbv beta. intros ms' mo' g' [PO FXF].
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & st' & -> & MI' & ST' & ERR' & CP' & GM' & TP' & RTS' & HO' & HBI' & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & BO').
  destruct RTS' as (HR' & WF' & HM' & HG' & HF' & HSW').
  unfold afree_post. do 15 eexists. exists m', (st_trs st'). split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|].
  rewrite (cb_remove_first st A n WF HIN).
  split; [exact CP'|]. split; [exact GM'|]. split; [exact TP'|].
  split.
  2:{ destruct HDRV as [->|HFX]; [left; reflexivity|].
      cbn [MS ms_mem] in FXF. destruct (FXF (HFX st (proj1 RTS0) WF)) as (st'' & HR'' & WF'' & FX'').
      exact (adrvd_keep kd m' mo' g' st'' HR'' WF'' FX''). }
  eapply (ARTd_intro st'); [exact HR'| exact WF'| exact HM'| exact HO'| exact HBI'| exact HG'| exact HF'| exact E1| exact E2| exact E3| reflexivity| | unfold cost_free in *; lia| | exact HSPB| exact HSW'].
  - unfold QUIET. rewrite E4, E5, E6, E7, E8. repeat split; assumption.
  - unfold budget_ok, cost_free in *. lia.
Qed.
End FREEN.

End CeilWrap.
End RTW_m_freeN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Exec SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep RT_kit CJ_iface RT_art RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_lib2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_tpz RTW_m_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_aspec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_i1.
Import RTW_m_r1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_unwind.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstateP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_fz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_mallocN.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_alloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_mallocN.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_bandtac3 RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section REALLOC0.
Hypothesis try_asan_init_proof : try_asan_init_spec.
Hypothesis internal_allocator_proof : internal_allocator_spec.
Hypothesis get_malloc_ctx_size_proof : get_malloc_ctx_size_spec.
Hypothesis get_current_pc_proof : get_current_pc_spec.
Hypothesis set_errno_enomem_proof : set_errno_enomem_spec.
Hypothesis unwind_ok : unwind_spec.
Hypothesis allocate_ok : allocate_spec.

Theorem art_realloc_null_proof : realloc_null_lscps_stmt ARTd.
Proof.
  unfold realloc_null_lscps_stmt. intros until tl. intros HART SPB0 ST HCL LO ERR MI TP -> -> Hn COST [RA1 RA2] UWT ROOM.
  pose proof tpx_ok_of_RTWF as tpx_all.
  destruct (ARTd_RTS _ _ _ _ _ _ _ _ _ HART) as (st & (HR & WF & HM & HG & HFR & HSWR) & HO & HB & Esp0 & Elb & Elf & Etrs & HQ & B0 & BB & HSPB).
  pose proof (wb_sp0 st (wf_base_ok st WF)) as SP0. rewrite Esp0 in SP0. unfold AMALLOC_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
  pose proof (bv_unsigned_in_range 64 ra) as RRA. unfold bv_modulus in RRA. cbn in RRA.
  pose proof (t_range st WF) as TR. olin TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all.
  pose proof (alloc_deposit_le_cost n Hn) as DEP.
  pose proof (stk_wr_at m lo (bv_unsigned sp) (bv_unsigned sp + -2160) 2160 ST ltac:(lia) ltac:(lia)) as WR0.
  change AERRNO with 6148524 in ERR.
  apply lscps_assume. intros NWX _ _. pose proof HR as HR0.
  (* [comment removed for export] *)
  (nelimp (set_ia_same st) 18%nat; intros Isp0 Ilb Ilf Itrs It Ictx Iqp Iqt Iqc Iap Isp Isec Iqth Idep Ifs Ipa Isb Ipb).
  set (st1 := set_ia_inited st) in *.
  pose proof (RTWF_ia' st WF) as WF1. pose proof (RTMODEL_ia' st mo HM) as HM1.
  change (set_ia_inited st) with st1 in WF1, HM1.
  pose proof (rt_prov_ia' st) as PV1. change (set_ia_inited st) with st1 in PV1.
  pose proof (munch_refl [(lo, bv_unsigned sp); (701568, 701568 + 528432); (1285384, 1285384 + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  eapply lscps_step_evt.
  callxp ltac:(eapply (realloc_r1_spec try_asan_init_proof internal_allocator_proof get_malloc_ctx_size_proof get_current_pc_proof) with (lo := lo) (st := st) (A := 0) (n := n);
              [exact HR| exact WF| exact MI| reflexivity| reflexivity| lia| exact ST| idtac; lia| unfold R1_DEPTH; lia])
         ltac:(unfold r1_post, A_IA_INSTANCE, A_IA_SIZE, A_IA_INITED; change (set_ia_inited st) with st1).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -2136) _ |- _ => rename H into OBJ1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -80) _ |- _ => rename H into BP1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => rename H into FR1 end.
  match goal with H : stk _ _ (bv_unsigned sp + -2120) _ |- _ => rename H into BUF1 end.
  match goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
  match goal with H : RTREP _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into HR1; rename mx into m1 end.
  change (set_ia_inited st) with st1 in HR1.
  replace (bv_unsigned sp + -2136 + 16) with (bv_unsigned sp + -2120) in OBJ1 by lia.
  (* [comment removed for export] *)
  pose proof (rw_cells_take m1 _ [C8 (Z_to_bv 64 (bv_unsigned sp + -2120))] [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] OBJ1) as OBa.
  pose proof (rw_cells_drop m1 _ [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C4 (Z_to_bv 64 0)] [C4 (Z_to_bv 64 0)] OBJ1) as OBc.
  cbn [cells_size Cells.csize Nat.add] in OBc. replace (bv_unsigned sp + -2136 + Z.of_nat 12) with (bv_unsigned sp + -2124) in OBc by lia.
  (* [comment removed for export] *)
  destruct (stk_split asegs m1 _ (bv_unsigned sp + -2120 + 8 * zlen (hook_tr PC0_REALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl)) _ BUF1) as [_ BUF2].
  { pose proof (hook_tr_facts PC0_REALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl m _ _ _ ltac:(unfold PC0_REALLOC; lia) ltac:(lia) UWT) as [L _].
    unfold TRACE_MAX_LEN in L. lia. }
  clear BUF1.
  (* [comment removed for export] *)
  assert (REC : bytes_at asegs m1 (bv_unsigned sp - 16) (le8 s0 ++ le8 ra)).
  { pose proof (rw_cells_drop m1 _ [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1) as [[_ RB] _].
    cbn [cells_size Cells.csize Nat.add cells_bytes cbytes] in RB. rewrite app_nil_r in RB.
    replace (bv_unsigned sp + -64 + Z.of_nat 48) with (bv_unsigned sp - 16) in RB by lia. exact RB. }
  assert (UWT1 : uwt m1 (bv_unsigned sp) (ASTACK_TOP sp0) PC0_REALLOC (bv_unsigned sp) (bv_unsigned s0) 2 tl).
  { eapply uwt_mem; [exact UWT|]. intros a Ha Ha'. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
  pose proof (hook_tr_facts PC0_REALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl m _ _ _ ltac:(unfold PC0_REALLOC; lia) ltac:(lia) UWT) as [TRL TRR].
  pose proof TRL as TRL30. unfold TRACE_MAX_LEN in TRL30.
  remember (hook_tr PC0_REALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl) as tr eqn:Etr.
  assert (CP01 : cli_pres st (bv_unsigned sp) m m1).
  { unfold cli_pres. eapply cj_pres_of_munch; [exact MU| exact WM|].
    intros a Ha HC. cbn. split; [| split; [| split; [| exact I]]].
    - intros Hin. apply (below_sp_not_client st WF (bv_unsigned sp) a); [unfold CEIL; lia| exact HC].
    - intros Hin. apply (wstatic_not_client st (bv_unsigned sp) a WF ltac:(unfold CEIL; lia)); [lia| exact HC].
    - intros Hin. apply (wstatic_not_client st (bv_unsigned sp) a WF ltac:(unfold CEIL; lia)); [lia| exact HC]. }
  assert (ES01 : errno_same m m1).
  { eapply errno_same_munch; [exact MU|]. unfold AERRNO, ATP. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  clear MU. pose proof (munch_refl [(lo, bv_unsigned sp); (st_t st + 3168, st_t st + 3168 + 1)] m1) as MU.
  pose proof (wmono_refl asegs m1) as WM1.
  assert (HG1 : GWIN st1 m1 mo g) by (apply GWIN_ia'; eapply GWIN_mem; [exact HG| exact HO| exact WM]).
  callxp ltac:(eapply unwind_ok with (st := st1) (S := bv_unsigned sp + -2136) (pc0 := PC0_REALLOC) (bp := bv_unsigned sp) (rac := ra) (s0c := s0) (tl := tl) (lo := lo);
    [ exact (RTS_intro _ _ _ _ HR1 WF1 HM1 HG1 HFR (SWIN_ia' st g HSWR))
    | reflexivity| reflexivity| symmetry; apply Z_to_bv_bv_unsigned| reflexivity| reflexivity| reflexivity| exact TP
    | replace (bv_unsigned sp + -2136 + 16) with (bv_unsigned sp + -2120) by lia; exact OBJ1
    | eapply wr_at_weaken; [first [exact WR0| eapply wr_at_wmono; [exact WR0| exact WM]]| lia| unfold BST_SIZE; lia]
    | rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| lia| unfold PC0_REALLOC; lia
    | exact REC| exact RA1| exact RA2
    | intros _; rewrite Isp0, Esp0; exact UWT1
    | left; unfold BST_SIZE; lia
    | rewrite unsigned_lit by lia; exact ST1| idtac; lia| rewrite unsigned_lit by lia; unfold AUNWIND_STACK; lia| exact MI1 ])
    ltac:(unfold unwind_post, T_UNWINDING; rewrite !Isp0, !Esp0, !It, !unsigned_lit by lia; rewrite <- !Etr).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST2 end.
  match goal with H : RTREP st1 ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into HR2; rename mx into m2 end.
  match goal with H : rw_cells _ m2 (bv_unsigned sp + -2136 + 8) _ |- _ => rename H into SZ2 end.
  match goal with H : rw_cells _ m2 (bv_unsigned sp + -2136 + 16) _ |- _ => rename H into TRC2 end.
  match goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
  assert (CP12 : cli_pres st (bv_unsigned sp) m1 m2).
  { eapply (cli_pres_tpz st WF); [| exact MU| exact WM1|]; [unfold CEIL; lia|].
    unfold T_ACACHE, CEIL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  assert (ES02 : errno_same m m2).
  { eapply errno_same_trans; [exact ES01|].
    eapply errno_same_munch; [exact MU|]. unfold AERRNO, ATP. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  clear MU WM1.
  (* [comment removed for export] *)
  assert (SOBJ : rw_cells asegs m2 (bv_unsigned sp + -2136)
            [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C4 (Z_to_bv 64 (zlen tr)); C4 (Z_to_bv 64 0)]).
  { apply (proj2 (rw_cells_app m2 _ [C8 _] [C4 _; C4 _])). split; [exact OBa|]. cbn [cells_size Cells.csize Nat.add].
    apply (proj2 (rw_cells_app m2 _ [C4 _] [C4 _])). split; [exact SZ2|]. cbn [cells_size Cells.csize Nat.add].
    replace (bv_unsigned sp + -2136 + Z.of_nat 8 + Z.of_nat 4) with (bv_unsigned sp + -2124) by lia. exact OBc. }
  clear SZ2 OBa OBc.
  (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof (munch_refl [(lo, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM2.
  carve_frame 16%nat ST2.
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  match goal with H : rw_cells _ _ (bv_unsigned sp + -2160) [CB 8 _; C8 _] |- _ => rename H into FRM end.
  match goal with H : stk _ _ lo (bv_unsigned sp + -2160) |- _ => rename H into ST3 end.
  match goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
  pose proof HR2 as HR3. rtrep_high HR3 WF1 MU WM2.
  assert (CP23 : cli_pres st (bv_unsigned sp) m2 m3).
  { eapply (cli_pres_tpz st WF); [| exact MU| exact WM2|]; [unfold CEIL; lia|]. constructor; [cbn; unfold CEIL; lia| constructor]. }
  assert (ES03 : errno_same m m3).
  { eapply errno_same_trans; [exact ES02|]. eapply errno_same_munch; [exact MU|]. constructor; [cbn; unfold AERRNO, ATP; lia| constructor]. }
  assert (HG3 : GWIN st1 m3 mo g) by (apply GWIN_ia'; eapply GWIN_mem; [exact HG| exact HO| exact WM]).
  assert (WR3 : wr_at asegs m3 (bv_unsigned sp + -2160) 2160) by (first [exact WR0| eapply wr_at_wmono; [exact WR0| exact WM]]).
  clear MU WM2.
  apply evt_done. eapply lscps_bind.
  { pose proof allocate_ok as AL. unfold allocate_spec in AL.
    eapply AL with (lo := lo) (st := st1) (n := n) (S := bv_unsigned sp + -2136) (tr := tr); try reflexivity.
    - exact (RTS_intro _ _ _ _ HR3 WF1 HM1 HG3 HFR (SWIN_ia' st g HSWR)).
    - exact tpx_all. - rewrite Iap; exact (proj1 HQ). - exact Hn. - exact TP.
    - replace (bv_unsigned sp + -2136 + 16) with (bv_unsigned sp + -2120) by lia. exact SOBJ.
    - exact (proj1 TRC2).
    - exact TRL. - exact TRR.
    - rewrite unsigned_lit by lia. lia. - rewrite Isp0, Esp0. unfold BST_SIZE. lia.
    - rewrite Itrs, Etrs. exact ROOM.
    - rewrite PV1. lia.
    - rewrite unsigned_lit by lia. exact ST3. - idtac. lia. - rewrite unsigned_lit by lia. unfold AALLOCATE_STACK. lia.
    - rewrite unsigned_lit, Isp0, Esp0 by lia. lia. - exact MI3. }
  cbv beta. intros ms4 mo4 g4 PO.
  (nelim PO 30%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 st4 -> MI4 r -> RTS4 ST4 CP4 ES4 GM4 Esp04 Elf4 AS4 RES).
  assert (HQ4 : QUIET st4).
  { (nelim AS4 5%nat; intros Q1 Q2 Q3 Q4 Q5). unfold QUIET in *. rewrite Q1, Q2, Q3, Q4, Q5, Iap, Isp, Iqp, Iqt, Iqc. exact HQ. }
  unfold cli_pres in CP4. rewrite Isp0, Ilb, Ilf in CP4. rewrite Isp0 in Esp04. rewrite Ilf in Elf4.
  rewrite unsigned_lit in ST4, CP4 by lia.
  replace (ret_pc (Z_to_bv 64 0x328f4)) with (Z_to_bv 64 0x328f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (nelim RTS4 6%nat; intros HR4 WF4 HM4 HG4 HF4 HSW4).
  (* [comment removed for export] *)
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP4) in FRM; [| left; cbn; rewrite Esp0; lia].
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP4) in FR1; [| left; cbn; rewrite Esp0; lia].
  apply (cj_pres_wr_at _ _ _ _ _ _ _ _ CP4) in WR3; [| left; rewrite Esp0; lia].
  assert (ERR4 : rw_cells asegs m4 6148524 [C4 errv]).
  { eapply rw_cells_same; [exact ERR|]. intros a Ha. cbn in Ha. apply ES4 || (replace a with (AERRNO + (a - 6148524)) by (unfold AERRNO, ATP; lia); apply ES4; lia). }
  assert (CP04 : cj_pres sp0 LB LF (bv_unsigned sp) m m4).
  { unfold cli_pres in *. rewrite Esp0, Elb, Elf in CP01, CP12, CP23, CP4.
    eapply cj_pres_trans; [exact CP01|]. eapply cj_pres_trans; [exact CP12|]. eapply cj_pres_trans; [exact CP23|].
    eapply cj_pres_weaken; [exact CP4| lia| auto| auto]. }
  clear CP01 CP12 CP23 CP4 ES01 ES02 ES03 ERR.
  apply lscps_assume. intros _ HO4 HB4.
  eapply lscps_step_evt. cbv beta delta [wz] in *.
  (* [comment removed for export] *)
  assert (HLB : forall A k, In (A, k) LB -> AIMG_HI <= A).
  { intros A k Hin. rewrite <- Elb in Hin. (nelimp (block_geom st WF A k ltac:(unfold all_blocks; apply in_or_app; left; exact Hin)) 5%nat; intros _ _ G1 G2 _). blia. }
  assert (HLF : forall Fr k, In (Fr, k) LF -> AIMG_HI <= Fr).
  { intros Fr k Hin. rewrite <- Elf in Hin. (nelimp (frame_range st WF Fr k Hin) 3%nat; intros _ X _). pose proof (fs_range st WF) as (F1 & _).
    change FS_FRAMES_OFF with 36864 in X. blia. }
  assert (B4 : 0 <= B - cost_malloc n) by lia.
  destruct RES as [(-> & Elb4 & Etrs4 & BO4)|(RNZ & ABR & NIN & NFR & Elb4 & TP4 & BO4 & JK)].
  - (* [comment removed for export] *)
    assert (ART4 : ARTd sp0 SPB LB LF TRS (B - cost_malloc n) m4 mo4 g4).
    { eapply (ARTd_intro st4); [exact HR4| exact WF4| exact HM4| exact HO4| exact HB4| exact HG4| exact HF4
        | rewrite Esp04; exact Esp0| rewrite Elb4, Ilb; exact Elb| rewrite Elf4; exact Elf| rewrite Etrs4, Itrs; exact Etrs| exact HQ4| exact B4| | exact HSPB| exact HSW4].
      unfold budget_ok in BO4. lia. }
    lstep; if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    pose proof (munch_refl [(lo, bv_unsigned sp); (6148524, 6148524 + 4)] m4) as MU.
    pose proof (wmono_refl asegs m4) as WM4.
    callxp ltac:(eapply set_errno_enomem_proof with (lo := lo) (errv := errv);
      [ exact MI4| exact TP| exact ERR4| rewrite unsigned_lit by lia; exact ST4| idtac; lia| rewrite unsigned_lit by lia; lia ])
      ltac:(unfold leaf_post, AERRNO, ATP; change (6148688 - 164) with 6148524; rewrite !unsigned_lit by lia).
    cbv beta delta [wz] in *.
    match goal with H : mem_inv _ _ |- _ => rename H into MI5 end.
    match goal with H : stk _ _ lo (bv_unsigned sp + -2160) |- _ => rename H into ST5 end.
    match goal with H : rw_cells _ _ 6148524 [C4 (Z_to_bv 64 ENOMEM)] |- _ => rename H into ERR5 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. do 8 lstep. lstep. lstep. (* [comment removed for export] *)
    try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
    apply evt_done. apply lscps_done. unfold amalloc_post.
    nexists 15%nat. exists m5, (Z_to_bv 64 ENOMEM), TRS. split; [reflexivity|]. split; [exact MI5|].
    split.
    { eapply stk_merge; [exact ST5| | lia]. replace (bv_unsigned sp) with (bv_unsigned sp + -2160 + 2160) at 2 by lia.
      apply stk_of_wr_high; [| unfold AIMG_HI; lia]. match goal with H : wr_at _ m5 _ _ |- _ => exact H end. }
    split; [exact ERR5|].
    split.
    { eapply cj_pres_trans; [exact CP04|]. eapply cj_pres_of_munch; [exact MU| exact WM4|].
      intros a Ha HC. cbn. split; [| split; [| exact I]].
      - intros Hin. apply (below_sp_not_client st WF (bv_unsigned sp) a); [unfold CEIL; lia| rewrite Esp0, Elb, Elf; exact HC].
      - intros Hin. apply (errno_not_client sp0 LB LF (bv_unsigned sp) a); [unfold AERRNO, ATP; lia| unfold CEIL; lia| exact HLB| exact HLF| exact HC]. }
    split; [exact GM4|]. split; [right; reflexivity|].
    left. split; [reflexivity|].
    eapply artd_frame; [exact ART4| exact MU| exact WM4|].
    constructor; [| constructor; [| constructor]]; unfold cj_write_ok; cbn [fst snd].
    + right. left. idtac. lia.
    + do 3 right. left. unfold AERRNO, ATP. lia.
  - (* [comment removed for export] *)
    assert (ART4 : ARTd sp0 SPB ((r, n) :: LB) LF (st_trs st4) (B - cost_malloc n) m4 mo4 g4).
    { eapply (ARTd_intro st4); [exact HR4| exact WF4| exact HM4| exact HO4| exact HB4| exact HG4| exact HF4
        | rewrite Esp04; exact Esp0| rewrite Elb4, Ilb, Elb; reflexivity| rewrite Elf4; exact Elf| reflexivity| exact HQ4| exact B4| | exact HSPB| exact HSW4].
      unfold budget_ok in BO4. rewrite PV1 in BO4. lia. }
    pose proof ABR as ABR'. unfold ablock_range, KHIGHMEM_BEG, AIMG_HI in ABR'. idtac.
    lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. do 8 lstep. lstep. lstep. (* [comment removed for export] *)
    try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
    apply evt_done. apply lscps_done. unfold amalloc_post.
    nexists 15%nat. exists m4, errv, (st_trs st4). split; [reflexivity|]. split; [exact MI4|].
    split.
    { eapply stk_merge; [exact ST4| | lia]. replace (bv_unsigned sp) with (bv_unsigned sp + -2160 + 2160) at 2 by lia.
      apply stk_of_wr_high; [exact WR3| unfold AIMG_HI; lia]. }
    split; [exact ERR4|].
    split; [exact CP04|].
    split; [exact GM4|]. split; [left; rewrite <- Etrs, <- Itrs; exact TP4|].
    right. (nelim JK 3%nat; intros uj JK1 JK2). exists r, uj.
    split; [reflexivity|]. split; [exact ABR|]. split; [rewrite <- Elb, <- Ilb; exact NIN|]. split; [rewrite <- Elf, <- Ilf; exact NFR|].
    split; [exact ART4|]. split; [exact JK1| exact JK2].
Qed.
End REALLOC0.


End CeilWrap.
