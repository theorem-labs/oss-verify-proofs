(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg SpinAlgB AgentLib AgentNodes Nodes AllocSim
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra MmapSim RefNodes NoReserve.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanCeil.  (* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanNodesMmLib () : Init.string Init.list := ["Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.img_lo"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.fst"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.snd"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.img_hi"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.in_ivs"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.orb"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.leb"; "Stdlib.ZArith.BinInt.Z.ltb"; "Corelib.Init.Logic.iff"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.ex"; "Stdlib.Lists.List.In"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.ABoot.BackingAlgebra.model_ivs_wf"; "OSSVerify.KrLib.ABoot.AsanAcct.eager_used"; "OSSVerify.KrLib.ABoot.BackingAlgebra.sum_count"; "Corelib.Init.Datatypes.negb"; "OSSVerify.KrLib.ABoot.BackingAlgebra.covered"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "OSSVerify.KrLib.ABoot.AsanAcct.MInv"; "OSSVerify.KrLib.ABoot.AsanAcct.A_wf"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.page_size"; "OSSVerify.KrLib.ABoot.AsanAcct.A_bytes"; "OSSVerify.KrLib.ABoot.BackingAlgebra.iv_wf"; "LinuxProcessSemantics.LinuxProcessSem.State.iv_subtract"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.ABoot.BackingAlgebra.ivs_wf"; "LinuxProcessSemantics.LinuxProcessSem.State.maps_subtract"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.page_in_ranges"; "LinuxProcessSemantics.LinuxProcessSem.State.page_base"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.ABoot.MmapSim.zfill"; "Corelib.Init.Datatypes.Some"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.ABoot.MmapSim.unfill"; "Corelib.Init.Datatypes.None"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.acs"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.is_ecall_at"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.pc"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.expr"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.sr_vars_lt"; "Corelib.Init.Peano.lt"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.expr_vars_lt"; "Corelib.Lists.ListDef.nth"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.ELit"; "OSSVerify.KrLib.ABoot.BackingAlgebra.B"; "OSSVerify.KrLib.ABoot.BackingAlgebra.S"; "Stdlib.Lists.List.filter"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_noreserve_b"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.with_mmap_backing"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_add_lazy"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_flags_core"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_modeled_b"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_noaccess_b"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_fixed_noaccess_b"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_fixed_rw_b"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.access_report"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step_accesses"; "OSSVerify.KrLib.ABoot.PropExec.mkst"; "asanreflect_fx"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.mkAccessReport"; "OSSVerify.KrLib.ABoot.AgentNodes.epend"; "OSSVerify.KrLib.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_access"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "OSSVerify.KrLib.ABoot.ShapeAlg.node_ok"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "Corelib.Init.Datatypes.unit"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "OSSVerify.KrLib.ABoot.ShapeAlg.TSet"; "OSSVerify.KrLib.ABoot.SpinAlg.srealizes"; "LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.check_result"; "LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.check_syscall"; "LinuxProcessSemantics.LinuxProcessSem.Run.sys_input"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.CheckOk"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.CheckUnmodeled"; "LinuxProcessSemantics.LinuxProcessSem.State.syscall_effect_accesses"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr"; "OSSVerify.KrLib.ABoot.AsanCeil.init_sp_ok"; "LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z"; "OSSVerify.KrLib.ABoot.RefNodes.grant_ok_na_pin"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_noreserve_backed_ok"; "OSSVerify.KrLib.ABoot.PropExec.regupd"; "LinuxProcessSemantics.LinuxProcessSem.State.errno_ret"; "LinuxProcessSemantics.LinuxProcessSem.State.ENOMEM"; "OSSVerify.KrLib.ABoot.PropExec.v_addi"; "OSSVerify.KrLib.ABoot.MmapSim.mmap_model"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_alt2"; "OSSVerify.KrLib.ABoot.RefNodes.noaccess_model"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "OSSVerify.KrLib.ABoot.AsanCeil.alloc_ceiling"; "LinuxProcessSemantics.LinuxProcessSem.State.two_pow_64"; "LinuxProcessSemantics.LinuxProcessSem.State.alloc_top"; "Stdlib.ZArith.BinInt.Z.eqb"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_budget_ok"; "OSSVerify.KrLib.ABoot.RefNodes.mprotect_model"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.amap"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.amap_eqb"; "Corelib.Lists.ListDef.map"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.replace_entry"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.seps"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.iv_disjoint"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.env"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.is_fog"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.maps_match"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.amap_den"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.edenot"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.am_base"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.am_len"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.cs_ok"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.mmap_len"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.reg"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.hull_apart"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.kentry"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.vis_add"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.xhi"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kn"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.ACS"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.mk_ss"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.s_regs"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_ss"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.shadow_facts"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_maps"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.nxt"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_totsz"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_ylo"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_eager"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_vis"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_ghost"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_abytes"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.vis_cost"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_brk"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_fd"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_tidset"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_sub"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.mkind"; "Nodes.grant_post"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.vis"; "Nodes.maps_apart"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.coalesce1"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.coalesce"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.lit_ivs"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.uE"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.two64"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.lit_runs"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.know_ok"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.inside_runs"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.estart"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.SA"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.elenZ"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.inside_maps"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.uE_sp0"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.ATOP"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.safe_range"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kn_grant_filter"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.regs_ok"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.in_hull"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.gbump"; "Stdlib.Lists.List.fold_left"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.lo_fit"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.shadow_disj"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kdisj_all"; "Nodes.grant_mem"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.Mr"; "Nodes.kind_none"; "Nodes.kind_lazy"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.is_tok_kind"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.is_hole"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.mkind_eqb"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.KMIXEDL"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.add_entry"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.AM"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.escale"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.EVar"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.KRange"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.ATOPMAX"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.sr_upd"; "Corelib.Init.Datatypes.S"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.KHI"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.CEIL"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.null_kend"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.ev"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.fresh_ok"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.no_holes"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.ext1"; "Nodes.null_cs1"; "OSSVerify.KrLib.ABoot.AxSymRun3.env_agree"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.KWr"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.KZero"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.kimg_in_hull"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.gap_ok"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.budget_ok"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_backing_used"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_limit"; "LinuxProcessSemantics.LinuxProcessSem.State.lazy_interior"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.refuse"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.with_ss"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.ENOMEM_RET"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.cfg_of"; "OSSVerify.KrLib.ABoot.PropExec.seg_rom"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.page_aligned"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.fixed_args"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.split_lit"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.flat_x"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.fixed_args_in"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.no_fog"; "Stdlib.Lists.List.forallb"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.ranges_apart_x"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.KRWLAZY"; "Stdlib.Lists.List.flat_map"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.same_val"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.find_hole"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.with_maps0"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.unhole"; "Nodes.fixed_cs1"; "OSSVerify.KrLib.ABoot.BackingAlgebra.overlap_sum"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.rekind"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.rekind_k"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.am_kind"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.born"; "OSSVerify.KrLib.ABoot.BackingAlgebra.in_rng"; "Nodes.sl_nn"; "Nodes.slarm"; "Nodes.SlG"; "Nodes.SlF"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kimg_clip"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kn_unfill"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kn_rezero"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.find_containing"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RES_hull_def (SEGS : list Segment) (A : AP.atable) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "(0.(1.(2.&40.)(2.&40.))Liv,(1.(2.&40.)(2.&40.))(3.(4.(5.O1.)(6.&40.(7.(2.&40.)(2.&40.)R1.)))(4.(8.(6.&40.(7.(2.&40.)(2.&40.)R1.))(6.&40.(9.(2.&40.)(2.&40.)R1.)))(:.O1.)))(;.O2.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_ivs_covered : forall z l, in_ivs z l = covered l z.
Proof.
  intros z l. unfold in_ivs, covered, in_iv, in_rng, B, S. reflexivity.
Qed.

Lemma in_ivs_cons : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pz,$<.Piv,(1.(2.&40.)(2.&40.))Pl,(=.(1.(2.&40.)(2.&40.)))(>.$?.(10.R3.(11.(1.(2.&40.)(2.&40.))R2.R1.))(12.(13.(14.(6.&40.(7.(2.&40.)(2.&40.)R2.))R3.)(15.R3.(8.(6.&40.(7.(2.&40.)(2.&40.)R2.))(6.&40.(9.(2.&40.)(2.&40.)R2.)))))(10.R3.R1.)))")
(* [comment removed for export] *).
Proof. reflexivity. Qed.

Lemma in_ivs_app : forall z l1 l2, in_ivs z (l1 ++ l2) = (in_ivs z l1 || in_ivs z l2)%bool.
Proof. intros. unfold in_ivs. apply existsb_app. Qed.

Lemma in_ivs_true' : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pz,$<.Pl,(=.(1.(2.&40.)(2.&40.)))(16.(>.$?.(10.R2.R1.)$17.)(18.(1.(2.&40.)(2.&40.))Liv,(1.(2.&40.)(2.&40.))(3.(19.(1.(2.&40.)(2.&40.))R1.R2.)(3.(4.(6.&40.(7.(2.&40.)(2.&40.)R1.))R3.)(1:.R3.(8.(6.&40.(7.(2.&40.)(2.&40.)R1.))(6.&40.(9.(2.&40.)(2.&40.)R1.))))))))")
(* [comment removed for export] *).
Proof.
  intros z l. unfold in_ivs. rewrite existsb_exists. split.
  - intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. eauto.
  - intros [iv [Hin Hb]]. exists iv. split; [exact Hin|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma in_ivs_false : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pz,$<.Pl,(=.(1.(2.&40.)(2.&40.)))(16.(>.$?.(10.R2.R1.)$1;.)Piv,(1.(2.&40.)(2.&40.))P,(19.(1.(2.&40.)(2.&40.))R1.R2.)(1<.(3.(4.(6.&40.(7.(2.&40.)(2.&40.)R2.))R4.)(1:.R4.(8.(6.&40.(7.(2.&40.)(2.&40.)R2.))(6.&40.(9.(2.&40.)(2.&40.)R2.)))))))")
(* [comment removed for export] *).
Proof.
  intros z l. split.
  - intros H iv Hin Hz. assert (T : in_ivs z l = true) by (apply (proj2 (in_ivs_true' z l)); eauto). congruence.
  - intros H. destruct (in_ivs z l) eqn:E; [|reflexivity]. exfalso.
    apply in_ivs_true' in E as [iv [Hin Hz]]. exact (H iv Hin Hz).
Qed.

Lemma sum_sizes_live : forall l, sum_sizes l = live_bytes l.
Proof. induction l as [|[a s] l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma sum_sizes_app : forall l1 l2, sum_sizes (l1 ++ l2) = sum_sizes l1 + sum_sizes l2.
Proof. intros. rewrite !sum_sizes_live. apply live_bytes_app. Qed.

(* [comment removed for export] *)
Lemma region_free_sem : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pl,(=.(1.(2.&40.)(2.&40.)))Plo,(2.&40.)Pn,(2.&40.)Pz,$<.P,(>.$?.(1=.R4.R3.R2.)$17.)P,(1:.=(6.&40.R3.))P,(3.(4.(6.&40.R5.)R3.)(1:.R3.(8.(6.&40.R5.)(6.&40.R4.))))(>.$?.(10.R4.R7.)$1;.)")
(* [comment removed for export] *).
Proof.
  intros l lo n z Hrf Hn Hz. apply (proj2 (in_ivs_false z l)). intros [b s] Hin Hin2. cbn [fst snd] in Hin2.
  pose proof (region_free_In l lo n b s Hrf Hin) as Hov. lia.
Qed.

Lemma region_free_app : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pl1,(=.(1.(2.&40.)(2.&40.)))Pl2,(=.(1.(2.&40.)(2.&40.)))Plo,(2.&40.)Pn,(2.&40.)(>.$?.(1=.(1>.(1.(2.&40.)(2.&40.))R4.R3.)R2.R1.)(13.(1=.R4.R2.R1.)(1=.R3.R2.R1.)))")
(* [comment removed for export] *).
Proof. induction l1 as [|[a s] l1 IH]; intros; cbn; [reflexivity|]. rewrite IH, andb_assoc. reflexivity. Qed.

(* [comment removed for export] *)
Lemma map_contains_intro : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pl,(=.(1.(2.&40.)(2.&40.)))Plo,(2.&40.)Pn,(2.&40.)Pb,(2.&40.)Ps,(2.&40.)P,(19.(1.(2.&40.)(2.&40.))(1?.(2.&40.)(2.&40.)R2.R1.)R5.)P,(4.(6.&40.R3.)(6.&40.R5.))P,(4.(8.(6.&40.R6.)(6.&40.R5.))(8.(6.&40.R4.)(6.&40.R3.)))(>.$?.(20.R8.R7.R6.)$17.)")
(* [comment removed for export] *).
Proof.
  intros l lo n b s Hin H1 H2. unfold map_contains. apply existsb_exists. exists (b, s). split; [exact Hin|].
  cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma map_has_intro : forall l (lo n : word), In (lo, n) l -> map_has l lo n = true.
Proof.
  intros l lo n Hin. unfold map_has. apply existsb_exists. exists (lo, n). split; [exact Hin|].
  cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma eager_used_sem : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pm,$21.P,(22.R1.)(>.$<.(23.R2.)(24.Lx,$<.(25.(26.(1>.(1.(2.&40.)(2.&40.))(27.(28.R3.))(29.R3.))R1.))(2:.(28.R2.))))")
(* [comment removed for export] *).
Proof.
  intros m Hwf. pose proof (vm_backing_used_sem m Hwf) as H. rewrite vm_backing_used_split in H. lia.
Qed.

Lemma mat_pages_le_A_bytes : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PA,(=.(1.$<.$<.))Pm,$21.P,(2;.R2.R1.)P,(2<.R3.)(4.(2=.(2>.(2?.(2.&40.)(30.R3.)))$31.)(32.R4.))")
(* [comment removed for export] *).
Proof.
  intros A m [N1 N2 N3 N4 N5] Hwf. apply allowed_pages_bound; assumption.
Qed.

Lemma vm_backing_used_le : forall A m,
  MInv A m -> A_wf A -> vm_backing_used m <= eager_used m + A_bytes A.
Proof.
  intros A m HM Hwf. rewrite vm_backing_used_split. pose proof (mat_pages_le_A_bytes A m HM Hwf). lia.
Qed.

Lemma vm_backing_used_limit : forall A m,
  MInv A m -> A_wf A -> vm_backing_used m <= vm_limit (m_vmmaps m).
Proof.
  intros A m HM Hwf. pose proof (vm_backing_used_le A m HM Hwf). pose proof (minv_budget _ _ HM). lia.
Qed.

(* [comment removed for export] *)
Lemma sum_count_negb_covered_mono : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PC,(=.(1.(2.&40.)(2.&40.)))PC',(=.(1.(2.&40.)(2.&40.)))Pl,(=.(1.(2.&40.)(2.&40.)))P,Px,$<.P,(>.$?.(26.R4.R1.)$17.)(>.$?.(26.R4.R2.)$17.)(4.(24.Lx,$<.(25.(26.R4.R1.))R2.)(24.Lx,$<.(25.(26.R5.R1.))R2.))")
(* [comment removed for export] *).
Proof.
  intros C C' l H. apply sum_count_mono. intros x Hx. apply negb_true_iff in Hx. apply negb_true_iff.
  destruct (covered C x) eqn:E; [|reflexivity]. rewrite (H x E) in Hx. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma iv_subtract_pieces : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pa,(2.&40.)Psz,(2.&40.)Plo,$<.Phi,$<.Pq,(1.(2.&40.)(2.&40.))P,(33.(1?.(2.&40.)(2.&40.)R5.R4.))P,(19.(1.(2.&40.)(2.&40.))R2.(34.R6.R5.R4.R3.))(3.(4.(6.&40.R7.)(6.&40.(7.(2.&40.)(2.&40.)R3.)))(3.(4.(8.(6.&40.(7.(2.&40.)(2.&40.)R3.))(6.&40.(9.(2.&40.)(2.&40.)R3.)))(8.(6.&40.R7.)(6.&40.R6.)))(35.(4.(8.(6.&40.(7.(2.&40.)(2.&40.)R3.))(6.&40.(9.(2.&40.)(2.&40.)R3.)))R5.)(4.R4.(6.&40.(7.(2.&40.)(2.&40.)R3.))))))")
(* [comment removed for export] *).
Proof.
  intros a sz lo hi q Hwf Hin. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:El; [|destruct Hin]. apply Z.ltb_lt in El.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite u64_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite !u64_lit by lia. lia.
Qed.

Lemma maps_subtract_pieces : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pl,(=.(1.(2.&40.)(2.&40.)))Plo,$<.Phi,$<.Pq,(1.(2.&40.)(2.&40.))P,(36.R4.)P,(19.(1.(2.&40.)(2.&40.))R2.(37.R5.R4.R3.))(18.(1.(2.&40.)(2.&40.))Lr,(1.(2.&40.)(2.&40.))(3.(19.(1.(2.&40.)(2.&40.))R1.R7.)(3.(4.(6.&40.(7.(2.&40.)(2.&40.)R1.))(6.&40.(7.(2.&40.)(2.&40.)R4.)))(3.(4.(8.(6.&40.(7.(2.&40.)(2.&40.)R4.))(6.&40.(9.(2.&40.)(2.&40.)R4.)))(8.(6.&40.(7.(2.&40.)(2.&40.)R1.))(6.&40.(9.(2.&40.)(2.&40.)R1.))))(35.(4.(8.(6.&40.(7.(2.&40.)(2.&40.)R4.))(6.&40.(9.(2.&40.)(2.&40.)R4.)))R6.)(4.R5.(6.&40.(7.(2.&40.)(2.&40.)R4.))))))))")
(* [comment removed for export] *).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi q Hwf Hin; [destruct Hin|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity|]. cbn [fst snd]. exact (iv_subtract_pieces a sz lo hi q Ha Hin).
  - destruct (IH lo hi q Hl Hin) as (r & Hr & H). exists r. split; [right; exact Hr | exact H].
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pa,(2.&40.)Psz,(2.&40.)Plo,$<.Phi,$<.P,(1:.R2.R1.)P,(1:.=(6.&40.R4.))P,(35.(4.(8.(6.&40.R6.)(6.&40.R5.))R4.)(4.R3.(6.&40.R6.)))(>.(=.(1.(2.&40.)(2.&40.)))(34.R7.R6.R5.R4.)(11.(1.(2.&40.)(2.&40.))(1?.(2.&40.)(2.&40.)R7.R6.)(38.(1.(2.&40.)(2.&40.)))))")
(* [comment removed for export] *).
Proof.
  intros a sz lo hi Hlh Hsz Hd. pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. unfold iv_subtract.
  destruct Hd as [Hd|Hd].
  - destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; [|exfalso; lia].
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned.
    destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [exfalso; lia | reflexivity].
  - destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; [exfalso; lia|].
    destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Er|Er]; [|exfalso; lia].
    cbn [app]. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_keeps : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pl,(=.(1.(2.&40.)(2.&40.)))Pb,(2.&40.)Ps,(2.&40.)Plo,$<.Phi,$<.P,(1:.R2.R1.)P,(1:.=(6.&40.R4.))P,(19.(1.(2.&40.)(2.&40.))(1?.(2.&40.)(2.&40.)R6.R5.)R7.)P,(35.(4.(8.(6.&40.R7.)(6.&40.R6.))R5.)(4.R4.(6.&40.R7.)))(19.(1.(2.&40.)(2.&40.))(1?.(2.&40.)(2.&40.)R8.R7.)(37.R9.R6.R5.))")
(* [comment removed for export] *).
Proof.
  induction l as [|[a sz] l IH]; intros b s lo hi Hlh Hs Hin Hd; [destruct Hin|].
  cbn [maps_subtract]. apply in_app_iff. destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. left. rewrite (iv_subtract_disjoint b s lo hi Hlh Hs Hd). left. reflexivity.
  - right. apply IH; assumption.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_pos : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pa,(2.&40.)Psz,(2.&40.)Plo,$<.Phi,$<.Pq,(1.(2.&40.)(2.&40.))P,(33.(1?.(2.&40.)(2.&40.)R5.R4.))P,(1:.=(6.&40.R5.))P,(19.(1.(2.&40.)(2.&40.))R3.(34.R7.R6.R5.R4.))(1:.=(6.&40.(9.(2.&40.)(2.&40.)R4.)))")
(* [comment removed for export] *).
Proof.
  intros a sz lo hi q Hwf Hsz Hin. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:El; [|destruct Hin]. apply Z.ltb_lt in El.
    destruct Hin as [<-|[]]. cbn [snd]. rewrite u64_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er.
    destruct Hin as [<-|[]]. cbn [snd]. rewrite u64_lit by lia. lia.
Qed.
Lemma maps_subtract_pos : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pl,(=.(1.(2.&40.)(2.&40.)))Plo,$<.Phi,$<.Pq,(1.(2.&40.)(2.&40.))P,(36.R4.)P,Pe,(1.(2.&40.)(2.&40.))P,(19.(1.(2.&40.)(2.&40.))R1.R6.)(1:.=(6.&40.(9.(2.&40.)(2.&40.)R2.)))P,(19.(1.(2.&40.)(2.&40.))R3.(37.R6.R5.R4.))(1:.=(6.&40.(9.(2.&40.)(2.&40.)R4.)))")
(* [comment removed for export] *).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi q Hwf Hpos Hin; [destruct Hin|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - eapply iv_subtract_pos; [exact Ha | exact (Hpos (a, sz) (or_introl eq_refl)) | exact Hin].
  - eapply IH; [exact Hl | intros e He; apply Hpos; right; exact He | exact Hin].
Qed.

(* [comment removed for export] *)

Lemma page_in_ranges_cons : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pp,(2.&40.)Piv,(1.(2.&40.)(2.&40.))Pl,(=.(1.(2.&40.)(2.&40.)))(>.$?.(39.R3.(11.(1.(2.&40.)(2.&40.))R2.R1.))(12.(13.(14.(6.&40.(7.(2.&40.)(2.&40.)R2.))(6.&40.R3.))(14.(8.(6.&40.R3.)$31.)(8.(6.&40.(7.(2.&40.)(2.&40.)R2.))(6.&40.(9.(2.&40.)(2.&40.)R2.)))))(39.R3.R1.)))")
(* [comment removed for export] *).
Proof. reflexivity. Qed.

Lemma page_in_ranges_app : forall p l1 l2,
  page_in_ranges p (l1 ++ l2) = (page_in_ranges p l1 || page_in_ranges p l2)%bool.
Proof. intros. unfold page_in_ranges. apply existsb_app. Qed.

Lemma page_in_ranges_true : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pp,(2.&40.)Pl,(=.(1.(2.&40.)(2.&40.)))(16.(>.$?.(39.R2.R1.)$17.)(18.(1.(2.&40.)(2.&40.))Liv,(1.(2.&40.)(2.&40.))(3.(19.(1.(2.&40.)(2.&40.))R1.R2.)(3.(4.(6.&40.(7.(2.&40.)(2.&40.)R1.))(6.&40.R3.))(4.(8.(6.&40.R3.)$31.)(8.(6.&40.(7.(2.&40.)(2.&40.)R1.))(6.&40.(9.(2.&40.)(2.&40.)R1.))))))))")
(* [comment removed for export] *).
Proof.
  intros p l. unfold page_in_ranges. rewrite existsb_exists. split.
  - intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. eauto.
  - intros (iv & Hin & H1 & H2). exists iv. split; [exact Hin|]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma page_in_ranges_false : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pp,(2.&40.)Pl,(=.(1.(2.&40.)(2.&40.)))(16.(>.$?.(39.R2.R1.)$1;.)Piv,(1.(2.&40.)(2.&40.))P,(19.(1.(2.&40.)(2.&40.))R1.R2.)(1<.(3.(4.(6.&40.(7.(2.&40.)(2.&40.)R2.))(6.&40.R4.))(4.(8.(6.&40.R4.)$31.)(8.(6.&40.(7.(2.&40.)(2.&40.)R2.))(6.&40.(9.(2.&40.)(2.&40.)R2.)))))))")
(* [comment removed for export] *).
Proof.
  intros p l. split.
  - intros H iv Hin Hc. assert (T : page_in_ranges p l = true) by (apply (proj2 (page_in_ranges_true p l)); exists iv; tauto). congruence.
  - intros H. destruct (page_in_ranges p l) eqn:E; [|reflexivity]. exfalso.
    apply page_in_ranges_true in E as (iv & Hin & H1 & H2). exact (H iv Hin (conj H1 H2)).
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_covers : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pp,(2.&40.)Pl,(=.(1.(2.&40.)(2.&40.)))Pz,$<.P,(>.$?.(39.R3.R2.)$17.)P,(3.(4.(6.&40.R4.)R2.)(1:.R2.(8.(6.&40.R4.)$31.)))(>.$?.(10.R3.R4.)$17.)")
(* [comment removed for export] *).
Proof.
  intros p l z Hp Hz. apply page_in_ranges_true in Hp as (iv & Hin & H1 & H2).
  apply (proj2 (in_ivs_true' z l)). exists iv. split; [exact Hin | lia].
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_subtract_out : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pp,(2.&40.)Pl,(=.(1.(2.&40.)(2.&40.)))Plo,$<.Phi,$<.P,(36.R3.)P,(4.R3.R2.)P,(35.(4.(8.(6.&40.R6.)$31.)R4.)(4.R3.(6.&40.R6.)))(>.$?.(39.R7.(37.R6.R5.R4.))(39.R7.R6.))")
(* [comment removed for export] *).
Proof.
  intros p l lo hi Hwf Hlh Hout. pose proof (u64_range p) as Rp. unfold page_size in *.
  induction l as [|[a sz] l IH]; [reflexivity|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract]. rewrite page_in_ranges_app, page_in_ranges_cons, (IH Hl). f_equal.
  cbn [fst snd]. unfold iv_wf, B, S in Ha. cbn [fst snd] in Ha.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract. rewrite page_in_ranges_app.
  destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Er|Er];
    cbn [page_in_ranges existsb fst snd app orb]; unfold page_size; rewrite ?u64_lit by lia; rewrite ?orb_false_r.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout].
    + destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
    + destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_subtract_in : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pp,(2.&40.)Pl,(=.(1.(2.&40.)(2.&40.)))Plo,$<.Phi,$<.P,(36.R3.)P,(3.(4.R3.(6.&40.R5.))(1:.(6.&40.R5.)R2.))(>.$?.(39.R6.(37.R5.R4.R3.))$1;.)")
(* [comment removed for export] *).
Proof.
  intros p l lo hi Hwf Hp. pose proof (u64_range p) as Rp.
  destruct (page_in_ranges p (maps_subtract l lo hi)) eqn:E; [|reflexivity]. exfalso.
  pose proof (page_in_ranges_covers p _ (bv_unsigned p) E ltac:(unfold page_size; lia)) as C.
  rewrite in_ivs_covered in C.
  destruct (maps_subtract_sem l lo hi Hwf ltac:(lia)) as (_ & _ & Cv). rewrite Cv in C.
  apply andb_prop in C as [_ C]. apply negb_true_iff in C. unfold in_rng in C.
  apply andb_false_iff in C as [C|C]; [apply Z.leb_gt in C | apply Z.ltb_ge in C]; lia.
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_cons_in : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pp,(2.&40.)Pa,(2.&40.)Pn,(2.&40.)Pl,(=.(1.(2.&40.)(2.&40.)))P,(4.(6.&40.R3.)(6.&40.R4.))P,(4.(8.(6.&40.R5.)$31.)(8.(6.&40.R4.)(6.&40.R3.)))(>.$?.(39.R6.(11.(1.(2.&40.)(2.&40.))(1?.(2.&40.)(2.&40.)R5.R4.)R3.))$17.)")
(* [comment removed for export] *).
Proof.
  intros p a n l H1 H2. rewrite page_in_ranges_cons. cbn [fst snd]. apply orb_true_iff. left.
  apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma page_in_ranges_cons_out : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pp,(2.&40.)Pa,(2.&40.)Pn,(2.&40.)Pl,(=.(1.(2.&40.)(2.&40.)))P,(35.(4.(8.(6.&40.R4.)$31.)(6.&40.R3.))(4.(8.(6.&40.R3.)(6.&40.R2.))(6.&40.R4.)))P,(1:.=(6.&40.R3.))(>.$?.(39.R6.(11.(1.(2.&40.)(2.&40.))(1?.(2.&40.)(2.&40.)R5.R4.)R3.))(39.R6.R3.))")
(* [comment removed for export] *).
Proof.
  intros p a n l H Hn. rewrite page_in_ranges_cons. cbn [fst snd]. unfold page_size in *.
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned n)); cbn; try reflexivity. exfalso. lia.
Qed.

(* [comment removed for export] *)
Lemma page_base_facts : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pa,(2.&40.)(3.(4.(6.&40.(3:.R1.))(6.&40.R1.))(3.(1:.(6.&40.R1.)(8.(6.&40.(3:.R1.))+1000.))(>.$<.(3;.(6.&40.(3:.R1.))+1000.)=)))")
(* [comment removed for export] *).
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
  rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma page_of_byte_in_aligned : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Px,(2.&40.)Plo,$<.Phi,$<.P,(>.$<.(3;.R2.+1000.)=)P,(>.$<.(3;.R2.+1000.)=)P,(3.(4.R4.(6.&40.R5.))(1:.(6.&40.R5.)R3.))(3.(4.R5.(6.&40.(3:.R6.)))(4.(8.(6.&40.(3:.R6.))+1000.)R4.))")
(* [comment removed for export] *).
Proof.
  intros x lo hi Hlo Hhi Hx. pose proof (page_base_facts x) as (P1 & P2 & P3).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma page_of_byte_out_aligned : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Px,(2.&40.)Plo,$<.Phi,$<.P,(>.$<.(3;.R2.+1000.)=)P,(>.$<.(3;.R2.+1000.)=)P,(35.(1:.(6.&40.R5.)R4.)(4.R3.(6.&40.R5.)))(35.(4.(8.(6.&40.(3:.R6.))+1000.)R5.)(4.R4.(6.&40.(3:.R6.))))")
(* [comment removed for export] *).
Proof.
  intros x lo hi Hlo Hhi Hx. pose proof (page_base_facts x) as (P1 & P2 & P3).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zfill_in : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pa,(2.&40.)Pn,(2.&40.)Pm,P,(2.&40.)(3<.(2.&8.))Px,(2.&40.)P,(3.(4.(6.&40.R4.)(6.&40.R1.))(1:.(6.&40.R1.)(8.(6.&40.R4.)(6.&40.R3.))))(>.(3<.(2.&8.))(3=.R5.R4.R3.R2.)(3>.(2.&8.)(3?.&8.=)))")
(* [comment removed for export] *).
Proof.
  intros a n m x Hx. unfold zfill, zmem.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma unfill_in : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pa,(2.&40.)Pn,(2.&40.)Pm,P,(2.&40.)(3<.(2.&8.))Px,(2.&40.)P,(3.(4.(6.&40.R4.)(6.&40.R1.))(1:.(6.&40.R1.)(8.(6.&40.R4.)(6.&40.R3.))))(>.(3<.(2.&8.))(40.R5.R4.R3.R2.)(41.(2.&8.)))")
(* [comment removed for export] *).
Proof.
  intros a n m x Hx. unfold unfill.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma mrestrict_at : forall (H : word -> bool) M (x : word),
  mrestrict H M x = if H x then None else M x.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma v_addi_pc : forall p, 0 <= p -> p + 4 < 2 ^ 64 -> v_addi (Z_to_bv 64 p) 4 = Z_to_bv 64 (p + 4).
Proof. intros p H0 H4. unfold v_addi. rewrite u64_lit by lia. reflexivity. Qed.

Lemma is_ecall_at_sound : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PSEGS,(=.$42.)Pcs,$43.P,(>.$?.(44.R2.R1.)$17.)(18.(2.&20.)Lw,(2.&20.)(3.(>.(3<.(2.&20.))(45.R4.(3?.&40.(46.R3.)))(3>.(2.&20.)R1.))(3.(>.$?.(47.R1.)$17.)(3.(4.=(46.R3.))(1:.(8.(46.R3.)+4.)(48.+2.+40.))))))")
(* [comment removed for export] *).
Proof.
  intros SEGS cs H. unfold is_ecall_at in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4]. apply Z.leb_le in H0. apply Z.ltb_lt in H4.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hw; [|discriminate].
  exists w. unfold two64 in H4. auto.
Qed.

Lemma page_up_eq : forall len, page_up len = page_round_up_Z len.
Proof. intros. unfold page_up, page_round_up_Z, page_size. f_equal. f_equal. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma env_agree_le' : forall b b' E E', env_agree b' E E' -> (b <= b')%nat -> env_agree b E E'.
Proof. intros b b' E E' [H1 H2] Hle. split; [|exact H2]. intros n Hn. apply H1. lia. Qed.

Lemma env_agree_refl' : forall b E, env_agree b E E.
Proof. intros. split; [intros; reflexivity | reflexivity]. Qed.

Lemma env_agree_trans' : forall b E1 E2 E3, env_agree b E1 E2 -> env_agree b E2 E3 -> env_agree b E1 E3.
Proof. intros b E1 E2 E3 [A1 B1] [A2 B2]. split; [intros n Hn; rewrite A1 by lia; apply A2; lia | congruence]. Qed.

Lemma ext1_agree'' : forall E v a, env_agree v E (ext1 E v a).
Proof.
  intros E v a. split; [|reflexivity]. intros n Hn. cbn [ext1 ev].
  destruct (Nat.eqb_spec n v); [lia | reflexivity].
Qed.

Lemma nth_sr_vars_lt' : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pb,$49.Psr,(=.$4:.)Pr,$49.P,(>.$?.(4;.R3.R2.)$17.)P,(4<.R2.#20.)(>.$?.(4=.R5.(4>.$4:.R3.R4.(4?.=)))$17.)")
(* [comment removed for export] *).
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [AP.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma elenZ_lit'' : forall E z, 0 <= z < 2 ^ 64 -> elenZ E (ELit z) = z.
Proof. intros E z Hz. unfold elenZ. cbn [edenot]. rewrite u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma aluop_eqb_refl : forall o, aluop_eqb o o = true.
Proof. intros []; reflexivity. Qed.
Lemma mulop_eqb_refl : forall o, mulop_eqb o o = true.
Proof. intros []; reflexivity. Qed.
Lemma expr_eqb_refl : forall e, expr_eqb e e = true.
Proof.
  induction e; cbn; rewrite ?aluop_eqb_refl, ?mulop_eqb_refl, ?IHe1, ?IHe2, ?IHe, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
Lemma amap_eqb_refl : forall m, amap_eqb m m = true.
Proof. intros [b l k]. unfold amap_eqb. cbn. rewrite !expr_eqb_refl. destruct k; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma seps_filter : forall f l, seps l -> seps (List.filter f l).
Proof.
  intros f l H. induction H as [|p l Hf Hl IH]; cbn; [constructor|].
  destruct (f p); [|exact IH]. constructor; [|exact IH].
  apply Forall_forall. intros q Hq. apply filter_In in Hq as [Hq _]. exact (proj1 (Forall_forall _ _) Hf q Hq).
Qed.

Lemma sum_sizes_filter_le : forall f l, sum_sizes (List.filter f l) <= sum_sizes l.
Proof.
  intros f l. induction l as [|[b s] l IH]; cbn; [lia|]. pose proof (u64_range s). destruct (f (b, s)); cbn; lia.
Qed.

Lemma A_bytes_app' : forall l1 l2, A_bytes (l1 ++ l2) = A_bytes l1 + A_bytes l2.
Proof. intros l1 l2. induction l1; cbn [A_bytes app]; [lia|]. rewrite IHl1. lia. Qed.

Lemma A_bytes_flat_map_split : forall {T} (f : T -> list (Z * Z)) (g : T -> bool) l r,
  A_bytes (flat_map f (List.filter g l ++ (List.filter (fun x => negb (g x)) l ++ r))) = A_bytes (flat_map f (l ++ r)).
Proof.
  intros T f g l r. rewrite !flat_map_app, !A_bytes_app'. induction l as [|x l IH]; cbn; [lia|].
  destruct (g x); cbn; rewrite !A_bytes_app'; lia.
Qed.

Lemma in_flat_map_split : forall {T U} (f : T -> list U) (g : T -> bool) l r y,
  In y (flat_map f (List.filter g l ++ (List.filter (fun x => negb (g x)) l ++ r))) <-> In y (flat_map f (l ++ r)).
Proof.
  intros T U f g l r y. rewrite !in_flat_map. split.
  - intros (x & Hx & Hy). exists x. split; [|exact Hy]. apply in_app_iff in Hx as [Hx|Hx]; [apply filter_In in Hx as [Hx _]; apply in_app_iff; left; exact Hx|].
    apply in_app_iff in Hx as [Hx|Hx]; [apply filter_In in Hx as [Hx _]; apply in_app_iff; left; exact Hx|]. apply in_app_iff; right; exact Hx.
  - intros (x & Hx & Hy). exists x. split; [|exact Hy]. apply in_app_iff in Hx as [Hx|Hx].
    + destruct (g x) eqn:E; [apply in_app_iff; left; apply filter_In; auto|].
      apply in_app_iff; right. apply in_app_iff; left. apply filter_In. rewrite E. auto.
    + apply in_app_iff; right. apply in_app_iff; right. exact Hx.
Qed.

Lemma sum_count_filter_le : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PP,P,$<.$?.PP',P,$<.$?.Pf,P,(1.(2.&40.)(2.&40.))$?.Pl,(=.(1.(2.&40.)(2.&40.)))P,Pq,(1.(2.&40.)(2.&40.))P,(19.(1.(2.&40.)(2.&40.))R1.R2.)P,(>.$?.A1.R4.R2.$17.)Px,$<.P,(3.(4.(50.R4.)R1.)(1:.R1.(8.(50.R4.)(51.R4.))))(>.$?.A1.R8.R2.A1.R9.R2.)(4.(24.R4.(52.(1.(2.&40.)(2.&40.))R3.R2.))(24.R5.R2.))")
(* [comment removed for export] *).
Proof.
  intros P P' f l H. induction l as [|q l IH]; cbn; [lia|].
  assert (IH' := IH ltac:(intros q' Hq'; apply H; right; exact Hq')).
  destruct (f q) eqn:E; cbn; [|unfold iv_count in *; pose proof (zcount_nonneg P (B q) (Z.to_nat (S q))); lia].
  unfold iv_count in *. rewrite (zcount_ext P' P); [lia|].
  intros x Hx. apply (H q (or_introl eq_refl) E). pose proof (S_range q). rewrite Z2Nat.id in Hx by lia. lia.
Qed.

Lemma filter_map_ext : forall {T U} (h : T -> U) (f : U -> bool) (f' : T -> bool) l,
  (forall x, In x l -> f (h x) = f' x) -> List.filter f (map h l) = map h (List.filter f' l).
Proof.
  intros T U h f f' l H. induction l as [|x l IH]; cbn; [reflexivity|].
  rewrite (H x (or_introl eq_refl)). rewrite (IH ltac:(intros y Hy; apply H; right; exact Hy)).
  destruct (f' x); reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma mmap_flags_core_22 : mmap_flags_core (Z_to_bv 64 34) = 34%Z.       Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_32 : mmap_flags_core (Z_to_bv 64 50) = 50%Z.       Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_4022 : mmap_flags_core (Z_to_bv 64 16418) = 34%Z.  Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_4032 : mmap_flags_core (Z_to_bv 64 16434) = 50%Z.  Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_22 : mmap_noreserve_b (Z_to_bv 64 34) = false.   Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_32 : mmap_noreserve_b (Z_to_bv 64 50) = false.   Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_4022 : mmap_noreserve_b (Z_to_bv 64 16418) = true. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_4032 : mmap_noreserve_b (Z_to_bv 64 16434) = true. Proof. vm_compute. reflexivity. Qed.

Lemma with_mmap_backing_plain : forall flags a n m,
  mmap_noreserve_b flags = false -> with_mmap_backing flags a n m = m.
Proof. intros flags a n m H. unfold with_mmap_backing. now rewrite H. Qed.

Lemma with_mmap_backing_lazy : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pflags,(2.&40.)Pa,(2.&40.)Pn,(2.&40.)Pm,$21.P,(>.$?.(53.R4.)$17.)(>.$21.(54.R5.R4.R3.R2.)(55.R4.R3.R2.))")
(* [comment removed for export] *).
Proof. intros flags a n m H. unfold with_mmap_backing. now rewrite H. Qed.

Lemma with_mmap_backing_halted : forall flags a n m,
  m_halted (with_mmap_backing flags a n m) = m_halted m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma with_mmap_backing_fs : forall flags a n m,
  m_fs (with_mmap_backing flags a n m) = m_fs m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma with_mmap_backing_vmmaps : forall flags a n m,
  m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_gates_core34 : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pflags,(2.&40.)P,(>.$<.(56.R1.)+22.)(3.(>.$?.(57.(3?.&40.+3.)R2.(3?.&40.=))$17.)(3.(>.$?.(57.(3?.&40.=)R2.(3?.&40.=))$1;.)(>.$?.(58.(3?.&40.=)R2.(3?.&40.=))$17.)))")
(* [comment removed for export] *).
Proof.
  intros flags Hc. unfold mmap_modeled_b, mmap_noaccess_b. rewrite Hc.
  repeat split; vm_compute; reflexivity.
Qed.

Lemma mmap_gates_core50 : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pflags,(2.&40.)Pprot,(2.&40.)P,(>.$<.(56.R2.)+32.)(3.(>.$?.(57.R2.R3.(3?.&40.=))$1;.)(3.(>.$?.(58.R2.R3.(3?.&40.=))$1;.)(3.(>.$?.(59.(3?.&40.=)R3.(3?.&40.=))$17.)(3.(>.$?.(59.(3?.&40.+3.)R3.(3?.&40.=))$1;.)(>.$?.(5:.(3?.&40.+3.)R3.(3?.&40.=))$17.)))))")
(* [comment removed for export] *).
Proof.
  intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b.
  rewrite Hc. repeat split; try (vm_compute; reflexivity).
  all: destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_free_not_contains : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pl,(=.(1.(2.&40.)(2.&40.)))Plo,(2.&40.)Pn,(2.&40.)P,(1:.=(6.&40.R1.))P,(>.$?.(1=.R4.R3.R2.)$17.)(>.$?.(20.R5.R4.R3.)$1;.)")
(* [comment removed for export] *).
Proof.
  intros l lo n Hn Hfree. unfold map_contains.
  apply Bool.not_true_iff_false. intros H. apply existsb_exists in H as ([b s] & Hin & H).
  cbn [fst snd] in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (State.region_free_In _ _ _ _ _ Hfree Hin) as Hov.
  unfold iv_overlap in Hov. apply andb_false_iff in Hov as [Hov|Hov]; apply Z.ltb_ge in Hov; lia.
Qed.

Lemma mmap_errnos_ENOMEM : forall e, In e mmap_errnos -> e = ENOMEM.
Proof. intros e [<-|[]]. reflexivity. Qed.
Lemma mprotect_errnos_ENOMEM : forall e, In e mprotect_errnos -> e = ENOMEM.
Proof. intros e [<-|[]]. reflexivity. Qed.

Lemma errno_ret_ENOMEM : errno_ret ENOMEM = Z_to_bv 64 (two64 - 12).
Proof. apply bv_eq. reflexivity. Qed.

Section OurSpecNodes.
Variable segs : list Segment.
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma stepacc_ecall_epend : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pregs,(5;.&5.(2.&40.))Ppc,(2.&40.)Pmem,P,(2.&40.)(3<.(2.&8.))Prom,P,(2.&40.)(3<.(2.&8.))Pw,(2.&20.)P,(>.(3<.(2.&20.))(45.Vsegs,R4.)(3>.(2.&20.)R1.))P,(>.$?.(47.R2.)$17.)(>.(5<.(5=.$5>.))(5?.Vsegs,(60.$61.R7.R6.R5.R4.))(62.(5=.$5>.)(63.$5>.(64.R7.R6.R5.R4.(65.R7.(66.&5.+11.$67.)))(38.$68.))))")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_instr_noacc : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pms,$5>.Pmodel,$21.Pms',$5>.P,(>.(3<.(2.&40.))(69.R2.)(41.(2.&40.)))P,(>.(3<.(2.&40.))(6:.R4.)(41.(2.&40.)))P,(>.(5<.(5=.$5>.))(5?.Vsegs,R5.)(62.(5=.$5>.)(63.$5>.R3.(38.$68.))))(6;.Vsegs,(6<.R6.R5.)$6=.L,$6=.(38.$6>.)L,$6=.(6<.R5.R6.))")
(* [comment removed for export] *).
Proof.
  intros ms model ms' Hh Hsvc Hstep.
  assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
  { unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
    rewrite materialize_model_accesses_nil. reflexivity. }
  split.
  - intros []. apply (sstep_instr segs ms model ms' model Hh Hsvc Hacc).
  - intros e st Hss. exists tt.
    inversion Hss; subst;
      match goal with
      | H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
      | H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
      end.
Qed.

#[using="Type"] Lemma srz_sys_lazy : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pregs,(5;.&5.(2.&40.))Ppc,(2.&40.)Pmem,P,(2.&40.)(3<.(2.&8.))Prom,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.Pw,(2.&20.)PT,$6?.P,(>.(3<.(2.&40.))(69.R3.)(41.(2.&40.)))P,(>.(3<.(2.&20.))(45.Vsegs,R7.)(3>.(2.&20.)R3.))P,(>.$?.(47.R4.)$17.)P,(70.Vsegs,(6<.(64.R:.R9.R8.R7.(65.R:.(66.&5.+11.$67.)))R6.)R4.)(70.Vsegs,(6<.(60.$61.R;.R:.R9.R8.)R7.)R5.)")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply srz_silent1; [| exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_chk_ev_mat : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pms,$5>.Pmodel,$21.Px8,(2.&40.)PI,StPeffs,P,R1.$71.Pms',P,R2.$21.Pevs,P,R3.(=.$6>.)P,(>.(3<.(2.&40.))(69.R6.)(41.(2.&40.)))P,(>.(3<.(2.&40.))(6:.R8.)(3>.(2.&40.)R6.))P,Pi,R6.(>.$72.(73.(74.Vsegs,R:.R8.)A1.R6.R1.R9.)(75.A1.R5.R1.A1.R4.R1.))P,Peff,$71.Pm',$21.Pev,(=.$6>.)P,(>.$72.(73.(74.Vsegs,R=.R;.)R3.R<.)(75.R2.R1.))(18.R;.Li,R;.(3.(>.$71.R5.A1.R;.R1.)(3.(>.$21.R4.A1.R:.R1.)(>.(=.$6>.)R3.A1.R9.R1.))))P,Peff,$71.(1<.(>.$72.(73.(74.Vsegs,R<.R:.)R1.R;.)$76.))P,Pi,R9.(>.(3<.(2.&40.))(69.A1.R8.R1.)(41.(2.&40.)))P,Pi,R:.(>.(=.(1.(2.&40.)$49.))(77.A1.R:.R1.)(38.(1.(2.&40.)$49.)))(6;.Vsegs,(6<.R>.R=.)R;.R8.Li,R;.(6<.(78.(79.R?.A1.R;.R1.))A1.R:.R1.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hacc. split.
  - intros i. apply (sstep_syscall segs ms model x8 (effs i) (ms' i) (ms' i) (evs i) Hh Hsvc).
    + apply check_syscall_ok_iff. exact (Hok i).
    + exact (Hh' i).
    + rewrite (Hacc i). apply materialize_model_accesses_nil.
  - intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hm & ->) | [(Hh2 & -> & Hm & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (Hacc i), materialize_model_accesses_nil in Hm. injection Hm as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite (Hacc i), materialize_model_accesses_nil in Hm. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite Hh' in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma epend_len : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pregs,(5;.&5.(2.&40.))Ppc,(2.&40.)Pmem,P,(2.&40.)(3<.(2.&8.))Prom,P,(2.&40.)(3<.(2.&8.))Plen,$<.P,(>.(2.&40.)(65.R5.(66.&5.+;.$67.))(3?.&40.R1.))P,(3.(1:.=R2.)(1:.R2.(48.+2.+40.)))(3.(>.$<.(6.&40.(7:.(64.R7.R6.R5.R4.(65.R7.(66.&5.+11.$67.)))#1.))R3.)(1<.(>.(2.&40.)(7:.(64.R7.R6.R5.R4.(65.R7.(66.&5.+11.$67.)))#1.)(3?.&40.=))))")
(* [comment removed for export] *).
Proof.
  intros regs pc mem rom len H11 Hlen. rewrite ms_gpr_epend1, H11. split.
  - apply u64_lit. lia.
  - intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma mmap_rw_check : forall ms x8 model eff flags,
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 1 <> Z_to_bv 64 0 -> ms_gpr ms 2 = Z_to_bv 64 3 ->
  ms_gpr ms 3 = flags -> mmap_flags_core flags = 34%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mmap_errnos r
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        else if grant_ok_na_pin model r nZ && mmap_noreserve_backed_ok flags model nZ
                && listNN_eqb zs [(r, Z_to_bv 64 nZ)]
        then CheckOk (with_mmap_backing flags r (Z_to_bv 64 nZ) (mmap_model r (Z_to_bv 64 nZ) model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags Hno H1 H2 H3 Hcore H4 H5 nZ.
  destruct (mmap_gates_core34 flags Hcore) as (Gm & _ & _).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm. cbn [negb]. cbv beta iota zeta. fold nZ.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct us; [|reflexivity]. destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
  destruct (errno_ret_in mmap_errnos r); [reflexivity|].
  unfold grant_ok_na_pin, mmap_model.
  destruct (mmap_noreserve_backed_ok flags model nZ); rewrite ?andb_true_r, ?andb_false_r; [reflexivity|].
  cbn [andb]. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_mmap_rw2 : forall regs (pc : word) mem rom model w (len : Z) (flags : word) KA KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> init_sp_ok (m_vmmaps model) ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 34%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (exists a, grant_ok_na_pin model a nZ = true /\ mmap_noreserve_backed_ok flags model nZ = true) ->
  srealizes0 segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) KA ->      (* [comment removed for export] *)
  (forall a, grant_ok_na_pin model a nZ = true -> mmap_noreserve_backed_ok flags model nZ = true ->
     srealizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom)
                          (with_mmap_backing flags a n (mmap_model a n model))) KB) ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) (t_alt2 KA KB).
(* [comment removed for export] *)
Proof.
  intros regs pc mem rom model w len flags KA KB HF HE Hh Hisp H17 H11 Hlen H12 H13 Hcore H14 H15 nZ n (a0 & Ha0 & Hb0) HA HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  destruct (epend_len regs pc mem rom len H11 Hlen) as [Hl1 Hne1]. fold ms in Hl1, Hne1.
  pose proof (fun eff => mmap_rw_check ms (getr regs 17) model eff flags Hno Hne1
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)) as Hchk.
  cbv zeta in Hchk. rewrite Hl1 in Hchk. fold nZ n in Hchk.
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  rewrite Hb0 in Hchk.
  assert (Hn0 : (0 <= nZ)%Z) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
  assert (HnZpos : (0 < nZ)%Z) by (unfold nZ; apply page_round_up_Z_pos'; lia).
  assert (HnZal : (nZ mod page_size = 0)%Z) by (unfold nZ; apply page_round_up_Z_aligned').
  pose (IB := {a : word | grant_ok_na_pin model a nZ = true}).
  pose (effs := fun i : unit + IB => match i with
                           | inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | inr (exist _ a _) => mkEffectU a [] [(a, n)] [] [] [] end).
  pose (ms' := fun i : unit + IB => match i with
                          | inl _ => model
                          | inr (exist _ a _) => with_mmap_backing flags a n (mmap_model a n model) end).
  assert (Hrb : forall i, refusal_b (sys_input segs ms (getr regs 17)) model
                            (ms_gpr (cfg_ms (mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))) 0)
                          = errno_ret_in mmap_errnos (eff_ret (effs i))).
  { intros i. cbn [cfg_ms]. rewrite ms_gpr0_advance_apply_effect.
    apply (refusal_b_mmap (sys_input segs ms (getr regs 17)) model). cbn [in_sysno sys_input]. exact Hno. }
  eapply (srz_alt2_sp segs ms model (getr regs 17) unit IB
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KA KB
            tt (exist _ a0 Ha0)).     (* [comment removed for export] *)
  - reflexivity.
  - apply (family_off_alloc (sys_input segs ms (getr regs 17))). cbn [in_sysno sys_input]. rewrite Hno. right; right; left; reflexivity.
  - apply (node_chk_ev_mat ms model (getr regs 17) (unit + IB) effs ms' (fun _ => []) Hh eq_refl).
    + intros [[] | [a Ha]]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * rewrite (grant_na_pin_not_errno model a nZ Hn0 Ha), Ha. cbn [andb].
        rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct zs; [|discriminate]. injection Hc as <- <-.
        destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
        rewrite (mmap_errnos_ENOMEM e He). exists (inl tt). repeat split; reflexivity.
      * destruct (grant_ok_na_pin model r nZ) eqn:Hg; [|discriminate].
        cbn [andb] in Hc.
        destruct (listNN_eqb zs [(r, n)]) eqn:Hl; [|discriminate].
        apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
        exists (inr (exist _ r Hg)). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
      destruct (grant_ok_na_pin model r nZ && true && listNN_eqb zs [(r, n)])%bool; discriminate.
    + intros [[] | [a Ha]]; cbn [ms']; [exact Hh | rewrite with_mmap_backing_halted; unfold mmap_model; rewrite with_vmmaps_halted; exact Hh].
    + intros [[] | [a Ha]]; reflexivity.
  - intros []. exact (eq_trans (Hrb (inl tt)) (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos)).
  - exact (eq_trans (Hrb (inr (exist _ a0 Ha0))) (grant_na_pin_not_errno model a0 nZ Hn0 Ha0)).
  - intros []. cbn [effs ms']. unfold ms. rewrite adv_ret_epend. exact HA.
  - intros [a Ha]. cbn [effs ms']. unfold ms. rewrite adv_zeros1_epend. apply HB; [exact Ha | exact Hb0].
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma mmap_none_check : forall ms x8 model eff flags,
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 1 <> Z_to_bv 64 0 -> ms_gpr ms 2 = Z_to_bv 64 0 ->
  ms_gpr ms 3 = flags -> mmap_flags_core flags = 34%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with [] => CheckOk model [] | _ => CheckReject end
        else if grant_ok_na_pin model r nZ && listNN_eqb us [(r, Z_to_bv 64 nZ)]
        then CheckOk (with_mmap_backing flags r (Z_to_bv 64 nZ) (noaccess_model r (Z_to_bv 64 nZ) model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags Hno H1 H2 H3 Hcore H4 H5 nZ.
  destruct (mmap_gates_core34 flags Hcore) as (_ & Gm & Gn).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn. cbn [negb]. cbv beta iota zeta. fold nZ.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
  destruct (errno_ret_in mmap_errnos r); [reflexivity|].
  unfold grant_ok_na_pin, noaccess_model. reflexivity.
Qed.

#[using="Type"] Lemma srz_mmap_none2 : forall regs (pc : word) mem rom model w (len : Z) (flags : word) KA KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> init_sp_ok (m_vmmaps model) ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = flags -> mmap_flags_core flags = 34%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (exists a, grant_ok_na_pin model a nZ = true) ->
  srealizes0 segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) KA ->      (* [comment removed for export] *)
  (forall a, grant_ok_na_pin model a nZ = true ->
     srealizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (unfill a n mem) rom)
                          (with_mmap_backing flags a n (noaccess_model a n model))) KB) ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) (t_alt2 KA KB).
(* [comment removed for export] *)
Proof.
  intros regs pc mem rom model w len flags KA KB HF HE Hh Hisp H17 H11 Hlen H12 H13 Hcore H14 H15 nZ n (a0 & Ha0) HA HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  destruct (epend_len regs pc mem rom len H11 Hlen) as [Hl1 Hne1]. fold ms in Hl1, Hne1.
  pose proof (fun eff => mmap_none_check ms (getr regs 17) model eff flags Hno Hne1
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)) as Hchk.
  cbv zeta in Hchk. rewrite Hl1 in Hchk. fold nZ n in Hchk.
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  assert (Hn0 : (0 <= nZ)%Z) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
  assert (HnZpos : (0 < nZ)%Z) by (unfold nZ; apply page_round_up_Z_pos'; lia).
  assert (HnZal : (nZ mod page_size = 0)%Z) by (unfold nZ; apply page_round_up_Z_aligned').
  pose (IB := {a : word | grant_ok_na_pin model a nZ = true}).
  pose (effs := fun i : unit + IB => match i with
                           | inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | inr (exist _ a _) => mkEffectU a [] [] [(a, n)] [] [] end).
  pose (ms' := fun i : unit + IB => match i with
                          | inl _ => model
                          | inr (exist _ a _) => with_mmap_backing flags a n (noaccess_model a n model) end).
  assert (Hrb : forall i, refusal_b (sys_input segs ms (getr regs 17)) model
                            (ms_gpr (cfg_ms (mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))) 0)
                          = errno_ret_in mmap_errnos (eff_ret (effs i))).
  { intros i. cbn [cfg_ms]. rewrite ms_gpr0_advance_apply_effect.
    apply (refusal_b_mmap (sys_input segs ms (getr regs 17)) model). cbn [in_sysno sys_input]. exact Hno. }
  eapply (srz_alt2_sp segs ms model (getr regs 17) unit IB
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KA KB
            tt (exist _ a0 Ha0)).     (* [comment removed for export] *)
  - reflexivity.
  - apply (family_off_alloc (sys_input segs ms (getr regs 17))). cbn [in_sysno sys_input]. rewrite Hno. right; right; left; reflexivity.
  - apply (node_chk_ev_mat ms model (getr regs 17) (unit + IB) effs ms' (fun _ => []) Hh eq_refl).
    + intros [[] | [a Ha]]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * rewrite (grant_na_pin_not_errno model a nZ Hn0 Ha), Ha. cbn [andb].
        rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct us; [|discriminate]. injection Hc as <- <-.
        destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
        rewrite (mmap_errnos_ENOMEM e He). exists (inl tt). repeat split; reflexivity.
      * destruct (grant_ok_na_pin model r nZ) eqn:Hg; [|discriminate].
        destruct (listNN_eqb us [(r, n)]) eqn:Hl; [|discriminate].
        apply listNN_eqb_eq in Hl. subst us. injection Hc as <- <-.
        exists (inr (exist _ r Hg)). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
      destruct (grant_ok_na_pin model r nZ && listNN_eqb us [(r, n)])%bool; discriminate.
    + intros [[] | [a Ha]]; cbn [ms']; [exact Hh | rewrite with_mmap_backing_halted; unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh].
    + intros [[] | [a Ha]]; reflexivity.
  - intros []. exact (eq_trans (Hrb (inl tt)) (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos)).
  - exact (eq_trans (Hrb (inr (exist _ a0 Ha0))) (grant_na_pin_not_errno model a0 nZ Hn0 Ha0)).
  - intros []. cbn [effs ms']. unfold ms. rewrite adv_ret_epend. exact HA.
  - intros [a Ha]. cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. apply HB. exact Ha.
Qed.

End OurSpecNodes.


Section OurSpecNodes2.
Variable segs : list Segment.

#[using="Type"] Lemma mmap_fixed_gate_open : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Ph,$86.Paddr,(2.&40.)Plen,$<.P,(>.$<.(3;.(6.&40.R2.)$31.)=)P,(1:.=(6.&40.R3.))P,(1:.=R3.)P,(4.(8.(6.&40.R5.)(7<.R4.))$87.)P,(7;.R7.)(3.(>.$?.(14.$88.(8.(6.&40.R7.)(7<.R6.)))$1;.)(3.(>.$?.(25.(14.(8.(6.&40.R7.)(7<.R6.))(89.R8.)))$1;.)(3.(>.$?.(25.(8:.(3;.(6.&40.R7.)$31.)=))$1;.)(3.(>.$?.(25.(15.=(6.&40.R7.)))$1;.)(3.(1:.R6.(48.+2.+40.))(3.(1:.=(7<.R6.))(1:.(7<.R6.)(48.+2.+40.))))))))")
(* [comment removed for export] *).
Proof.
  intros h addr len Hal Hpos Hlen Hce Hisp. pose proof alloc_ceiling_val.
  pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr).
  repeat split.
  - apply Z.leb_gt. unfold two_pow_64. lia.
  - rewrite (proj2 (Z.leb_le _ _) (alloc_top_ge_of_ceiling _ _ Hisp Hce)). reflexivity.
  - rewrite (proj2 (Z.eqb_eq _ _) Hal). reflexivity.
  - rewrite (proj2 (Z.ltb_lt _ _) Hpos). reflexivity.
  - lia. - lia. - lia.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma mmap_fixed_rw_free_check : forall ms x8 model eff flags (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  ms_gpr ms 2 = Z_to_bv 64 3 -> ms_gpr ms 3 = flags -> mmap_flags_core flags = 50%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mmap_errnos r
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        else if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_noreserve_backed_ok flags model nZ
        then CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hcore H4 H5 nZ n Hrf.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (G1 & G2 & G3 & G4 & Hlen' & HnZ).
  destruct (mmap_gates_core50 flags (Z_to_bv 64 3) Hcore) as (Gm & Gn & _ & Gfn & Gfr).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn, Gfn, Gfr. cbn [negb]. cbv beta iota zeta.
  rewrite G1, G2, G3, G4. fold nZ. fold n.
  assert (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = false).
  { apply region_free_not_contains; [unfold n; rewrite u64_lit by lia; lia|].
    rewrite RefNodes.region_free_app in Hrf. apply andb_true_iff in Hrf. tauto. }
  rewrite Hmc, andb_false_r, Hrf.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct us; [|destruct (errno_ret_in mmap_errnos r); [destruct zs|]; reflexivity].
  destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
  unfold mmap_model. reflexivity.
Qed.

#[using="Type"] Lemma srz_mmap_fixed_rw_free2 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KA KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 50%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  mmap_noreserve_backed_ok flags model nZ = true ->
  srealizes0 segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) KA ->      (* [comment removed for export] *)
  srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (zfill addr n mem) rom)
                       (with_mmap_backing flags addr n (mmap_model addr n model))) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) (t_alt2 KA KB).
(* [comment removed for export] *)
Proof.
  intros regs pc mem rom model w addr len flags KA KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15
         nZ n Hrf Hbk HA HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mmap_fixed_rw_free_check ms (getr regs 17) model eff flags addr len Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hce Hisp
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15) Hrf) as Hchk.
  cbv zeta in Hchk. fold nZ in Hchk. fold n in Hchk. rewrite Hbk in Hchk.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (_ & _ & _ & _ & _ & HnZ). fold nZ in HnZ.
  assert (Hna : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. pose proof alloc_ceiling_val. unfold two_pow_64. lia. }
  pose (effs := fun i : unit + unit => match i with
                           | inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | inr _ => mkEffectU addr [] [(addr, n)] [] [] [] end).
  pose (ms' := fun i : unit + unit => match i with
                          | inl _ => model
                          | inr _ => with_mmap_backing flags addr n (mmap_model addr n model) end).
  assert (Hrb : forall i, refusal_b (sys_input segs ms (getr regs 17)) model
                            (ms_gpr (cfg_ms (mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))) 0)
                          = errno_ret_in mmap_errnos (eff_ret (effs i))).
  { intros i. cbn [cfg_ms]. rewrite ms_gpr0_advance_apply_effect.
    apply (refusal_b_mmap (sys_input segs ms (getr regs 17)) model). cbn [in_sysno sys_input]. exact Hno. }
  eapply (srz_alt2_sp segs ms model (getr regs 17) unit unit
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KA KB tt tt).     (* [comment removed for export] *)
  - reflexivity.
  - apply (family_off_alloc (sys_input segs ms (getr regs 17))). cbn [in_sysno sys_input]. rewrite Hno. right; right; left; reflexivity.
  - apply (node_chk_ev_mat segs ms model (getr regs 17) (unit + unit) effs ms' (fun _ => []) Hh eq_refl).
    + intros [[] | []]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * rewrite Hna, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct zs; [|discriminate]. injection Hc as <- <-.
        destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
        rewrite (mmap_errnos_ENOMEM e He). exists (inl tt). repeat split; reflexivity.
      * destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r zs. cbn [andb] in Hc. injection Hc as <- <-.
        exists (inr tt). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
      destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)] && true)%bool; discriminate.
    + intros [[] | []]; cbn [ms']; [exact Hh | rewrite with_mmap_backing_halted; unfold mmap_model; rewrite with_vmmaps_halted; exact Hh].
    + intros [[] | []]; reflexivity.
  - intros []. exact (eq_trans (Hrb (inl tt)) (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos)).
  - exact (eq_trans (Hrb (inr tt)) Hna).
  - intros []. cbn [effs ms']. unfold ms. rewrite adv_ret_epend. exact HA.
  - intros []. cbn [effs ms']. unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma mmap_fixed_none_free_check : forall ms x8 model eff flags (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  ms_gpr ms 2 = Z_to_bv 64 0 -> ms_gpr ms 3 = flags -> mmap_flags_core flags = 50%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with [] => CheckOk model [] | _ => CheckReject end
        else if bv_eqb r addr && listNN_eqb us [(addr, n)]
        then CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hcore H4 H5 nZ n Hrf.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (G1 & G2 & G3 & G4 & Hlen' & HnZ).
  destruct (mmap_gates_core50 flags (Z_to_bv 64 0) Hcore) as (Gm & Gn & Gfn & _ & _).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn, Gfn. cbn [negb]. cbv beta iota zeta.
  rewrite G1, G2, G3, G4. fold nZ. fold n.
  assert (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = false).
  { apply region_free_not_contains; [unfold n; rewrite u64_lit by lia; lia|].
    rewrite RefNodes.region_free_app in Hrf. apply andb_true_iff in Hrf. tauto. }
  rewrite Hmc, andb_false_r, Hrf.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct zs; [|reflexivity].
  destruct cs; [|destruct (errno_ret_in mmap_errnos r); [destruct us|]; reflexivity].
  destruct ci; [|destruct (errno_ret_in mmap_errnos r); [destruct us|]; reflexivity].
  unfold noaccess_model. reflexivity.
Qed.

#[using="Type"] Lemma srz_mmap_fixed_none_free2 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KA KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = flags -> mmap_flags_core flags = 50%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  srealizes0 segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) KA ->      (* [comment removed for export] *)
  srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) rom)
                       (with_mmap_backing flags addr n (noaccess_model addr n model))) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) (t_alt2 KA KB).
(* [comment removed for export] *)
Proof.
  intros regs pc mem rom model w addr len flags KA KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15
         nZ n Hrf HA HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mmap_fixed_none_free_check ms (getr regs 17) model eff flags addr len Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hce Hisp
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15) Hrf) as Hchk.
  cbv zeta in Hchk. fold nZ in Hchk. fold n in Hchk.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (_ & _ & _ & _ & _ & HnZ). fold nZ in HnZ.
  assert (Hna : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. pose proof alloc_ceiling_val. unfold two_pow_64. lia. }
  pose (effs := fun i : unit + unit => match i with
                           | inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | inr _ => mkEffectU addr [] [] [(addr, n)] [] [] end).
  pose (ms' := fun i : unit + unit => match i with
                          | inl _ => model
                          | inr _ => with_mmap_backing flags addr n (noaccess_model addr n model) end).
  assert (Hrb : forall i, refusal_b (sys_input segs ms (getr regs 17)) model
                            (ms_gpr (cfg_ms (mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))) 0)
                          = errno_ret_in mmap_errnos (eff_ret (effs i))).
  { intros i. cbn [cfg_ms]. rewrite ms_gpr0_advance_apply_effect.
    apply (refusal_b_mmap (sys_input segs ms (getr regs 17)) model). cbn [in_sysno sys_input]. exact Hno. }
  eapply (srz_alt2_sp segs ms model (getr regs 17) unit unit
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KA KB tt tt).     (* [comment removed for export] *)
  - reflexivity.
  - apply (family_off_alloc (sys_input segs ms (getr regs 17))). cbn [in_sysno sys_input]. rewrite Hno. right; right; left; reflexivity.
  - apply (node_chk_ev_mat segs ms model (getr regs 17) (unit + unit) effs ms' (fun _ => []) Hh eq_refl).
    + intros [[] | []]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * rewrite Hna, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct us; [|discriminate]. injection Hc as <- <-.
        destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
        rewrite (mmap_errnos_ENOMEM e He). exists (inl tt). repeat split; reflexivity.
      * destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r us. injection Hc as <- <-.
        exists (inr tt). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
      destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; discriminate.
    + intros [[] | []]; cbn [ms']; [exact Hh | rewrite with_mmap_backing_halted; unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh].
    + intros [[] | []]; reflexivity.
  - intros []. exact (eq_trans (Hrb (inl tt)) (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos)).
  - exact (eq_trans (Hrb (inr tt)) Hna).
  - intros []. cbn [effs ms']. unfold ms. rewrite adv_ret_epend. exact HA.
  - intros []. cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. exact HB.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma srz_mprotect2 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) KA KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 226 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  getr regs 12 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = true ->
  srealizes0 segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) KA ->      (* [comment removed for export] *)
  srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill addr n mem) rom)
                       (mprotect_model addr n model)) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) (t_alt2 KA KB).
(* [comment removed for export] *)
Proof.
  intros regs pc mem rom model w addr len KA KB HF HE Hh H17 H10 Hal H11 Hlen Hnw H12 n Hna Hma Hbud HA HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 226%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mprotect_check segs ms (getr regs 17) model eff addr len Hno
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hnw
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12) Hna Hma) as Hchk.
  cbv zeta in Hchk. fold n in Hchk. rewrite Hbud in Hchk.
  pose (effs := fun i : unit + unit => match i with
                           | inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | inr _ => mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [] end).
  pose (ms' := fun i : unit + unit => match i with inl _ => model | inr _ => mprotect_model addr n model end).
  assert (Hrb : forall i, refusal_b (sys_input segs ms (getr regs 17)) model
                            (ms_gpr (cfg_ms (mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))) 0)
                          = errno_ret_in mprotect_errnos (eff_ret (effs i))).
  { intros i. cbn [cfg_ms]. rewrite ms_gpr0_advance_apply_effect.
    apply (refusal_b_mprotect (sys_input segs ms (getr regs 17)) model). cbn [in_sysno sys_input]. exact Hno. }
  eapply (srz_alt2_sp segs ms model (getr regs 17) unit unit
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KA KB tt tt).     (* [comment removed for export] *)
  - reflexivity.
  - apply (family_off_alloc (sys_input segs ms (getr regs 17))). cbn [in_sysno sys_input]. rewrite Hno. right; right; right; reflexivity.
  - apply (node_chk_ev_mat segs ms model (getr regs 17) (unit + unit) effs ms' (fun _ => []) Hh eq_refl).
    + intros [[] | []]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mprotect_errnos). reflexivity.
      * change (errno_ret_in mprotect_errnos (Z_to_bv 64 0)) with false.
        unfold w_is0. rewrite bv_eqb_refl. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mprotect_errnos r) eqn:Er.
      * destruct zs; [|discriminate]. injection Hc as <- <-.
        destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
        rewrite (mprotect_errnos_ENOMEM e He). exists (inl tt). repeat split; reflexivity.
      * cbn [andb] in Hc. destruct (w_is0 r) eqn:E0; [|discriminate].
        destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
        apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
        unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r.
        exists (inr tt). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate|].
      cbn [andb] in Hc. destruct (w_is0 r && listNN_eqb zs [(addr, n)])%bool; discriminate.
    + intros [[] | []]; cbn [ms']; [exact Hh | unfold mprotect_model; rewrite with_vmmaps_halted; exact Hh].
    + intros [[] | []]; reflexivity.
  - intros []. exact (eq_trans (Hrb (inl tt)) (errno_ret_in_intro _ _ ENOMEM_in_mprotect_errnos)).
  - exact (eq_trans (Hrb (inr tt)) eq_refl).
  - intros []. cbn [effs ms']. unfold ms. rewrite adv_ret_epend. exact HA.
  - intros []. cbn [effs ms']. unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

End OurSpecNodes2.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma page_base_aligned' : forall p : word, bv_unsigned p mod 4096 = 0 -> page_base p = p.
Proof.
  intros p Hp. unfold page_base, page_base_of, page_size. apply bv_eq. pose proof (u64_range p).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  rewrite u64_lit; lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma iv_subtract_contained : forall (a sz : word) lo hi,
  bv_unsigned a <= lo -> hi <= bv_unsigned a + bv_unsigned sz -> lo <= hi ->
  iv_subtract a sz lo hi
  = (if bv_unsigned a <? lo then [(a, Z_to_bv 64 (lo - bv_unsigned a))] else [])
    ++ (if hi <? bv_unsigned a + bv_unsigned sz then [(Z_to_bv 64 hi, Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - hi))] else []).
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite Z.min_r by lia. rewrite Z.max_r by lia. reflexivity.
Qed.

Lemma map_replace_entry : forall (f : amap -> word * word) l m pcs,
  map f (replace_entry l m pcs) = flat_map (fun m' => if amap_eqb m' m then map f pcs else [f m']) l.
Proof.
  intros f l m pcs. unfold replace_entry. rewrite flat_map_concat_map, concat_map, map_map, <- flat_map_concat_map.
  apply flat_map_ext. intros m'. destruct (amap_eqb m' m); reflexivity.
Qed.

Lemma maps_subtract_map_replace : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pf,P,$8>.(1.(2.&40.)(2.&40.))Pl,(=.$8>.)Pm,$8>.Ppcs,(=.$8>.)Plo,$<.Phi,$<.P,Pm',$8>.P,(19.$8>.R1.R6.)P,(>.$?.(8?.R2.R6.)$1;.)(>.(=.(1.(2.&40.)(2.&40.)))(34.(7.(2.&40.)(2.&40.)A1.R9.R3.)(9.(2.&40.)(2.&40.)A1.R9.R3.)R5.R4.)(11.(1.(2.&40.)(2.&40.))A1.R9.R3.(38.(1.(2.&40.)(2.&40.)))))P,Pm',$8>.P,(19.$8>.R1.R7.)P,(>.$?.(8?.R2.R7.)$17.)(>.(=.(1.(2.&40.)(2.&40.)))(34.(7.(2.&40.)(2.&40.)A1.R:.R3.)(9.(2.&40.)(2.&40.)A1.R:.R3.)R6.R5.)(90.$8>.(1.(2.&40.)(2.&40.))R:.R7.))(>.(=.(1.(2.&40.)(2.&40.)))(37.(90.$8>.(1.(2.&40.)(2.&40.))R8.R7.)R4.R3.)(90.$8>.(1.(2.&40.)(2.&40.))R8.(91.R7.R6.R5.)))")
(* [comment removed for export] *).
Proof.
  intros f l m pcs lo hi Hout Hin. rewrite map_replace_entry.
  induction l as [|m' l IH]; [reflexivity|]. cbn [map flat_map maps_subtract].
  destruct (f m') as [a sz] eqn:Ef. cbn [maps_subtract].
  rewrite (IH ltac:(intros x Hx; apply Hout; right; exact Hx) ltac:(intros x Hx; apply Hin; right; exact Hx)). f_equal.
  destruct (amap_eqb m' m) eqn:Heq.
  - rewrite <- (Hin m' (or_introl eq_refl) Heq), Ef. reflexivity.
  - pose proof (Hout m' (or_introl eq_refl) Heq) as X. rewrite Ef in X. cbn [fst snd] in X. exact X.
Qed.

Lemma in_replace_entry : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pl,(=.$8>.)Pm,$8>.Ppcs,(=.$8>.)Pm',$8>.P,(19.$8>.R1.(91.R4.R3.R2.))(35.(3.(19.$8>.R2.R5.)(1<.(>.$8>.R2.R4.)))(3.(19.$8>.R4.R5.)(19.$8>.R2.R3.)))")
(* [comment removed for export] *).
Proof.
  intros l m pcs m' H. unfold replace_entry in H. apply in_flat_map in H as (m0 & Hm0 & Hin).
  destruct (amap_eqb m0 m) eqn:He.
  - apply APS.amap_eqb_eq in He. subst m0. right. auto.
  - destruct Hin as [<-|[]]. left. split; [exact Hm0|]. intros ->. rewrite amap_eqb_refl in He. discriminate.
Qed.

Lemma maps_subtract_in_pieces : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pl,(=.(1.(2.&40.)(2.&40.)))Pb,(2.&40.)Ps,(2.&40.)Plo,$<.Phi,$<.Pq,(1.(2.&40.)(2.&40.))P,(19.(1.(2.&40.)(2.&40.))(1?.(2.&40.)(2.&40.)R5.R4.)R6.)P,(19.(1.(2.&40.)(2.&40.))R2.(34.R6.R5.R4.R3.))(19.(1.(2.&40.)(2.&40.))R3.(37.R8.R5.R4.))")
(* [comment removed for export] *).
Proof.
  induction l as [|[a sz] l IH]; intros b s lo hi q Hin Hq; [destruct Hin|].
  cbn [maps_subtract]. apply in_app_iff. destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. left. exact Hq.
  - right. eapply IH; eassumption.
Qed.

Lemma seps_app_intro : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pl1,(=.(1.(2.&40.)(2.&40.)))Pl2,(=.(1.(2.&40.)(2.&40.)))P,(92.R2.)P,(92.R2.)P,Pp,(1.(2.&40.)(2.&40.))Pq,(1.(2.&40.)(2.&40.))P,(19.(1.(2.&40.)(2.&40.))R2.R6.)P,(19.(1.(2.&40.)(2.&40.))R2.R6.)(93.R4.R3.)(92.(1>.(1.(2.&40.)(2.&40.))R5.R4.))")
(* [comment removed for export] *).
Proof.
  induction l1 as [|p l1 IH]; intros l2 H1 H2 H12; [exact H2|].
  inversion H1 as [|p' l' Hf Hl]; subst. cbn [app]. constructor.
  - apply Forall_app. split; [exact Hf|]. apply Forall_forall. intros q Hq. apply H12; [left; reflexivity | exact Hq].
  - apply IH; [exact Hl | exact H2 |]. intros a b Ha Hb. apply H12; [right; exact Ha | exact Hb].
Qed.

Lemma seps_iv_subtract : forall (a sz : word) lo hi,
  iv_wf (a, sz) -> lo <= hi -> seps (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hwf Hlh. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. unfold iv_subtract.
  assert (S1 : forall p : word * word, seps [p]) by (intros p; apply seps_cons; [apply Forall_nil | apply seps_nil]).
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app];
    try apply S1; try apply seps_nil.
  apply seps_cons; [|apply S1]. apply Forall_cons; [|apply Forall_nil].
  unfold iv_disjoint. cbn [fst snd]. rewrite !u64_lit by lia. left. lia.
Qed.

Lemma seps_maps_subtract : forall l lo hi,
  seps l -> ivs_wf l -> lo <= hi -> seps (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hs Hwf Hlh; [constructor|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. inversion Hs as [|p' l' Hf Htl]; subst.
  cbn [maps_subtract]. apply seps_app_intro; [apply seps_iv_subtract; assumption | apply IH; assumption |].
  intros p q Hp Hq.
  destruct (iv_subtract_pieces a sz lo hi p Ha Hp) as (P1 & P2 & P3).
  destruct (maps_subtract_pieces l lo hi q Hl Hq) as (r & Hr & Q1 & Q2 & Q3).
  pose proof (proj1 (Forall_forall _ _) Hf r Hr) as D. unfold iv_disjoint in *. cbn [fst snd] in *. lia.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_bounds : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pa,(2.&40.)Psz,(2.&40.)Plo,$<.Phi,$<.Pq,(1.(2.&40.)(2.&40.))Pih,$<.Pce,$<.P,(>.$<.(3;.R5.+1000.)=)P,(>.$<.(3;.R5.+1000.)=)P,(1:.=(6.&40.R8.))P,(>.$<.(3;.(6.&40.R:.)+1000.)=)P,(>.$<.(3;.(6.&40.R:.)+1000.)=)P,(4.R7.(6.&40.R<.))P,(4.(8.(6.&40.R=.)(6.&40.R<.))R7.)P,(4.R8.(48.+2.+40.))P,(19.(1.(2.&40.)(2.&40.))R;.(34.R?.R>.R=.R<.))(3.(1:.=(6.&40.(9.(2.&40.)(2.&40.)R<.)))(3.(>.$<.(3;.(6.&40.(7.(2.&40.)(2.&40.)R<.))+1000.)=)(3.(>.$<.(3;.(6.&40.(9.(2.&40.)(2.&40.)R<.))+1000.)=)(3.(4.R;.(6.&40.(7.(2.&40.)(2.&40.)R<.)))(4.(8.(6.&40.(7.(2.&40.)(2.&40.)R<.))(6.&40.(9.(2.&40.)(2.&40.)R<.)))R:.)))))")
(* [comment removed for export] *).
Proof.
  intros a sz lo hi q ih ce Hlo Hhi Hsz Hal Hszl Hih Hce Hce64 Hq.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract in Hq. apply in_app_iff in Hq as [Hq|Hq].
  - destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hq]. destruct Hq as [<-|[]]. cbn [fst snd].
    rewrite u64_lit by lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    destruct (Z.le_gt_cases (bv_unsigned sz) (lo - bv_unsigned a)); [rewrite Z.min_l by lia | rewrite Z.min_r by lia]; repeat split; try lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hq]. destruct Hq as [<-|[]]. cbn [fst snd].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    destruct (Z.le_gt_cases hi (bv_unsigned a)); [rewrite !Z.max_l by lia | rewrite !Z.max_r by lia]; rewrite !u64_lit by lia; repeat split; try lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma maps_subtract_bounds : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pl,(=.(1.(2.&40.)(2.&40.)))Plo,$<.Phi,$<.Pih,$<.Pce,$<.P,(>.$<.(3;.R4.+1000.)=)P,(>.$<.(3;.R4.+1000.)=)P,(4.R3.(48.+2.+40.))P,(0.(1.(2.&40.)(2.&40.))Liv,(1.(2.&40.)(2.&40.))(3.(1:.=(6.&40.(9.(2.&40.)(2.&40.)R1.)))(3.(>.$<.(3;.(6.&40.(7.(2.&40.)(2.&40.)R1.))+1000.)=)(3.(>.$<.(3;.(6.&40.(9.(2.&40.)(2.&40.)R1.))+1000.)=)(3.(4.R6.(6.&40.(7.(2.&40.)(2.&40.)R1.)))(4.(8.(6.&40.(7.(2.&40.)(2.&40.)R1.))(6.&40.(9.(2.&40.)(2.&40.)R1.)))R5.)))))R8.)(0.(1.(2.&40.)(2.&40.))Liv,(1.(2.&40.)(2.&40.))(3.(1:.=(6.&40.(9.(2.&40.)(2.&40.)R1.)))(3.(>.$<.(3;.(6.&40.(7.(2.&40.)(2.&40.)R1.))+1000.)=)(3.(>.$<.(3;.(6.&40.(9.(2.&40.)(2.&40.)R1.))+1000.)=)(3.(4.R7.(6.&40.(7.(2.&40.)(2.&40.)R1.)))(4.(8.(6.&40.(7.(2.&40.)(2.&40.)R1.))(6.&40.(9.(2.&40.)(2.&40.)R1.)))R6.)))))(37.R9.R8.R7.))")
(* [comment removed for export] *).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi ih ce Hlo Hhi Hce HB; [constructor|].
  apply Forall_cons_iff in HB as [(B1 & B2 & B3 & B4 & B5) HBl]. cbn [fst snd] in B1, B2, B3, B4, B5.
  cbn [maps_subtract]. apply Forall_app. split; [|apply IH; assumption].
  apply Forall_forall. intros q Hq. exact (iv_subtract_bounds a sz lo hi q ih ce Hlo Hhi B1 B2 B3 B4 B5 Hce Hq).
Qed.

Lemma sum_sizes_maps_subtract_le : forall l lo hi, ivs_wf l -> lo <= hi -> sum_sizes (maps_subtract l lo hi) <= sum_sizes l.
Proof.
  intros l lo hi Hwf Hlh. rewrite !sum_sizes_live, !live_bytes_sum_count.
  rewrite (proj1 (proj2 (maps_subtract_sem l lo hi Hwf Hlh))). apply sum_count_mono. intros; reflexivity.
Qed.

Lemma ledger_split_maps_subtract : forall l lo hi K Y, ivs_wf l -> ledger_split l K Y -> ledger_split (maps_subtract l lo hi) K Y.
Proof.
  intros l lo hi K Y Hwf H b s Hin. destruct (maps_subtract_pieces l lo hi (b, s) Hwf Hin) as ([b' s'] & Hr & R1 & R2 & _).
  cbn [fst snd] in R1, R2. destruct (H b' s' Hr); lia.
Qed.

Lemma replace_entry_notin : forall ms m pcs, ~ In m ms -> replace_entry ms m pcs = ms.
Proof.
  intros ms m pcs H. induction ms as [|h t IH]; [reflexivity|]. unfold replace_entry in *. cbn [flat_map].
  destruct (amap_eqb h m) eqn:He.
  - apply APS.amap_eqb_eq in He. subst h. exfalso. apply H. left. reflexivity.
  - cbn [app]. f_equal. apply IH. intros Hin. apply H. right. exact Hin.
Qed.

Lemma maps_subtract_disjoint_id : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pl,(=.(1.(2.&40.)(2.&40.)))Plo,$<.Phi,$<.P,(1:.R2.R1.)P,Piv,(1.(2.&40.)(2.&40.))P,(19.(1.(2.&40.)(2.&40.))R1.R5.)(3.(1:.=(6.&40.(9.(2.&40.)(2.&40.)R2.)))(35.(4.(8.(6.&40.(7.(2.&40.)(2.&40.)R2.))(6.&40.(9.(2.&40.)(2.&40.)R2.)))R5.)(4.R4.(6.&40.(7.(2.&40.)(2.&40.)R2.)))))(>.(=.(1.(2.&40.)(2.&40.)))(37.R5.R4.R3.)R5.)")
(* [comment removed for export] *).
Proof.
  intros l lo hi Hlh H. induction l as [|[a sz] l IH]; [reflexivity|]. cbn [maps_subtract].
  destruct (H (a, sz) (or_introl eq_refl)) as [P D]. cbn [fst snd] in P, D.
  rewrite (iv_subtract_disjoint a sz lo hi Hlh P D). cbn [app]. f_equal. apply IH. intros iv Hiv. apply H. right. exact Hiv.
Qed.

Lemma maps_match_app_pcs : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Ppcs,(=.$8>.)Pms,(=.$8>.)Pl,(=.(1.(2.&40.)(2.&40.)))P,Ppc,$8>.P,(19.$8>.R1.R4.)(>.$?.(95.R2.)$1;.)P,(96.R5.R3.R2.)(96.R6.(1>.$8>.R5.R4.)(1>.(1.(2.&40.)(2.&40.))(90.$8>.(1.(2.&40.)(2.&40.))(97.R6.)R5.)R3.))")
(* [comment removed for export] *).
Proof.
  intros E pcs ms l Hpf HM. induction pcs as [|pc pcs IH]; [exact HM|]. cbn [app map maps_match].
  rewrite (Hpf pc (or_introl eq_refl)). exists (map (amap_den E) pcs ++ l). split; [reflexivity|].
  apply IH. intros x Hx. apply Hpf. right. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma maps_match_subtract : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pms,(=.$8>.)Pl,(=.(1.(2.&40.)(2.&40.)))Pm,$8>.Ppcs,(=.$8>.)Plo,$<.Phi,$<.P,(96.R7.R6.R5.)P,(92.R6.)P,Piv,(1.(2.&40.)(2.&40.))P,(19.(1.(2.&40.)(2.&40.))R1.R8.)(1:.=(6.&40.(9.(2.&40.)(2.&40.)R2.)))P,(19.$8>.R7.R9.)P,(>.$?.(95.R8.)$1;.)P,(1:.R7.R6.)P,(4.(6.&40.(98.R=.(99.R:.)))R8.)P,(4.R8.(8.(6.&40.(98.R>.(99.R;.)))(6.&40.(98.R>.(9:.R;.)))))P,(>.(=.(1.(2.&40.)(2.&40.)))(90.$8>.(1.(2.&40.)(2.&40.))(97.R?.)R;.)(34.(98.R?.(99.R<.))(98.R?.(9:.R<.))R:.R9.))P,Ppc,$8>.P,(19.$8>.R1.R=.)(>.$?.(95.R2.)$1;.)(96.R11.(91.R10.R>.R=.)(37.R?.R<.R;.))")
(* [comment removed for export] *).
Proof.
  intros E ms. induction ms as [|h t IH]; intros l m pcs lo hi HM Hs Hpos Hm Hf Hlh Hc1 Hc2 Hpcs Hpf; [destruct Hm|].
  cbn [maps_match] in HM. unfold replace_entry. cbn [flat_map]. fold (replace_entry t m pcs).
  destruct (is_fog h) eqn:Hfh.
  - assert (He : amap_eqb h m = false).
    { destruct (amap_eqb h m) eqn:He; [|reflexivity]. apply APS.amap_eqb_eq in He. subst h. congruence. }
    rewrite He. cbn [app maps_match]. rewrite Hfh.
    assert (Hmt : In m t) by (destruct Hm as [<-|Hm]; [congruence | exact Hm]).
    destruct HM as [HM | ([a sz] & l' & -> & Hsz & HM)].
    + left. eapply IH; eassumption.
    + right. inversion Hs as [|p l0 Hfa Hl]; subst. cbn [maps_subtract].
      pose proof (proj1 (Forall_forall _ _) Hfa (amap_den E m) (maps_match_In E t l' m HM Hmt Hf)) as D.
      unfold iv_disjoint, amap_den in D. cbn [fst snd] in D.
      rewrite (iv_subtract_disjoint a sz lo hi Hlh (Hpos (a, sz) (or_introl eq_refl)) ltac:(lia)). cbn [app].
      exists (a, sz), (maps_subtract l' lo hi). split; [reflexivity|]. split; [exact Hsz|].
      eapply IH; try eassumption. intros iv Hiv. apply Hpos. right. exact Hiv.
  - destruct HM as (l' & -> & HM). inversion Hs as [|p l0 Hfa Hl]; subst.
    unfold amap_den at 1. cbn [maps_subtract].
    destruct (amap_eqb h m) eqn:He.
    + apply APS.amap_eqb_eq in He. subst h.
      assert (Hnot : ~ In m t).
      { intros Hmt. pose proof (proj1 (Forall_forall _ _) Hfa (amap_den E m) (maps_match_In E t l' m HM Hmt Hf)) as D.
        pose proof (Hpos (amap_den E m) (or_introl eq_refl)) as P. unfold iv_disjoint, amap_den in D, P. cbn [fst snd] in D, P. lia. }
      rewrite (replace_entry_notin t m pcs Hnot). rewrite <- Hpcs.
      rewrite (maps_subtract_disjoint_id l' lo hi Hlh).
      2:{ intros iv Hiv. split; [apply Hpos; right; exact Hiv|].
          pose proof (proj1 (Forall_forall _ _) Hfa iv Hiv) as D. unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. lia. }
      apply maps_match_app_pcs; [exact Hpf | exact HM].
    + assert (Hmt : In m t) by (destruct Hm as [<-|Hm]; [rewrite amap_eqb_refl in He; discriminate | exact Hm]).
      pose proof (proj1 (Forall_forall _ _) Hfa (amap_den E m) (maps_match_In E t l' m HM Hmt Hf)) as D.
      unfold iv_disjoint, amap_den in D. cbn [fst snd] in D.
      pose proof (Hpos _ (or_introl eq_refl)) as P. unfold amap_den in P. cbn [snd] in P.
      rewrite (iv_subtract_disjoint (edenot E (am_base h)) (edenot E (am_len h)) lo hi Hlh P ltac:(lia)). cbn [app maps_match]. rewrite Hfh.
      exists (maps_subtract l' lo hi). split; [reflexivity|].
      eapply IH; try eassumption. intros iv Hiv. apply Hpos. right. exact Hiv.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Nodes.
Variable SEGS : list Segment.            Variable A : atable.
Variable nx0 : nat.                      Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "(0.(1.(2.&40.)(2.&40.))Liv,(1.(2.&40.)(2.&40.))(3.(4.(5.VA,)(6.&40.(7.(2.&40.)(2.&40.)R1.)))(4.(8.(6.&40.(7.(2.&40.)(2.&40.)R1.))(6.&40.(9.(2.&40.)(2.&40.)R1.)))(:.VA,)))(;.VSEGS,))")
(* [comment removed for export] *).
Hypothesis HULL_ok : hull_ok A.                  Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis HULL_cov : APS.hull_cov SEGS A.   (* [comment removed for export] *)
Variable SP0 : Z.                        (* [comment removed for export] *)
Hypothesis SP0_ok : APS.sp0_ok SP0.
Hypothesis argH_high : forall E (a : word), argH E a = true -> SP0 <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.PM,Px,(2.&40.)(3<.(2.&8.))PM',Px,(2.&40.)(3<.(2.&8.))P,Pa,(2.&40.)P,(>.$?.A2.VargH,R4.R1.$17.)(>.(3<.(2.&8.))A1.R3.R2.A1.R4.R2.)P,Pa,(2.&40.)P,(4.VSP0,(6.&40.R1.))P,(1<.(>.(3<.(2.&8.))A1.R5.R2.(41.(2.&8.))))(1<.(>.(3<.(2.&8.))A1.R5.R3.(41.(2.&8.))))P,A2.VSINV,R5.R4.A2.VSINV,R6.R4.")
(* [comment removed for export] *).   (* [comment removed for export] *)
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis SINV_sp : forall E M, SINV E M -> APS.uE_sp0 E = SP0.   (* [comment removed for export] *)

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT SP0 SINV argH FS0).
#[local] Notation HID := (APS.hid A SP0 argH).
#[local] Notation VIS := (APS.vis A SP0).
#[local] Notation MR := (APS.Mr A SP0 argH).
#[local] Notation ALLOW := (APS.allowA A).
#[local] Notation cfg := (cfg_of SEGS).

(* [comment removed for export] *)
Let HS : nat -> option acs := fun _ => None.
Let XN : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let XE : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let XB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.
Let RES_len' : length (segments_reserved SEGS) = n_res A := RES_len.
Let HULL_ok' : 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI := HULL_ok.
Let SHADOW_ok' : 0 <= shadow_off A <= 2 ^ 47 := SHADOW_ok.
Let RES_hullH : RES_hull_def SEGS A := RES_hull.

(* [comment removed for export] *)
Let reg_sound' := APS.reg_sound SEGS A LIMIT SP0 SINV argH FS0.
Let reg_lit_sound' := APS.reg_lit_sound SEGS A LIMIT SP0 SINV argH FS0.
Let kentry_keep_sem' := APS.kentry_keep_sem SEGS.
Let kentry_apart_b_sem' := APS.kentry_apart_b_sem SEGS.
Let regs_ok_set_n' := APS.regs_ok_set_n.
Let in_ivs_map_den' := APS.in_ivs_map_den.
Let kimg_clip_in_hull' := APS.kimg_clip_in_hull A.
Let cs_ok_agree' := APS.cs_ok_agree SEGS A nx0 LIMIT SP0 SINV argH argH_agree SINV_agree FS0.
Let cs_ok_frame' := APS.cs_ok_frame SEGS A LIMIT SP0 SINV argH SINV_frame FS0.
Let hid_agree' := APS.hid_agree A nx0 SP0 argH argH_agree.
Let vis_add_sound' := APS.vis_add_sound SEGS A LIMIT HS XN XE XB SHADOW_ok SP0 SP0_ok SINV argH argH_high FS0 0%nat.
Let A_wf_allowA' := APS.A_wf_allowA A HS XN XE XB 0%nat.
Let know_ok_unhide' := APS.know_ok_unhide SEGS A.
Let hid_hull' := APS.hid_hull A HULL_ok SP0 SP0_ok argH argH_high.
Let H_off_segments_cs' := APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok SP0 SP0_ok argH argH_high.
Let maps_match_exact' := APS.maps_match_exact nx0 HS XN XE XB.

(* [comment removed for export] *)
#[local] Notation ATOP := (APS.ATOP SP0).
Let ATOP_facts' := APS.ATOP_facts SP0 SP0_ok.
Ltac atopb := first [pose proof ATOP_facts' as ATB | idtac].
#[using="SINV_sp"] Lemma cs_sp0 : forall E cs R FULL model, CSOK E cs R FULL model -> APS.uE_sp0 E = SP0.
Proof. intros E cs R FULL model HC. exact (SINV_sp _ _ (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)). Qed.
#[using="Type"] Lemma cs_atop : forall E cs R FULL model, CSOK E cs R FULL model -> alloc_top (m_vmmaps model) = ATOP.
Proof. intros E cs R FULL model HC. unfold alloc_top, stack_max_size, APS.ATOP. rewrite (co_isp _ _ _ _ _ _ _ _ _ _ _ _ HC). reflexivity. Qed.
(* [comment removed for export] *)
#[using="SEGS A RES_len SP0_ok RES_len' ATOP_facts'"] Lemma estart_sp0 : forall E, APS.uE_sp0 E = SP0 -> estart E (SA e_sp0 (-8388608)) = ATOP.
Proof.
  intros E H. unfold estart. cbn [a_base a_off]. atopb.
  destruct (APS.uE_sp0_sound E SP0 ltac:(unfold APS.ATOP in *; lia) H) as (U & _). unfold APS.uE in U. rewrite U. unfold APS.ATOP. lia.
Qed.
(* [comment removed for export] *)
Definition STKB : Z := SP0 - SP0 mod 4096 - 8388608.
#[using="SEGS A RES_len SP0_ok RES_len' ATOP_facts'"] Lemma estart_stkpg : forall E, APS.uE_sp0 E = SP0 -> estart E (SA e_stkpg (-8388608)) = STKB.
Proof.
  intros E H. unfold estart. cbn [a_base a_off]. atopb.
  destruct (APS.uE_sp0_sound E SP0 ltac:(unfold APS.ATOP in *; lia) H) as (_ & U & _). unfold APS.uE in U. rewrite U. unfold STKB. lia.
Qed.
#[using="SEGS A RES_len SP0_ok RES_len' ATOP_facts'"] Lemma u_e_stkbase : forall E, APS.uE_sp0 E = SP0 -> bv_unsigned (edenot E e_stkbase) = STKB.
Proof.
  intros E H. atopb. destruct (APS.uE_sp0_sound E SP0 ltac:(unfold APS.ATOP in *; lia) H) as (_ & _ & U & _). unfold APS.uE in U. rewrite U. unfold STKB. lia.
Qed.
#[using="SEGS A RES_len SP0_ok RES_len' ATOP_facts'"] Lemma u_e_sp0_of : forall E, APS.uE_sp0 E = SP0 -> bv_unsigned (edenot E e_sp0) = SP0.
Proof.
  intros E H. atopb. destruct (APS.uE_sp0_sound E SP0 ltac:(unfold APS.ATOP in *; lia) H) as (U & _). unfold APS.uE in U. exact U.
Qed.
(* [comment removed for export] *)
#[using="SEGS A RES_len HULL_ok SP0_ok RES_len' HULL_ok' ATOP_facts'"] Lemma end_le_STKB : forall lo n, lo mod 4096 = 0 -> n mod 4096 = 0 -> lo + n <= ATOP -> lo + n <= STKB.
Proof.
  intros lo n Hl Hn H. unfold STKB, APS.ATOP in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="RES_len HULL_ok RES_len' HULL_ok' reg_sound' reg_lit_sound'"] Lemma mmap_len_sound : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pcs,$43.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.Pne,$4:.Pnlo,$<.Pnhi,$<.P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R8.R7.R6.R5.R4.)P,(>.(3<.(1.(1.$4:.$<.)$<.))(9<.R8.)(3>.(1.(1.$4:.$<.)$<.)(1?.(1.$4:.$<.)$<.(1?.$4:.$<.R4.R3.)R2.)))Zlen,$<.(6.&40.(98.R:.(9=.R9.#;.)))(3.(>.(2.&40.)(65.R9.(3?.&5.+;.))(3?.&40.R1.))(3.(3.(1:.=R1.)(1:.R1.(48.+2.+40.)))(3.(>.(2.&40.)(98.R;.R6.)(3?.&40.(7<.R1.)))(3.(1:.=R5.)(3.(3.(4.R5.(7<.R1.))(4.(7<.R1.)R4.))(3.(>.$<.(3;.(7<.R1.)+1000.)=)PE',$94.P,(>.(2.&40.)(98.R1.(9=.R;.#;.))(98.R<.(9=.R;.#;.)))(>.(2.&40.)(98.R2.R8.)(98.R=.R8.))))))))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model ne nlo nhi HC HML len.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (reg_sound' E cs R FULL model 11 HC ltac:(lia)) as R11. change (Z.of_nat 11) with 11 in R11.
  pose proof (u64_range (edenot E (reg cs 11))) as Hr.
  rewrite mmap_len_eq in HML. (* [comment removed for export] *) unfold mmap_len_ref in HML.
  destruct (reg_lit cs 11) as [lz|] eqn:H11.
  - destruct (Z.ltb_spec 0 lz); [|discriminate]. injection HML as <- <- <-.
    destruct (reg_lit_sound' E cs R FULL model 11 lz HC ltac:(lia) H11) as [R11' Hlz]. change (Z.of_nat 11) with 11 in R11'.
    assert (Hlen : len = lz).
    { unfold len. rewrite <- R11, R11'. apply u64_lit. unfold two64 in Hlz. lia. }
    rewrite Hlen. pose proof (page_round_up_Z_bounds lz ltac:(lia)) as PB. unfold page_size in PB.
    rewrite page_up_eq.
    split; [exact R11'|]. split; [unfold two64 in Hlz; lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [apply page_round_up_Z_aligned'|]. intros E' _. reflexivity.
  - destruct (xlo (kn cs) (reg cs 11)) as [lo|] eqn:Hxl; [|discriminate].
    destruct (xhi (kn cs) (reg cs 11)) as [hi|] eqn:Hxh; [|discriminate].
    match type of HML with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    injection HML as <- <- <-.
    apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hlo Hal].
    apply Z.ltb_lt in Hlo. apply Z.leb_le in Hal. apply Z.leb_le in Hhi.
    pose proof (xlo_sound SEGS E _ (kn cs) _ lo HK Hxl) as B1.
    pose proof (xhi_sound SEGS E _ (kn cs) _ hi HK Hxh) as B2.
    destruct (ealign_sound SEGS E _ (kn cs) (reg cs 11) HK) as [_ Hdiv].
    assert (Hmod : len mod 4096 = 0).
    { unfold len. destruct Hdiv as [q Hq]. rewrite Hq.
      replace (2 ^ ealign (kn cs) (reg cs 11)) with (2 ^ (ealign (kn cs) (reg cs 11) - 12) * 4096)
        by (rewrite <- (Z.pow_add_r 2 _ 12) by lia; f_equal; lia).
      rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
    assert (Hpr : page_round_up_Z len = len).
    { unfold page_round_up_Z, page_size.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). unfold len in *. lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    rewrite Hpr.
    split; [rewrite R11; symmetry; apply Z_to_bv_bv_unsigned|].
    split; [unfold len in *; lia|]. split; [symmetry; apply Z_to_bv_bv_unsigned|].
    split; [lia|]. split; [unfold len in *; lia|]. split; [exact Hmod|].
    intros E' HE'. exact HE'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma bv5_of_nat : forall n, (n < 32)%nat -> Z_to_bv 5 (Z.of_nat n) = Z_to_bv 5 (Z.of_nat n). Proof. reflexivity. Qed.
#[using="Type"] Lemma bv5_10 : (10%bv : bv 5) = Z_to_bv 5 (Z.of_nat 10). Proof. apply bv_eq. reflexivity. Qed.
#[using="Type"] Lemma bv5_11 : (11%bv : bv 5) = Z_to_bv 5 (Z.of_nat 11). Proof. apply bv_eq. reflexivity. Qed.
#[using="Type"] Lemma bv5_12 : (12%bv : bv 5) = Z_to_bv 5 (Z.of_nat 12). Proof. apply bv_eq. reflexivity. Qed.
#[using="Type"] Lemma bv5_13 : (13%bv : bv 5) = Z_to_bv 5 (Z.of_nat 13). Proof. apply bv_eq. reflexivity. Qed.
#[using="Type"] Lemma bv5_14 : (14%bv : bv 5) = Z_to_bv 5 (Z.of_nat 14). Proof. apply bv_eq. reflexivity. Qed.
#[using="Type"] Lemma bv5_15 : (15%bv : bv 5) = Z_to_bv 5 (Z.of_nat 15). Proof. apply bv_eq. reflexivity. Qed.
#[using="Type"] Lemma bv5_17 : (17%bv : bv 5) = Z_to_bv 5 (Z.of_nat 17). Proof. apply bv_eq. reflexivity. Qed.

#[using="Type"] Lemma some_inj : forall {T} (a b : T), Some a = Some b -> a = b.
Proof. intros T a b H. injection H as H1. exact H1. Qed.

#[using="Type"] Lemma CEIL_eq : alloc_ceiling = CEIL.
Proof. reflexivity. Qed.
#[using="Type"] Lemma KHI_eq : kHighMemBeg = KHI.
Proof. reflexivity. Qed.
#[using="Type"] Lemma FLOOR_eq : bottomup_floor = FLOOR.
Proof. rewrite bottomup_floor_val. reflexivity. Qed.

#[using="Type"] Lemma Z_to_bv64_m1 : forall m1, m1 = two64 - 1 -> Z_to_bv 64 m1 = Z_to_bv 64 (-1).
Proof. intros m1 ->. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
#[using="RES_len RES_hull HULL_ok RES_len' HULL_ok' RES_hullH"] Lemma reserved_free_above : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pmodel,$21.Plo,(2.&40.)Pn,(2.&40.)P,(>.(=.(1.(2.&40.)(2.&40.)))(8;.(28.R3.))(;.VSEGS,))P,(4.(:.VA,)(6.&40.R3.))(>.$?.(1=.(8;.(28.R5.))R4.R3.)$17.)")
(* [comment removed for export] *).
Proof.
  intros model lo n Hres Hlo. rewrite Hres. apply RefNodes.region_free_intro. intros b s Hin.
  pose proof (proj1 (Forall_forall _ _) RES_hullH _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2. right. lia.
Qed.

(* [comment removed for export] *)
#[using="RES_len RES_hull HULL_ok RES_len' HULL_ok' RES_hullH"] Lemma reserved_free_apart : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pmodel,$21.Plo,(2.&40.)Pn,(2.&40.)P,(>.(=.(1.(2.&40.)(2.&40.)))(8;.(28.R3.))(;.VSEGS,))P,(9>.VA,(6.&40.R3.)(6.&40.R2.))(>.$?.(1=.(8;.(28.R5.))R4.R3.)$17.)")
(* [comment removed for export] *).
Proof.
  intros model lo n Hres Hlo. rewrite Hres. apply RefNodes.region_free_intro. intros b s Hin.
  pose proof (proj1 (Forall_forall _ _) RES_hullH _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2. unfold hull_apart in Hlo. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma vis_add_inv : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pcs,$43.Pb,$4:.Pn,$4:.Pk,(=.$9?.)Pcs2,$43.P,(>.(3<.$43.)(:0.VA,VLIMIT,R5.R4.R3.R2.)(3>.$43.R1.))(18.$<.Lnhi,$<.(3.(>.(3<.$<.)(:1.(:2.R7.)R5.)(3>.$<.R1.))(>.$43.R3.(:3.(:4.(46.R7.)(:5.(:6.R7.))(1>.$9?.(:7.VA,(:2.R7.)(:8.R7.)R6.R5.)R4.)(:9.R7.))(:8.R7.)(::.R7.)(:;.R7.)(:<.R7.)(11.(1.$4:.$4:.)(1?.$4:.$4:.R6.R5.)(:=.R7.))(:>.R7.)(8.(:?.R7.)(;0.R1.))(;1.R7.)(;2.R7.)(;3.R7.)(;4.R7.)))))")
(* [comment removed for export] *).
Proof.
  intros cs b n k cs2 Hv. rewrite vis_add_eq in Hv. (* [comment removed for export] *) unfold vis_add_ref in Hv.
  destruct (split_lit b) as [bb bk]. destruct (shadow_of A (kn cs) b n) as [[sb sk] sn] eqn:Hsh.
  destruct (xhi (kn cs) n) as [nhi|]; [|discriminate].
  match type of Hv with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  injection Hv as <-. exists nhi. split; [reflexivity|]. unfold shadow_facts. rewrite Hsh. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma in_allow_ext : forall E cs cs', a_vis cs' = a_vis cs -> in_allow A E cs' = in_allow A E cs.
Proof. intros E cs cs' H. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kind_none (k : mkind) : bool := match k with KNONE | KNONELAZY => true | _ => false end.
Definition kind_lazy (k : mkind) : bool := match k with KRWLAZY | KNONELAZY => true | _ => false end.

Record grant_post (kd : mkind) (a n : word) (model model' : Model) : Prop := GP {
  gp_maps : vm_maps (m_vmmaps model') = (a, n) :: vm_maps (m_vmmaps model);
  gp_res : vm_reserved (m_vmmaps model') = vm_reserved (m_vmmaps model);
  gp_noacc : vm_noaccess (m_vmmaps model') = (if kind_none kd then (a, n) :: vm_noaccess (m_vmmaps model) else vm_noaccess (m_vmmaps model));
  gp_lazy : m_vm_lazy model' = (if kind_lazy kd then (a, n) :: m_vm_lazy model else m_vm_lazy model);
  gp_mat : m_vm_materialized model' = m_vm_materialized model;
  gp_limit : vm_limit (m_vmmaps model') = vm_limit (m_vmmaps model);
  gp_brk : vm_brk (m_vmmaps model') = vm_brk (m_vmmaps model);
  gp_sbrk : vm_start_brk (m_vmmaps model') = vm_start_brk (m_vmmaps model);
  gp_mbase : vm_mmap_base (m_vmmaps model') = vm_mmap_base (m_vmmaps model);
  gp_halted : m_halted model' = m_halted model;
  gp_fds : m_fds model' = m_fds model;
  gp_fs : m_fs model' = m_fs model;
  gp_tid : m_tid model' = m_tid model;
  gp_isp : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model)  (* [comment removed for export] *) }.

Definition grant_mem (kd : mkind) (a n : word) (FULL FULL' : word -> option byte) : Prop :=
  (forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x -> FULL' x = FULL x)
  /\ (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n ->
        FULL' x = if kind_none kd then None else Some (Z_to_bv 8 0)).

(* [comment removed for export] *)
#[using="SEGS RES_len RES_len'"] Lemma vis_grant_out : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pkd,$;5.Pa,(2.&40.)Pn,(2.&40.)Pmodel,$21.Pmodel',$21.PE,$94.Pcs,$43.Pcs1,$43.Px,(2.&40.)P,(;6.R9.R8.R7.R6.R5.)P,(>.(=.(1.$4:.$4:.))(:=.R3.)(:=.R4.))P,(1:.=(6.&40.R9.))P,(>.$<.(3;.(6.&40.R;.)+1000.)=)P,(>.$<.(3;.(6.&40.R;.)+1000.)=)P,(35.(1:.(6.&40.R6.)(6.&40.R=.))(4.(8.(6.&40.R=.)(6.&40.R<.))(6.&40.R6.)))(>.$?.(;7.VA,VSP0,R:.R8.R;.R7.)(;7.VA,VSP0,R:.R9.R<.R7.))")
(* [comment removed for export] *).
Proof.
  intros kd a n model model' E cs cs1 x GPo Hvis Hn Hal Hnl Hx.
  unfold vis. rewrite (gp_maps _ _ _ _ _ GPo), (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo).
  rewrite (in_allow_ext E cs cs1 Hvis).
  rewrite in_ivs_cons. cbn [fst snd].
  assert (T : ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + bv_unsigned n))%bool = false).
  { apply andb_false_iff. destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
  rewrite T. cbn [orb].
  assert (P : page_in_ranges (page_base x) ((a, n) :: m_vm_lazy model) = page_in_ranges (page_base x) (m_vm_lazy model)).
  { apply page_in_ranges_cons_out; [|exact Hn].
    pose proof (page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + bv_unsigned n) Hal ltac:(rewrite Z.add_mod, Hal, Hnl by lia; reflexivity) Hx).
    unfold page_size. lia. }
  destruct (kind_none kd); destruct (kind_lazy kd); rewrite ?in_ivs_cons; cbn [fst snd]; rewrite ?T, ?P; cbn [orb]; reflexivity.
Qed.

#[using="SEGS A RES_len RES_len'"] Lemma grant_wf : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pkd,$;5.Pa,(2.&40.)Pn,(2.&40.)Pmodel,$21.Pmodel',$21.P,(;6.R5.R4.R3.R2.R1.)P,(22.R3.)P,(4.(8.(6.&40.R6.)(6.&40.R5.))(48.+2.+40.))(22.R4.)")
(* [comment removed for export] *).
Proof.
  intros kd a n model model' GPo (W1 & W2 & W3 & Wsp) Hb. unfold model_ivs_wf.
  rewrite (gp_maps _ _ _ _ _ GPo), (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo).
  assert (iv_wf (a, n)) by (unfold iv_wf, B, S; cbn; lia).
  split; [apply ivs_wf_cons; assumption|].
  split; [destruct (kind_none kd); try apply ivs_wf_cons; assumption|].
  split; [destruct (kind_lazy kd); try apply ivs_wf_cons; assumption|].
  unfold init_sp_ok in *. rewrite (gp_isp _ _ _ _ _ GPo). exact Wsp.
Qed.

(* [comment removed for export] *)
#[using="SEGS A RES_len HULL_ok RES_len' HULL_ok'"] Lemma grant_eager_le : forall kd a n model model',
  grant_post kd a n model model' -> model_ivs_wf model -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  eager_used model' <= eager_used model + (if (kind_none kd || kind_lazy kd)%bool then 0 else bv_unsigned n).
Proof.
  intros kd a n model model' GPo Hwf Hb.
  pose proof (grant_wf kd a n model model' GPo Hwf Hb) as Hwf'.
  rewrite (eager_used_sem model' Hwf'), (eager_used_sem model Hwf).
  rewrite (gp_maps _ _ _ _ _ GPo).
  set (C := vm_noaccess (m_vmmaps model) ++ m_vm_lazy model).
  set (C' := vm_noaccess (m_vmmaps model') ++ m_vm_lazy model').
  cbn [sum_count].
  assert (MONO : sum_count (fun x => negb (covered C' x)) (vm_maps (m_vmmaps model))
                 <= sum_count (fun x => negb (covered C x)) (vm_maps (m_vmmaps model))).
  { apply sum_count_negb_covered_mono. intros x Hx. subst C C'.
    rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). rewrite covered_app in Hx. rewrite covered_app.
    apply orb_true_iff in Hx. apply orb_true_iff.
    destruct Hx as [Hx|Hx]; [left|right]; [destruct (kind_none kd) | destruct (kind_lazy kd)]; try exact Hx;
      unfold covered in *; cbn [existsb]; rewrite Hx; apply orb_true_r. }
  assert (HEAD : iv_count (fun x => negb (covered C' x)) (a, n) <= (if (kind_none kd || kind_lazy kd)%bool then 0 else bv_unsigned n)).
  { destruct (kind_none kd || kind_lazy kd)%bool eqn:Hk.
    - unfold iv_count, B, S. cbn [fst snd]. rewrite zcount_false; [lia|]. intros x Hx.
      pose proof (u64_range n). rewrite Z2Nat.id in Hx by lia. apply negb_false_iff.
      subst C'. rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). rewrite covered_app.
      assert (IN : in_iv (a, n) x = true).
      { unfold in_iv, in_rng, B, S. cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
      apply orb_prop in Hk as [Hk|Hk]; rewrite Hk; unfold covered; cbn [existsb]; rewrite IN; cbn [orb];
        [reflexivity | apply orb_true_r].
    - unfold iv_count, S. cbn [snd]. pose proof (u64_range n).
      pose proof (zcount_le_len (fun x => negb (covered C' x)) (B (a, n)) (Z.to_nat (bv_unsigned n))). lia. }
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition maps_apart (E : env) (ms : list amap) (lo n : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pm,$8>.P,(19.$8>.R1.O3.)P,(>.$?.(95.R2.)$1;.)(35.(4.(8.O2.O1.)(6.&40.(98.O4.(99.R3.))))(4.(8.(6.&40.(98.O4.(99.R3.)))(6.&40.(98.O4.(9:.R3.))))O2.))")
(* [comment removed for export] *).

#[using="Type"] Lemma maps_apart_of_region_free : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pms,(=.$8>.)Pmodel,$21.Pa,(2.&40.)Pn,(2.&40.)P,(96.R5.R4.(2:.(28.R3.)))P,(>.$?.(1=.(1>.(1.(2.&40.)(2.&40.))(8;.(28.R4.))(2:.(28.R4.)))R3.R2.)$17.)(;8.R7.R6.(6.&40.R4.)(6.&40.R3.))")
(* [comment removed for export] *).
Proof.
  intros E ms model a n Hmaps Hrf m Hin Hnf.
  rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf].
  exact (RefNodes.region_free_In _ a n (edenot E (am_base m)) (edenot E (am_len m)) Hrf (maps_match_In E ms _ m Hmaps Hin Hnf)).
Qed.

(* [comment removed for export] *)
#[using="SEGS A RES_len HULL_ok RES_len' HULL_ok'"] Lemma coalesce1_cov : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Piv,(1.$<.$<.)Pruns,(=.(1.$<.$<.))Pr,(1.$<.$<.)Px,$<.P,(19.(1.$<.$<.)R2.(;9.R4.R3.))P,(3.(4.(7.$<.$<.R3.)R2.)(1:.R2.(8.(7.$<.$<.R3.)(9.$<.$<.R3.))))(35.(3.(4.(7.$<.$<.R6.)R3.)(1:.R3.(8.(7.$<.$<.R6.)(9.$<.$<.R6.))))(18.(1.$<.$<.)Lr',(1.$<.$<.)(3.(19.(1.$<.$<.)R1.R6.)(3.(4.(7.$<.$<.R1.)R4.)(1:.R4.(8.(7.$<.$<.R1.)(9.$<.$<.R1.)))))))")
(* [comment removed for export] *).
Proof.
  intros iv runs. revert iv. induction runs as [|r0 rest IH]; intros iv r x Hin Hx.
  - cbn in Hin. destruct Hin as [<-|[]]. left. exact Hx.
  - cbn [coalesce1] in Hin.
    destruct (Z.eqb (fst iv + snd iv) (fst r0)) eqn:E1.
    + apply Z.eqb_eq in E1. destruct (IH _ r x Hin Hx) as [H|[r' [Hr' Hx']]].
      * cbn [fst snd] in H. destruct (Z_lt_le_dec x (fst iv + snd iv)); [left; lia | right; exists r0; split; [left; reflexivity | lia]].
      * right. exists r'. split; [right; exact Hr' | exact Hx'].
    + destruct (Z.eqb (fst r0 + snd r0) (fst iv)) eqn:E2.
      * apply Z.eqb_eq in E2. destruct (IH _ r x Hin Hx) as [H|[r' [Hr' Hx']]].
        -- cbn [fst snd] in H. destruct (Z_lt_le_dec x (fst r0 + snd r0)); [right; exists r0; split; [left; reflexivity | lia] | left; lia].
        -- right. exists r'. split; [right; exact Hr' | exact Hx'].
      * destruct Hin as [<-|Hin]; [right; exists r0; split; [left; reflexivity | exact Hx]|].
        destruct (IH _ r x Hin Hx) as [H|[r' [Hr' Hx']]]; [left; exact H | right; exists r'; split; [right; exact Hr' | exact Hx']].
Qed.

#[using="SEGS A RES_len HULL_ok RES_len' HULL_ok'"] Lemma coalesce_cov : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pivs,(=.(1.$<.$<.))Pr,(1.$<.$<.)Px,$<.P,(19.(1.$<.$<.)R2.(;:.R3.))P,(3.(4.(7.$<.$<.R3.)R2.)(1:.R2.(8.(7.$<.$<.R3.)(9.$<.$<.R3.))))(18.(1.$<.$<.)Liv,(1.$<.$<.)(3.(19.(1.$<.$<.)R1.R6.)(3.(4.(7.$<.$<.R1.)R4.)(1:.R4.(8.(7.$<.$<.R1.)(9.$<.$<.R1.))))))")
(* [comment removed for export] *).
Proof.
  induction ivs as [|iv ivs IH]; intros r x Hin Hx; [destruct Hin|].
  cbn [coalesce fold_right] in Hin. change (fold_right coalesce1 [] ivs) with (coalesce ivs) in Hin.
  destruct (coalesce1_cov iv (coalesce ivs) r x Hin Hx) as [H|[r' [Hr' Hx']]].
  - exists iv. split; [left; reflexivity | exact H].
  - destruct (IH r' x Hr' Hx') as [iv' [H1 H2]]. exists iv'. split; [right; exact H1 | exact H2].
Qed.

#[using="SEGS A RES_len RES_len'"] Lemma lit_ivs_In : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pms,(=.$8>.)Pz,$<.Pl,$<.P,(19.(1.$<.$<.)(1?.$<.$<.R2.R1.)(;;.R3.))(18.$8>.Lm,$8>.(3.(19.$8>.R1.R5.)(3.(>.$?.(95.R1.)$1;.)(3.(>.$<.(;<.R6.(99.R1.))R4.)(3.(>.$<.(;<.R6.(9:.R1.))R3.)(3.(3.(4.=R4.)(1:.R4.$;=.))(3.(1:.=R3.)(1:.R3.$;=.))))))))")
(* [comment removed for export] *).
Proof.
  intros E ms z l H. unfold lit_ivs in H. apply in_flat_map in H as [m [Hm H]].
  destruct (is_fog m) eqn:Hf; [destruct H|].
  destruct (am_base m) as [zb| | | | | | |] eqn:Hb; try (destruct H; fail); try solve [destruct (am_len m); destruct H].
  destruct (am_len m) as [zl| | | | | | |] eqn:Hl; try solve [destruct H].
  match type of H with In _ (if ?c then _ else _) => destruct c eqn:Hc; [|destruct H] end.
  destruct H as [H|[]]. injection H as <- <-.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  apply Z.leb_le in Hc. apply Z.ltb_lt in X1. apply Z.ltb_lt in X0. apply Z.ltb_lt in X.
  exists m. rewrite Hb, Hl. unfold uE. rewrite !edenot_lit, !u64_lit by (unfold two64 in *; lia).
  unfold two64 in *. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
#[using="SEGS A RES_len HULL_ok RES_len' HULL_ok'"] Lemma lit_run_apart : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pms,(=.$8>.)Pr,(1.$<.$<.)Plo,$<.Pn,$<.P,(;8.R5.R4.R2.R1.)P,(1:.=R2.)P,(19.(1.$<.$<.)R5.(;>.R6.))(35.(4.(8.(7.$<.$<.R6.)(9.$<.$<.R6.))R5.)(4.(8.R5.R4.)(7.$<.$<.R6.)))")
(* [comment removed for export] *).
Proof.
  intros E ms r lo n Hapart Hn Hr. unfold lit_runs in Hr. apply filter_In in Hr as [Hr Hck].
  apply andb_prop in Hck as [Hck _]. apply andb_prop in Hck as [Hck R3]. apply andb_prop in Hck as [R1 R2].
  apply Z.leb_le in R1. apply Z.ltb_lt in R2.
  assert (RUN : forall x, fst r <= x < fst r + snd r -> lo + n <= x \/ x < lo).
  { intros x Hx. destruct (coalesce_cov _ r x Hr Hx) as [[z l] [Hin Hzl]]. cbn [fst snd] in Hzl.
    destruct (lit_ivs_In E ms z l Hin) as (m & Hm & Hfm & Uz & Ul & Rz & Rl).
    pose proof (Hapart m Hm Hfm) as D. unfold uE in Uz, Ul. rewrite Uz, Ul in D. lia. }
  destruct (Z_le_gt_dec (fst r + snd r) lo) as [L1|L1]; [left; lia|].
  destruct (Z_le_gt_dec (lo + n) (fst r)) as [L2|L2]; [right; lia|]. exfalso.
  pose proof (RUN (Z.max lo (fst r)) ltac:(lia)). lia.
Qed.

#[using="A RES_len HULL_ok RES_len' HULL_ok'"] Lemma inside_runs_apart : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.PM,P,(2.&40.)(3<.(2.&8.))Pk,(=.$9?.)Pms,(=.$8>.)Pb,$4:.Po,$<.Pl,$4:.Plo,$<.Pn,$<.P,(;?.VSEGS,R9.R8.R7.)P,(;8.R:.R7.R3.R2.)P,(1:.=R3.)P,(>.$?.(<0.R:.(;>.R9.)R8.R7.R6.)$17.)(35.(4.(8.(<1.R=.(<2.R9.R8.))(<3.R=.R7.))R6.)(4.(8.R6.R5.)(<1.R=.(<2.R9.R8.))))")
(* [comment removed for export] *).
Proof.
  intros E M k ms b o l lo n HK Hap Hn H. unfold inside_runs in H. apply existsb_exists in H as [r [Hr Hx]].
  pose proof (xinside_sound SEGS E M k b o l (ELit 0) (fst r) (ELit (snd r)) HK Hx) as [I1 I2].
  unfold lit_runs in Hr. pose proof Hr as Hr0. apply filter_In in Hr as [_ Hck].
  apply andb_prop in Hck as [Hck _]. apply andb_prop in Hck as [Hck R3]. apply andb_prop in Hck as [R1 R2].
  apply Z.leb_le in R1. apply Z.ltb_lt in R2. apply Z.ltb_lt in R3. unfold two64 in R3.
  assert (E0 : bv_unsigned (edenot E (ELit 0)) = 0) by (cbn [edenot]; apply u64_lit; lia).
  assert (Es : bv_unsigned (edenot E (ELit (snd r))) = snd r) by (cbn [edenot]; apply u64_lit; lia).
  unfold estart, elenZ in I1, I2 |- *. cbn [a_base a_off] in I1, I2 |- *.
  rewrite ?E0, ?Es in I1. rewrite ?E0, ?Es in I2.
  pose proof (lit_run_apart E ms r lo n Hap Hn Hr0) as D. lia.
Qed.

#[using="A RES_len HULL_ok RES_len' HULL_ok'"] Lemma inside_maps_apart : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.PM,P,(2.&40.)(3<.(2.&8.))Pk,(=.$9?.)Pms,(=.$8>.)Pb,$4:.Po,$<.Pl,$4:.Plo,$<.Pn,$<.P,(;?.VSEGS,R9.R8.R7.)P,(;8.R:.R7.R3.R2.)P,(>.$?.(<4.R9.R8.R7.R6.R5.)$17.)(35.(4.(8.(<1.R<.(<2.R8.R7.))(<3.R<.R6.))R5.)(4.(8.R5.R4.)(<1.R<.(<2.R8.R7.))))")
(* [comment removed for export] *).
Proof.
  intros E M k ms b o l lo n HK Hap. induction ms as [|m ms IH]; intros H; [discriminate|].
  cbn [inside_maps] in H. apply orb_prop in H as [H|H].
  - apply andb_prop in H as [Hnf H]. apply negb_true_iff in Hnf.
    pose proof (xinside_sound SEGS E M k b o l (am_base m) 0 (am_len m) HK H) as [I1 I2].
    unfold estart in I1, I2 |- *. cbn [a_base a_off] in *. unfold elenZ in *.
    destruct (Hap m (or_introl eq_refl) Hnf); lia.
  - apply IH; [|exact H]. intros m' Hm'. apply Hap. right. exact Hm'.
Qed.

(* [comment removed for export] *)
#[using="RES_len HULL_ok SP0_ok RES_len' HULL_ok' ATOP_facts'"] Lemma safe_range_apart : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.PM,P,(2.&40.)(3<.(2.&8.))Pk,(=.$9?.)Pms,(=.$8>.)Pb,$4:.Po,$<.Pl,$4:.Plo,$<.Pn,$<.P,(;?.VSEGS,R9.R8.R7.)P,(;8.R:.R7.R3.R2.)P,(1:.=R3.)P,(9>.VA,R5.R4.)P,(>.$<.(<5.R=.)VSP0,)P,(4.(8.R7.R6.)(<6.VSP0,))P,(>.$?.(<7.VA,R=.R<.R;.R:.R9.)$17.)(35.(4.(8.(<1.R10.(<2.R<.R;.))(<3.R10.R:.))R9.)(4.(8.R9.R8.)(<1.R10.(<2.R<.R;.))))")
(* [comment removed for export] *).
Proof.
  intros E M k ms b o l lo n HK Hap Hn Hha Hsp Hhi H. unfold safe_range in H.
  apply orb_prop in H as [H|H]; [|exact (inside_runs_apart E M k ms b o l lo n HK Hap Hn H)].
  apply orb_prop in H as [H|H].
  - destruct (xhi k l) as [lh|] eqn:Hlh; [|discriminate]. destruct (base_range k b) as [[blo bhi]|] eqn:Hb; [|discriminate].
    pose proof (xhi_sound SEGS E M k l lh HK Hlh) as L1. pose proof (base_range_sound SEGS E M k b blo bhi HK Hb) as [B1 B2].
    unfold hull_apart in Hha. unfold estart, elenZ. cbn [a_base a_off].
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H2.
    + (* [comment removed for export] *)
      pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as G. cbn [xt_den] in G.
      rewrite (u_e_sp0_of E Hsp) in G. unfold APS.ATOP in Hhi. lia.
    + apply Z.leb_le in H1. lia.
  - eapply inside_maps_apart; eassumption.
Qed.

#[using="RES_len HULL_ok SP0_ok RES_len' HULL_ok' ATOP_facts'"] Lemma grant_keep_apart : forall E M k ms K lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n -> 0 < n -> hull_apart A lo n -> APS.uE_sp0 E = SP0 -> lo + n <= ATOP ->
  grant_keep_b A k ms K = true ->
  match K with KImg _ _ => False | _ => True end ->
  kfoot_apart E K lo n.
Proof.
  intros E M k ms K lo n HK Hap Hn Hha Hsp Hhi H HnI. unfold kfoot_apart, kfoot.
  destruct K as [[b o] w v|[b o] l|[b o] l kb|ilo ihi|e m|e rlo rhi|[b o] l|a1 n1 a2 n2|[b o] l fc|[b o] l]; cbn [grant_keep_b] in H;
    try exact I; [apply andb_prop in H as [Hw H]; apply Nat.leb_le in Hw| | | destruct HnI | | |];
    pose proof (safe_range_apart E M k ms b o _ lo n HK Hap Hn Hha Hsp Hhi H) as D; try lia.
  rewrite elenZ_lit'' in D by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="RES_len HULL_ok SP0_ok RES_len' HULL_ok' kentry_keep_sem' kimg_clip_in_hull' ATOP_facts'"] Lemma kn_grant_filter_ok : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.PM,P,(2.&40.)(3<.(2.&8.))PM',Px,(2.&40.)(3<.(2.&8.))Pk,(=.$9?.)Pms,(=.$8>.)Plo,$<.Pn,$<.P,(;?.VSEGS,R7.R6.R4.)P,(;8.R8.R4.R3.R2.)P,(1:.=R3.)P,(9>.VA,R5.R4.)P,(>.$<.(<5.R;.)VSP0,)P,(4.(8.R7.R6.)(<6.VSP0,))P,Px,(2.&40.)P,(35.(1:.(6.&40.R1.)R9.)(4.(8.R9.R8.)(6.&40.R1.)))(>.(3<.(2.&8.))A1.R=.R2.A1.R>.R2.)(;?.VSEGS,R>.R<.(<8.VA,R;.R:.))")
(* [comment removed for export] *).
Proof.
  intros E M M' k ms lo n HK Hap Hn Hha Hsp Hhi Hout. unfold kn_grant_filter.
  pose proof (kimg_clip_in_hull' (List.filter (grant_keep_b A k ms) k)) as Hhull.
  unfold know_ok. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) Hhull K Hin) as HKh.
  apply kimg_clip_incl in Hin. apply filter_In in Hin as [Hin Hkeep].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  eapply kentry_keep_sem'; [exact HKK | | exact Hout].
  destruct K as [| | |ilo ihi| | | | | |];
    try (eapply grant_keep_apart; [exact HK | exact Hap | exact Hn | exact Hha | exact Hsp | exact Hhi | exact Hkeep | exact I]).
  (* [comment removed for export] *)
  unfold kfoot_apart, kfoot. unfold hull_apart in Hha. cbn in HKh. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="SEGS A RES_len RES_len'"] Lemma regs_ok_regupd_same : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Psr,(=.$4:.)PR,(5;.&5.(2.&40.))Pn,$49.Pv,(2.&40.)P,(<9.R5.R4.R3.)P,(3.(4<.#0.R3.)(4<.R3.#20.))P,(>.(2.&40.)(65.R5.(3?.&5.(2>.R4.)))R3.)(<9.R8.R7.(7?.R6.(3?.&5.(2>.R5.))R4.))")
(* [comment removed for export] *).
Proof.
  intros E sr R n v HR Hn Hv r.
  assert (Hne : Z_to_bv 5 (Z.of_nat n) <> 0%bv).
  { intros Hz. apply (f_equal bv_unsigned) in Hz. rewrite Z_to_bv_unsigned in Hz. unfold bv_wrap in Hz.
    change (bv_modulus 5) with 32%Z in Hz. rewrite Z.mod_small in Hz by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z in Hz by reflexivity. lia. }
  destruct (bv_eqb r (Z_to_bv 5 (Z.of_nat n))) eqn:Hr.
  - apply (proj1 (bv_eqb_eq _ _)) in Hr. subst r. rewrite getr_same by exact Hne. rewrite <- Hv. apply HR.
  - assert (Hr' : r <> Z_to_bv 5 (Z.of_nat n)) by (intros ->; rewrite bv_eqb_refl in Hr; discriminate).
    rewrite getr_other by exact Hr'. apply HR.
Qed.

(* [comment removed for export] *)
#[using="RES_len HULL_ok HULL_cov RES_len' HULL_ok'"] Lemma free_hull_apart : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pcs,$43.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.Pa,(2.&40.)Pn,(2.&40.)P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R7.R6.R5.R4.R3.)P,(>.$?.(1=.(1>.(1.(2.&40.)(2.&40.))(8;.(28.R4.))(2:.(28.R4.)))R3.R2.)$17.)P,(1:.=(6.&40.R3.))(9>.VA,(6.&40.R5.)(6.&40.R4.))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model a n HC Hrf Hn.
  rewrite region_free_app in Hrf. apply andb_prop in Hrf as [Hrf1 _].
  rewrite (co_res _ _ _ _ _ _ _ _ _ _ _ _ HC) in Hrf1.
  unfold hull_apart. pose proof (u64_range a) as Ra. pose proof (proj1 HULL_cov) as Hne.
  destruct (Z_le_gt_dec (bv_unsigned a + bv_unsigned n) (img_lo A)) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec (img_hi A) (bv_unsigned a)) as [L2|L2]; [right; exact L2|]. exfalso.
  set (z := Z.max (bv_unsigned a) (img_lo A)).
  assert (Hz1 : bv_unsigned a <= z < bv_unsigned a + bv_unsigned n) by (unfold z; lia).
  assert (Hz2 : img_lo A <= z < img_hi A) by (unfold z; lia).
  pose proof (proj2 HULL_cov z Hz2) as Hin.
  pose proof (region_free_sem _ a n z Hrf1 ltac:(lia) ltac:(lia)) as Hout. congruence.
Qed.

(* [comment removed for export] *)
#[using="RES_len HULL_ok SP0_ok argH_high RES_len' HULL_ok' ATOP_facts'"] Lemma grant_new_facts : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pcs,$43.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.Pa,(2.&40.)Pn,(2.&40.)PnZ,$<.P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R8.R7.R6.R5.R4.)P,(>.$?.(1=.(1>.(1.(2.&40.)(2.&40.))(8;.(28.R5.))(2:.(28.R5.)))R4.R3.)$17.)P,(>.$<.(6.&40.R4.)R3.)P,(1:.=R4.)P,(9>.VA,(6.&40.R7.)R5.)P,(4.(8.(6.&40.R8.)R6.)(<6.VSP0,))Px,(2.&40.)P,(3.(4.(6.&40.R:.)(6.&40.R1.))(1:.(6.&40.R1.)(8.(6.&40.R:.)R8.)))(3.(>.$?.(10.(6.&40.R2.)(2:.(28.R<.)))$1;.)(3.(>.$?.(10.(6.&40.R2.)(27.(28.R<.)))$1;.)(3.(>.$?.A2.VargH,R10.R2.$1;.)(3.(>.$?.(<:.VA,(6.&40.R2.))$1;.)(3.(>.$?.(14.(<6.VSP0,)(6.&40.R2.))$1;.)(>.$?.(;7.VA,VSP0,R10.R?.R<.R2.)$1;.))))))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model a n nZ HC Hrf Un HnZ Himg HaC x Hx. atopb.
  rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf2].
  pose proof (region_free_sem _ a n (bv_unsigned x) Hrf2 ltac:(rewrite Un; lia) ltac:(rewrite Un; lia)) as M0.
  assert (N0 : in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false).
  { destruct (in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model))) eqn:En; [|reflexivity]. exfalso.
    apply (co_nasub _ _ _ _ _ _ _ _ _ _ _ _ HC) in En. congruence. }
  assert (Hh : in_hull A (bv_unsigned x) = false).
  { unfold in_hull. unfold hull_apart in Himg. apply andb_false_iff. destruct Himg as [Himg|Himg]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
  assert (Hc : (ATOP <=? bv_unsigned x) = false) by (apply Z.leb_gt; lia).
  repeat split; try assumption.
  - destruct (argH E x) eqn:Ea; [|reflexivity]. pose proof (argH_high _ _ Ea). lia.
  - unfold vis. rewrite Hh, Hc, M0. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="SEGS A RES_len HULL_ok RES_len' HULL_ok'"] Lemma bump_sound : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pnlo,$<.Pn,$<.Pa,$<.Pp,$<.Piv,(1.$<.$<.)P,(>.$<.(3;.R3.+1000.)=)P,(4.(2=.+1000.R3.)R4.)P,(4.R7.R6.)P,(35.(4.(8.R6.R7.)(7.$<.$<.R4.))(4.(8.(7.$<.$<.R4.)(9.$<.$<.R4.))R6.))(4.(2=.+1000.(<;.R9.R6.R5.))R7.)")
(* [comment removed for export] *).
Proof.
  intros nlo n a p iv Hal Hp Hn D. unfold gbump.
  destruct (Z.ltb (fst iv) (4096 * p + nlo) && Z.ltb (4096 * p) (fst iv + snd iv))%bool eqn:Hb; [|exact Hp].
  apply andb_prop in Hb as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (fst iv + snd iv <= a) by lia. nia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
#[using="SEGS A RES_len HULL_ok RES_len' HULL_ok'"] Lemma bump_fold_sound : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pnlo,$<.Pn,$<.Pa,$<.Pivs,(=.(1.$<.$<.))Pp,$<.P,(>.$<.(3;.R3.+1000.)=)P,(4.R6.R5.)P,Piv,(1.$<.$<.)P,(19.(1.$<.$<.)R1.R5.)(35.(4.(8.R7.R8.)(7.$<.$<.R2.))(4.(8.(7.$<.$<.R2.)(9.$<.$<.R2.))R7.))P,(4.(2=.+1000.R4.)R6.)(4.(2=.+1000.(<<.$<.(1.$<.$<.)(<;.R9.)R6.R5.))R7.)")
(* [comment removed for export] *).
Proof.
  intros nlo n a ivs. induction ivs as [|iv ivs IH]; intros p Hal Hn D Hp; cbn [fold_left]; [exact Hp|].
  apply IH; [exact Hal | exact Hn | intros; apply D; right; assumption |].
  apply (bump_sound nlo n); [exact Hal | exact Hp | exact Hn | apply D; left; reflexivity].
Qed.
#[using="SEGS RES_len HULL_ok RES_len' HULL_ok'"] Lemma lo_fit_sound : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pms,(=.$8>.)Pnlo,$<.PE,$94.Pa,(2.&40.)Pn,(2.&40.)P,(>.$<.(3;.(6.&40.R2.)+1000.)=)P,(1:.=(6.&40.R3.))P,(4.R6.(6.&40.R3.))P,(9>.VA,(6.&40.R5.)(6.&40.R4.))P,(;8.R7.R9.(6.&40.R6.)(6.&40.R5.))(4.(2=.+1000.(<=.VA,R:.R9.))(6.&40.R7.))")
(* [comment removed for export] *).
Proof.
  intros ms nlo E a n Hal Hpos Hn Hha Hap. unfold lo_fit.
  set (ivs := (img_lo A, img_hi A - img_lo A) :: lit_ivs ms).
  assert (D : forall iv, In iv ivs -> bv_unsigned a + bv_unsigned n <= fst iv \/ fst iv + snd iv <= bv_unsigned a).
  { intros iv [<-|Hin]; [cbn [fst snd]; unfold hull_apart in Hha; lia|].
    destruct iv as [z l]. destruct (lit_ivs_In E ms z l Hin) as (m & Hm & Hfm & Uz & Ul & _ & _).
    cbn [fst snd]. pose proof (Hap m Hm Hfm) as X. unfold uE in Uz, Ul. rewrite Uz, Ul in X. lia. }
  assert (GEN : forall k p, 4096 * p <= bv_unsigned a -> 4096 * bump_iter k nlo ivs p <= bv_unsigned a).
  { induction k as [|k IH]; intros p Hp; cbn [bump_iter]; [exact Hp|].
    apply IH. apply (bump_fold_sound nlo (bv_unsigned n)); assumption. }
  apply GEN. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
#[using="SEGS A RES_len RES_len'"] Lemma mod4096_mod8 : forall z, z mod 4096 = 0 -> z mod 8 = 0.
Proof.
  intros z H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|]. destruct H as [q ->]. exists (q * 512). lia.
Qed.

(* [comment removed for export] *)
#[using="RES_len HULL_ok SHADOW_ok RES_len' HULL_ok' SHADOW_ok'"] Lemma shadow_disj_ok : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.PM,P,(2.&40.)(3<.(2.&8.))PM0,P,(2.&40.)(3<.(2.&8.))Pk0,(=.$9?.)Ppb,$4:.Ppn,$4:.Pnb,$4:.Pne,$4:.P,(;?.VSEGS,R8.R6.R5.)P,(35.(4.(8.(;<.R9.R5.)(;<.R9.R4.))(;<.R9.R3.))(4.(8.(;<.R9.R3.)(;<.R9.R2.))(;<.R9.R5.)))(;?.VSEGS,R:.R9.(<>.VA,R7.R6.R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros E M M0 k0 pb pn nb ne HK0 Hap. pose proof SHADOW_ok' as SO.
  pose proof (u64_range (edenot E pb)) as R1. pose proof (u64_range (edenot E pn)) as R2.
  pose proof (u64_range (edenot E nb)) as R3. pose proof (u64_range (edenot E ne)) as R4. unfold uE in Hap.
  unfold shadow_disj.
  destruct (shadow_of A k0 pb pn) as [[ssb ssk] ssn] eqn:Hs1.
  destruct (shadow_of A k0 nb ne) as [[gsb gsk] gsn] eqn:Hs2.
  destruct (flat_x k0 ssb ssk ssn && flat_x k0 gsb gsk gsn)%bool eqn:Hf; [|apply Forall_nil].
  apply andb_prop in Hf as [F1 F2].
  destruct (APS.shadow_of_val SEGS A SHADOW_ok E M0 k0 _ _ ssb ssk ssn HK0 Hs1 F1) as [V1 L1].
  destruct (APS.shadow_of_val SEGS A SHADOW_ok E M0 k0 _ _ gsb gsk gsn HK0 Hs2 F2) as [V2 L2].
  apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok]. rewrite V1, L1, V2, L2.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  rewrite (Z.mod_small (bv_unsigned (edenot E pb) / 8 + shadow_off A)) by lia.
  rewrite (Z.mod_small (bv_unsigned (edenot E nb) / 8 + shadow_off A)) by lia.
  lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

#[using="RES_len HULL_ok SHADOW_ok HULL_cov SP0_ok RES_len' HULL_ok' SHADOW_ok' ATOP_facts'"] Lemma kdisj_all_ok : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.PM,P,(2.&40.)(3<.(2.&8.))PM0,P,(2.&40.)(3<.(2.&8.))Pk0,(=.$9?.)Pms,(=.$8>.)Pnb,$4:.Pne,$4:.Pa,(2.&40.)Pn,(2.&40.)P,(;?.VSEGS,R9.R7.R6.)P,(;8.R:.R6.(6.&40.R3.)(6.&40.R2.))P,(1:.=(6.&40.R3.))P,(>.$<.(3;.(6.&40.R5.)+1000.)=)P,(>.$<.(3;.(6.&40.R5.)+1000.)=)P,(9>.VA,(6.&40.R7.)(6.&40.R6.))P,(>.$<.(<5.R?.)VSP0,)P,(4.(8.(6.&40.R9.)(6.&40.R8.))(<6.VSP0,))P,(>.(2.&40.)(98.R11.R<.)R:.)P,(>.(2.&40.)(98.R12.R<.)R:.)(;?.VSEGS,R13.R12.(<?.VA,R10.R?.R>.R=.))")
(* [comment removed for export] *).
Proof.
  intros E M M0 k0 ms nb ne a n HK0 Hapart Hn Hal Hnal Hha Hsp HaC Hb Hne. atopb.
  pose proof (end_le_STKB _ _ Hal Hnal HaC) as HaS.
  pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3). pose proof (proj1 HULL_cov) as HUlt.
  pose proof (u64_range a) as Ra. pose proof (u64_range n) as Rn.
  unfold kdisj_all.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split]]]].
  - (* [comment removed for export] *) cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite Hb, Hne.
    rewrite !edenot_lit, !u64_lit by (unfold KHI in *; lia). unfold hull_apart in Hha. lia.
  - (* [comment removed for export] *) cbn [kentry_ok]. rewrite (estart_stkpg E Hsp).
    unfold estart, elenZ. cbn [a_base a_off]. rewrite Hb, Hne, edenot_lit, u64_lit by lia. right. lia.
  - (* [comment removed for export] *) unfold stack_shadow_disj. apply (shadow_disj_ok E M M0); [exact HK0|]. right.
    unfold uE. rewrite Hb, Hne, (u_e_stkbase E Hsp). exact HaS.
  - (* [comment removed for export] *) unfold hull_shadow_disj. apply (shadow_disj_ok E M M0); [exact HK0|].
    unfold uE. rewrite Hb, Hne, !edenot_lit, !u64_lit by (unfold KHI in *; lia). unfold hull_apart in Hha. lia.
  - (* [comment removed for export] *) apply Forall_map. apply Forall_forall. intros r Hr.
    unfold lit_runs in Hr. apply filter_In in Hr as [Hr Hck].
    apply andb_prop in Hck as [Hck _]. apply andb_prop in Hck as [Hck R3]. apply andb_prop in Hck as [R1 R2].
    apply Z.leb_le in R1. apply Z.ltb_lt in R2. apply Z.ltb_lt in R3. unfold two64 in R3.
    cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite Hb, Hne. rewrite !edenot_lit, !u64_lit by lia. rewrite Z.add_0_l.
    assert (RUN : forall x, fst r <= x < fst r + snd r -> bv_unsigned a + bv_unsigned n <= x \/ x < bv_unsigned a).
    { intros x Hx. destruct (coalesce_cov _ r x Hr Hx) as [[z l] [Hin Hzl]]. cbn [fst snd] in Hzl.
      destruct (lit_ivs_In E ms z l Hin) as (m & Hm & Hfm & Uz & Ul & Rz & Rl).
      pose proof (Hapart m Hm Hfm) as D. unfold uE in Uz, Ul. rewrite Uz, Ul in D. lia. }
    destruct (Z_le_gt_dec (fst r + snd r) (bv_unsigned a)) as [L1|L1]; [left; lia|].
    destruct (Z_le_gt_dec (bv_unsigned a + bv_unsigned n) (fst r)) as [L2|L2]; [right; lia|]. exfalso.
    pose proof (RUN (Z.max (bv_unsigned a) (fst r)) ltac:(lia)). lia.
  - (* [comment removed for export] *) apply Forall_flat_map. apply Forall_forall. intros m Hm.
    destruct (is_fog m) eqn:Hfm; [apply Forall_nil|].
    pose proof (Hapart m Hm Hfm) as D.
    apply Forall_cons; [|apply Forall_nil].
    cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite Hb, Hne. lia.
Qed.


(* [comment removed for export] *)
#[using="RES_len HULL_ok SP0_ok argH_high SINV_frame SINV_sp RES_len' HULL_ok' kentry_keep_sem' kimg_clip_in_hull' ATOP_facts'"] Lemma grant_cs1_ok : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pcs,$43.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.Pkd,$;5.Pa,(2.&40.)Pn,(2.&40.)PnZ,$<.Pmodel',$21.PFULL',P,(2.&40.)(3<.(2.&8.))Psr',(=.$4:.)PR',(5;.&5.(2.&40.))Pknew,(=.$9?.)Pbe,$4:.Pne,$4:.Pnhi,$<.Peager,$?.Pylo',$<.Pnx',$49.P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R14.R13.R12.R11.R10.)P,(>.$<.(6.&40.R>.)R=.)P,(1:.=R>.)P,(>.$<.(3;.R?.+1000.)=)P,(>.$<.(3;.(6.&40.R12.)+1000.)=)P,(9>.VA,(6.&40.R13.)R11.)P,(4.(8.(6.&40.R14.)R12.)(<6.VSP0,))P,(1:.=(6.&40.R15.))P,(>.$?.(1=.(1>.(1.(2.&40.)(2.&40.))(8;.(28.R18.))(2:.(28.R18.)))R16.R15.)$17.)P,(;6.R18.R17.R16.R19.R14.)P,(=0.R19.R18.R17.R1;.R14.)P,(<9.R1?.R14.R13.)P,(>.(2.&40.)(98.R20.R12.)R1:.)P,(>.(2.&40.)(98.R21.R12.)R1:.)P,(;?.VSEGS,R22.(=1.VA,VSP0,VargH,R22.R21.R19.R18.)R15.)P,(>.$?.(12.(=2.R1>.)(=3.R1>.))(25.R12.))P,(>.$?.(=4.R1?.)$1;.)P,(4.R1=.R15.)P,P,(>.$?.R15.$17.)(4.(8.(8.(:<.R26.)(:?.R26.))R17.)VLIMIT,)P,(4.R15.(:;.R26.))P,Pm,$8>.P,(19.$8>.R1.(:8.R28.))P,(>.$?.(=5.R2.)$17.)(35.(4.(8.(6.&40.R25.)R23.)(;<.R2;.(99.R3.)))(4.(8.(;<.R2;.(99.R3.))(;<.R2;.(9:.R3.)))(6.&40.R25.)))P,(>.$?.(=6.R24.$=7.)$1;.)Zcs1,$43.(=8.R29.R1?.(1>.$9?.R1=.(<8.VA,(:2.R29.)(:8.R29.)))R17.(=9.R1<.R1;.R25.)R1:.R19.R18.)(3.(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R2;.R1.R1?.R21.R22.)(3.Px,(2.&40.)P,(35.(1:.(6.&40.R1.)(6.&40.R26.))(4.(8.(6.&40.R26.)R24.)(6.&40.R1.)))(>.(3<.(2.&8.))(=1.VA,VSP0,VargH,R2=.R3.R24.R23.R2.)(=1.VA,VSP0,VargH,R2=.R2<.R29.R2:.R2.))(>.P,(2.&40.)(3<.(2.&8.))(=1.VA,VSP0,VargH,R2;.R1.R22.R21.)(=1.VA,VSP0,VargH,R2;.R2:.R22.R21.))))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model kd a n nZ model' FULL' sr' R' knew be ne nhi eager ylo' nx'
         HC Un HnZpos HnZal Hal Himg_a HaC Hapos Hrf GPo [GM1 GM2] Hregs Hbase HneE Hknew Hkind Hkfog Hnhi Hbudget Hylo Hholes HkdB cs1.
  pose proof (u64_range a) as Ra. atopb. pose proof HaC as HaC'. unfold APS.ATOP in HaC'.
  pose proof (cs_sp0 _ _ _ _ _ HC) as Hsp.
  pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3).
  pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hmaps.
  pose proof (maps_apart_of_region_free E (a_maps cs) model a n Hmaps Hrf) as Hapart. rewrite Un in Hapart.
  pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf.
  pose proof (grant_new_facts E cs R FULL model a n nZ HC Hrf Un HnZpos Himg_a HaC) as NEW.
  (* [comment removed for export] *)
  assert (VISOUT : forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
                    VIS E cs1 model' x = VIS E cs model x).
  { intros x Hx. eapply vis_grant_out; [exact GPo | reflexivity | rewrite Un; lia | exact Hal | rewrite Un; exact HnZal | rewrite Un; exact Hx]. }
  assert (HIDOUT : forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
                    HID E cs1 model' x = HID E cs model x).
  { intros x Hx. unfold hid. rewrite (VISOUT x Hx). reflexivity. }
  assert (MROUT : forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
                   MR E cs1 model' FULL' x = MR E cs model FULL x).
  { intros x Hx. unfold Mr, mrestrict. rewrite (HIDOUT x Hx). rewrite (GM1 x) by (rewrite Un; exact Hx). reflexivity. }
  assert (MRSAME : MR E cs1 model' FULL' = MR E cs model' FULL').
  { unfold Mr. rewrite (hid_ext A SP0 argH E cs cs1 model') by reflexivity. reflexivity. }
  split; [| split; [exact MROUT | exact MRSAME]].
  (* [comment removed for export] *)
  pose proof (grant_wf kd a n model model' GPo Hwf ltac:(rewrite Un; lia)) as Hwf'.
  (* [comment removed for export] *)
  assert (FRESH : forall iv, In iv (vm_maps (m_vmmaps model)) ->
            bv_unsigned a + nZ <= bv_unsigned (fst iv) \/ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned a).
  { intros [b0 s0] Hiv. rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf2].
    pose proof (RefNodes.region_free_In _ a n b0 s0 Hrf2 Hiv). cbn [fst snd]. rewrite Un in *. lia. }
  assert (NEWDEN : amap_den E (AM be ne kd) = (a, n)) by (unfold amap_den; cbn [am_base am_len]; rewrite Hbase, HneE; reflexivity).
  assert (NOTOLD : forall iv, In iv (vm_maps (m_vmmaps model)) -> iv <> (a, n)).
  { intros iv Hiv ->. pose proof (FRESH _ Hiv) as F. cbn [fst snd] in F.
    pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HC) _ Hiv) as (P0 & _). cbn [snd] in P0. rewrite Un in *. lia. }
  assert (BORN : forall ks iv, In iv (vm_maps (m_vmmaps model)) ->
            born E (AM be ne kd :: a_maps cs) ks iv -> born E (a_maps cs) ks iv).
  { intros ks iv Hiv (m1 & [<-|Hin1] & Hf1 & Hk1 & Hd1).
    - exfalso. rewrite NEWDEN in Hd1. exact (NOTOLD iv Hiv (eq_sym Hd1)).
    - exists m1. auto. }
  assert (BORNNEW : forall ks, ~ In kd ks -> ~ born E (AM be ne kd :: a_maps cs) ks (a, n)).
  { intros ks Hks (m1 & [<-|Hin1] & Hf1 & Hk1 & Hd1).
    - cbn [am_kind] in Hk1. exact (Hks Hk1).
    - pose proof (maps_match_In E _ _ m1 (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) Hin1 Hf1) as Hiv. rewrite Hd1 in Hiv. exact (NOTOLD _ Hiv eq_refl). }
  destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xisp Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xnk Xlzk Xsub Xdef Xnn Xcov].
  constructor.
  all: unfold cs1, add_entry; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_sub kn s_regs s_log s_know s_next mk_ss].
  all: try change (ALLOW E (ACS ?s ?m ?t ?y ?e (a_vis cs) (a_ghost cs) ?ab ?br ?fd ?ti ?sb)) with (ALLOW E cs).
  - (* [comment removed for export] *) exact Hregs.
  - (* [comment removed for export] *) reflexivity.
  - (* [comment removed for export] *) apply Forall_app. split.
    + unfold cs1, add_entry in MRSAME. cbn [kn a_ss s_know mk_ss] in MRSAME. rewrite MRSAME. exact Hknew.
    + eapply kn_grant_filter_ok; [exact Xknow | exact Hapart | exact HnZpos | exact Himg_a | exact Hsp | exact HaC | exact MROUT].
  - (* [comment removed for export] *) rewrite (gp_halted _ _ _ _ _ GPo). exact Xhalt.
  - (* [comment removed for export] *) unfold fds_ok in *. rewrite (gp_fds _ _ _ _ _ GPo), (gp_fs _ _ _ _ _ GPo). exact Xfds.
  - (* [comment removed for export] *) rewrite (gp_fs _ _ _ _ _ GPo). exact Xfs.
  - (* [comment removed for export] *) rewrite (gp_tid _ _ _ _ _ GPo). exact Xtid.
  - (* [comment removed for export] *) rewrite (gp_res _ _ _ _ _ GPo). exact Xres.
  - (* [comment removed for export] *) rewrite (gp_limit _ _ _ _ _ GPo). exact Xlimit.
  - (* [comment removed for export] *) rewrite (gp_maps _ _ _ _ _ GPo). rewrite <- Hbase, <- HneE. apply maps_match_cons; [exact Hkfog | exact Xmaps].
  - (* [comment removed for export] *)
    rewrite (gp_res _ _ _ _ _ GPo), (gp_maps _ _ _ _ _ GPo). apply Forall_cons.
    + intros Hh. exfalso. unfold is_hole in Hh. cbn [am_kind] in Hh. destruct kd; cbn in Hkfog, Hh; discriminate.
    + apply Forall_forall. intros m Hm Hk. destruct (proj1 (Forall_forall _ _) Xholes m Hm Hk) as [F1 F2]. split; [|lia].
      intros iv Hiv. apply in_app_iff in Hiv as [Hiv|[<-|Hiv]].
      * apply F1. apply in_app_iff. left. exact Hiv.
      * cbn [fst snd]. rewrite Un. pose proof (Hholes m Hm Hk). lia.
      * apply F1. apply in_app_iff. right. exact Hiv.
  - (* [comment removed for export] *) rewrite (gp_maps _ _ _ _ _ GPo). constructor; [|exact Xseps].
    apply Forall_forall. intros [b s] Hin. unfold iv_disjoint. cbn [fst snd]. rewrite Un.
    rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf2].
    pose proof (RefNodes.region_free_In _ a n b s Hrf2 Hin). rewrite Un in *. lia.
  - (* [comment removed for export] *) exact Hwf'.
  - (* [comment removed for export] *) rewrite (gp_maps _ _ _ _ _ GPo). apply Forall_cons; [|exact Xbounds]. cbn [fst snd]. rewrite Un. repeat split; first [exact Himg_a | exact Hapos | lia].   (* [comment removed for export] *)
  - (* [comment removed for export] *) rewrite (gp_lazy _ _ _ _ _ GPo). destruct (kind_lazy kd); [apply Forall_cons; [cbn [fst snd]; rewrite Un; split; [exact Himg_a | lia]|]|]; exact Xlazyb.
  - (* [comment removed for export] *) intros z Hz. rewrite (gp_maps _ _ _ _ _ GPo). rewrite in_ivs_cons. rewrite (gp_noacc _ _ _ _ _ GPo) in Hz.
    destruct (kind_none kd); [rewrite in_ivs_cons in Hz; apply orb_prop in Hz as [Hz|Hz]; [rewrite Hz; reflexivity|]|];
      rewrite (Xnasub z Hz); apply orb_true_r.
  - (* [comment removed for export] *) apply Forall_cons.
    + cbn [am_kind amap_den am_base am_len]. intros Hk. rewrite (gp_noacc _ _ _ _ _ GPo).
      replace (kind_none kd) with true by (destruct Hk as [-> | ->]; reflexivity). left. unfold amap_den. cbn [am_base am_len]. rewrite Hbase, HneE. reflexivity.
    + apply Forall_forall. intros m Hm Hk. rewrite (gp_noacc _ _ _ _ _ GPo).
      pose proof (proj1 (Forall_forall _ _) Xnone m Hm Hk) as X. destruct (kind_none kd); [right|]; exact X.
  - (* [comment removed for export] *) apply Forall_cons.
    + cbn [am_kind am_base am_len]. intros Hk x Hx. subst kd. rewrite Hbase, HneE, Un in Hx. cbn in Hkind.
      rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). cbn [kind_none kind_lazy]. split.
      * exact (proj1 (proj2 (NEW x Hx))).
      * destruct (page_of_byte_in_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Hal ltac:(rewrite Z.add_mod, Hal, HnZal by lia; reflexivity) Hx) as [P1 P2].
        apply page_in_ranges_cons_in; unfold page_size; rewrite ?Un; lia.
    + apply Forall_forall. intros m Hm Hk x Hx.
      destruct (proj1 (Forall_forall _ _) Xkinds m Hm Hk x Hx) as [K1 K2].
      rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). split.
      * destruct (kind_none kd); [|exact K1]. rewrite in_ivs_cons. cbn [fst snd]. rewrite K1, Un.
        pose proof (Hapart m Hm ltac:(unfold is_fog; rewrite Hk; reflexivity)) as D.
        replace ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + nZ))%bool with false; [reflexivity|].
        symmetry. apply andb_false_iff. destruct D; [right; apply Z.ltb_ge | left; apply Z.leb_gt]; lia.
      * destruct (kind_lazy kd); [|exact K2]. rewrite page_in_ranges_cons, K2. apply orb_true_r.
  - (* [comment removed for export] *) rewrite (gp_res _ _ _ _ _ GPo), (gp_maps _ _ _ _ _ GPo).
    rewrite sum_sizes_app in *. cbn [sum_sizes snd]. rewrite Un. cbn [sum_sizes] in Xtotsz. lia.
  - (* [comment removed for export] *) rewrite (gp_isp _ _ _ _ _ GPo). exact Xisp.
  - (* [comment removed for export] *) rewrite (gp_brk _ _ _ _ _ GPo). exact Xbrk.
  - (* [comment removed for export] *) rewrite (gp_brk _ _ _ _ _ GPo), (gp_sbrk _ _ _ _ _ GPo). exact Xsbrk.
  - (* [comment removed for export] *) pose proof (grant_eager_le kd a n model model' GPo Xwf ltac:(rewrite Un; lia)) as EG. rewrite Hkind in EG.
    destruct eager; cbn [negb] in EG; [|lia]. rewrite Un in EG. lia.
  - (* [comment removed for export] *) exact Xabytes.
  - (* [comment removed for export] *) destruct Xminv as [N1 N2 N3 N4 N5]. constructor; rewrite ?(gp_mat _ _ _ _ _ GPo), ?(gp_limit _ _ _ _ _ GPo); try assumption.
    + intros p Hp. rewrite (gp_lazy _ _ _ _ _ GPo). destruct (kind_lazy kd); [rewrite page_in_ranges_cons, (N4 p Hp); apply orb_true_r | exact (N4 p Hp)].
    + pose proof (grant_eager_le kd a n model model' GPo Xwf ltac:(rewrite Un; lia)) as EG. rewrite Hkind in EG.
      destruct eager; cbn [negb] in EG; [|lia]. rewrite Un in EG. rewrite Xlimit. specialize (Hbudget eq_refl). lia.
  - (* [comment removed for export] *) intros x Hh Hm Hna Hlz Hgh.
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + nZ)) as [Hlt2|Hge2]].
    + rewrite (GM1 x) by lia. apply Xzero; [rewrite <- (HIDOUT x) by lia; exact Hh | | | | exact Hgh].
      * rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons in Hm. apply orb_prop in Hm as [Hm|Hm]; [|exact Hm].
        apply andb_prop in Hm as [Hm _]. apply Z.leb_le in Hm. cbn [fst] in Hm. lia.
      * rewrite (gp_noacc _ _ _ _ _ GPo) in Hna. destruct (kind_none kd); [rewrite in_ivs_cons in Hna; apply orb_false_iff in Hna as [_ Hna]|]; exact Hna.
      * rewrite (gp_lazy _ _ _ _ _ GPo) in Hlz. destruct (kind_lazy kd); [|exact Hlz].
        rewrite page_in_ranges_cons_out in Hlz; [exact Hlz | | rewrite Un; lia].
        pose proof (page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Hal ltac:(rewrite Z.add_mod, Hal, HnZal by lia; reflexivity) ltac:(lia)). unfold page_size. rewrite Un. lia.
    + (* [comment removed for export] *) rewrite (GM2 x) by (rewrite Un; lia).
      rewrite (gp_noacc _ _ _ _ _ GPo) in Hna. destruct (kind_none kd); [|reflexivity].
      rewrite in_ivs_cons in Hna. cbn [fst snd] in Hna. apply orb_false_iff in Hna as [Hna _].
      apply andb_false_iff in Hna as [Hna|Hna]; [apply Z.leb_gt in Hna | apply Z.ltb_ge in Hna; rewrite Un in Hna]; lia.
    + rewrite (GM1 x) by (rewrite Un; lia). apply Xzero; [rewrite <- (HIDOUT x) by lia; exact Hh | | | | exact Hgh].
      * rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons in Hm. apply orb_prop in Hm as [Hm|Hm]; [|exact Hm].
        apply andb_prop in Hm as [_ Hm]. apply Z.ltb_lt in Hm. cbn [fst snd] in Hm. rewrite Un in Hm. lia.
      * rewrite (gp_noacc _ _ _ _ _ GPo) in Hna. destruct (kind_none kd); [rewrite in_ivs_cons in Hna; apply orb_false_iff in Hna as [_ Hna]|]; exact Hna.
      * rewrite (gp_lazy _ _ _ _ _ GPo) in Hlz. destruct (kind_lazy kd); [|exact Hlz].
        rewrite page_in_ranges_cons_out in Hlz; [exact Hlz | | rewrite Un; lia].
        pose proof (page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Hal ltac:(rewrite Z.add_mod, Hal, HnZal by lia; reflexivity) ltac:(lia)). unfold page_size. rewrite Un. lia.
  - (* [comment removed for export] *) eapply SINV_frame; [| |exact Xsinv].
    + intros x Hx. apply GM1. pose proof (argH_high _ _ Hx). rewrite Un. lia.
    + (* [comment removed for export] *) intros x Hx Hd. rewrite GM1; [exact Hd|]. rewrite Un. lia.
  - (* [comment removed for export] *) rewrite (gp_maps _ _ _ _ _ GPo). intros e He. rewrite (gp_noacc _ _ _ _ _ GPo) in He.
    assert (OLD : In e (vm_noaccess (m_vmmaps model)) ->
              0 < bv_unsigned (snd e) /\ exists iv, In iv ((a, n) :: vm_maps (m_vmmaps model)) /\ zB iv <= zB e /\ zE e <= zE iv /\ ~ born E (AM be ne kd :: a_maps cs) K_NOTNONE iv).
    { intros Ho. destruct (Xnk e Ho) as (P0 & iv & Hiv & B1 & B2 & NB). split; [exact P0|]. exists iv. split; [right; exact Hiv|].
      split; [exact B1|]. split; [exact B2|]. intros Hb. exact (NB (BORN _ iv Hiv Hb)). }
    destruct (kind_none kd) eqn:Hkn; [destruct He as [<-|He]; [|exact (OLD He)] | exact (OLD He)].
    split; [cbn [snd]; rewrite Un; exact HnZpos|]. exists (a, n). split; [left; reflexivity|]. unfold zB, zE; cbn [fst snd]. split; [lia|]. split; [lia|].
    apply BORNNEW. destruct kd; cbn in Hkn |- *; try discriminate Hkn; intros [X|[X|[]]]; discriminate X.
  - (* [comment removed for export] *) rewrite (gp_maps _ _ _ _ _ GPo). intros e He. rewrite (gp_lazy _ _ _ _ _ GPo) in He.
    assert (OLD : In e (m_vm_lazy model) ->
              0 < bv_unsigned (snd e) /\ exists iv, In iv ((a, n) :: vm_maps (m_vmmaps model)) /\ zB iv <= zB e /\ zE e <= zE iv /\ ~ born E (AM be ne kd :: a_maps cs) K_EAGER iv).
    { intros Ho. destruct (Xlzk e Ho) as (P0 & iv & Hiv & B1 & B2 & NB). split; [exact P0|]. exists iv. split; [right; exact Hiv|].
      split; [exact B1|]. split; [exact B2|]. intros Hb. exact (NB (BORN _ iv Hiv Hb)). }
    destruct (kind_lazy kd) eqn:Hkl; [destruct He as [<-|He]; [|exact (OLD He)] | exact (OLD He)].
    split; [cbn [snd]; rewrite Un; exact HnZpos|]. exists (a, n). split; [left; reflexivity|]. unfold zB, zE; cbn [fst snd]. split; [lia|]. split; [lia|].
    apply BORNNEW. destruct kd; cbn in Hkl |- *; try discriminate Hkl; intros HX; repeat (destruct HX as [HX|HX]; [discriminate HX|]); destruct HX.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    rewrite (gp_maps _ _ _ _ _ GPo). apply Forall_forall. intros t Ht.
    pose proof (proj1 (Forall_forall _ _) Xsub t Ht) as (S1 & (iv & Hiv & C1 & C2) & S3 & S4).
    pose proof (FRESH iv Hiv) as Fiv. unfold zB, zE in C1, C2.
    split; [exact S1|]. split; [exists iv; split; [right; exact Hiv|]; unfold zB, zE; auto|]. split.
    + intros e He. rewrite (gp_noacc _ _ _ _ _ GPo) in He. destruct (kind_none kd); [destruct He as [<-|He]; [unfold zB, zE; cbn [fst snd]; rewrite Un; lia|]|]; exact (S3 e He).
    + intros e He. rewrite (gp_lazy _ _ _ _ _ GPo) in He. destruct (kind_lazy kd); [destruct He as [<-|He]; [unfold zB, zE; cbn [fst snd]; rewrite Un; lia|]|]; exact (S4 e He).
  - (* [comment removed for export] *)
    apply Forall_cons.
    + intros Hf Hk x Hx. cbn [am_base am_len am_kind] in Hk, Hx. rewrite Hbase, HneE, Un in Hx. rewrite (GM2 x) by (rewrite Un; lia).
      destruct kd; cbn in Hk; try (exfalso; destruct Hk as [Hk|[Hk|[]]]; discriminate Hk); cbn; discriminate.
    + apply Forall_forall. intros m Hm Hf Hk x Hx. rewrite (GM1 x); [exact (proj1 (Forall_forall _ _) Xdef m Hm Hf Hk x Hx)|].
      pose proof (Hapart m Hm Hf) as AP. rewrite Un. lia.
  - (* [comment removed for export] *)
    intros x Hx. rewrite (gp_noacc _ _ _ _ _ GPo) in Hx.
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [L1|L1]; [|destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + nZ)) as [L2|L2]].
    + rewrite (GM1 x) by (rewrite Un; lia). apply Xnn. destruct (kind_none kd); [|exact Hx].
      rewrite in_ivs_cons in Hx. cbn [fst snd] in Hx. apply orb_prop in Hx as [Hx|Hx]; [|exact Hx].
      apply andb_prop in Hx as [Z1 Z2]. apply Z.leb_le in Z1. lia.
    + rewrite (GM2 x) by (rewrite Un; lia). destruct (kind_none kd) eqn:Hkn; [reflexivity|]. exfalso.
      pose proof (Xnasub _ Hx) as Hm. apply (proj1 (APS.in_ivs_true _ _)) in Hm as (iv & Hiv & Hz). pose proof (FRESH iv Hiv). lia.
    + rewrite (GM1 x) by (rewrite Un; lia). apply Xnn. destruct (kind_none kd); [|exact Hx].
      rewrite in_ivs_cons in Hx. cbn [fst snd] in Hx. apply orb_prop in Hx as [Hx|Hx]; [|exact Hx].
      apply andb_prop in Hx as [Z1 Z2]. apply Z.ltb_lt in Z2. rewrite Un in Z2. lia.
  - (* [comment removed for export] *)
    rewrite (gp_noacc _ _ _ _ _ GPo). apply Forall_cons.
    + intros Hk z Hz. left. unfold APS.uE in Hz. cbn [am_base am_len am_kind] in Hk, Hz. rewrite Hbase, HneE, Un in Hz.
      assert (Hkn : kind_none kd = true) by (destruct Hk as [<-|[<-|[]]]; [reflexivity | discriminate HkdB]).
      rewrite Hkn, in_ivs_cons. cbn [fst snd]. rewrite Un.
      replace (bv_unsigned a <=? z) with true by (symmetry; apply Z.leb_le; lia).
      replace (z <? bv_unsigned a + nZ) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    + eapply APS.cov_Forall_mono; [| intros t Ht; exact Ht | exact Xcov].
      intros z Hz. destruct (kind_none kd); [rewrite in_ivs_cons, Hz; apply orb_true_r | exact Hz].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition null_cs1 (cs : acs) (kd : mkind) (eager : bool) (ne : expr) (nlo nhi : Z) : acs := ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Zv,$49.(:9.O6.)Zbase,$4:.(=:.+1000.(=;.R1.))Zkv,$9?.(=<.(=;.R2.)(<=.VA,(:8.O6.)O2.)(==.(=>.$=?.O2.)+1000.))(=8.O6.(>0.(:5.(:6.O6.))#:.R2.)(1>.$9?.(11.$9?.R1.(<?.VA,(11.$9?.R1.(:2.O6.))(:8.O6.)R2.O3.))(<8.VA,(:2.O6.)(:8.O6.)))(>1.R3.)(=9.R2.O3.O5.)O1.O4.(:;.O6.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="A RES_len HULL_ok RES_len' HULL_ok'"] Lemma null_kend_ok : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.PM,P,(2.&40.)(3<.(2.&8.))Pbase,$4:.Pne,$4:.Pnlo,$<.Pa,(2.&40.)Pn,(2.&40.)P,(>.(2.&40.)(98.R7.R5.)R2.)P,(>.(2.&40.)(98.R8.R5.)R2.)P,(4.(2=.+1000.(8.(==.$>2.+1000.)+1.))(6.&40.R4.))P,(4.R6.(6.&40.R4.))P,(4.(8.(6.&40.R6.)(6.&40.R5.))$>3.)(;?.VSEGS,R<.R;.(>4.R:.R9.R8.))")
(* [comment removed for export] *).
Proof.
  intros E M base ne nlo a n Hb Hn Hlo Hnlo HaC. unfold null_kend.
  pose proof (u64_range a) as Ra. pose proof (u64_range n) as Rn. unfold two64 in *.
  destruct ne; try (apply Forall_nil); apply Forall_cons; try apply Forall_nil;
    cbn [kentry_ok]; unfold eadd; rewrite AX2S.mkAlu_denot; cbn [alu64 alu]; rewrite bv_add_unsigned, Hb, Hn;
    unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64)%Z;
    unfold CEIL, KHI in *; rewrite Z.mod_small by lia; lia.
Qed.
#[using="Type"] Lemma null_kend_pure : forall base ne nlo,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (null_kend base ne nlo).
Proof. intros. unfold null_kend. destruct ne; repeat constructor. Qed.

#[using="SEGS A RES_len HULL_ok RES_len' HULL_ok'"] Lemma escale_4096_denot : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pv,$49.Pa,(2.&40.)P,(>.(2.&40.)(>5.R3.R2.)(3?.&40.(==.(6.&40.R1.)+1000.)))P,(>.$<.(3;.(6.&40.R2.)+1000.)=)(>.(2.&40.)(98.R5.(=:.+1000.(=;.R4.)))R3.)")
(* [comment removed for export] *).
Proof.
  intros E v a Hv Hal. unfold escale. rewrite mkMd_denot. cbn [edenot]. rewrite Hv.
  pose proof (u64_range a) as Ra. apply bv_eq. rewrite u_mul64.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  rewrite !u64_lit by lia. rewrite Z.mod_small; lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

#[using="RES_len HULL_ok SHADOW_ok HULL_cov SP0_ok argH_high argH_agree SINV_frame SINV_agree SINV_sp RES_len' HULL_ok' SHADOW_ok' reg_sound' reg_lit_sound' kentry_keep_sem' regs_ok_set_n' kimg_clip_in_hull' cs_ok_agree' ATOP_facts'"] Lemma mmap_null_cs1 : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pcs,$43.Pkd,$;5.Peager,$?.Pne,$4:.Pnlo,$<.Pnhi,$<.PE,$94.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.Pa,(2.&40.)Pmodel',$21.PFULL',P,(2.&40.)(3<.(2.&8.))P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R7.R=.R6.R5.R4.)P,(>.(3<.(1.(1.$4:.$<.)$<.))(9<.R>.)(3>.(1.(1.$4:.$<.)$<.)(1?.(1.$4:.$<.)$<.(1?.$4:.$<.R;.R:.)R9.)))P,(>.$?.(>6.Vnx0,R?.)$17.)P,(>.$?.(4=.(:9.R10.)R=.)$17.)P,P,(>.$?.R?.$17.)(4.(8.(8.(:<.R12.)(:?.R12.))R=.)VLIMIT,)P,(>.$?.(12.(=2.R11.)(=3.R11.))(25.R10.))P,(>.$?.(=4.R12.)$1;.)P,(>.$?.(>7.(:8.R14.))$17.)P,(>.$?.(=6.R14.$=7.)$1;.)Zlen,$<.(6.&40.(98.R10.(9=.R16.#;.)))ZnZ,$<.(7<.R1.)Zn,(2.&40.)(3?.&40.R1.)P,(>.$?.(7=.R10.R?.R2.)$17.)P,(;6.R19.R10.R2.R11.R?.)P,(=0.R1:.R11.R3.R13.R?.)Zv,$49.(:9.R1<.)ZE',$94.(>8.R17.R1.(3?.&40.(==.(6.&40.R13.)+1000.)))Zcs1,$43.(>9.R1>.R1=.R1<.R1;.R1:.R19.)(3.(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R2.R1.(7?.R18.(3?.&5.(2>.#:.))R15.)R13.R14.)(3.(>.(2.&40.)(98.R2.(=:.+1000.(=;.R3.)))R15.)(3.(>.(2.&40.)(98.R2.R1<.)R7.)(3.(>.$<.(6.&40.R7.)R8.)(3.(>:.Vnx0,R19.R2.)Px,(2.&40.)P,(3.(4.(6.&40.R16.)(6.&40.R1.))(1:.(6.&40.R1.)(8.(6.&40.R16.)R9.)))(3.(>.$?.(10.(6.&40.R2.)(2:.(28.R16.)))$17.)(3.(>.$?.(10.(6.&40.R2.)(27.(28.R18.)))$1;.)(3.(>.$?.A2.VargH,R4.R2.$1;.)(3.(>.$?.(<:.VA,(6.&40.R2.))$1;.)(>.$?.(14.(<6.VSP0,)(6.&40.R2.))$1;.))))))))))")
(* [comment removed for export] *).
Proof.
  intros cs kd eager ne nlo nhi E R FULL model a model' FULL' HC HML Hfresh Hnev Hbudget Hkind Hkfog Hnoh HkdB len nZ n Hg GPo GM v E' cs1.
  atopb.
  assert (Hnoholes : Forall (fun m => is_hole m = false) (a_maps cs)).
  { unfold no_holes in Hnoh. apply Forall_forall. intros m Hm. pose proof (proj1 (forallb_forall _ _) Hnoh m Hm) as X. apply negb_true_iff in X. exact X. }
  (* [comment removed for export] *)
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & HneE).
  fold len in R11, Hlen, Hne, HnZ, HnZal. fold nZ in Hne, HnZ, HnZal.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. fold nZ in PB. unfold page_size in PB.
  pose proof Hg as Hg0.
  unfold grant_ok_na_pin in Hg. apply andb_prop in Hg as [Hg Hrf].
  apply andb_prop in Hg as [Hg Hceil]. apply andb_prop in Hg as [Hal Hpos].
  apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Hceil. fold n in Hrf.
  unfold page_size in Hal. rewrite (cs_atop _ _ _ _ _ HC) in Hceil.
  assert (Un : bv_unsigned n = nZ) by (subst n; apply u64_lit; lia).
  pose proof (u64_range a) as Ra.
  pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3). pose proof (proj1 HULL_cov) as HUlt.
  assert (HnZpos : 0 < nZ) by lia.
  (* [comment removed for export] *)
  assert (Himg_a : hull_apart A (bv_unsigned a) nZ).
  { rewrite <- Un. eapply free_hull_apart; [exact HC | exact Hrf | rewrite Un; exact HnZpos]. }
  assert (HaC : bv_unsigned a + nZ <= ATOP) by exact Hceil.
  (* [comment removed for export] *)
  pose proof (ext1_agree'' E v (Z_to_bv 64 (bv_unsigned a / 4096))) as Hag. fold E' in Hag.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fvis & Fbrk & Ffd & Fle). fold v in Fsr, Fkn, Fmaps, Fvis, Fbrk, Ffd, Fle.
  assert (HC' : CSOK E' cs R FULL model) by (eapply cs_ok_agree'; [exact Hag | exact Hfresh | exact HC]).
  assert (Hag0 : env_agree nx0 E E') by (eapply env_agree_le'; [exact Hag | exact Fle]).
  assert (Hv : ev E' v = Z_to_bv 64 (bv_unsigned a / 4096)) by apply ext1_at.
  assert (Hbase : edenot E' (escale 4096 (EVar v)) = a) by (apply escale_4096_denot; assumption).
  assert (HneE' : edenot E' ne = n).
  { rewrite (HneE E'); [exact Hne|]. symmetry. eapply edenot_agree'; [exact Hag|]. unfold reg. apply nth_sr_vars_lt'; [exact Fsr | lia]. }
  pose proof (cs_sp0 _ _ _ _ _ HC') as Hsp'.
  pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC') as Hmaps.
  pose proof (maps_apart_of_region_free E' (a_maps cs) model a n Hmaps Hrf) as Hapart.
  pose proof Hapart as Hapart0. rewrite Un in Hapart.
  pose proof (grant_new_facts E' cs R FULL model a n nZ HC' Hrf Un HnZpos Himg_a HaC) as NEW.
  (* [comment removed for export] *)
  destruct (grant_cs1_ok E' cs R FULL model kd a n nZ model' FULL'
              (sr_upd (s_regs (a_ss cs)) 10 (escale 4096 (EVar v))) (regupd R (Z_to_bv 5 (Z.of_nat 10)) a)
              (KRange (EVar v) (lo_fit A (a_maps cs) nlo) ((ATOPMAX - nlo) / 4096)
                 :: kdisj_all A (KRange (EVar v) (lo_fit A (a_maps cs) nlo) ((ATOPMAX - nlo) / 4096) :: kn cs) (a_maps cs) (escale 4096 (EVar v)) ne)
              (escale 4096 (EVar v)) ne nhi eager (a_ylo cs) (Datatypes.S v)
              HC' Un HnZpos HnZal Hal Himg_a HaC Hpos Hrf GPo GM) as (HC1 & MROUT & MRSAME).   (* [comment removed for export] *)
  - apply regs_ok_set_n'; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC') | lia | exact Hbase].
  - exact Hbase.
  - exact HneE'.
  - assert (KV : kentry_ok SEGS E' (MR E' cs model FULL) (KRange (EVar v) (lo_fit A (a_maps cs) nlo) ((ATOPMAX - nlo) / 4096))).
    { (* [comment removed for export] *) cbn [kentry_ok edenot]. rewrite Hv.
      pose proof (lo_fit_sound (a_maps cs) nlo E' a n Hal Hpos ltac:(rewrite Un; lia) ltac:(rewrite Un; exact Himg_a) Hapart0) as LF.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      rewrite u64_lit by lia. unfold ATOPMAX, APS.ATOP in *. split; lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    apply Forall_cons.
    + exact KV.
    + (* [comment removed for export] *)
      eapply (kdisj_all_ok E' _ (MR E' cs model FULL));
        [apply Forall_cons; [exact KV | exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC')]
        | exact Hapart0 | rewrite Un; exact HnZpos | exact Hal | rewrite Un; exact HnZal | rewrite Un; exact Himg_a | exact Hsp' | rewrite Un; exact HaC | exact Hbase | exact HneE'].
  - exact Hkind.
  - exact Hkfog.
  - lia.
  - exact Hbudget.
  - cbn [a_ylo]. lia.
  - intros m Hm Hk. exfalso. pose proof (proj1 (Forall_forall _ _) Hnoholes m Hm) as X. congruence.
  - exact HkdB.
  - split; [exact HC1|]. split; [exact Hbase|]. split; [exact HneE'|]. split; [exact Un|]. split; [exact Hag0|].
    intros x Hx. destruct (NEW x Hx) as (N0 & N1 & N2 & N3 & N4 & _).
    split; [|auto]. rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons. cbn [fst snd]. rewrite Un.
    apply orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="A RES_len HULL_ok RES_len' HULL_ok'"] Lemma kmem_ok : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.PM,Px,(2.&40.)(3<.(2.&8.))Pb,$4:.Pne,$4:.Plo,$<.Pn,$<.P,(>.$<.(<1.R6.(<2.R4.=))R2.)P,(>.$<.(<3.R7.R4.)R2.)P,(3.(4.=R4.)(1:.R4.(48.+2.+40.)))P,(4.=R4.)P,(4.(8.R6.R5.)(48.+2.+40.))P,Px,(2.&40.)P,(3.(4.R8.(6.&40.R1.))(1:.(6.&40.R1.)(8.R8.R7.)))(>.(3<.(2.&8.))A1.R<.R2.(3>.(2.&8.)(3?.&8.=)))(;?.VSEGS,R<.R;.(11.$9?.(>;.(<2.R:.=)R9.)(11.$9?.(><.(<2.R:.=)R9.)(38.$9?.))))")
(* [comment removed for export] *).
Proof.
  intros E M b ne lo n Hs Hn Hlo Hn0 Hhi BYTE.
  assert (Hfl : flat E (SA b 0) (elenZ E ne)) by (unfold flat; rewrite Hs, Hn; lia).
  constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; split; try exact Hfl; rewrite ?Hs, ?Hn.
  - intros d w Hd Hdw. destruct w as [|w']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia. unfold wview. rewrite (BYTE x) by lia. discriminate.
  - intros i Hi. apply BYTE. rewrite u64_lit by lia. lia.
Qed.

#[using="Type"] Lemma kimg_in_hull_pure : forall k,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) k -> kimg_in_hull A k.
Proof.
  intros k H. unfold kimg_in_hull. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) H K Hin) as HK. destruct K; try exact I. destruct HK.
Qed.

#[using="Type"] Lemma kdisj_new_pure : forall ms nb ne,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (kdisj_new ms nb ne).
Proof.
  intros ms nb ne. unfold kdisj_new. apply Forall_flat_map. apply Forall_forall. intros m _.
  destruct (is_fog m); [apply Forall_nil|].
  destruct (am_base m); (apply Forall_cons; [exact I | apply Forall_nil]) || apply Forall_nil.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kdisj_all_pure : forall k0 ms nb ne,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (kdisj_all A k0 ms nb ne).
Proof.
  intros k0 ms nb ne. unfold kdisj_all. apply Forall_cons; [exact I|]. apply Forall_cons; [exact I|].
  assert (SD : forall pb pn, Forall (fun K => match K with KImg _ _ => False | _ => True end) (shadow_disj A k0 pb pn nb ne)).
  { intros pb pn. unfold shadow_disj. destruct (shadow_of A k0 pb pn) as [[? ?] ?]. destruct (shadow_of A k0 nb ne) as [[? ?] ?].
    destruct (_ && _)%bool; [apply Forall_cons; [exact I|]|]; apply Forall_nil. }
  apply Forall_app. split; [apply SD|]. apply Forall_app. split; [apply SD|]. apply Forall_app. split.
  - apply Forall_map. apply Forall_forall. intros r _. exact I.
  - apply Forall_flat_map. apply Forall_forall. intros m _. destruct (is_fog m); [apply Forall_nil|]. apply Forall_cons; [exact I | apply Forall_nil].
Qed.

(* [comment removed for export] *)
#[using="SEGS_in_hull RES_len HULL_ok SHADOW_ok SP0_ok argH_high HS XN XE XB RES_len' HULL_ok' vis_add_sound' know_ok_unhide' hid_hull' H_off_segments_cs'"] Lemma grant_vis_add : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pcs1,$43.Pcs2,$43.Pbase,$4:.Pne,$4:.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.Pa,(2.&40.)Pn,(2.&40.)PnZ,$<.P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R;.R:.R6.R5.R4.)P,(>.(3<.$43.)(:0.VA,VLIMIT,R;.R9.R8.(1>.$9?.(11.$9?.(>;.(<2.R9.=)R8.)(11.$9?.(><.(<2.R9.=)R8.)(38.$9?.)))(:2.R;.)))(3>.$43.R:.))P,(>=.VA,(:2.R<.))P,(>.(2.&40.)(98.R>.R;.)R6.)P,(>.(2.&40.)(98.R?.R;.)R6.)P,(>.$<.(6.&40.R7.)R6.)P,(4.=R7.)P,(4.(8.(6.&40.R:.)R8.)(48.+2.+40.))P,Px,(2.&40.)P,(3.(4.(6.&40.R<.)(6.&40.R1.))(1:.(6.&40.R1.)(8.(6.&40.R<.)R:.)))(3.(>.$?.(10.(6.&40.R2.)(2:.(28.R>.)))$17.)(3.(>.$?.(10.(6.&40.R2.)(27.(28.R>.)))$1;.)(>.$?.A2.VargH,R15.R2.$1;.)))P,Px,(2.&40.)P,(3.(4.(6.&40.R=.)(6.&40.R1.))(1:.(6.&40.R1.)(8.(6.&40.R=.)R;.)))(>.(3<.(2.&8.))A1.R10.R2.(3>.(2.&8.)(3?.&8.=)))(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R15.R13.R10.R?.R>.)")
(* [comment removed for export] *).
Proof.
  intros E cs1 cs2 base ne R FULL model a n nZ HC1 Hva Hkh Hbase Hne Un HnZ Hhi NEW ZERO.
  pose proof (u64_range a) as Ra.
  eapply vis_add_sound'; [exact Hva | exact HC1 |].
  destruct (vis_add_inv cs1 base ne _ cs2 Hva) as (nhi & Hnhi & Ecs2).
  apply Forall_app. split.
  - (* [comment removed for export] *)
    eapply (kmem_ok E _ base ne (bv_unsigned a) nZ); [unfold estart; cbn [a_base a_off]; rewrite Hbase; lia | unfold elenZ; rewrite Hne; exact Un | lia | lia | lia |].
    intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3).
    unfold Mr, mrestrict, hid. rewrite N3. cbn [orb].
    unfold vis. rewrite N1, N2. cbn [negb andb].
    assert (Hal : in_allow A E cs2 (bv_unsigned x) = true).
    { unfold in_allow, in_vis. rewrite Ecs2. cbn [a_vis existsb fst snd]. unfold uE. rewrite Hbase, Hne, Un.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    rewrite Hal. rewrite !orb_true_r. cbn [negb]. apply ZERO. exact Hx.
  - (* [comment removed for export] *)
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
    eapply know_ok_unhide'; [apply H_off_segments_cs' | exact Hkh | | | exact HK1].
    + intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
    + intros y Hy. apply hid_hull'. exact Hy.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="SEGS A RES_len RES_len'"] Lemma gap_weight_eq : forall nZ l, gap_weight nZ l = sum_sizes l + Z.of_nat (length l) * (nZ + 4095).
Proof. induction l as [|[b sz] l IH]; cbn -[Z.of_nat Z.add Z.mul]; [lia|]. rewrite IH. rewrite Nat2Z.inj_succ. cbn [snd]. lia. Qed.

(* [comment removed for export] *)
#[using="RES_len HULL_ok SHADOW_ok SP0_ok RES_len' HULL_ok' SHADOW_ok' ATOP_facts'"] Lemma gap_ok_sound : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pcs,$43.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.Pnhi,$<.PnZ,$<.P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R7.R6.R5.R4.R3.)P,(>.$?.(>>.VA,R7.R3.)$17.)P,(3.(4.=R3.)(4.R3.R4.))(18.(2.&40.)La,(2.&40.)(>.$?.(7=.R7.R1.R5.)$17.))")
(* [comment removed for export] *).      (* [comment removed for export] *)
Proof.
  intros E cs R FULL model nhi nZ HC Hg HnZ. unfold gap_ok in Hg. apply Z.leb_le in Hg.
  pose proof (co_totsz _ _ _ _ _ _ _ _ _ _ _ _ HC) as T.
  assert (L : (length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= n_res A + length (a_maps cs))%nat).
  { rewrite length_app, (co_res _ _ _ _ _ _ _ _ _ _ _ _ HC), RES_len'. pose proof (maps_match_length E _ _ (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC)). lia. }
  assert (GW : gw_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= a_totsz cs).
  { pose proof (gap_weight_sizes nZ (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) as G1.
    rewrite gap_weight_eq in G1. lia. }
  destruct (free_gap_of_totals (m_vmmaps model) nZ (a_totsz cs) ltac:(lia) GW) as (g & Hal & Hfl & Hc & Hfree & Hpl).
  { rewrite FLOOR_eq, CEIL_eq.
    assert (0 <= a_totsz cs).
    { assert (0 <= sum_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))); [|lia].
      clear. induction (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) as [|[b sz] l IH]; cbn; [lia|]. pose proof (u64_range sz). lia. }
    set (len1 := length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) in *.
    set (len2 := (n_res A + length (a_maps cs))%nat) in *.
    assert (Z.of_nat len1 * (nZ + 4095) <= Z.of_nat len2 * (nhi + 4095)) by nia. nia. }
  pose proof bottomup_floor_val as Hfv. pose proof alloc_ceiling_val as Hcv. atopb.
  pose proof (cs_atop _ _ _ _ _ HC) as HT. pose proof (APS.CEIL_le_ATOP SP0 SP0_ok) as HCA. unfold CEIL in HCA.
  assert (Hg64 : 0 <= g < 2 ^ 64) by lia.
  exists (Z_to_bv 64 g). unfold grant_ok_na_pin. rewrite u64_lit by lia.
  rewrite Hfree, HT. unfold page_size in Hal |- *.
  rewrite (proj2 (Z.eqb_eq _ _) Hal). rewrite (proj2 (Z.ltb_lt 0 g)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

#[using="RES_len HULL_ok HS XN XE XB RES_len' HULL_ok' A_wf_allowA'"] Lemma budget_slack : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pcs,$43.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.Pextra,$<.P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R6.R5.R4.R3.R2.)P,(>.$?.(>?.VLIMIT,R6.R2.)$17.)(4.(8.(?0.R4.)R3.)(?1.(28.R4.)))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model extra HC Hb. unfold budget_ok in Hb. apply Z.leb_le in Hb.
  pose proof (vm_backing_used_le (ALLOW E cs) model (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) (A_wf_allowA' E cs)).
  pose proof (co_eager _ _ _ _ _ _ _ _ _ _ _ _ HC). pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ _ HC).
  rewrite (co_limit _ _ _ _ _ _ _ _ _ _ _ _ HC). lia.
Qed.

#[using="Type"] Lemma lazy_interior_fresh : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pa,(2.&40.)Pn,(2.&40.)P,(>.$<.(3;.(6.&40.R2.)+1000.)=)P,(>.$<.(3;.(6.&40.R2.)+1000.)=)P,(1:.=(6.&40.R3.))P,(4.(8.(6.&40.R5.)(6.&40.R4.))(48.+2.+40.))(>.(=.(1.(2.&40.)(2.&40.)))(?2.R6.R5.)(11.(1.(2.&40.)(2.&40.))(1?.(2.&40.)(2.&40.)R6.R5.)(38.(1.(2.&40.)(2.&40.)))))")
(* [comment removed for export] *).
Proof. intros. apply lazy_interior_aligned; unfold page_size; assumption. Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma refuse_eq : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pcs,$43.(>.$43.(?3.R1.)(?4.R1.(:4.(8.(46.R1.)+4.)(>0.(:5.(:6.R1.))#:.(4?.$?5.))(:2.R1.)(:9.R1.))))")
(* [comment removed for export] *).
Proof. reflexivity. Qed.

#[using="Type"] Lemma refuse_pc : forall cs, pc (refuse cs) = pc cs + 4.
Proof. reflexivity. Qed.

#[using="Type"] Lemma refuse_nxt : forall cs, nxt (refuse cs) = nxt cs.
Proof. reflexivity. Qed.

#[using="RES_len SINV_frame RES_len' regs_ok_set_n' cs_ok_frame'"] Lemma refuse_ok : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pcs,$43.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R5.R4.R3.R2.R1.)(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R6.(?3.R5.)(7?.R4.(3?.&5.(2>.#:.))(80.$81.))R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model HC. rewrite refuse_eq.
  eapply cs_ok_frame'; [exact HC | apply same_but_materialized_refl | exact (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) | | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) | intros; reflexivity | intros a' X'; exact X'].
  cbn [s_regs mk_ss]. apply regs_ok_set_n'; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) | lia |].
  cbn [edenot]. rewrite errno_ret_ENOMEM. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="RES_len SINV_frame RES_len' regs_ok_set_n' cs_ok_frame'"] Lemma refuse_cont : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pcs,$43.PE,$94.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.PTA,$6?.P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R5.R6.R4.R3.R2.)P,(4.=(46.R7.))P,(1:.(8.(46.R8.)+4.)(48.+2.+40.))P,PE',$94.PR',(5;.&5.(2.&40.))PFULL',P,(2.&40.)(3<.(2.&8.))Pmodel',$21.P,(3.(>:.Vnx0,R<.R4.)(>:.(:9.R=.)R<.R4.))P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R5.(?3.R>.)R4.R3.R2.)P,(>.$?6.(?7.R3.)(?7.R;.))(70.VSEGS,(?8.VSEGS,R6.(46.(?3.R10.))R5.R4.)R;.)(70.VSEGS,(6<.(60.$61.(7?.R8.(66.&5.+:.$67.)(80.$81.))(82.(3?.&40.(46.R:.))+4.)R7.(?9.VSEGS,))R6.)R5.)")
(* [comment removed for export] *).
Proof.
  intros cs E R FULL model TA HC Hp0 Hp4 HKA.
  specialize (HKA E (regupd R (Z_to_bv 5 (Z.of_nat 10)) (errno_ret ENOMEM)) FULL model
                  (conj (env_agree_refl' _ _) (env_agree_refl' _ _)) (refuse_ok E cs R FULL model HC) eq_refl).
  unfold cfg_of in HKA. rewrite refuse_pc, <- bv5_10 in HKA. rewrite (v_addi_pc (pc cs) Hp0 Hp4). exact HKA.
Qed.

(* [comment removed for export] *)
#[using="RES_len SINV_frame RES_len' regs_ok_set_n' cs_ok_frame'"] Lemma refuse_cont0 : forall cs E R FULL model TA,
  CSOK E cs R FULL model -> 0 <= pc cs -> pc cs + 4 < 2 ^ 64 ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' (refuse cs) R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes0 SEGS (cfg R' (pc (refuse cs)) FULL' model') TA) ->
  srealizes0 SEGS (mkCfg (mkst (regupd R 10 (errno_ret ENOMEM)) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL (seg_rom SEGS)) model) TA.
Proof.
  intros cs E R FULL model TA HC Hp0 Hp4 HKA.
  specialize (HKA E (regupd R (Z_to_bv 5 (Z.of_nat 10)) (errno_ret ENOMEM)) FULL model
                  (conj (env_agree_refl' _ _) (env_agree_refl' _ _)) (refuse_ok E cs R FULL model HC) eq_refl).
  unfold cfg_of in HKA. rewrite refuse_pc, <- bv5_10 in HKA. rewrite (v_addi_pc (pc cs) Hp0 Hp4). exact HKA.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="A RES_len RES_len'"] Lemma page_aligned_sound : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.PM,P,(2.&40.)(3<.(2.&8.))Pk,(=.$9?.)Pe,$4:.P,(;?.VSEGS,R4.R3.R2.)P,(>.$?.(?:.R3.R2.)$17.)(>.$<.(3;.(6.&40.(98.R6.R3.))+1000.)=)")
(* [comment removed for export] *).
Proof.
  intros E M k e HK H.
  assert (GEN : 12 <= ealign k e -> bv_unsigned (edenot E e) mod 4096 = 0).
  { intros Hle. destruct (ealign_sound SEGS E M k e HK) as [Hr [q Hq]]. rewrite Hq.
    replace (2 ^ ealign k e) with (2 ^ (ealign k e - 12) * 4096) by (rewrite <- (Z.pow_add_r 2 _ 12) by lia; f_equal; lia).
    rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
  unfold page_aligned in H. destruct e as [z| | | | | | |]; try (apply GEN; apply Z.leb_le; exact H).
  apply Z.eqb_eq in H. cbn [edenot]. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  rewrite Z.mod_mod_divide; [exact H | exists (2 ^ 52); reflexivity].
Qed.

#[using="RES_len HULL_ok RES_len' HULL_ok' reg_sound'"] Lemma fixed_args_sound : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pcs,$43.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.Ptop,$<.Pb,$4:.Poff,$<.Pne,$4:.Pnlo,$<.Pnhi,$<.P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R;.R:.R9.R8.R7.)P,(>.(3<.(1.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.))(?;.VA,R;.R7.)(3>.(1.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.)(1?.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.(1?.(1.(1.$4:.$<.)$4:.)$<.(1?.(1.$4:.$<.)$4:.(1?.$4:.$<.R6.R5.)R4.)R3.)R2.)))(3.(>.(1.$4:.$<.)(?<.(9=.R<.#:.))(1?.$4:.$<.R7.R6.))(3.(>.(3<.(1.(1.$4:.$<.)$<.))(9<.R<.)(3>.(1.(1.$4:.$<.)$<.)(1?.(1.$4:.$<.)$<.(1?.$4:.$<.R5.R4.)R3.)))(3.(>.$<.(3;.(6.&40.(98.R=.(9=.R<.#:.)))+1000.)=)(3.(1:.=(6.&40.(98.R=.(9=.R<.#:.))))(3.(4.(:.VA,)(6.&40.(98.R=.(9=.R<.#:.))))(3.(4.(8.(6.&40.(98.R=.(9=.R<.#:.)))R3.)R8.)(3.(>.(2.&40.)(65.R;.(3?.&5.(2>.#:.)))(98.R=.(9=.R<.#:.)))(>.$?.(?=.(:2.R<.)R7.R6.R5.)$17.))))))))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model top b off ne nlo nhi HC H. unfold fixed_args in H.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (split_lit (reg cs 10)) as [b0 off0] eqn:Hsp.
  destruct (mmap_len cs) as [[[ne0 nlo0] nhi0]|] eqn:HML; [|discriminate].
  destruct (xlo (kn cs) (reg cs 10)) as [alo|] eqn:Hxl; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [ahi|] eqn:Hxh; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hflat].
  injection H as <- <- <- <- <-.
  apply andb_prop in Hc as [Hc Htop]. apply andb_prop in Hc as [Hc Himg]. apply andb_prop in Hc as [Hpa Hpos].
  apply Z.ltb_lt in Hpos. apply Z.leb_le in Himg. apply Z.leb_le in Htop.
  pose proof (xlo_sound SEGS E _ (kn cs) _ alo HK Hxl). pose proof (xhi_sound SEGS E _ (kn cs) _ ahi HK Hxh).
  repeat split; try lia.
  - eapply page_aligned_sound; [exact HK | exact Hpa].
  - apply (reg_sound' E cs R FULL model); [exact HC | lia].
  - exact Hflat.
Qed.

(* [comment removed for export] *)
#[using="RES_len HULL_ok RES_len' HULL_ok' reg_sound'"] Lemma fixed_args_in_sound : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pcs,$43.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.Pb,$4:.Poff,$<.Pne,$4:.Pnlo,$<.Pnhi,$<.P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R:.R9.R8.R7.R6.)P,(>.(3<.(1.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.))(?>.R:.)(3>.(1.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.)(1?.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.(1?.(1.(1.$4:.$<.)$4:.)$<.(1?.(1.$4:.$<.)$4:.(1?.$4:.$<.R6.R5.)R4.)R3.)R2.)))(3.(>.(1.$4:.$<.)(?<.(9=.R;.#:.))(1?.$4:.$<.R7.R6.))(3.(>.(3<.(1.(1.$4:.$<.)$<.))(9<.R;.)(3>.(1.(1.$4:.$<.)$<.)(1?.(1.$4:.$<.)$<.(1?.$4:.$<.R5.R4.)R3.)))(3.(>.$<.(3;.(6.&40.(98.R<.(9=.R;.#:.)))+1000.)=)(3.(1:.=(6.&40.(98.R<.(9=.R;.#:.))))(3.(4.R3.$=?.)(3.(>.(2.&40.)(65.R:.(3?.&5.(2>.#:.)))(98.R<.(9=.R;.#:.)))(>.$?.(?=.(:2.R;.)R7.R6.R5.)$17.)))))))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model b off ne nlo nhi HC H. unfold fixed_args_in in H.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (split_lit (reg cs 10)) as [b0 off0] eqn:Hsp.
  destruct (mmap_len cs) as [[[ne0 nlo0] nhi0]|] eqn:HML; [|discriminate].
  destruct (xlo (kn cs) (reg cs 10)) as [alo|] eqn:Hxl; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hflat].
  injection H as <- <- <- <- <-.
  apply andb_prop in Hc as [Hc Hnhi]. apply andb_prop in Hc as [Hpa Hpos].
  apply Z.ltb_lt in Hpos. apply Z.leb_le in Hnhi.
  pose proof (xlo_sound SEGS E _ (kn cs) _ alo HK Hxl).
  repeat split; try lia.
  - eapply page_aligned_sound; [exact HK | exact Hpa].
  - apply (reg_sound' E cs R FULL model); [exact HC | lia].
  - exact Hflat.
Qed.

(* [comment removed for export] *)
#[using="A RES_len HULL_ok RES_len' HULL_ok'"] Lemma split_flat_estart : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.PM,P,(2.&40.)(3<.(2.&8.))Pk,(=.$9?.)Pe,$4:.Pb,$4:.Poff,$<.Pn,$4:.P,(;?.VSEGS,R7.R6.R5.)P,(>.(1.$4:.$<.)(?<.R5.)(1?.$4:.$<.R4.R3.))P,(>.$?.(?=.R7.R5.R4.R3.)$17.)(3.(>.$<.(<1.R:.(<2.R6.R5.))(6.&40.(98.R:.R7.)))(3.(4.(8.(<1.R:.(<2.R6.R5.))(6.&40.(98.R:.R4.)))(48.+2.+40.))(1:.=(6.&40.(98.R:.R4.)))))")
(* [comment removed for export] *).
Proof.
  intros E M k e b off n HK Hsp Hfl.
  destruct (APS.flat_x_sound SEGS E M k b off n HK Hfl) as (F1 & F2 & F3).
  pose proof (APS.u_of_split E e b off Hsp ltac:(lia)). repeat split; lia.
Qed.

(* [comment removed for export] *)
#[using="nx0 RES_len RES_hull HULL_ok HS XN XE XB RES_len' HULL_ok' RES_hullH maps_match_exact'"] Lemma region_free_of_apart : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pcs,$43.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.Pb,$4:.Poff,$<.Pne,$4:.Plo,(2.&40.)Pn,(2.&40.)P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R:.R9.R8.R7.R6.)P,(>.$?.(??.(:8.R:.))$17.)P,(>.$?.(100.$8>.Lm,$8>.(101.(:2.R<.)R8.R7.R6.(99.R1.)=(9:.R1.))(:8.R;.))$17.)P,(>.$<.(<1.R=.(<2.R8.R7.))(6.&40.R5.))P,(>.$<.(<3.R>.R7.)(6.&40.R5.))P,(4.(:.VA,)(6.&40.R7.))(>.$?.(1=.(1>.(1.(2.&40.)(2.&40.))(8;.(28.R<.))(2:.(28.R<.)))R8.R7.)$17.)")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model b off ne lo n HC Hnf Hall Hs Hn Himg.
  rewrite region_free_app. apply andb_true_intro. split.
  - apply reserved_free_above; [exact (co_res _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact Himg].
  - rewrite (proj1 (maps_match_exact' E _ _ Hnf) (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC)). apply RefNodes.region_free_intro. intros bm sm Hin.
    apply in_map_iff in Hin as (m & Hm & Hinm). unfold amap_den in Hm. injection Hm as <- <-.
    pose proof (proj1 (forallb_forall _ _) Hall m Hinm) as Hap.
    pose proof (ranges_apart_x_sound SEGS E _ (kn cs) b off ne (am_base m) 0 (am_len m) (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Hap) as D.
    unfold estart in D at 2 3. cbn [a_base a_off] in D. unfold elenZ in D, Hn. rewrite Hs, Hn in D. lia.
Qed.

Definition fixed_cs1 (cs : acs) (kd : mkind) (eager : bool) (ne : expr) (nhi : Z) : acs :=
  let k := kn cs in
  let m := AM (reg cs 10) ne kd in
  let ksh := if mkind_eqb kd KRWLAZY then flat_map (fun p => shadow_facts A k [m] (fst p) (snd p)) (a_vis cs) else [] in
  add_entry cs (s_regs (a_ss cs)) (ksh ++ kn_grant_filter A k (a_maps cs)) (nxt cs) m nhi eager (a_ylo cs).

(* [comment removed for export] *)
#[using="RES_len HULL_ok SHADOW_ok RES_len' HULL_ok' SHADOW_ok'"] Lemma shadow_facts_new_ok : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pcs,$43.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.Pa,(2.&40.)Pn,(2.&40.)PnZ,$<.Pne,$4:.Pmodel',$21.PFULL',P,(2.&40.)(3<.(2.&8.))P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R;.R:.R9.R8.R7.)P,(>.$<.(6.&40.R6.)R5.)P,(>.(2.&40.)(98.R=.R5.)R7.)P,(4.(8.(6.&40.R9.)R7.)$>3.)P,(>.(2.&40.)(98.R?.(9=.R>.#:.))R:.)P,(;6.$102.R;.R:.R<.R7.)P,(=0.$102.R<.R;.R>.R7.)P,Px,(2.&40.)P,(3.(4.(6.&40.R>.)(6.&40.R1.))(1:.(6.&40.R1.)(8.(6.&40.R>.)R<.)))(3.(>.$?.(10.(6.&40.R2.)(27.(28.R10.)))$1;.)(>.$?.A2.VargH,R14.R2.$1;.))(;?.VSEGS,R13.(=1.VA,VSP0,VargH,R13.R12.R:.R9.)(103.(1.$4:.$4:.)$9?.Lp,(1.$4:.$4:.)(:7.VA,(:2.R13.)(11.$8>.(=9.(9=.R13.#:.)R<.$102.)(38.$8>.))(7.$4:.$4:.R1.)(9.$4:.$4:.R1.))(:=.R12.)))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model a n nZ ne model' FULL' HC Un Hne HaC Hra GPo [GM1 GM2] NEW.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (u64_range a) as Ra. pose proof SHADOW_ok' as SO.
  unfold know_ok. apply Forall_flat_map. apply Forall_forall. intros p Hp.
  unfold shadow_facts.
  destruct (shadow_of A (kn cs) (fst p) (snd p)) as [[sb sk] sn] eqn:Hsh.
  (* [comment removed for export] *)
  assert (FIND : forall k' m, find_containing k' [AM (reg cs 10) ne KRWLAZY] [KRWLAZY] sb sk sn = Some m ->
                 xinside k' sb sk sn (reg cs 10) 0 ne = true).
  { intros k' m Hf. unfold find_containing in Hf. cbn [find] in Hf.
    match type of Hf with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    apply andb_prop in Hc as [_ Hins]. cbn [am_base am_len] in Hins. exact Hins. }
  assert (CONT : match find_containing (kn cs) [AM (reg cs 10) ne KRWLAZY] [KRWLAZY] sb sk sn with Some _ => true
                 | None => shadow_in_cls (kn cs) [AM (reg cs 10) ne KRWLAZY] (fst p) sb sk sn end = true ->
            exists k', know_ok SEGS E (MR E cs model FULL) k' /\ xinside k' sb sk sn (reg cs 10) 0 ne = true).
  { destruct (find_containing (kn cs) [AM (reg cs 10) ne KRWLAZY] [KRWLAZY] sb sk sn) as [m0|] eqn:Hf0;
      [intros _; exists (kn cs); split; [exact HK | exact (FIND _ _ Hf0)]|].
    intros Hcls. unfold shadow_in_cls in Hcls. apply existsb_exists in Hcls as [[[[[[cA oA] nA] cB] oB] nB] [Hfd Hcls]].
    unfold cls_cand_ok in Hcls.
    destruct (flat_x (kn cs) cA oA nA && flat_x (kn cs) cB oB nB)%bool eqn:Hfl; [|discriminate].
    apply andb_prop in Hfl as [FA FB].
    pose proof (APS.flat_x_sound SEGS E _ (kn cs) cA oA nA HK FA) as (FA1 & FA2 & FA3).
    pose proof (APS.flat_x_sound SEGS E _ (kn cs) cB oB nB HK FB) as (FB1 & FB2 & FB3).
    destruct (find_containing (APC.disj_var_fact (kn cs) cB oB nB cA oA ++ kn cs) [AM (reg cs 10) ne KRWLAZY] [KRWLAZY] sb sk sn) as [mL|] eqn:HfL; [|discriminate].
    destruct (find_containing (APC.disj_var_fact (kn cs) cA oA nA cB oB ++ kn cs) [AM (reg cs 10) ne KRWLAZY] [KRWLAZY] sb sk sn) as [mH|] eqn:HfH; [|discriminate].
    destruct (APS.disj_cands_sound SEGS E _ (kn cs) _ cA oA nA cB oB nB HK Hfd) as [Hd|Hd].
    - exists (APC.disj_var_fact (kn cs) cA oA nA cB oB ++ kn cs). split; [|exact (FIND _ _ HfH)].
      apply Forall_app. split; [|exact HK]. eapply APS.disj_var_fact_sound; [exact HK | lia | unfold elenZ in *; lia | exact Hd].
    - exists (APC.disj_var_fact (kn cs) cB oB nB cA oA ++ kn cs). split; [|exact (FIND _ _ HfL)].
      apply Forall_app. split; [|exact HK]. eapply APS.disj_var_fact_sound; [exact HK | lia | unfold elenZ in *; lia | exact Hd]. }
  match goal with |- Forall ?P (match ?f with Some _ => ?l | None => if ?c then _ else [] end) =>
    assert (GOAL : (exists k', know_ok SEGS E (MR E cs model FULL) k' /\ xinside k' sb sk sn (reg cs 10) 0 ne = true) -> Forall P l);
    [| destruct f as [m0|] eqn:Hf0; [exact (GOAL (CONT eq_refl)) | destruct c eqn:Hc0; [exact (GOAL (CONT eq_refl)) | constructor]]]
  end.
  intros (k' & HK' & Hins).
  pose proof (xinside_sound SEGS E _ k' sb sk sn (reg cs 10) 0 ne HK' Hins) as [I1 I2].
  unfold estart in I1, I2. cbn [a_base a_off] in I1, I2. rewrite Z.add_0_r in I1, I2. unfold elenZ in I2. rewrite Hne, Un in I2. rewrite Hra in I1, I2.
  pose proof HaC as HaC'. unfold CEIL in HaC'.
  (* [comment removed for export] *)
  unfold shadow_of in Hsh.
  destruct (split_lit (eadd (mkSrl (kn cs) (fst p) 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss. injection Hsh as -> -> <-.
  assert (Usn : bv_unsigned (edenot E (mkSrl (kn cs) (snd p) 3)) = bv_unsigned (edenot E (snd p)) / 8).
  { rewrite (mkSrl_denot SEGS E _ (kn cs) (snd p) 3 (Z_to_bv 64 3) HK) by (rewrite u64_lit by lia; reflexivity).
    rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
  rewrite Usn in I2.
  set (S0 := bv_unsigned (edenot E sb) + sk) in *.
  pose proof (u64_range (edenot E (fst p))) as Rb. pose proof (u64_range (edenot E (snd p))) as Rn.
  pose proof (u64_range (edenot E (mkSrl (kn cs) (snd p) 3))) as Rsn.
  assert (HS0 : S0 = shadow_off A + bv_unsigned (edenot E (fst p)) / 8).
  { pose proof (APS.split_lit_denot E _ sb sk Hss) as D. unfold eadd in D. rewrite mkAlu_denot in D. cbn [edenot] in D.
    apply (f_equal bv_unsigned) in D. rewrite u_add64 in D.
    rewrite (mkSrl_denot SEGS E _ (kn cs) (fst p) 3 (Z_to_bv 64 3) HK) in D by (rewrite u64_lit by lia; reflexivity).
    rewrite u_srl64 in D. fold S0 in D.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite !u64_lit in D by (unfold CEIL in *; lia).
    change (2 ^ (3 mod 64)) with 8 in D.
    rewrite (Z.mod_small (bv_unsigned (edenot E (fst p)) / 8 + shadow_off A)) in D by (unfold CEIL in *; lia).
    unfold CEIL in *. lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  (* [comment removed for export] *)
  assert (BYTE : forall y : word, S0 <= bv_unsigned y < S0 + bv_unsigned (edenot E (snd p)) / 8 ->
            MR E cs model' FULL' y = Some (Z_to_bv 8 0)).
  { intros y Hy.
    assert (Hya : bv_unsigned a <= bv_unsigned y < bv_unsigned a + nZ) by (clear -Hy I1 I2; lia).
    destruct (NEW y Hya) as [N1 N2].
    assert (Hsh2 : in_sh A E cs (bv_unsigned y) = true).
    { unfold in_sh. apply existsb_exists. exists p. split; [exact Hp|]. unfold sh_lo, sh_hi, uE.
      apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt].
      - lia.
      - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (V : VIS E cs model' y = true).
    { unfold vis. rewrite (gp_maps _ _ _ _ _ GPo), (gp_noacc _ _ _ _ _ GPo). cbn [kind_none].
      rewrite in_ivs_cons. cbn [fst snd]. rewrite Un, N1.
      rewrite (proj2 (Z.leb_le (bv_unsigned a) (bv_unsigned y))) by lia.
      rewrite (proj2 (Z.ltb_lt (bv_unsigned y) (bv_unsigned a + nZ))) by lia.
      unfold in_allow. rewrite Hsh2. rewrite !orb_true_r. cbn [andb orb negb]. rewrite ?orb_true_r. reflexivity. }
    unfold Mr, mrestrict, hid. rewrite N2, V. cbn [orb negb].
    rewrite (GM2 y) by (rewrite Un; exact Hya). reflexivity. }
  assert (Hfl : flat E (SA sb sk) (elenZ E (mkSrl (kn cs) (snd p) 3))).
  { unfold flat, estart, elenZ. cbn [a_base a_off]. fold S0. rewrite Usn. unfold CEIL in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; split; try exact Hfl;
    unfold estart, elenZ; cbn [a_base a_off]; fold S0; rewrite Usn.
  - intros d w Hd Hdw. destruct w as [|w']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by (unfold CEIL in *; lia); unfold CEIL in *; lia|].
    intros x Hx. rewrite u64_lit in Hx by (unfold CEIL in *; lia). unfold wview. rewrite (BYTE x) by lia. discriminate.
  - intros i Hi. apply BYTE. rewrite u64_lit by (unfold CEIL in *; lia). lia.
Qed.

(* [comment removed for export] *)
#[using="RES_len HULL_ok RES_len' HULL_ok' reg_sound' reg_lit_sound'"] Lemma fixed_pre : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pcs,$43.Ptop,$<.Pb,$4:.Poff,$<.Pne,$4:.Pnlo,$<.Pnhi,$<.PE,$94.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R4.R;.R3.R2.R1.)P,(>.(3<.(1.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.))(?;.VA,R<.R;.)(3>.(1.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.)(1?.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.(1?.(1.(1.$4:.$<.)$4:.)$<.(1?.(1.$4:.$<.)$4:.(1?.$4:.$<.R:.R9.)R8.)R7.)R6.)))P,(4.R<.$>3.)Zaddr,(2.&40.)(98.R7.(9=.R>.#:.))Zlen,$<.(6.&40.(98.R8.(9=.R?.#;.)))ZnZ,$<.(7<.R1.)Zn,(2.&40.)(3?.&40.R1.)(3.(>.(2.&40.)(98.R;.R>.)R1.)(3.(>.$<.(6.&40.R1.)R2.)(3.(>.$<.(<1.R;.(<2.R10.R?.))(6.&40.R4.))(3.(>.$<.(3;.(6.&40.R4.)+1000.)=)(3.(1:.=(6.&40.R4.))(3.(4.(:.VA,)(6.&40.R4.))(3.(4.(8.(6.&40.R4.)R2.)R11.)(3.(>.(2.&40.)(65.R:.(3?.&5.(2>.#:.)))R4.)(3.(>.$<.(3;.R2.+1000.)=)(3.(1:.=R2.)(4.R2.R<.)))))))))))")
(* [comment removed for export] *).
Proof.
  intros cs top b off ne nlo nhi E R FULL model HC HFA Htop addr len nZ n.
  destruct (fixed_args_sound E cs R FULL model top b off ne nlo nhi HC HFA) as (Hsp & HML & Hal & Hpos & Himg & HtopA & R10 & Hflat).
  fold addr in Hal, Hpos, Himg, HtopA, R10.
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & HneE).
  fold len in R11, Hlen, Hne, HnZ, HnZal. fold nZ in Hne, HnZ, HnZal. fold n in Hne.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. fold nZ in PB. unfold page_size in PB.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (split_flat_estart E _ (kn cs) (reg cs 10) b off ne HK Hsp Hflat) as (Hest & Hfl2 & Hfl3). fold addr in Hest.
  pose proof (u64_range addr) as Ra.
  assert (Un0 : bv_unsigned n = nZ).
  { subst n. apply u64_lit. split; [lia|]. pose proof (u64_range (Z_to_bv 64 nZ)) as Rn. unfold CEIL in Htop. lia. }
  split; [exact Hne|]. split; [exact Un0|]. split; [exact Hest|]. split; [exact Hal|]. split; [exact Hpos|].
  split; [exact Himg|]. split; [lia|]. split; [exact R10|]. split; [exact HnZal | lia].
Qed.

(* [comment removed for export] *)
#[using="A HULL_ok SHADOW_ok SP0 SP0_ok HULL_ok' SHADOW_ok' ATOP_facts'"] Lemma maps_match_unhole : forall E ms h l, maps_match E ms l <-> maps_match E (unhole ms h) l.
Proof.
  intros E ms h. unfold unhole. induction ms as [|m ms IH]; intros l; [cbn; tauto|].
  cbn [List.map maps_match].
  destruct (is_hole m && amap_eqb m h)%bool eqn:Hc.
  - apply andb_prop in Hc as [Hh _].
    assert (Hf : is_fog m = true) by (unfold is_fog, is_hole in *; destruct (am_kind m); cbn in Hh |- *; congruence).
    rewrite Hf. cbn [is_fog is_tok_kind am_kind am_len].
    split; (intros [H|(iv & l' & H1 & H2 & H3)]; [left; apply IH; exact H | right; exists iv, l'; split; [exact H1|]; split; [exact H2| apply IH; exact H3]]).
  - destruct (is_fog m).
    + split; (intros [H|(iv & l' & H1 & H2 & H3)]; [left; apply IH; exact H | right; exists iv, l'; split; [exact H1|]; split; [exact H2| apply IH; exact H3]]).
    + split; (intros (l' & H1 & H2); exists l'; split; [exact H1 | apply IH; exact H2]).
Qed.

(* [comment removed for export] *)
#[using="A RES_len RES_len'"] Lemma same_val_sound : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.PM,P,(2.&40.)(3<.(2.&8.))Pk,(=.$9?.)Pa,$4:.Pb,$4:.P,(;?.VSEGS,R5.R4.R3.)P,(>.$?.(104.R4.R3.R2.)$17.)(>.$<.(6.&40.(98.R7.R4.))(6.&40.(98.R7.R3.)))")
(* [comment removed for export] *).
Proof.
  intros E M k a b HK H. unfold same_val in H.
  destruct (expr_eqb a b) eqn:He; [apply expr_eqb_eq in He; subst; reflexivity|].
  destruct (lin_ge0 k [(a, 0)] [(b, 0)]) eqn:H1; [|discriminate].
  pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as X1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H) as X2.
  cbn [xt_den] in X1, X2. lia.
Qed.

(* [comment removed for export] *)
#[using="A RES_len RES_len'"] Lemma find_hole_sound : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.PM,P,(2.&40.)(3<.(2.&8.))Pk,(=.$9?.)Pms,(=.$8>.)Pa,$4:.Pne,$4:.Ph,$8>.P,(;?.VSEGS,R7.R6.R5.)P,(>.(3<.$8>.)(105.R6.R5.R4.R3.)(3>.$8>.R2.))(3.(19.$8>.R3.R6.)(3.(>.$?.(=5.R3.)$17.)(3.(>.$<.(;<.R9.(99.R3.))(6.&40.(98.R9.R5.)))(>.$<.(;<.R9.(9:.R3.))(6.&40.(98.R9.R4.))))))")
(* [comment removed for export] *).
Proof.
  intros E M k ms a ne h HK H. unfold find_hole in H. apply find_some in H as [Hin Hc].
  apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Hh H1].
  split; [exact Hin|]. split; [exact Hh|]. unfold uE.
  split; symmetry; [exact (same_val_sound E M k _ _ HK H1) | exact (same_val_sound E M k _ _ HK H2)].
Qed.

(* [comment removed for export] *)
#[using="HULL_ok SHADOW_ok SP0_ok HULL_ok' SHADOW_ok' ATOP_facts'"] Lemma cs_ok_unhole : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pcs,$43.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.Ph,$8>.P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R6.R5.R4.R3.R2.)(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R7.(106.R6.(107.(:8.R6.)R2.))R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model h HC.
  assert (ELEM : forall m, In m (unhole (a_maps cs) h) ->
            In m (a_maps cs) \/ exists m0, In m0 (a_maps cs) /\ m = AM (am_base m0) (am_len m0) KFOG).
  { intros m Hm. unfold unhole in Hm. apply in_map_iff in Hm as (m0 & Hm0 & Hin).
    destruct (is_hole m0 && amap_eqb m0 h)%bool; [right; exists m0; split; [exact Hin | symmetry; exact Hm0] | left; subst; exact Hin]. }
  destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xisp Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv].
  constructor; unfold with_maps0 in *;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn] in *; try assumption.
  - (* [comment removed for export] *) apply (proj1 (maps_match_unhole E _ h _)). exact Xmaps.
  - (* [comment removed for export] *) apply Forall_forall. intros m Hm Hk. destruct (ELEM m Hm) as [Hin|(m0 & Hin & ->)];
      [exact (proj1 (Forall_forall _ _) Xholes m Hin Hk) | cbn in Hk; discriminate].
  - (* [comment removed for export] *) apply Forall_forall. intros m Hm Hk. destruct (ELEM m Hm) as [Hin|(m0 & Hin & ->)];
      [exact (proj1 (Forall_forall _ _) Xnone m Hin Hk) | cbn in Hk; destruct Hk; discriminate].
  - (* [comment removed for export] *) apply Forall_forall. intros m Hm Hk. destruct (ELEM m Hm) as [Hin|(m0 & Hin & ->)];
      [exact (proj1 (Forall_forall _ _) Xkinds m Hin Hk) | cbn in Hk; discriminate].
  - (* [comment removed for export] *) eapply nlz_ok_weaken; [|eassumption]. intros m' Hm' Hf' Hk'.
    destruct (ELEM m' Hm') as [Hin|(m0 & Hin & ->)]; [exists m'; auto | cbn in Hf'; discriminate].
  - (* [comment removed for export] *) eapply nlz_ok_weaken; [|eassumption]. intros m' Hm' Hf' Hk'.
    destruct (ELEM m' Hm') as [Hin|(m0 & Hin & ->)]; [exists m'; auto | cbn in Hf'; discriminate].
  - (* [comment removed for export] *) eapply def_Forall_weaken; [|eassumption]. intros m' Hm' Hf' Hk'.
    destruct (ELEM m' Hm') as [Hin|(m0 & Hin & ->)]; [exists m'; auto | cbn in Hf'; discriminate].
  - (* [comment removed for export] *) eapply APS.cov_Forall_weaken; [|eassumption]. intros m' Hm' Hk'.
    destruct (ELEM m' Hm') as [Hin|(m0 & Hin & ->)]; [exists m'; auto | cbn in Hk'; destruct Hk' as [X|[X|[]]]; discriminate X].
Qed.

(* [comment removed for export] *)
#[using="RES_len HULL_ok SHADOW_ok SP0_ok argH_high SINV_frame SINV_sp RES_len' HULL_ok' SHADOW_ok' reg_sound' reg_lit_sound' kentry_keep_sem' kimg_clip_in_hull' ATOP_facts'"] Lemma mmap_fixed_grant_cs1 : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pcs,$43.Pms0,(=.$8>.)Pkd,$;5.Peager,$?.Ptop,$<.Pb,$4:.Poff,$<.Pne,$4:.Pnlo,$<.Pnhi,$<.PE,$94.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.Pmodel',$21.PFULL',P,(2.&40.)(3<.(2.&8.))P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R6.R10.R5.R4.R3.)P,(>.(3<.(1.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.))(?;.VA,R11.R=.)(3>.(1.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.)(1?.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.(1?.(1.(1.$4:.$<.)$4:.)$<.(1?.(1.$4:.$<.)$4:.(1?.$4:.$<.R<.R;.)R:.)R9.)R8.)))P,(4.R>.$>3.)P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R9.(106.R13.R12.)R8.R7.R6.)Zaddr,(2.&40.)(98.R:.(9=.R14.#:.))Zlen,$<.(6.&40.(98.R;.(9=.R15.#;.)))ZnZ,$<.(7<.R1.)Zn,(2.&40.)(3?.&40.R1.)P,(>.$?.(1=.(1>.(1.(2.&40.)(2.&40.))(8;.(28.R;.))(2:.(28.R;.)))R4.R1.)$17.)P,Pm,$8>.P,(19.$8>.R1.R19.)P,(>.$?.(=5.R2.)$17.)(35.(4.(8.(6.&40.R8.)R6.)(;<.R12.(99.R3.)))(4.(8.(;<.R12.(99.R3.))(;<.R12.(9:.R3.)))(6.&40.R8.)))P,P,(>.$?.R17.$17.)(4.(8.(8.(:<.R1;.)(:?.R1;.))R12.)VLIMIT,)P,(>.$?.(12.(=2.R19.)(=3.R19.))(25.R18.))P,(>.$?.(=4.R1:.)$1;.)P,(>.$?.(=6.R1;.$=7.)$1;.)P,(;6.R1<.R:.R7.R11.R10.)P,(=0.R1=.R;.R8.R13.R10.)(3.(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R16.(108.(106.R20.R1?.)R1>.R1=.R19.R17.)(7?.R15.(3?.&5.(2>.#:.))R<.)R11.R12.)Px,(2.&40.)P,(3.(4.(6.&40.R=.)(6.&40.R1.))(1:.(6.&40.R1.)(8.(6.&40.R=.)R;.)))(3.(>.$?.(10.(6.&40.R2.)(2:.(28.R14.)))$17.)(3.(>.$?.(10.(6.&40.R2.)(27.(28.R15.)))$1;.)(>.$?.A2.VargH,R18.R2.$1;.))))")
(* [comment removed for export] *).
Proof.
  intros cs ms0 kd eager top b off ne nlo nhi E R FULL model model' FULL' HC HFA Htop HC0 addr len nZ n Hrf Hholes Hbudget Hkind Hkfog HkdB GPo GM.
  destruct (fixed_pre cs top b off ne nlo nhi E R FULL model HC HFA Htop) as (Hne & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
  fold addr len nZ n in Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  assert (HaC : bv_unsigned addr + nZ <= CEIL) by lia.
  pose proof (APS.CEIL_le_ATOP SP0 SP0_ok) as HCA.
  assert (HaT : bv_unsigned addr + nZ <= ATOP) by lia.        (* [comment removed for export] *)
  assert (Hha : hull_apart A (bv_unsigned addr) nZ) by (right; exact Himg).
  assert (HnZpos : 0 < nZ) by lia.
  pose proof (grant_new_facts E cs R FULL model addr n nZ HC Hrf Un HnZpos Hha HaT) as NEW.
  destruct (grant_cs1_ok E (with_maps0 cs ms0) R FULL model kd addr n nZ model' FULL'
              (s_regs (a_ss cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr)
              (if mkind_eqb kd KRWLAZY then flat_map (fun p => shadow_facts A (kn cs) [AM (reg cs 10) ne kd] (fst p) (snd p)) (a_vis cs) else [])
              (reg cs 10) ne nhi eager (a_ylo cs) (nxt cs)
              HC0 Un HnZpos HnZal Hal Hha HaT Hpos Hrf GPo GM) as (HC1 & MROUT & MRSAME).   (* [comment removed for export] *)
  - apply regs_ok_regupd_same; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) | lia | exact R10].
  - reflexivity.
  - exact Hne.
  - destruct kd; cbn [mkind_eqb]; try constructor.
    change (MR E (with_maps0 cs ms0) model' FULL') with (MR E cs model' FULL').
    eapply shadow_facts_new_ok; [exact HC | exact Un | exact Hne | exact HaC | reflexivity | exact GPo | exact GM |].
    intros x Hx. destruct (NEW x Hx) as (_ & N1 & N2 & _). auto.
  - exact Hkind.
  - exact Hkfog.
  - lia.
  - exact Hbudget.
  - cbn [with_maps0 a_ylo]. lia.
  - cbn [with_maps0 a_maps]. exact Hholes.
  - exact HkdB.
  - split; [exact HC1|].
    intros x Hx. destruct (NEW x Hx) as (N0 & N1 & N2 & _). split; [|auto].
    rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons. cbn [fst snd]. rewrite Un.
    apply orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
#[using="nx0 RES_len RES_hull HULL_ok HS XN XE XB RES_len' HULL_ok' RES_hullH reg_sound' reg_lit_sound' maps_match_exact'"] Lemma mmap_fixed_old_facts : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pcs,$43.Pb,$4:.Poff,$<.Pne,$4:.Pnlo,$<.Pnhi,$<.PE,$94.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R4.R:.R3.R2.R1.)P,(>.(3<.(1.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.))(?;.VA,R;.$>2.)(3>.(1.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.)(1?.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.(1?.(1.(1.$4:.$<.)$4:.)$<.(1?.(1.$4:.$<.)$4:.(1?.$4:.$<.R:.R9.)R8.)R7.)R6.)))P,(>.$?.(??.(:8.R<.))$17.)P,(>.$?.(100.$8>.Lm,$8>.(101.(:2.R>.)R=.R<.R;.(99.R1.)=(9:.R1.))(:8.R=.))$17.)Zaddr,(2.&40.)(98.R8.(9=.R>.#:.))ZnZ,$<.(7<.(6.&40.(98.R9.(9=.R?.#;.))))(3.(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R:.(106.R10.(:8.R10.))R9.R8.R7.)(3.(>.$?.(1=.(1>.(1.(2.&40.)(2.&40.))(8;.(28.R7.))(2:.(28.R7.)))R2.(3?.&40.R1.))$17.)Pm,$8>.P,(19.$8>.R1.(:8.R11.))P,(>.$?.(=5.R2.)$17.)(35.(4.(8.(6.&40.R5.)R4.)(;<.R=.(99.R3.)))(4.(8.(;<.R=.(99.R3.))(;<.R=.(9:.R3.)))(6.&40.R5.)))))")
(* [comment removed for export] *).
Proof.
  intros cs b off ne nlo nhi E R FULL model HC HFA Hnf Hall addr nZ.
  destruct (fixed_pre cs KHI b off ne nlo nhi E R FULL model HC HFA ltac:(unfold KHI, CEIL; lia)) as (Hne & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
  fold addr nZ in Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  split; [|split].
  - destruct cs; exact HC.
  - eapply region_free_of_apart; [exact HC | exact Hnf | exact Hall | exact Hest | unfold elenZ; rewrite Hne; reflexivity | exact Himg].
  - intros m Hm Hk. exfalso. unfold no_fog in Hnf. pose proof (proj1 (forallb_forall _ _) Hnf m Hm) as X.
    apply negb_true_iff in X. unfold is_fog, is_hole in *. destruct (am_kind m); cbn in X, Hk; congruence.
Qed.

(* [comment removed for export] *)
#[using="RES_len HULL_ok SHADOW_ok SP0_ok RES_len' HULL_ok' SHADOW_ok' reg_sound' reg_lit_sound' ATOP_facts'"] Lemma mmap_fixed_hole_facts : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pcs,$43.Pb,$4:.Poff,$<.Pne,$4:.Pnlo,$<.Pnhi,$<.Ph,$8>.PE,$94.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R4.R;.R3.R2.R1.)P,(>.(3<.(1.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.))(?;.VA,R<.$>3.)(3>.(1.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.)(1?.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.(1?.(1.(1.$4:.$<.)$4:.)$<.(1?.(1.$4:.$<.)$4:.(1?.$4:.$<.R;.R:.)R9.)R8.)R7.)))P,(>.(3<.$8>.)(105.(:2.R=.)(:8.R=.)(9=.R=.#:.)R:.)(3>.$8>.R7.))P,(>.$?.(100.$8>.Lm,$8>.(12.(25.(=5.R1.))(101.(:2.R?.)R>.R=.R<.(99.R1.)=(9:.R1.)))(107.(:8.R>.)R8.))$17.)Zaddr,(2.&40.)(98.R8.(9=.R?.#:.))ZnZ,$<.(7<.(6.&40.(98.R9.(9=.R10.#;.))))(3.(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R:.(106.R11.(107.(:8.R11.)R;.))R9.R8.R7.)(3.(>.$?.(1=.(1>.(1.(2.&40.)(2.&40.))(8;.(28.R7.))(2:.(28.R7.)))R2.(3?.&40.R1.))$17.)Pm,$8>.P,(19.$8>.R1.(107.(:8.R12.)R<.))P,(>.$?.(=5.R2.)$17.)(35.(4.(8.(6.&40.R5.)R4.)(;<.R=.(99.R3.)))(4.(8.(;<.R=.(99.R3.))(;<.R=.(9:.R3.)))(6.&40.R5.)))))")
(* [comment removed for export] *).
Proof.
  intros cs b off ne nlo nhi h E R FULL model HC HFA Hfh Hap addr nZ.
  destruct (fixed_pre cs CEIL b off ne nlo nhi E R FULL model HC HFA ltac:(lia)) as (Hne & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
  fold addr nZ in Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (find_hole_sound E _ (kn cs) (a_maps cs) (reg cs 10) ne h HK Hfh) as (Hin & Hh & Hhb & Hhn).
  fold addr in Hhb. rewrite Hne, Un in Hhn.
  destruct (proj1 (Forall_forall _ _) (co_holes _ _ _ _ _ _ _ _ _ _ _ _ HC) h Hin Hh) as [F1 F2].
  rewrite Hhb, Hhn in F1, F2.
  split; [apply cs_ok_unhole; exact HC|]. split.
  - apply RefNodes.region_free_intro. intros b' s' Hin'. rewrite Un. destruct (F1 (b', s') Hin'); cbn [fst snd] in *; lia.
  - intros m Hm Hk. pose proof (proj1 (forallb_forall _ _) Hap m Hm) as X. cbn beta in X. rewrite Hk in X. cbn [negb orb] in X.
    pose proof (ranges_apart_x_sound SEGS E _ (kn cs) b off ne (am_base m) 0 (am_len m) HK X) as D.
    unfold estart in D at 2 3. cbn [a_base a_off] in D. unfold elenZ in D. rewrite Hest, Hne, Un in D. unfold uE. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="SEGS A RES_len RES_len'"] Lemma seps_map_disjoint : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pf,P,$8>.(1.(2.&40.)(2.&40.))Pms,(=.$8>.)Pm,$8>.Pm',$8>.P,(92.(90.$8>.(1.(2.&40.)(2.&40.))R4.R3.))P,(19.$8>.R3.R4.)P,(19.$8>.R3.R5.)P,(1<.(>.$8>.R5.R4.))(93.A1.R8.R6.A1.R8.R5.)")
(* [comment removed for export] *).
Proof.
  intros f ms. induction ms as [|h t IH]; intros m m' Hs Hm Hm' Hne; [destruct Hm|].
  cbn [map] in Hs. inversion Hs as [|p l Hf Hl]; subst.
  destruct Hm as [<-|Hm]; destruct Hm' as [<-|Hm'].
  - exfalso. exact (Hne eq_refl).
  - exact (proj1 (Forall_forall _ _) Hf (f m') (in_map f t m' Hm')).
  - pose proof (proj1 (Forall_forall _ _) Hf (f m) (in_map f t m Hm)) as D. unfold iv_disjoint in *. lia.
  - exact (IH m m' Hl Hm Hm' Hne).
Qed.

(* [comment removed for export] *)
#[using="SEGS A RES_len RES_len'"] Lemma maps_match_disjoint : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pms,(=.$8>.)Pl,(=.(1.(2.&40.)(2.&40.)))Pm,$8>.Pm',$8>.P,(96.R5.R4.R3.)P,(92.R4.)P,(19.$8>.R4.R6.)P,(19.$8>.R4.R7.)P,(>.$?.(95.R6.)$1;.)P,(>.$?.(95.R6.)$1;.)P,(1<.(>.$8>.R8.R7.))(93.(97.R<.R9.)(97.R<.R8.))")
(* [comment removed for export] *).
Proof.
  intros E ms. induction ms as [|h t IH]; intros l m m' HM Hs Hm Hm' Hf Hf' Hne; [destruct Hm|].
  cbn [maps_match] in HM. destruct (is_fog h) eqn:Hfh.
  - assert (Hmt : In m t) by (destruct Hm as [<-|Hm]; [congruence | exact Hm]).
    assert (Hmt' : In m' t) by (destruct Hm' as [<-|Hm']; [congruence | exact Hm']).
    destruct HM as [HM|(iv & l' & -> & _ & HM)].
    + exact (IH l m m' HM Hs Hmt Hmt' Hf Hf' Hne).
    + inversion Hs as [|p l0 Hfa Hl]; subst. exact (IH l' m m' HM Hl Hmt Hmt' Hf Hf' Hne).
  - destruct HM as (l' & -> & HM). inversion Hs as [|p l0 Hfa Hl]; subst.
    destruct Hm as [<-|Hm]; destruct Hm' as [<-|Hm'].
    + exfalso. exact (Hne eq_refl).
    + exact (proj1 (Forall_forall _ _) Hfa (amap_den E m') (maps_match_In E t l' m' HM Hm' Hf')).
    + pose proof (proj1 (Forall_forall _ _) Hfa (amap_den E m) (maps_match_In E t l' m HM Hm Hf)) as D. unfold iv_disjoint in *. lia.
    + exact (IH l' m m' HM Hl Hm Hm' Hf Hf' Hne).
Qed.

(* [comment removed for export] *)
#[using="SEGS A RES_len HULL_ok RES_len' HULL_ok'"] Lemma overlap_sum_contained : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pl,(=.(1.(2.&40.)(2.&40.)))Pb,(2.&40.)Ps,(2.&40.)Plo,$<.Phi,$<.P,(92.R5.)P,(19.(1.(2.&40.)(2.&40.))(1?.(2.&40.)(2.&40.)R5.R4.)R6.)P,(4.(6.&40.R6.)R4.)P,(4.R4.(8.(6.&40.R7.)(6.&40.R6.)))P,(4.R6.R5.)(4.(109.R:.R7.R6.)(=>.R6.R7.))")
(* [comment removed for export] *).
Proof.
  intros l b s lo hi Hs Hin H1 H2 Hlh. induction l as [|p l IH]; [destruct Hin|].
  inversion Hs as [|p' l' Hf Hl]; subst. rewrite overlap_sum_cons. destruct Hin as [->|Hin].
  - pose proof (iv_count_in_rng_le (b, s) lo hi Hlh).
    assert (Z0 : overlap_sum l lo hi = 0); [|lia].
    clear IH Hs. revert Hf Hl. induction l as [|q l IH2]; intros Hf Hl; [reflexivity|]. rewrite overlap_sum_cons.
    apply Forall_cons_iff in Hf as [Hq Hf']. inversion Hl; subst.
    rewrite (IH2 Hf' ltac:(assumption)). rewrite iv_count_in_rng_disjoint; [lia|].
    unfold iv_disjoint, B, S in *. cbn [fst snd] in Hq. lia.
  - pose proof (IH Hl Hin) as IH'. rewrite iv_count_in_rng_disjoint; [lia|].
    pose proof (proj1 (Forall_forall _ _) Hf (b, s) Hin) as D. unfold iv_disjoint, B, S in *. cbn [fst snd] in D. lia.
Qed.

#[using="Type"] Lemma rekind_den : forall E ms m, map (amap_den E) (rekind ms m) = map (amap_den E) ms.
Proof.
  intros E ms m. unfold rekind. rewrite map_map. apply map_ext. intros m'. destruct (amap_eqb m' m); reflexivity.
Qed.

#[using="Type"] Lemma in_rekind : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pms,(=.$8>.)Pm,$8>.Pm',$8>.P,(19.$8>.R1.(10:.R3.R2.))(18.$8>.Lm0,$8>.(3.(19.$8>.R1.R5.)(35.(3.(>.$8>.R1.R4.)(>.$8>.R3.(=9.(99.R4.)(9:.R4.)(10;.(10<.R4.)))))(3.(1<.(>.$8>.R1.R4.))(>.$8>.R3.R1.)))))")
(* [comment removed for export] *).   (* [comment removed for export] *)
Proof.
  intros ms m m' H. unfold rekind in H. apply in_map_iff in H as (m0 & Hm0 & Hin). exists m0. split; [exact Hin|].
  destruct (amap_eqb m0 m) eqn:He.
  - left. apply APS.amap_eqb_eq in He. subst m0. auto.
  - right. split; [|symmetry; exact Hm0]. intros ->. rewrite amap_eqb_refl in He. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma born_rekind : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pms,(=.$8>.)Pm,$8>.Pks,(=.$;5.)Piv,(1.(2.&40.)(2.&40.))P,Pk,$;5.(1<.(19.$;5.(10;.R1.)R3.))P,(10=.R6.(10:.R5.R4.)R3.R2.)(18.$8>.Lm1,$8>.(3.(19.$8>.R1.R7.)(3.(1<.(>.$8>.R1.R6.))(3.(>.$?.(95.R1.)$1;.)(3.(19.$;5.(10<.R1.)R5.)(>.(1.(2.&40.)(2.&40.))(97.R8.R1.)R4.))))))")
(* [comment removed for export] *).
Proof.
  intros E ms m ks iv Hks (m' & Hin & Hf & Hk & Hd). destruct (in_rekind ms m m' Hin) as (m0 & Hin0 & [[-> ->]|[Hne ->]]).
  - exfalso. cbn [am_kind] in Hk. exact (Hks _ Hk).
  - exists m0. auto 6.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma rekind_k_not_def : forall k, In (rekind_k k) APS.K_DEF -> False.
Proof. intros k H. destruct k; cbn in H; destruct H as [K|[K|[]]]; discriminate K. Qed.
#[using="Type"] Lemma born_rekind_weaken : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pms,(=.$8>.)Pm,$8>.Pks,(=.$;5.)Piv,(1.(2.&40.)(2.&40.))P,(>.$?.(95.R3.)$1;.)P,Pk,$;5.P,(19.$;5.(10;.R1.)R4.)(19.$;5.R2.R5.)P,(10=.R7.(10:.R6.R5.)R4.R3.)(10=.R8.R7.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros E ms m ks iv Hnf Hks (m' & Hin & Hf & Hk & Hd). destruct (in_rekind ms m m' Hin) as (m0 & Hin0 & [[-> ->]|[Hne ->]]).
  - exists m. cbn [am_kind] in Hk. unfold amap_den in Hd |- *. cbn [am_base am_len] in Hd.
    split; [exact Hin0|]. split; [exact Hnf|]. split; [exact (Hks _ Hk) | exact Hd].
  - exists m0. auto.
Qed.
#[using="Type"] Lemma is_fog_rekind : forall m, is_fog m = false -> is_fog (AM (am_base m) (am_len m) (rekind_k (am_kind m))) = false.
Proof. intros [b l k] H. unfold is_fog in *. cbn [am_kind] in *. destruct k; cbn in *; congruence. Qed.
#[using="Type"] Lemma is_hole_rekind : forall m, is_fog m = false -> is_hole (AM (am_base m) (am_len m) (rekind_k (am_kind m))) = false.
Proof. intros [b l k] H. unfold is_fog, is_hole in *. cbn [am_kind] in *. destruct k; cbn in *; congruence. Qed.
#[using="Type"] Lemma rekind_k_not_none : forall k, rekind_k k <> KNONE /\ rekind_k k <> KNONELAZY /\ rekind_k k <> KRWLAZY.
Proof. intros []; cbn; repeat split; discriminate. Qed.
#[using="Type"] Lemma KMIXED_notnone : forall k, ~ In (rekind_k k) K_NOTNONE. Proof. intros k; unfold K_NOTNONE; destruct k; cbn; intros [H|[H|[]]]; discriminate. Qed.
#[using="Type"] Lemma KMIXED_notnone_w : forall k, In (rekind_k k) K_NOTNONE -> In k K_NOTNONE. Proof. intros k H. exfalso. exact (KMIXED_notnone k H). Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma uE_eaddz : forall E b off z, estart E (SA b off) = z -> 0 <= z < 2 ^ 64 -> uE E (eaddz b off) = z.
Proof.
  intros E b off z Hest Hz. clear - Hest Hz. unfold uE, eaddz. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite u_lit64a.
  unfold estart in Hest. cbn [a_base a_off] in Hest.
  rewrite Z.add_mod_idemp_r by lia. rewrite Hest. apply Z.mod_small. exact Hz.
Qed.
#[using="A HULL_ok SHADOW_ok SP0 SP0_ok HULL_ok' SHADOW_ok' ATOP_facts'"] Lemma KMIXED_eager : forall k, In (rekind_k k) K_EAGER -> In k K_EAGER.
Proof. intros k H; unfold K_EAGER in *; destruct k; cbn in H |- *; first [tauto | exfalso; destruct H as [H|[H|[H|[]]]]; discriminate H]. Qed.

#[using="Type"] Lemma covered_maps_subtract : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pl,(=.(1.(2.&40.)(2.&40.)))Plo,$<.Phi,$<.Px,$<.P,(36.R4.)P,(4.R4.R3.)(>.$?.(26.(37.R6.R5.R4.)R3.)(13.(26.R6.R3.)(25.(10>.R5.R4.R3.))))")
(* [comment removed for export] *).
Proof. intros. apply (proj2 (proj2 (maps_subtract_sem l lo hi H H0))). Qed.

Inductive slarm := SlE | SlF | SlG | SlM.

Definition sl_nn (s : slarm) : bool := match s with SlG => true | _ => false end.
Definition sl_charge (s : slarm) : bool := match s with SlE | SlM => true | _ => false end.

Record slice_post (s : slarm) (addr n : word) (model model' : Model) : Prop := SP {
  sp_maps : vm_maps (m_vmmaps model') = vm_maps (m_vmmaps model);
  sp_res : vm_reserved (m_vmmaps model') = vm_reserved (m_vmmaps model);
  sp_noacc : vm_noaccess (m_vmmaps model') =
             (if sl_nn s then [(addr, n)] else [])
               ++ maps_subtract (vm_noaccess (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n);
  sp_lazy : m_vm_lazy model' =
            match s with
            | SlM => m_vm_lazy model
            | SlF => (addr, n) :: maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
            | _ => maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
            end;
  sp_mat : m_vm_materialized model' =
           match s with
           | SlM => m_vm_materialized model
           | _ => List.filter (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model)
           end;
  sp_limit : vm_limit (m_vmmaps model') = vm_limit (m_vmmaps model);
  sp_brk : vm_brk (m_vmmaps model') = vm_brk (m_vmmaps model);
  sp_sbrk : vm_start_brk (m_vmmaps model') = vm_start_brk (m_vmmaps model);
  sp_mbase : vm_mmap_base (m_vmmaps model') = vm_mmap_base (m_vmmaps model);
  sp_halted : m_halted model' = m_halted model;
  sp_fds : m_fds model' = m_fds model;
  sp_fs : m_fs model' = m_fs model;
  sp_tid : m_tid model' = m_tid model;
  sp_isp : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model)  (* [comment removed for export] *) }.

Definition slice_mem (s : slarm) (addr n : word) (FULL FULL' : word -> option byte) : Prop :=
  (forall x : word, bv_unsigned x < bv_unsigned addr \/ bv_unsigned addr + bv_unsigned n <= bv_unsigned x -> FULL' x = FULL x)
  /\ (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + bv_unsigned n ->
        FULL' x = if sl_nn s then None else Some (Z_to_bv 8 0)).

(* [comment removed for export] *)
Record slice_hyps (E : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model)
       (s : slarm) (m : amap) (addr n : word) (nZ : Z) (model' : Model) (FULL' : word -> option byte) : Prop := SH_ {
  sh_C : CSOK E cs R FULL model;
  sh_m : In m (a_maps cs);
  sh_nf : is_fog m = false;
  sh_Un : bv_unsigned n = nZ;
  sh_pos : 0 < nZ;
  sh_nal : nZ mod 4096 = 0;
  sh_al : bv_unsigned addr mod 4096 = 0;
  sh_in1 : bv_unsigned (edenot E (am_base m)) <= bv_unsigned addr;
  sh_in2 : bv_unsigned addr + nZ <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m));
  sh_post : slice_post s addr n model model';
  sh_mem : slice_mem s addr n FULL FULL';
  sh_F : s = SlF -> am_kind m = KRWLAZY;
  sh_nF : s <> SlF -> am_kind m <> KRWLAZY }.

Section Slice.
  Variables (E : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Variables (s : slarm) (m : amap) (addr n : word) (nZ : Z) (model' : Model) (FULL' : word -> option byte).
  Hypothesis SH : slice_hyps E cs R FULL model s m addr n nZ model' FULL'.
  Let HC := sh_C _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hm := sh_m _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hnf := sh_nf _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Un := sh_Un _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let HnZpos := sh_pos _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let HnZal := sh_nal _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hal := sh_al _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hin1 := sh_in1 _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hin2 := sh_in2 _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let SPo := sh_post _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let SM := sh_mem _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let HF := sh_F _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let HnF := sh_nF _ _ _ _ _ _ _ _ _ _ _ _ SH.

  Let lo := bv_unsigned addr.
  Let hi := bv_unsigned addr + nZ.

  (* [comment removed for export] *)
  #[using="SEGS LIMIT SINV argH FS0 cs R FULL model s addr n nZ model' FULL' SH HC Hm Hnf"] Lemma sl_bounds : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "(3.(1:.=(6.&40.(98.VE,(9:.Vm,))))(3.(>.$<.(3;.(6.&40.(98.VE,(99.Vm,)))+1000.)=)(3.(>.$<.(3;.(6.&40.(98.VE,(9:.Vm,)))+1000.)=)(3.(9>.VA,(6.&40.(98.VE,(99.Vm,)))(6.&40.(98.VE,(9:.Vm,))))(3.(4.(8.(6.&40.(98.VE,(99.Vm,)))(6.&40.(98.VE,(9:.Vm,))))(<6.VSP0,))(1:.=(6.&40.(98.VE,(99.Vm,)))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)
  Proof.
    pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HC) as B.
    exact (proj1 (Forall_forall _ _) B (amap_den E m) (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf)).
  Qed.

  #[using="SEGS LIMIT SINV argH FS0 RES_len HULL_ok SP0_ok RES_len' HULL_ok' ATOP_facts' E cs R FULL model s m n model' FULL' SH HC Hm Hnf HnZpos HnZal Hal Hin1 Hin2"] Lemma sl_lohi : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "(3.(35.(4.Vhi,(5.VA,))(4.(:.VA,)Vlo,))(3.(4.Vhi,(<6.VSP0,))(3.(1:.Vlo,Vhi,)(3.(4.Vhi,(48.+2.+40.))(3.(>.$<.(3;.Vlo,+1000.)=)(>.$<.(3;.Vhi,+1000.)=))))))")
(* [comment removed for export] *).
  Proof.
    pose proof sl_bounds as (B1 & B2 & B3 & B4 & B5 & B6). subst lo hi. unfold hull_apart in B4. atopb.
    repeat split; try lia. rewrite Z.add_mod, Hal, HnZal by lia. reflexivity.
  Qed.

  #[using="SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SP0 RES_len' HULL_ok' E cs R FULL s m n model' FULL' SH HC Hm Hnf HnZpos Hin1 Hin2"] Lemma sl_in_maps : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Px,(2.&40.)P,(3.(4.Vlo,(6.&40.R1.))(1:.(6.&40.R1.)Vhi,))(>.$?.(10.(6.&40.R2.)(2:.(28.Vmodel,)))$17.)")
(* [comment removed for export] *).
  Proof.
    intros x Hx. eapply in_ivs_maps_match; [exact (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hm | exact Hnf |]. subst lo hi. lia.
  Qed.

  #[using="SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SP0 SP0_ok RES_len' HULL_ok' ATOP_facts' E cs R FULL model s m addr n nZ FULL' SH HC Hm Hnf Un HnZpos HnZal Hal Hin1 Hin2 SPo lo hi"] Lemma sl_wf' : model_ivs_wf model'.
  Proof.
    pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & Wsp). pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
    assert (iv_wf (addr, n)) by (unfold iv_wf, B, S; cbn; subst lo hi; lia).
    unfold model_ivs_wf. rewrite (sp_maps _ _ _ _ _ SPo), (sp_noacc _ _ _ _ _ SPo), (sp_lazy _ _ _ _ _ SPo).
    split; [exact W1|]. split; [|split; [|unfold init_sp_ok in *; rewrite (sp_isp _ _ _ _ _ SPo); exact Wsp]].
    - apply ivs_wf_app; [destruct (sl_nn s); [apply ivs_wf_cons; [assumption | apply ivs_wf_nil] | apply ivs_wf_nil] |].
      apply maps_subtract_wf; [exact W2 | rewrite Un; lia].
    - destruct s; try exact W3; try (apply ivs_wf_cons; [assumption|]); apply maps_subtract_wf; try assumption; rewrite Un; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="SEGS A LIMIT SINV argH FS0 RES_len SP0 RES_len' E cs R FULL s m n FULL' SH HC Un HnZpos SPo"] Lemma sl_noacc_out : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Px,(2.&40.)P,(35.(1:.(6.&40.R1.)Vlo,)(4.Vhi,(6.&40.R1.)))(>.$?.(10.(6.&40.R2.)(27.(28.Vmodel',)))(10.(6.&40.R2.)(27.(28.Vmodel,))))")
(* [comment removed for export] *).
  Proof.
    intros x Hx. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _).
    rewrite (sp_noacc _ _ _ _ _ SPo), in_ivs_app. rewrite !in_ivs_covered.
    rewrite covered_maps_subtract by (try exact W2; rewrite Un; lia). rewrite Un.
    replace (in_rng (bv_unsigned addr) (bv_unsigned addr + nZ) (bv_unsigned x)) with false
      by (symmetry; unfold in_rng; apply andb_false_iff; subst lo hi; destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    destruct (sl_nn s); cbn [app]; [|rewrite andb_true_r; reflexivity].
    rewrite <- in_ivs_covered, in_ivs_cons. cbn [fst snd in_ivs existsb]. rewrite Un.
    replace ((bv_unsigned addr <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned addr + nZ))%bool with false
      by (symmetry; apply andb_false_iff; subst lo hi; destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    cbn [orb]. rewrite andb_true_r. reflexivity.
  Qed.

  #[using="SEGS A LIMIT SINV argH FS0 RES_len SP0 RES_len' E cs R FULL model m n FULL' SH HC Un HnZpos SPo"] Lemma sl_noacc_in : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Px,(2.&40.)P,(3.(4.Vlo,(6.&40.R1.))(1:.(6.&40.R1.)Vhi,))(>.$?.(10.(6.&40.R2.)(27.(28.Vmodel',)))(10?.Vs,))")
(* [comment removed for export] *).
  Proof.
    intros x Hx. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _).
    rewrite (sp_noacc _ _ _ _ _ SPo), in_ivs_app. rewrite (in_ivs_covered _ (maps_subtract _ _ _)).
    rewrite covered_maps_subtract by (try exact W2; rewrite Un; lia). rewrite Un.
    replace (in_rng (bv_unsigned addr) (bv_unsigned addr + nZ) (bv_unsigned x)) with true
      by (symmetry; unfold in_rng; apply andb_true_intro; subst lo hi; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [negb]. rewrite andb_false_r, orb_false_r.
    destruct (sl_nn s); cbn [app in_ivs existsb fst snd]; [|reflexivity]. rewrite Un.
    rewrite (proj2 (Z.leb_le _ _)) by (subst lo; lia). rewrite (proj2 (Z.ltb_lt _ _)) by (subst hi; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SP0 SP0_ok RES_len' HULL_ok' ATOP_facts' E cs R FULL s m n FULL' SH HC Hm Hnf HnZpos HnZal Hal Hin1 Hin2 SPo"] Lemma sl_lazy_out : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Px,(2.&40.)P,(35.(1:.(6.&40.R1.)Vlo,)(4.Vhi,(6.&40.R1.)))(>.$?.(39.(3:.R2.)(29.Vmodel',))(39.(3:.R2.)(29.Vmodel,)))")
(* [comment removed for export] *).
  Proof.
    intros x Hx. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _). pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
    pose proof (page_of_byte_out_aligned x lo hi L5 L6 Hx) as P. subst lo hi.
    rewrite (sp_lazy _ _ _ _ _ SPo). destruct s; try reflexivity.
    - apply page_in_ranges_subtract_out; [exact W3 | rewrite Un; lia | unfold page_size; rewrite Un; lia].
    - rewrite page_in_ranges_cons_out; [| unfold page_size; rewrite Un; lia | rewrite Un; lia].
      apply page_in_ranges_subtract_out; [exact W3 | rewrite Un; lia | unfold page_size; rewrite Un; lia].
    - apply page_in_ranges_subtract_out; [exact W3 | rewrite Un; lia | unfold page_size; rewrite Un; lia].
  Qed.

  #[using="SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SP0 SP0_ok RES_len' HULL_ok' ATOP_facts' E cs R FULL m n FULL' SH HC Hm Hnf HnZpos HnZal Hal Hin1 Hin2 SPo"] Lemma sl_lazy_in : forall x : word, lo <= bv_unsigned x < hi ->
    page_in_ranges (page_base x) (m_vm_lazy model') =
      match s with SlM => page_in_ranges (page_base x) (m_vm_lazy model) | SlF => true | _ => false end.
  Proof.
    intros x Hx. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _). pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
    destruct (page_of_byte_in_aligned x lo hi L5 L6 Hx) as [P1 P2]. subst lo hi.
    rewrite (sp_lazy _ _ _ _ _ SPo). destruct s; try reflexivity.
    - apply page_in_ranges_subtract_in; [exact W3 | rewrite Un; lia].
    - apply page_in_ranges_cons_in; unfold page_size; rewrite ?Un; lia.
    - apply page_in_ranges_subtract_in; [exact W3 | rewrite Un; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="SEGS LIMIT SINV argH FS0 RES_len HULL_ok SP0_ok RES_len' HULL_ok' ATOP_facts' R FULL s m n FULL' SH HC Hm Hnf Un HnZpos HnZal Hal Hin1 Hin2 SPo"] Lemma sl_vis_out : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pcs1,$43.Px,(2.&40.)P,(>.(=.(1.$4:.$4:.))(:=.R2.)(:=.Vcs,))P,(35.(1:.(6.&40.R2.)Vlo,)(4.Vhi,(6.&40.R2.)))(>.$?.(;7.VA,VSP0,VE,R4.Vmodel',R3.)(;7.VA,VSP0,VE,Vcs,Vmodel,R3.))")
(* [comment removed for export] *).
  Proof.
    intros cs1 x Hv Hx. unfold vis. rewrite (sp_maps _ _ _ _ _ SPo), (sl_noacc_out x Hx), (sl_lazy_out x Hx), (in_allow_ext E cs cs1 Hv). reflexivity.
  Qed.

  #[using="SEGS LIMIT SINV FS0 RES_len HULL_ok SP0_ok RES_len' HULL_ok' ATOP_facts' R s m n SH HC Hm Hnf Un HnZpos HnZal Hal Hin1 Hin2 SPo SM"] Lemma sl_MR_out : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pcs1,$43.Px,(2.&40.)P,(>.(=.(1.$4:.$4:.))(:=.R2.)(:=.Vcs,))P,(35.(1:.(6.&40.R2.)Vlo,)(4.Vhi,(6.&40.R2.)))(>.(3<.(2.&8.))(=1.VA,VSP0,VargH,VE,R4.Vmodel',VFULL',R3.)(=1.VA,VSP0,VargH,VE,Vcs,Vmodel,VFULL,R3.))")
(* [comment removed for export] *).
  Proof.
    intros cs1 x Hv Hx. unfold Mr, mrestrict, hid. rewrite (sl_vis_out cs1 x Hv Hx). rewrite (proj1 SM x) by (subst lo hi; rewrite Un; exact Hx). reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="SEGS LIMIT SINV argH FS0 RES_len HULL_ok SP0_ok RES_len' HULL_ok' ATOP_facts' cs R FULL model m n FULL' SH HC Hm Hnf Un HnZpos HnZal Hal Hin1 Hin2 SPo"] Lemma sl_vis_in_E : s = SlE -> forall cs1 (x : word), lo <= bv_unsigned x < hi -> VIS E cs1 model' x = true.
  Proof.
    intros Hs cs1 x Hx. unfold vis. rewrite (sp_maps _ _ _ _ _ SPo), (sl_in_maps x Hx), (sl_noacc_in x Hx), (sl_lazy_in x Hx). subst s.
    cbn. rewrite !orb_true_r. reflexivity.
  Qed.

  #[using="SEGS LIMIT SINV FS0 RES_len HULL_ok SP0_ok RES_len' HULL_ok' ATOP_facts' cs R FULL model m n FULL' SH HC Hm Hnf Un HnZpos HnZal Hal Hin1 Hin2 SPo"] Lemma sl_vis_in_G : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "P,(>.$110.Vs,$111.)Pcs1,$43.Px,(2.&40.)P,(3.(4.Vlo,(6.&40.R1.))(1:.(6.&40.R1.)Vhi,))P,(>.$?.A2.VargH,VE,R2.$1;.)(>.$?.(;7.VA,VSP0,VE,R4.Vmodel',R3.)$1;.)")
(* [comment removed for export] *).
  Proof.
    intros Hs cs1 x Hx Ha. pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6). unfold vis.
    rewrite (sp_maps _ _ _ _ _ SPo), (sl_in_maps x Hx), (sl_noacc_in x Hx). subst s. cbn [sl_nn negb andb].
    replace (in_hull A (bv_unsigned x)) with false by (symmetry; unfold in_hull; apply andb_false_iff; destruct L1 as [L1|L1]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    replace (ATOP <=? bv_unsigned x) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  #[using="SEGS LIMIT SINV argH FS0 RES_len HULL_ok SP0_ok RES_len' HULL_ok' ATOP_facts' R FULL m n FULL' SH HC Hm Hnf Un HnZpos HnZal Hal Hin1 Hin2 SPo HF"] Lemma sl_vis_in_F : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "P,(>.$110.Vs,$112.)Pcs1,$43.Px,(2.&40.)P,(>.(=.(1.$4:.$4:.))(:=.R2.)(:=.Vcs,))P,(3.(4.Vlo,(6.&40.R2.))(1:.(6.&40.R2.)Vhi,))(>.$?.(;7.VA,VSP0,VE,R4.Vmodel',R3.)(;7.VA,VSP0,VE,Vcs,Vmodel,R3.))")
(* [comment removed for export] *).
  Proof.
    intros Hs cs1 x Hv Hx. unfold vis.
    rewrite (sp_maps _ _ _ _ _ SPo), (sl_in_maps x Hx), (sl_noacc_in x Hx), (sl_lazy_in x Hx), (in_allow_ext E cs cs1 Hv).
    destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ _ HC) m Hm (HF Hs) x ltac:(subst lo hi; lia)) as [K1 K2].
    rewrite K1, K2. subst s. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SP0 SP0_ok RES_len' HULL_ok' ATOP_facts' E cs R FULL m addr n FULL' SH HC Hm Hnf Un HnZpos HnZal Hal Hin1 Hin2 SPo lo hi"] Lemma sl_eager : eager_used model' <= eager_used model + (if sl_charge s then nZ else 0).
  Proof.
    pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf. pose proof Hwf as (W1 & W2 & W3 & _). pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
    rewrite (eager_used_sem model' sl_wf'), (eager_used_sem model Hwf). rewrite (sp_maps _ _ _ _ _ SPo).
    set (C := vm_noaccess (m_vmmaps model) ++ m_vm_lazy model).
    set (C' := vm_noaccess (m_vmmaps model') ++ m_vm_lazy model').
    assert (CEQ : forall x, covered C' x =
              ((sl_nn s && in_rng lo hi x)
               || (covered (vm_noaccess (m_vmmaps model)) x && negb (in_rng lo hi x))
               || match s with
                  | SlM => covered (m_vm_lazy model) x
                  | SlF => in_rng lo hi x || (covered (m_vm_lazy model) x && negb (in_rng lo hi x))
                  | _ => covered (m_vm_lazy model) x && negb (in_rng lo hi x)
                  end)%bool).
    { intros x. subst C'. rewrite (sp_noacc _ _ _ _ _ SPo), (sp_lazy _ _ _ _ _ SPo). rewrite !covered_app.
      rewrite covered_maps_subtract by (try exact W2; rewrite Un; lia). rewrite Un. fold hi. fold lo.
      assert (HD : covered (if sl_nn s then [(addr, n)] else []) x = (sl_nn s && in_rng lo hi x)%bool).
      { destruct (sl_nn s); cbn [covered existsb]; [|reflexivity]. unfold in_iv, B, S. cbn [fst snd]. rewrite Un. fold lo hi. apply orb_false_r. }
      rewrite HD. f_equal.
      assert (SC : lo <= hi) by (unfold lo, hi; lia).
      destruct s; cbn [sl_nn]; rewrite ?covered_maps_subtract by first [exact W3 | exact SC]; try reflexivity.
      unfold covered at 1. cbn [existsb]. fold (covered (maps_subtract (m_vm_lazy model) lo hi) x).
      rewrite covered_maps_subtract by first [exact W3 | exact SC]. unfold in_iv, B, S. cbn [fst snd]. rewrite Un. reflexivity. }
    assert (CC : forall x, covered C x = (covered (vm_noaccess (m_vmmaps model)) x || covered (m_vm_lazy model) x)%bool).
    { intros x. subst C. apply covered_app. }
    assert (MONO : sum_count (fun x => negb (covered C' x)) (vm_maps (m_vmmaps model))
                   <= sum_count (fun x => (negb (covered C x) || (in_rng lo hi x && sl_charge s))%bool) (vm_maps (m_vmmaps model))).
    { apply sum_count_mono. intros x Hx. apply negb_true_iff in Hx. rewrite CEQ in Hx. rewrite CC.
      destruct s; cbn [sl_nn sl_charge] in Hx |- *;
        destruct (in_rng lo hi x), (covered (vm_noaccess (m_vmmaps model)) x), (covered (m_vm_lazy model) x); cbn in Hx |- *; congruence. }
    pose proof (sum_count_or_le (fun x => negb (covered C x)) (fun x => (in_rng lo hi x && sl_charge s)%bool) (vm_maps (m_vmmaps model))) as OR.
    assert (CH : sum_count (fun x => (in_rng lo hi x && sl_charge s)%bool) (vm_maps (m_vmmaps model)) <= (if sl_charge s then nZ else 0)).
    { destruct (sl_charge s).
      - rewrite (sum_count_ext _ (in_rng lo hi)) by (intros; apply andb_true_r).
        pose proof (overlap_sum_contained (vm_maps (m_vmmaps model)) (edenot E (am_base m)) (edenot E (am_len m)) lo hi
                      (co_seps _ _ _ _ _ _ _ _ _ _ _ _ HC) (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf)
                      ltac:(unfold lo; lia) ltac:(unfold hi; lia) ltac:(unfold lo, hi; lia)) as OV.
        unfold overlap_sum in OV. unfold lo, hi in *. lia.
      - rewrite (sum_count_ext _ (fun _ => false)) by (intros; apply andb_false_r).
        clear. induction (vm_maps (m_vmmaps model)) as [|q l IH]; cbn; [lia|]. unfold iv_count. rewrite zcount_const_false. lia. }
    cbv beta in OR. lia.
  Qed.

  #[using="SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SP0 RES_len' HULL_ok' E cs R FULL model s m addr n nZ model' FULL' SH HnZpos lo hi"] Lemma page_base_aligned : forall p : word, bv_unsigned p mod 4096 = 0 -> page_base p = p.
  Proof.
    intros p Hp. unfold page_base, page_base_of, page_size. apply bv_eq. pose proof (u64_range p).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite u64_lit; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)
  Definition sl_adds (s0 : slarm) : bool := match s0 with SlF | SlG => true | _ => false end.

  (* [comment removed for export] *)
  #[using="RES_len HULL_ok SHADOW_ok SP0_ok argH_high SINV_frame RES_len' HULL_ok' SHADOW_ok' ATOP_facts' R FULL model n SH HC Hm Hnf Un HnZpos HnZal Hal Hin1 Hin2 SPo SM HF HnF"] Lemma slice_cs1_ok : forall sr' R' k' p nx nhi sub',
    regs_ok E sr' R' ->
    know_ok SEGS E (MR E cs model' FULL') k' ->
    nZ <= nhi ->
    (sl_charge s = true -> a_eager cs + a_abytes cs + nhi <= LIMIT) ->
    (forall t, In t sub' ->
       (In t (a_sub cs) /\ (sl_adds s = true -> uE E (fst t) + uE E (snd t) <= lo \/ hi <= uE E (fst t)))
       \/ ((s = SlE \/ (s = SlM /\ am_kind m = KNONE)) /\ uE E (fst t) = lo /\ uE E (snd t) = nZ)) ->   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (forall t, In t (a_sub cs) -> In t sub') ->
    (s = SlE -> exists t, In t sub' /\ uE E (fst t) = lo /\ uE E (snd t) = nZ) ->
    (s = SlM -> ~ In (am_kind m) K_NLZ) ->
    CSOK E (ACS (mk_ss p sr' k' nx)
                (match s with SlF => a_maps cs | _ => rekind (a_maps cs) m end)
                (a_totsz cs) (a_ylo cs)
                (if sl_charge s then a_eager cs + nhi else a_eager cs)
                (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) sub') R' FULL' model'.
  Proof.
    intros sr' R' k' p nx nhi sub' Hregs Hknow Hnhi Hbudget Hsub' Hkeep HtokE HMnl.
    assert (Es : exists s0, s0 = s) by (exists s; reflexivity). destruct Es as [s0 Es].
    pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf. pose proof Hwf as (W1 & W2 & W3 & _).
    pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6). pose proof sl_bounds as (B1 & B2 & B3 & B4 & B5).
    pose proof sl_wf' as Hwf'. pose proof sl_eager as EG.
    pose proof (co_seps _ _ _ _ _ _ _ _ _ _ _ _ HC) as SEPS. pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) as MM.
    assert (DISJ := fun m' Hm' Hnf' Hne => maps_match_disjoint E (a_maps cs) _ m m' MM SEPS Hm Hm' Hnf Hnf' Hne).
    assert (DISJ' : forall m', In m' (a_maps cs) -> is_fog m' = false -> m <> m' ->
              bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) <= lo
              \/ hi <= bv_unsigned (edenot E (am_base m'))).
    { intros m' Hm' Hnf' Hne. pose proof (DISJ m' Hm' Hnf' Hne) as D. unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. unfold lo, hi. lia. }
    assert (KNF : forall m', am_kind m' = KNONE \/ am_kind m' = KNONELAZY \/ am_kind m' = KRWLAZY -> is_fog m' = false).
    { intros m' Hk. unfold is_fog. destruct Hk as [-> |[-> | ->]]; reflexivity. }
    (* [comment removed for export] *)
    assert (NONE : forall m', In m' (a_maps cs) -> m <> m' -> (am_kind m' = KNONE \/ am_kind m' = KNONELAZY) ->
              In (amap_den E m') (vm_noaccess (m_vmmaps model'))).
    { intros m' Hm' Hne Hk. rewrite (sp_noacc _ _ _ _ _ SPo). apply in_app_iff. right.
      assert (Hnf' : is_fog m' = false) by (apply KNF; tauto).
      pose proof (proj1 (Forall_forall _ _) (co_none _ _ _ _ _ _ _ _ _ _ _ _ HC) m' Hm' Hk) as X.
      pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HC) (amap_den E m')
                    (maps_match_In E _ _ m' MM Hm' Hnf')) as (Bm1 & _).
      unfold amap_den in *. apply maps_subtract_keeps; [rewrite Un; lia | exact Bm1 | exact X |].
      cbn [fst snd]. rewrite Un. pose proof (DISJ' m' Hm' Hnf' Hne). unfold lo, hi in *. lia. }
    (* [comment removed for export] *)
    assert (KINDS : forall m', In m' (a_maps cs) -> am_kind m' = KRWLAZY ->
              forall x : word, bv_unsigned (edenot E (am_base m')) <= bv_unsigned x < bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) ->
                in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model')) = false
                /\ page_in_ranges (page_base x) (m_vm_lazy model') = true).
    { intros m' Hm' Hk x Hx.
      destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ _ HC) m' Hm' Hk x Hx) as [K1 K2].
      destruct (Z_lt_le_dec (bv_unsigned x) lo) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) hi) as [Hlt2|Hge2]].
      - rewrite sl_noacc_out, sl_lazy_out by lia. auto.
      - (* [comment removed for export] *)
        assert (Hmm : m = m').
        { destruct (amap_eqb m m') eqn:He; [apply APS.amap_eqb_eq in He; exact He|]. exfalso.
          assert (Hne : m <> m') by (intros ->; rewrite amap_eqb_refl in He; discriminate).
          pose proof (DISJ' m' Hm' ltac:(apply KNF; tauto) Hne). lia. }
        subst m'. rewrite sl_noacc_in, sl_lazy_in by lia.
        destruct s0; rewrite <- Es; cbn [sl_nn]; auto; exfalso; refine (HnF _ Hk); rewrite <- Es; discriminate.
      - rewrite sl_noacc_out, sl_lazy_out by lia. auto. }
    match goal with |- CSOK _ ?c _ _ _ => set (cs1 := c) end.
    assert (HIDOUT : forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x -> HID E cs1 model' x = HID E cs model x).
    { intros x Hx. unfold hid. rewrite (sl_vis_out cs1 x eq_refl Hx). reflexivity. }
    assert (HALLOW : ALLOW E cs1 = ALLOW E cs) by reflexivity.
    (* [comment removed for export] *)
    assert (MIN : In (amap_den E m) (vm_maps (m_vmmaps model))) by exact (maps_match_In E _ _ m MM Hm Hnf).
    assert (DENm : zB (amap_den E m) <= lo /\ hi <= zE (amap_den E m)).
    { unfold zB, zE, amap_den. cbn [fst snd]. pose proof Hin1 as I1. pose proof Hin2 as I2. unfold lo, hi. lia. }
    assert (SAMEDEN : forall m1, In m1 (a_maps cs) -> is_fog m1 = false -> amap_den E m1 = amap_den E m -> m1 = m).
    { intros m1 Hm1 Hf1 Hd1. destruct (amap_eqb m m1) eqn:He; [apply APS.amap_eqb_eq in He; symmetry; exact He|]. exfalso.
      assert (Hne : m <> m1) by (intros ->; rewrite amap_eqb_refl in He; discriminate).
      pose proof (DISJ m1 Hm1 Hf1 Hne) as D. rewrite Hd1 in D. unfold iv_disjoint in D.
      pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HC) _ MIN) as (P0 & _). lia. }
    destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xisp Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xnk Xlzk Xsub Xdef Xnn Xcov].
    pose proof Xwf as (WFM & WFN & WFL & _).
    constructor; rewrite ?HALLOW; unfold cs1; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_sub kn s_regs s_log s_know s_next mk_ss]; fold cs1.
    - exact Hregs.
    - reflexivity.
    - unfold Mr. rewrite (hid_ext A SP0 argH E cs _ model') by reflexivity. exact Hknow.
    - rewrite (sp_halted _ _ _ _ _ SPo). exact Xhalt.
    - unfold fds_ok in *. rewrite (sp_fds _ _ _ _ _ SPo), (sp_fs _ _ _ _ _ SPo). exact Xfds.
    - rewrite (sp_fs _ _ _ _ _ SPo). exact Xfs.
    - rewrite (sp_tid _ _ _ _ _ SPo). exact Xtid.
    - rewrite (sp_res _ _ _ _ _ SPo). exact Xres.
    - rewrite (sp_limit _ _ _ _ _ SPo). exact Xlimit.
    - rewrite (sp_maps _ _ _ _ _ SPo).
      assert (RK : maps_match E (rekind (a_maps cs) m) (vm_maps (m_vmmaps model))).
      { unfold rekind. apply maps_match_rekind; [|exact Xmaps]. intros m0. destruct (amap_eqb m0 m) eqn:He; [|auto].
        apply APS.amap_eqb_eq in He. subst m0. cbn [am_base am_len]. split; [reflexivity|]. split; [reflexivity|].
        rewrite (is_fog_rekind m Hnf), Hnf. reflexivity. }
      destruct s0; rewrite <- Es; first [exact RK | exact Xmaps].
    - (* [comment removed for export] *)
      rewrite (sp_maps _ _ _ _ _ SPo), (sp_res _ _ _ _ _ SPo).
      assert (RKH : Forall (hole_ok E (a_ylo cs) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) (rekind (a_maps cs) m)).
      { unfold rekind. apply Forall_forall. intros m0 HinR Hh. apply in_map_iff in HinR as (m1 & <- & HinR1).
        destruct (amap_eqb m1 m) eqn:He.
        - exfalso. apply APS.amap_eqb_eq in He. subst m1. rewrite (is_hole_rekind m Hnf) in Hh. discriminate Hh.
        - exact (proj1 (Forall_forall _ _) Xholes m1 HinR1 Hh). }
      destruct s0; rewrite <- Es; first [exact RKH | exact Xholes].
    - rewrite (sp_maps _ _ _ _ _ SPo). exact Xseps.
    - exact Hwf'.
    - rewrite (sp_maps _ _ _ _ _ SPo). exact Xbounds.
    - (* [comment removed for export] *) rewrite (sp_lazy _ _ _ _ _ SPo).
      assert (SUB : Forall (fun iv : word * word => hull_apart A (bv_unsigned (fst iv)) (bv_unsigned (snd iv)) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ATOP)
                      (maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))).
      { apply Forall_forall. intros q Hq. destruct (maps_subtract_pieces _ _ _ q W3 Hq) as (r & Hr & R1 & R2 & _).
        pose proof (proj1 (Forall_forall _ _) Xlazyb r Hr) as [Y1 Y2]. unfold hull_apart in *. lia. }
      destruct s0; rewrite <- Es; try exact SUB; try exact Xlazyb. apply Forall_cons; [cbn [fst snd]; unfold hull_apart; unfold lo, hi in *; lia | exact SUB].
    - (* [comment removed for export] *) intros z Hz. rewrite (sp_maps _ _ _ _ _ SPo). rewrite (sp_noacc _ _ _ _ _ SPo), in_ivs_app in Hz.
      apply orb_prop in Hz as [Hz|Hz].
      + destruct (sl_nn s); [|discriminate]. rewrite in_ivs_cons in Hz. cbn [fst snd in_ivs existsb] in Hz. rewrite orb_false_r in Hz.
        apply andb_prop in Hz as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2.
        eapply in_ivs_maps_match; [exact Xmaps | exact Hm | exact Hnf |]. unfold lo, hi in *. lia.
      + apply Xnasub. rewrite in_ivs_covered in Hz |- *. rewrite covered_maps_subtract in Hz by (try exact W2; rewrite Un; lia).
        apply andb_prop in Hz as [Hz _]. exact Hz.
    - (* [comment removed for export] *) apply Forall_forall. intros m' Hm' Hk'. destruct s0; rewrite <- Es in Hm'.
      2: { apply NONE; [exact Hm' | | exact Hk']. intros <-. rewrite (HF (eq_sym Es)) in Hk'. destruct Hk'; discriminate. }
      all: destruct (in_rekind _ _ _ Hm') as (m0 & Hm0 & [[-> ->]|[Hne ->]]);
             [cbn [am_kind] in Hk'; exfalso; destruct Hk' as [Hk'|Hk']; [exact (proj1 (rekind_k_not_none _) Hk') | exact (proj1 (proj2 (rekind_k_not_none _)) Hk')]|];
           apply NONE; [exact Hm0 | congruence | exact Hk'].
    - (* [comment removed for export] *) apply Forall_forall. intros m' Hm' Hk'. destruct s0; rewrite <- Es in Hm'.
      2: { apply KINDS; assumption. }
      all: destruct (in_rekind _ _ _ Hm') as (m0 & Hm0 & [[-> ->]|[Hne ->]]); [cbn [am_kind] in Hk'; exfalso; exact (proj2 (proj2 (rekind_k_not_none _)) Hk')|];
           apply KINDS; assumption.
    - rewrite (sp_res _ _ _ _ _ SPo), (sp_maps _ _ _ _ _ SPo). exact Xtotsz.
    - rewrite (sp_isp _ _ _ _ _ SPo). exact Xisp.
    - rewrite (sp_brk _ _ _ _ _ SPo). exact Xbrk.
    - rewrite (sp_brk _ _ _ _ _ SPo), (sp_sbrk _ _ _ _ _ SPo). exact Xsbrk.
    - (* [comment removed for export] *) destruct (sl_charge s); lia.
    - exact Xabytes.
    - (* [comment removed for export] *) destruct Xminv as [N1 N2 N3 N4 N5].
      assert (MAT : forall q, In q (m_vm_materialized model') -> In q (m_vm_materialized model)
                      /\ (s <> SlM -> bv_unsigned q < lo \/ hi <= bv_unsigned q)).
      { intros q Hq. pose proof (sp_mat _ _ _ _ _ SPo) as SMAT. destruct s0; rewrite <- Es in SMAT; rewrite SMAT in Hq; try (split; [exact Hq | congruence]).
        all: apply filter_In in Hq as [Hq Ho]; split; [exact Hq|]; intros _;
             unfold page_outside_range in Ho; apply negb_true_iff in Ho; apply andb_false_iff in Ho as [Ho|Ho];
             [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; unfold lo, hi; rewrite <- ?Un; lia. }
      constructor; rewrite ?(sp_limit _ _ _ _ _ SPo).
      + pose proof (sp_mat _ _ _ _ _ SPo) as SMAT. destruct s0; rewrite <- Es in SMAT; rewrite SMAT; try apply NoDup_filter; exact N1.
      + intros q Hq. apply N2. apply MAT. exact Hq.
      + intros q Hq. apply N3. apply MAT. exact Hq.
      + intros q Hq. destruct (MAT q Hq) as [Hq0 Hout]. pose proof (N4 q Hq0) as L0.
        pose proof (sl_lazy_out q) as LO. pose proof (sp_lazy _ _ _ _ _ SPo) as SL.
        destruct s0; rewrite <- Es in SL, Hout; [| | | rewrite SL; exact L0].
        all: specialize (Hout ltac:(discriminate)); rewrite <- (page_base_aligned q (N2 q Hq0)); rewrite LO by exact Hout;
             rewrite page_base_aligned by exact (N2 q Hq0); exact L0.
      + destruct (sl_charge s); [specialize (Hbudget eq_refl)|]; rewrite Xlimit in *; lia.
    - (* [comment removed for export] *) intros x Hh Hmx Hna Hlz Hgh.
      destruct (Z_lt_le_dec (bv_unsigned x) lo) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) hi) as [Hlt2|Hge2]].
      + rewrite (proj1 SM x) by (unfold lo in *; lia). rewrite HIDOUT in Hh by lia. rewrite (sp_maps _ _ _ _ _ SPo) in Hmx.
        rewrite sl_noacc_out in Hna by lia. rewrite sl_lazy_out in Hlz by lia. exact (Xzero x Hh Hmx Hna Hlz Hgh).
      + rewrite sl_noacc_in in Hna by lia. rewrite (proj2 SM x) by (unfold lo, hi in *; rewrite Un; lia). rewrite Hna. reflexivity.
      + rewrite (proj1 SM x) by (unfold hi in *; rewrite Un; lia). rewrite HIDOUT in Hh by lia. rewrite (sp_maps _ _ _ _ _ SPo) in Hmx.
        rewrite sl_noacc_out in Hna by lia. rewrite sl_lazy_out in Hlz by lia. exact (Xzero x Hh Hmx Hna Hlz Hgh).
    - (* [comment removed for export] *) eapply SINV_frame; [| |exact Xsinv].
      + intros x Hx. apply (proj1 SM). pose proof (argH_high _ _ Hx). unfold hi in *. rewrite Un. lia.
      + (* [comment removed for export] *) intros x Hx Hd. rewrite (proj1 SM x); [exact Hd|]. unfold hi in *. rewrite Un. lia.
    - (* [comment removed for export] *)
      rewrite (sp_maps _ _ _ _ _ SPo). intros e He. rewrite (sp_noacc _ _ _ _ _ SPo) in He. apply in_app_iff in He as [He|He].
      + (* [comment removed for export] *)
        destruct s0; rewrite <- Es in He; cbn [sl_nn] in He; try (destruct He; fail); destruct He as [<-|[]].
        split; [cbn [snd]; rewrite Un; exact HnZpos|].
        exists (amap_den E m). split; [exact MIN|]. unfold zB, zE in *. cbn [fst snd]. rewrite Un. split; [lia|]. split; [unfold hi in *; lia|].
        rewrite <- Es. intros Hb. destruct (born_rekind E (a_maps cs) m K_NOTNONE _ KMIXED_notnone Hb) as (m1 & Hm1in & Hne1 & Hf1 & _ & Hd1).
        exact (Hne1 (SAMEDEN m1 Hm1in Hf1 Hd1)).
      + (* [comment removed for export] *)
        destruct (maps_subtract_pieces _ _ _ _ WFN He) as (e0 & He0 & Q1 & Q2 & Q3).
        destruct (Xnk e0 He0) as (P0 & iv & Hiv & C1 & C2 & NB). split; [exact (maps_subtract_pos _ _ _ _ WFN (fun e1 He1 => proj1 (Xnk e1 He1)) He)|].
        exists iv. split; [exact Hiv|]. unfold zB, zE in *. split; [lia|]. split; [lia|].
        intros Hb. apply NB. destruct s0; rewrite <- Es in Hb; first [exact Hb | exact (born_rekind_weaken E _ _ _ _ Hnf KMIXED_notnone_w Hb)].
    - (* [comment removed for export] *)
      rewrite (sp_maps _ _ _ _ _ SPo). intros e He. rewrite (sp_lazy _ _ _ _ _ SPo) in He.
      assert (PIECE : In e (maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) ->
                0 < bv_unsigned (snd e) /\ exists iv, In iv (vm_maps (m_vmmaps model)) /\ zB iv <= zB e /\ zE e <= zE iv
                                           /\ ~ born E (match s with SlF => a_maps cs | _ => rekind (a_maps cs) m end) K_EAGER iv).
      { intros Hp. destruct (maps_subtract_pieces _ _ _ _ WFL Hp) as (e0 & He0 & Q1 & Q2 & Q3).
        destruct (Xlzk e0 He0) as (P0 & iv & Hiv & C1 & C2 & NB). split; [exact (maps_subtract_pos _ _ _ _ WFL (fun e1 He1 => proj1 (Xlzk e1 He1)) Hp)|].
        exists iv. split; [exact Hiv|]. unfold zB, zE in *. split; [lia|]. split; [lia|].
        intros Hb. apply NB. destruct s0; rewrite <- Es in Hb; first [exact Hb | exact (born_rekind_weaken E _ _ _ _ Hnf KMIXED_eager Hb)]. }
      destruct s0; rewrite <- Es in He; cbn in He; try exact (PIECE He).
      + (* [comment removed for export] *)
        apply in_inv in He as [<-|He]; [|exact (PIECE He)].
        split; [cbn [snd]; rewrite Un; exact HnZpos|].
        exists (amap_den E m). split; [exact MIN|]. unfold zB, zE in *. cbn [fst snd]. rewrite Un. split; [lia|]. split; [unfold hi in *; lia|].
        intros (m1 & Hm1in & Hf1 & Hk1 & Hd1). rewrite <- Es in Hm1in. cbn in Hm1in. pose proof (SAMEDEN m1 Hm1in Hf1 Hd1) as ->.
        rewrite (sh_F _ _ _ _ _ _ _ _ _ _ _ _ SH (eq_sym Es)) in Hk1. unfold K_EAGER in Hk1. cbn in Hk1. destruct Hk1 as [Hk1|[Hk1|[Hk1|[]]]]; discriminate Hk1.   (* [comment removed for export] *)
      + (* [comment removed for export] *)
        destruct (Xlzk e He) as (P0 & iv & Hiv & C1 & C2 & NB). split; [exact P0|]. exists iv. split; [exact Hiv|]. split; [exact C1|]. split; [exact C2|].
        intros Hb. apply NB. rewrite <- Es in Hb. cbn in Hb. exact (born_rekind_weaken E _ _ _ _ Hnf KMIXED_eager Hb).
    - (* [comment removed for export] *)
      rewrite (sp_maps _ _ _ _ _ SPo). apply Forall_forall. intros t Ht.
      destruct (Hsub' t Ht) as [[Hold Hapart] | (EsE & T1 & T2)].
      + (* [comment removed for export] *)
        pose proof (proj1 (Forall_forall _ _) Xsub t Hold) as (S1 & S2 & S3 & S4). split; [exact S1|]. split; [exact S2|]. split.
        * intros e He. rewrite (sp_noacc _ _ _ _ _ SPo) in He. apply in_app_iff in He as [He|He].
          -- destruct s0; rewrite <- Es in He, Hapart; cbn [sl_nn sl_adds] in He, Hapart; try (destruct He; fail); destruct He as [<-|[]].
             unfold zB, zE. cbn [fst snd]. rewrite Un. specialize (Hapart eq_refl). unfold hi in Hapart. lia.
          -- destruct (maps_subtract_pieces _ _ _ _ WFN He) as (e0 & He0 & Q1 & Q2 & Q3). pose proof (S3 e0 He0). unfold zB, zE in *. lia.
        * intros e He. rewrite (sp_lazy _ _ _ _ _ SPo) in He.
          assert (PIECE : In e (maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) -> zE e <= uE E (fst t) \/ uE E (fst t) + uE E (snd t) <= zB e).
          { intros Hp. destruct (maps_subtract_pieces _ _ _ _ WFL Hp) as (e0 & He0 & Q1 & Q2 & Q3). pose proof (S4 e0 He0). unfold zB, zE in *. lia. }
          destruct s0; rewrite <- Es in He, Hapart; cbn [sl_adds] in Hapart; cbn in He; try exact (PIECE He); try exact (S4 e He).
          apply in_inv in He as [<-|He]; [|exact (PIECE He)]. unfold zB, zE. cbn [fst snd]. rewrite Un. specialize (Hapart eq_refl). unfold hi in Hapart. lia.
      + (* [comment removed for export] *)
        split; [rewrite T2; exact HnZpos|]. rewrite T1, T2. split.
        * exists (amap_den E m). split; [exact MIN|]. unfold hi in DENm. exact DENm.
        * split.
          -- intros e He. rewrite (sp_noacc _ _ _ _ _ SPo) in He.
             destruct EsE as [EsE|[EsE HkM]]; rewrite EsE in He; cbn [sl_nn app] in He;
               destruct (maps_subtract_pieces _ _ _ _ WFN He) as (e0 & He0 & Q1 & Q2 & Q3); unfold zB, zE, lo in *; rewrite Un in Q3; lia.
          -- intros e He. rewrite (sp_lazy _ _ _ _ _ SPo) in He. destruct EsE as [EsE|[EsE HkM]]; rewrite EsE in He.
             ++ destruct (maps_subtract_pieces _ _ _ _ WFL He) as (e0 & He0 & Q1 & Q2 & Q3). unfold zB, zE, lo in *. rewrite Un in Q3. lia.
             ++ pose proof (APS.eager_range_lz_clear SEGS A LIMIT SP0 SINV argH FS0 E cs R FULL model m lo hi HC Hm Hnf
                              ltac:(rewrite HkM; cbn; tauto) (proj1 DENm) (proj2 DENm) e He) as D.
                pose proof (proj1 (APS.co_lzk _ _ _ _ _ _ _ _ _ _ _ _ HC e He)) as Pe. unfold hi, lo, zB, zE in *. rewrite ?Un in *. lia.
    - (* [comment removed for export] *)
      apply Forall_forall. intros m' Hm' Hf' Hk' x Hx.
      assert (OLD : exists m1, In m1 (a_maps cs) /\ am_base m1 = am_base m' /\ am_len m1 = am_len m' /\ is_fog m1 = false /\ In (am_kind m1) K_DEF
                           /\ (m1 <> m \/ s = SlF)).
      { destruct s0; rewrite <- Es in Hm' |- *;
          [ change (In m' (rekind (a_maps cs) m)) in Hm'
          | change (In m' (a_maps cs)) in Hm'; exists m'; split; [exact Hm'|]; split; [reflexivity|]; split; [reflexivity|];
            split; [exact Hf'|]; split; [exact Hk'|]; right; reflexivity
          | change (In m' (rekind (a_maps cs) m)) in Hm'
          | change (In m' (rekind (a_maps cs) m)) in Hm' ].
        all: destruct (in_rekind _ _ _ Hm') as (m0 & Hin0 & [[-> ->]|[Hne ->]]);
          [ exfalso; cbn [am_kind] in Hk'; exact (rekind_k_not_def _ Hk')
          | exists m0; split; [exact Hin0|]; split; [reflexivity|]; split; [reflexivity|]; split; [exact Hf'|]; split; [exact Hk'|]; left; exact Hne ]. }
      destruct OLD as (m1 & Hm1 & Eb & El & Hf1 & Hk1 & Hsel). rewrite <- Eb, <- El in Hx.
      destruct (Z_lt_le_dec (bv_unsigned x) lo) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) hi) as [Hlt2|Hge2]].
      + rewrite (proj1 SM x) by (rewrite Un; unfold lo, hi in *; lia). exact (proj1 (Forall_forall _ _) Xdef m1 Hm1 Hf1 Hk1 x Hx).
      + rewrite (proj2 SM x) by (rewrite Un; unfold lo, hi in *; lia).
        destruct s0; rewrite <- Es; cbn [sl_nn]; try discriminate.
        (* [comment removed for export] *) exfalso. destruct Hsel as [Hne|Hs]; [|rewrite <- Es in Hs; discriminate Hs].
        pose proof (DISJ' m1 Hm1 Hf1 (fun HH => Hne (eq_sym HH))) as D. unfold lo, hi in *. lia.
      + rewrite (proj1 SM x) by (rewrite Un; unfold lo, hi in *; lia). exact (proj1 (Forall_forall _ _) Xdef m1 Hm1 Hf1 Hk1 x Hx).
    - (* [comment removed for export] *)
      intros x Hx.
      destruct (Z_lt_le_dec (bv_unsigned x) lo) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) hi) as [Hlt2|Hge2]].
      + rewrite sl_noacc_out in Hx by lia. rewrite (proj1 SM x) by (rewrite Un; unfold lo, hi in *; lia). exact (Xnn x Hx).
      + rewrite sl_noacc_in in Hx by lia. rewrite (proj2 SM x) by (rewrite Un; unfold lo, hi in *; lia). rewrite Hx. reflexivity.
      + rewrite sl_noacc_out in Hx by lia. rewrite (proj1 SM x) by (rewrite Un; unfold lo, hi in *; lia). exact (Xnn x Hx).
    - (* [comment removed for export] *)
      assert (OUTN : forall z, 0 <= z < 2 ^ 64 -> z < lo \/ hi <= z -> in_ivs z (vm_noaccess (m_vmmaps model)) = true ->
                in_ivs z (vm_noaccess (m_vmmaps model')) = true).
      { intros z Rz Hz Hn. pose proof (sl_noacc_out (Z_to_bv 64 z)) as X. rewrite u64_lit in X by lia. rewrite (X Hz). exact Hn. }
      assert (OLDCOV : forall m1, In m1 (a_maps cs) -> In (am_kind m1) K_NLZ ->
                forall z, uE E (am_base m1) <= z < uE E (am_base m1) + uE E (am_len m1) -> z < lo \/ hi <= z ->
                in_ivs z (vm_noaccess (m_vmmaps model')) = true \/ exists t, In t sub' /\ APS.in_tok E z t).
      { intros m1 Hm1 Hk1 z Hz Hout.
        assert (Rz : 0 <= z < 2 ^ 64).
        { unfold uE in Hz. pose proof (u64_range (edenot E (am_base m1))). pose proof (u64_range (edenot E (am_len m1))).
          assert (Hf1 : is_fog m1 = false) by (unfold is_fog; destruct Hk1 as [<-|[<-|[]]]; reflexivity).
          pose proof (proj1 (Forall_forall _ _) Xbounds _ (maps_match_In E _ _ m1 Xmaps Hm1 Hf1)) as (_ & _ & _ & _ & HT & _).
          unfold amap_den in HT. cbn [fst snd] in HT. atopb. unfold APS.ATOP in *. lia. }
        destruct (proj1 (Forall_forall _ _) Xcov m1 Hm1 Hk1 z Hz) as [Hn|(t & Ht & Hzt)];
          [left; exact (OUTN z Rz Hout Hn) | right; exists t; split; [exact (Hkeep t Ht) | exact Hzt]]. }
      assert (MCOV : In (am_kind m) K_NLZ -> s <> SlF ->
                forall z, uE E (am_base m) <= z < uE E (am_base m) + uE E (am_len m) ->
                in_ivs z (vm_noaccess (m_vmmaps model')) = true \/ exists t, In t sub' /\ APS.in_tok E z t).
      { intros Hkm HsF z Hz.
        destruct (Z_lt_le_dec z lo) as [Hlt|Hge]; [|destruct (Z_lt_le_dec z hi) as [Hlt2|Hge2]].
        - exact (OLDCOV m Hm Hkm z Hz ltac:(lia)).
        - (* [comment removed for export] *)
          destruct s0.
          + (* [comment removed for export] *) right. destruct (HtokE (eq_sym Es)) as (t & Ht & T1 & T2). exists t. split; [exact Ht|]. unfold APS.in_tok. rewrite T1, T2. unfold hi in *. lia.
          + exfalso. exact (HsF (eq_sym Es)).
          + (* [comment removed for export] *) left. pose proof (sl_noacc_in (Z_to_bv 64 z)) as X. rewrite u64_lit in X by (unfold lo in *; pose proof (u64_range addr); lia).
            rewrite (X ltac:(lia)). rewrite <- Es. reflexivity.
          + (* [comment removed for export] *) exfalso. exact (HMnl (eq_sym Es) Hkm).
        - exact (OLDCOV m Hm Hkm z Hz ltac:(lia)). }
      apply Forall_forall. intros m' Hm' Hk' z Hz.
      assert (CASES : (In m' (a_maps cs) /\ m' <> m) \/ (In m' (a_maps cs) /\ s = SlF)
                      \/ (s <> SlF /\ m' = AM (am_base m) (am_len m) (rekind_k (am_kind m)))).
      { destruct s0; rewrite <- Es in Hm' |- *;
          [ change (In m' (rekind (a_maps cs) m)) in Hm'
          | right; left; split; [exact Hm' | reflexivity]
          | change (In m' (rekind (a_maps cs) m)) in Hm'
          | change (In m' (rekind (a_maps cs) m)) in Hm' ].
        all: destruct (in_rekind _ _ _ Hm') as (m0 & Hin0 & [[-> ->]|[Hne ->]]);
          [ right; right; split; [discriminate | reflexivity] | left; split; [exact Hin0 | exact Hne] ]. }
      destruct CASES as [[Hin Hne]|[[Hin HsF]|[HsF ->]]].
      + (* [comment removed for export] *)
        assert (Hf' : is_fog m' = false) by (unfold is_fog; destruct Hk' as [<-|[<-|[]]]; reflexivity).
        pose proof (DISJ' m' Hin Hf' (fun HH => Hne (eq_sym HH))) as D. unfold uE in Hz. exact (OLDCOV m' Hin Hk' z Hz ltac:(lia)).
      + (* [comment removed for export] *)
        destruct (amap_eqb m m') eqn:He.
        * apply APS.amap_eqb_eq in He. subst m'. exfalso. rewrite (HF HsF) in Hk'. destruct Hk' as [X|[X|[]]]; discriminate X.
        * assert (Hne : m <> m') by (intros ->; rewrite amap_eqb_refl in He; discriminate).
          assert (Hf' : is_fog m' = false) by (unfold is_fog; destruct Hk' as [<-|[<-|[]]]; reflexivity).
          pose proof (DISJ' m' Hin Hf' Hne) as D. unfold uE in Hz. exact (OLDCOV m' Hin Hk' z Hz ltac:(lia)).
      + (* [comment removed for export] *)
        cbn [am_base am_len am_kind] in Hk', Hz.
        assert (Hkm : In (am_kind m) K_NLZ).
        { pose proof (HnF HsF) as Hnl. revert Hk' Hnl. generalize (am_kind m). intros k0 Hk0 Hnl.
          destruct k0; cbn in Hk0 |- *; try (destruct Hk0 as [X|[X|[]]]; discriminate X); try (left; reflexivity); try (right; left; reflexivity).
          exfalso. exact (Hnl eq_refl). }
        exact (MCOV Hkm HsF z Hz).
  Qed.

End Slice.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="RES_len HULL_ok RES_len' HULL_ok' kentry_keep_sem' kentry_apart_b_sem' kimg_clip_in_hull'"] Lemma kn_unfill_clip_ok : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.PM,P,(2.&40.)(3<.(2.&8.))PM',Px,(2.&40.)(3<.(2.&8.))Pk,(=.$9?.)Pb,$4:.Poff,$<.Pne,$4:.P,(;?.VSEGS,R7.R6.R4.)P,(9>.VA,(<1.R8.(<2.R4.R3.))(<3.R8.R2.))P,Px,(2.&40.)P,(35.(1:.(6.&40.R1.)(<1.R:.(<2.R6.R5.)))(4.(8.(<1.R:.(<2.R6.R5.))(<3.R:.R4.))(6.&40.R1.)))(>.(3<.(2.&8.))A1.R9.R2.A1.R:.R2.)(;?.VSEGS,R:.R8.(113.VA,(114.R7.R6.R5.R4.)))")
(* [comment removed for export] *).
Proof.
  intros E M M' k b off ne HK Hhull Hout.
  pose proof (kimg_clip_in_hull' (kn_unfill k b off ne)) as Hh.
  unfold know_ok. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) Hh K Hin) as HKh.
  apply kimg_clip_incl in Hin. unfold kn_unfill in Hin. apply filter_In in Hin as [Hin Hkeep].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  eapply kentry_keep_sem'; [exact HKK | | exact Hout].
  apply orb_prop in Hkeep as [Himg|Hap].
  - destruct K; try discriminate. unfold kfoot_apart, kfoot. unfold hull_apart in Hhull. cbn in HKh. lia.
  - rewrite APS.kentry_apart_bp_eq in Hap. eapply kentry_apart_b_sem'; [exact HK | exact Hap].
Qed.

(* [comment removed for export] *)
#[using="RES_len HULL_ok RES_len' HULL_ok' kentry_keep_sem' kentry_apart_b_sem'"] Lemma kn_rezero_ok_gen : forall E M M' k b off ne,
  know_ok SEGS E M k ->
  hull_apart A (estart E (SA b off)) (elenZ E ne) ->      (* [comment removed for export] *)
  (forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x -> M' x = M x) ->
  (forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E ne -> M x <> None -> M' x = Some (Z_to_bv 8 0)) ->
  forall K, In K (kn_rezero k b off ne) ->
    match K with KImg lo hi => img_lo A <= lo /\ hi <= img_hi A | _ => True end ->
    kentry_ok SEGS E M' K.
Proof.
  intros E M M' k b off ne HK Hhull Hout Hin0 K Hin HKh.
  assert (DEF : forall x : word, M x <> None -> M' x <> None).
  { intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off))); [rewrite Hout by lia; exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off) + elenZ E ne)); [rewrite (Hin0 x ltac:(lia) Hx); discriminate | rewrite Hout by lia; exact Hx]. }
  assert (ZERO : forall x : word, M x = Some (Z_to_bv 8 0) -> M' x = Some (Z_to_bv 8 0)).
  { intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off))); [rewrite Hout by lia; exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off) + elenZ E ne)); [apply Hin0; [lia | rewrite Hx; discriminate] | rewrite Hout by lia; exact Hx]. }
  unfold kn_rezero in Hin. apply filter_In in Hin as [Hin Hkeep].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct K as [[kb kk] w v|[kb kk] l|[kb kk] l bk|ilo ihi|e mm|e rlo rhi|[kb kk] l|a1 n1 a2 n2|[kb kk] l fc|[kb kk] l];
    try (rewrite APS.kentry_apart_bp_eq in Hkeep; eapply kentry_keep_sem'; [exact HKK | eapply kentry_apart_b_sem'; [exact HK | exact Hkeep] | exact Hout]).
  - (* [comment removed for export] *) cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. apply ZERO. apply Hz. exact Hi.
  - (* [comment removed for export] *) eapply kentry_keep_sem'; [exact HKK | | exact Hout]. unfold kfoot_apart, kfoot. unfold hull_apart in Hhull. lia.
  - exact HKK.
  - exact HKK.
  - (* [comment removed for export] *) cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hs]. split; [exact Hfl|]. intros d mm Hd Hdm. eapply store_ok_mono; [exact DEF | apply Hs; assumption].
  - exact HKK.
  - (* [comment removed for export] *) cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. apply DEF. apply Hz. exact Hi.
Qed.

#[using="RES_len HULL_ok RES_len' HULL_ok' kentry_keep_sem' kentry_apart_b_sem' kimg_clip_in_hull'"] Lemma kn_rezero_clip_ok : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.PM,P,(2.&40.)(3<.(2.&8.))PM',Px,(2.&40.)(3<.(2.&8.))Pk,(=.$9?.)Pb,$4:.Poff,$<.Pne,$4:.P,(;?.VSEGS,R7.R6.R4.)P,(9>.VA,(<1.R8.(<2.R4.R3.))(<3.R8.R2.))P,Px,(2.&40.)P,(35.(1:.(6.&40.R1.)(<1.R:.(<2.R6.R5.)))(4.(8.(<1.R:.(<2.R6.R5.))(<3.R:.R4.))(6.&40.R1.)))(>.(3<.(2.&8.))A1.R9.R2.A1.R:.R2.)P,Px,(2.&40.)P,(3.(4.(<1.R;.(<2.R7.R6.))(6.&40.R1.))(1:.(6.&40.R1.)(8.(<1.R;.(<2.R7.R6.))(<3.R;.R5.))))P,(1<.(>.(3<.(2.&8.))A1.R;.R2.(41.(2.&8.))))(>.(3<.(2.&8.))A1.R;.R3.(3>.(2.&8.)(3?.&8.=)))(;?.VSEGS,R;.R9.(113.VA,(115.R8.R7.R6.R5.)))")
(* [comment removed for export] *).
Proof.
  intros E M M' k b off ne HK Hhull Hout Hin0. pose proof (kimg_clip_in_hull' (kn_rezero k b off ne)) as Hh.
  unfold know_ok. apply Forall_forall. intros K Hin. pose proof (proj1 (Forall_forall _ _) Hh K Hin) as HKh.
  apply kimg_clip_incl in Hin. apply (kn_rezero_ok_gen E M M' k b off ne HK Hhull Hout Hin0 K Hin). destruct K; try exact I. exact HKh.
Qed.

#[using="RES_len HULL_ok RES_len' HULL_ok' kentry_keep_sem' kentry_apart_b_sem'"] Lemma kn_rezero_hull_ok : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.PM,P,(2.&40.)(3<.(2.&8.))PM',Px,(2.&40.)(3<.(2.&8.))Pk,(=.$9?.)Pb,$4:.Poff,$<.Pne,$4:.P,(;?.VSEGS,R7.R6.R4.)P,(>=.VA,R5.)P,(9>.VA,(<1.R9.(<2.R5.R4.))(<3.R9.R3.))P,Px,(2.&40.)P,(35.(1:.(6.&40.R1.)(<1.R;.(<2.R7.R6.)))(4.(8.(<1.R;.(<2.R7.R6.))(<3.R;.R5.))(6.&40.R1.)))(>.(3<.(2.&8.))A1.R:.R2.A1.R;.R2.)P,Px,(2.&40.)P,(3.(4.(<1.R<.(<2.R8.R7.))(6.&40.R1.))(1:.(6.&40.R1.)(8.(<1.R<.(<2.R8.R7.))(<3.R<.R6.))))P,(1<.(>.(3<.(2.&8.))A1.R<.R2.(41.(2.&8.))))(>.(3<.(2.&8.))A1.R<.R3.(3>.(2.&8.)(3?.&8.=)))(;?.VSEGS,R<.R:.(115.R9.R8.R7.R6.))")
(* [comment removed for export] *).
Proof.
  intros E M M' k b off ne HK Hh Hhull Hout Hin0.
  unfold know_ok. apply Forall_forall. intros K Hin.
  assert (Hin' : In K k) by (unfold kn_rezero in Hin; apply filter_In in Hin as [Hin _]; exact Hin).
  pose proof (proj1 (Forall_forall _ _) Hh K Hin') as HKh.
  apply (kn_rezero_ok_gen E M M' k b off ne HK Hhull Hout Hin0 K Hin). destruct K; try exact I. exact HKh.
Qed.

#[using="HULL_ok SHADOW_ok SP0 SP0_ok HULL_ok' SHADOW_ok' ATOP_facts'"] Lemma kimg_in_hull_cons2 : forall K1 K2 k,
  match K1 with KImg _ _ => False | _ => True end -> match K2 with KImg _ _ => False | _ => True end ->
  kimg_in_hull A k -> kimg_in_hull A (K1 :: K2 :: k).
Proof.
  intros K1 K2 k H1 H2 Hk. unfold kimg_in_hull in *. constructor; [destruct K1; tauto|]. constructor; [destruct K2; tauto | exact Hk].
Qed.

(* [comment removed for export] *)
#[using="SEGS_in_hull RES_len HULL_ok SHADOW_ok SP0_ok argH_high HS XN XE XB RES_len' HULL_ok' vis_add_sound' know_ok_unhide' hid_hull' H_off_segments_cs' ATOP_facts'"] Lemma vis_add_slice_ok : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pcs1,$43.Pcs2,$43.Pea,$4:.Pb,$4:.Poff,$<.Pne,$4:.PR,(5;.&5.(2.&40.))PFULL',P,(2.&40.)(3<.(2.&8.))Pmodel',$21.Plo,$<.PnZ,$<.P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R<.R;.R5.R4.R3.)P,(>.(3<.$43.)(:0.VA,VLIMIT,R<.R:.R7.(11.$9?.(>;.(<2.R9.R8.)R7.)(11.$9?.(><.(<2.R9.R8.)R7.)(:2.R<.))))(3>.$43.R;.))P,(>=.VA,(:2.R=.))P,(>.$<.(;<.R?.R<.)R5.)P,(>.$<.(<1.R10.(<2.R<.R;.))R6.)P,(>.$<.(<3.R11.R;.)R6.)P,(4.=R8.)P,(1:.=R8.)P,(4.(8.R:.R9.)(<6.VSP0,))P,Px,(2.&40.)P,(3.(4.R<.(6.&40.R1.))(1:.(6.&40.R1.)(8.R<.R;.)))(3.(>.$?.(10.(6.&40.R2.)(2:.(28.R>.)))$17.)(3.(>.$?.(10.(6.&40.R2.)(27.(28.R>.)))$1;.)(3.(>.$?.A2.VargH,R17.R2.$1;.)(>.(3<.(2.&8.))A1.R?.R2.(3>.(2.&8.)(3?.&8.=))))))(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R16.R14.R?.R>.R=.)")
(* [comment removed for export] *).
Proof.
  intros E cs1 cs2 ea b off ne R FULL' model' lo nZ HC1 Hva Hkh Hea Hest Hne Hlo HnZ Hhi NEW.
  atopb. unfold APS.ATOP in Hhi.
  eapply vis_add_sound'; [exact Hva | exact HC1 |].
  destruct (vis_add_inv cs1 ea ne _ cs2 Hva) as (nhi & Hnhi & Ecs2).
  assert (BYTE : forall x : word, lo <= bv_unsigned x < lo + nZ -> MR E cs2 model' FULL' x = Some (Z_to_bv 8 0)).
  { intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3 & N4).
    unfold Mr, mrestrict, hid. rewrite N3. cbn [orb]. unfold vis. rewrite N1, N2. cbn [negb andb].
    assert (Hal : in_allow A E cs2 (bv_unsigned x) = true).
    { unfold in_allow, in_vis. rewrite Ecs2. cbn [a_vis existsb fst snd]. rewrite Hea. unfold uE. fold (elenZ E ne). rewrite Hne.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    rewrite Hal, !orb_true_r. cbn [negb]. exact N4. }
  assert (Hfl : flat E (SA b off) (elenZ E ne)) by (unfold flat; rewrite Hest, Hne; unfold CEIL in Hhi; lia).
  constructor; [|constructor].
  - cbn [kentry_ok]. split; [exact Hfl|]. rewrite Hest, Hne. intros d w' Hd Hdw. destruct w' as [|w'']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by (unfold CEIL in Hhi; lia); unfold CEIL in Hhi; lia|].
    intros x Hx. rewrite u64_lit in Hx by (unfold CEIL in Hhi; lia). unfold wview. rewrite (BYTE x) by lia. discriminate.
  - cbn [kentry_ok]. split; [exact Hfl|]. rewrite Hest, Hne. intros i Hi. apply BYTE. rewrite u64_lit by (unfold CEIL in Hhi; lia). lia.
  - pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
    eapply know_ok_unhide'; [apply H_off_segments_cs' | exact Hkh | | | exact HK1].
    + intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
    + intros y Hy. apply hid_hull'. exact Hy.
Qed.

(* [comment removed for export] *)
#[using="A RES_len RES_len'"] Lemma find_containing_sound : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.PM,P,(2.&40.)(3<.(2.&8.))Pk,(=.$9?.)Pms,(=.$8>.)Pkinds,(=.$;5.)Pb,$4:.Poff,$<.Pne,$4:.Pm,$8>.P,(;?.VSEGS,R9.R8.R7.)P,(>.(3<.$8>.)(116.R8.R7.R6.R5.R4.R3.)(3>.$8>.R2.))(3.(19.$8>.R3.R8.)(3.(3.(19.$;5.(10<.R3.)R7.)(>.$?.(95.R3.)$1;.))(3.(4.(6.&40.(98.R;.(99.R3.)))(<1.R;.(<2.R6.R5.)))(4.(8.(<1.R;.(<2.R6.R5.))(<3.R;.R4.))(8.(6.&40.(98.R;.(99.R3.)))(6.&40.(98.R;.(9:.R3.))))))))")
(* [comment removed for export] *).
Proof.
  intros E M k ms kinds b off ne m HK Hf. unfold find_containing in Hf. apply find_some in Hf as [Hin Hb].
  apply andb_prop in Hb as [Hk Hins]. apply andb_prop in Hk as [Hnf Hk]. apply negb_true_iff in Hnf.
  apply existsb_exists in Hk as (k0 & Hk0 & Hkk). apply APS.mkind_eqb_eq in Hkk. subst k0.
  pose proof (xinside_sound SEGS E M k b off ne (am_base m) 0 (am_len m) HK Hins) as [I1 I2].
  unfold estart in I1, I2 |- *. cbn [a_base a_off] in *. unfold elenZ in *. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
#[using="RES_len RES_hull HULL_ok SP0_ok RES_len' HULL_ok' RES_hullH reg_sound' reg_lit_sound' ATOP_facts'"] Lemma slice_args : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "PE,$94.Pcs,$43.PR,(5;.&5.(2.&40.))PFULL,P,(2.&40.)(3<.(2.&8.))Pmodel,$21.Pb,$4:.Poff,$<.Pne,$4:.Pnlo,$<.Pnhi,$<.Pkinds,(=.$;5.)Pm,$8>.P,(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R<.R;.R:.R9.R8.)P,(>.(3<.(1.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.))(?>.R<.)(3>.(1.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.)(1?.(1.(1.(1.$4:.$<.)$4:.)$<.)$<.(1?.(1.(1.$4:.$<.)$4:.)$<.(1?.(1.$4:.$<.)$4:.(1?.$4:.$<.R8.R7.)R6.)R5.)R4.)))P,(>.(3<.$8>.)(116.(:2.R=.)(:8.R=.)R4.R9.R8.R7.)(3>.$8>.R3.))Zaddr,(2.&40.)(98.R?.(9=.R>.#:.))Zlen,$<.(6.&40.(98.R10.(9=.R?.#;.)))ZnZ,$<.(7<.R1.)Zn,(2.&40.)(3?.&40.R1.)(3.(19.$8>.R8.(:8.R12.))(3.(3.(19.$;5.(10<.R8.)R9.)(>.$?.(95.R8.)$1;.))(3.(>.(2.&40.)(65.R11.(3?.&5.(2>.#:.)))R4.)(3.(>.(2.&40.)(65.R11.(3?.&5.(2>.#;.)))(3?.&40.R3.))(3.(3.(1:.=R3.)(1:.R3.(48.+2.+40.)))(3.(>.(2.&40.)(98.R13.R<.)R1.)(3.(>.$<.(6.&40.R1.)R2.)(3.(1:.=R2.)(3.(4.R2.R:.)(3.(>.$<.(3;.R2.+1000.)=)(3.(>.$<.(3;.(6.&40.R4.)+1000.)=)(3.(1:.=(6.&40.R4.))(3.(9>.VA,(6.&40.R4.)R2.)(3.(>.$<.(<1.R13.(<2.R>.R=.))(6.&40.R4.))(3.(4.(6.&40.(98.R13.(99.R8.)))(6.&40.R4.))(3.(4.(8.(6.&40.R4.)R2.)(8.(6.&40.(98.R13.(99.R8.)))(6.&40.(98.R13.(9:.R8.)))))(3.(4.(8.(6.&40.(98.R13.(99.R8.)))(6.&40.(98.R13.(9:.R8.))))(<6.VSP0,))(3.(>.$?.(20.(2:.(28.R?.))R4.R1.)$17.)(3.(>.$?.(1=.(8;.(28.R?.))R4.R1.)$17.)(4.(109.(2:.(28.R?.))(6.&40.R4.)(8.(6.&40.R4.)(6.&40.R1.)))R2.))))))))))))))))))))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model b off ne nlo nhi kinds m HC HFA Hf addr len nZ n.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (fixed_args_in_sound E cs R FULL model b off ne nlo nhi HC HFA) as (Hsp & HML & Hal & Hpos & Hnhi & R10 & _).
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & _).
  fold addr in Hal, Hpos, R10. fold len in R11, Hlen, Hne, HnZ, HnZal. fold nZ in Hne, HnZ, HnZal. fold n in Hne. unfold ATOPMAX in Hnhi.
  destruct (find_containing_sound E _ (kn cs) (a_maps cs) kinds b off ne m HK Hf) as (Hm & [Hkind Hnf] & I1 & I2).
  pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HC) as HB. atopb.
  pose proof (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf) as HIN.
  pose proof (proj1 (Forall_forall _ _) HB (amap_den E m) HIN) as (B1 & B2 & B3 & B4 & B5 & B6). cbn [amap_den fst snd] in B1, B2, B3, B4, B5, B6.
  unfold hull_apart in B4.
  pose proof (u64_range (edenot E (am_base m))) as Rb.
  assert (Hest : bv_unsigned addr = estart E (SA b off)).
  { unfold addr. apply (APS.u_of_split E (reg cs 10) b off Hsp). unfold elenZ in I2. pose proof (u64_range (edenot E ne)). lia. }
  unfold elenZ in I2. rewrite Hne in I2.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. fold nZ in PB. unfold page_size in PB.
  assert (Un : bv_unsigned n = nZ).
  { unfold n. apply u64_lit. pose proof (u64_range (Z_to_bv 64 nZ)). fold n in H. lia. }
  rewrite Un in I2.
  assert (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = true).
  { eapply map_contains_intro; [exact HIN | lia | rewrite Un; lia]. }
  assert (Hha : hull_apart A (bv_unsigned addr) nZ) by (unfold hull_apart; lia).
  split; [exact Hm|]. split; [split; [exact Hkind | exact Hnf]|].
  repeat (split; [first [assumption | lia | symmetry; assumption] |]).
  split; [apply reserved_free_apart; [exact (co_res _ _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Un; exact Hha] |].
  rewrite Un. pose proof (overlap_sum_contained (vm_maps (m_vmmaps model)) (edenot E (am_base m)) (edenot E (am_len m)) (bv_unsigned addr) (bv_unsigned addr + nZ)
    (co_seps _ _ _ _ _ _ _ _ _ _ _ _ HC) HIN ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="SEGS A RES_len HULL_ok RES_len' HULL_ok'"] Lemma iv_subtract_cover : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pa,(2.&40.)Psz,(2.&40.)Plo,$<.Phi,$<.Px1,$<.Px2,$<.P,(33.(1?.(2.&40.)(2.&40.)R6.R5.))P,(4.(6.&40.R7.)R3.)P,(1:.R4.R3.)P,(4.R4.(8.(6.&40.R9.)(6.&40.R8.)))P,(35.(4.R5.R8.)(4.R7.R6.))(18.(1.(2.&40.)(2.&40.))Lq,(1.(2.&40.)(2.&40.))(3.(19.(1.(2.&40.)(2.&40.))R1.(34.R<.R;.R:.R9.))(3.(4.(6.&40.(7.(2.&40.)(2.&40.)R1.))R8.)(4.R7.(8.(6.&40.(7.(2.&40.)(2.&40.)R1.))(6.&40.(9.(2.&40.)(2.&40.)R1.)))))))")
(* [comment removed for export] *).
Proof.
  intros a sz lo hi x1 x2 Hwf H1 H12 H2 Hout. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. unfold iv_subtract.
  destruct Hout as [Hl|Hr].
  - exists (a, Z_to_bv 64 (Z.min (bv_unsigned sz) (lo - bv_unsigned a))). split.
    + apply in_app_iff. left. rewrite (proj2 (Z.ltb_lt _ _)) by lia. left. reflexivity.
    + cbn [fst snd]. rewrite u64_lit by lia. lia.
  - exists (Z_to_bv 64 (Z.max (bv_unsigned a) hi), Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)). split.
    + apply in_app_iff. right. rewrite (proj2 (Z.ltb_lt _ _)) by lia. left. reflexivity.
    + cbn [fst snd]. rewrite !u64_lit by lia. lia.
Qed.

#[using="SEGS A RES_len HULL_ok RES_len' HULL_ok'"] Lemma maps_subtract_cover : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pl,(=.(1.(2.&40.)(2.&40.)))Plo,$<.Phi,$<.Piv,(1.(2.&40.)(2.&40.))Px1,$<.Px2,$<.P,(36.R6.)P,(19.(1.(2.&40.)(2.&40.))R4.R7.)P,(4.(6.&40.(7.(2.&40.)(2.&40.)R5.))R4.)P,(1:.R5.R4.)P,(4.R5.(8.(6.&40.(7.(2.&40.)(2.&40.)R7.))(6.&40.(9.(2.&40.)(2.&40.)R7.))))P,(35.(4.R6.R:.)(4.R9.R7.))(18.(1.(2.&40.)(2.&40.))Lq,(1.(2.&40.)(2.&40.))(3.(19.(1.(2.&40.)(2.&40.))R1.(37.R=.R<.R;.))(3.(4.(6.&40.(7.(2.&40.)(2.&40.)R1.))R9.)(4.R8.(8.(6.&40.(7.(2.&40.)(2.&40.)R1.))(6.&40.(9.(2.&40.)(2.&40.)R1.)))))))")
(* [comment removed for export] *).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi iv x1 x2 Hwf Hin H1 H12 H2 Hout; [destruct Hin|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract]. destruct Hin as [<-|Hin].
  - cbn [fst snd] in H1, H2. destruct (iv_subtract_cover a sz lo hi x1 x2 Ha H1 H12 H2 Hout) as (q & Hq & Q1 & Q2).
    exists q. split; [apply in_app_iff; left; exact Hq | split; assumption].
  - destruct (IH lo hi iv x1 x2 Hl Hin H1 H12 H2 Hout) as (q & Hq & Q1 & Q2).
    exists q. split; [apply in_app_iff; right; exact Hq | split; assumption].
Qed.

#[using="Type"] Lemma iv_eq_dec' : forall p q : word * word, p = q \/ p <> q.
Proof.
  intros [a1 n1] [a2 n2]. destruct (bv_eqb a1 a2) eqn:Ea; [|right; intros H; injection H as -> ->; rewrite bv_eqb_refl in Ea; discriminate].
  destruct (bv_eqb n1 n2) eqn:En; [|right; intros H; injection H as -> ->; rewrite bv_eqb_refl in En; discriminate].
  apply bv_eqb_eq in Ea, En. subst. left. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="SEGS A RES_len HULL_ok RES_len' HULL_ok'"] Lemma seps_overlap_eq : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pl,(=.(1.(2.&40.)(2.&40.)))Pp,(1.(2.&40.)(2.&40.))Pq,(1.(2.&40.)(2.&40.))Px1,$<.Px2,$<.P,(92.R5.)P,Piv,(1.(2.&40.)(2.&40.))P,(19.(1.(2.&40.)(2.&40.))R1.R7.)(1:.=(6.&40.(9.(2.&40.)(2.&40.)R2.)))P,(19.(1.(2.&40.)(2.&40.))R6.R7.)P,(19.(1.(2.&40.)(2.&40.))R6.R8.)P,(1:.R6.R5.)P,(4.(6.&40.(7.(2.&40.)(2.&40.)R9.))R7.)P,(4.R7.(8.(6.&40.(7.(2.&40.)(2.&40.)R:.))(6.&40.(9.(2.&40.)(2.&40.)R:.))))P,(4.(6.&40.(7.(2.&40.)(2.&40.)R:.))R9.)P,(4.R9.(8.(6.&40.(7.(2.&40.)(2.&40.)R;.))(6.&40.(9.(2.&40.)(2.&40.)R;.))))(>.(1.(2.&40.)(2.&40.))R=.R<.)")
(* [comment removed for export] *).
Proof.
  intros l p q x1 x2 Hs Hpos Hp Hq H12 P1 P2 Q1 Q2. destruct (iv_eq_dec' p q) as [He|Hne]; [exact He|]. exfalso.
  pose proof (APS.seps_In_disjoint0 l p q Hs Hpos Hp Hq Hne) as D. unfold iv_disjoint in D. lia.
Qed.

(* [comment removed for export] *)

Record dest_post (addr n : word) (model model' : Model) : Prop := DP_ {
  dp_maps : vm_maps (m_vmmaps model') = maps_subtract (vm_maps (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n);
  dp_res : vm_reserved (m_vmmaps model') = vm_reserved (m_vmmaps model);
  dp_noacc : vm_noaccess (m_vmmaps model') = maps_subtract (vm_noaccess (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n);
  dp_lazy : m_vm_lazy model' = maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n);
  dp_mat : m_vm_materialized model' = List.filter (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model);
  dp_limit : vm_limit (m_vmmaps model') = vm_limit (m_vmmaps model);
  dp_brk : vm_brk (m_vmmaps model') = vm_brk (m_vmmaps model);
  dp_sbrk : vm_start_brk (m_vmmaps model') = vm_start_brk (m_vmmaps model);
  dp_mbase : vm_mmap_base (m_vmmaps model') = vm_mmap_base (m_vmmaps model);
  dp_halted : m_halted model' = m_halted model;
  dp_fds : m_fds model' = m_fds model;
  dp_fs : m_fs model' = m_fs model;
  dp_tid : m_tid model' = m_tid model;
  dp_isp : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model) }.

Definition dest_mem (addr n : word) (FULL FULL' : word -> option byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "(3.Px,(2.&40.)P,(35.(1:.(6.&40.R1.)(6.&40.O4.))(4.(8.(6.&40.O4.)(6.&40.O3.))(6.&40.R1.)))(>.(3<.(2.&8.))A1.O1.R2.A1.O2.R2.)Px,(2.&40.)P,(3.(4.(6.&40.O4.)(6.&40.R1.))(1:.(6.&40.R1.)(8.(6.&40.O4.)(6.&40.O3.))))(>.(3<.(2.&8.))A1.O1.R2.(41.(2.&8.))))")
(* [comment removed for export] *).

Record dest_hyps (E : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model)
       (m : amap) (addr n : word) (nZ : Z) (model' : Model) (FULL' : word -> option byte) : Prop := DH_ {
  dh_C : CSOK E cs R FULL model;
  dh_m : In m (a_maps cs);
  dh_nf : is_fog m = false;
  dh_Un : bv_unsigned n = nZ;
  dh_pos : 0 < nZ;
  dh_nal : nZ mod 4096 = 0;
  dh_al : bv_unsigned addr mod 4096 = 0;
  dh_in1 : bv_unsigned (edenot E (am_base m)) <= bv_unsigned addr;
  dh_in2 : bv_unsigned addr + nZ <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m));
  dh_post : dest_post addr n model model';
  dh_mem : dest_mem addr n FULL FULL' }.

#[using="Type"] Lemma tok_of_hole : forall k, mkind_eqb k KHOLE = true -> is_tok_kind k = true.
Proof. intros [] H; cbn in H |- *; congruence. Qed.

Section Destroyed.
  Variables (E : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Variables (m : amap) (addr n : word) (nZ : Z) (model' : Model) (FULL' : word -> option byte).
  Hypothesis DH : dest_hyps E cs R FULL model m addr n nZ model' FULL'.
  Let HC := dh_C _ _ _ _ _ _ _ _ _ _ _ DH.
  Let Hm := dh_m _ _ _ _ _ _ _ _ _ _ _ DH.
  Let Hnf := dh_nf _ _ _ _ _ _ _ _ _ _ _ DH.
  Let Un := dh_Un _ _ _ _ _ _ _ _ _ _ _ DH.
  Let HnZpos := dh_pos _ _ _ _ _ _ _ _ _ _ _ DH.
  Let HnZal := dh_nal _ _ _ _ _ _ _ _ _ _ _ DH.
  Let Hal := dh_al _ _ _ _ _ _ _ _ _ _ _ DH.
  Let Hin1 := dh_in1 _ _ _ _ _ _ _ _ _ _ _ DH.
  Let Hin2 := dh_in2 _ _ _ _ _ _ _ _ _ _ _ DH.
  Let DPo := dh_post _ _ _ _ _ _ _ _ _ _ _ DH.
  Let DM := dh_mem _ _ _ _ _ _ _ _ _ _ _ DH.

  Let lo := bv_unsigned addr.
  Let hi := bv_unsigned addr + nZ.

  #[using="SEGS LIMIT SINV argH FS0 cs R FULL model addr n nZ model' FULL' DH HC Hm Hnf"] Lemma d_bounds : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "(3.(1:.=(6.&40.(98.VE,(9:.Vm,))))(3.(>.$<.(3;.(6.&40.(98.VE,(99.Vm,)))+1000.)=)(3.(>.$<.(3;.(6.&40.(98.VE,(9:.Vm,)))+1000.)=)(3.(9>.VA,(6.&40.(98.VE,(99.Vm,)))(6.&40.(98.VE,(9:.Vm,))))(3.(4.(8.(6.&40.(98.VE,(99.Vm,)))(6.&40.(98.VE,(9:.Vm,))))(<6.VSP0,))(1:.=(6.&40.(98.VE,(99.Vm,)))))))))")
(* [comment removed for export] *).
  Proof.
    pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HC) as B.
    exact (proj1 (Forall_forall _ _) B (amap_den E m) (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf)).
  Qed.

  #[using="SEGS LIMIT SINV argH FS0 RES_len HULL_ok SP0_ok RES_len' HULL_ok' ATOP_facts' E cs R FULL model m n model' FULL' DH HC Hm Hnf HnZpos HnZal Hal Hin1 Hin2"] Lemma d_lohi : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "(3.(35.(4.Vhi,(5.VA,))(4.(:.VA,)Vlo,))(3.(4.Vhi,(<6.VSP0,))(3.(1:.Vlo,Vhi,)(3.(4.Vhi,(48.+2.+40.))(3.(>.$<.(3;.Vlo,+1000.)=)(>.$<.(3;.Vhi,+1000.)=))))))")
(* [comment removed for export] *).
  Proof.
    pose proof d_bounds as (B1 & B2 & B3 & B4 & B5 & B6). subst lo hi. unfold hull_apart in B4. atopb.
    repeat split; try lia. rewrite Z.add_mod, Hal, HnZal by lia. reflexivity.
  Qed.

  #[using="SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SP0 RES_len' HULL_ok' E cs R FULL m n model' FULL' DH HC Hm Hnf HnZpos Hin1 Hin2"] Lemma d_in_maps : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Px,(2.&40.)P,(3.(4.Vlo,(6.&40.R1.))(1:.(6.&40.R1.)Vhi,))(>.$?.(10.(6.&40.R2.)(2:.(28.Vmodel,)))$17.)")
(* [comment removed for export] *).
  Proof.
    intros x Hx. eapply in_ivs_maps_match; [exact (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hm | exact Hnf |]. subst lo hi. lia.
  Qed.

  #[using="SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SP0 SP0_ok RES_len' HULL_ok' ATOP_facts' E cs R FULL model m addr n nZ FULL' DH HC Hm Hnf Un HnZpos HnZal Hal Hin1 Hin2 DPo lo hi"] Lemma d_wf' : model_ivs_wf model'.
  Proof.
    pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & Wsp). pose proof d_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
    unfold model_ivs_wf. rewrite (dp_maps _ _ _ _ DPo), (dp_noacc _ _ _ _ DPo), (dp_lazy _ _ _ _ DPo).
    split; [|split; [|split; [|unfold init_sp_ok in *; rewrite (dp_isp _ _ _ _ DPo); exact Wsp]]]; apply maps_subtract_wf; try assumption; rewrite Un; subst lo hi; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="SEGS A LIMIT SINV argH FS0 RES_len SP0 RES_len' E cs R FULL model m model' FULL' DH Un HnZpos"] Lemma d_sub_out : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pl,(=.(1.(2.&40.)(2.&40.)))Px,(2.&40.)P,(36.R2.)P,(35.(1:.(6.&40.R2.)Vlo,)(4.Vhi,(6.&40.R2.)))(>.$?.(10.(6.&40.R3.)(37.R4.(6.&40.Vaddr,)(8.(6.&40.Vaddr,)(6.&40.Vn,))))(10.(6.&40.R3.)R4.))")
(* [comment removed for export] *).
  Proof.
    intros l x W Hx. rewrite !in_ivs_covered. rewrite covered_maps_subtract by (try exact W; rewrite Un; lia). rewrite Un.
    replace (in_rng (bv_unsigned addr) (bv_unsigned addr + nZ) (bv_unsigned x)) with false
      by (symmetry; unfold in_rng; apply andb_false_iff; subst lo hi; destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    apply andb_true_r.
  Qed.

  #[using="SEGS A LIMIT SINV argH FS0 RES_len SP0 RES_len' E cs R FULL model m model' FULL' DH Un HnZpos"] Lemma d_sub_in : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pl,(=.(1.(2.&40.)(2.&40.)))Px,(2.&40.)P,(36.R2.)P,(3.(4.Vlo,(6.&40.R2.))(1:.(6.&40.R2.)Vhi,))(>.$?.(10.(6.&40.R3.)(37.R4.(6.&40.Vaddr,)(8.(6.&40.Vaddr,)(6.&40.Vn,))))$1;.)")
(* [comment removed for export] *).
  Proof.
    intros l x W Hx. rewrite in_ivs_covered. rewrite covered_maps_subtract by (try exact W; rewrite Un; lia). rewrite Un.
    replace (in_rng (bv_unsigned addr) (bv_unsigned addr + nZ) (bv_unsigned x)) with true
      by (symmetry; unfold in_rng; apply andb_true_intro; subst lo hi; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    apply andb_false_r.
  Qed.

  #[using="SEGS A LIMIT SINV argH FS0 RES_len SP0 RES_len' E cs R FULL m n FULL' DH HC Un HnZpos DPo"] Lemma d_maps_out : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Px,(2.&40.)P,(35.(1:.(6.&40.R1.)Vlo,)(4.Vhi,(6.&40.R1.)))(>.$?.(10.(6.&40.R2.)(2:.(28.Vmodel',)))(10.(6.&40.R2.)(2:.(28.Vmodel,))))")
(* [comment removed for export] *).
  Proof. intros x Hx. rewrite (dp_maps _ _ _ _ DPo). apply d_sub_out; [exact (proj1 (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC)) | exact Hx]. Qed.

  #[using="SEGS A LIMIT SINV argH FS0 RES_len SP0 RES_len' E cs R FULL model m n FULL' DH HC Un HnZpos DPo"] Lemma d_maps_in : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Px,(2.&40.)P,(3.(4.Vlo,(6.&40.R1.))(1:.(6.&40.R1.)Vhi,))(>.$?.(10.(6.&40.R2.)(2:.(28.Vmodel',)))$1;.)")
(* [comment removed for export] *).
  Proof. intros x Hx. rewrite (dp_maps _ _ _ _ DPo). apply d_sub_in; [exact (proj1 (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC)) | exact Hx]. Qed.

  #[using="SEGS A LIMIT SINV argH FS0 RES_len SP0 RES_len' E cs R FULL m n FULL' DH HC Un HnZpos DPo"] Lemma d_noacc_out : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Px,(2.&40.)P,(35.(1:.(6.&40.R1.)Vlo,)(4.Vhi,(6.&40.R1.)))(>.$?.(10.(6.&40.R2.)(27.(28.Vmodel',)))(10.(6.&40.R2.)(27.(28.Vmodel,))))")
(* [comment removed for export] *).
  Proof. intros x Hx. rewrite (dp_noacc _ _ _ _ DPo). apply d_sub_out; [exact (proj1 (proj2 (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC))) | exact Hx]. Qed.

  #[using="SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SP0 SP0_ok RES_len' HULL_ok' ATOP_facts' E cs R FULL m n FULL' DH HC Hm Hnf Un HnZpos HnZal Hal Hin1 Hin2 DPo"] Lemma d_lazy_out : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Px,(2.&40.)P,(35.(1:.(6.&40.R1.)Vlo,)(4.Vhi,(6.&40.R1.)))(>.$?.(39.(3:.R2.)(29.Vmodel',))(39.(3:.R2.)(29.Vmodel,)))")
(* [comment removed for export] *).
  Proof.
    intros x Hx. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _). pose proof d_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
    pose proof (page_of_byte_out_aligned x lo hi L5 L6 Hx) as P. subst lo hi.
    rewrite (dp_lazy _ _ _ _ DPo). apply page_in_ranges_subtract_out; [exact W3 | rewrite Un; lia | unfold page_size; rewrite Un; lia].
  Qed.

  #[using="SEGS LIMIT SINV argH FS0 RES_len HULL_ok SP0_ok RES_len' HULL_ok' ATOP_facts' R FULL m n FULL' DH HC Hm Hnf Un HnZpos HnZal Hal Hin1 Hin2 DPo"] Lemma d_vis_out : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pcs1,$43.Px,(2.&40.)P,(>.(=.(1.$4:.$4:.))(:=.R2.)(:=.Vcs,))P,(35.(1:.(6.&40.R2.)Vlo,)(4.Vhi,(6.&40.R2.)))(>.$?.(;7.VA,VSP0,VE,R4.Vmodel',R3.)(;7.VA,VSP0,VE,Vcs,Vmodel,R3.))")
(* [comment removed for export] *).
  Proof.
    intros cs1 x Hv Hx. unfold vis. rewrite (d_maps_out x Hx), (d_noacc_out x Hx), (d_lazy_out x Hx), (in_allow_ext E cs cs1 Hv). reflexivity.
  Qed.

  #[using="SEGS LIMIT SINV argH FS0 RES_len HULL_ok SP0_ok RES_len' HULL_ok' ATOP_facts' cs R FULL model m n FULL' DH HC Hm Hnf Un HnZpos HnZal Hal Hin1 Hin2 DPo"] Lemma d_vis_in : forall cs1 (x : word), lo <= bv_unsigned x < hi -> VIS E cs1 model' x = false.
  Proof.
    intros cs1 x Hx. pose proof d_lohi as (L1 & L2 & L3 & L4 & L5 & L6). unfold vis. rewrite (d_maps_in x Hx). cbn [andb].
    replace (in_hull A (bv_unsigned x)) with false by (symmetry; unfold in_hull; apply andb_false_iff; destruct L1 as [L1|L1]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    replace (ATOP <=? bv_unsigned x) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  #[using="SEGS LIMIT SINV FS0 RES_len HULL_ok SP0_ok RES_len' HULL_ok' ATOP_facts' R m n DH HC Hm Hnf Un HnZpos HnZal Hal Hin1 Hin2 DPo DM"] Lemma d_MR_out : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Pcs1,$43.Px,(2.&40.)P,(>.(=.(1.$4:.$4:.))(:=.R2.)(:=.Vcs,))P,(35.(1:.(6.&40.R2.)Vlo,)(4.Vhi,(6.&40.R2.)))(>.(3<.(2.&8.))(=1.VA,VSP0,VargH,VE,R4.Vmodel',VFULL',R3.)(=1.VA,VSP0,VargH,VE,Vcs,Vmodel,VFULL,R3.))")
(* [comment removed for export] *).
  Proof.
    intros cs1 x Hv Hx. unfold Mr, mrestrict, hid. rewrite (d_vis_out cs1 x Hv Hx). rewrite (proj1 DM x) by (subst lo hi; rewrite Un; exact Hx). reflexivity.
  Qed.

  #[using="SEGS LIMIT SINV FS0 RES_len HULL_ok SP0_ok RES_len' HULL_ok' ATOP_facts' cs R FULL model m n DH HC Hm Hnf Un HnZpos HnZal Hal Hin1 Hin2 DPo"] Lemma d_MR_in : forall cs1 (x : word), lo <= bv_unsigned x < hi -> MR E cs1 model' FULL' x = None.
  Proof.
    intros cs1 x Hx. unfold Mr, mrestrict, hid. rewrite (d_vis_in cs1 x Hx). rewrite orb_true_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SP0 SP0_ok RES_len' HULL_ok' ATOP_facts' E cs R FULL m addr n nZ FULL' DH HC Hm Hnf Un HnZpos HnZal Hal Hin1 Hin2 DPo lo hi"] Lemma d_eager : eager_used model' <= eager_used model.
  Proof.
    pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf. pose proof Hwf as (W1 & W2 & W3 & _). pose proof d_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
    rewrite (eager_used_sem model' d_wf'), (eager_used_sem model Hwf). rewrite (dp_maps _ _ _ _ DPo).
    rewrite (proj1 (proj2 (maps_subtract_sem (vm_maps (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) W1 ltac:(rewrite Un; subst lo hi; lia)))).
    apply sum_count_mono. intros x Hx. apply andb_prop in Hx as [Hx Hr]. apply negb_true_iff in Hx. apply negb_true_iff in Hr. apply negb_true_iff.
    rewrite (dp_noacc _ _ _ _ DPo), (dp_lazy _ _ _ _ DPo), !covered_app in Hx. rewrite covered_app.
    rewrite !covered_maps_subtract in Hx by (first [exact W2 | exact W3 | rewrite Un; subst lo hi; lia]). rewrite Hr in Hx. cbn [negb] in Hx. rewrite !andb_true_r in Hx. exact Hx.
  Qed.

  (* [comment removed for export] *)
  #[using="RES_len HULL_ok SHADOW_ok SP0_ok argH_high SINV_frame RES_len' HULL_ok' SHADOW_ok' ATOP_facts' R FULL model DH HC Hm Hnf Un HnZpos HnZal Hal Hin1 Hin2 DPo DM"] Lemma dest_cs1_ok : ltac2:(CDefT.buildp (gd_tbl_AsanNodesMmLib ()) "Psr',(=.$4:.)PR',(5;.&5.(2.&40.))Pk',(=.$9?.)Pp,$<.Pnx,$49.Ppcs,(=.$8>.)Psub',(=.(1.$4:.$4:.))P,(<9.VE,R7.R6.)P,(;?.VSEGS,VE,(=1.VA,VSP0,VargH,VE,Vcs,Vmodel',VFULL',)R6.)P,(>.(=.(1.(2.&40.)(2.&40.)))(90.$8>.(1.(2.&40.)(2.&40.))(97.VE,)R4.)(34.(98.VE,(99.Vm,))(98.VE,(9:.Vm,))(6.&40.Vaddr,)(8.(6.&40.Vaddr,)(6.&40.Vn,))))P,(0.$8>.Lpc,$8>.(>.$;5.(10<.R1.)(10<.Vm,))R5.)P,Pt,(1.$4:.$4:.)P,(19.(1.$4:.$4:.)R1.R6.)(3.(19.(1.$4:.$4:.)R2.(;4.Vcs,))(35.(4.(8.(;<.VE,(7.$4:.$4:.R2.))(;<.VE,(9.$4:.$4:.R2.)))Vlo,)(4.Vhi,(;<.VE,(7.$4:.$4:.R2.)))))P,Pt,(1.$4:.$4:.)P,(19.(1.$4:.$4:.)R1.(;4.Vcs,))(19.(1.$4:.$4:.)R2.R8.)(9;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,VE,(:3.(:4.R:.R=.R;.R9.)(91.(:8.Vcs,)Vm,R8.)(::.Vcs,)(:;.Vcs,)(:<.Vcs,)(:=.Vcs,)(:>.Vcs,)(:?.Vcs,)(;1.Vcs,)(;2.Vcs,)(;3.Vcs,)R7.)R<.VFULL',Vmodel',)")
(* [comment removed for export] *).
  Proof.
    intros sr' R' k' p nx pcs sub' Hregs Hknow Hpcs Hkinds Hsub' Hkeep.
    pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf. pose proof Hwf as (W1 & W2 & W3 & _).
    pose proof d_lohi as (L1 & L2 & L3 & L4 & L5 & L6). pose proof d_bounds as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof d_wf' as Hwf'. pose proof d_eager as EG.
    pose proof (co_seps _ _ _ _ _ _ _ _ _ _ _ _ HC) as SEPS. pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) as MM.
    assert (LH : bv_unsigned addr <= bv_unsigned addr + bv_unsigned n) by (rewrite Un; lia).
    assert (DISJ := fun m' Hm' Hnf' Hne => maps_match_disjoint E (a_maps cs) _ m m' MM SEPS Hm Hm' Hnf Hnf' Hne).
    assert (DISJ' : forall m', In m' (a_maps cs) -> is_fog m' = false -> m <> m' ->
              bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) <= lo
              \/ hi <= bv_unsigned (edenot E (am_base m'))).
    { intros m' Hm' Hnf' Hne. pose proof (DISJ m' Hm' Hnf' Hne) as D. unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. unfold lo, hi. lia. }
    assert (KNF : forall m', am_kind m' = KNONE \/ am_kind m' = KNONELAZY \/ am_kind m' = KRWLAZY -> is_fog m' = false).
    { intros m' Hk. unfold is_fog. destruct Hk as [-> |[-> | ->]]; reflexivity. }
    assert (BND : forall m', In m' (a_maps cs) -> is_fog m' = false -> 0 < bv_unsigned (edenot E (am_len m'))).
    { intros m' Hm' Hnf'. pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HC) (amap_den E m')
                    (maps_match_In E _ _ m' MM Hm' Hnf')) as (Bm1 & _). exact Bm1. }
    assert (BNDl : forall iv, In iv (vm_maps (m_vmmaps model)) -> 0 < bv_unsigned (snd iv)).
    { intros iv Hiv. exact (proj1 (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HC) iv Hiv)). }
    assert (MIN : In (amap_den E m) (vm_maps (m_vmmaps model))) by exact (maps_match_In E _ _ m MM Hm Hnf).
    (* [comment removed for export] *)
    assert (PCS : forall pc, In pc pcs ->
              bv_unsigned (edenot E (am_base m)) <= bv_unsigned (edenot E (am_base pc))
              /\ bv_unsigned (edenot E (am_base pc)) + bv_unsigned (edenot E (am_len pc)) <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m))
              /\ (bv_unsigned (edenot E (am_base pc)) + bv_unsigned (edenot E (am_len pc)) <= lo \/ hi <= bv_unsigned (edenot E (am_base pc)))
              /\ In (amap_den E pc) (iv_subtract (edenot E (am_base m)) (edenot E (am_len m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))).
    { intros pc Hpc. pose proof (in_map (amap_den E) _ _ Hpc) as Hin. rewrite Hpcs in Hin.
      assert (Hwfm : iv_wf (edenot E (am_base m), edenot E (am_len m))) by (unfold iv_wf, B, S; cbn [fst snd]; atopb; lia).
      pose proof (iv_subtract_pieces _ _ _ _ _ Hwfm Hin) as (P1 & P2 & P3).
      unfold amap_den in P1, P2, P3. cbn [fst snd] in P1, P2, P3. rewrite Un in P3. subst lo hi. auto. }
    assert (PCF : forall pc, In pc pcs -> is_fog pc = false).
    { intros pc Hpc. rewrite <- Hnf. unfold is_fog. rewrite (proj1 (Forall_forall _ _) Hkinds pc Hpc). reflexivity. }
    match goal with |- CSOK _ ?c _ _ _ => set (cs1 := c) end.
    assert (HIDOUT : forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x -> HID E cs1 model' x = HID E cs model x).
    { intros x Hx. unfold hid. rewrite (d_vis_out cs1 x eq_refl Hx). reflexivity. }
    assert (HALLOW : ALLOW E cs1 = ALLOW E cs) by reflexivity.
    (* [comment removed for export] *)
    assert (NBORN : forall ks iv q x1 x2, In iv (vm_maps (m_vmmaps model)) -> ~ born E (a_maps cs) ks iv ->
              In q (maps_subtract (vm_maps (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) ->
              x1 < x2 -> zB iv <= x1 -> x2 <= zE iv -> zB q <= x1 -> x2 <= zE q ->
              ~ born E (replace_entry (a_maps cs) m pcs) ks q).
    { intros ks iv q x1 x2 Hiv NB Hq H12 I1 I2 Q1 Q2 (m2 & Hm2 & Hf2 & Hk2 & Hd2). apply NB. unfold zB, zE in *.
      destruct (in_replace_entry _ _ _ _ Hm2) as [[Hin2' Hne2]|[_ Hpc2]].
      - (* [comment removed for export] *)
        pose proof (maps_match_In E _ _ m2 MM Hin2' Hf2) as Hd2in. rewrite Hd2 in Hd2in.
        rewrite (seps_overlap_eq _ iv q x1 x2 SEPS BNDl Hiv Hd2in H12 I1 I2 Q1 Q2). exists m2. auto.
      - (* [comment removed for export] *)
        destruct (PCS m2 Hpc2) as (P1 & P2 & _ & _). rewrite <- Hd2 in Q1, Q2. unfold amap_den in Q1, Q2. cbn [fst snd] in Q1, Q2.
        rewrite (seps_overlap_eq _ iv (amap_den E m) x1 x2 SEPS BNDl Hiv MIN H12 I1 I2 ltac:(unfold amap_den; cbn [fst snd]; lia) ltac:(unfold amap_den; cbn [fst snd]; lia)).
        exists m. split; [exact Hm|]. split; [exact Hnf|]. split; [|reflexivity].
        rewrite <- (proj1 (Forall_forall _ _) Hkinds m2 Hpc2). exact Hk2. }
    destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xisp Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xnk Xlzk Xsub Xdef Xnn Xcov].
    pose proof Xwf as (WFM & WFN & WFL & _).
    constructor; rewrite ?HALLOW; unfold cs1; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_sub kn s_regs s_log s_know s_next mk_ss]; fold cs1.
    - exact Hregs.
    - reflexivity.
    - unfold Mr. rewrite (hid_ext A SP0 argH E cs _ model') by reflexivity. exact Hknow.
    - rewrite (dp_halted _ _ _ _ DPo). exact Xhalt.
    - unfold fds_ok in *. rewrite (dp_fds _ _ _ _ DPo), (dp_fs _ _ _ _ DPo). exact Xfds.
    - rewrite (dp_fs _ _ _ _ DPo). exact Xfs.
    - rewrite (dp_tid _ _ _ _ DPo). exact Xtid.
    - rewrite (dp_res _ _ _ _ DPo). exact Xres.
    - rewrite (dp_limit _ _ _ _ DPo). exact Xlimit.
    - (* [comment removed for export] *) rewrite (dp_maps _ _ _ _ DPo). rewrite Un. fold hi.
      apply maps_match_subtract; [exact Xmaps | exact Xseps | exact BNDl | exact Hm | exact Hnf | lia | exact Hin1 | exact Hin2 | rewrite Hpcs, Un; reflexivity | exact PCF].
    - (* [comment removed for export] *)
      rewrite (dp_maps _ _ _ _ DPo), (dp_res _ _ _ _ DPo).
      apply Forall_forall. intros m' Hm' Hk'.
      destruct (in_replace_entry _ _ _ _ Hm') as [[Hin Hne]|[_ Hpc]].
      + destruct (proj1 (Forall_forall _ _) Xholes m' Hin Hk') as [F1 F2]. split; [|exact F2].
        intros iv Hiv. apply in_app_iff in Hiv as [Hiv|Hiv].
        * exact (F1 iv ltac:(apply in_app_iff; left; exact Hiv)).
        * destruct (maps_subtract_pieces _ _ _ iv W1 Hiv) as (r & Hr & R1 & R2 & _).
          destruct (F1 r ltac:(apply in_app_iff; right; exact Hr)); lia.
      + exfalso. pose proof (proj1 (Forall_forall _ _) Hkinds m' Hpc) as Hk. unfold is_hole in Hk'. cbn beta in Hk. rewrite Hk in Hk'.
        pose proof Hnf as Hnf0. unfold is_fog in Hnf0. rewrite (tok_of_hole _ Hk') in Hnf0. discriminate.
    - (* [comment removed for export] *) rewrite (dp_maps _ _ _ _ DPo). apply seps_maps_subtract; [exact Xseps | exact W1 | exact LH].
    - exact Hwf'.
    - (* [comment removed for export] *) rewrite (dp_maps _ _ _ _ DPo). apply Forall_forall. intros q Hq.
      destruct (maps_subtract_pieces _ _ _ q W1 Hq) as (r & Hr & R1 & R2 & _).
      pose proof (proj1 (Forall_forall _ _) Xbounds r Hr) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6). atopb.
      pose proof (proj1 (Forall_forall _ _) (maps_subtract_bounds _ (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) 1 ATOP L5 ltac:(rewrite Un; exact L6) ltac:(lia)
                    ltac:(apply Forall_forall; intros iv Hiv; pose proof (proj1 (Forall_forall _ _) Xbounds iv Hiv) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6); repeat split; try assumption; lia)) q Hq)
        as (Q1 & Q2 & Q3 & Q4 & Q5).
      repeat split; try assumption; try lia. unfold hull_apart in *. lia.
    - (* [comment removed for export] *) rewrite (dp_lazy _ _ _ _ DPo). apply Forall_forall. intros q Hq.
      destruct (maps_subtract_pieces _ _ _ q W3 Hq) as (r & Hr & R1 & R2 & _).
      pose proof (proj1 (Forall_forall _ _) Xlazyb r Hr) as [Y1 Y2]. unfold hull_apart in *. lia.
    - (* [comment removed for export] *) intros z Hz. rewrite (dp_maps _ _ _ _ DPo). rewrite (dp_noacc _ _ _ _ DPo) in Hz.
      rewrite in_ivs_covered in Hz |- *. rewrite covered_maps_subtract in Hz |- * by (first [exact W1 | exact W2 | exact LH]).
      apply andb_prop in Hz as [Hz Hr]. rewrite <- in_ivs_covered in Hz |- *. rewrite (Xnasub z Hz), Hr. reflexivity.
    - (* [comment removed for export] *) apply Forall_forall. intros m' Hm' Hk'. rewrite (dp_noacc _ _ _ _ DPo).
      destruct (in_replace_entry _ _ _ _ Hm') as [[Hin Hne]|[_ Hpc]].
      + pose proof (proj1 (Forall_forall _ _) Xnone m' Hin Hk') as X.
        assert (Hnf' : is_fog m' = false) by (apply KNF; tauto).
        unfold amap_den in *. apply maps_subtract_keeps; [rewrite Un; lia | exact (BND m' Hin Hnf') | exact X |].
        cbn [fst snd]. rewrite Un. pose proof (DISJ' m' Hin Hnf' ltac:(congruence)). unfold lo, hi in *. lia.
      + pose proof (proj1 (Forall_forall _ _) Hkinds m' Hpc) as Hk. rewrite Hk in Hk'.
        pose proof (proj1 (Forall_forall _ _) Xnone m Hm Hk') as X.
        destruct (PCS m' Hpc) as (_ & _ & _ & P4). eapply maps_subtract_in_pieces; [exact X | exact P4].
    - (* [comment removed for export] *) apply Forall_forall. intros m' Hm' Hk' x Hx.
      destruct (in_replace_entry _ _ _ _ Hm') as [[Hin Hne]|[_ Hpc]].
      + destruct (proj1 (Forall_forall _ _) Xkinds m' Hin Hk' x Hx) as [K1 K2].
        pose proof (DISJ' m' Hin ltac:(apply KNF; tauto) ltac:(congruence)) as D.
        rewrite d_noacc_out, d_lazy_out by lia. auto.
      + pose proof (proj1 (Forall_forall _ _) Hkinds m' Hpc) as Hk. rewrite Hk in Hk'.
        destruct (PCS m' Hpc) as (P1 & P2 & P3 & _).
        destruct (proj1 (Forall_forall _ _) Xkinds m Hm Hk' x ltac:(lia)) as [K1 K2].
        rewrite d_noacc_out, d_lazy_out by lia. auto.
    - (* [comment removed for export] *) rewrite (dp_res _ _ _ _ DPo), (dp_maps _ _ _ _ DPo). rewrite sum_sizes_app in Xtotsz |- *.
      pose proof (sum_sizes_maps_subtract_le (vm_maps (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) W1 LH). lia.
    - rewrite (dp_isp _ _ _ _ DPo). exact Xisp.
    - rewrite (dp_brk _ _ _ _ DPo). exact Xbrk.
    - rewrite (dp_brk _ _ _ _ DPo), (dp_sbrk _ _ _ _ DPo). exact Xsbrk.
    - (* [comment removed for export] *) lia.
    - exact Xabytes.
    - (* [comment removed for export] *) destruct Xminv as [N1 N2 N3 N4 N5].
      assert (MAT : forall q, In q (m_vm_materialized model') -> In q (m_vm_materialized model) /\ (bv_unsigned q < lo \/ hi <= bv_unsigned q)).
      { intros q Hq. rewrite (dp_mat _ _ _ _ DPo) in Hq. apply filter_In in Hq as [Hq Ho]. split; [exact Hq|].
        unfold page_outside_range in Ho. apply negb_true_iff in Ho. apply andb_false_iff in Ho as [Ho|Ho];
          [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; unfold lo, hi; rewrite <- ?Un; lia. }
      constructor; rewrite ?(dp_limit _ _ _ _ DPo).
      + rewrite (dp_mat _ _ _ _ DPo). apply NoDup_filter. exact N1.
      + intros q Hq. apply N2. apply MAT. exact Hq.
      + intros q Hq. apply N3. apply MAT. exact Hq.
      + intros q Hq. destruct (MAT q Hq) as [Hq0 Hout]. pose proof (N4 q Hq0) as L0.
        rewrite <- (page_base_aligned' q (N2 q Hq0)). rewrite (d_lazy_out q Hout). rewrite page_base_aligned' by exact (N2 q Hq0). exact L0.
      + rewrite Xlimit in *. lia.
    - (* [comment removed for export] *) intros x Hh Hmx Hna Hlz Hgh.
      destruct (Z_lt_le_dec (bv_unsigned x) lo) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) hi) as [Hlt2|Hge2]].
      + rewrite (proj1 DM x) by (unfold lo in *; lia). rewrite HIDOUT in Hh by lia. rewrite d_maps_out in Hmx by lia.
        rewrite d_noacc_out in Hna by lia. rewrite d_lazy_out in Hlz by lia. exact (Xzero x Hh Hmx Hna Hlz Hgh).
      + rewrite d_maps_in in Hmx by lia. discriminate.
      + rewrite (proj1 DM x) by (unfold hi in *; rewrite Un; lia). rewrite HIDOUT in Hh by lia. rewrite d_maps_out in Hmx by lia.
        rewrite d_noacc_out in Hna by lia. rewrite d_lazy_out in Hlz by lia. exact (Xzero x Hh Hmx Hna Hlz Hgh).
    - (* [comment removed for export] *) eapply SINV_frame; [| |exact Xsinv].
      + intros x Hx. apply (proj1 DM). pose proof (argH_high _ _ Hx). atopb. unfold hi in *. rewrite Un. lia.
      + intros x Hx Hd. rewrite (proj1 DM x); [exact Hd|]. atopb. unfold hi in *. rewrite Un. lia.
    - (* [comment removed for export] *)
      rewrite (dp_maps _ _ _ _ DPo). intros e He. rewrite (dp_noacc _ _ _ _ DPo) in He.
      destruct (maps_subtract_pieces _ _ _ _ WFN He) as (e0 & He0 & Q1 & Q2 & Q3).
      destruct (Xnk e0 He0) as (P0 & iv & Hiv & C1 & C2 & NB).
      pose proof (maps_subtract_pos _ _ _ _ WFN (fun e1 He1 => proj1 (Xnk e1 He1)) He) as Pe. split; [exact Pe|].
      unfold zB, zE in C1, C2.
      destruct (maps_subtract_cover _ (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) iv (bv_unsigned (fst e)) (bv_unsigned (fst e) + bv_unsigned (snd e)) WFM Hiv
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (q & Hq & G1 & G2).
      exists q. split; [exact Hq|]. unfold zB, zE. split; [exact G1|]. split; [exact G2|].
      eapply (NBORN K_NOTNONE iv q (bv_unsigned (fst e)) (bv_unsigned (fst e) + bv_unsigned (snd e))); unfold zB, zE; first [assumption | lia].
    - (* [comment removed for export] *)
      rewrite (dp_maps _ _ _ _ DPo). intros e He. rewrite (dp_lazy _ _ _ _ DPo) in He.
      destruct (maps_subtract_pieces _ _ _ _ WFL He) as (e0 & He0 & Q1 & Q2 & Q3).
      destruct (Xlzk e0 He0) as (P0 & iv & Hiv & C1 & C2 & NB).
      pose proof (maps_subtract_pos _ _ _ _ WFL (fun e1 He1 => proj1 (Xlzk e1 He1)) He) as Pe. split; [exact Pe|].
      unfold zB, zE in C1, C2.
      destruct (maps_subtract_cover _ (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) iv (bv_unsigned (fst e)) (bv_unsigned (fst e) + bv_unsigned (snd e)) WFM Hiv
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (q & Hq & G1 & G2).
      exists q. split; [exact Hq|]. unfold zB, zE. split; [exact G1|]. split; [exact G2|].
      eapply (NBORN K_EAGER iv q (bv_unsigned (fst e)) (bv_unsigned (fst e) + bv_unsigned (snd e))); unfold zB, zE; first [assumption | lia].
    - (* [comment removed for export] *)
      rewrite (dp_maps _ _ _ _ DPo). apply Forall_forall. intros t Ht. destruct (Hsub' t Ht) as [Hold Hapart].
      pose proof (proj1 (Forall_forall _ _) Xsub t Hold) as (S1 & (iv & Hiv & I1 & I2) & S3 & S4). split; [exact S1|]. unfold zB, zE in I1, I2. split; [|split].
      + destruct (maps_subtract_cover _ (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) iv (uE E (fst t)) (uE E (fst t) + uE E (snd t)) WFM Hiv
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold lo, hi in Hapart; rewrite Un; lia)) as (q & Hq & G1 & G2).
        exists q. split; [exact Hq|]. unfold zB, zE. split; [exact G1 | exact G2].
      + intros e He. rewrite (dp_noacc _ _ _ _ DPo) in He. destruct (maps_subtract_pieces _ _ _ _ WFN He) as (e0 & He0 & Q1 & Q2 & Q3).
        pose proof (S3 e0 He0). unfold zB, zE in *. lia.
      + intros e He. rewrite (dp_lazy _ _ _ _ DPo) in He. destruct (maps_subtract_pieces _ _ _ _ WFL He) as (e0 & He0 & Q1 & Q2 & Q3).
        pose proof (S4 e0 He0). unfold zB, zE in *. lia.
    - (* [comment removed for export] *)
      apply Forall_forall. intros m' Hm' Hf' Hk' x Hx.
      destruct (in_replace_entry _ _ _ _ Hm') as [[Hin Hne]|[_ Hpc]].
      + pose proof (DISJ' m' Hin Hf' ltac:(congruence)) as D.
        rewrite (proj1 DM x) by (rewrite Un; unfold lo, hi in *; lia). exact (proj1 (Forall_forall _ _) Xdef m' Hin Hf' Hk' x Hx).
      + pose proof (proj1 (Forall_forall _ _) Hkinds m' Hpc) as Hk. rewrite Hk in Hk'. destruct (PCS m' Hpc) as (P1 & P2 & P3 & _).
        rewrite (proj1 DM x) by (rewrite Un; unfold lo, hi in *; lia). exact (proj1 (Forall_forall _ _) Xdef m Hm Hnf Hk' x ltac:(lia)).
    - (* [comment removed for export] *)
      intros x Hx.
      destruct (Z_lt_le_dec (bv_unsigned x) lo) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) hi) as [Hlt2|Hge2]].
      + rewrite d_noacc_out in Hx by lia. rewrite (proj1 DM x) by (unfold lo in *; lia). exact (Xnn x Hx).
      + exfalso. rewrite (dp_noacc _ _ _ _ DPo) in Hx. rewrite (d_sub_in _ x W2 ltac:(lia)) in Hx. discriminate Hx.
      + rewrite d_noacc_out in Hx by lia. rewrite (proj1 DM x) by (unfold hi in *; rewrite Un; lia). exact (Xnn x Hx).
    - (* [comment removed for export] *)
      assert (OLDCOV : forall m1, In m1 (a_maps cs) -> In (am_kind m1) K_NLZ ->
                forall z, uE E (am_base m1) <= z < uE E (am_base m1) + uE E (am_len m1) -> z < lo \/ hi <= z ->
                in_ivs z (vm_noaccess (m_vmmaps model')) = true \/ exists t, In t sub' /\ APS.in_tok E z t).
      { intros m1 Hm1 Hk1 z Hz Hout.
        assert (Rz : 0 <= z < 2 ^ 64).
        { unfold uE in Hz. pose proof (u64_range (edenot E (am_base m1))). pose proof (u64_range (edenot E (am_len m1))).
          assert (Hf1 : is_fog m1 = false) by (unfold is_fog; destruct Hk1 as [<-|[<-|[]]]; reflexivity).
          pose proof (proj1 (Forall_forall _ _) Xbounds _ (maps_match_In E _ _ m1 Xmaps Hm1 Hf1)) as (_ & _ & _ & _ & HT & _).
          unfold amap_den in HT. cbn [fst snd] in HT. atopb. unfold APS.ATOP in *. lia. }
        destruct (proj1 (Forall_forall _ _) Xcov m1 Hm1 Hk1 z Hz) as [Hn|(t & Ht & Hzt)];
          [left | right; exists t; split; [exact (Hkeep t Ht) | exact Hzt]].
        pose proof (d_noacc_out (Z_to_bv 64 z)) as X. rewrite u64_lit in X by lia. rewrite (X Hout). exact Hn. }
      apply Forall_forall. intros m' Hm' Hk' z Hz.
      destruct (in_replace_entry _ _ _ _ Hm') as [[Hin Hne]|[_ Hpc]].
      + assert (Hf' : is_fog m' = false) by (unfold is_fog; destruct Hk' as [<-|[<-|[]]]; reflexivity).
        pose proof (DISJ' m' Hin Hf' ltac:(congruence)) as D. unfold uE in Hz. exact (OLDCOV m' Hin Hk' z Hz ltac:(lia)).
      + pose proof (proj1 (Forall_forall _ _) Hkinds m' Hpc) as Hk. cbn beta in Hk. rewrite Hk in Hk'. destruct (PCS m' Hpc) as (P1 & P2 & P3 & _).
        unfold uE in Hz. exact (OLDCOV m Hm Hk' z ltac:(unfold uE; lia) ltac:(lia)).
  Qed.

End Destroyed.


End Nodes.
