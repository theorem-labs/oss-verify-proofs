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
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg DivergeSim SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanPlanSound () : Init.string Init.list := ["OSSVerify.KrLib.ABoot.AxSymExec3.AX2.env"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.eq"; "APS.uE_sp0"; "Corelib.Init.Logic.and"; "APS.uE"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.e_sp0"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.e_stkpg"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.e_stkbase"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.EVar"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.V_S1"; "Stdlib.ZArith.BinInt.Z.div"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.V_S2"; "Stdlib.Lists.List.existsb"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.leb"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.fst"; "Stdlib.ZArith.BinInt.Z.ltb"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Logic.or"; "Corelib.Lists.ListDef.Forall"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.img_lo"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.img_hi"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.bool"; "APS.in_ivs"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "APS.pagedown"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.expr"; "APS.pageup"; "APS.Sound.sh_lo"; "APS.Sound.sh_hi"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.acs"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_ghost"; "Corelib.Init.Datatypes.app"; "APS.Sound.in_ghost"; "Corelib.Init.Datatypes.false"; "Stdlib.Lists.List.In"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "Corelib.Init.Datatypes.orb"; "APS.in_hull"; "APS.Sound.ATOP"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.negb"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess"; "LinuxProcessSemantics.LinuxProcessSem.State.page_in_ranges"; "LinuxProcessSemantics.LinuxProcessSem.State.page_base"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "APS.Sound.in_allow"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.is_hole"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.am_base"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.am_len"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.KHI"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.amap"; "APS.Sound.hole_ok"; "Corelib.Init.Logic.ex"; "APS.Sound.zB"; "APS.Sound.zE"; "APS.Sound.born"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.is_fog"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.mkind"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.am_kind"; "APS.Sound.K_DEF"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.edenot"; "APS.Sound.K_NLZ"; "APS.Sound.in_tok"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "APS.Sound.cs_ok"; "OSSVerify.KrLib.ABoot.AsanAcct.lazy_cover"; "APS.Sound.hid"; "APS.Sound.allowA"; "OSSVerify.KrLib.ABoot.AsanAcct.mrestrict"; "OSSVerify.KrLib.ABoot.AsanAcct.munrestrict"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.sym_state"; "OSSVerify.KrLib.ABoot.AsanAcct.same_but_materialized"; "OSSVerify.KrLib.ABoot.AsanAcct.MInv"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.regs_ok"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.s_regs"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.sentry"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.s_log"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.know_ok"; "APS.Sound.Mr"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.s_know"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.with_ss"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.kentry"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.set_kn"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.drop_ixs"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kn"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.kentry_ok"; "APS.Sound.kfoot_apart"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kentry_apart_b"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.estart"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.SA"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.elenZ"; "Stdlib.Lists.List.filter"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kentry_apart_bp"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.mk_sprep"; "OSSVerify.KrLib.ABoot.StoreOk.mem_grows"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kn_havoc"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.saddr"; "Corelib.Init.Logic.iff"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.flat"; "APS.Sound.pw_kind"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.kcut"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.KWr"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kwr_cut"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kn_cutout"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_droprange"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_bump"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.pc"; "OSSVerify.KrLib.ABoot.AsanAcct.H_off_segments"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "Stdlib.ZArith.BinInt.Z.of_nat"; "APS.Sound.kimg_in_hull"; "APS.Sound.vis"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.afd"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.ACS"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_maps"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_vis"; "OSSVerify.KrLib.ABoot.AsanAcct.eager_used"; "OSSVerify.KrLib.ABoot.AsanAcct.A_bytes"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_limit"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.flat_x"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.split_lit"; "APS.Sound.maps_match"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.is_tok_kind"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.AM"; "APS.Sound.amap_den"; "Corelib.Lists.ListDef.map"; "Stdlib.Lists.List.NoDup"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.amap_eqb"; "LinuxProcessSemantics.LinuxProcessSem.State.map_remove"; "OSSVerify.KrLib.ABoot.AxSymRun3.env_agree"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kn_vars_lt"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.sr_vars_lt"; "OSSVerify.KrLib.ABoot.ShapeAlg.TSet"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.shape"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.shape_vars_lt"; "APS.Sound.sd"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.salt2"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.nxt"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "OSSVerify.KrLib.ABoot.SpinAlg.srealizes"; "APS.cfg_of"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.is_ecall_at"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_brk2"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_alt2"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_exit"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_exit"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.spiece"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_emit"; "APS.Sound.Wp"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.erange"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.KRange"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.deand"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.expr_vars_lt"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.xb2"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.residue_fact"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.fact_ok"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.add_kn"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.entails"; "Corelib.Init.Peano.lt"; "OSSVerify.KrLib.ABoot.PropExec.getr"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.reg"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.reg_lit"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.two64"; "Corelib.Lists.ListDef.nth"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.ELit"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.sr_upd"; "OSSVerify.KrLib.ABoot.PropExec.regupd"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.fresh_ok"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_ss"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.maps_vars_lt"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.pairs_vars_lt"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_brk"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.fd_vars_lt"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_fd"; "Corelib.Init.Peano.le"; "APS.Sound.in_ghostl"; "APS.Sound.fds_ok"; "APS.Sound.nlz_ok"; "APS.Sound.sub_ok"; "APS.Sound.def_ok"; "APS.Sound.cov_ok"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.run_block"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.run_block_gc"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.find_disj"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.disj_cands"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.disj_side_fact"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.scaled_var"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.svar_range"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.ev"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.disj_var_fact"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.vis_add"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_casedisj"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.shadow_of"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.shadow_off"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_shdisj"; "Corelib.Init.Datatypes.length"; "APS.Sound.ext_list"; "Corelib.Init.Nat.add"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.sr_fresh"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_havoc"; "APS.Sound.kn_bigexprs"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kn_bigsubst"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_havocbig"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.ksubst"; "APS.Sound.upd"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.inst"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.msubst"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.psubst"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kentry_eqb_h"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kflat_h"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.cover1"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.cover_x"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.regs_match_h"; "APS.Sound.is_havoc"; "APS.Sound.henv"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_sub"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.set_regs"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.entails_h"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_diamond_join"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.loop_ok"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.xhi"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.plan"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.cres"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.check_all"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.COk"; "Corelib.Init.Logic.True"; "Stdlib.Lists.List.nth_error"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.list_set_nth"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.fog_token"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.with_sub"; "APS.seps"; "APS.iv_disjoint"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_fog"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_fognew"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_ghost"; "APS.Sound.K_EAGER"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kzero_x"; "Stdlib.Lists.List.flat_map"; "APS.Sound.allow1"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_unvis"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_unvis_keep"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.unvis_all"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_havocbrk"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_intro"; "Stdlib.Lists.List.forallb"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.evars_all"; "APS.Sound.ren_ok"; "APS.Sound.ren_env"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.erename"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kvars_all"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.krename"; "APS.Sound.RenameCS.pvars_all"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.rename_cs"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.mrename"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.csvars_all"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_rename"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_compact"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_abstractcell"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.hw_val"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.hw_apply"; "Corelib.Init.Datatypes.S"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.hw_go"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_havocwords"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_respell"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_pc"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.SPIN_WORD"; "OSSVerify.KrLib.ABoot.DivergeSim.is_self_jump"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.node_spin"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_nil"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.loopctx"; "APS.Sound.LCOK"; "APS.Sound.lc_guard"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.check"].


Module APS.
Import AX2. Import AX2S. Import AP.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition uE (E : env) (e : expr) : Z := bv_unsigned (edenot E e).
(* [comment removed for export] *)
Definition uE_sp0 (E : env) : Z :=
  let x := uE E (EVar V_S1) in let y := uE E (EVar V_S2) in
  if ((x <=? 0xFFFFFFFF) && (y <=? 2047))%bool then 32768 * x + 16 * y else -1.

Lemma uE_sp0_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pz,$1.P,(2.+800000.R1.)P,(3.$1.(4.R3.)R2.)(5.(3.$1.(6.R4.$7.)R3.)(5.(3.$1.(6.R4.$8.)(9.R3.(:.R3.+1000.)))(5.(3.$1.(6.R4.$;.)(9.(9.R3.(:.R3.+1000.))+800000.))(5.(3.$1.(6.R4.(<.$=.))(>.R3.+8000.))(3.$1.(6.R4.(<.$?.))(>.(:.R3.+8000.)+10.))))))")
(* [comment removed for export] *).
Proof.
  intros E z Hz H. unfold uE_sp0 in H. cbv zeta in H. unfold uE in *. cbn [edenot] in *.
  pose proof (u64_range (ev E V_S1)) as R1. pose proof (u64_range (ev E V_S2)) as R2.
  destruct ((bv_unsigned (ev E V_S1) <=? 0xFFFFFFFF) && (bv_unsigned (ev E V_S2) <=? 2047))%bool eqn:Hc; [|lia].
  apply andb_prop in Hc as [Hx Hy]. apply Z.leb_le in Hx. apply Z.leb_le in Hy.
  set (x := bv_unsigned (ev E V_S1)) in *. set (y := bv_unsigned (ev E V_S2)) in *.
  unfold e_stkbase, e_stkpg, e_sp0, eaddz, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot. cbn [edenot]. fold x y.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (V1 : bv_unsigned (Sem.mul_div M_MUL (Z_to_bv 64 32768) (ev E V_S1)) = 32768 * x).
  { rewrite u_mul64, u64_lit by lia. fold x. apply Z.mod_small. lia. }
  assert (V2 : bv_unsigned (Sem.mul_div M_MUL (Z_to_bv 64 16) (ev E V_S2)) = 16 * y).
  { rewrite u_mul64, u64_lit by lia. fold y. apply Z.mod_small. lia. }
  assert (V3 : bv_unsigned (Sem.alu64 ALU_SRL (ev E V_S2) (Z_to_bv 64 8)) = y / 256).
  { rewrite u_srl64, u64_lit by lia. fold y. change (2 ^ (8 mod 64)) with 256. reflexivity. }
  assert (V4 : bv_unsigned (Sem.mul_div M_MUL (Z_to_bv 64 4096) (Sem.alu64 ALU_SRL (ev E V_S2) (Z_to_bv 64 8))) = 4096 * (y / 256)).
  { rewrite u_mul64, u64_lit, V3 by lia. apply Z.mod_small. lia. }
  assert (V5 : bv_unsigned (Sem.alu64 ALU_ADD (Sem.mul_div M_MUL (Z_to_bv 64 32768) (ev E V_S1)) (Sem.mul_div M_MUL (Z_to_bv 64 16) (ev E V_S2))) = 32768 * x + 16 * y).
  { rewrite u_add64, V1, V2. apply Z.mod_small. lia. }
  assert (V6 : bv_unsigned (Sem.alu64 ALU_ADD (Sem.mul_div M_MUL (Z_to_bv 64 32768) (ev E V_S1))
                 (Sem.mul_div M_MUL (Z_to_bv 64 4096) (Sem.alu64 ALU_SRL (ev E V_S2) (Z_to_bv 64 8)))) = 32768 * x + 4096 * (y / 256)).
  { rewrite u_add64, V1, V4. apply Z.mod_small. lia. }
  rewrite V5, V6, u_add64, V6, (u_lit64 (-8388608)). unfold two64.
  assert (XY : 32768 * x + 16 * y = z) by lia.
  assert (PG : 32768 * x + 4096 * (y / 256) = z - z mod 4096) by nia.
  repeat split; try nia.
  all: rewrite PG; replace ((-8388608) mod 2 ^ 64) with (2 ^ 64 - 8388608) by reflexivity;
       rewrite <- (Z.mod_small (z - z mod 4096 - 8388608) (2 ^ 64)) by nia; f_equal; nia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Definition pagedown (z : Z) : Z := z / 4096 * 4096.
Definition pageup (z : Z) : Z := (z + 4095) / 4096 * 4096.

Lemma pagedown_le : forall z, pagedown z <= z.
Proof. intros z. unfold pagedown. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma pageup_ge : forall z, z <= pageup z.
Proof. intros z. unfold pageup. lia. Qed.
Lemma pagedown_mod : forall z, pagedown z mod 4096 = 0.
Proof. intros z. unfold pagedown. rewrite Z.mod_mul. reflexivity. lia. Qed.
Lemma pageup_mod : forall z, pageup z mod 4096 = 0.
Proof. intros z. unfold pageup. apply Z.mod_mul. lia. Qed.
Lemma pageup_minus_pagedown : forall a b, a <= b -> pageup b - pagedown a <= b - a + 8192.
Proof. intros a b H. unfold pageup, pagedown. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition in_ivs (z : Z) (l : list (word * word)) : bool := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "(10.(11.(12.&40.)(12.&40.))Liv,(11.(12.&40.)(12.&40.))(13.(14.(15.&40.(16.(12.&40.)(12.&40.)R1.))O2.)(17.O2.(18.(15.&40.(16.(12.&40.)(12.&40.)R1.))(15.&40.(19.(12.&40.)(12.&40.)R1.)))))O1.)")
(* [comment removed for export] *).

Definition in_hull (A : atable) (z : Z) : bool := ((img_lo A <=? z) && (z <? img_hi A))%bool.
(* [comment removed for export] *)
Definition hull_apart (A : atable) (lo n : Z) : Prop := lo + n <= img_lo A \/ img_hi A <= lo.

(* [comment removed for export] *)
Definition iv_disjoint (p q : word * word) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "(1:.(2.(18.(15.&40.(16.(12.&40.)(12.&40.)O2.))(15.&40.(19.(12.&40.)(12.&40.)O2.)))(15.&40.(16.(12.&40.)(12.&40.)O1.)))(2.(18.(15.&40.(16.(12.&40.)(12.&40.)O1.))(15.&40.(19.(12.&40.)(12.&40.)O1.)))(15.&40.(16.(12.&40.)(12.&40.)O2.))))")
(* [comment removed for export] *).
Inductive seps : list (word * word) -> Prop :=
| seps_nil : seps []
| seps_cons : forall p l, Forall (iv_disjoint p) l -> seps l -> seps (p :: l).

Fixpoint sum_sizes (l : list (word * word)) : Z :=
  match l with [] => 0 | iv :: r => bv_unsigned (snd iv) + sum_sizes r end.

Definition cfg_of (SEGS : list Segment) (R : bvmap 5 word) (p : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (mkst R (Z_to_bv 64 p) M (seg_rom SEGS)) model.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition x_spin_ok (x : xnode) : bool :=
  match x with XIMemset => true | _ => false end.

Fixpoint spin_only (p : plan) : bool :=
  match p with
  | PSpin => true
  | PRun _ k => spin_only k
  | PX x _ k => x_spin_ok x && spin_only k
  | PFresh _ _ _ k => spin_only k
  | PDiamond _ _ k => spin_only k
  | _ => false
  end.

Fixpoint spin_guarded (p : plan) : bool :=
  match p with
  | PSpin => false
  | PRun _ k => spin_guarded k
  | PSplit _ _ k1 k2 | PCase2 _ _ k1 k2 | PCaseDisj _ _ k1 k2 => spin_guarded k1 && spin_guarded k2
  | PShDisj _ _ _ _ k => spin_guarded k
  | PContra => true
  | PFact _ k | PJoin _ _ _ k | PForget _ k | PDropRange _ _ k | PGcKeep _ k | PBump _ k | PHavoc _ k | PHavocBig _ k
  | PFresh _ _ _ k | PSys _ k => spin_guarded k
  | PMmap kr kg => (spin_only kr || spin_guarded kr) && spin_guarded kg
  | PMmapIn kk ko kd | PMmapInH kk ko kd => (spin_only kk || spin_guarded kk) && spin_guarded ko && (spin_only kd || spin_guarded kd)
  | PMprotect kr kg => (spin_only kr || spin_guarded kr) && spin_guarded kg
  | PBrk2 ka kb => spin_guarded ka && spin_guarded kb
  | PX _ _ k | PExt _ _ k | PEmit _ _ k => spin_guarded k
  | PExt2 _ _ k1 k2 => (spin_only k1 || spin_guarded k1) && spin_guarded k2
  | PLoop _ _ _ body k => spin_guarded body && spin_guarded k
  | PNext | PHandoff _ | PExit => true
  | PFog _ _ k | PFogNew _ _ k | PGhost _ _ k | PUnvis _ _ k | PHavocBrk _ _ k | PIntro _ _ k | PDiamond _ _ k
  | PRename _ k | PCompact k => spin_guarded k
  | PVia _ _ _ karms k => spin_guarded karms && spin_guarded k
  | PMerge _ => true
  | PAbstractCell _ _ k | PHavocWords _ k | PRespell _ _ k => spin_guarded k
  end.

Section Sound.
Variable SEGS : list Segment.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable HS : nat -> option acs.
(* [comment removed for export] *)
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).

(* [comment removed for export] *)
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
(* [comment removed for export] *)
Definition res_len_ok : Prop := length (segments_reserved SEGS) = n_res A.
Definition hull_ok : Prop := 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI.
Definition shadow_ok : Prop := 0 <= shadow_off A <= 2 ^ 47.
Hypothesis RES_len : res_len_ok.
Hypothesis RES_hull : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "(1;.(11.(12.&40.)(12.&40.))Liv,(11.(12.&40.)(12.&40.))(5.(2.(1<.VA,)(15.&40.(16.(12.&40.)(12.&40.)R1.)))(2.(18.(15.&40.(16.(12.&40.)(12.&40.)R1.))(15.&40.(19.(12.&40.)(12.&40.)R1.)))(1=.VA,)))(1>.VSEGS,))")
(* [comment removed for export] *).
Hypothesis HULL_ok : hull_ok.
Hypothesis SHADOW_ok : shadow_ok.
(* [comment removed for export] *)
Definition hull_cov : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "(5.(1?.(1<.VA,)(1=.VA,))Pz,$1.P,(5.(2.(1<.VA,)R1.)(1?.R1.(1=.VA,)))(3.$20.(21.R2.(1>.VSEGS,))$22.))")
(* [comment removed for export] *).
Hypothesis HULL_cov : hull_cov.

(* [comment removed for export] *)
Variable SP0 : Z.
Definition sp0_ok : Prop := sp_window_lo <= SP0 <= sp_window_hi.
Hypothesis SP0_ok : sp0_ok.
Definition ATOP : Z := SP0 - 8388608.
#[using="SP0_ok"] Lemma CEIL_le_ATOP : CEIL <= ATOP.
Proof. pose proof SP0_ok as H. unfold sp0_ok, sp_window_lo, sp_window_hi in H. unfold CEIL, ATOP. lia. Qed.
#[using="SP0_ok"] Lemma ATOP_le_ATOPMAX : ATOP <= ATOPMAX.
Proof. pose proof SP0_ok as H. unfold sp0_ok, sp_window_lo, sp_window_hi in H. unfold ATOPMAX, ATOP. lia. Qed.
#[using="SP0_ok"] Lemma ATOP_bounds : CEIL <= ATOP <= ATOPMAX.
Proof. split; [apply CEIL_le_ATOP | apply ATOP_le_ATOPMAX]. Qed.
#[using="SP0_ok"] Lemma ATOP_facts : 0x7fff80000000 <= SP0 <= 0x800000000000 /\ ATOP = SP0 - 8388608.
Proof. pose proof SP0_ok as H. unfold sp0_ok, sp_window_lo, sp_window_hi in H. unfold ATOP. lia. Qed.
(* [comment removed for export] *)
Ltac atopb := first [pose proof ATOP_facts as ATB | idtac].

(* [comment removed for export] *)
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> SP0 <= bv_unsigned a.   (* [comment removed for export] *)
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
(* [comment removed for export] *)
Hypothesis SINV_frame : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,Px,(12.&40.)(23.(12.&8.))PM',Px,(12.&40.)(23.(12.&8.))P,Pa,(12.&40.)P,(3.$20.A2.VargH,R4.R1.$22.)(3.(23.(12.&8.))A1.R3.R2.A1.R4.R2.)P,Pa,(12.&40.)P,(2.VSP0,(15.&40.R1.))P,(24.(3.(23.(12.&8.))A1.R5.R2.(25.(12.&8.))))(24.(3.(23.(12.&8.))A1.R5.R3.(25.(12.&8.))))P,A2.VSINV,R5.R4.A2.VSINV,R6.R4.")
(* [comment removed for export] *).
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
(* [comment removed for export] *)
Hypothesis SINV_sp : forall E M, SINV E M -> uE_sp0 E = SP0.

(* [comment removed for export] *)
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs, env_agree nx0 E E' -> HOLES h E fs = HOLES h E' fs.
Hypothesis HOLES_nil : forall h E fs, HOLES h E fs [].
(* [comment removed for export] *)
Variable FS0 : Fs.Fs.

(* [comment removed for export] *)
Variable KC : nat.

#[local] Notation CHECK := (AP.check SEGS IT A nx0 LIMIT XN XE XB HS KC).

#[local] Notation cfg := (cfg_of SEGS).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Wz (fd : Z) (bs : list Z) : list event := map (fun z => WriteEv (Z_to_bv 64 fd) (Z_to_bv 8 z)) bs.
(* [comment removed for export] *)
Definition piece_den (E : env) (p : spiece) : list byte :=
  match p with SPLit bs => map (Z_to_bv 8) bs | SPBlob k => eb E k end.
Definition Wp (E : env) (fd : Z) (ps : list spiece) : list event :=
  map (WriteEv (Z_to_bv 64 fd)) (flat_map (piece_den E) ps).

(* [comment removed for export] *)
Fixpoint sd (D : TSet) (E : env) (fs : Fs.Fs) (s : shape) : TSet :=
  match s with
  | SNil => t_nil
  | SExit c => t_exit (Z_to_bv 64 c) fs
  | SEmitP fd ps s' => t_emit (Wp E fd ps) (sd D E fs s')
  | SAlt2 a b => t_alt2 (sd D E fs a) (sd D E fs b)
  | SCase e mid s1 s2 => if (bv_unsigned (edenot E e) <=? mid)%Z then sd D E fs s1 else sd D E fs s2
  | SHole h => HOLES h E fs
  | SNext => D
  end.

(* [comment removed for export] *)
Definition sh_lo (E : env) (p : expr * expr) : Z := shadow_off A + uE E (fst p) / 8.
Definition sh_hi (E : env) (p : expr * expr) : Z := shadow_off A + (uE E (fst p) + uE E (snd p)) / 8.

(* [comment removed for export] *)
Definition allow1 (E : env) (p : expr * expr) : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "(26.(11.$1.$1.)(27.$1.$1.(28.(6.O2.(16.$29.$29.O1.)))(2:.(18.(6.O2.(16.$29.$29.O1.))(6.O2.(19.$29.$29.O1.)))))(26.(11.$1.$1.)(27.$1.$1.(28.(2;.O2.O1.))(2:.(2<.O2.O1.)))(2=.(11.$1.$1.))))")
(* [comment removed for export] *).
(* [comment removed for export] *)
Definition allow_sh (E : env) (p : expr * expr) : list (Z * Z) := [(pagedown (sh_lo E p), pageup (sh_hi E p))].
Definition allowA (E : env) (cs : acs) : list (Z * Z) := flat_map (allow1 E) (a_vis cs) ++ flat_map (allow_sh E) (a_ghost cs).

Definition amap_den (E : env) (m : amap) : word * word := (edenot E (am_base m), edenot E (am_len m)).

(* [comment removed for export] *)
Definition in_vis (E : env) (cs : acs) (z : Z) : bool :=
  existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool (a_vis cs).
Definition in_sh (E : env) (cs : acs) (z : Z) : bool :=
  existsb (fun p => (sh_lo E p <=? z) && (z <? sh_hi E p))%bool (a_vis cs).
Definition in_allow (E : env) (cs : acs) (z : Z) : bool := (in_vis E cs z || in_sh E cs z)%bool.

(* [comment removed for export] *)
Definition in_ghostl (E : env) (cs : acs) (z : Z) : bool :=
  existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool (a_ghost cs).
Definition in_band (z : Z) : bool := ((shadow_off A <=? z) && (z <? shadow_off A + BAND_LEN))%bool.
Definition in_ghost (E : env) (cs : acs) (z : Z) : bool := (in_ghostl E cs z && negb (in_band z))%bool.

#[using="Type"] Lemma in_ghost_of_l : forall E E' cs cs', in_ghostl E' cs' = in_ghostl E cs -> in_ghost E' cs' = in_ghost E cs.
Proof. intros E E' cs cs' H. apply functional_extensionality. intros z. unfold in_ghost. rewrite H. reflexivity. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma in_ghost_app_false : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.Pcs',$2>.Pl,(2?.(11.$29.$29.))Pz,$1.P,(3.(2?.(11.$29.$29.))(30.R3.)(31.(11.$29.$29.)(30.R4.)R2.))P,(3.$20.(32.R6.R4.R2.)$33.)(3.$20.(32.R7.R6.R3.)$33.)")
(* [comment removed for export] *).
Proof.
  intros E cs cs' l z Hg H. unfold in_ghost, in_ghostl in *. rewrite Hg, existsb_app in H.
  destruct (negb (in_band z)); [|rewrite andb_false_r; reflexivity]. rewrite andb_true_r in *.
  apply orb_false_iff in H as [H _]. exact H.
Qed.
#[using="Type"] Lemma in_ghost_incl_false : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.Pcs',$2>.Pz,$1.P,Pp,(11.$29.$29.)P,(34.(11.$29.$29.)R1.(30.R4.))(34.(11.$29.$29.)R2.(30.R4.))P,(3.$20.(32.R5.R3.R2.)$33.)(3.$20.(32.R6.R5.R3.)$33.)")
(* [comment removed for export] *).
Proof.
  intros E cs cs' z Hincl H. unfold in_ghost, in_ghostl in *.
  destruct (negb (in_band z)); [|rewrite andb_false_r; reflexivity]. rewrite andb_true_r in *.
  destruct (existsb _ (a_ghost cs)) eqn:X; [|reflexivity]. exfalso.
  apply existsb_exists in X as [q [Hq Hzq]].
  assert (Y : existsb (fun p0 : expr * expr => (uE E (fst p0) <=? z) && (z <? uE E (fst p0) + uE E (snd p0)))%bool (a_ghost cs') = true).
  { apply existsb_exists. exists q. split; [exact (Hincl q Hq) | exact Hzq]. }
  rewrite Y in H. discriminate H.
Qed.
#[using="Type"] Lemma in_ghost_false_band : forall E cs z, in_band z = true -> in_ghost E cs z = false.
Proof. intros E cs z H. unfold in_ghost. rewrite H. apply andb_false_r. Qed.

(* [comment removed for export] *)
Definition vis (E : env) (cs : acs) (model : Model) (a : word) : bool := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Zh,$35.(36.O2.)Zz,$1.(15.&40.O1.)(37.(37.(38.VA,R1.)(14.$39.R1.))(13.(13.(21.R1.(3:.R2.))(3;.(21.R1.(3<.R2.))))(37.(3;.(3=.(3>.O1.)(3?.O2.)))(40.O4.O3.R1.))))")
(* [comment removed for export] *).

Definition hid (E : env) (cs : acs) (model : Model) (a : word) : bool :=
  (argH E a || negb (vis E cs model a))%bool.

(* [comment removed for export] *)
Definition Mr (E : env) (cs : acs) (model : Model) (FULL : word -> option byte) : word -> option byte :=
  mrestrict (hid E cs model) FULL.

Definition fds_std : list (word * FdEntry) := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "(26.(11.(12.&40.)$41.)(27.(12.&40.)$41.(42.&40.=)(43.(42.&40.=)))(26.(11.(12.&40.)$41.)(27.(12.&40.)$41.(42.&40.+1.)(43.(42.&40.+1.)))(26.(11.(12.&40.)$41.)(27.(12.&40.)$41.(42.&40.+2.)(43.(42.&40.+2.)))(2=.(11.(12.&40.)$41.)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition CH : nat := Z.to_nat 65536.
Definition chunk (j : nat) (c : list byte) : list byte := firstn CH (skipn (CH * j) c).
Definition flen (c : list byte) : Z := Z.min (Z.of_nat (length c)) (2 ^ 26).
Definition fds3 (e : FdEntry) : list (word * FdEntry) := (Z_to_bv 64 3, e) :: fds_std.
Definition fds_ok (E : env) (f : afd) (model : Model) : Prop :=
  match f with
  | AP.FdStd => m_fds model = fds_std
  | AP.FdDir => m_fds model = fds3 State.FdDir
  | AP.FdFile k len off => exists p c,
        m_fds model = fds3 (State.FdFile p (edenot E off)) /\ fs_lookup (m_fs model) p = Some c
     /\ uE E len = flen c /\ uE E off <= uE E len
     /\ (forall j, (65536 * Z.of_nat j < 2 ^ 26)%Z -> eb E (k + j)%nat = chunk j c)
  end.

(* [comment removed for export] *)
Fixpoint maps_match (E : env) (ms : list amap) (l : list (word * word)) : Prop :=
  match ms with
  | [] => l = []
  | m :: ms' =>
      if is_fog m       (* [comment removed for export] *)
      then maps_match E ms' l
           \/ exists iv l', l = iv :: l' /\ bv_unsigned (snd iv) <= uE E (am_len m) /\ maps_match E ms' l'
      else exists l', l = amap_den E m :: l' /\ maps_match E ms' l'
  end.

(* [comment removed for export] *)
Definition hole_ok (E : env) (ylo : Z) (l : list (word * word)) (m : amap) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "P,(3.$20.(44.O1.)$22.)(5.Piv,(11.(12.&40.)(12.&40.))P,(34.(11.(12.&40.)(12.&40.))R1.O2.)(1:.(2.(18.(15.&40.(16.(12.&40.)(12.&40.)R2.))(15.&40.(19.(12.&40.)(12.&40.)R2.)))(6.O4.(45.O1.)))(2.(18.(6.O4.(45.O1.))(6.O4.(46.O1.)))(15.&40.(16.(12.&40.)(12.&40.)R2.))))(1:.(2.(18.(6.O4.(45.O1.))(6.O4.(46.O1.)))$47.)(2.O3.(6.O4.(45.O1.)))))")
(* [comment removed for export] *).
#[using="Type"] Lemma holes_mono : forall E y y' l ms,
  Forall (hole_ok E y l) ms -> y' <= y -> Forall (hole_ok E y' l) ms.
Proof.
  intros E y y' l ms H Hy. apply Forall_forall. intros m Hm Hh.
  destruct (proj1 (Forall_forall _ _) H m Hm Hh) as [H1 H2]. split; [exact H1 | lia].
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma holes_sublist : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Py,$1.Pl,(2?.(11.(12.&40.)(12.&40.)))Pl',(2?.(11.(12.&40.)(12.&40.)))Pms,(2?.$48.)P,(1;.$48.(49.R5.R4.R3.)R1.)P,Piv,(11.(12.&40.)(12.&40.))P,(34.(11.(12.&40.)(12.&40.))R1.R4.)(34.(11.(12.&40.)(12.&40.))R2.R6.)(1;.$48.(49.R7.R6.R4.)R3.)")
(* [comment removed for export] *).
Proof.
  intros E y l l' ms H Hs. apply Forall_forall. intros m Hm Hh.
  destruct (proj1 (Forall_forall _ _) H m Hm Hh) as [H1 H2]. split; [intros iv Hiv; apply H1; apply Hs; exact Hiv | exact H2].
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma holes_none : forall E y l ms, Forall (fun m => is_hole m = false) ms -> Forall (hole_ok E y l) ms.
Proof. intros E y l ms H. apply Forall_forall. intros m Hm Hh. pose proof (proj1 (Forall_forall _ _) H m Hm) as X. congruence. Qed.

(* [comment removed for export] *)
Definition zB (e : word * word) : Z := bv_unsigned (fst e).
Definition zE (e : word * word) : Z := bv_unsigned (fst e) + bv_unsigned (snd e).
Definition born (E : env) (ms : list amap) (ks : list mkind) (iv : word * word) : Prop :=
  exists m, In m ms /\ is_fog m = false /\ In (am_kind m) ks /\ amap_den E m = iv.
Definition nlz_ok (E : env) (ms : list amap) (ks : list mkind) (M X : list (word * word)) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pe,(11.(12.&40.)(12.&40.))P,(34.(11.(12.&40.)(12.&40.))R1.O1.)(5.(1?.=(15.&40.(19.(12.&40.)(12.&40.)R2.)))(4:.(11.(12.&40.)(12.&40.))Liv,(11.(12.&40.)(12.&40.))(5.(34.(11.(12.&40.)(12.&40.))R1.O2.)(5.(2.(4;.R1.)(4;.R3.))(5.(2.(4<.R3.)(4<.R1.))(24.(4=.O5.O4.O3.R1.)))))))")
(* [comment removed for export] *).
Definition K_NOTNONE : list mkind := [KRW; KRWLAZY].   (* [comment removed for export] *)
Definition K_EAGER : list mkind := [KRW; KNONE; KMIXED].        (* [comment removed for export] *)
#[using="Type"] Lemma existsb_mkind_In : forall k l, existsb (mkind_eqb k) l = true -> In k l.
Proof. intros k l H. apply existsb_exists in H as (k' & Hin & E). destruct k, k'; cbn in E; try discriminate E; exact Hin. Qed.
Definition sub_ok (E : env) (M N Lz : list (word * word)) (t : expr * expr) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Zlo,$1.(6.O5.(16.$29.$29.O1.))Zn,$1.(6.O5.(19.$29.$29.O1.))(5.(1?.=R1.)(5.(4:.(11.(12.&40.)(12.&40.))Liv,(11.(12.&40.)(12.&40.))(5.(34.(11.(12.&40.)(12.&40.))R1.O4.)(5.(2.(4;.R1.)R3.)(2.(18.R3.R2.)(4<.R1.)))))(5.Pe,(11.(12.&40.)(12.&40.))P,(34.(11.(12.&40.)(12.&40.))R1.O3.)(1:.(2.(4<.R2.)R4.)(2.(18.R4.R3.)(4;.R2.)))Pe,(11.(12.&40.)(12.&40.))P,(34.(11.(12.&40.)(12.&40.))R1.O2.)(1:.(2.(4<.R2.)R4.)(2.(18.R4.R3.)(4;.R2.))))))")
(* [comment removed for export] *).
(* [comment removed for export] *)
Definition K_DEF : list mkind := [KRW; KRWLAZY].
Definition def_ok (E : env) (FULL : word -> option byte) (m : amap) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "P,(3.$20.(4>.O1.)$33.)P,(34.$4?.(50.O1.)$51.)Pa,(12.&40.)P,(5.(2.(15.&40.(52.O3.(45.O1.)))(15.&40.R1.))(1?.(15.&40.R1.)(18.(15.&40.(52.O3.(45.O1.)))(15.&40.(52.O3.(46.O1.))))))(24.(3.(23.(12.&8.))A1.O2.R2.(25.(12.&8.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition K_NLZ : list mkind := [KNONELAZY; KMIXEDL].
Definition in_tok (E : env) (z : Z) (t : expr * expr) : Prop := uE E (fst t) <= z < uE E (fst t) + uE E (snd t).
Definition cov_ok (E : env) (N : list (word * word)) (sub : list (expr * expr)) (m : amap) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "P,(34.$4?.(50.O1.)$53.)Pz,$1.P,(5.(2.(6.O4.(45.O1.))R1.)(1?.R1.(18.(6.O4.(45.O1.))(6.O4.(46.O1.)))))(1:.(3.$20.(21.R2.O3.)$22.)(4:.(11.$29.$29.)Lt,(11.$29.$29.)(5.(34.(11.$29.$29.)R1.O2.)(54.O4.R3.R1.))))")
(* [comment removed for export] *).

Record cs_ok (E : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model) : Prop := CS_OK {
  (* [comment removed for export] *)
  co_regs  : regs_ok E (s_regs (a_ss cs)) R;
  co_log   : s_log (a_ss cs) = [];
  co_know  : know_ok SEGS E (Mr E cs model FULL) (kn cs);
  (* [comment removed for export] *)
  co_halt  : m_halted model = None;
  co_fds   : fds_ok E (a_fd cs) model;
  co_fs    : m_fs model = FS0;
  co_tid   : a_tidset cs = false -> m_tid model = None;
  co_res   : vm_reserved (m_vmmaps model) = segments_reserved SEGS;
  co_limit : vm_limit (m_vmmaps model) = LIMIT;
  (* [comment removed for export] *)
  co_maps  : maps_match E (a_maps cs) (vm_maps (m_vmmaps model));
  co_holes : Forall (hole_ok E (a_ylo cs) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) (a_maps cs);   (* [comment removed for export] *)
  co_seps  : seps (vm_maps (m_vmmaps model));
  co_wf    : model_ivs_wf model;
  co_bounds : Forall (fun iv => 0 < bv_unsigned (snd iv)
                                /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                                /\ hull_apart A (bv_unsigned (fst iv)) (bv_unsigned (snd iv))
                                /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ATOP
                                /\ 0 < bv_unsigned (fst iv)) (vm_maps (m_vmmaps model));   (* [comment removed for export] *)
  co_lazyb : Forall (fun iv => hull_apart A (bv_unsigned (fst iv)) (bv_unsigned (snd iv))
                               /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ATOP) (m_vm_lazy model);          (* [comment removed for export] *)
  co_nasub : forall z, in_ivs z (vm_noaccess (m_vmmaps model)) = true -> in_ivs z (vm_maps (m_vmmaps model)) = true;
  co_none  : Forall (fun m => am_kind m = KNONE \/ am_kind m = KNONELAZY ->
               In (amap_den E m) (vm_noaccess (m_vmmaps model))) (a_maps cs);
  co_kinds : Forall (fun m => am_kind m = KRWLAZY ->
               forall a : word, bv_unsigned (edenot E (am_base m)) <= bv_unsigned a < bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) ->
                 in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false
                 /\ page_in_ranges (page_base a) (m_vm_lazy model) = true) (a_maps cs);
  co_totsz : sum_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= a_totsz cs;
  (* [comment removed for export] *)
  co_isp   : bv_unsigned (vm_init_sp (m_vmmaps model)) = SP0;
  co_brk   : vm_brk (m_vmmaps model) = edenot E (a_brk cs);
  co_sbrk  : bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned (vm_brk (m_vmmaps model));
  (* [comment removed for export] *)
  co_eager : eager_used model <= a_eager cs;
  co_abytes : A_bytes (allowA E cs) <= a_abytes cs;
  co_minv  : MInv (allowA E cs) model;
  (* [comment removed for export] *)
  co_zero  : forall a : word, hid E cs model a = true ->
               in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true ->
               in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false ->
               page_in_ranges (page_base a) (m_vm_lazy model) = true ->
               in_ghost E cs (bv_unsigned a) = false ->
               FULL a = Some (Z_to_bv 8 0);
  co_sinv  : SINV E FULL;
  (* [comment removed for export] *)
  co_nk    : nlz_ok E (a_maps cs) K_NOTNONE (vm_maps (m_vmmaps model)) (vm_noaccess (m_vmmaps model));
  co_lzk   : nlz_ok E (a_maps cs) K_EAGER (vm_maps (m_vmmaps model)) (m_vm_lazy model);
  co_sub   : Forall (sub_ok E (vm_maps (m_vmmaps model)) (vm_noaccess (m_vmmaps model)) (m_vm_lazy model)) (a_sub cs);
  (* [comment removed for export] *)
  co_def   : Forall (def_ok E FULL) (a_maps cs);
  (* [comment removed for export] *)
  co_nn    : forall a : word, in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = true -> FULL a = None;
  co_cov   : Forall (cov_ok E (vm_noaccess (m_vmmaps model)) (a_sub cs)) (a_maps cs)
}.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="HS XN XE XB KC"] Lemma A_wf_allowA : forall E cs, A_wf (allowA E cs).
Proof.
  intros E cs. unfold A_wf, allowA. apply Forall_forall. intros iv Hin.
  assert (SH : forall p, iv = (pagedown (sh_lo E p), pageup (sh_hi E p)) -> fst iv <= snd iv /\ fst iv mod page_size = 0 /\ snd iv mod page_size = 0).
  { intros p ->. cbn [fst snd]. unfold page_size.
    pose proof (u64_range (edenot E (snd p))) as Hn. pose proof (u64_range (edenot E (fst p))) as Hb.
    pose proof (pagedown_le (sh_lo E p)). pose proof (pageup_ge (sh_hi E p)). unfold sh_lo, sh_hi, uE in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  apply in_app_iff in Hin as [Hin|Hin]; apply in_flat_map in Hin as [p [_ Hin]].
  - unfold allow1 in Hin.
    pose proof (u64_range (edenot E (snd p))) as Hn. pose proof (u64_range (edenot E (fst p))) as Hb.
    destruct Hin as [<-|[E1|[]]]; [cbn [fst snd]; unfold page_size | exact (SH p (eq_sym E1))].
    pose proof (pagedown_le (uE E (fst p))). pose proof (pageup_ge (uE E (fst p) + uE E (snd p))). unfold uE in *.
    split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
  - unfold allow_sh in Hin. destruct Hin as [E1|[]]. exact (SH p (eq_sym E1)).
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma allow_sh_le : forall E p, A_bytes (allow_sh E p) <= A_bytes (allow1 E p).
Proof.
  intros E p. unfold allow_sh, allow1. cbn [A_bytes fst snd].
  pose proof (pagedown_le (uE E (fst p))). pose proof (pageup_ge (uE E (fst p) + uE E (snd p))). pose proof (u64_range (edenot E (snd p))). unfold uE in *. lia.
Qed.
#[using="Type"] Lemma allow_sh_in1 : forall E p iv, In iv (allow_sh E p) -> In iv (allow1 E p).
Proof. intros E p iv H. unfold allow_sh, allow1 in *. destruct H as [<-|[]]. right. left. reflexivity. Qed.
#[using="Type"] Lemma A_bytes_fm_sh_le : forall E l, A_bytes (flat_map (allow_sh E) l) <= A_bytes (flat_map (allow1 E) l).
Proof.
  intros E l. induction l as [|p l IH]; cbn [flat_map]; [cbn; lia|].
  assert (AP : forall l1 l2, A_bytes (l1 ++ l2) = A_bytes l1 + A_bytes l2) by (intros l1 l2; induction l1 as [|x l1 IH1]; cbn [app A_bytes]; [lia| rewrite IH1; lia]).
  rewrite !AP. pose proof (allow_sh_le E p). lia.
Qed.

#[using="HS XN XE XB KC"] Lemma page_base_le : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pa,(12.&40.)(5.(2.(15.&40.(3>.R1.))(15.&40.R1.))(5.(1?.(15.&40.R1.)(18.(15.&40.(3>.R1.))+1000.))(3.$1.(:.(15.&40.(3>.R1.))+1000.)=)))")
(* [comment removed for export] *).
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
  rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
#[using="HS XN XE XB KC"] Lemma page_in_ranges_bounds : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pa,(12.&40.)Pl,(2?.(11.(12.&40.)(12.&40.)))Plo,$1.Phi,$1.P,(1;.(11.(12.&40.)(12.&40.))Liv,(11.(12.&40.)(12.&40.))(5.(2.R3.(15.&40.(16.(12.&40.)(12.&40.)R1.)))(2.(18.(15.&40.(16.(12.&40.)(12.&40.)R1.))(15.&40.(19.(12.&40.)(12.&40.)R1.)))R2.))R3.)P,(3.$20.(3=.(3>.R5.)R4.)$22.)(5.(2.R4.(15.&40.R6.))(2.(18.(15.&40.R6.)+1.)(18.R3.+???.)))")
(* [comment removed for export] *).
Proof.
  intros a l lo hi Hl Hp. unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hin Hb]].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) Hl iv Hin) as [L1 L2].
  pose proof (page_base_le a) as (P1 & P2 & P3). unfold page_size in H2. lia.
Qed.

#[using="HS XN XE XB HULL_ok KC"] Lemma lazy_cover_cs : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.P,(57.R5.R4.R3.R2.R1.)(58.(59.R6.R5.R2.)(3?.R2.)(5:.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model HC w Hlz Hh. unfold hid in Hh. apply orb_false_iff in Hh as [Ha Hv].
  apply negb_false_iff in Hv. unfold vis in Hv.
  pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (H0 & H1 & H2 & H3).
  apply orb_prop in Hv as [Hv|Hv].
  - (* [comment removed for export] *)
    exfalso.
    pose proof Hlz as Hlz0. unfold page_in_ranges in Hlz0. apply existsb_exists in Hlz0 as [iv [Hin Hb]].
    apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
    pose proof (proj1 (Forall_forall _ _) (co_lazyb _ _ _ _ _ HC) iv Hin) as [L1 L2]. unfold hull_apart in L1.
    pose proof (page_base_le w) as (P1 & P2 & P3). unfold page_size in *.
    apply orb_prop in Hv as [Hv|Hv].
    + unfold in_hull in Hv. apply andb_prop in Hv as [Hv1 Hv2]. apply Z.leb_le in Hv1. apply Z.ltb_lt in Hv2. lia.
    + apply Z.leb_le in Hv. lia.
  - apply andb_prop in Hv as [_ Hv]. rewrite Hlz in Hv. cbn [negb orb] in Hv.
    (* [comment removed for export] *)
    pose proof (page_base_le w) as (P1 & P2 & P3).
    unfold page_allowedb, allowA. apply existsb_exists. unfold page_size.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    unfold in_allow in Hv. apply orb_prop in Hv as [Hv|Hv].
    + unfold in_vis in Hv. apply existsb_exists in Hv as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
      apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
      exists (pagedown (uE E (fst p)), pageup (uE E (fst p) + uE E (snd p))). split.
      * apply in_or_app. left. apply in_flat_map. exists p. split; [exact Hin|]. left. reflexivity.
      * cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
    + unfold in_sh in Hv. apply existsb_exists in Hv as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
      apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
      exists (pagedown (sh_lo E p), pageup (sh_hi E p)). split.
      * apply in_or_app. left. apply in_flat_map. exists p. split; [exact Hin|]. right. left. reflexivity.
      * cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

#[using="SEGS_in_hull HULL_ok SP0_ok argH_high"] Lemma H_off_segments_cs : forall E cs model, H_off_segments SEGS (hid E cs model).
Proof.
  intros E cs model a Hh. unfold hid in Hh. apply orb_prop in Hh as [Ha|Hv].
  - apply SEGS_in_hull. unfold in_hull. pose proof (argH_high _ _ Ha). pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (?&?&?&?).
    atopb. unfold CEIL, KHI in *. apply andb_false_iff. right. apply Z.ltb_ge. lia.
  - apply negb_true_iff in Hv. unfold vis in Hv. apply orb_false_iff in Hv as [Hv _]. apply orb_false_iff in Hv as [Hv _].
    apply SEGS_in_hull. exact Hv.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma mrestrict_munrestrict_clean : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PH,P,(12.&40.)$20.PFULL,P,(12.&40.)(23.(12.&8.))Pm',Px,(12.&40.)(23.(12.&8.))P,Pa,(12.&40.)P,(3.$20.A1.R4.R1.$22.)(3.(23.(12.&8.))A1.R3.R2.(25.(12.&8.)))(3.P,(12.&40.)(23.(12.&8.))(5;.R4.(5<.R4.R3.R2.))R2.)")
(* [comment removed for export] *).
Proof.
  intros H FULL m' Hc. apply functional_extensionality. intros a.
  unfold mrestrict, munrestrict. destruct (H a) eqn:Ha; [symmetry; apply Hc; exact Ha | reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma vis_same : forall E cs model model',
  same_but_materialized model model' -> vis E cs model' = vis E cs model.
Proof.
  intros E cs model model' Hs. pose proof (same_but_materialized_frame _ _ Hs) as Hfr.
  apply functional_extensionality. intros a. unfold vis.
  replace (m_vmmaps model') with (m_vmmaps model) by (symmetry; apply Hfr).
  replace (m_vm_lazy model') with (m_vm_lazy model) by (symmetry; apply Hfr). reflexivity.
Qed.

#[using="Type"] Lemma hid_same : forall E cs model model',
  same_but_materialized model model' -> hid E cs model' = hid E cs model.
Proof. intros. unfold hid. apply functional_extensionality. intros a. rewrite (vis_same _ _ _ _ H). reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma vis_ext : forall E cs cs' model,
  a_vis cs' = a_vis cs -> vis E cs' model = vis E cs model.
Proof. intros E cs cs' model Ha. apply functional_extensionality. intros a. unfold vis, in_allow, in_vis, in_sh. rewrite Ha. reflexivity. Qed.
#[using="Type"] Lemma hid_ext : forall E cs cs' model,
  a_vis cs' = a_vis cs -> hid E cs' model = hid E cs model.
Proof. intros. unfold hid. apply functional_extensionality. intros a. rewrite (vis_ext _ _ _ _ H). reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma noacc_hid : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pa,(12.&40.)P,(57.R6.R5.R4.R3.R2.)P,(3.$20.(21.(15.&40.R2.)(3<.(36.R3.)))$22.)(3.$20.(59.R8.R7.R4.R3.)$22.)")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model a HC Hn. pose proof (co_nasub _ _ _ _ _ HC _ Hn) as Hm.
  unfold hid, vis. rewrite Hm, Hn. cbn [negb andb orb].
  unfold in_ivs in Hm. apply existsb_exists in Hm as (iv & Hiv & Hz). apply andb_prop in Hz as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2.
  pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ HC) iv Hiv) as (_ & _ & _ & HA & HT & _). unfold hull_apart in HA.
  replace (in_hull A (bv_unsigned a)) with false by (symmetry; unfold in_hull; apply andb_false_iff; destruct HA as [HA|HA]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
  replace (ATOP <=? bv_unsigned a) with false by (symmetry; apply Z.leb_gt; lia).
  cbn [orb negb]. apply orb_true_r.
Qed.

(* [comment removed for export] *)
#[using="SINV_frame"] Lemma cs_ok_frame : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pss',$5=.PR',(55.&5.(12.&40.))PFULL',P,(12.&40.)(23.(12.&8.))Pmodel',$56.P,(57.R9.R8.R7.R6.R5.)P,(5>.R6.R2.)P,(5?.(5:.R;.R:.)R3.)P,(60.R<.(61.R7.)R6.)P,(3.(2?.$62.)(63.R8.)(2=.$62.))P,(64.VSEGS,R>.(65.R>.R=.R:.R7.)(66.R9.))P,Pa,(12.&40.)P,(3.$20.(59.R10.R?.R<.R1.)$22.)(3.(23.(12.&8.))A1.R:.R2.A1.R>.R2.)P,Pa,(12.&40.)P,(24.(3.(23.(12.&8.))A1.R>.R1.(25.(12.&8.))))(24.(3.(23.(12.&8.))A1.R;.R2.(25.(12.&8.))))(57.R11.(67.R10.R<.)R;.R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model ss' R' FULL' model' HC Hs Hinv HR HL HK Hhid Hdom.
  pose proof (same_but_materialized_frame _ _ Hs) as Hfr.
  assert (Evm : m_vmmaps model' = m_vmmaps model) by apply Hfr.
  assert (Elz : m_vm_lazy model' = m_vm_lazy model) by apply Hfr.
  pose proof (fun a => noacc_hid E cs R FULL model a HC) as NH.
  destruct HC. constructor; cbn [with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset kn];
    rewrite ?Evm, ?Elz; try assumption.
  - unfold Mr. rewrite (hid_same _ _ _ _ Hs). exact HK.
  - replace (m_halted model') with (m_halted model) by (symmetry; apply Hfr). assumption.
  - unfold fds_ok in *. replace (m_fds model') with (m_fds model) by (symmetry; apply Hfr).
    replace (m_fs model') with (m_fs model) by (symmetry; apply Hfr). assumption.
  - replace (m_fs model') with (m_fs model) by (symmetry; apply Hfr). assumption.
  - intros Ht. replace (m_tid model') with (m_tid model) by (symmetry; apply Hfr). auto.
  - unfold model_ivs_wf in *. rewrite Evm, Elz. assumption.
  - replace (eager_used model') with (eager_used model) by (symmetry; apply Hfr). assumption.
  - intros a Hh. rewrite (hid_same _ _ _ _ Hs) in Hh. rewrite (Hhid a Hh). auto.
  - eapply SINV_frame; [| intros a0 _ D0; exact (Hdom a0 D0) | eassumption]. intros a Ha. apply Hhid. unfold hid. rewrite Ha. reflexivity.
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hf Hk a Ha. apply Hdom. exact (proj1 (Forall_forall _ _) co_def0 m Hin Hf Hk a Ha).
  - (* [comment removed for export] *) intros a Hn. rewrite (Hhid a (NH a Hn)). auto.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma know_ok_filter : forall E M f k, know_ok SEGS E M k -> know_ok SEGS E M (List.filter f k).
Proof.
  intros E M f k HK. unfold know_ok in *. apply Forall_forall. intros K Hin.
  apply filter_In in Hin as [Hin _]. exact (proj1 (Forall_forall _ _) HK K Hin).
Qed.

#[using="Type"] Lemma cs_ok_set_kn : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pk',(2?.$68.)P,(57.R6.R5.R4.R3.R2.)P,(64.VSEGS,R7.(65.R7.R6.R3.R4.)R2.)(57.R8.(69.R7.R3.)R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model k' HC HK.
  destruct HC; constructor; cbn [set_kn with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know];
    try assumption; reflexivity.
Qed.

#[using="Type"] Lemma cs_gc_ok : forall gb E cs R FULL model, cs_ok E cs R FULL model -> cs_ok E (cs_gc gb cs) R FULL model.
Proof.
  intros gb E cs R FULL model HC. unfold cs_gc. destruct (split_lit (reg cs 2)) as [spb spk].
  apply cs_ok_set_kn; [exact HC|]. apply know_ok_filter. exact (co_know _ _ _ _ _ HC).
Qed.

#[using="Type"] Lemma mk_itab_ranges_acc_sound : forall rs t, itab_sound SEGS t -> itab_sound SEGS (mk_itab_ranges_acc SEGS rs t).
Proof.
  induction rs as [|[lo n] rs IH]; intros t Ht; cbn [mk_itab_ranges_acc]; [exact Ht|].
  apply IH. apply mk_itab_fuel_sound. exact Ht.
Qed.
#[using="Type"] Lemma mk_itab_ranges_sound : forall rs, itab_sound SEGS (mk_itab_ranges SEGS rs).
Proof.
  intros rs. unfold mk_itab_ranges. apply mk_itab_ranges_acc_sound.
  intros pc i. unfold itab_lookup. destruct pc; try discriminate. rewrite pt_get_leaf. discriminate.
Qed.

#[using="Type"] Lemma pc_set_kn : forall cs k, pc (set_kn cs k) = pc cs.
Proof. reflexivity. Qed.
#[using="Type"] Lemma pc_cs_gc : forall gb cs, pc (cs_gc gb cs) = pc cs.
Proof. intros gb cs. unfold cs_gc. destruct (split_lit (reg cs 2)); reflexivity. Qed.

#[using="Type"] Lemma drop_ixs_incl : forall ixs i k K, In K (drop_ixs ixs i k) -> In K k.
Proof.
  intros ixs i k. revert i. induction k as [|K' r IH]; intros i K Hin; cbn [drop_ixs] in Hin.
  - exact Hin.
  - destruct (existsb (Nat.eqb i) ixs).
    + right. eapply IH. exact Hin.
    + destruct Hin as [<-|Hin]; [left; reflexivity | right; eapply IH; exact Hin].
Qed.

#[using="Type"] Lemma forget_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pixs,(2?.$6:.)P,(57.R6.R5.R4.R3.R2.)(57.R7.(69.R6.(6;.R2.#0.(6<.R6.)))R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model ixs HC. apply cs_ok_set_kn; [exact HC|].
  unfold know_ok. apply Forall_forall. intros K Hin. apply drop_ixs_incl in Hin.
  exact (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ HC) K Hin).
Qed.

(* [comment removed for export] *)
Definition kfoot (E : env) (K : kentry) : option (Z * Z) :=
  match K with
  | KWord a w _ => Some (estart E a, Z.of_nat w)
  | KZero a l => Some (estart E a, elenZ E l)
  | KBlob a l _ => Some (estart E a, elenZ E l)
  | KImg lo hi => Some (lo, hi - lo)%Z
  | KWr a n => Some (estart E a, elenZ E n)
  | KFill a l _ => Some (estart E a, elenZ E l)
  | KUnk a l => Some (estart E a, elenZ E l)
  | KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => None
  end.

Definition kfoot_apart (E : env) (K : kentry) (lo n : Z) : Prop :=
  match kfoot E K with
  | None => True
  | Some (s, l) => (s + l <= lo \/ lo + n <= s)%Z
  end.

#[using="Type"] Lemma kentry_keep_sem : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))PM',Px,(12.&40.)(23.(12.&8.))PK,$68.Plo,$1.Pn,$1.P,(6=.VSEGS,R6.R5.R3.)P,(6>.R7.R4.R3.R2.)P,Px,(12.&40.)P,(1:.(1?.(15.&40.R1.)R5.)(2.(18.R5.R4.)(15.&40.R1.)))(3.(23.(12.&8.))A1.R8.R2.A1.R9.R2.)(6=.VSEGS,R9.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros E M M' K lo n HK Hap Hout.
  assert (RD : forall (a : word) k, (bv_unsigned a + Z.of_nat k <= 2 ^ 64)%Z ->
     (bv_unsigned a + Z.of_nat k <= lo \/ lo + n <= bv_unsigned a)%Z ->
     rdn SEGS M' a k = rdn SEGS M a k).
  { intros a k Hnw Hd. apply rdn_ext; [exact Hnw|]. intros x Hx. apply Hout. lia. }
  unfold kfoot_apart, kfoot in Hap.
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2|[b k] nn fc|[b k] nn]; cbn [kentry_ok] in *;
    try exact HK.
  7: { (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia. }
  6: { (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia. }
  - (* [comment removed for export] *) destruct HK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
    rewrite RD; [exact Hrd | rewrite (flat_u E _ _ Hfl); destruct Hfl; lia | rewrite (flat_u E _ _ Hfl); lia].
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as (HA & HB & HC). split; [exact HA|]. split; [exact HB|]. intros i Hi.
    rewrite Hout; [apply HC; lia|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as [Hfl Hs]. split; [exact Hfl|]. intros d m Hd0 Hdm.
    pose proof (Hs d m Hd0 Hdm) as H. destruct Hfl as (F1 & F2 & F3 & F4).
    destruct m as [|m']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia.
    unfold wview. rewrite Hout by lia. fold (wview SEGS M x).
    eapply (store_ok_all SEGS M (Datatypes.S m')); [| exact H |]; rewrite u64_lit by lia; lia.
Qed.

#[using="Type"] Lemma elenZ_lit : forall E z, (0 <= z < 2 ^ 64)%Z -> elenZ E (ELit z) = z.
Proof. intros E z Hz. unfold elenZ. cbn [edenot]. rewrite u64_lit by lia. reflexivity. Qed.

#[using="Type"] Lemma kentry_apart_b_sem : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))Pallkn,(2?.$68.)PK,$68.Pub,$29.Puk,$1.Pun,$29.P,(64.VSEGS,R7.R6.R5.)P,(3.$20.(6?.R6.R4.R3.R2.R5.)$22.)(6>.R9.R6.(70.R9.(71.R5.R4.))(72.R9.R3.))")
(* [comment removed for export] *).
Proof.
  intros E M allkn K ub uk un Hall Hb. unfold kfoot_apart, kfoot.
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2|[b k] nn fc|[b k] nn]; cbn [kentry_apart_b] in Hb;
    try exact I; try discriminate.
  7: { pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia. }
  6: { pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia. }
  - apply andb_prop in Hb as [Hw Hb]. apply Nat.leb_le in Hw.
    pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb) as Hd.
    rewrite (elenZ_lit E (Z.of_nat w)) in Hd by lia. lia.
  - pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
  - pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
  - apply andb_prop in Hb as [Hb Hap]. apply andb_prop in Hb as [Hb Hlt]. apply andb_prop in Hb as [H0 Hl].
    apply Z.leb_le in H0. apply Z.leb_le in Hl. apply Z.ltb_lt in Hlt. unfold two64 in Hlt.
    pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hap) as Hd.
    rewrite (elenZ_lit E (ihi - ilo)) in Hd by lia.
    unfold estart in Hd at 2 3. cbn [a_base a_off edenot] in Hd.
    rewrite !u64_lit in Hd by lia. lia.
  - pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
Qed.

#[using="Type"] Lemma kentry_apart_keep : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))PM',Px,(12.&40.)(23.(12.&8.))Pallkn,(2?.$68.)PK,$68.Pub,$29.Puk,$1.Pun,$29.P,(64.VSEGS,R8.R7.R5.)P,(6=.VSEGS,R9.R8.R5.)P,(3.$20.(6?.R7.R5.R4.R3.R6.)$22.)P,Px,(12.&40.)P,(1:.(1?.(15.&40.R1.)(70.R<.(71.R7.R6.)))(2.(18.(70.R<.(71.R7.R6.))(72.R<.R5.))(15.&40.R1.)))(3.(23.(12.&8.))A1.R;.R2.A1.R<.R2.)(6=.VSEGS,R<.R:.R8.)")
(* [comment removed for export] *).
Proof.
  intros E M M' allkn K ub uk un Hall HK Hb Hout.
  eapply kentry_keep_sem; [exact HK | eapply kentry_apart_b_sem; [exact Hall | exact Hb] | exact Hout].
Qed.

#[using="Type"] Lemma know_ok_filter_apart : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))PM',P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)Pf,P,$68.$20.Pub,$29.Puk,$1.Pun,$29.P,(64.VSEGS,R8.R7.R5.)P,PK,$68.P,(34.$68.R1.R7.)P,(3.$20.A1.R7.R2.$22.)(1:.(3.$20.(6?.R9.R7.R6.R5.R3.)$22.)(6=.VSEGS,R<.R:.R3.))P,Px,(12.&40.)P,(1:.(1?.(15.&40.R1.)(70.R;.(71.R6.R5.)))(2.(18.(70.R;.(71.R6.R5.))(72.R;.R4.))(15.&40.R1.)))(3.(23.(12.&8.))A1.R:.R2.A1.R;.R2.)(64.VSEGS,R;.R9.(73.$68.R7.R8.))")
(* [comment removed for export] *).
Proof.
  intros E M M' k f ub uk un HK Hf Hout. unfold know_ok. apply Forall_forall. intros K Hin.
  apply filter_In in Hin as [Hin Hfk].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct (Hf K Hin Hfk) as [Hap | Hdone]; [|exact Hdone].
  eapply kentry_apart_keep; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kentry_apart_bp_eq : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pallkn,(2?.$68.)Pub,$29.Puk,$1.Pun,$29.PK,$68.(3.$20.(74.R5.(75.R5.R4.R3.R2.)R4.R3.R2.R1.)(6?.R5.R4.R3.R2.R1.))")
(* [comment removed for export] *).
Proof.
  intros allkn ub uk un K. destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [kentry_apart_bp kentry_apart_b]; rewrite ?ranges_apart_p_eq; reflexivity.
Qed.

#[using="Type"] Lemma havoc1p_eq : forall k ub uk un K,
  havoc1p k (mk_sprep k ub uk un) ub uk un K = havoc1 k ub uk un K.
Proof. intros. unfold havoc1p, havoc1. rewrite kentry_apart_bp_eq. reflexivity. Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma know_ok_havoc : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))PM',Px,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)Pb,$29.Po,$1.Pn,$29.P,(64.VSEGS,R7.R6.R4.)P,Px,(12.&40.)P,(1:.(1?.(15.&40.R1.)(70.R9.(71.R5.R4.)))(2.(18.(70.R9.(71.R5.R4.))(72.R9.R3.))(15.&40.R1.)))(3.(23.(12.&8.))A1.R8.R2.A1.R9.R2.)P,(76.R8.R7.)(64.VSEGS,R:.R8.(77.R7.R6.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros E M M' k b o n HK Hout Hg. unfold kn_havoc, know_ok. cbv zeta.
  apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK.
  rewrite havoc1p_eq. unfold havoc1.
  destruct (kwr_b K || kentry_apart_b k b o n K)%bool eqn:Hf.
  - apply Forall_one. apply orb_prop in Hf as [Hw|Ha].
    + destruct K as [| | | | | |[wb wk] wn| | |]; try discriminate.
      destruct HKK as [Hfl Hs]. cbn [kentry_ok]. split; [exact Hfl|].
      intros d m Hd Hdm. eapply store_ok_mono; [exact Hg | apply Hs; assumption].
    + eapply kentry_apart_keep; eassumption.
  - destruct K as [|[kb kk] len| | | | | | |[kb kk] len fc|[kb kk] len]; try constructor.
    + eapply kzero_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kfill_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kunk_cut_sound; [exact HK | exact HKK | exact Hout].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pw_kind (mk : saddr -> expr -> kentry) (P : (word -> option byte) -> word -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))Pa,$78.Pn,$29.(79.(6=.VSEGS,R4.R3.A2.O2.R2.R1.)(5.(7:.R4.R2.(72.R4.R1.))Pi,$1.P,(5.(2.=R1.)(1?.R1.(72.R5.R2.)))A2.O1.R5.(42.&40.(18.(70.R6.R4.)R2.))))")
(* [comment removed for export] *).

#[using="Type"] Lemma pw_kind_zf : forall mk byteof, zf_kind SEGS mk byteof -> pw_kind mk (fun M x => byteof (M x)).
Proof. intros mk byteof H E M a n. exact (H E M a n). Qed.

#[using="Type"] Lemma pw_kind_wr : pw_kind KWr (fun M x => wview SEGS M x <> None).
Proof.
  intros E M a n. cbn [kentry_ok]. split; intros [Hfl H]; split; try exact Hfl.
  - intros i Hi. pose proof (H i 1%nat ltac:(lia) ltac:(cbn; lia)) as S1. cbn [store_ok] in S1.
    destruct (wview SEGS M (Z_to_bv 64 (estart E a + i))); [discriminate | discriminate].
  - intros d m Hd Hdm. pose proof Hfl as Hfl0. destruct Hfl as (F1 & F2 & F3 & F4).
    destruct m as [|m']; [reflexivity|]. set (m := Datatypes.S m') in *.
    assert (Hm : 1 <= Z.of_nat m) by (subst m; rewrite Nat2Z.inj_succ; lia).
    assert (Hu : bv_unsigned (Z_to_bv 64 (estart E a + d)) = estart E a + d) by (apply u_small; lia).
    apply store_ok_of_all; rewrite Hu; [lia|].
    intros x Hx. replace x with (Z_to_bv 64 (estart E a + (bv_unsigned x - estart E a))).
    + apply H. lia.
    + apply bv_eq. rewrite u_small; [lia|]. pose proof (u64_range x). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kcut_pw_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pmk,P,$78.P,$29.$68.PP,P,P,(12.&40.)(23.(12.&8.))P,(12.&40.)SpPE,$0.PM0,P,(12.&40.)(23.(12.&8.))PM,P,(12.&40.)(23.(12.&8.))PM',P,(12.&40.)(23.(12.&8.))Pallkn,(2?.$68.)Pwb,$29.Pwk,$1.Pwn,$29.Pkb,$29.Pkk,$1.Plen,$29.P,(7;.R=.R<.)P,(64.VSEGS,R<.R;.R8.)P,(6=.VSEGS,R=.R;.A2.R?.(71.R5.R4.)R3.)P,Px,(12.&40.)P,(1:.(1?.(15.&40.R1.)(70.R?.(71.R:.R9.)))(2.(18.(70.R?.(71.R:.R9.))(72.R?.R8.))(15.&40.R1.)))P,A2.R11.R>.R2.A2.R12.R>.R3.(1;.$68.(6=.VSEGS,R?.R<.)(7<.R11.R;.R:.R9.R8.R7.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros mk P E M0 M M' allkn wb wk wn kb kk len Hkind Hall HK Hout.
  apply (proj1 (Hkind E M _ _)) in HK. destruct HK as [Hfl Hz].
  unfold kcut.
  set (ws := mkAlu ALU_ADD wb (ELit wk)). set (ks := mkAlu ALU_ADD kb (ELit kk)).
  assert (Uws : eqm (bv_unsigned (edenot E ws)) (estart E (SA wb wk))).
  { subst ws. rewrite mkAlu_denot. unfold estart; cbn [a_base a_off edenot].
    eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [apply eqm_refl|apply eqm_u_lit]. }
  assert (Uks : eqm (bv_unsigned (edenot E ks)) (estart E (SA kb kk))).
  { subst ks. rewrite mkAlu_denot. unfold estart; cbn [a_base a_off edenot].
    eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [apply eqm_refl|apply eqm_u_lit]. }
  pose proof Hfl as Hfl0. destruct Hfl as (F1 & F2 & F3 & F4).
  apply Forall_app; split.
  - (* [comment removed for export] *)
    destruct (lin_ge0 allkn [(kb, kk)] [(wb, wk)]); [constructor|].
    destruct (lin_ge0 allkn [(wb, wk)] [(kb, kk)]) eqn:H1; [|constructor].
    destruct (lin_ge0 allkn [(kb, kk); (len, 0%Z)] [(wb, wk)]) eqn:H2; [|constructor].
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H1) as A0. cbn [xt_den] in A0.
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H2) as B0. cbn [xt_den] in B0.
    constructor; [|constructor]. apply (proj2 (Hkind E M' _ _)).
    assert (HL : elenZ E (mkAlu ALU_SUB ws ks) = (estart E (SA wb wk) - estart E (SA kb kk))%Z).
    { unfold elenZ. rewrite mkAlu_denot.
      assert (eqm (bv_unsigned (alu64 ALU_SUB (edenot E ws) (edenot E ks))) (estart E (SA wb wk) - estart E (SA kb kk))) as [q Hq].
      { eapply eqm_trans; [apply u_sub_eqm|]. apply eqm_add; [exact Uws|]. destruct Uks as [q Hq]. exists (-q)%Z. lia. }
      pose proof (u64_range (alu64 ALU_SUB (edenot E ws) (edenot E ks))) as R.
      pose proof (u64_range (edenot E len)) as RL.
      unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia. }
    rewrite HL. split.
    + unfold flat in *. unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
    + intros i Hi. apply Hout; [|apply Hz]; unfold estart, elenZ in *; cbn [a_base a_off] in *; [|lia].
      left. rewrite u_small; lia.
  - (* [comment removed for export] *)
    destruct (lin_ge0 allkn [(kb, kk); (len, 0%Z)] [(wb, wk); (wn, 0%Z)]) eqn:H1; [|constructor].
    destruct (lin_ge0 allkn [(wb, wk); (wn, 0%Z)] [(kb, kk)]) eqn:H2; [|constructor].
    destruct (lin_ge0 allkn [(ELit 0, (two64 - 1)%Z)] [(kb, kk); (len, 0%Z)]) eqn:H3; [|constructor].
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H1) as A0. cbn [xt_den] in A0.
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H2) as B0. cbn [xt_den] in B0.
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H3) as C0. cbn [xt_den edenot] in C0.
    rewrite u_lit0 in C0. unfold two64 in C0.
    cbv zeta.
    set (we := mkAlu ALU_ADD ws wn).
    assert (Uwe : eqm (bv_unsigned (edenot E we)) (estart E (SA wb wk) + elenZ E wn)).
    { subst we. rewrite mkAlu_denot. eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [exact Uws|apply eqm_refl]. }
    destruct (split_lit we) as [hb ho] eqn:Hsp.
    lazymatch goal with |- Forall _ [mk ?ha0 _] => set (ha := ha0) end.
    assert (Hst : estart E ha = (estart E (SA wb wk) + elenZ E wn)%Z).
    { subst ha.
      destruct (lin_ge0 allkn [(hb, ho)] [(wb, wk); (wn, 0%Z)] && lin_ge0 allkn [(wb, wk); (wn, 0%Z)] [(hb, ho)])%bool eqn:Hh.
      - apply andb_prop in Hh as [Hh1 Hh2].
        pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall Hh1) as C1. cbn [xt_den] in C1.
        pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall Hh2) as C2. cbn [xt_den] in C2.
        unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
      - unfold estart at 1; cbn [a_base a_off]. rewrite Z.add_0_r.
        destruct Uwe as [q Hq]. pose proof (u64_range (edenot E we)).
        pose proof (u64_range (edenot E len)) as RL.
        unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia. }
    assert (HL : elenZ E (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)
                 = (estart E (SA kb kk) + elenZ E len - (estart E (SA wb wk) + elenZ E wn))%Z).
    { unfold elenZ at 1. rewrite mkAlu_denot.
      assert (eqm (bv_unsigned (alu64 ALU_SUB (edenot E (mkAlu ALU_ADD ks len)) (edenot E we)))
                  (estart E (SA kb kk) + elenZ E len - (estart E (SA wb wk) + elenZ E wn))) as [q Hq].
      { eapply eqm_trans; [apply u_sub_eqm|]. apply eqm_add.
        - rewrite mkAlu_denot. eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [exact Uks|apply eqm_refl].
        - destruct Uwe as [q Hq]. exists (-q)%Z. lia. }
      pose proof (u64_range (alu64 ALU_SUB (edenot E (mkAlu ALU_ADD ks len)) (edenot E we))) as R.
      pose proof (u64_range (edenot E len)) as RL.
      unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia. }
    constructor; [|constructor]. apply (proj2 (Hkind E M' _ _)). rewrite HL.
    split.
    + unfold flat. rewrite Hst. pose proof (u64_range (edenot E len)) as RL.
      unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia.
    + intros i Hi. rewrite Hst.
      apply Hout.
      * right. pose proof (u64_range (edenot E len)) as RL.
        rewrite u_small; unfold flat, estart, elenZ in *; cbn [a_base a_off] in *; lia.
      * replace (estart E (SA wb wk) + elenZ E wn + i)%Z
          with (estart E (SA kb kk) + (estart E (SA wb wk) + elenZ E wn - estart E (SA kb kk) + i))%Z by lia.
        apply Hz. unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
Qed.

#[using="Type"] Lemma kwr_cut_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM0,P,(12.&40.)(23.(12.&8.))PM,P,(12.&40.)(23.(12.&8.))PM',Px,(12.&40.)(23.(12.&8.))Pallkn,(2?.$68.)Pwb,$29.Pwk,$1.Pwn,$29.Pkb,$29.Pkk,$1.Plen,$29.P,(64.VSEGS,R;.R:.R7.)P,(6=.VSEGS,R<.R:.(7=.(71.R4.R3.)R2.))P,Px,(12.&40.)P,(1:.(1?.(15.&40.R1.)(70.R>.(71.R9.R8.)))(2.(18.(70.R>.(71.R9.R8.))(72.R>.R7.))(15.&40.R1.)))(3.(23.(12.&8.))A1.R<.R2.A1.R=.R2.)(1;.$68.(6=.VSEGS,R>.R;.)(7>.R:.R9.R8.R7.R6.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros. eapply (kcut_pw_sound KWr _ E M0 M M'); [apply pw_kind_wr | eassumption | eassumption |].
  intros x Hx HP. unfold wview in *. rewrite (H1 x Hx). exact HP.
Qed.

#[using="Type"] Lemma cutout1p_eq : forall k ub uk un K,
  cutout1p k (mk_sprep k ub uk un) ub uk un K = cutout1 k ub uk un K.
Proof. intros. unfold cutout1p, cutout1. rewrite kentry_apart_bp_eq. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma know_ok_cutout : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))PM',Px,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)Pb,$29.Po,$1.Pn,$29.P,(64.VSEGS,R7.R6.R4.)P,Px,(12.&40.)P,(1:.(1?.(15.&40.R1.)(70.R9.(71.R5.R4.)))(2.(18.(70.R9.(71.R5.R4.))(72.R9.R3.))(15.&40.R1.)))(3.(23.(12.&8.))A1.R8.R2.A1.R9.R2.)(64.VSEGS,R9.R7.(7?.R6.R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros E M M' k b o n HK Hout. unfold kn_cutout, know_ok. cbv zeta.
  apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK.
  rewrite cutout1p_eq. unfold cutout1.
  destruct (kentry_apart_b k b o n K) eqn:Hf.
  - apply Forall_one. eapply kentry_apart_keep; eassumption.
  - destruct K as [|[kb kk] len| | | | |[kb kk] len| |[kb kk] len fc|[kb kk] len]; try constructor.
    + eapply kzero_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kwr_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kfill_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kunk_cut_sound; [exact HK | exact HKK | exact Hout].
Qed.

#[using="Type"] Lemma droprange_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pb,$29.Pn,$29.P,(57.R7.R6.R5.R4.R3.)(57.R8.(80.R7.R3.R2.)R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model b n HC. unfold node_droprange. destruct (split_lit b) as [bb bk]. rewrite kn_havocM_eq.   (* [comment removed for export] *)
  apply cs_ok_set_kn; [exact HC|]. eapply know_ok_havoc; [exact (co_know _ _ _ _ _ HC) | intros; reflexivity | apply mem_grows_refl].
Qed.

#[using="Type"] Lemma bump_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pm,$6:.Pcs',$2>.P,(57.R7.R6.R5.R4.R3.)P,(3.(23.$2>.)(81.R7.R3.)(82.$2>.R2.))(5.(57.R9.R3.R7.R6.R5.)(3.$1.(83.R3.)(83.R8.)))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model m cs' HC H. unfold node_bump in H. destruct (Nat.leb (nxt cs) m); [|discriminate]. injection H as <-.
  split; [|reflexivity].
  destruct HC; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
    try assumption; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mkind_eqb_eq : forall a b, mkind_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; first [reflexivity | discriminate]. Qed.
#[using="Type"] Lemma kentry_eqb_eq : forall x y, kentry_eqb x y = true -> x = y.
Proof.
  intros x y H. destruct x, y; cbn [kentry_eqb] in H; try discriminate;
  repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
    end;
  repeat match goal with
    | H : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in H
    | H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
    | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
    end; subst; reflexivity.
Qed.
#[using="Type"] Lemma amap_eqb_eq : forall x y, amap_eqb x y = true -> x = y.
Proof.
  intros [b l k] [b' l' k'] H. unfold amap_eqb in H. cbn [am_base am_len am_kind] in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. apply mkind_eqb_eq in H3. congruence.
Qed.
#[using="Type"] Lemma pair_eqb_eq : forall x y, pair_eqb x y = true -> x = y.
Proof.
  intros [a b] [a' b'] H. unfold pair_eqb in H. cbn [fst snd] in H. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. congruence.
Qed.
#[using="Type"] Lemma afd_eqb_eq : forall x y, afd_eqb x y = true -> x = y.
Proof.
  intros [|k l o|] [|k' l' o'|] H; cbn [afd_eqb] in H; try discriminate; try reflexivity.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1. apply expr_eqb_eq in H2. apply expr_eqb_eq in H3. congruence.
Qed.
#[using="Type"] Lemma list_eqb_eq : forall {T} (eqb : T -> T -> bool), (forall x y, eqb x y = true -> x = y) ->
  forall x y, list_eqb eqb x y = true -> x = y.
Proof.
  intros T eqb Heq x. induction x as [|a x IH]; intros [|b y] H; cbn [list_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (Heq _ _ H1), (IH _ H2). reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kimg_in_hull (k : list kentry) : Prop :=
  Forall (fun K => match K with KImg lo hi => img_lo A <= lo /\ hi <= img_hi A | _ => True end) k.

#[using="Type"] Lemma kimg_clip_in_hull : forall k, kimg_in_hull (kimg_clip A k).
Proof.
  intros k. unfold kimg_in_hull, kimg_clip. apply Forall_forall. intros K Hin. apply filter_In in Hin as [_ Hb].
  destruct K; try exact I. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H3. lia.
Qed.

#[using="Type"] Lemma kimg_clip_incl : forall k K, In K (kimg_clip A k) -> In K k.
Proof. intros k K H. unfold kimg_clip in H. apply filter_In in H as [H _]. exact H. Qed.

#[using="Type"] Lemma kimg_in_hull_app : forall k1 k2, kimg_in_hull k1 -> kimg_in_hull k2 -> kimg_in_hull (k1 ++ k2).
Proof. intros. unfold kimg_in_hull in *. apply Forall_app. auto. Qed.

(* [comment removed for export] *)
#[using="HULL_ok SP0_ok argH_high"] Lemma hid_hull : forall E cs model (a : word), in_hull A (bv_unsigned a) = true -> hid E cs model a = false.
Proof.
  intros E cs model a Hh. unfold hid, vis. rewrite Hh. cbn [orb].
  destruct (argH E a) eqn:Ha; [|reflexivity]. exfalso.
  pose proof (argH_high _ _ Ha). unfold in_hull in Hh. apply andb_prop in Hh as [_ Hh]. apply Z.ltb_lt in Hh.
  pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (?&?&?&?). atopb. unfold CEIL, KHI in *. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_visible : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PH,P,(12.&40.)$20.PFULL,P,(12.&40.)(23.(12.&8.))Pa,(12.&40.)Pw,$6:.Pbs,(2?.(12.&8.))P,(84.VSEGS,R5.)P,(3.(23.(2?.(12.&8.)))(85.VSEGS,(5;.R6.R5.)R4.R3.)(82.(2?.(12.&8.))R2.))Px,(12.&40.)P,(5.(2.(15.&40.R6.)(15.&40.R1.))(1?.(15.&40.R1.)(18.(15.&40.R6.)(86.R5.))))(3.$20.A1.R9.R2.$33.)")
(* [comment removed for export] *).
Proof.
  intros H FULL a w. revert a. induction w as [|w IH]; intros a bs HH Hr x Hx; [lia|].
  cbn [rdn] in Hr. unfold mrestrict in Hr at 1.
  destruct (H a) eqn:Ha.
  - (* [comment removed for export] *)
    assert (Hs : seg_rom SEGS a = None).
    { unfold seg_rom. rewrite (memory_read1_hidden SEGS H HH a Ha). reflexivity. }
    rewrite Hs in Hr. discriminate.
  - destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
    + assert (x = a) by (apply bv_eq; exact Heq). subst x. exact Ha.
    + fold (mrestrict H FULL) in Hr.
      destruct (match FULL a with Some b => Some b | None => seg_rom SEGS a end) as [b|]; [|discriminate].
      destruct (rdn SEGS (mrestrict H FULL) (a + 1)%bv w) as [rest|] eqn:Hr2; [|discriminate].
      pose proof (u64_range x).
      assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      eapply (IH (a + 1)%bv rest HH Hr2). rewrite Hu1. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma know_ok_unhide : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PH1,P,(12.&40.)$20.PH2,P,(12.&40.)$20.PFULL,P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)P,(84.VSEGS,R4.)P,(87.R2.)P,Pa,(12.&40.)P,(3.$20.A1.R6.R1.$22.)(3.$20.A1.R8.R2.$22.)P,Pa,(12.&40.)P,(3.$20.(38.VA,(15.&40.R1.))$22.)(3.$20.A1.R9.R2.$33.)P,(64.VSEGS,R9.(5;.R8.R6.)R5.)(64.VSEGS,R:.(5;.R8.R7.)R6.)")
(* [comment removed for export] *).
Proof.
  intros E H1 H2 FULL k HH1 Hki Hsub Hhull HK.
  assert (AG : forall a, H1 a = false -> mrestrict H2 FULL a = mrestrict H1 FULL a).
  { intros a Ha. unfold mrestrict. rewrite Ha. destruct (H2 a) eqn:Ha2; [|reflexivity].
    rewrite (Hsub a Ha2) in Ha. discriminate. }
  assert (GR : mem_grows (mrestrict H1 FULL) (mrestrict H2 FULL)).
  { intros x Hx. unfold mrestrict in *. destruct (H1 x) eqn:H1x; [exfalso; apply Hx; reflexivity|].
    destruct (H2 x) eqn:H2x; [rewrite (Hsub x H2x) in H1x; discriminate | exact Hx]. }
  unfold know_ok in *. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  pose proof (proj1 (Forall_forall _ _) Hki K Hin) as HKi.
  destruct K as [a w v|a n|a n kb|lo hi|e m|e lo hi|a n|a1 n1 a2 n2|a n fc|a n]; cbn [kentry_ok] in *; try exact HKK.
  7: { (* [comment removed for export] *) destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    pose proof (Hz i Hi) as Hzi. rewrite AG; [exact Hzi|].
    unfold mrestrict in Hzi |- *. destruct (H1 _); [exfalso; apply Hzi; reflexivity | reflexivity]. }
  - (* [comment removed for export] *) destruct HKK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
    rewrite <- Hrd. apply rdn_ext.
    + rewrite (flat_u E _ _ Hfl). destruct Hfl as (?&?&?&?). lia.
    + intros x Hx. apply AG. eapply rdn_visible; [exact HH1 | exact Hrd | exact Hx].
  - (* [comment removed for export] *) destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    pose proof (Hz i Hi) as Hzi. rewrite AG; [exact Hzi|].
    unfold mrestrict in Hzi. destruct (H1 _); [discriminate | reflexivity].
  - (* [comment removed for export] *) destruct HKK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    pose proof (Hz i Hi) as Hzi. rewrite AG; [exact Hzi|].
    unfold mrestrict in Hzi. destruct (H1 _); [discriminate | reflexivity].
  - (* [comment removed for export] *) destruct HKK as (HA & HB & HC). split; [exact HA|]. split; [exact HB|]. intros i Hi.
    assert (Hh : in_hull A (bv_unsigned (Z_to_bv 64 i)) = true).
    { unfold in_hull. rewrite u64_lit by lia. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    rewrite AG; [apply HC; exact Hi | apply Hhull; exact Hh].
  - (* [comment removed for export] *) destruct HKK as [Hfl Hs]. split; [exact Hfl|]. intros d m Hd Hdm.
    eapply store_ok_mono; [exact GR | apply Hs; assumption].
  - (* [comment removed for export] *) destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    pose proof (Hz i Hi) as Hzi. rewrite AG; [exact Hzi|].
    unfold mrestrict in Hzi. destruct (H1 _); [discriminate | reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma vis_mono : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.Pcs',$2>.Pmodel,$56.Pa,(12.&40.)P,Pz,$1.P,(3.$20.(40.R6.R5.R1.)$22.)(3.$20.(40.R7.R5.R2.)$22.)P,(3.$20.(88.R6.R5.R3.R2.)$22.)(3.$20.(88.R7.R5.R4.R3.)$22.)")
(* [comment removed for export] *).
Proof.
  intros E cs cs' model a Hm H. unfold vis in *.
  apply orb_true_iff in H. apply orb_true_iff. destruct H as [H|H]; [left; exact H|]. right.
  apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split; [exact H1|].
  apply orb_true_iff in H2. apply orb_true_iff. destruct H2 as [H2|H2]; [left; exact H2|]. right. apply Hm. exact H2.
Qed.

#[using="Type"] Lemma in_allow_cons : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.Pp,(11.$29.$29.)Pss,$5=.Ptot,$1.Pylo,$1.Peg,$1.Pgh,(2?.(11.$29.$29.))Pab,$1.Pbrk,$29.Pfd,$89.Ptid,$20.Psub,(2?.(11.$29.$29.))Pz,$1.P,(3.$20.(40.R>.R=.R1.)$22.)(3.$20.(40.R?.(8:.R<.(8;.R>.)R;.R:.R9.(26.(11.$29.$29.)R=.(8<.R>.))R8.R7.R6.R5.R4.R3.)R2.)$22.)")
(* [comment removed for export] *).
Proof.
  intros. unfold in_allow, in_vis, in_sh in *. cbn [a_vis existsb].
  apply orb_true_iff in H. apply orb_true_iff.
  destruct H as [H|H]; [left|right]; apply orb_true_iff; right; exact H.
Qed.

#[using="Type"] Lemma hid_cons_sub : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.Pp,(11.$29.$29.)Pmodel,$56.Pa,(12.&40.)Pss,$5=.Ptot,$1.Pylo,$1.Peg,$1.Pgh,(2?.(11.$29.$29.))Pab,$1.Pbrk,$29.Pfd,$89.Ptid,$20.Psub,(2?.(11.$29.$29.))P,(3.$20.(59.R?.(8:.R:.(8;.R>.)R9.R8.R7.(26.(11.$29.$29.)R=.(8<.R>.))R6.R5.R4.R3.R2.R1.)R<.R;.)$22.)(3.$20.(59.R10.R?.R=.R<.)$22.)")
(* [comment removed for export] *).
Proof.
  intros E cs p model a ss tot ylo eg gh ab brk fd tid sub H. unfold hid in *.
  apply orb_true_iff in H. apply orb_true_iff. destruct H as [H|H]; [left; exact H|]. right.
  apply negb_true_iff in H. apply negb_true_iff.
  destruct (vis E cs model a) eqn:Hv; [|reflexivity].
  rewrite (vis_mono E cs _ model a (fun z Hz => in_allow_cons E cs p ss tot ylo eg gh ab brk fd tid sub z Hz) Hv) in H. discriminate.
Qed.

#[using="Type"] Lemma A_bytes_app : forall l1 l2, A_bytes (l1 ++ l2) = A_bytes l1 + A_bytes l2.
Proof. intros l1 l2. induction l1; cbn [A_bytes app]; [lia|]. rewrite IHl1. lia. Qed.

#[using="Type"] Lemma page_allowedb_app_r : forall l1 l2 p, page_allowedb l2 p = true -> page_allowedb (l1 ++ l2) p = true.
Proof. intros. unfold page_allowedb in *. rewrite existsb_app, H. apply orb_true_r. Qed.

#[using="Type"] Lemma MInv_app : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pl1,(2?.(11.$1.$1.))Pl2,(2?.(11.$1.$1.))Pm,$56.P,(5?.R2.R1.)P,(2.(18.(8=.R2.)(8>.(31.(11.$1.$1.)R4.R3.)))(8?.(36.R2.)))(5?.(31.(11.$1.$1.)R5.R4.)R3.)")
(* [comment removed for export] *).
Proof.
  intros l1 l2 m [N1 N2 N3 N4 N5] Hb. constructor; try assumption.
  intros p Hp. apply page_allowedb_app_r. apply N3. exact Hp.
Qed.

#[using="Type"] Lemma in_ivs_true : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pz,$1.Pl,(2?.(11.(12.&40.)(12.&40.)))(79.(3.$20.(21.R2.R1.)$22.)(4:.(11.(12.&40.)(12.&40.))Liv,(11.(12.&40.)(12.&40.))(5.(34.(11.(12.&40.)(12.&40.))R1.R2.)(5.(2.(15.&40.(16.(12.&40.)(12.&40.)R1.))R3.)(1?.R3.(18.(15.&40.(16.(12.&40.)(12.&40.)R1.))(15.&40.(19.(12.&40.)(12.&40.)R1.))))))))")
(* [comment removed for export] *).
Proof.
  intros z l. unfold in_ivs. rewrite existsb_exists. split.
  - intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. eauto.
  - intros [iv [Hin Hb]]. exists iv. split; [exact Hin|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

#[using="Type"] Lemma split_lit_denot : forall E e b k, split_lit e = (b, k) ->
  edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof.
  intros E e b k H.
  assert (G : forall e' : expr, edenot E e' = Z_to_bv 64 (bv_unsigned (edenot E e') + 0)).
  { intros e'. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
  unfold split_lit in H.
  destruct e; try (injection H as <- <-; apply G).
  - injection H as <- <-. cbn [edenot]. rewrite u64_lit by (unfold two64; lia). rewrite Z.add_0_l. reflexivity.
  - lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; apply G).
    lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; apply G).
    injection H as <- <-. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma flat_x_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)Pb,$29.Poff,$1.Pn,$29.P,(64.VSEGS,R6.R5.R4.)P,(3.$20.(90.R5.R4.R3.R2.)$22.)(5.(2.=(70.R8.(71.R5.R4.)))(5.(2.(18.(70.R8.(71.R5.R4.))(15.&40.(52.R8.R3.)))(91.+2.+40.))(1?.=(15.&40.(52.R8.R3.)))))")
(* [comment removed for export] *).
Proof.
  intros E M k b off n HK H. unfold flat_x in H.
  destruct (base_range k b) as [[lo hi]|] eqn:Hb; [|discriminate].
  destruct (xlo k n) as [nl|] eqn:Hnl; [|discriminate]. destruct (xhi k n) as [nh|] eqn:Hnh; [|discriminate].
  apply andb_prop in H as [H Hn]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in Hn. unfold two64 in H2.
  pose proof (base_range_sound SEGS E M k b lo hi HK Hb). pose proof (xlo_sound SEGS E M k n nl HK Hnl). pose proof (xhi_sound SEGS E M k n nh HK Hnh).
  unfold estart. cbn [a_base a_off]. lia.
Qed.

#[using="Type"] Lemma u_of_split : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pe,$29.Pb,$29.Pk,$1.P,(3.(11.$29.$1.)(92.R3.)(27.$29.$1.R2.R1.))P,(5.(2.=(70.R5.(71.R3.R2.)))(1?.(70.R5.(71.R3.R2.))(91.+2.+40.)))(3.$1.(15.&40.(52.R6.R5.))(70.R6.(71.R4.R3.)))")
(* [comment removed for export] *).
Proof.
  intros E e b k Hs Hr. rewrite (split_lit_denot E e b k Hs). unfold estart in *. cbn [a_base a_off] in *.
  apply u64_lit. lia.
Qed.

#[using="HS XN XE XB KC"] Lemma pageup_pagedown_gap : forall a b, a <= b -> pageup b - pagedown a <= b - a + 8190.
Proof.
  intros a b H. unfold pageup, pagedown.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
#[using="nx0 HS XN XE XB"] Lemma maps_match_exact : forall E ms l,
  no_fog ms = true -> (maps_match E ms l <-> l = map (amap_den E) ms).
Proof.
  intros E ms. induction ms as [|m ms IH]; intros l Hnf; cbn [maps_match map].
  - tauto.
  - cbn [no_fog forallb] in Hnf. apply andb_prop in Hnf as [Hm Hr]. apply negb_true_iff in Hm. rewrite Hm.
    split.
    + intros (l' & -> & Hm'). f_equal. apply (proj1 (IH l' Hr)). exact Hm'.
    + intros ->. exists (map (amap_den E) ms). split; [reflexivity|]. apply (proj2 (IH _ Hr)). reflexivity.
Qed.

#[using="Type"] Lemma maps_match_In : forall E ms l m,
  maps_match E ms l -> In m ms -> is_fog m = false -> In (amap_den E m) l.
Proof.
  intros E ms. induction ms as [|m0 ms IH]; intros l m HM Hin Hf; [destruct Hin|].
  cbn [maps_match] in HM. destruct Hin as [<-|Hin].
  - rewrite Hf in HM. destruct HM as (l' & -> & _). left. reflexivity.
  - destruct (is_fog m0).
    + destruct HM as [HM|(iv & l' & -> & _ & HM)]; [exact (IH _ _ HM Hin Hf) | right; exact (IH _ _ HM Hin Hf)].
    + destruct HM as (l' & -> & HM). right. exact (IH _ _ HM Hin Hf).
Qed.

#[using="Type"] Lemma in_ivs_maps_match : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pms,(2?.$48.)Pl,(2?.(11.(12.&40.)(12.&40.)))Pm,$48.Pz,$1.P,(93.R5.R4.R3.)P,(34.$48.R3.R5.)P,(3.$20.(4>.R4.)$33.)P,(5.(2.(15.&40.(52.R8.(45.R5.)))R4.)(1?.R4.(18.(15.&40.(52.R8.(45.R5.)))(15.&40.(52.R8.(46.R5.))))))(3.$20.(21.R5.R7.)$22.)")
(* [comment removed for export] *).
Proof.
  intros E ms l m z HM Hin Hf Hz. apply (proj2 (in_ivs_true z _)). exists (amap_den E m).
  split; [exact (maps_match_In E ms l m HM Hin Hf) | exact Hz].
Qed.

#[using="Type"] Lemma maps_match_cons : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pms,(2?.$48.)Pl,(2?.(11.(12.&40.)(12.&40.)))Pb,$29.Pn,$29.Pk,$4?.P,(3.$20.(94.R1.)$33.)P,(93.R7.R6.R5.)(93.R8.(26.$48.(95.R5.R4.R3.)R7.)(26.(11.(12.&40.)(12.&40.))(27.(12.&40.)(12.&40.)(52.R8.R5.)(52.R8.R4.))R6.))")
(* [comment removed for export] *).
Proof.
  intros E ms l b n k Hk HM. cbn [maps_match]. unfold is_fog. cbn [am_kind]. rewrite Hk. exists l. split; [reflexivity | exact HM].
Qed.

#[using="Type"] Lemma maps_match_length : forall E ms l, maps_match E ms l -> (length l <= length ms)%nat.
Proof.
  intros E ms. induction ms as [|m ms IH]; intros l HM; cbn [maps_match] in HM.
  - subst l. cbn. lia.
  - cbn [length]. destruct (is_fog m).
    + destruct HM as [HM|(iv & l' & -> & _ & HM)]; [pose proof (IH _ HM); lia | cbn; pose proof (IH _ HM); lia].
    + destruct HM as (l' & -> & HM). cbn. pose proof (IH _ HM). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma maps_match_elem : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pms,(2?.$48.)Pl,(2?.(11.(12.&40.)(12.&40.)))Piv,(11.(12.&40.)(12.&40.))P,(93.R4.R3.R2.)P,(34.(11.(12.&40.)(12.&40.))R2.R3.)(4:.$48.Lm,$48.(5.(34.$48.R1.R6.)(1:.(5.(3.$20.(4>.R1.)$33.)(3.(11.(12.&40.)(12.&40.))R4.(96.R7.R1.)))(5.(3.$20.(4>.R1.)$22.)(2.(15.&40.(19.(12.&40.)(12.&40.)R4.))(6.R7.(46.R1.)))))))")
(* [comment removed for export] *).
Proof.
  intros E ms. induction ms as [|m ms IH]; intros l iv HM Hin; cbn [maps_match] in HM.
  - subst l. destruct Hin.
  - destruct (is_fog m) eqn:Hf.
    + destruct HM as [HM|(iv0 & l' & -> & Hsz & HM)].
      * destruct (IH _ _ HM Hin) as (m' & Hm' & H'). exists m'. split; [right; exact Hm' | exact H'].
      * destruct Hin as [<-|Hin].
        -- exists m. split; [left; reflexivity|]. right. split; [exact Hf | exact Hsz].
        -- destruct (IH _ _ HM Hin) as (m' & Hm' & H'). exists m'. split; [right; exact Hm' | exact H'].
    + destruct HM as (l' & -> & HM). destruct Hin as [<-|Hin].
      * exists m. split; [left; reflexivity|]. left. split; [exact Hf | reflexivity].
      * destruct (IH _ _ HM Hin) as (m' & Hm' & H'). exists m'. split; [right; exact Hm' | exact H'].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma maps_match_rekind : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pms,(2?.$48.)Pl,(2?.(11.(12.&40.)(12.&40.)))Pf,P,$48.$48.P,Pm,$48.(5.(3.$29.(45.A1.R2.R1.)(45.R1.))(5.(3.$29.(46.A1.R2.R1.)(46.R1.))(3.$20.(4>.A1.R2.R1.)(4>.R1.))))P,(93.R5.R4.R3.)(93.R6.(97.$48.$48.R3.R5.)R4.)")
(* [comment removed for export] *).
Proof.
  intros E ms. induction ms as [|m ms IH]; intros l f Hf HM; cbn [maps_match map] in *; [exact HM|].
  destruct (Hf m) as (Hb & Hn & Hk). rewrite Hk. unfold uE, amap_den in *. rewrite Hb, Hn.
  destruct (is_fog m).
  - destruct HM as [HM|(iv & l' & -> & Hsz & HM)]; [left; exact (IH _ f Hf HM) | right].
    exists iv, l'. split; [reflexivity|]. split; [exact Hsz | exact (IH _ f Hf HM)].
  - destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | exact (IH _ f Hf HM)].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma filter_all_true : forall {T} (f : T -> bool) l, (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof.
  intros T f l H. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)).
  rewrite IH by (intros y Hy; apply H; right; exact Hy). reflexivity.
Qed.

#[using="Type"] Lemma aluop_eqb_refl' : forall o, aluop_eqb o o = true.
Proof. intros []; reflexivity. Qed.
#[using="Type"] Lemma mulop_eqb_refl' : forall o, mulop_eqb o o = true.
Proof. intros []; reflexivity. Qed.
#[using="Type"] Lemma expr_eqb_refl' : forall e, expr_eqb e e = true.
Proof.
  induction e; cbn; rewrite ?aluop_eqb_refl', ?mulop_eqb_refl', ?IHe1, ?IHe2, ?IHe, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
#[using="Type"] Lemma amap_eqb_refl' : forall m, amap_eqb m m = true.
Proof. intros [b l k]. unfold amap_eqb. cbn. rewrite !expr_eqb_refl'. destruct k; reflexivity. Qed.

#[using="Type"] Lemma map_remove_notin' : forall l (a : word),
  (forall b sz, In (b, sz) l -> b <> a) -> map_remove l a = l.
Proof.
  induction l as [|[b sz] l IH]; intros a H; [reflexivity|].
  unfold map_remove in *. cbn [List.filter fst]. rewrite (bv_eqb_neq b a) by (apply (H b sz); left; reflexivity). cbn [negb].
  f_equal. apply IH. intros b' s' Hin. apply (H b' s'). right. exact Hin.
Qed.

#[using="Type"] Lemma maps_match_remove : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pms,(2?.$48.)Pl,(2?.(11.(12.&40.)(12.&40.)))Pm,$48.P,(93.R4.R3.R2.)P,(34.$48.R2.R4.)P,(3.$20.(4>.R3.)$33.)P,(98.(11.(12.&40.)(12.&40.))R5.)P,Piv,(11.(12.&40.)(12.&40.))P,(34.(11.(12.&40.)(12.&40.))R1.R7.)P,(3.(12.&40.)(16.(12.&40.)(12.&40.)R2.)(52.R:.(45.R7.)))(3.(11.(12.&40.)(12.&40.))R3.(96.R;.R8.))(93.R9.(73.$48.Lm',$48.(3;.(99.R1.R7.))R8.)(9:.R7.(52.R9.(45.R6.))))")
(* [comment removed for export] *).
Proof.
  intros E ms. induction ms as [|m0 ms IH]; intros l m HM Hin Hf Hnd Huniq; [destruct Hin|].
  cbn [maps_match] in HM. cbn [List.filter].
  destruct (amap_eqb m0 m) eqn:Heq.
  - (* [comment removed for export] *)
    apply amap_eqb_eq in Heq. subst m0.
    rewrite Hf in HM. destruct HM as (l' & -> & HM). cbn [negb].
    unfold map_remove. cbn [List.filter amap_den fst]. rewrite bv_eqb_refl. cbn [negb].
    inversion Hnd as [|x l0 Hnotin Hnd']; subst.
    assert (Hnotin' : ~ In m ms).
    { intros Hm. apply Hnotin. exact (maps_match_In E ms l' m HM Hm Hf). }
    rewrite (filter_all_true (fun m' => negb (amap_eqb m' m)) ms).
    2:{ intros x Hx. destruct (amap_eqb x m) eqn:Ex; [|reflexivity]. apply amap_eqb_eq in Ex. subst x. exfalso. exact (Hnotin' Hx). }
    fold (map_remove l' (edenot E (am_base m))). rewrite map_remove_notin'; [exact HM|].
    intros b sz Hbs Hb. apply Hnotin. rewrite <- (Huniq (b, sz) (or_intror Hbs) Hb). exact Hbs.
  - (* [comment removed for export] *)
    destruct Hin as [->|Hin]; [rewrite amap_eqb_refl' in Heq; discriminate|].
    cbn [negb maps_match].
    destruct (is_fog m0) eqn:Hf0.
    + destruct HM as [HM|(iv & l' & -> & Hsz & HM)].
      * left. exact (IH _ _ HM Hin Hf Hnd Huniq).
      * inversion Hnd as [|x l0 Hnotin Hnd']; subst.
        assert (Hne : bv_eqb (fst iv) (edenot E (am_base m)) = false).
        { apply bv_eqb_neq. intros Hb. apply Hnotin. rewrite (Huniq iv (or_introl eq_refl) Hb).
          exact (maps_match_In E ms l' m HM Hin Hf). }
        unfold map_remove. cbn [List.filter]. rewrite Hne. cbn [negb]. fold (map_remove l' (edenot E (am_base m))).
        right. exists iv, (map_remove l' (edenot E (am_base m))). split; [reflexivity|]. split; [exact Hsz|].
        apply (IH _ _ HM Hin Hf Hnd'). intros x Hx. apply Huniq. right. exact Hx.
    + destruct HM as (l' & -> & HM).
      inversion Hnd as [|x l0 Hnotin Hnd']; subst.
      assert (Hne : bv_eqb (fst (amap_den E m0)) (edenot E (am_base m)) = false).
      { apply bv_eqb_neq. intros Hb. apply Hnotin. rewrite (Huniq _ (or_introl eq_refl) Hb).
        exact (maps_match_In E ms l' m HM Hin Hf). }
      unfold map_remove. cbn [List.filter]. rewrite Hne. cbn [negb]. fold (map_remove l' (edenot E (am_base m))).
      exists (map_remove l' (edenot E (am_base m))). split; [reflexivity|].
      apply (IH _ _ HM Hin Hf Hnd'). intros x Hx. apply Huniq. right. exact Hx.
Qed.

#[using="Type"] Lemma in_ivs_map_den : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pms,(2?.$48.)Pm,$48.Pz,$1.P,(34.$48.R2.R3.)P,(5.(2.(15.&40.(52.R5.(45.R3.)))R2.)(1?.R2.(18.(15.&40.(52.R5.(45.R3.)))(15.&40.(52.R5.(46.R3.))))))(3.$20.(21.R3.(97.$48.(11.(12.&40.)(12.&40.))(96.R6.)R5.))$22.)")
(* [comment removed for export] *).
Proof.
  intros E ms m z Hin Hz. apply (proj2 (in_ivs_true z _)). exists (amap_den E m). split; [apply in_map; exact Hin | exact Hz].
Qed.

#[using="Type"] Lemma existsb_false_forall : forall {T} (f : T -> bool) l, (forall x, In x l -> f x = false) -> existsb f l = false.
Proof.
  intros T f l H. induction l as [|x l IH]; [reflexivity|]. cbn [existsb].
  rewrite (H x (or_introl eq_refl)). cbn [orb]. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ext1 (E : env) (v : nat) (a : word) : env :=
  Env (fun n => if Nat.eqb n v then a else ev E n) (eb E).

#[using="Type"] Lemma ext1_agree : forall E v a, env_agree v E (ext1 E v a).
Proof.
  intros E v a. split; [|reflexivity]. intros n Hn. cbn [ext1 ev].
  destruct (Nat.eqb_spec n v); [lia | reflexivity].
Qed.
#[using="Type"] Lemma ext1_at : forall E v a, ev (ext1 E v a) v = a.
Proof. intros. cbn [ext1 ev]. rewrite Nat.eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma env_agree_le : forall b b' E E', env_agree b' E E' -> (b <= b')%nat -> env_agree b E E'.
Proof. intros b b' E E' [H1 H2] Hle. split; [|exact H2]. intros n Hn. apply H1. lia. Qed.
#[using="Type"] Lemma env_agree_refl : forall b E, env_agree b E E.
Proof. intros. split; [intros; reflexivity | reflexivity]. Qed.
#[using="Type"] Lemma env_agree_trans : forall b E1 E2 E3, env_agree b E1 E2 -> env_agree b E2 E3 -> env_agree b E1 E3.
Proof. intros b E1 E2 E3 [A1 B1] [A2 B2]. split; [intros n Hn; rewrite A1 by lia; apply A2; lia | congruence]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma expr_vars_lt_eq : forall b e, AP.expr_vars_lt b e = AxSymRun3.expr_vars_lt b e.
Proof. intros b e. induction e; cbn; try rewrite IHe1, IHe2; try rewrite IHe; reflexivity. Qed.
#[using="Type"] Lemma kentry_vars_lt_eq : forall b K, AP.kentry_vars_lt b K = AxSymRun3.kentry_vars_lt b K.
Proof.
  intros b K. destruct K as [[? ?] | [? ?] | [? ?] | | | | [? ?] | [? ?] ? [? ?] ?| [? ?] ? ?| [? ?] ?];
    cbn -[AP.expr_vars_lt AxSymRun3.expr_vars_lt]; unfold AP.saddr_vars_lt, AxSymRun3.saddr_vars_lt; cbn [a_base];
    rewrite ?expr_vars_lt_eq; reflexivity.
Qed.
#[using="Type"] Lemma kn_vars_lt_eq : forall b k, AP.kn_vars_lt b k = AxSymRun3.kn_vars_lt b k.
Proof. intros b k. induction k; cbn [AP.kn_vars_lt AxSymRun3.kn_vars_lt]; [reflexivity|]. rewrite kentry_vars_lt_eq, IHk. reflexivity. Qed.
#[using="Type"] Lemma sr_vars_lt_eq : forall b sr, AP.sr_vars_lt b sr = AxSymRun3.sr_vars_lt b sr.
Proof. intros b sr. induction sr; cbn [AP.sr_vars_lt AxSymRun3.sr_vars_lt]; [reflexivity|]. rewrite expr_vars_lt_eq, IHsr. reflexivity. Qed.

#[using="Type"] Lemma edenot_agree' : forall b E E' e, env_agree b E E' -> AP.expr_vars_lt b e = true -> edenot E e = edenot E' e.
Proof. intros. eapply edenot_agree; [eassumption | rewrite <- expr_vars_lt_eq; assumption]. Qed.
#[using="Type"] Lemma know_ok_agree' : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.PM,P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)P,(9;.R5.R4.R3.)P,(3.$20.(9<.R6.R2.)$22.)P,(64.VSEGS,R6.R4.R3.)(64.VSEGS,R6.R5.R4.)")
(* [comment removed for export] *).
Proof. intros. eapply know_ok_agree; [eassumption | rewrite <- kn_vars_lt_eq; eassumption | assumption]. Qed.
#[using="Type"] Lemma regs_ok_agree' : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.Psr,(2?.$29.)PR,(55.&5.(12.&40.))P,(9;.R5.R4.R3.)P,(3.$20.(9=.R6.R3.)$22.)P,(60.R6.R4.R3.)(60.R6.R5.R4.)")
(* [comment removed for export] *).
Proof. intros. eapply regs_ok_agree; [eassumption | rewrite <- sr_vars_lt_eq; eassumption | assumption]. Qed.

(* [comment removed for export] *)

#[using="HOLES_agree"] Lemma sd_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PD,$9>.PE,$0.PE',$0.Pfs,$9?.Ps,$:0.P,(9;.Vnx0,R4.R3.)P,(3.$20.(:1.Vnx0,R2.)$22.)(3.$9>.(:2.R7.R6.R4.R3.)(:2.R7.R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros D E E' fs s Hag. induction s; cbn [shape_vars_lt sd]; intros H; try reflexivity.
  - rewrite IHs by exact H. unfold Wp. replace (flat_map (piece_den E') ps) with (flat_map (piece_den E) ps); [reflexivity|].
    apply flat_map_ext. intros [bs|k]; cbn [piece_den]; [reflexivity|]. destruct Hag as [_ Heb]. rewrite Heb. reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite IHs1, IHs2 by assumption. reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    rewrite IHs1, IHs2 by assumption. rewrite (edenot_agree' nx0 E E' e Hag H1). reflexivity.
  - apply HOLES_agree. exact Hag.
Qed.

#[using="Type"] Lemma t_exit_has_nil : forall code fs, t_exit code fs [].
Proof. intros. unfold t_exit. apply t_emit_has_nil. Qed.
#[using="HOLES_nil"] Lemma sd_has_nil : forall D E fs s, D [] -> sd D E fs s [].
Proof.
  intros D E fs s HD. induction s; cbn [sd].
  - reflexivity.
  - apply t_exit_has_nil.
  - apply t_emit_has_nil.
  - left. exact IHs1.
  - destruct (_ <=? _)%Z; assumption.
  - apply HOLES_nil.
  - exact HD.
Qed.
#[using="Type"] Lemma t_alt2_nil_l : forall T : TSet, T [] -> t_eq (t_alt2 t_nil T) T.
Proof. intros T HT tr. unfold t_alt2, t_nil. split; [intros [->|H]; assumption | intros H; right; exact H]. Qed.
#[using="Type"] Lemma t_alt2_nil_r : forall T : TSet, T [] -> t_eq (t_alt2 T t_nil) T.
Proof. intros T HT tr. unfold t_alt2, t_nil. split; [intros [H| ->]; assumption | intros H; left; exact H]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma t_eq_alt2 : forall TA TA' TB TB' : TSet, t_eq TA TA' -> t_eq TB TB' -> t_eq (t_alt2 TA TB) (t_alt2 TA' TB').
Proof. intros TA TA' TB TB' HA HB tr. unfold t_alt2. split; (intros [H|H]; [left; apply HA | right; apply HB]; exact H). Qed.
#[using="nx0 HS XN XE XB"] Lemma t_eq_refl' : forall T : TSet, t_eq T T.
Proof. intros T tr. tauto. Qed.
#[using="nx0 HS XN XE XB HOLES_nil"] Lemma sd_salt2 : forall D E fs a b, D [] ->
  t_eq (t_alt2 (sd D E fs a) (sd D E fs b)) (sd D E fs (salt2 a b)).
Proof.
  intros D E fs a b HD.
  assert (Ha : sd D E fs a []) by (apply sd_has_nil; exact HD).
  assert (Hb : sd D E fs b []) by (apply sd_has_nil; exact HD).
  unfold salt2. destruct a; destruct b; cbn [sd] in *;
    first [ apply t_alt2_nil_l; assumption | apply t_alt2_nil_r; assumption | apply t_eq_refl' ].
Qed.
#[using="Type"] Lemma salt2_vars : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.Px,$:0.Py,$:0.P,(3.$20.(:1.R3.R2.)$22.)P,(3.$20.(:1.R4.R2.)$22.)(3.$20.(:1.R5.(:3.R4.R3.))$22.)")
(* [comment removed for export] *).
Proof.
  intros b x y Hx Hy. unfold salt2.
  destruct x; destruct y; cbn [shape_vars_lt] in *; rewrite ?Hx, ?Hy; try reflexivity; try assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node1_stmt (pre : acs -> bool) (node : acs -> option acs) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pcs,$2>.Pcs',$2>.PE,$0.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.PT,$9>.P,(57.R5.R7.R4.R3.R2.)P,(3.$20.A1.O2.R8.$22.)P,(3.(23.$2>.)A1.O1.R9.(82.$2>.R8.))P,PE',$0.PR',(55.&5.(12.&40.))PFULL',P,(12.&40.)(23.(12.&8.))Pmodel',$56.P,(5.(9;.Vnx0,R<.R4.)(9;.(:4.R>.)R<.R4.))P,(57.R5.R>.R4.R3.R2.)P,(3.$9?.(:5.R3.)(:5.R;.))(:6.VSEGS,(:7.VSEGS,R6.(83.R10.)R5.R4.)R;.)(:6.VSEGS,(:7.VSEGS,R8.(83.R;.)R7.R6.)R5.)")
(* [comment removed for export] *).

Definition always (cs : acs) : bool := true.

(* [comment removed for export] *)
Definition node1_stmt_R (SR : config -> TSet -> Prop) (pre : acs -> bool) (node : acs -> option acs) : Prop :=
  forall cs cs' E R FULL model T,
    cs_ok E cs R FULL model -> pre cs = true -> node cs = Some cs' ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
        SR (cfg R' (pc cs') FULL' model') T) ->
    SR (cfg R (pc cs) FULL model) T.

(* [comment removed for export] *)
Definition srchain (SR : config -> TSet -> Prop) : Prop :=
  forall (H : word -> bool), H_off_segments SEGS H -> wx_segs_nowrap SEGS ->
  forall (AL : list (Z * Z)) ms msr' model T,
    lazy_cover H (m_vm_lazy model) AL -> A_wf AL -> MInv AL model ->
    m_halted model = None ->
    msteps SEGS (restrict H ms) msr' ->
    (forall model',
        MInv AL model' -> same_but_materialized model model' ->
        hclean H msr' ->
        SR (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
    SR (mkCfg ms model) T.

Lemma srchain_srealizes : srchain (srealizes SEGS).
Proof. intros H HH Hwx. exact (srz_msteps_restricted_T SEGS H HH Hwx). Qed.
Lemma srchain_srealizes0 : srchain (srealizes0 SEGS).
Proof. intros H HH Hwx. exact (srz0_msteps_restricted_T SEGS H HH Hwx). Qed.

(* [comment removed for export] *)
Definition x_stmt0 (x : xnode) : Prop := forall args, node1_stmt_R (srealizes0 SEGS) always (node_x SEGS A nx0 x args).

(* [comment removed for export] *)
Definition sys_stmt (y : snode) : Prop := node1_stmt (is_ecall_at SEGS) (node_sys A nx0 y).
(* [comment removed for export] *)
Definition x_stmt (x : xnode) : Prop := forall args, node1_stmt always (node_x SEGS A nx0 x args).
(* [comment removed for export] *)
Definition fresh_stmt : Prop := forall r logc base, node1_stmt always (fun cs => node_fresh nx0 cs r logc base).
(* [comment removed for export] *)
Definition join_stmt : Prop := forall b off n, node1_stmt always (fun cs => node_join SEGS cs b off n).

(* [comment removed for export] *)
Definition brk2_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pcs,$2>.Pcsa,$2>.Pcsb,$2>.PE,$0.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.PTA,$9>.PTB,$9>.P,(57.R6.R9.R5.R4.R3.)P,(3.$20.(:8.VSEGS,R:.)$22.)P,(3.(23.(11.$2>.$2>.))(:9.VA,VLIMIT,R;.)(82.(11.$2>.$2>.)(27.$2>.$2>.R:.R9.)))P,PE',$0.PR',(55.&5.(12.&40.))PFULL',P,(12.&40.)(23.(12.&8.))Pmodel',$56.P,(5.(9;.Vnx0,R=.R4.)(9;.(:4.R10.)R=.R4.))P,(57.R5.R10.R4.R3.R2.)P,(3.$9?.(:5.R3.)(:5.R<.))(:6.VSEGS,(:7.VSEGS,R6.(83.R12.)R5.R4.)R<.)P,PE',$0.PR',(55.&5.(12.&40.))PFULL',P,(12.&40.)(23.(12.&8.))Pmodel',$56.P,(5.(9;.Vnx0,R>.R4.)(9;.(:4.R11.)R>.R4.))P,(57.R5.R10.R4.R3.R2.)P,(3.$9?.(:5.R3.)(:5.R=.))(:6.VSEGS,(:7.VSEGS,R6.(83.R12.)R5.R4.)R<.)P,Ptr,(2?.$::.)P,A1.R7.R1.A1.R9.R2.(:6.VSEGS,(:7.VSEGS,R;.(83.R?.)R:.R9.)(:;.R8.R7.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition exit_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pcs,$2>.Pcode,$1.PE,$0.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.P,(57.R4.R6.R3.R2.R1.)P,(3.$20.(:8.VSEGS,R7.)$22.)P,(3.(23.$1.)(:<.R8.)(82.$1.R7.))(:6.VSEGS,(:7.VSEGS,R6.(83.R9.)R5.R4.)(:=.(42.&40.R8.)(:5.R4.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition ext_stmt : Prop := forall id args, node1_stmt always (XN id args).
(* [comment removed for export] *)
Definition ext2_stmt : Prop :=   (* [comment removed for export] *)
  forall id args cs csa csb E R FULL model TA TB,
    cs_ok E cs R FULL model -> XB id args cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes0 SEGS (cfg R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csb) FULL' model') TB) ->
    srealizes SEGS (cfg R (pc cs) FULL model) (t_alt2 TA TB).
(* [comment removed for export] *)
Definition mm2_stmt (node : acs -> option (acs * acs)) : Prop :=   (* [comment removed for export] *)
  forall cs csa csb E R FULL model TA TB,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes0 SEGS (cfg R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csb) FULL' model') TB) ->
    srealizes SEGS (cfg R (pc cs) FULL model) (t_alt2 TA TB).

Definition mm3_stmt (node : acs -> option (acs * acs * list acs)) : Prop :=   (* [comment removed for export] *)
  forall cs csa csb cscs E R FULL model TA TB TC,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node cs = Some (csa, csb, cscs) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes0 SEGS (cfg R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csb) FULL' model') TB) ->
    (forall csc E' R' FULL' model', In csc cscs ->
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csc R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes0 SEGS (cfg R' (pc csc) FULL' model') TC) ->
    srealizes SEGS (cfg R (pc cs) FULL model) (t_alt2 TA (t_alt2 TB TC)).

(* [comment removed for export] *)
Definition emit_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pid,$6:.Pargs,(2?.$29.)Pcs,$2>.Pfd,$1.Pps,(2?.$:>.)Pcs',$2>.PE,$0.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.PT,Px,(2?.$::.)SpP,(57.R5.R9.R4.R3.R2.)P,(3.(23.(11.(11.$1.(2?.$:>.))$2>.))A3.VXE,R<.R;.R:.(82.(11.(11.$1.(2?.$:>.))$2>.)(27.(11.$1.(2?.$:>.))$2>.(27.$1.(2?.$:>.)R9.R8.)R7.)))P,A1.R3.(2=.$::.)P,PE',$0.PR',(55.&5.(12.&40.))PFULL',P,(12.&40.)(23.(12.&8.))Pmodel',$56.P,(5.(9;.Vnx0,R<.R4.)(9;.(:4.R10.)R<.R4.))P,(57.R5.R>.R4.R3.R2.)P,(3.$9?.(:5.R3.)(:5.R;.))(:6.VSEGS,(:7.VSEGS,R6.(83.R10.)R5.R4.)R;.)(:6.VSEGS,(:7.VSEGS,R8.(83.R=.)R7.R6.)(:?.(;0.R9.R<.R;.)R5.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition holes_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Ph,$6:.Pch,$2>.P,(3.(23.$2>.)A1.VHS,R2.(82.$2>.R1.))PE,$0.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.P,(57.R4.R6.R3.R2.R1.)(:6.VSEGS,(:7.VSEGS,R4.(83.R7.)R3.R2.)A3.VHOLES,R8.R5.(:5.R2.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Hypothesis node_sys_sound : forall y, sys_stmt y.
Hypothesis node_brk2_sound : brk2_stmt.
Hypothesis node_mmap2_sound : mm2_stmt (node_mmap2 A nx0 LIMIT).
Hypothesis node_mmapin_sound : mm3_stmt (node_mmapin A LIMIT false).   (* [comment removed for export] *)
Hypothesis node_mprotect2_sound : mm2_stmt (node_mprotect2 A LIMIT).
Hypothesis node_exit_sound : exit_stmt.
Hypothesis node_x_sound : forall x, x_stmt x.
Hypothesis node_x_sound0 : forall x, x_spin_ok x = true -> x_stmt0 x.   (* [comment removed for export] *)
Hypothesis node_join_sound : join_stmt.
Hypothesis node_ext_sound : ext_stmt.
Hypothesis node_emit_sound : emit_stmt.
Hypothesis node_ext2_sound : ext2_stmt.
Hypothesis HS_sound : holes_stmt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma split_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pcs,$2>.Pe,$29.Pmid,$1.Plo,$1.Phi,$1.PE,$0.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.P,(57.R4.R9.R3.R2.R1.)P,(3.(23.(11.$1.$1.))(;1.(6<.R:.)R9.)(82.(11.$1.$1.)(27.$1.$1.R7.R6.)))(5.P,(2.(15.&40.(52.R6.R:.))R9.)(57.R7.(69.R<.(26.$68.(;2.R;.R9.R:.)(6<.R<.)))R6.R5.R4.)P,(1?.R9.(15.&40.(52.R6.R:.)))(57.R7.(69.R<.(26.$68.(;2.R;.(18.R:.+1.)R8.)(6<.R<.)))R6.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros cs e mid lo hi E R FULL model HC Hr.
  pose proof (erange_sound SEGS E _ (kn cs) e lo hi (co_know _ _ _ _ _ HC) Hr) as Hb.
  split; intros Hm; apply cs_ok_set_kn; [exact HC| |exact HC|];
    (constructor; [cbn [kentry_ok]; lia | exact (co_know _ _ _ _ _ HC)]).
Qed.

#[using="Type"] Lemma kn_contra_sound : forall E M k, know_ok SEGS E M k -> kn_contra k = true -> False.
Proof.
  intros E M k HK H. unfold kn_contra in H. apply existsb_exists in H as (K & Hin & HKb).
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct K as [| | | | |e lo hi| | | |]; try discriminate. cbn [kentry_ok] in HKK.
  destruct (Z.ltb hi lo) eqn:Hlt; [apply Z.ltb_lt in Hlt; lia|].
  assert (GEN : forall c ts, lin_of e = (c, ts) ->
            match lin_range (erange k) c ts with
            | Some (a, b) => (Z.leb 0 a && Z.ltb b two64 && (Z.ltb b lo || Z.ltb hi a))%bool
            | None => false end = true -> False).
  { intros c ts Hle Hm.
    destruct (lin_range (erange k) c ts) as [[a b]|] eqn:Hlr; [|discriminate].
    apply andb_prop in Hm as [Hm Hd]. apply andb_prop in Hm as [Ha Hb].
    apply Z.leb_le in Ha. apply Z.ltb_lt in Hb. unfold two64 in Hb.
    pose proof (lin_range_sound E (erange k) (fun a lo hi Ha => erange_sound SEGS E M k a lo hi HK Ha) _ _ _ _ Hlr) as Hbd.
    pose proof (lin_of_sound E e) as [q Hq]. unfold lden, AX2S.uE in Hq. rewrite Hle in Hq. cbn [fst snd] in Hq.
    pose proof (u64_range (edenot E e)).
    assert (q = 0)%Z by nia. subst q.
    apply orb_prop in Hd as [Hd|Hd]; apply Z.ltb_lt in Hd; lia. }
  destruct e; try discriminate;
    (destruct (lin_of _) as [c [|t1 [|t2 ts]]] eqn:Hle; try discriminate; exact (GEN _ _ eq_refl HKb)).
Qed.

#[using="Type"] Lemma estart_SA : forall E b k, estart E (SA b k) = bv_unsigned (edenot E b) + k.
Proof. reflexivity. Qed.

#[using="Type"] Lemma xlo1_sound : forall E M k e lo, know_ok SEGS E M k -> xlo1 k e = Some lo -> lo <= bv_unsigned (edenot E e).
Proof.
  intros E M k e lo HK H. unfold xlo1 in H.
  assert (LIT : forall z, e = ELit z -> Some (zlit64 z) = Some lo -> lo <= bv_unsigned (edenot E e)).
  { intros z -> Hs. injection Hs as <-. cbn [edenot]. rewrite zlit64_eq, u_lit64. lia. }
  destruct e; [exact (LIT _ eq_refl H)|..]; clear LIT;
  (destruct (erange k _) as [[l1 h1]|] eqn:He; [pose proof (erange_sound SEGS E M k _ l1 h1 HK He)|];
   destruct (lin_brange k _) as [[l2 h2]|] eqn:Hb; [pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)| |pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)|];
   [..| (* [comment removed for export] *) destruct (lin_srange k _) as [[l3 h3]|] eqn:Hs; [pose proof (lin_srange_sound SEGS E M k _ l3 h3 HK Hs)|]];
   try discriminate; injection H as <-; lia).
Qed.

#[using="Type"] Lemma xhi1_sound : forall E M k e hi, know_ok SEGS E M k -> xhi1 k e = Some hi -> bv_unsigned (edenot E e) <= hi.
Proof.
  intros E M k e hi HK H. unfold xhi1 in H.
  assert (LIT : forall z, e = ELit z -> Some (zlit64 z) = Some hi -> bv_unsigned (edenot E e) <= hi).
  { intros z -> Hs. injection Hs as <-. cbn [edenot]. rewrite zlit64_eq, u_lit64. lia. }
  destruct e; [exact (LIT _ eq_refl H)|..]; clear LIT;
  (destruct (erange k _) as [[l1 h1]|] eqn:He; [pose proof (erange_sound SEGS E M k _ l1 h1 HK He)|];
   destruct (lin_brange k _) as [[l2 h2]|] eqn:Hb; [pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)| |pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)|];
   [..| (* [comment removed for export] *) destruct (lin_srange k _) as [[l3 h3]|] eqn:Hs; [pose proof (lin_srange_sound SEGS E M k _ l3 h3 HK Hs)|]];
   try discriminate; injection H as <-; lia).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma deand_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pe,$29.Pe',$29.Ps,$1.P,(3.(11.$29.$1.)(;3.R3.)(27.$29.$1.R2.R1.))(5.(2.=R2.)(4:.$1.Lrho,$1.(5.(5.(2.=R1.)(2.R1.R3.))(3.$1.(15.&40.(52.R6.R5.))(:.(9.(15.&40.(52.R6.R4.))R1.)(91.+2.+40.))))))")
(* [comment removed for export] *).
Proof.
  intros E e. induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|u w sx a IHa|bk bo bn bw];
    intros e' s Hd;
    try (cbn [deand] in Hd; injection Hd as <- <-; split; [lia|]; exists 0; split; [lia|];
         rewrite Z.sub_0_r, Z.mod_small by (apply u64_range); reflexivity).
  cbn [deand] in Hd. fold (deand a) (deand b) in Hd.
  destruct op;
    try (injection Hd as <- <-; split; [lia|]; exists 0; split; [lia|];
         rewrite Z.sub_0_r, Z.mod_small by (apply u64_range); reflexivity).
  - (* [comment removed for export] *)
    destruct (deand a) as [a' s1] eqn:Ha. destruct (deand b) as [b' s2] eqn:Hb. injection Hd as <- <-.
    destruct (IHa a' s1 eq_refl) as [Hs1 [ra [Hra Ea]]]. destruct (IHb b' s2 eq_refl) as [Hs2 [rb [Hrb Eb]]].
    split; [lia|]. exists (ra + rb). split; [lia|].
    cbn [edenot]. rewrite !u_add64, Ea, Eb. unfold two64.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    pose proof (u64_range (edenot E a')). pose proof (u64_range (edenot E b')).
    set (A1 := bv_unsigned (edenot E a')) in *. set (B1 := bv_unsigned (edenot E b')) in *.
    nia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - (* [comment removed for export] *)
    destruct b as [m| | | | | | |];
      try (injection Hd as <- <-; split; [lia|]; exists 0; split; [lia|];
           rewrite Z.sub_0_r, Z.mod_small by (apply u64_range); reflexivity).
    cbv zeta in Hd.
    set (m' := m mod two64) in Hd. set (j := Z.log2 (two64 - m')) in Hd.
    destruct (Z.eqb (two64 - m') (2 ^ j) && Z.leb j 48)%bool eqn:Ht;
      [|injection Hd as <- <-; split; [lia|]; exists 0; split; [lia|];
         rewrite Z.sub_0_r, Z.mod_small by (apply u64_range); reflexivity].
    apply andb_prop in Ht as [Hm Hj]. apply Z.eqb_eq in Hm. apply Z.leb_le in Hj.
    assert (Hj0 : 0 <= j) by (unfold j; apply Z.log2_nonneg).
    destruct (deand a) as [a' s0] eqn:Ha. injection Hd as <- <-.
    destruct (IHa a' s0 eq_refl) as [Hs0 [ra [Hra Ea]]].
    assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
    split; [lia|].
    set (X := bv_unsigned (edenot E a)) in *.
    pose proof (u64_range (edenot E a)) as HX. fold X in HX.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (Hr : 0 <= X mod 2 ^ j < 2 ^ j) by (apply Z.mod_pos_bound; lia).
    assert (Hr2 : X mod 2 ^ j <= X) by (apply Z.mod_le; lia).
    exists (ra + X mod 2 ^ j). split; [lia|].
    cbn [edenot]. rewrite u_and64, u_lit64. fold X. fold m'.
    assert (Hm' : 0 <= m' < two64) by (unfold m'; apply Z.mod_pos_bound; unfold two64; lia).
    replace m' with (2 ^ 64 - 2 ^ j) by (unfold two64 in *; lia).
    rewrite land_highmask by lia.
    pose proof (u64_range (edenot E a')) as HA'. set (A' := bv_unsigned (edenot E a')) in *.
    set (r := X mod 2 ^ j) in *. clearbody r.
    rewrite Ea. rewrite Ea in HX. nia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

#[using="Type"] Lemma deand_vars : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pbnd,$6:.Pe,$29.Pe',$29.Ps,$1.P,(3.(11.$29.$1.)(;3.R3.)(27.$29.$1.R2.R1.))P,(3.$20.(;4.R5.R4.)$22.)(3.$20.(;4.R6.R4.)$22.)")
(* [comment removed for export] *).
Proof.
  intros bnd e. induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|u w sx a IHa|bk bo bn bw];
    intros e' s Hd Hv; try (cbn [deand] in Hd; injection Hd as <- <-; exact Hv).
  cbn [deand] in Hd. fold (deand a) (deand b) in Hd.
  pose proof Hv as Hv0.
  cbn [AP.expr_vars_lt] in Hv. apply andb_prop in Hv as [Hva Hvb].
  destruct op; try (injection Hd as <- <-; exact Hv0).
  - destruct (deand a) as [a' s1] eqn:Ha. destruct (deand b) as [b' s2] eqn:Hb. injection Hd as <- <-.
    cbn [AP.expr_vars_lt]. rewrite (IHa a' s1 eq_refl Hva), (IHb b' s2 eq_refl Hvb). reflexivity.
  - destruct b as [m| | | | | | |]; try (injection Hd as <- <-; exact Hv0).
    cbv zeta in Hd.
    destruct (Z.eqb _ _ && Z.leb _ 48)%bool; [|injection Hd as <- <-; exact Hv0].
    destruct (deand a) as [a' s0] eqn:Ha. injection Hd as <- <-. exact (IHa a' s0 eq_refl Hva).
Qed.

#[using="Type"] Lemma xb2_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)Pe,$29.Plo,$1.Phi,$1.P,(64.VSEGS,R6.R5.R4.)P,(3.(23.(11.$1.$1.))(;5.R5.R4.)(82.(11.$1.$1.)(27.$1.$1.R3.R2.)))(5.(2.R4.(15.&40.(52.R8.R5.)))(2.(15.&40.(52.R8.R5.))R3.))")
(* [comment removed for export] *).
Proof.
  intros E M k e lo hi HK H. unfold xb2 in H.
  set (plain := match xlo1 k e, xhi1 k e with Some lo, Some hi => Some (lo, hi) | _, _ => None end) in H.
  assert (HP : forall lo hi, plain = Some (lo, hi) -> lo <= bv_unsigned (edenot E e) <= hi).
  { intros l h Hp. unfold plain in Hp.
    destruct (xlo1 k e) as [l1|] eqn:H1; [|discriminate]. destruct (xhi1 k e) as [h1|] eqn:H2; [|discriminate].
    injection Hp as <- <-. split; [eapply xlo1_sound; eassumption | eapply xhi1_sound; eassumption]. }
  destruct (deand e) as [e' s] eqn:Hd.
  destruct (deand_sound E e e' s Hd) as [Hs [rho [Hrho Ee]]].
  destruct (Z.eqb s 0); [exact (HP lo hi H)|].
  destruct (xlo1 k e') as [lo'|] eqn:H1; [|exact (HP lo hi H)].
  destruct (xhi1 k e') as [hi'|] eqn:H2; [|exact (HP lo hi H)].
  destruct (Z.leb s lo') eqn:Hsl; [|exact (HP lo hi H)]. apply Z.leb_le in Hsl.
  pose proof (xlo1_sound E M k e' lo' HK H1) as L1. pose proof (xhi1_sound E M k e' hi' HK H2) as L2.
  pose proof (u64_range (edenot E e')) as R'.
  assert (Hue : bv_unsigned (edenot E e) = bv_unsigned (edenot E e') - rho) by (rewrite Ee; apply Z.mod_small; lia).
  destruct plain as [[l0 h0]|].
  - specialize (HP l0 h0 eq_refl). injection H as <- <-. lia.
  - injection H as <- <-. lia.
Qed.

#[using="Type"] Lemma xlo2_sound : forall E M k e lo, know_ok SEGS E M k -> xlo2 k e = Some lo -> lo <= bv_unsigned (edenot E e).
Proof.
  intros E M k e lo HK H. unfold xlo2 in H. destruct (xb2 k e) as [[l h]|] eqn:Hb; [|discriminate].
  injection H as <-. exact (proj1 (xb2_sound E M k e l h HK Hb)).
Qed.

#[using="Type"] Lemma xhi2_sound : forall E M k e hi, know_ok SEGS E M k -> xhi2 k e = Some hi -> bv_unsigned (edenot E e) <= hi.
Proof.
  intros E M k e hi HK H. unfold xhi2 in H. destruct (xb2 k e) as [[l h]|] eqn:Hb; [|discriminate].
  injection H as <-. exact (proj2 (xb2_sound E M k e l h HK Hb)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma residue_fact_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PE',$0.PM,P,(12.&40.)(23.(12.&8.))PM',P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)Pe,$29.Pne,$29.P,(64.VSEGS,R7.R5.R3.)P,(3.(12.&40.)(52.R7.R2.)(52.R8.R3.))P,Pe',$29.Ps,$1.P,(3.(11.$29.$1.)(;3.R6.)(27.$29.$1.R2.R1.))(3.(12.&40.)(52.R;.R3.)(52.R<.R3.))(64.VSEGS,R9.R7.(;6.R6.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros E E' M M' k e ne HK Hne Hag. unfold residue_fact.
  destruct (deand e) as [e' s] eqn:Hd. destruct (Z.ltb 0 s) eqn:Hs; [|constructor].
  destruct (xlo1 k e') as [lo'|] eqn:H1; [|constructor]. destruct (xhi1 k e') as [hi'|] eqn:H2; [|constructor].
  destruct (Z.leb s lo') eqn:Hsl; [|constructor]. apply Z.leb_le in Hsl.
  constructor; [|constructor]. cbn [kentry_ok]. unfold esub. rewrite mkAlu_denot, u_sub64, Hne, (Hag e' s eq_refl).
  destruct (deand_sound E e e' s Hd) as [Hs0 [rho [Hrho Ee]]].
  pose proof (xlo1_sound E M k e' lo' HK H1) as L1. pose proof (u64_range (edenot E e')) as R'.
  assert (Hue : bv_unsigned (edenot E e) = bv_unsigned (edenot E e') - rho) by (rewrite Ee; apply Z.mod_small; lia).
  rewrite Hue. replace (bv_unsigned (edenot E e') - (bv_unsigned (edenot E e') - rho)) with rho by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

#[using="Type"] Lemma fact_ok_sound : forall E M k K, know_ok SEGS E M k -> fact_ok k K = true -> kentry_ok SEGS E M K.
Proof.
  intros E M k K HK H. destruct K as [| | | |e m|e lo hi| |[b1 k1] n1 [b2 k2] n2| |]; try discriminate; cbn [fact_ok] in H.
  - (* [comment removed for export] *) apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. cbn [kentry_ok]. split; [exact H1|].
    destruct (ealign_sound SEGS E M k e HK) as [Hr Hd].
    rewrite H2. apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hd]. apply pow2_divide_le. split; [apply Z.log2_nonneg | exact H3].
  - (* [comment removed for export] *) destruct (xlo2 k e) as [l|] eqn:Hl; [|discriminate]. destruct (xhi2 k e) as [h|] eqn:Hh; [|discriminate].
    apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (xlo2_sound E M k e l HK Hl). pose proof (xhi2_sound E M k e h HK Hh). cbn [kentry_ok]. lia.
  - (* [comment removed for export] *) cbn [kentry_ok]. exact (ranges_apart_x_sound SEGS E M k b1 k1 n1 b2 k2 n2 HK H).
Qed.

#[using="Type"] Lemma fact_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.PK,$68.P,(57.R6.R5.R4.R3.R2.)P,(3.$20.(;7.(6<.R6.)R2.)$22.)(57.R8.(;8.R7.(26.$68.R3.(2=.$68.)))R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model K HC H. unfold add_kn. apply cs_ok_set_kn; [exact HC|].
  constructor; [eapply fact_ok_sound; [exact (co_know _ _ _ _ _ HC) | exact H] | exact (co_know _ _ _ _ _ HC)].
Qed.

#[using="Type"] Lemma regs_ok_ext_eq : forall E sr sr' R, sr = sr' -> regs_ok E sr R -> regs_ok E sr' R.
Proof. intros; subst; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma entails_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.Pch,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.P,(57.R6.R5.R3.R2.R1.)P,(3.$20.(;9.R6.R5.)$22.)(5.(57.R8.R6.R5.R4.R3.)(3.$1.(83.R6.)(83.R7.)))")
(* [comment removed for export] *).
Proof.
  intros E cs ch R FULL model HC H. unfold entails in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc. split; [|symmetry; exact Hpc].
  match goal with Hl : match s_log (a_ss ch) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss ch)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
  match goal with Hr : list_eqb expr_eqb _ _ = true |- _ => apply (list_eqb_eq expr_eqb expr_eqb_eq) in Hr; rename Hr into Hregs end.
  match goal with Hm : list_eqb amap_eqb _ _ = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hm; rename Hm into Hmaps end.
  match goal with Ha : list_eqb pair_eqb (a_vis cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Hallow end.
  match goal with Hg : list_eqb pair_eqb (a_ghost cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hg; rename Hg into Hghost end.
  match goal with Hs : list_eqb pair_eqb (a_sub cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hs; rename Hs into Hsub end.   (* [comment removed for export] *)
  match goal with Hb : expr_eqb (a_brk cs) _ = true |- _ => apply expr_eqb_eq in Hb; rename Hb into Hbrk end.
  match goal with Hf : afd_eqb _ _ = true |- _ => apply afd_eqb_eq in Hf; rename Hf into Hfd end.
  match goal with Ht : Bool.eqb _ _ = true |- _ => apply eqb_prop in Ht; rename Ht into Htid end.
  match goal with Hk : forallb _ (kn ch) = true |- _ => rename Hk into Hkn end.
  repeat match goal with Hz : Z.leb _ _ = true |- _ => apply Z.leb_le in Hz end.
  assert (HA : allowA E ch = allowA E cs) by (unfold allowA; rewrite Hallow, Hghost; reflexivity).
  assert (HH : hid E ch model = hid E cs model) by (apply hid_ext; symmetry; exact Hallow).
  destruct HC; constructor; rewrite <- ?Hregs, <- ?Hmaps, <- ?Hallow, <- ?Hghost, <- ?Hsub, <- ?Hbrk, <- ?Hfd, <- ?Htid, ?HA; try assumption.
  - unfold Mr. rewrite HH. unfold know_ok. apply Forall_forall. intros K Hin.
    pose proof (proj1 (forallb_forall _ _) Hkn K Hin) as HK. apply existsb_exists in HK as [K' [Hin' Heq]].
    apply kentry_eqb_eq in Heq. subst K'. exact (proj1 (Forall_forall _ _) co_know0 K Hin').
  - eapply holes_mono; [exact co_holes0 | lia].
  - lia.
  - lia.
  - lia.
  - intros a. rewrite HH. replace (in_ghost E ch) with (in_ghost E cs) by (unfold in_ghost, in_ghostl; rewrite Hghost; reflexivity). exact (co_zero0 a).
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma ridx_lit : forall n, (n < 32)%nat -> ridx (Z_to_bv 5 (Z.of_nat n)) = n.
Proof.
  intros n Hn. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.

#[using="Type"] Lemma reg_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pn,$6:.P,(57.R6.R5.R4.R3.R2.)P,(5.(;:.#0.R2.)(;:.R2.#20.))(3.(12.&40.)(;;.R6.(42.&5.(86.R3.)))(52.R8.(;<.R7.R3.)))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model n HC Hn. rewrite (co_regs _ _ _ _ _ HC). unfold sr_get, reg.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz. rewrite ridx_lit by lia. reflexivity.
Qed.

#[using="Type"] Lemma lit_of_sound : forall E e z, lit_of e = Some z -> edenot E e = Z_to_bv 64 z /\ (0 <= z < two64)%Z.
Proof.
  intros E e z H. destruct e; try discriminate. cbn [lit_of] in H. injection H as <-.
  split; [| unfold two64; apply Z.mod_pos_bound; lia].
  cbn [edenot]. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

#[using="Type"] Lemma reg_lit_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pn,$6:.Pz,$1.P,(57.R7.R6.R5.R4.R3.)P,(5.(;:.#0.R3.)(;:.R3.#20.))P,(3.(23.$1.)(;=.R8.R4.)(82.$1.R3.))(5.(3.(12.&40.)(;;.R8.(42.&5.(86.R5.)))(42.&40.R4.))(5.(2.=R4.)(1?.R4.$;>.)))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model n z HC Hn H. unfold reg_lit in H.
  destruct (lit_of_sound E (reg cs n) z H) as [He Hz]. rewrite (reg_sound E cs R FULL model n HC Hn), He. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma regs_ok_respell : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Psr,(2?.$29.)PR,(55.&5.(12.&40.))Pn,$6:.Pe,$29.P,(60.R5.R4.R3.)P,(5.(;:.#0.R3.)(;:.R3.#20.))P,(3.(12.&40.)(52.R7.R3.)(52.R7.(;?.$29.R4.R6.(<0.=))))(60.R8.(<1.R7.R5.R4.)R6.)")
(* [comment removed for export] *).
Proof.
  intros E sr R n e HR Hn He.
  replace (sr_upd sr n e) with (sr_upd sr (ridx (Z_to_bv 5 (Z.of_nat n))) e) by (rewrite ridx_lit by lia; reflexivity).
  apply regs_ok_pin; [exact HR|].
  rewrite (HR (Z_to_bv 5 (Z.of_nat n))). unfold sr_get.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz, ridx_lit by lia. symmetry. exact He.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma regs_ok_set_n : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Psr,(2?.$29.)PR,(55.&5.(12.&40.))Pn,$6:.Pe,$29.Pv,(12.&40.)P,(60.R6.R5.R4.)P,(5.(;:.#0.R4.)(;:.R4.#20.))P,(3.(12.&40.)(52.R8.R4.)R3.)(60.R9.(<1.R8.R6.R5.)(<2.R7.(42.&5.(86.R6.))R4.))")
(* [comment removed for export] *).
Proof.
  intros E sr R n e v HR Hn He.
  replace (sr_upd sr n e) with (sr_upd sr (ridx (Z_to_bv 5 (Z.of_nat n))) e) by (rewrite ridx_lit by lia; reflexivity).
  apply regs_ok_set; [exact HR | | exact He].
  intros Hz. apply (f_equal bv_unsigned) in Hz. rewrite Z_to_bv_unsigned in Hz. unfold bv_wrap in Hz.
  change (bv_modulus 5) with 32%Z in Hz. rewrite Z.mod_small in Hz by lia.
  replace (bv_unsigned (0%bv : bv 5)) with 0%Z in Hz by reflexivity. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fresh_ok_parts : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pcs,$2>.P,(3.$20.(<3.Vnx0,R1.)$22.)(5.(3.$20.(9=.(:4.R2.)(61.(<4.R2.)))$22.)(5.(3.$20.(9<.(:4.R2.)(6<.R2.))$22.)(5.(3.$20.(<5.(:4.R2.)(8;.R2.))$22.)(5.(3.$20.(<6.(:4.R2.)(31.(11.$29.$29.)(8<.R2.)(30.R2.)))$22.)(5.(3.$20.(;4.(:4.R2.)(<7.R2.))$22.)(5.(3.$20.(<8.(:4.R2.)(<9.R2.))$22.)(<:.Vnx0,(:4.R2.))))))))")
(* [comment removed for export] *).
Proof.
  intros cs H. unfold fresh_ok in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Nat.leb_le in X. repeat split; try assumption.
  unfold pairs_vars_lt in *. rewrite forallb_app. apply andb_true_intro. split; assumption.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma fresh_ok_sub : forall cs, fresh_ok nx0 cs = true -> pairs_vars_lt (nxt cs) (a_sub cs) = true.
Proof.
  intros cs H. unfold fresh_ok in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end. assumption.
Qed.

#[using="Type"] Lemma allowA_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.Pcs,$2>.P,(9;.R4.R3.R2.)P,(3.$20.(<6.R5.(31.(11.$29.$29.)(8<.R2.)(30.R2.)))$22.)(3.(2?.(11.$1.$1.))(5:.R4.R3.)(5:.R5.R3.))")
(* [comment removed for export] *).
Proof.
  intros b E E' cs Hag H. unfold allowA. rewrite !flat_map_concat_map.
  f_equal; f_equal; apply map_ext_in; intros p Hin;
    (pose proof (proj1 (forallb_forall _ _) H p ltac:(apply in_app_iff; first [left; exact Hin | right; exact Hin])) as Hp); apply andb_prop in Hp as [H1 H2];
    unfold allow1, allow_sh, sh_lo, sh_hi, uE; rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2); reflexivity.
Qed.

#[using="Type"] Lemma in_allow_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.Pcs,$2>.P,(9;.R4.R3.R2.)P,(3.$20.(<6.R5.(8<.R2.))$22.)(3.Pz,$1.$20.(40.R4.R3.)(40.R5.R3.))")
(* [comment removed for export] *).
Proof.
  intros b E E' cs Hag H. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh. unfold pairs_vars_lt in H.
  induction (a_vis cs) as [|p l IH]; [reflexivity|]. cbn [existsb forallb] in H |- *.
  apply andb_prop in H as [Hp Hl]. apply andb_prop in Hp as [H1 H2].
  unfold sh_lo, sh_hi, uE in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
  pose proof (IH Hl) as E1. apply (f_equal negb) in E1. rewrite !negb_orb in E1.
  apply (f_equal negb) in E1. rewrite !negb_andb, !negb_involutive in E1.
  destruct (existsb _ l), (existsb _ l), (existsb _ l), (existsb _ l); cbn in E1 |- *; rewrite ?orb_true_r, ?orb_false_r; try reflexivity; try discriminate.
Qed.

#[using="Type"] Lemma in_ghostl_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.Pcs,$2>.P,(9;.R4.R3.R2.)P,(3.$20.(<6.R5.(31.(11.$29.$29.)(8<.R2.)(30.R2.)))$22.)(3.Pz,$1.$20.(<;.R4.R3.)(<;.R5.R3.))")
(* [comment removed for export] *).
Proof.
  intros b E E' cs Hag H. apply functional_extensionality. intros z. unfold in_ghostl.
  unfold pairs_vars_lt in H. rewrite forallb_app in H. apply andb_prop in H as [_ H].
  induction (a_ghost cs) as [|p l IH]; [reflexivity|]. cbn [existsb forallb] in H |- *.
  apply andb_prop in H as [Hp Hl]. apply andb_prop in Hp as [H1 H2].
  unfold uE in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2), (IH Hl). reflexivity.
Qed.
#[using="Type"] Lemma in_ghost_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.Pcs,$2>.P,(9;.R4.R3.R2.)P,(3.$20.(<6.R5.(31.(11.$29.$29.)(8<.R2.)(30.R2.)))$22.)(3.Pz,$1.$20.(32.R4.R3.)(32.R5.R3.))")
(* [comment removed for export] *).
Proof. intros b E E' cs Hag H. apply in_ghost_of_l. exact (in_ghostl_agree b E E' cs Hag H). Qed.

#[using="argH_agree"] Lemma hid_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.Pcs,$2>.Pmodel,$56.P,(9;.R5.R4.R3.)P,(<:.Vnx0,R6.)P,(3.$20.(<6.R7.(31.(11.$29.$29.)(8<.R4.)(30.R4.)))$22.)(3.Pa,(12.&40.)$20.(59.R6.R5.R4.)(59.R7.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros b E E' cs model Hag Hle H. apply functional_extensionality. intros a. unfold hid, vis.
  assert (H' : pairs_vars_lt b (a_vis cs) = true).
  { unfold pairs_vars_lt in *. rewrite forallb_app in H. apply andb_prop in H as [H _]. exact H. }
  rewrite (in_allow_agree b E E' cs Hag H'). rewrite (argH_agree E E' a) by (eapply env_agree_le; eassumption). reflexivity.
Qed.

#[using="Type"] Lemma maps_den_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.Pms,(2?.$48.)P,(9;.R4.R3.R2.)P,(3.$20.(<5.R5.R2.)$22.)(3.(2?.(11.(12.&40.)(12.&40.)))(97.$48.(11.(12.&40.)(12.&40.))(96.R4.)R3.)(97.$48.(11.(12.&40.)(12.&40.))(96.R5.)R3.))")
(* [comment removed for export] *).
Proof.
  intros b E E' ms Hag H. apply map_ext_in. intros m Hin.
  pose proof (proj1 (forallb_forall _ _) H m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
  unfold amap_den. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2). reflexivity.
Qed.

#[using="Type"] Lemma maps_match_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.Pms,(2?.$48.)Pl,(2?.(11.(12.&40.)(12.&40.)))P,(9;.R5.R4.R3.)P,(3.$20.(<5.R6.R3.)$22.)P,(93.R6.R4.R3.)(93.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros b E E' ms. induction ms as [|m ms IH]; intros l Hag H HM; cbn [maps_match] in *; [exact HM|].
  cbn [maps_vars_lt forallb] in H. apply andb_prop in H as [Hm Hr]. apply andb_prop in Hm as [H1 H2].
  unfold uE, amap_den in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
  destruct (is_fog m).
  - destruct HM as [HM|(iv & l' & -> & Hsz & HM)]; [left; exact (IH _ Hag Hr HM) | right].
    exists iv, l'. split; [reflexivity|]. split; [exact Hsz | exact (IH _ Hag Hr HM)].
  - destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | exact (IH _ Hag Hr HM)].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma holes_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.Py,$1.Pl,(2?.(11.(12.&40.)(12.&40.)))Pms,(2?.$48.)P,(9;.R6.R5.R4.)P,(3.$20.(<5.R7.R2.)$22.)P,(1;.$48.(49.R7.R5.R4.)R3.)(1;.$48.(49.R7.R6.R5.)R4.)")
(* [comment removed for export] *).
Proof.
  intros b E E' y l ms Hag Hv H. apply Forall_forall. intros m Hin Hh.
  pose proof (proj1 (forallb_forall _ _) Hv m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
  unfold hole_ok, uE in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
  exact (proj1 (Forall_forall _ _) H m Hin Hh).
Qed.

#[using="Type"] Lemma fds_ok_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.Pf,$89.Pmodel,$56.P,(9;.R5.R4.R3.)P,(3.$20.(<8.R6.R3.)$22.)P,(<<.R6.R4.R3.)(<<.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros b E E' f model Hag Hv H. destruct f as [|k len off|]; try exact H.
  cbn [fd_vars_lt] in Hv. apply andb_prop in Hv as [Hl Ho].
  destruct H as [p [c (H1 & H2 & H3 & H4 & H5)]]. exists p, c.
  unfold uE in *. rewrite <- (edenot_agree' b E E' _ Hag Hl), <- (edenot_agree' b E E' _ Hag Ho).
  destruct Hag as [_ Heb]. rewrite <- Heb. repeat split; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma env_agree_sym0 : forall b E E', env_agree b E E' -> env_agree b E' E.
Proof. intros b E E' [H1 H2]. split; [intros n Hn; symmetry; apply H1; exact Hn | symmetry; exact H2]. Qed.
#[using="Type"] Lemma born_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.Pms,(2?.$48.)Pks,(2?.$4?.)Piv,(11.(12.&40.)(12.&40.))P,(9;.R6.R5.R4.)P,(3.$20.(<5.R7.R4.)$22.)P,(4=.R7.R5.R4.R3.)(4=.R7.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros b E E' ms ks iv Hag Hms (m & Hin & Hf & Hk & Hd). exists m. split; [exact Hin|]. split; [exact Hf|]. split; [exact Hk|].
  pose proof (proj1 (forallb_forall _ _) Hms m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
  unfold amap_den in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2). exact Hd.
Qed.
#[using="Type"] Lemma nlz_ok_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.Pms,(2?.$48.)Pks,(2?.$4?.)PM,(2?.(11.(12.&40.)(12.&40.)))PX,(2?.(11.(12.&40.)(12.&40.)))P,(9;.R7.R6.R5.)P,(3.$20.(<5.R8.R5.)$22.)P,(<=.R8.R6.R5.R4.R3.)(<=.R8.R7.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros b E E' ms ks M X Hag Hms H e He. destruct (H e He) as (P & iv & Hiv & B1 & B2 & NB). split; [exact P|].
  exists iv. split; [exact Hiv|]. split; [exact B1|]. split; [exact B2|]. intros Hb. apply NB.
  eapply born_agree; [apply env_agree_sym0; exact Hag | exact Hms | exact Hb].
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma nlz_ok_weaken : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pms,(2?.$48.)Pms',(2?.$48.)Pks,(2?.$4?.)PM,(2?.(11.(12.&40.)(12.&40.)))PX,(2?.(11.(12.&40.)(12.&40.)))P,Pm',$48.P,(34.$48.R1.R5.)P,(3.$20.(4>.R2.)$33.)P,(34.$4?.(50.R3.)R6.)(4:.$48.Lm,$48.(5.(34.$48.R1.R:.)(5.(3.$20.(4>.R1.)$33.)(5.(34.$4?.(50.R1.)R8.)(3.(11.(12.&40.)(12.&40.))(96.R;.R1.)(96.R;.R5.))))))P,(<=.R7.R6.R4.R3.R2.)(<=.R8.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros E ms ms' ks M X Hsub H e He. destruct (H e He) as (P & iv & Hiv & B1 & B2 & NB). split; [exact P|].
  exists iv. split; [exact Hiv|]. split; [exact B1|]. split; [exact B2|]. intros (m' & Hin' & Hf' & Hk' & Hd'). apply NB.
  destruct (Hsub m' Hin' Hf' Hk') as (m & Hin & Hf & Hk & Hd). exists m. rewrite Hd, Hd'. auto.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma nlz_ok_maps_mono : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pms,(2?.$48.)Pks,(2?.$4?.)PM,(2?.(11.(12.&40.)(12.&40.)))PM',(2?.(11.(12.&40.)(12.&40.)))PX,(2?.(11.(12.&40.)(12.&40.)))P,Piv,(11.(12.&40.)(12.&40.))P,(34.(11.(12.&40.)(12.&40.))R1.R4.)(34.(11.(12.&40.)(12.&40.))R2.R4.)P,(<=.R7.R6.R5.R4.R2.)(<=.R8.R7.R6.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros E ms ks M M' X HM H e He. destruct (H e He) as (P & iv & Hiv & B1 & B2 & NB). split; [exact P|].
  exists iv. split; [apply HM; exact Hiv|]. auto.
Qed.
#[using="Type"] Lemma sub_ok_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.PM,(2?.(11.(12.&40.)(12.&40.)))PN,(2?.(11.(12.&40.)(12.&40.)))PLz,(2?.(11.(12.&40.)(12.&40.)))Pt,(11.$29.$29.)P,(9;.R7.R6.R5.)P,(3.$20.(;4.R8.(16.$29.$29.R2.))$22.)P,(3.$20.(;4.R9.(19.$29.$29.R3.))$22.)P,(<>.R9.R7.R6.R5.R4.)(<>.R9.R8.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros b E E' M N Lz t Hag H1 H2 H. unfold sub_ok, uE in *.
  rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2). exact H.
Qed.
#[using="Type"] Lemma sub_Forall_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.PM,(2?.(11.(12.&40.)(12.&40.)))PN,(2?.(11.(12.&40.)(12.&40.)))PLz,(2?.(11.(12.&40.)(12.&40.)))Pl,(2?.(11.$29.$29.))P,(9;.R7.R6.R5.)P,(3.$20.(<6.R8.R2.)$22.)P,(1;.(11.$29.$29.)(<>.R8.R6.R5.R4.)R3.)(1;.(11.$29.$29.)(<>.R8.R7.R6.R5.)R4.)")
(* [comment removed for export] *).
Proof.
  intros b E E' M N Lz l Hag Hl H. apply Forall_forall. intros t Ht.
  pose proof (proj1 (forallb_forall _ _) Hl t Ht) as X. apply andb_prop in X as [X1 X2].
  eapply sub_ok_agree; [exact Hag | exact X1 | exact X2 | exact (proj1 (Forall_forall _ _) H t Ht)].
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma def_Forall_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.PF,P,(12.&40.)(23.(12.&8.))Pms,(2?.$48.)P,(9;.R5.R4.R3.)P,(3.$20.(<5.R6.R2.)$22.)P,(1;.$48.(<?.R6.R4.)R3.)(1;.$48.(<?.R6.R5.)R4.)")
(* [comment removed for export] *).
Proof.
  intros b E E' F ms Hag Hms H. apply Forall_forall. intros m Hin Hf Hk a Ha.
  pose proof (proj1 (forallb_forall _ _) Hms m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
  rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2) in Ha.
  exact (proj1 (Forall_forall _ _) H m Hin Hf Hk a Ha).
Qed.
#[using="Type"] Lemma def_Forall_mono : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PF,Px,(12.&40.)(23.(12.&8.))PF',Px,(12.&40.)(23.(12.&8.))Pms,(2?.$48.)P,Pa,(12.&40.)P,(24.(3.(23.(12.&8.))A1.R4.R1.(25.(12.&8.))))(24.(3.(23.(12.&8.))A1.R4.R2.(25.(12.&8.))))P,(1;.$48.(<?.R5.R4.)R2.)(1;.$48.(<?.R6.R4.)R3.)")
(* [comment removed for export] *).
Proof. intros E F F' ms HF H. apply Forall_forall. intros m Hin Hf Hk a Ha. apply HF. exact (proj1 (Forall_forall _ _) H m Hin Hf Hk a Ha). Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma def_Forall_weaken : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PF,P,(12.&40.)(23.(12.&8.))Pms,(2?.$48.)Pms',(2?.$48.)P,Pm',$48.P,(34.$48.R1.R2.)P,(3.$20.(4>.R2.)$33.)P,(34.$4?.(50.R3.)$51.)(4:.$48.Lm,$48.(5.(34.$48.R1.R7.)(5.(3.$20.(4>.R1.)$33.)(5.(34.$4?.(50.R1.)$51.)(3.(11.(12.&40.)(12.&40.))(96.R9.R1.)(96.R9.R5.))))))P,(1;.$48.(<?.R5.R4.)R3.)(1;.$48.(<?.R6.R5.)R3.)")
(* [comment removed for export] *).
Proof.
  intros E F ms ms' Hw H. apply Forall_forall. intros m' Hin Hf Hk a Ha.
  destruct (Hw m' Hin Hf Hk) as (m & Hm & Hfm & Hkm & Hd). unfold amap_den in Hd. injection Hd as Hd1 Hd2.
  rewrite <- Hd1, <- Hd2 in Ha. exact (proj1 (Forall_forall _ _) H m Hm Hfm Hkm a Ha).
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma in_tok_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.Pz,$1.Pt,(11.$29.$29.)P,(9;.R5.R4.R3.)P,(3.$20.(;4.R6.(16.$29.$29.R2.))$22.)P,(3.$20.(;4.R7.(19.$29.$29.R3.))$22.)P,(54.R7.R5.R4.)(54.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros b E E' z t Hag H1 H2 H. unfold in_tok, uE in *.
  rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2). exact H.
Qed.
#[using="Type"] Lemma cov_Forall_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.PN,(2?.(11.(12.&40.)(12.&40.)))Psub,(2?.(11.$29.$29.))Pms,(2?.$48.)P,(9;.R6.R5.R4.)P,(3.$20.(<5.R7.R2.)$22.)P,(3.$20.(<6.R8.R4.)$22.)P,(1;.$48.(=0.R8.R6.R5.)R4.)(1;.$48.(=0.R8.R7.R6.)R5.)")
(* [comment removed for export] *).
Proof.
  intros b E E' N sub ms Hag Hms Hsub H. apply Forall_forall. intros m Hin Hk z Hz.
  pose proof (proj1 (forallb_forall _ _) Hms m Hin) as Hm. apply andb_prop in Hm as [H1 H2]. unfold uE in Hz.
  rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2) in Hz.
  destruct (proj1 (Forall_forall _ _) H m Hin Hk z Hz) as [Hn|(t & Ht & Hzt)]; [left; exact Hn | right].
  exists t. split; [exact Ht|]. pose proof (proj1 (forallb_forall _ _) Hsub t Ht) as X. apply andb_prop in X as [X1 X2].
  eapply in_tok_agree; eassumption.
Qed.
#[using="Type"] Lemma cov_Forall_weaken : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PN,(2?.(11.(12.&40.)(12.&40.)))Psub,(2?.(11.$29.$29.))Pms,(2?.$48.)Pms',(2?.$48.)P,Pm',$48.P,(34.$48.R1.R2.)P,(34.$4?.(50.R2.)$53.)(4:.$48.Lm,$48.(5.(34.$48.R1.R6.)(5.(34.$4?.(50.R1.)$53.)(3.(11.(12.&40.)(12.&40.))(96.R9.R1.)(96.R9.R4.)))))P,(1;.$48.(=0.R6.R5.R4.)R3.)(1;.$48.(=0.R7.R6.R5.)R3.)")
(* [comment removed for export] *).
Proof.
  intros E N sub ms ms' Hw H. apply Forall_forall. intros m' Hin Hk z Hz.
  destruct (Hw m' Hin Hk) as (m & Hm & Hkm & Hd). unfold amap_den in Hd. injection Hd as Hd1 Hd2. unfold uE in Hz.
  rewrite <- Hd1, <- Hd2 in Hz. exact (proj1 (Forall_forall _ _) H m Hm Hkm z Hz).
Qed.
#[using="Type"] Lemma cov_Forall_mono : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PN,(2?.(11.(12.&40.)(12.&40.)))PN',(2?.(11.(12.&40.)(12.&40.)))Psub,(2?.(11.$29.$29.))Psub',(2?.(11.$29.$29.))Pms,(2?.$48.)P,Pz,$1.P,(3.$20.(21.R1.R6.)$22.)(3.$20.(21.R2.R6.)$22.)P,Pt,(11.$29.$29.)P,(34.(11.$29.$29.)R1.R5.)(34.(11.$29.$29.)R2.R5.)P,(1;.$48.(=0.R8.R7.R5.)R3.)(1;.$48.(=0.R9.R7.R5.)R4.)")
(* [comment removed for export] *).
Proof.
  intros E N N' sub sub' ms HN0 HS0 H. apply Forall_forall. intros m Hin Hk z Hz.
  destruct (proj1 (Forall_forall _ _) H m Hin Hk z Hz) as [Hn|(t & Ht & Hzt)]; [left; exact (HN0 z Hn) | right; exists t; split; [exact (HS0 t Ht) | exact Hzt]].
Qed.

#[using="argH_agree SINV_agree"] Lemma cs_ok_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PE',$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.P,(9;.(:4.R4.)R6.R5.)P,(3.$20.(<3.Vnx0,R5.)$22.)P,(57.R8.R6.R5.R4.R3.)(57.R8.R7.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros E E' cs R FULL model Hag Hf HC.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (hid_agree (nxt cs) E E' cs model Hag Fle Fallow) as HH.
  pose proof (allowA_agree (nxt cs) E E' cs Hag Fallow) as HA.
  destruct HC; constructor; rewrite ?HA; try assumption.
  - eapply regs_ok_agree'; eassumption.
  - unfold Mr. rewrite HH. eapply know_ok_agree'; eassumption.
  - eapply fds_ok_agree; eassumption.
  - eapply maps_match_agree; [exact Hag | exact Fmaps | assumption].
  - eapply holes_agree; [exact Hag | exact Fmaps | assumption].
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk.
    pose proof (proj1 (forallb_forall _ _) Fmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
    unfold amap_den. rewrite <- (edenot_agree' (nxt cs) E E' _ Hag H1), <- (edenot_agree' (nxt cs) E E' _ Hag H2).
    exact (proj1 (Forall_forall _ _) co_none0 m Hin Hk).
  - apply Forall_forall. intros m Hin Hk a Ha.
    pose proof (proj1 (forallb_forall _ _) Fmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
    rewrite <- (edenot_agree' (nxt cs) E E' _ Hag H1), <- (edenot_agree' (nxt cs) E E' _ Hag H2) in Ha.
    exact (proj1 (Forall_forall _ _) co_kinds0 m Hin Hk a Ha).
  - rewrite <- (edenot_agree' (nxt cs) E E' _ Hag Fbrk). assumption.
  - intros a. rewrite HH, (in_ghost_agree (nxt cs) E E' cs Hag Fallow). exact (co_zero0 a).
  - eapply SINV_agree; [eapply env_agree_le; [exact Hag | exact Fle] | assumption].
  - (* [comment removed for export] *) eapply nlz_ok_agree; [exact Hag | exact Fmaps | assumption].
  - eapply nlz_ok_agree; [exact Hag | exact Fmaps | assumption].
  - eapply sub_Forall_agree; [exact Hag | exact (fresh_ok_sub cs Hf) | assumption].
  - (* [comment removed for export] *) eapply def_Forall_agree; [exact Hag | exact Fmaps | assumption].
  - (* [comment removed for export] *) eapply cov_Forall_agree; [exact Hag | exact Fmaps | exact (fresh_ok_sub cs Hf) | assumption].
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma fresh_ok_mono : forall gb cs, (nx0 <= gb)%nat -> fresh_ok gb cs = true -> fresh_ok nx0 cs = true.
Proof.
  intros gb cs Hle H. unfold fresh_ok in *.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Nat.leb_le in X.
  repeat (apply andb_true_intro; split); try assumption. apply Nat.leb_le. lia.
Qed.

#[using="IT_ok HS XN XE XB SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Lemma run_block_sound_R : forall (SR : config -> TSet -> Prop), srchain SR ->   (* [comment removed for export] *)
  forall gb bfuel stops cs cs' E R FULL model T,
  (nx0 <= gb)%nat ->
  run_block SEGS IT gb KC bfuel stops cs = Some cs' -> cs_ok E cs R FULL model ->
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      SR (cfg R' (pc cs') FULL' model') T) ->
  SR (cfg R (pc cs) FULL model) T.
Proof.
  intros SR SRch gb bfuel stops cs cs' E R FULL model T Hgb Hrb HC Hk.
  rewrite run_block_eq in Hrb. (* [comment removed for export] *) unfold run_block_ref in Hrb.
  destruct (fresh_ok gb cs) eqn:Hf0; [|discriminate].
  pose proof (fresh_ok_mono gb cs Hgb Hf0) as Hf.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (co_regs _ _ _ _ _ HC) as HR. pose proof (co_know _ _ _ _ _ HC) as HK.
  unfold kn in HK, Fkn. unfold nxt in Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle, Hk.
  destruct (a_ss cs) as [p sr log k nx rsv] eqn:Hss.
  cbn [s_know s_regs s_pc s_next] in Hrb, HR, HK, Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle, Hk.
  set (ss' := sym_execTX SEGS IT KC bfuel true stops (SS p sr [] k nx)) in Hrb.
  destruct (carry (s_log ss') (s_know ss') []) as [[kn' scs] hs] eqn:Hc.
  destruct scs; [|discriminate]. injection Hrb as <-.
  (* [comment removed for export] *)
  set (H := hid E cs model). set (MR := Mr E cs model FULL).
  rewrite sr_vars_lt_eq in Fsr. rewrite kn_vars_lt_eq in Fkn.
  pose proof (runTX_sound SEGS IT KC bfuel stops p sr k nx E MR (seg_rom SEGS) R IT_ok HR HK Fsr Fkn) as HX.
  cbn zeta in HX. fold ss' in HX. destruct HX as (E' & R' & Hag & Hle & HR' & Hlf & HK' & Hms & _).
  assert (Hagc : env_agree (nxt cs) E E') by (unfold nxt; rewrite Hss; exact Hag).
  pose proof (cs_ok_agree E E' cs R FULL model Hagc Hf HC) as HC'.
  assert (HH : hid E' cs model = H).
  { unfold H. eapply hid_agree; [exact Hagc | unfold nxt; rewrite Hss; exact Fle | unfold nxt; rewrite Hss; exact Fallow]. }
  unfold cfg_of, pc. rewrite Hss. cbn [a_ss s_pc].
  apply (SRch H (H_off_segments_cs E cs model) SEGS_wx (allowA E cs)
           (mkst R (Z_to_bv 64 p) FULL (seg_rom SEGS)) _ model T
           (lazy_cover_cs E cs R FULL model HC) (A_wf_allowA E cs) (co_minv _ _ _ _ _ HC) (co_halt _ _ _ _ _ HC) Hms).
  intros model' Hinv' Hsame Hclean.
  assert (HKc : know_ok SEGS E' (mem_denot E' MR (s_log ss')) kn').
  { eapply (carry_sound SEGS E' MR); [exact Hc | exact Hlf | exact HK' | constructor]. }
  set (FULL' := munrestrict H FULL (mem_denot E' MR (s_log ss'))).
  assert (Hmr' : Mr E' cs model FULL' = mem_denot E' MR (s_log ss')).
  { unfold Mr, FULL'. rewrite HH. apply mrestrict_munrestrict_clean. intros a Ha. exact (Hclean a Ha). }
  assert (Flec : (nx0 <= nxt cs)%nat) by (unfold nxt; rewrite Hss; exact Fle).
  assert (Fallowc : pairs_vars_lt (nxt cs) (a_vis cs ++ a_ghost cs) = true) by (unfold nxt; rewrite Hss; exact Fallow).
  specialize (Hk E' R' FULL' model' (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
  unfold cfg_of, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk.
  replace (unrestrict H (ms_mem (mkst R (Z_to_bv 64 p) FULL (seg_rom SEGS)))
             (mkst R' (Z_to_bv 64 (s_pc ss')) (mem_denot E' MR (s_log ss')) (seg_rom SEGS)))
    with (mkst R' (Z_to_bv 64 (s_pc ss')) FULL' (seg_rom SEGS)) by reflexivity.
  apply Hk.
  - eapply cs_ok_frame; [exact HC' | exact Hsame | | exact HR' | reflexivity | | | ].
    + rewrite (allowA_agree (nxt cs) E E' cs Hagc Fallowc). exact Hinv'.
    + cbn [mk_ss s_know]. rewrite Hmr'. exact HKc.
    + intros a Ha. rewrite HH in Ha. unfold FULL', munrestrict. rewrite Ha. reflexivity.
    + (* [comment removed for export] *)
      intros a Hdef. unfold FULL', munrestrict. destruct (H a) eqn:Ha; [exact Hdef|].
      apply (AX2S.mem_denot_grows E' MR (s_log ss') a). unfold MR, Mr, mrestrict. fold H. rewrite HH || idtac. rewrite Ha. exact Hdef.
  - pose proof (same_but_materialized_frame _ _ Hsame) as Hfr. apply Hfr.
Qed.

#[using="IT_ok HS XN XE XB SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Lemma run_block_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pgb,$6:.Pbfuel,$6:.Pstops,(2?.$1.)Pcs,$2>.Pcs',$2>.PE,$0.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.PT,$9>.P,(<:.Vnx0,R:.)P,(3.(23.$2>.)(=1.VSEGS,VIT,R;.VKC,R:.R9.R8.)(82.$2>.R7.))P,(57.R7.R9.R6.R5.R4.)P,PE',$0.PR',(55.&5.(12.&40.))PFULL',P,(12.&40.)(23.(12.&8.))Pmodel',$56.P,(5.(9;.Vnx0,R<.R4.)(9;.(:4.R>.)R<.R4.))P,(57.R5.R>.R4.R3.R2.)P,(3.$9?.(:5.R3.)(:5.R;.))(:6.VSEGS,(:7.VSEGS,R6.(83.R10.)R5.R4.)R;.)(:6.VSEGS,(:7.VSEGS,R8.(83.R;.)R7.R6.)R5.)")
(* [comment removed for export] *).
Proof. exact (run_block_sound_R (srealizes SEGS) srchain_srealizes). Qed.

#[using="IT_ok HS XN XE XB SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Lemma run_block_sound0 : forall gb bfuel stops cs cs' E R FULL model T,
  (nx0 <= gb)%nat ->
  run_block SEGS IT gb KC bfuel stops cs = Some cs' -> cs_ok E cs R FULL model ->
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes0 SEGS (cfg R' (pc cs') FULL' model') T) ->
  srealizes0 SEGS (cfg R (pc cs) FULL model) T.
Proof. exact (run_block_sound_R (srealizes0 SEGS) srchain_srealizes0). Qed.

#[using="IT_ok HS XN XE XB SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Lemma run_block_gc_sound_R : forall (SR : config -> TSet -> Prop), srchain SR ->   (* [comment removed for export] *)
  forall gb bfuel stops cs cs' E R FULL model T,
  (nx0 <= gb)%nat ->
  run_block_gc SEGS IT gb KC bfuel stops cs = Some cs' -> cs_ok E cs R FULL model ->
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      SR (cfg R' (pc cs') FULL' model') T) ->
  SR (cfg R (pc cs) FULL model) T.
Proof.
  intros SR SRch gb bfuel stops cs cs' E R FULL model T Hgb H HC Hk. unfold run_block_gc in H.
  destruct (run_block SEGS IT gb KC bfuel stops cs) as [cs1|] eqn:Hrb; [|discriminate]. injection H as <-.
  eapply (run_block_sound_R SR SRch); [exact Hgb | exact Hrb | exact HC |].
  intros E' R' FULL' model' Hag HC1 Hfs. rewrite <- (pc_cs_gc gb cs1). apply (Hk E' R' FULL' model'); [exact Hag | apply cs_gc_ok; exact HC1 | exact Hfs].
Qed.

#[using="IT_ok HS XN XE XB SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Lemma run_block_gc_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pgb,$6:.Pbfuel,$6:.Pstops,(2?.$1.)Pcs,$2>.Pcs',$2>.PE,$0.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.PT,$9>.P,(<:.Vnx0,R:.)P,(3.(23.$2>.)(=2.VSEGS,VIT,R;.VKC,R:.R9.R8.)(82.$2>.R7.))P,(57.R7.R9.R6.R5.R4.)P,PE',$0.PR',(55.&5.(12.&40.))PFULL',P,(12.&40.)(23.(12.&8.))Pmodel',$56.P,(5.(9;.Vnx0,R<.R4.)(9;.(:4.R>.)R<.R4.))P,(57.R5.R>.R4.R3.R2.)P,(3.$9?.(:5.R3.)(:5.R;.))(:6.VSEGS,(:7.VSEGS,R6.(83.R10.)R5.R4.)R;.)(:6.VSEGS,(:7.VSEGS,R8.(83.R;.)R7.R6.)R5.)")
(* [comment removed for export] *).
Proof. exact (run_block_gc_sound_R (srealizes SEGS) srchain_srealizes). Qed.

#[using="IT_ok HS XN XE XB SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Lemma run_block_gc_sound0 : forall gb bfuel stops cs cs' E R FULL model T,
  (nx0 <= gb)%nat ->
  run_block_gc SEGS IT gb KC bfuel stops cs = Some cs' -> cs_ok E cs R FULL model ->
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes0 SEGS (cfg R' (pc cs') FULL' model') T) ->
  srealizes0 SEGS (cfg R (pc cs) FULL model) T.
Proof. exact (run_block_gc_sound_R (srealizes0 SEGS) srchain_srealizes0). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u_small : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. apply u64_lit. assumption. Qed.

#[using="Type"] Lemma nth_sr_vars_lt : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.Psr,(2?.$29.)Pr,$6:.P,(3.$20.(9=.R3.R2.)$22.)P,(;:.R2.#20.)(3.$20.(;4.R5.(;?.$29.R3.R4.(<0.=)))$22.)")
(* [comment removed for export] *).
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [AP.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

#[using="argH_agree SINV_agree"] Lemma node_fresh_sound_R : forall (SR : config -> TSet -> Prop) r logc base,   (* [comment removed for export] *)
  node1_stmt_R SR always (fun cs => node_fresh nx0 cs r logc base).
Proof.
  intros SR r logc base cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold node_fresh in Hn.
  set (b := match base with Some b => b | None => ELit 0 end) in Hn.
  set (e := esub (reg cs r) b) in Hn.
  destruct (Nat.ltb 0 r && Nat.ltb r 32 && Z.leb 0 logc && Z.leb logc 40 && Z.leb logc (ealign (kn cs) e)
            && AP.expr_vars_lt (nxt cs) b && AP.expr_vars_lt (nxt cs) e && fresh_ok nx0 cs)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc Hfresh]. apply andb_prop in Hc as [Hc Hve]. apply andb_prop in Hc as [Hc Hvb].
  apply andb_prop in Hc as [Hc Hal]. apply andb_prop in Hc as [Hc H40]. apply andb_prop in Hc as [Hc H0].
  apply andb_prop in Hc as [Hr0 Hr32].
  apply Nat.ltb_lt in Hr0. apply Nat.ltb_lt in Hr32. apply Z.leb_le in H0. apply Z.leb_le in H40. apply Z.leb_le in Hal.
  destruct (xlo2 (kn cs) e) as [lo|] eqn:Hlo; [|discriminate].
  destruct (xhi2 (kn cs) e) as [hi|] eqn:Hhi; [|discriminate].
  injection Hn as <-.
  set (c := 2 ^ logc) in *. set (v := nxt cs) in *.
  pose proof (co_know _ _ _ _ _ HC) as HK.
  pose proof (xlo2_sound E _ (kn cs) e lo HK Hlo) as Hlo'.
  pose proof (xhi2_sound E _ (kn cs) e hi HK Hhi) as Hhi'.
  destruct (ealign_sound SEGS E _ (kn cs) e HK) as [Hea Hdiv].
  assert (Hc : 0 < c) by (unfold c; apply Z.pow_pos_nonneg; lia).
  assert (Hc2 : c <= 2 ^ 40) by (unfold c; apply Z.pow_le_mono_r; lia).
  assert (Hcd : (c | bv_unsigned (edenot E e))%Z).
  { eapply Z.divide_trans; [|exact Hdiv]. unfold c. apply pow2_divide_le. lia. }
  destruct Hcd as [q Hq].
  pose proof (u64_range (edenot E e)) as Hue.
  assert (Hq0 : 0 <= q) by nia.
  assert (Hq64 : q < 2 ^ 64) by nia.
  set (a := Z_to_bv 64 q). set (E' := ext1 E v a).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  destruct (fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (cs_ok_agree E E' cs R FULL model Hag Hfresh HC) as HC'.
  assert (Hev : edenot E' e = edenot E e) by (symmetry; eapply (edenot_agree' v); [exact Hag | exact Hve]).
  assert (Hbv : edenot E' b = edenot E b) by (symmetry; eapply (edenot_agree' v); [exact Hag | exact Hvb]).
  assert (Hrv : edenot E' (reg cs r) = edenot E (reg cs r)).
  { symmetry. eapply (edenot_agree' v); [exact Hag|]. unfold reg. apply nth_sr_vars_lt; [exact Fsr | lia]. }
  assert (Hne : edenot E' (escale c (EVar v)) = edenot E e).
  { unfold escale. rewrite mkMd_denot. cbn [edenot]. unfold E'. rewrite ext1_at. unfold a.
    apply bv_eq. rewrite u_mul64. rewrite (u_small c) by lia. rewrite (u_small q) by lia. rewrite Z.mod_small by nia. lia. }
  assert (He_sem : edenot E e = alu64 ALU_SUB (edenot E (reg cs r)) (edenot E b)) by (unfold e, esub; apply mkAlu_denot).
  apply (Hk E' R FULL model); [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag] | | reflexivity].
  (* [comment removed for export] *)
  assert (HKf : know_ok SEGS E' (Mr E' cs model FULL)
            ((KRange (EVar v) ((lo + c - 1) / c) (hi / c) :: KRange (esub e (escale c (EVar v))) 0 0
               :: residue_fact (kn cs) e (escale c (EVar v)))
             ++ kn cs)).
  { apply Forall_app. split; [|exact (co_know _ _ _ _ _ HC')].
    constructor; [|constructor].
    - cbn [kentry_ok edenot]. unfold E' at 1 2. rewrite ext1_at. unfold a. rewrite u_small by lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      split; nia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - cbn [kentry_ok]. unfold esub. rewrite !mkAlu_denot, !Hne, !Hev.
      rewrite !u_sub64. rewrite Z.sub_diag, Z.mod_0_l by lia. lia.
    - eapply (residue_fact_sound E E' _ _ (kn cs) e); [exact HK | exact Hne |].
      intros e1 s1 Hd1. symmetry. eapply (edenot_agree' v); [exact Hag | exact (deand_vars v e e1 s1 Hd1 Hve)]. }
  destruct HC'; constructor; cbn [bump set_reg add_kn set_kn with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset]; try assumption.
  - apply regs_ok_respell; [exact co_regs0 | lia |].
    unfold eadd. rewrite mkAlu_denot, Hne, Hbv. fold (reg cs r). rewrite Hrv, He_sem.
    apply bv_eq. rewrite u_add64, u_sub64. pose proof (u64_range (edenot E (reg cs r))). pose proof (u64_range (edenot E b)).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite Zplus_mod_idemp_r. replace (bv_unsigned (edenot E b) + (bv_unsigned (edenot E (reg cs r)) - bv_unsigned (edenot E b))) with (bv_unsigned (edenot E (reg cs r))) by lia.
    rewrite Z.mod_small by lia. reflexivity.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - reflexivity.
Qed.

#[using="argH_agree SINV_agree"] Lemma node_fresh_sound_pf : fresh_stmt.
Proof. exact (node_fresh_sound_R (srealizes SEGS)). Qed.
#[using="argH_agree SINV_agree"] Lemma node_fresh_sound0 : forall r logc base, node1_stmt_R (srealizes0 SEGS) always (fun cs => node_fresh nx0 cs r logc base).
Proof. exact (node_fresh_sound_R (srealizes0 SEGS)). Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma listZ_eqb_eq : forall x y, listZ_eqb x y = true -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] H; cbn [listZ_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. rewrite (IH y H2), H1. reflexivity.
Qed.
#[using="Type"] Lemma spieces_eqb_eq : forall x y, spieces_eqb x y = true -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] H; cbn [spieces_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (IH y H2). f_equal.
  destruct a as [l|k], b as [l'|k']; cbn [spiece_eqb] in H1; try discriminate.
  - apply listZ_eqb_eq in H1. congruence.
  - apply Nat.eqb_eq in H1. congruence.
Qed.
#[using="Type"] Lemma shape_eqb_eq : forall x y, shape_eqb x y = true -> x = y.
Proof.
  induction x; intros y H; destruct y; cbn [shape_eqb] in H; try discriminate;
    repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end; try reflexivity.
  - apply Z.eqb_eq in H. congruence.
  - apply Z.eqb_eq in H. apply spieces_eqb_eq in X0. rewrite (IHx _ X). congruence.
  - rewrite (IHx1 _ H), (IHx2 _ X). reflexivity.
  - apply expr_eqb_eq in H. apply Z.eqb_eq in X1. rewrite (IHx1 _ X0), (IHx2 _ X). congruence.
  - apply Nat.eqb_eq in H. congruence.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shape_in_sound : forall D E fs b a, shape_in b a = true -> forall tr, sd D E fs b tr -> sd D E fs a tr.
Proof.
  intros D E fs b a. induction a as [|c|fd ps a IHa|a1 IH1 a2 IH2|e mid a1 IH1 a2 IH2|h|]; intros H tr Htr;
    cbn [shape_in] in H; apply orb_prop in H as [H|H];
    try (apply shape_eqb_eq in H; subst; exact Htr); try discriminate H.
  - cbn [sd]. unfold t_alt2. apply orb_prop in H as [H|H]; [left; exact (IH1 H tr Htr) | right; exact (IH2 H tr Htr)].
  - cbn [sd]. apply andb_prop in H as [H1 H2]. destruct (bv_unsigned (edenot E e) <=? mid)%Z; [exact (IH1 H1 tr Htr) | exact (IH2 H2 tr Htr)].
Qed.
#[using="HOLES_nil"] Lemma shape_le_sound : forall D E fs b a, D [] -> shape_le b a = true -> forall tr, sd D E fs b tr -> sd D E fs a tr.
Proof.
  intros D E fs b a HD. induction b as [|c|fd ps b IHb|b1 IH1 b2 IH2|e mid b1 IH1 b2 IH2|h|]; intros H tr Htr;
    cbn [shape_le] in H; apply orb_prop in H as [H|H];
    try (exact (shape_in_sound D E fs _ a H tr Htr)); try discriminate H.
  - cbn [sd] in Htr. unfold t_nil in Htr. subst tr. apply sd_has_nil. exact HD.
  - apply andb_prop in H as [H1 H2]. cbn [sd] in Htr. unfold t_alt2 in Htr. destruct Htr as [Htr|Htr]; [exact (IH1 H1 tr Htr) | exact (IH2 H2 tr Htr)].
  - apply andb_prop in H as [H1 H2]. cbn [sd] in Htr. destruct (bv_unsigned (edenot E e) <=? mid)%Z; [exact (IH1 H1 tr Htr) | exact (IH2 H2 tr Htr)].
Qed.

#[using="Type"] Lemma find_disj_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)Pb1,$29.Pb2,$29.Pc1,$29.Po1,$1.Pn1,$29.Pc2,$29.Po2,$1.Pn2,$29.P,(64.VSEGS,R;.R:.R9.)P,(3.(23.(11.(11.(11.(11.(11.$29.$1.)$29.)$29.)$1.)$29.))(=3.R:.R9.R8.)(82.(11.(11.(11.(11.(11.$29.$1.)$29.)$29.)$1.)$29.)(27.(11.(11.(11.(11.$29.$1.)$29.)$29.)$1.)$29.(27.(11.(11.(11.$29.$1.)$29.)$29.)$1.(27.(11.(11.$29.$1.)$29.)$29.(27.(11.$29.$1.)$29.(27.$29.$1.R7.R6.)R5.)R4.)R3.)R2.)))(1:.(2.(18.(70.R=.(71.R8.R7.))(72.R=.R6.))(70.R=.(71.R5.R4.)))(2.(18.(70.R=.(71.R5.R4.))(72.R=.R3.))(70.R=.(71.R8.R7.))))")
(* [comment removed for export] *).
Proof.
  intros E M k b1 b2 c1 o1 n1 c2 o2 n2 HK. induction k as [|K k IH]; intros H; [discriminate|].
  inversion HK as [|K' k' HKK HK']; subst.
  cbn [find_disj] in H.
  destruct K as [| | | | | | |[d1 p1] m1 [d2 p2] m2| |]; try exact (IH HK' H).
  cbv zeta in H.
  match type of H with (if ?c then _ else _) = _ => destruct c end.
  - injection H as <- <- <- <- <- <-. exact HKK.
  - match type of H with (if ?c then _ else _) = _ => destruct c end; [|exact (IH HK' H)].
    injection H as <- <- <- <- <- <-. cbn [kentry_ok] in HKK. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma disj_cands_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)Pb,$29.PcA,$29.PoA,$1.PnA,$29.PcB,$29.PoB,$1.PnB,$29.P,(64.VSEGS,R:.R9.R8.)P,(34.(11.(11.(11.(11.(11.$29.$1.)$29.)$29.)$1.)$29.)(27.(11.(11.(11.(11.$29.$1.)$29.)$29.)$1.)$29.(27.(11.(11.(11.$29.$1.)$29.)$29.)$1.(27.(11.(11.$29.$1.)$29.)$29.(27.(11.$29.$1.)$29.(27.$29.$1.R7.R6.)R5.)R4.)R3.)R2.)(=4.R9.R8.))(1:.(2.(18.(70.R<.(71.R8.R7.))(72.R<.R6.))(70.R<.(71.R5.R4.)))(2.(18.(70.R<.(71.R5.R4.))(72.R<.R3.))(70.R<.(71.R8.R7.))))")
(* [comment removed for export] *).
Proof.
  intros E M k b cA oA nA cB oB nB HK. induction k as [|K k IH]; intros H; [destruct H|].
  inversion HK as [|K' k' HKK HK']; subst.
  cbn [disj_cands] in H.
  destruct K as [| | | | | | |[d1 p1] m1 [d2 p2] m2| |]; try exact (IH HK' H).
  apply in_app_iff in H as [H|H]; [|exact (IH HK' H)].
  match type of H with In _ (if ?c then _ else _) => destruct c end.
  - destruct H as [H|[]]. injection H as <- <- <- <- <- <-. exact HKK.
  - match type of H with In _ (if ?c then _ else _) => destruct c end; [|destruct H].
    destruct H as [H|[]]. injection H as <- <- <- <- <- <-. cbn [kentry_ok] in HKK. lia.
Qed.

#[using="Type"] Lemma disj_side_fact_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)PcA,$29.PoA,$1.PnA,$29.PcB,$29.PoB,$1.PK,$68.P,(64.VSEGS,R9.R8.R7.)P,(3.(23.$68.)(=5.R8.R7.R6.R5.R4.R3.)(82.$68.R2.))P,(2.=(70.R;.(71.R8.R7.)))P,(1?.(70.R<.(71.R6.R5.))(91.+2.+40.))P,(2.(18.(70.R=.(71.R:.R9.))(72.R=.R8.))(70.R=.(71.R7.R6.)))(6=.VSEGS,R>.R=.R6.)")
(* [comment removed for export] *).
Proof.
  intros E M k cA oA nA cB oB K HK H HA HB Hle. unfold disj_side_fact in H.
  destruct (xlo2 k nA) as [n|] eqn:Hn; [|discriminate].
  destruct (base_range k cB) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  destruct (Z.leb 0 n && Z.leb n (bhi + oB))%bool eqn:Ht; [|discriminate]. injection H as <-.
  apply andb_prop in Ht as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1.
  pose proof (xlo2_sound E M k nA n HK Hn) as Ln. pose proof (base_range_sound SEGS E M k cB blo bhi HK Hbr) as [_ Bh].
  pose proof (u64_range (edenot E nA)) as RnA.
  cbn [kentry_ok]. unfold esub, eaddz. rewrite !mkAlu_denot, u_sub64, !u_add64. cbn [edenot]. rewrite !u_lit64.
  unfold estart, elenZ in *; cbn [a_base a_off] in *.
  pose proof (u64_range (edenot E cA)) as RA. pose proof (u64_range (edenot E cB)) as RB. unfold two64.
  set (uA := bv_unsigned (edenot E cA)) in *. set (uB := bv_unsigned (edenot E cB)) in *. set (uN := bv_unsigned (edenot E nA)) in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (E1 : (uB + oB mod 2 ^ 64) mod 2 ^ 64 = uB + oB).
  { rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia. }
  assert (E2 : (uA + oA mod 2 ^ 64) mod 2 ^ 64 = uA + oA).
  { rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia. }
  rewrite E1, E2. rewrite Z.mod_small by lia. lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma scaled_var_denot : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)Pe,$29.Pc,$1.Pv,$6:.Pvlo,$1.Pvhi,$1.P,(64.VSEGS,R8.R7.R6.)P,(3.(23.(11.$1.$6:.))(=6.R6.)(82.(11.$1.$6:.)(27.$1.$6:.R5.R4.)))P,(3.(23.(11.$1.$1.))(=7.R8.R6.R5.)(82.(11.$1.$1.)(27.$1.$1.R4.R3.)))(5.(3.$1.(15.&40.(52.R;.R8.))(=8.R7.(15.&40.(=9.R;.R6.))))(5.(1?.=R7.)(5.(2.=R5.)(5.(2.R5.(15.&40.(=9.R;.R6.)))(2.(15.&40.(=9.R;.R6.))R4.)))))")
(* [comment removed for export] *).
Proof.
  intros E M k e c v vlo vhi HK Hs Hr.
  unfold svar_range in Hr.
  destruct (xlo k (EVar v)) as [vlo'|] eqn:Hvl; [|discriminate]. destruct (xhi k (EVar v)) as [vhi'|] eqn:Hvh; [|discriminate].
  destruct (Z.ltb 0 c && Z.ltb (c * vhi') two64 && Z.leb 0 vlo')%bool eqn:Hc; [|discriminate]. injection Hr as <- <-.
  apply andb_prop in Hc as [Hc Hv0]. apply andb_prop in Hc as [Hc Hcv]. apply Z.ltb_lt in Hc. apply Z.ltb_lt in Hcv. apply Z.leb_le in Hv0.
  pose proof (xlo_sound SEGS E M k (EVar v) vlo' HK Hvl) as V1. pose proof (xhi_sound SEGS E M k (EVar v) vhi' HK Hvh) as V2. cbn [edenot] in V1, V2.
  destruct e as [| | | |[] [zc| | | | | | |] [|v'| | | | | |] | | |]; try discriminate Hs. cbn in Hs. injection Hs as -> ->.
  pose proof (u64_range (ev E v)) as Rv.
  split; [|split; [exact Hc | split; [exact Hv0 | split; [exact V1 | exact V2]]]].
  cbn [edenot]. rewrite u_mul64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mul_mod_idemp_l by lia. apply Z.mod_small. unfold two64 in *. nia.
Qed.

#[using="Type"] Lemma disj_var_fact_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)PcA,$29.PoA,$1.PnA,$29.PcB,$29.PoB,$1.P,(64.VSEGS,R8.R7.R6.)P,(2.=(70.R9.(71.R6.R5.)))P,(1?.(70.R:.(71.R4.R3.))(91.+2.+40.))P,(2.(18.(70.R;.(71.R8.R7.))(72.R;.R6.))(70.R;.(71.R5.R4.)))(1;.$68.(6=.VSEGS,R<.R;.)(=:.R:.R9.R8.R7.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros E M k cA oA nA cB oB HK HA HB Hle. unfold disj_var_fact.
  destruct (xlo2 k nA) as [nlo|] eqn:Hn; [|constructor].
  destruct (Z.leb 0 nlo) eqn:Hn0; [|constructor]. apply Z.leb_le in Hn0.
  pose proof (xlo2_sound E M k nA nlo HK Hn) as Ln.
  unfold estart, elenZ in *; cbn [a_base a_off] in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  destruct (scaled_var cA) as [[c v]|] eqn:HsA; [destruct (xhi k cB) as [bhi|] eqn:Hbh|].
  - destruct (svar_range k c v) as [[vlo vhi]|] eqn:Hr; [|constructor].
    destruct (scaled_var_denot E M k cA c v vlo vhi HK HsA Hr) as (UA & Hc & Hv0 & V1 & V2).
    pose proof (xhi_sound SEGS E M k cB bhi HK Hbh) as BH. rewrite UA in *.
    constructor; [|constructor]. cbn [kentry_ok edenot]. split; nia.
  - destruct (scaled_var cB) as [[c' v']|] eqn:HsB; [|constructor]. destruct (xlo k cA) as [alo|] eqn:Hal; [|constructor].
    destruct (svar_range k c' v') as [[vlo vhi]|] eqn:Hr; [|constructor].
    destruct (scaled_var_denot E M k cB c' v' vlo vhi HK HsB Hr) as (UB & Hc & Hv0 & V1 & V2).
    pose proof (xlo_sound SEGS E M k cA alo HK Hal) as AL. rewrite UB in *.
    constructor; [|constructor]. cbn [kentry_ok edenot]. unfold zcdiv'. split; nia.
  - destruct (scaled_var cB) as [[c' v']|] eqn:HsB; [|constructor]. destruct (xlo k cA) as [alo|] eqn:Hal; [|constructor].
    destruct (svar_range k c' v') as [[vlo vhi]|] eqn:Hr; [|constructor].
    destruct (scaled_var_denot E M k cB c' v' vlo vhi HK HsB Hr) as (UB & Hc & Hv0 & V1 & V2).
    pose proof (xlo_sound SEGS E M k cA alo HK Hal) as AL. rewrite UB in *.
    constructor; [|constructor]. cbn [kentry_ok edenot]. unfold zcdiv'. split; nia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

#[using="HS XN XE XB SHADOW_ok SP0_ok argH_high KC"] Lemma vis_add_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.Pb,$29.Pn,$29.Pk,(2?.$68.)Pcs2,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.P,(3.(23.$2>.)(=;.VA,VLIMIT,R8.R7.R6.R5.)(82.$2>.R4.))P,(57.R:.R9.R4.R3.R2.)P,(64.VSEGS,R;.(65.R;.R6.R3.R4.)R7.)(57.R<.R7.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros E cs b n k cs2 R FULL model Hv HC HKk.
  rewrite vis_add_eq in Hv. (* [comment removed for export] *) unfold vis_add_ref in Hv.
  destruct (split_lit b) as [bb bk] eqn:Hsplit.
  destruct (shadow_of A (kn cs) b n) as [[sb sk] sn] eqn:Hsh.
  destruct (xhi (kn cs) n) as [nhi|] eqn:Hnhi; [|discriminate].
  match type of Hv with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hv as <-.
  apply andb_prop in Hc as [Hc Hbudget]. apply andb_prop in Hc as [Hc Hband]. apply andb_prop in Hc as [Hc Hapart]. apply andb_prop in Hc as [Hc Hvn].
  apply andb_prop in Hc as [Hc Hvb]. apply andb_prop in Hc as [Hc Hflat]. apply andb_prop in Hc as [Halb Haln].
  apply Z.leb_le in Hbudget.
  pose proof (co_know _ _ _ _ _ HC) as HK.
  pose proof (xhi_sound SEGS E _ (kn cs) n nhi HK Hnhi) as Hnhi'.
  destruct (flat_x_sound E _ (kn cs) bb bk n HK Hflat) as (Fb1 & Fb2 & Fb3).
  pose proof (u_of_split E b bb bk Hsplit ltac:(lia)) as Ub.
  set (cs2 := ACS _ _ _ _ _ _ _ _ _ _ _ _).
  (* [comment removed for export] *)
  assert (SUB : forall a, hid E cs2 model a = true -> hid E cs model a = true).
  { intros a. apply hid_cons_sub. }
  (* [comment removed for export] *)
  assert (HA : allowA E cs2 = allow1 E (b, n) ++ allowA E cs) by reflexivity.
  assert (Hcost : A_bytes (allow1 E (b, n)) <= vis_cost nhi).
  { unfold allow1, vis_cost. cbn [A_bytes fst snd]. unfold sh_lo, sh_hi. cbn [fst snd].
    pose proof (u64_range (edenot E b)) as Rb. pose proof (u64_range (edenot E n)) as Rn. unfold uE in *.
    pose proof (pageup_pagedown_gap (bv_unsigned (edenot E b)) (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) ltac:(lia)) as G1.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    pose proof (pageup_pagedown_gap (shadow_off A + bv_unsigned (edenot E b) / 8)
                  (shadow_off A + (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) / 8) ltac:(lia)) as G2.
    assert (G3 : (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) / 8 - bv_unsigned (edenot E b) / 8 <= nhi / 8 + 1) by lia.
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  (* [comment removed for export] *)
  assert (HKsh : know_ok SEGS E (Mr E cs2 model FULL) (shadow_facts A (kn cs) (a_maps cs) b n)).
  { unfold shadow_facts. rewrite Hsh.
    (* [comment removed for export] *)
    assert (FIND : forall k' m, know_ok SEGS E (Mr E cs model FULL) k' ->
              find_containing k' (a_maps cs) [KRWLAZY] sb sk sn = Some m ->
              exists m k', In m (a_maps cs) /\ is_fog m = false /\ am_kind m = KRWLAZY
                           /\ know_ok SEGS E (Mr E cs model FULL) k' /\ xinside k' sb sk sn (am_base m) 0 (am_len m) = true).
    { intros k' m HK' Hf. exists m, k'.
      unfold find_containing in Hf. apply find_some in Hf as [Hmin Hmb]. apply andb_prop in Hmb as [Hkind Hins].
      apply andb_prop in Hkind as [Hnf Hkind]. apply negb_true_iff in Hnf.
      cbn [existsb] in Hkind. rewrite orb_false_r in Hkind. apply mkind_eqb_eq in Hkind. repeat split; assumption. }
    assert (CONT : match find_containing (kn cs) (a_maps cs) [KRWLAZY] sb sk sn with Some _ => true
                   | None => shadow_in_cls (kn cs) (a_maps cs) b sb sk sn end = true ->
              exists m k', In m (a_maps cs) /\ is_fog m = false /\ am_kind m = KRWLAZY
                           /\ know_ok SEGS E (Mr E cs model FULL) k' /\ xinside k' sb sk sn (am_base m) 0 (am_len m) = true).
    { destruct (find_containing (kn cs) (a_maps cs) [KRWLAZY] sb sk sn) as [m0|] eqn:Hf0; [intros _; exact (FIND _ _ HK Hf0)|].
      intros Hcls. unfold shadow_in_cls in Hcls. apply existsb_exists in Hcls as [[[[[[cA oA] nA] cB] oB] nB] [Hfd Hcls]].
      unfold cls_cand_ok in Hcls.
      destruct (flat_x (kn cs) cA oA nA && flat_x (kn cs) cB oB nB)%bool eqn:Hfl; [|discriminate].
      apply andb_prop in Hfl as [FA FB].
      pose proof (flat_x_sound E _ (kn cs) cA oA nA HK FA) as (FA1 & FA2 & FA3).
      pose proof (flat_x_sound E _ (kn cs) cB oB nB HK FB) as (FB1 & FB2 & FB3).
      destruct (find_containing (disj_var_fact (kn cs) cB oB nB cA oA ++ kn cs) (a_maps cs) [KRWLAZY] sb sk sn) as [mL|] eqn:HfL; [|discriminate].
      destruct (find_containing (disj_var_fact (kn cs) cA oA nA cB oB ++ kn cs) (a_maps cs) [KRWLAZY] sb sk sn) as [mH|] eqn:HfH; [|discriminate].
      destruct (disj_cands_sound E _ (kn cs) _ cA oA nA cB oB nB HK Hfd) as [Hd|Hd].
      - (* [comment removed for export] *)
        apply (FIND (disj_var_fact (kn cs) cA oA nA cB oB ++ kn cs) mH); [|exact HfH]. apply Forall_app. split; [|exact HK].
        eapply disj_var_fact_sound; [exact HK | lia | unfold elenZ in *; lia | exact Hd].
      - apply (FIND (disj_var_fact (kn cs) cB oB nB cA oA ++ kn cs) mL); [|exact HfL]. apply Forall_app. split; [|exact HK].
        eapply disj_var_fact_sound; [exact HK | lia | unfold elenZ in *; lia | exact Hd]. }
    match goal with |- know_ok _ _ _ (match ?f with Some _ => ?l | None => if ?c then _ else [] end) =>
      assert (GOAL : (exists m k', In m (a_maps cs) /\ is_fog m = false /\ am_kind m = KRWLAZY
                           /\ know_ok SEGS E (Mr E cs model FULL) k' /\ xinside k' sb sk sn (am_base m) 0 (am_len m) = true) ->
                     know_ok SEGS E (Mr E cs2 model FULL) l);
      [| destruct f as [m0|] eqn:Hf0; [exact (GOAL (CONT eq_refl)) | destruct c eqn:Hc0; [exact (GOAL (CONT eq_refl)) | constructor]]]
    end.
    intros (m & k' & Hmin & Hnf & Hkind & HK' & Hins).
    pose proof (xinside_sound SEGS E _ k' sb sk sn (am_base m) 0 (am_len m) HK' Hins) as [I1 I2].
    (* [comment removed for export] *)
    assert (Hmv : In (amap_den E m) (vm_maps (m_vmmaps model))) by (eapply maps_match_In; [exact (co_maps _ _ _ _ _ HC) | exact Hmin | exact Hnf]).
    pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ HC) _ Hmv) as (B1 & B2 & B3 & B4 & B5 & B6). cbn [amap_den fst snd] in B1, B2, B3, B4, B5, B6.
    unfold hull_apart in B4. atopb.   (* [comment removed for export] *)
    unfold estart in I1, I2. cbn [a_base a_off] in I1, I2. rewrite Z.add_0_r in I1, I2.
    pose proof (u64_range (edenot E (am_base m))) as Rmb.
    (* [comment removed for export] *)
    unfold shadow_of in Hsh.
    destruct (split_lit (eadd (mkSrl (kn cs) b 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss. injection Hsh as -> -> <-.
    assert (Usn : elenZ E (mkSrl (kn cs) n 3) = bv_unsigned (edenot E n) / 8).
    { unfold elenZ. rewrite (mkSrl_denot SEGS E _ (kn cs) n 3 (Z_to_bv 64 3) HK) by (rewrite u64_lit by lia; reflexivity).
      rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
    unfold elenZ in I2. pose proof (u64_range (edenot E (mkSrl (kn cs) n 3))) as Rsn.
    pose proof SHADOW_ok as SO. unfold shadow_ok in SO. pose proof (u64_range (edenot E b)) as Rb.
    set (S0 := estart E (SA sb sk)) in *.
    assert (ES0 : S0 = bv_unsigned (edenot E sb) + sk) by reflexivity.
    assert (HS0 : S0 = shadow_off A + bv_unsigned (edenot E b) / 8).
    { pose proof (split_lit_denot E _ sb sk Hss) as D. unfold eadd in D. rewrite mkAlu_denot in D. cbn [edenot] in D.
      apply (f_equal bv_unsigned) in D. rewrite u_add64 in D.
      rewrite (mkSrl_denot SEGS E _ (kn cs) b 3 (Z_to_bv 64 3) HK) in D by (rewrite u64_lit by lia; reflexivity).
      rewrite u_srl64 in D.
      unfold S0, estart in *. cbn [a_base a_off] in *.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      rewrite !u64_lit in D by (unfold CEIL in *; lia).
      change (2 ^ (3 mod 64)) with 8 in D.
      rewrite (Z.mod_small (bv_unsigned (edenot E b) / 8 + shadow_off A)) in D by (unfold CEIL, KHI in *; lia).
      lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    (* [comment removed for export] *)
    assert (BYTE : forall i, 0 <= i < elenZ E (mkSrl (kn cs) n 3) ->
              Mr E cs2 model FULL (Z_to_bv 64 (S0 + i)) = Some (Z_to_bv 8 0)).
    { intros i Hi. rewrite Usn in Hi.
      set (z := S0 + i).
      assert (Hz : 0 <= z < 2 ^ 64).
      { unfold z. rewrite ES0. pose proof Usn as U2. unfold elenZ in U2. clear - Hi I1 I2 B5 Rsn Rmb Rb U2 ATB.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
      assert (Zin : bv_unsigned (edenot E (am_base m)) <= z < bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m))
                    /\ z < ATOP /\ (z < img_lo A \/ img_hi A <= z) /\ S0 <= z < S0 + bv_unsigned (edenot E n) / 8).   (* [comment removed for export] *)
      { unfold z. rewrite ES0. pose proof Usn as U2. unfold elenZ in U2. clear - Hi I1 I2 B4 B5 Rsn Rmb Rb U2 ATB.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
      clearbody z. destruct Zin as (Z1 & Z2 & Z3 & Z4).
      set (a := Z_to_bv 64 z). assert (Ua : bv_unsigned a = z) by (unfold a; apply u64_lit; exact Hz).
      assert (Hm1 : in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true).
      { eapply in_ivs_maps_match; [exact (co_maps _ _ _ _ _ HC) | exact Hmin | exact Hnf |]. rewrite Ua. exact Z1. }
      destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ HC) m Hmin Hkind a ltac:(rewrite Ua; exact Z1)) as [Hna Hlz].
      assert (Hargh : argH E a = false).
      { destruct (argH E a) eqn:Ha; [|reflexivity]. pose proof (argH_high _ _ Ha). clear - H Z2 Ua ATB. lia. }
      assert (Hvis2 : hid E cs2 model a = false).
      { unfold hid. rewrite Hargh. cbn [orb]. apply negb_false_iff. unfold vis.
        rewrite Hm1, Hna, Hlz. cbn [negb andb].
        assert (Hsh2 : in_sh E cs2 (bv_unsigned a) = true).
        { unfold in_sh. cbn [cs2 a_vis existsb]. unfold sh_lo, sh_hi. cbn [fst snd]. unfold uE.
          rewrite Ua. apply orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt].
          - lia.
          - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
            Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
        unfold in_allow. rewrite Hsh2. rewrite !orb_true_r. reflexivity. }
      assert (Hhid1 : hid E cs model a = true).
      { unfold hid. rewrite Hargh. cbn [orb]. apply negb_true_iff. unfold vis.
        rewrite Hm1, Hna, Hlz. cbn [negb andb].
        assert (Hh : in_hull A (bv_unsigned a) = false).
        { unfold in_hull. rewrite Ua. apply andb_false_iff. destruct Z3 as [Z3|Z3]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
        assert (Hc : (ATOP <=? bv_unsigned a) = false) by (apply Z.leb_gt; rewrite Ua; lia).
        rewrite Hh, Hc. cbn [orb].
        (* [comment removed for export] *)
        assert (Hold : in_allow E cs (bv_unsigned a) = false).
        { unfold in_allow. apply orb_false_iff.
          assert (P : forall p, In p (a_vis cs) ->
                    ((uE E (fst p) <=? bv_unsigned a) && (bv_unsigned a <? uE E (fst p) + uE E (snd p)))%bool = false
                    /\ ((sh_lo E p <=? bv_unsigned a) && (bv_unsigned a <? sh_hi E p))%bool = false).
          { intros p Hp. pose proof (proj1 (forallb_forall _ _) Hapart p Hp) as Hpp. cbv beta in Hpp.
            destruct (split_lit (fst p)) as [pb pk] eqn:Hps.
            apply andb_prop in Hpp as [Hpp Hap2]. apply andb_prop in Hpp as [Hpf Hap1].
            destruct (flat_x_sound E _ (kn cs) pb pk (snd p) HK Hpf) as (Fp1 & Fp2 & Fp3).
            pose proof (u_of_split E (fst p) pb pk Hps ltac:(lia)) as Up.
            pose proof (ranges_apart_x_sound SEGS E _ (kn cs) _ _ _ _ _ _ HK Hap1) as A1.
            pose proof (ranges_apart_x_sound SEGS E _ (kn cs) _ _ _ _ _ _ HK Hap2) as A2.
            fold S0 in A2. unfold elenZ in A1, A2. rewrite Usn in A2 |- * || idtac.
            change (elenZ E (mkSrl (kn cs) n 3)) with (bv_unsigned (edenot E (mkSrl (kn cs) n 3))) in Hi |- * || idtac.
            unfold sh_lo, sh_hi, uE. rewrite Up, Ua. rewrite <- Ub in A1.
            Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
            pose proof Usn as U'. unfold elenZ in U'. rewrite ?U' in A2.
            split; apply andb_false_iff.
            - destruct A2 as [A2|A2]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
            - destruct A1 as [A1|A1]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
            Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
          unfold in_vis, in_sh. split; apply existsb_false_forall; intros p Hp; [exact (proj1 (P p Hp)) | exact (proj2 (P p Hp))]. }
        rewrite Hold. reflexivity. }
      assert (Hgh : in_ghost E cs (bv_unsigned a) = false).
      { (* [comment removed for export] *)
        apply in_ghost_false_band. unfold in_band. rewrite Ua.
        unfold band_okb in Hband.
        destruct (xlo (kn cs) sb) as [bl|] eqn:Hbl; [|discriminate]. destruct (xhi (kn cs) sb) as [bh|] eqn:Hbh; [|discriminate].
        destruct (xhi (kn cs) (mkSrl (kn cs) n 3)) as [snh|] eqn:Hsnh; [|discriminate].
        apply andb_prop in Hband as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
        pose proof (xlo_sound SEGS E _ (kn cs) sb bl HK Hbl) as XbL. pose proof (xhi_sound SEGS E _ (kn cs) sb bh HK Hbh) as XbH.
        pose proof (xhi_sound SEGS E _ (kn cs) _ snh HK Hsnh) as XnH.
        pose proof Usn as U'. unfold elenZ in U'. rewrite U' in XnH.
        apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
      unfold Mr, mrestrict. rewrite Hvis2.
      apply (co_zero _ _ _ _ _ HC a Hhid1 Hm1 Hna Hlz Hgh). }
    assert (Hfl : flat E (SA sb sk) (elenZ E (mkSrl (kn cs) n 3))).
    { unfold flat. fold S0. rewrite Usn. unfold CEIL in *.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    constructor; [|constructor; [|constructor]].
    - (* [comment removed for export] *) cbn [kentry_ok]. split; [exact Hfl|]. intros d w Hd Hdw.
      pose proof Hfl as (F1 & F2 & F3 & F4). fold S0 in F1, F2, F3, F4. fold S0.
      assert (ES1 : S0 = estart E (SA sb sk)) by reflexivity.
      destruct w as [|w']; [reflexivity|].
      apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
      intros x Hx. rewrite u64_lit in Hx by lia.
      unfold wview. replace x with (Z_to_bv 64 (S0 + (bv_unsigned x - S0))) by (apply bv_eq; rewrite u64_lit; pose proof (u64_range x); lia).
      rewrite (BYTE (bv_unsigned x - S0)) by lia. discriminate.
    - (* [comment removed for export] *) cbn [kentry_ok]. split; [exact Hfl|]. intros i Hi. fold S0. apply BYTE. exact Hi. }
  destruct HC. constructor; cbn [cs2 a_ss a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know];
    try assumption; try reflexivity.
  - (* [comment removed for export] *)
    apply Forall_app. split; [exact HKsh | exact HKk].
  - (* [comment removed for export] *) rewrite HA, A_bytes_app. lia.
  - (* [comment removed for export] *) rewrite HA. apply MInv_app; [exact co_minv0|]. rewrite A_bytes_app, co_limit0. lia.
  - (* [comment removed for export] *) intros a Ha. apply co_zero0. apply SUB. exact Ha.
Qed.

#[using="Type"] Lemma casedisj_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pcs,$2>.Pb1,$29.Pb2,$29.Pcsa,$2>.Pcsb,$2>.PE,$0.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.P,(57.R4.R9.R3.R2.R1.)P,(3.(23.(11.$2>.$2>.))(=<.R:.R9.R8.)(82.(11.$2>.$2>.)(27.$2>.$2>.R7.R6.)))(1:.(5.(57.R6.R8.R5.R4.R3.)(3.$1.(83.R8.)(83.R;.)))(5.(57.R6.R7.R5.R4.R3.)(3.$1.(83.R7.)(83.R;.))))")
(* [comment removed for export] *).
Proof.
  intros cs b1 b2 csa csb E R FULL model HC H. unfold node_casedisj in H.
  pose proof (co_know _ _ _ _ _ HC) as HK.
  destruct (find_disj (kn cs) b1 b2) as [[[[[[c1 o1] n1] c2] o2] n2]|] eqn:Hf; [|discriminate].
  destruct (flat_x (kn cs) c1 o1 n1) eqn:F1; [|discriminate].
  destruct (flat_x (kn cs) c2 o2 n2) eqn:F2; [|cbn in H; discriminate].
  destruct (disj_side_fact (kn cs) c1 o1 n1 c2 o2) as [K1|] eqn:D1; [|discriminate].
  destruct (disj_side_fact (kn cs) c2 o2 n2 c1 o1) as [K2|] eqn:D2; [|discriminate].
  injection H as <- <-.
  pose proof (flat_x_sound E _ (kn cs) c1 o1 n1 HK F1) as (A1 & A2 & A3).
  pose proof (flat_x_sound E _ (kn cs) c2 o2 n2 HK F2) as (B1 & B2 & B3).
  unfold elenZ in *.
  destruct (find_disj_sound E _ (kn cs) b1 b2 c1 o1 n1 c2 o2 n2 HK Hf) as [Hd|Hd].
  - left. split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. apply Forall_app. split; [|exact HK]. constructor.
    + eapply disj_side_fact_sound; [exact HK | exact D1 | lia | unfold elenZ in *; lia | exact Hd].
    + eapply disj_var_fact_sound; [exact HK | lia | unfold elenZ in *; lia | exact Hd].
  - right. split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. apply Forall_app. split; [|exact HK]. constructor.
    + eapply disj_side_fact_sound; [exact HK | exact D2 | lia | unfold elenZ in *; lia | exact Hd].
    + eapply disj_var_fact_sound; [exact HK | lia | unfold elenZ in *; lia | exact Hd].
Qed.

#[using="SHADOW_ok"] Lemma shadow_of_val : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)Pb,$29.Pn,$29.Psb,$29.Psk,$1.Psn,$29.P,(64.VSEGS,R8.R7.R6.)P,(3.(11.(11.$29.$1.)$29.)(==.VA,R7.R6.R5.)(27.(11.$29.$1.)$29.(27.$29.$1.R4.R3.)R2.))P,(3.$20.(90.R8.R5.R4.R3.)$22.)(5.(3.$1.(70.R;.(71.R6.R5.))(:.(18.(>.(15.&40.(52.R;.R8.))+8.)(=>.VA,))(91.+2.+40.)))(3.$1.(72.R;.R4.)(>.(15.&40.(52.R;.R7.))+8.)))")
(* [comment removed for export] *).
Proof.
  intros E M k b n sb sk sn HK Hs Hf. unfold shadow_of in Hs.
  destruct (split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hsp. injection Hs as E1 E2 E3. subst sb' sk'. rewrite <- E3 in *.
  pose proof (flat_x_sound E _ k sb sk (mkSrl k n 3) HK Hf) as (F1 & F2 & F3).
  pose proof (split_lit_denot E _ sb sk Hsp) as Hd.
  assert (S3 : forall x, bv_unsigned (edenot E (mkSrl k x 3)) = bv_unsigned (edenot E x) / 8).
  { intros x. rewrite (mkSrl_denot SEGS E _ k x 3 (Z_to_bv 64 3) HK) by reflexivity.
    rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
  split.
  - unfold eadd in Hd. rewrite mkAlu_denot in Hd. apply (f_equal bv_unsigned) in Hd.
    rewrite u_add64, S3 in Hd. cbn [edenot] in Hd. rewrite (u64_lit (shadow_off A)) in Hd by (pose proof SHADOW_ok as SO; unfold shadow_ok in SO; lia).
    rewrite Z_to_bv_unsigned in Hd. unfold bv_wrap, bv_modulus in Hd. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hd.
    unfold estart; cbn [a_base a_off].
    pose proof (u64_range (edenot E (mkSrl k n 3))). unfold elenZ, estart in *; cbn [a_base a_off] in *.
    unfold two64 in *. rewrite (Z.mod_small (bv_unsigned (edenot E sb) + sk)) in Hd by lia.
    rewrite <- Hd. reflexivity.
  - unfold elenZ. apply S3.
Qed.

#[using="SHADOW_ok"] Lemma shdisj_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pcs,$2>.Pb1,$29.Pn1,$29.Pb2,$29.Pn2,$29.Pcs',$2>.PE,$0.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.P,(57.R4.R:.R3.R2.R1.)P,(3.(23.$2>.)(=?.VA,R;.R:.R9.R8.R7.)(82.$2>.R6.))(5.(57.R6.R7.R5.R4.R3.)(3.$1.(83.R7.)(83.R<.)))")
(* [comment removed for export] *).
Proof.
  intros cs b1 n1 b2 n2 cs' E R FULL model HC H. rewrite node_shdisj_eq in H. (* [comment removed for export] *) unfold node_shdisj_ref in H.
  pose proof (co_know _ _ _ _ _ HC) as HK.
  destruct (split_lit b1) as [c1 o1] eqn:S1. destruct (split_lit b2) as [c2 o2] eqn:S2.
  destruct (shadow_of A (kn cs) b1 n1) as [[sb1 sk1] sn1] eqn:H1. destruct (shadow_of A (kn cs) b2 n2) as [[sb2 sk2] sn2] eqn:H2.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as <-.
  apply andb_prop in Hc as [Hc Hap]. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hc Fs2]. apply andb_prop in Hc as [Hc Fs1].
  apply andb_prop in Hc as [Hc F2]. apply andb_prop in Hc as [Hc F1].
  apply andb_prop in Hc as [Hc Ln2]. apply andb_prop in Hc as [Hc Lb2]. apply andb_prop in Hc as [Lb1 Ln1].
  apply Z.leb_le in Lb1. apply Z.leb_le in Ln1. apply Z.leb_le in Lb2. apply Z.leb_le in Ln2.
  split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
  destruct (xhi (kn cs) b1) as [h1|] eqn:Xh1; [|discriminate]. destruct (xhi (kn cs) n1) as [m1|] eqn:Xm1; [|discriminate].
  destruct (xhi (kn cs) b2) as [h2|] eqn:Xh2; [|discriminate]. destruct (xhi (kn cs) n2) as [m2|] eqn:Xm2; [|discriminate].
  apply andb_prop in Hhi as [Y1 Y2]. apply Z.leb_le in Y1. apply Z.leb_le in Y2.
  pose proof (xhi_sound SEGS E _ (kn cs) b1 h1 HK Xh1) as B1. pose proof (xhi_sound SEGS E _ (kn cs) n1 m1 HK Xm1) as M1.
  pose proof (xhi_sound SEGS E _ (kn cs) b2 h2 HK Xh2) as B2. pose proof (xhi_sound SEGS E _ (kn cs) n2 m2 HK Xm2) as M2.
  pose proof (flat_x_sound E _ (kn cs) c1 o1 n1 HK F1) as (A1 & A2 & A3).
  pose proof (flat_x_sound E _ (kn cs) c2 o2 n2 HK F2) as (C1 & C2 & C3).
  pose proof (u64_range (edenot E n1)) as Rn1. pose proof (u64_range (edenot E n2)) as Rn2.
  pose proof (u_of_split E b1 c1 o1 S1 ltac:(lia)) as U1. pose proof (u_of_split E b2 c2 o2 S2 ltac:(lia)) as U2.
  pose proof (ranges_apart_x_sound SEGS E _ (kn cs) c1 o1 n1 c2 o2 n2 HK Hap) as AP0.
  destruct (shadow_of_val E _ (kn cs) b1 n1 sb1 sk1 sn1 HK H1 Fs1) as [V1 L1].
  destruct (shadow_of_val E _ (kn cs) b2 n2 sb2 sk2 sn2 HK H2 Fs2) as [V2 L2].
  pose proof SHADOW_ok as SO; unfold shadow_ok in SO.
  cbn [kentry_ok]. rewrite V1, V2, L1, L2.
  destruct (ealign_sound SEGS E _ (kn cs) b1 HK) as [_ D1]. destruct (ealign_sound SEGS E _ (kn cs) n1 HK) as [_ D2].
  destruct (ealign_sound SEGS E _ (kn cs) b2 HK) as [_ D3]. destruct (ealign_sound SEGS E _ (kn cs) n2 HK) as [_ D4].
  assert (P8 : forall e, 3 <= ealign (kn cs) e -> (2 ^ ealign (kn cs) e | bv_unsigned (edenot E e)) -> (8 | bv_unsigned (edenot E e))).
  { intros e He Hd. eapply Z.divide_trans; [|exact Hd]. change 8 with (2 ^ 3). apply pow2_divide_le. lia. }
  pose proof (P8 _ Lb1 D1) as [q1 Q1]. pose proof (P8 _ Ln1 D2) as [q2 Q2]. pose proof (P8 _ Lb2 D3) as [q3 Q3]. pose proof (P8 _ Ln2 D4) as [q4 Q4].
  unfold elenZ in AP0. rewrite <- U1, <- U2 in AP0.
  pose proof (u64_range (edenot E b1)) as Rb1. pose proof (u64_range (edenot E b2)) as Rb2.
  generalize dependent AP0. rewrite Q1, Q2, Q3, Q4. rewrite Q1 in Rb1, B1. rewrite Q2 in Rn1, M1. rewrite Q3 in Rb2, B2. rewrite Q4 in Rn2, M2.
  rewrite !Z.div_mul by lia. intros AP0.
  rewrite (Z.mod_small (q1 + shadow_off A)) by lia. rewrite (Z.mod_small (q3 + shadow_off A)) by lia.
  clear - AP0 Rb1 Rb2 Rn1 Rn2 SO. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma expr_vars_lt_mono : forall b b' e, AP.expr_vars_lt b e = true -> (b <= b')%nat -> AP.expr_vars_lt b' e = true.
Proof.
  intros b b' e H Hle. induction e; cbn [AP.expr_vars_lt] in *; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity); try (apply IHe; exact H).
  apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.
#[using="Type"] Lemma sr_vars_lt_mono : forall b b' sr, AP.sr_vars_lt b sr = true -> (b <= b')%nat -> AP.sr_vars_lt b' sr = true.
Proof.
  intros b b' sr H Hle. induction sr; cbn [AP.sr_vars_lt] in *; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (expr_vars_lt_mono _ _ _ H1 Hle), (IHsr H2). reflexivity.
Qed.
#[using="Type"] Lemma sr_vars_lt_upd : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.Psr,(2?.$29.)Pn,$6:.Pe,$29.P,(3.$20.(9=.R4.R3.)$22.)P,(3.$20.(;4.R5.R2.)$22.)(3.$20.(9=.R6.(<1.R5.R4.R3.))$22.)")
(* [comment removed for export] *).
Proof.
  intros b sr n e. revert sr. induction n as [|n IH]; intros sr Hsr He.
  - destruct sr; cbn [sr_upd AP.sr_vars_lt]; cbn [AP.sr_vars_lt] in Hsr; rewrite He; [reflexivity|].
    apply andb_prop in Hsr as [_ H2]. rewrite H2. reflexivity.
  - destruct sr; cbn [sr_upd AP.sr_vars_lt]; cbn [AP.sr_vars_lt] in Hsr.
    + rewrite IH by (reflexivity || exact He). reflexivity.
    + apply andb_prop in Hsr as [H1 H2]. rewrite H1, (IH _ H2 He). reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint ext_list (E : env) (nx : nat) (vals : list word) : env :=
  match vals with
  | [] => E
  | v :: rest => ext_list (ext1 E nx v) (Datatypes.S nx) rest
  end.

#[using="Type"] Lemma ext_list_agree : forall E nx vals, env_agree nx E (ext_list E nx vals).
Proof.
  intros E nx vals. revert E nx. induction vals as [|v rest IH]; intros E nx; cbn [ext_list].
  - apply env_agree_refl.
  - eapply env_agree_trans; [apply ext1_agree|]. eapply env_agree_le; [apply IH | lia].
Qed.

#[using="Type"] Lemma ext_list_at : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pnx,$6:.Pvals,(2?.(12.&40.))Pi,$6:.P,(;:.R1.(>0.(12.&40.)R2.))(3.(12.&40.)(=9.(>1.R5.R4.R3.)(>2.R4.R2.))(;?.(12.&40.)R2.R3.(42.&40.=)))")
(* [comment removed for export] *).
Proof.
  intros E nx vals. revert E nx. induction vals as [|v rest IH]; intros E nx i Hi; cbn [length] in Hi; [lia|].
  cbn [ext_list]. destruct i as [|i].
  - rewrite Nat.add_0_r. pose proof (ext_list_agree (ext1 E nx v) (Datatypes.S nx) rest) as [Hag _].
    rewrite <- Hag by lia. cbn [nth]. apply ext1_at.
  - replace (nx + Datatypes.S i)%nat with (Datatypes.S nx + i)%nat by lia. cbn [nth]. apply IH. lia.
Qed.

#[using="Type"] Lemma regs_ok_sr_fresh : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Psr,(2?.$29.)PR,(55.&5.(12.&40.))Prs,(2?.$6:.)Pnx,$6:.P,(60.R5.R4.R3.)P,(3.$20.(9=.R2.R5.)$22.)P,(1;.$6:.Lr,$6:.(5.(;:.#0.R1.)(;:.R1.#20.))R4.)(60.(>1.R8.R4.(97.$6:.(12.&40.)Lr,$6:.(;;.R7.(42.&5.(86.R1.)))R5.))(>3.R7.R5.R4.)R6.)")
(* [comment removed for export] *).
Proof.
  intros E sr R rs. revert E sr. induction rs as [|r rest IH]; intros E sr nx HR Hsr Hrs; cbn [sr_fresh map ext_list].
  - exact HR.
  - apply Forall_cons_iff in Hrs as [Hr Hrest].
    apply IH.
    + apply regs_ok_respell.
      * eapply regs_ok_agree'; [apply ext1_agree | exact Hsr | exact HR].
      * exact Hr.
      * cbn [edenot]. rewrite ext1_at.
        pose proof (regs_ok_agree' nx E (ext1 E nx (getr R (Z_to_bv 5 (Z.of_nat r)))) sr R (ext1_agree _ _ _) Hsr HR) as HR'.
        etransitivity; [exact (HR' (Z_to_bv 5 (Z.of_nat r)))|]. unfold sr_get.
        assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat r)) 0%bv = false).
        { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
          change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
          replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
        rewrite Hnz, ridx_lit by lia. reflexivity.
    + apply sr_vars_lt_upd; [eapply sr_vars_lt_mono; [exact Hsr | lia] |]. cbn [AP.expr_vars_lt]. apply Nat.ltb_lt. lia.
    + exact Hrest.
Qed.

#[using="argH_agree SINV_agree"] Lemma havoc_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Prs,(2?.$6:.)Pcs',$2>.P,(57.R7.R6.R5.R4.R3.)P,(3.(23.$2>.)(>4.Vnx0,R7.R3.)(82.$2>.R2.))(4:.$0.LE',$0.(5.(5.(9;.Vnx0,R:.R1.)(9;.(:4.R9.)R:.R1.))(5.(57.R1.R4.R8.R7.R6.)(3.$1.(83.R4.)(83.R9.)))))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model rs cs' HC H. unfold node_havoc in H.
  destruct (fresh_ok nx0 cs && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool eqn:Hc; [|discriminate].
  injection H as <-. apply andb_prop in Hc as [Hf Hrs].
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := ext_list E (nxt cs) (map (fun r => getr R (Z_to_bv 5 (Z.of_nat r))) rs)).
  assert (Hag : env_agree (nxt cs) E E') by apply ext_list_agree.
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC'.
  destruct HC'; constructor; cbn [with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset]; try assumption; [|reflexivity].
  apply regs_ok_sr_fresh; [exact (co_regs _ _ _ _ _ HC) | exact Fsr |].
  apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hrs r Hr) as Hb.
  apply andb_prop in Hb as [H1 H2]. apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2. lia.
Qed.

(* [comment removed for export] *)
Fixpoint kn_bigexprs (K : nat) (k : list kentry) : list expr :=
  match k with
  | [] => []
  | KWord a w v :: r => if bigb K v then v :: kn_bigexprs K r else kn_bigexprs K r
  | _ :: r => kn_bigexprs K r
  end.

#[using="Type"] Lemma kentry_vars_lt_mono : forall b b' K, AP.kentry_vars_lt b K = true -> (b <= b')%nat -> AP.kentry_vars_lt b' K = true.
Proof.
  intros b b' K H Hle.
  assert (E1 : forall e, AP.expr_vars_lt b e = true -> AP.expr_vars_lt b' e = true) by (intros; eapply expr_vars_lt_mono; eassumption).
  assert (A1 : forall a, AP.saddr_vars_lt b a = true -> AP.saddr_vars_lt b' a = true) by (intros [? ?]; unfold AP.saddr_vars_lt; apply E1).
  destruct K; cbn [AP.kentry_vars_lt] in *;
    repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end;
    repeat match goal with
    | Y : AP.expr_vars_lt b ?e = true |- _ => rewrite (E1 e Y); clear Y
    | Y : AP.saddr_vars_lt b ?a = true |- _ => rewrite (A1 a Y); clear Y
    end; reflexivity.
Qed.
#[using="Type"] Lemma kn_vars_lt_mono' : forall b b' k, AP.kn_vars_lt b k = true -> (b <= b')%nat -> AP.kn_vars_lt b' k = true.
Proof.
  intros b b' k H Hle. induction k as [|K k IH]; [reflexivity|]. cbn [AP.kn_vars_lt] in *. apply andb_prop in H as [H1 H2].
  rewrite (kentry_vars_lt_mono b b' K H1 Hle), (IH H2). reflexivity.
Qed.

#[using="Type"] Lemma kn_bigsubst_len : forall K k nx, snd (kn_bigsubst K k nx) = length (kn_bigexprs K k).
Proof.
  intros K k. induction k as [|x r IH]; intros nx; [reflexivity|].
  cbn [kn_bigsubst kn_bigexprs]. destruct x as [a w v| | | | | | | | |]; try (specialize (IH nx); destruct (kn_bigsubst K r nx); cbn in *; exact IH).
  destruct (bigb K v).
  - specialize (IH (Datatypes.S nx)). destruct (kn_bigsubst K r (Datatypes.S nx)). cbn in *. rewrite IH. reflexivity.
  - specialize (IH nx). destruct (kn_bigsubst K r nx). cbn in *. exact IH.
Qed.

#[using="Type"] Lemma kn_bigsubst_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PK,$6:.Pk,(2?.$68.)Pnx,$6:.PE2,$0.PM,P,(12.&40.)(23.(12.&8.))P,(64.VSEGS,R2.R1.R4.)P,(3.$20.(9<.R4.R5.)$22.)P,Pi,$6:.P,(;:.R1.(>0.$29.(>5.R8.R7.)))(3.(12.&40.)(=9.R6.(>2.R7.R2.))(52.R6.(;?.$29.R2.(>5.R9.R8.)(<0.=))))(64.VSEGS,R5.R4.(16.(2?.$68.)$6:.(>6.R8.R7.R6.)))")
(* [comment removed for export] *).
Proof.
  intros K k. induction k as [|x r IH]; intros nx E2 M HK Hv Hvals; [constructor|].
  inversion HK as [|x' r' Hx Hr]; subst. cbn [AP.kn_vars_lt] in Hv. apply andb_prop in Hv as [Hvx Hvr].
  cbn [kn_bigsubst]. cbn [kn_bigexprs] in Hvals.
  assert (DFLT : (forall i, (i < length (kn_bigexprs K r))%nat -> ev E2 (nx + i) = edenot E2 (nth i (kn_bigexprs K r) (ELit 0))) ->
                 know_ok SEGS E2 M (fst (let '(r', c) := kn_bigsubst K r nx in (x :: r', c)))).
  { intros Hvals'. pose proof (IH nx E2 M Hr Hvr Hvals') as IH'. destruct (kn_bigsubst K r nx) as [r' c]. cbn [fst] in *. constructor; [exact Hx | apply IH']. }
  destruct x as [a w v| | | | | | | | |]; try (apply DFLT; exact Hvals).
  destruct (bigb K v) eqn:Hb; [|apply DFLT; exact Hvals]. clear DFLT.
  pose proof (IH (Datatypes.S nx) E2 M Hr ltac:(eapply kn_vars_lt_mono'; [exact Hvr | lia])) as IH'.
  destruct (kn_bigsubst K r (Datatypes.S nx)) as [r' c] eqn:Hs. cbn [fst]. constructor.
  - cbn [kentry_ok] in Hx |- *. destruct Hx as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    rewrite H3. f_equal. f_equal. cbn [edenot]. symmetry. replace nx with (nx + 0)%nat by lia. rewrite (Hvals 0%nat ltac:(cbn; lia)). reflexivity.
  - apply IH'. intros i Hi. replace (Datatypes.S nx + i)%nat with (nx + Datatypes.S i)%nat by lia. rewrite (Hvals (Datatypes.S i) ltac:(cbn; lia)). reflexivity.
Qed.

#[using="Type"] Lemma node_havoc_nxt : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pcs,$2>.Prs,(2?.$6:.)Pcs1,$2>.P,(3.(23.$2>.)(>4.Vnx0,R3.R2.)(82.$2>.R1.))(5.(3.$6:.(:4.R2.)(>2.(:4.R4.)(>0.$6:.R3.)))(3.$1.(83.R2.)(83.R4.)))")
(* [comment removed for export] *).
Proof.
  intros cs rs cs1 H. unfold node_havoc in H.
  destruct (fresh_ok nx0 cs && forallb (fun r : nat => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool; [|discriminate].
  injection H as <-. split; reflexivity.
Qed.

#[using="argH_agree SINV_agree"] Lemma havocbig_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.PK,$6:.Pcs',$2>.P,(57.R7.R6.R5.R4.R3.)P,(3.(23.$2>.)(>7.Vnx0,R7.R3.)(82.$2>.R2.))(4:.$0.LE',$0.(5.(5.(9;.Vnx0,R:.R1.)(9;.(:4.R9.)R:.R1.))(5.(57.R1.R4.R8.R7.R6.)(3.$1.(83.R4.)(83.R9.)))))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model K cs' HC H. unfold node_havocbig in H.
  destruct (node_havoc nx0 cs _) as [cs1|] eqn:Hh; [|discriminate].
  destruct (fresh_ok nx0 cs1) eqn:Hf1; [|discriminate].
  destruct (kn_bigsubst K (kn cs1) (nxt cs1)) as [k' c] eqn:Hs. injection H as <-.
  destruct (havoc_sound E cs R FULL model _ cs1 HC Hh) as (E1 & [Hag0 Hag1] & HC1 & Hpc1).
  destruct (fresh_ok_parts cs1 Hf1) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (vals := map (edenot E1) (kn_bigexprs K (kn cs1))).
  set (E2 := ext_list E1 (nxt cs1) vals).
  assert (Hag2 : env_agree (nxt cs1) E1 E2) by apply ext_list_agree.
  assert (Hnx : (nxt cs <= nxt cs1)%nat).
  { destruct (node_havoc_nxt cs _ cs1 Hh) as [-> _]. lia. }
  exists E2. split; [|split; [|rewrite <- Hpc1; reflexivity]].
  { split; (eapply env_agree_trans; [|eapply env_agree_le; [exact Hag2 | lia]]); assumption. }
  pose proof (cs_ok_agree E1 E2 cs1 R FULL model Hag2 Hf1 HC1) as HC2.
  replace (with_ss cs1 (mk_ss (pc cs1) (s_regs (a_ss cs1)) k' (nxt cs1 + c))) with (set_kn (bump cs1 c) k') by reflexivity.
  apply cs_ok_set_kn.
  - destruct HC2; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
      try assumption; reflexivity.
  - replace k' with (fst (kn_bigsubst K (kn cs1) (nxt cs1))) by (rewrite Hs; reflexivity).
    unfold Mr. change (hid E2 (bump cs1 c) model) with (hid E2 cs1 model).
    apply kn_bigsubst_sound; [exact (co_know _ _ _ _ _ HC2) | rewrite kn_vars_lt_eq; rewrite <- kn_vars_lt_eq; exact Fkn |].
    intros i Hi. unfold E2. rewrite ext_list_at by (unfold vals; rewrite length_map; exact Hi).
    unfold vals. change (Z_to_bv 64 0) with (edenot E1 (ELit 0)). rewrite map_nth.
    eapply (edenot_agree' (nxt cs1)); [apply ext_list_agree|].
    (* [comment removed for export] *)
    clear - Fkn Hi. revert i Hi. generalize (kn cs1) Fkn. intros k Hk.
    induction k as [|x r IH]; intros i Hi; [cbn in Hi; lia|].
    cbn [AP.kn_vars_lt] in Hk. apply andb_prop in Hk as [Hx Hr]. cbn [kn_bigexprs] in Hi |- *.
    destruct x as [a w v| | | | | | | | |]; try (apply IH; assumption).
    destruct (bigb K v); [|apply IH; assumption].
    destruct i as [|i]; cbn [nth]; [cbn [AP.kentry_vars_lt] in Hx; apply andb_prop in Hx as [_ Hx]; exact Hx | apply IH; [exact Hr | cbn [length] in Hi; lia]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition upd (E : env) (J : nat) (w : word) : env := Env (fun n => if Nat.eqb n J then w else ev E n) (eb E).

#[using="Type"] Lemma esubst_denot : forall E J e x, edenot E (esubst J e x) = edenot (upd E J (edenot E e)) x.
Proof.
  intros E J e x. induction x as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
    cbn [esubst edenot]; try reflexivity.
  - cbn [upd ev]. destruct (Nat.eqb n J); reflexivity.
  - rewrite mkAlu_denot, IHa, IHb. reflexivity.
  - rewrite mkAluw_denot, IHa, IHb. reflexivity.
  - rewrite mkMd_denot, IHa, IHb. reflexivity.
  - rewrite mkMdw_denot, IHa, IHb. reflexivity.
  - rewrite IHa. reflexivity.
Qed.

#[using="Type"] Lemma upd_agree : forall E J w, env_agree J E (upd E J w).
Proof. intros E J w. split; [|reflexivity]. intros n Hn. cbn [upd ev]. destruct (Nat.eqb_spec n J); [lia|reflexivity]. Qed.
#[using="Type"] Lemma upd_at : forall E J w, ev (upd E J w) J = w.
Proof. intros. cbn [upd ev]. rewrite Nat.eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma upd_same : forall E J, upd E J (ev E J) = E.
Proof. intros [f g] J. unfold upd. cbn [ev eb]. f_equal. apply functional_extensionality. intros n. destruct (Nat.eqb_spec n J); [subst; reflexivity|reflexivity]. Qed.
#[using="Type"] Lemma upd_upd : forall E J w w', upd (upd E J w) J w' = upd E J w'.
Proof. intros [f g] J w w'. unfold upd. cbn [ev eb]. f_equal. apply functional_extensionality. intros n. destruct (Nat.eqb n J); reflexivity. Qed.

#[using="Type"] Lemma estart_asubst : forall E J e a, estart E (asubst J e a) = estart (upd E J (edenot E e)) a.
Proof. intros E J e [b o]. unfold asubst, estart. cbn [a_base a_off]. rewrite esubst_denot. reflexivity. Qed.
#[using="Type"] Lemma adenot_asubst : forall E J e a, adenot E (asubst J e a) = adenot (upd E J (edenot E e)) a.
Proof. intros E J e [b o]. unfold asubst, adenot. cbn [a_base a_off]. rewrite esubst_denot. reflexivity. Qed.

#[using="Type"] Lemma kentry_ok_ksubst : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PJ,$6:.Pe,$29.PM,P,(12.&40.)(23.(12.&8.))PK,$68.(79.(6=.VSEGS,R5.R2.(>8.R4.R3.R1.))(6=.VSEGS,(>9.R5.R4.(52.R5.R3.))R2.R1.))")
(* [comment removed for export] *).
Proof.
  intros E J e M K. set (E' := upd E J (edenot E e)).
  destruct K as [a w v|a n|a n k|lo hi|x m|x lo hi|a n|a1 n1 a2 n2|a n c|a n]; cbn [ksubst kentry_ok];
    unfold flat, elenZ; rewrite ?estart_asubst, ?adenot_asubst, ?esubst_denot; fold E'; tauto.
Qed.

#[using="Type"] Lemma know_ok_ksubst : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PJ,$6:.Pe,$29.PM,P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)(79.(64.VSEGS,R5.R2.(97.$68.$68.(>8.R4.R3.)R1.))(64.VSEGS,(>9.R5.R4.(52.R5.R3.))R2.R1.))")
(* [comment removed for export] *).
Proof.
  intros E J e M k. unfold know_ok. induction k as [|K k IH]; [split; intros; constructor|].
  cbn [map]. split; intros H; inversion H; subst; constructor; try (apply IH; assumption);
    apply (kentry_ok_ksubst E J e M K); assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma inst_allowA : forall E J e inv, allowA E (inst inv J e) = allowA (upd E J (edenot E e)) inv.
Proof.
  intros E J e inv. unfold allowA, inst. cbn [a_vis a_ghost]. rewrite !flat_map_concat_map, !map_map.
  f_equal; f_equal; apply map_ext; intros [b n]; unfold allow1, allow_sh, psubst, sh_lo, sh_hi, uE; cbn [fst snd]; rewrite !esubst_denot; reflexivity.
Qed.

#[using="Type"] Lemma existsb_map' : forall {X Y} (f : Y -> bool) (g : X -> Y) l, existsb f (map g l) = existsb (fun x => f (g x)) l.
Proof. intros X Y f g l. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

#[using="Type"] Lemma inst_in_allow : forall E J e inv, in_allow E (inst inv J e) = in_allow (upd E J (edenot E e)) inv.
Proof.
  intros E J e inv. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh, inst. cbn [a_vis].
  rewrite !existsb_map'. f_equal; f_equal; apply functional_extensionality; intros [b n];
    unfold psubst, sh_lo, sh_hi, uE; cbn [fst snd]; rewrite !esubst_denot; reflexivity.
Qed.

#[using="Type"] Lemma inst_in_ghostl : forall E J e inv, in_ghostl E (inst inv J e) = in_ghostl (upd E J (edenot E e)) inv.
Proof.
  intros E J e inv. apply functional_extensionality. intros z. unfold in_ghostl, inst. cbn [a_ghost].
  induction (a_ghost inv) as [|[b n] l IH]; [reflexivity|]. cbn [map existsb fst snd psubst].
  unfold uE in *. cbn [fst snd]. rewrite !esubst_denot, IH. reflexivity.
Qed.
#[using="Type"] Lemma inst_in_ghost : forall E J e inv, in_ghost E (inst inv J e) = in_ghost (upd E J (edenot E e)) inv.
Proof. intros E J e inv. apply in_ghost_of_l. apply inst_in_ghostl. Qed.

#[using="argH_agree"] Lemma inst_hid : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PJ,$6:.Pe,$29.Pinv,$2>.Pmodel,$56.P,(<:.Vnx0,R4.)(3.Pa,(12.&40.)$20.(59.R6.(>:.R3.R5.R4.)R2.)(59.(>9.R6.R5.(52.R6.R4.))R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros E J e inv model HJ. apply functional_extensionality. intros a. unfold hid, vis.
  rewrite inst_in_allow. rewrite (argH_agree E (upd E J (edenot E e)) a); [|eapply env_agree_le; [apply upd_agree | exact HJ]].
  unfold inst. cbn [a_maps]. reflexivity.
Qed.

#[using="Type"] Lemma inst_maps : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PJ,$6:.Pe,$29.Pinv,$2>.(3.(2?.(11.(12.&40.)(12.&40.)))(97.$48.(11.(12.&40.)(12.&40.))(96.R4.)(8;.(>:.R1.R3.R2.)))(97.$48.(11.(12.&40.)(12.&40.))(96.(>9.R4.R3.(52.R4.R2.)))(8;.R1.)))")
(* [comment removed for export] *).
Proof.
  intros. unfold inst. cbn [a_maps]. rewrite map_map. apply map_ext. intros m. unfold amap_den, msubst. cbn [am_base am_len].
  rewrite !esubst_denot. reflexivity.
Qed.

#[using="Type"] Lemma maps_match_msubst : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PJ,$6:.Pe,$29.Pms,(2?.$48.)Pl,(2?.(11.(12.&40.)(12.&40.)))(79.(93.R5.(97.$48.$48.(>;.R4.R3.)R2.)R1.)(93.(>9.R5.R4.(52.R5.R3.))R2.R1.))")
(* [comment removed for export] *).
Proof.
  intros E J e ms. induction ms as [|m ms IH]; intros l; cbn [maps_match map]; [tauto|].
  unfold is_fog, msubst, uE, amap_den. cbn [am_kind am_base am_len]. rewrite !esubst_denot.
  destruct (is_tok_kind (am_kind m)).
  - split; (intros [HM|(iv & l' & -> & Hsz & HM)]; [left; apply IH; exact HM | right; exists iv, l'; split; [reflexivity|]; split; [exact Hsz | apply IH; exact HM]]).
  - split; (intros (l' & -> & HM); exists l'; split; [reflexivity | apply IH; exact HM]).
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma holes_msubst : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PJ,$6:.Pe,$29.Py,$1.Pl,(2?.(11.(12.&40.)(12.&40.)))Pms,(2?.$48.)(79.(1;.$48.(49.R6.R3.R2.)(97.$48.$48.(>;.R5.R4.)R1.))(1;.$48.(49.(>9.R6.R5.(52.R6.R4.))R3.R2.)R1.))")
(* [comment removed for export] *).
Proof.
  intros E J e y l ms. induction ms as [|m ms IH]; cbn [map].
  - split; intros; constructor.
  - rewrite !Forall_cons_iff, IH.
    assert (X : hole_ok E y l (msubst J e m) <-> hole_ok (upd E J (edenot E e)) y l m).
    { unfold hole_ok, is_hole, msubst, uE. cbn [am_kind am_base am_len]. rewrite !esubst_denot. tauto. }
    rewrite X. tauto.
Qed.
#[using="Type"] Lemma inst_maps_match : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PJ,$6:.Pe,$29.Pinv,$2>.Pl,(2?.(11.(12.&40.)(12.&40.)))(79.(93.R5.(8;.(>:.R2.R4.R3.))R1.)(93.(>9.R5.R4.(52.R5.R3.))(8;.R2.)R1.))")
(* [comment removed for export] *).
Proof. intros. unfold inst. cbn [a_maps]. apply maps_match_msubst. Qed.

#[using="Type"] Lemma regs_ok_inst : forall E J e sr R,
  regs_ok E (map (esubst J e) sr) R <-> regs_ok (upd E J (edenot E e)) sr R.
Proof.
  intros E J e sr R. unfold regs_ok, sr_get.
  assert (G : forall r, edenot E (if bv_eqb r 0 then ELit 0 else nth (ridx r) (map (esubst J e) sr) (ELit 0))
                     = edenot (upd E J (edenot E e)) (if bv_eqb r 0 then ELit 0 else nth (ridx r) sr (ELit 0))).
  { intros r. destruct (bv_eqb r 0); [reflexivity|].
    replace (ELit 0) with (esubst J e (ELit 0)) at 1 by reflexivity. rewrite map_nth. apply esubst_denot. }
  split; intros H r; [rewrite <- G | rewrite G]; apply H.
Qed.

#[using="Type"] Lemma fds_ok_inst : forall E J e f model, fds_ok E (fsubst J e f) model <-> fds_ok (upd E J (edenot E e)) f model.
Proof.
  intros E J e f model. destruct f as [|k l o|]; cbn [fsubst fds_ok]; try tauto.
  unfold uE. rewrite !esubst_denot. cbn [eb upd]. tauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma is_fog_msubst : forall J e m, is_fog (msubst J e m) = is_fog m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma born_msubst : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PJ,$6:.Pe,$29.Pms,(2?.$48.)Pks,(2?.$4?.)Piv,(11.(12.&40.)(12.&40.))(79.(4=.R6.(97.$48.$48.(>;.R5.R4.)R3.)R2.R1.)(4=.(>9.R6.R5.(52.R6.R4.))R3.R2.R1.))")
(* [comment removed for export] *).
Proof.
  intros E J e ms ks iv. split.
  - intros (m' & Hin & Hf & Hk & Hd). apply in_map_iff in Hin as (m & <- & Hin).
    exists m. split; [exact Hin|]. split; [exact Hf|]. split; [exact Hk|].
    unfold amap_den, msubst in Hd |- *. cbn [am_base am_len am_kind] in Hd. rewrite !esubst_denot in Hd. exact Hd.
  - intros (m & Hin & Hf & Hk & Hd). exists (msubst J e m). split; [apply in_map; exact Hin|]. split; [exact Hf|]. split; [exact Hk|].
    unfold amap_den, msubst in Hd |- *. cbn [am_base am_len am_kind]. rewrite !esubst_denot. exact Hd.
Qed.
#[using="Type"] Lemma nlz_ok_msubst : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PJ,$6:.Pe,$29.Pms,(2?.$48.)Pks,(2?.$4?.)PM,(2?.(11.(12.&40.)(12.&40.)))PX,(2?.(11.(12.&40.)(12.&40.)))(79.(<=.R7.(97.$48.$48.(>;.R6.R5.)R4.)R3.R2.R1.)(<=.(>9.R7.R6.(52.R7.R5.))R4.R3.R2.R1.))")
(* [comment removed for export] *).
Proof.
  intros E J e ms ks M X. split; intros H x Hx; destruct (H x Hx) as (P & iv & Hiv & B1 & B2 & NB); split; try exact P;
    exists iv; (split; [exact Hiv|]); (split; [exact B1|]); (split; [exact B2|]); intros Hb; apply NB;
    [apply (proj2 (born_msubst E J e ms ks iv)) | apply (proj1 (born_msubst E J e ms ks iv))]; exact Hb.
Qed.
#[using="Type"] Lemma sub_ok_psubst : forall E J e M N Lz t,
  sub_ok E M N Lz (psubst J e t) <-> sub_ok (upd E J (edenot E e)) M N Lz t.
Proof.
  intros E J e M N Lz t. unfold sub_ok, psubst, uE. cbn [fst snd]. rewrite !esubst_denot. tauto.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma def_Forall_msubst : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PJ,$6:.Pe,$29.PF,P,(12.&40.)(23.(12.&8.))Pms,(2?.$48.)(79.(1;.$48.(<?.R5.R2.)(97.$48.$48.(>;.R4.R3.)R1.))(1;.$48.(<?.(>9.R5.R4.(52.R5.R3.))R2.)R1.))")
(* [comment removed for export] *).
Proof.
  intros E J e F ms. rewrite Forall_map. split; intros H; apply Forall_forall; intros m Hm; unfold def_ok; intros Hf Hk a Ha;
    pose proof (proj1 (Forall_forall _ _) H m Hm) as X; unfold def_ok, msubst, is_fog in X, Hf, Hk, Ha |- *; cbn [am_base am_len am_kind] in X, Hf, Hk, Ha |- *;
    rewrite ?esubst_denot in X; rewrite ?esubst_denot in Ha; exact (X Hf Hk a Ha).
Qed.
#[using="Type"] Lemma sub_Forall_psubst : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PJ,$6:.Pe,$29.PM,(2?.(11.(12.&40.)(12.&40.)))PN,(2?.(11.(12.&40.)(12.&40.)))PLz,(2?.(11.(12.&40.)(12.&40.)))Pl,(2?.(11.$29.$29.))(79.(1;.(11.$29.$29.)(<>.R7.R4.R3.R2.)(97.(11.$29.$29.)(11.$29.$29.)(><.R6.R5.)R1.))(1;.(11.$29.$29.)(<>.(>9.R7.R6.(52.R7.R5.))R4.R3.R2.)R1.))")
(* [comment removed for export] *).
Proof.
  intros E J e M N Lz l. rewrite Forall_map. split; intros H; apply Forall_forall; intros t Ht;
    pose proof (proj1 (Forall_forall _ _) H t Ht) as X; [apply (proj1 (sub_ok_psubst E J e M N Lz t)) | apply (proj2 (sub_ok_psubst E J e M N Lz t))]; exact X.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma cov_Forall_msubst : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PJ,$6:.Pe,$29.PN,(2?.(11.(12.&40.)(12.&40.)))Psub,(2?.(11.$29.$29.))Pms,(2?.$48.)(79.(1;.$48.(=0.R6.R3.(97.(11.$29.$29.)(11.$29.$29.)(><.R5.R4.)R2.))(97.$48.$48.(>;.R5.R4.)R1.))(1;.$48.(=0.(>9.R6.R5.(52.R6.R4.))R3.R2.)R1.))")
(* [comment removed for export] *).
Proof.
  intros E J e N sub ms. rewrite Forall_map. split; intros H; apply Forall_forall; intros m Hm Hk z Hz;
    pose proof (proj1 (Forall_forall _ _) H m Hm) as X; unfold cov_ok, msubst, uE in X, Hk, Hz |- *; cbn [am_base am_len am_kind] in X, Hk, Hz |- *;
    rewrite ?esubst_denot in X; rewrite ?esubst_denot in Hz; (destruct (X Hk z Hz) as [Hn|(t & Ht & Hzt)]; [left; exact Hn | right]).
  - apply in_map_iff in Ht as (t0 & <- & Ht0). exists t0. split; [exact Ht0|]. unfold in_tok, psubst, uE in Hzt |- *. cbn [fst snd] in Hzt. rewrite !esubst_denot in Hzt. exact Hzt.
  - exists (psubst J e t). split; [apply in_map; exact Ht|]. unfold in_tok, psubst, uE in Hzt |- *. cbn [fst snd]. rewrite !esubst_denot. exact Hzt.
Qed.

#[using="argH_agree SINV_agree"] Lemma cs_ok_inst : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PJ,$6:.Pe,$29.Pinv,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.P,(<:.Vnx0,R6.)P,(3.(2?.$62.)(63.(<4.R5.))(2=.$62.))(79.(57.R9.(>:.R6.R8.R7.)R5.R4.R3.)(57.(>9.R9.R8.(52.R9.R7.))R6.R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros E J e inv R FULL model HJ Hlog.
  pose proof (inst_hid E J e inv model HJ) as HH. pose proof (inst_allowA E J e inv) as HA. pose proof (inst_maps E J e inv) as HM.
  pose proof (inst_in_ghost E J e inv) as HG.
  assert (AG : env_agree nx0 E (upd E J (edenot E e))) by (eapply env_agree_le; [apply upd_agree | exact HJ]).
  split; intros HC; destruct HC; constructor;
    cbn [inst a_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_sub mk_ss] in *;
    rewrite <- ?HA, <- ?HM; try assumption;
    (* [comment removed for export] *)
    try (apply (proj1 (nlz_ok_msubst E J e _ _ _ _)); assumption); try (apply (proj2 (nlz_ok_msubst E J e _ _ _ _)); assumption);
    try (apply (proj1 (sub_Forall_psubst E J e _ _ _ _)); assumption); try (apply (proj2 (sub_Forall_psubst E J e _ _ _ _)); assumption);
    try (apply (proj1 (def_Forall_msubst E J e _ _)); assumption); try (apply (proj2 (def_Forall_msubst E J e _ _)); assumption);   (* [comment removed for export] *)
    try (apply (proj1 (cov_Forall_msubst E J e _ _ _)); assumption); try (apply (proj2 (cov_Forall_msubst E J e _ _ _)); assumption).   (* [comment removed for export] *)
  - apply regs_ok_inst. assumption.
  - unfold Mr. rewrite <- HH. apply know_ok_ksubst. exact co_know0.
  - apply fds_ok_inst. assumption.
  - apply (proj1 (maps_match_msubst E J e _ _)). assumption.
  - apply (proj1 (holes_msubst E J e _ _ _)). assumption.
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk.
    pose proof (proj1 (Forall_forall _ _) co_none0 (msubst J e m) ltac:(apply in_map; exact Hin) Hk) as X.
    unfold amap_den, msubst in X |- *. cbn [am_base am_len am_kind] in X. rewrite !esubst_denot in X. exact X.
  - apply Forall_forall. intros m Hin Hk a Ha.
    pose proof (proj1 (Forall_forall _ _) co_kinds0 (msubst J e m) ltac:(apply in_map; exact Hin) Hk a) as X.
    unfold msubst in X. cbn [am_base am_len] in X. rewrite !esubst_denot in X. exact (X Ha).
  - rewrite <- esubst_denot. assumption.
  - intros a. unfold Mr in *. rewrite <- HH. first [rewrite HG | rewrite <- HG]. exact (co_zero0 a).
  - eapply SINV_agree; [exact AG | assumption].
  - apply regs_ok_inst. assumption.
  - reflexivity.
  - unfold Mr in *. rewrite HH. apply know_ok_ksubst. assumption.
  - apply fds_ok_inst. assumption.
  - apply (proj2 (maps_match_msubst E J e _ _)). assumption.
  - apply (proj2 (holes_msubst E J e _ _ _)). assumption.
  - apply Forall_forall. intros m' Hin Hk. apply in_map_iff in Hin as [m [<- Hin]].
    pose proof (proj1 (Forall_forall _ _) co_none0 m Hin Hk) as X.
    unfold amap_den, msubst. cbn [am_base am_len am_kind]. rewrite !esubst_denot. exact X.
  - apply Forall_forall. intros m' Hin Hk a Ha. apply in_map_iff in Hin as [m [<- Hin]].
    unfold msubst in Ha, Hk. cbn [am_base am_len am_kind] in Ha, Hk. rewrite !esubst_denot in Ha.
    exact (proj1 (Forall_forall _ _) co_kinds0 m Hin Hk a Ha).
  - rewrite esubst_denot. assumption.
  - rewrite HA. assumption.
  - rewrite HA. assumption.
  - intros a. unfold Mr in *. rewrite HH. first [rewrite <- HG | rewrite HG]. exact (co_zero0 a).
  - eapply SINV_agree; [|eassumption]. destruct AG as [AG1 AG2]. split; [intros n Hn; symmetry; apply AG1; exact Hn | symmetry; exact AG2].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma kentry_eqb_h_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)PX,$68.PK,$68.P,(64.VSEGS,R5.R4.R3.)P,(6=.VSEGS,R6.R5.R3.)P,(3.$20.(>=.R4.R3.)$22.)P,(3.$20.(>>.R6.R4.)$22.)(6=.VSEGS,R9.R8.R5.)")
(* [comment removed for export] *).
Proof.
  intros E M k X K HK HX Heq Hfl. unfold kentry_eqb_h in Heq. apply orb_prop in Heq as [Heq|Heq].
  { apply kentry_eqb_eq in Heq. subst. exact HX. }
  assert (SAD : forall b o b' o' n ne, saddr_eqb_h (SA b o) (SA b' o') = true -> flat E (SA b o) n ->
            flat_x k b' o' ne = true -> estart E (SA b' o') = estart E (SA b o)).
  { intros b o b' o' n ne Hs Hf Hf'. unfold saddr_eqb_h in Hs. cbn [a_base a_off] in *.
    apply orb_prop in Hs as [Hs|Hs]; [apply saddr_eqb_eq in Hs; injection Hs as -> ->; reflexivity|].
    apply expr_eqb_eq in Hs. apply (f_equal (fun x => bv_unsigned (edenot E x))) in Hs.
    unfold eaddz in Hs. rewrite !mkAlu_denot, !u_add64 in Hs. cbn [edenot] in Hs. rewrite !u_lit64 in Hs.
    pose proof (flat_x_sound E M k b' o' ne HK Hf') as (F1 & F2 & F3). pose proof (u64_range (edenot E ne)).
    unfold flat, estart in *; cbn [a_base a_off] in *.
    pose proof (u64_range (edenot E b)). pose proof (u64_range (edenot E b')). unfold two64 in Hs.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (E1 : (bv_unsigned (edenot E b) + o mod 2 ^ 64) mod 2 ^ 64 = bv_unsigned (edenot E b) + o) by (rewrite Zplus_mod_idemp_r; apply Z.mod_small; lia).
    assert (E2 : (bv_unsigned (edenot E b') + o' mod 2 ^ 64) mod 2 ^ 64 = bv_unsigned (edenot E b') + o') by (rewrite Zplus_mod_idemp_r; apply Z.mod_small; lia).
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  assert (AD : forall a a', estart E a' = estart E a -> adenot E a' = adenot E a).
  { intros [b o] [b' o'] He. unfold adenot, estart, v_addi in *. cbn [a_base a_off] in *. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite He. reflexivity. }
  destruct X as [[b o] w v|[b o] n|[b o] n kk| | | |[b o] n| |[b o] n c|[b o] n];
    destruct K as [[b' o'] w' v'|[b' o'] n'|[b' o'] n' kk'| | | |[b' o'] n'| |[b' o'] n' c'|[b' o'] n']; try discriminate;
    repeat match type of Heq with (_ && _)%bool = true => apply andb_prop in Heq as [Heq ?X] end;
    cbn [kentry_ok kflat_h] in *.
  - apply Nat.eqb_eq in X0. apply expr_eqb_eq in X. subst w' v'. destruct HX as (H1 & H2 & H3).
    pose proof (SAD b o b' o' _ _ Heq H2 Hfl) as ES.
    split; [exact H1|]. split; [unfold flat in *; rewrite ES; exact H2|]. rewrite (AD _ _ ES). exact H3.
  - apply expr_eqb_eq in X. subst n'. destruct HX as [H1 H2].
    pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. exact H2.
  - apply Nat.eqb_eq in X. apply expr_eqb_eq in X0. subst n' kk'. destruct HX as (H1 & H2 & H3).
    pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. split; [exact H2 | exact H3].
  - apply expr_eqb_eq in X. subst n'. destruct HX as [H1 H2].
    pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. exact H2.
  - apply Z.eqb_eq in X. apply expr_eqb_eq in X0. subst n' c'. destruct HX as [H1 H2].
    pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. exact H2.
  - apply expr_eqb_eq in X. subst n'. destruct HX as [H1 H2].
    pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. exact H2.
Qed.

(* [comment removed for export] *)
#[using="SEGS_in_hull"] Lemma seg_rom_off_hull : forall a : word, in_hull A (bv_unsigned a) = false -> seg_rom SEGS a = None.
Proof.
  intros a Ha. unfold seg_rom.
  rewrite (memory_read1_hidden SEGS (fun x => negb (in_hull A (bv_unsigned x)))); [reflexivity| |].
  - intros x Hx. apply SEGS_in_hull. apply negb_true_iff in Hx. exact Hx.
  - rewrite Ha. reflexivity.
Qed.

#[using="SEGS_in_hull"] Lemma rdn_bytes_some : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PM,P,(12.&40.)(23.(12.&8.))Pa,(12.&40.)Pw,$6:.Pbs,(2?.(12.&8.))P,(3.(23.(2?.(12.&8.)))(85.VSEGS,R4.R3.R2.)(82.(2?.(12.&8.))R1.))Px,(12.&40.)P,(5.(2.(15.&40.R5.)(15.&40.R1.))(1?.(15.&40.R1.)(18.(15.&40.R5.)(86.R4.))))P,(3.$20.(38.VA,(15.&40.R2.))$33.)(24.(3.(23.(12.&8.))A1.R8.R3.(25.(12.&8.))))")
(* [comment removed for export] *).
Proof.
  intros M a w. revert a. induction w as [|w IH]; intros a bs Hr x Hx Hh; [lia|].
  cbn [rdn] in Hr.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  - assert (x = a) by (apply bv_eq; exact Heq). subst x.
    destruct (M a) eqn:HMa; [congruence|]. rewrite (seg_rom_off_hull a Hh) in Hr. discriminate.
  - destruct (match M a with Some b => Some b | None => seg_rom SEGS a end) as [b|]; [|discriminate].
    destruct (rdn SEGS M (a + 1)%bv w) as [rest|] eqn:Hr2; [|discriminate].
    pose proof (u64_range x).
    assert (Hu1 : bv_unsigned (a + 1)%bv = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    eapply (IH (a + 1)%bv rest Hr2); [rewrite Hu1; lia | exact Hh].
Qed.

#[using="SEGS_in_hull"] Lemma cover1_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)Pb,$29.Pi,$1.Pe,$1.P,(64.VSEGS,R6.R5.R4.)P,(3.(23.$1.)(>?.R5.R4.R3.)(82.$1.R2.))(5.(1?.R4.R3.)Pj,$1.P,(5.(2.R5.R1.)(1?.R1.R4.))P,(3.$20.(38.VA,(18.(6.R:.R7.)R2.))$33.)(5.(5.(2.=(18.(6.R;.R8.)R3.))(1?.(18.(6.R;.R8.)R3.)(91.+2.+40.)))(24.(3.(23.(12.&8.))A1.R:.(42.&40.(18.(6.R;.R8.)R3.))(25.(12.&8.))))))")
(* [comment removed for export] *).
Proof.
  intros E M k b i e HK. induction k as [|K r IH]; intros H; [discriminate|].
  inversion HK as [|K' r' HKK Hr]; subst. cbn [cover1] in H.
  match type of H with (match ?h with Some e0 => Some e0 | None => _ end = _) => destruct h as [e1|] eqn:Hhit end;
    [injection H as <- | exact (IH Hr H)].
  clear IH Hr HK.
  assert (ZF : forall kb kk l (P : option byte -> Prop),
            (flat E (SA kb kk) (elenZ E (ELit l)) /\ forall i0, (0 <= i0 < elenZ E (ELit l))%Z -> P (M (Z_to_bv 64 (estart E (SA kb kk) + i0)))) ->
            (forall x, P x -> x <> None) ->
            (if (expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool then Some (kk + l)%Z else None) = Some e1 ->
            (i < e1)%Z /\ forall j, (i <= j < e1)%Z -> in_hull A (uE E b + j) = false ->
               (0 <= uE E b + j < 2 ^ 64)%Z /\ M (Z_to_bv 64 (uE E b + j)) <> None).
  { intros kb kk l P [Hfl Hall] HP Hc.
    destruct (expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool eqn:Hcnd; [|discriminate].
    injection Hc as <-.
    repeat match type of Hcnd with (_ && _)%bool = true => apply andb_prop in Hcnd as [Hcnd ?X] end.
    apply expr_eqb_eq in Hcnd. subst kb. apply Z.leb_le in X2. apply Z.ltb_lt in X1. apply Z.leb_le in X0. apply Z.ltb_lt in X.
    unfold two64 in X1. rewrite (elenZ_lit E l) in Hfl, Hall by lia.
    destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in *; cbn [a_base a_off] in *. unfold uE.
    split; [lia|]. intros j Hj Hh. split; [lia|].
    replace (bv_unsigned (edenot E b) + j)%Z with (bv_unsigned (edenot E b) + kk + (j - kk))%Z by lia.
    apply HP. apply Hall. lia. }
  destruct K as [[kb kk] w v|[kb kk] [l| | | | | | |]|[kb kk] [l| | | | | | |] bk| | | | | |[kb kk] [l| | | | | | |] fc|[kb kk] [l| | | | | | |]];
    try discriminate.
  - (* [comment removed for export] *)
    destruct (expr_eqb b kb && Z.leb kk i && Z.ltb i (kk + Z.of_nat w))%bool eqn:Hcnd; [|discriminate]. injection Hhit as <-.
    apply andb_prop in Hcnd as [Hcnd X]. apply andb_prop in Hcnd as [Hb X0].
    apply expr_eqb_eq in Hb. subst kb. apply Z.leb_le in X0. apply Z.ltb_lt in X.
    cbn [kentry_ok] in HKK. destruct HKK as (Hw & Hfl & Hrd).
    pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in *; cbn [a_base a_off] in *. unfold uE.
    split; [lia|]. intros j Hj Hh. split; [lia|].
    apply (rdn_bytes_some M _ w _ Hrd); rewrite ?Hu, ?u64_lit by lia; [lia | exact Hh].
  - (* [comment removed for export] *) eapply (ZF kb kk l (fun x => x = Some (Z_to_bv 8 0))); [exact HKK | intros x ->; discriminate | exact Hhit].
  - (* [comment removed for export] *) cbn [kentry_ok] in HKK. destruct HKK as (Hfl & Hlen & Hall).
    eapply (ZF kb kk l (fun x => exists b0, x = Some b0)); [split; [exact Hfl | intros i0 Hi0; eexists; apply Hall; exact Hi0] | intros x [b0 ->]; discriminate | exact Hhit].
  - (* [comment removed for export] *) eapply (ZF kb kk l (fun x => x = Some (Z_to_bv 8 fc))); [exact HKK | intros x ->; discriminate | exact Hhit].
  - (* [comment removed for export] *) eapply (ZF kb kk l (fun x => x <> None)); [exact HKK | intros x Hx; exact Hx | exact Hhit].
Qed.

#[using="SEGS_in_hull"] Lemma cover_x_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pfuel,$6:.PE,$0.PM,P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)Pb,$29.Pi,$1.Pstop,$1.P,(64.VSEGS,R6.R5.R4.)P,(3.$20.(?0.R8.R5.R4.R3.R2.)$22.)Pj,$1.P,(5.(2.R5.R1.)(1?.R1.R4.))P,(3.$20.(38.VA,(18.(6.R:.R7.)R2.))$33.)(5.(5.(2.=(18.(6.R;.R8.)R3.))(1?.(18.(6.R;.R8.)R3.)(91.+2.+40.)))(24.(3.(23.(12.&8.))A1.R:.(42.&40.(18.(6.R;.R8.)R3.))(25.(12.&8.)))))")
(* [comment removed for export] *).
Proof.
  induction fuel as [|f IH]; intros E M k b i stop HK H j Hj Hh; [discriminate|].
  cbn [cover_x] in H. destruct (Z.leb_spec stop i); [lia|].
  destruct (cover1 k b i) as [e|] eqn:Hc; [|discriminate].
  destruct (Z.ltb_spec i e); [|discriminate].
  destruct (cover1_sound E M k b i e HK Hc) as [_ Hcov].
  destruct (Z.lt_ge_cases j e).
  - apply Hcov; [lia | exact Hh].
  - eapply IH; [exact HK | exact H | lia | exact Hh].
Qed.

#[using="SEGS_in_hull HULL_ok"] Lemma kunk_covered_sound : forall E M k K, know_ok SEGS E M k -> kunk_covered A k K = true -> kentry_ok SEGS E M K.
Proof.
  intros E M k K HK H. unfold kunk_covered in H.
  destruct K as [| | | | | | | | |[b o] [n| | | | | | |]]; try discriminate.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Z.ltb_lt in H. apply Z.leb_le in X3. apply Z.leb_le in X2.
  pose proof (flat_x_sound E M k b o (ELit n) HK X1) as (F1 & F2 & F3).
  pose proof (ranges_apart_x_sound SEGS E M k _ _ _ _ _ _ HK X0) as AP0.
  cbn [edenot] in F2, F3. rewrite u64_lit in F2, F3 by lia.
  pose proof HULL_ok as HU; unfold hull_ok, KHI in HU.
  rewrite (elenZ_lit E n) in AP0 by lia. rewrite (elenZ_lit E (img_hi A - img_lo A)) in AP0 by lia.
  unfold estart in AP0; cbn [a_base a_off edenot] in AP0. rewrite u_lit0 in AP0.
  cbn [kentry_ok]. rewrite elenZ_lit by lia. split.
  - unfold flat, estart in *; cbn [a_base a_off] in *. lia.
  - intros i Hi. unfold estart in *; cbn [a_base a_off] in *.
    replace (bv_unsigned (edenot E b) + o + i)%Z with (uE E b + (o + i))%Z by (unfold uE; lia).
    apply (cover_x_sound _ E M k b o (o + n) HK X); [lia|].
    unfold in_hull, uE. apply andb_false_iff.
    destruct AP0 as [AP0|AP0]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

#[using="SEGS_in_hull HULL_ok"] Lemma kn_incl_h_sound : forall E M k tk, know_ok SEGS E M k -> kn_incl_h A k tk = true -> know_ok SEGS E M tk.
Proof.
  intros E M k tk HK H. unfold kn_incl_h in H. apply Forall_forall. intros K Hin.
  pose proof (proj1 (forallb_forall _ _) H K Hin) as HK1. unfold kn_incl1_h in HK1.
  destruct (existsb (fun X => kentry_eqb X K) k) eqn:Hex1.
  { apply existsb_exists in Hex1 as [X [HinX Heq]]. apply kentry_eqb_eq in Heq. subst. exact (proj1 (Forall_forall _ _) HK K HinX). }
  (* [comment removed for export] *)
  assert (IMG : kimg_sub_covered k K = true -> kentry_ok SEGS E M K).
  { intros Hc. unfold kimg_sub_covered in Hc. destruct K as [| | |lo hi| | | | | |]; try discriminate.
    apply existsb_exists in Hc as [X [HinX HX]]. destruct X as [| | |lo' hi'| | | | | |]; try discriminate.
    apply andb_prop in HX as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (proj1 (Forall_forall _ _) HK _ HinX) as HKX. cbn [kentry_ok] in HKX |- *.
    destruct HKX as (Ha & Hb & Hc). split; [lia|]. split; [lia|]. intros i Hi. apply Hc. lia. }
  destruct (kflat_h k K) eqn:Hfl.
  - destruct (existsb (fun X => kentry_eqb_h X K) k) eqn:Hex.
    + apply existsb_exists in Hex as [X [HinX Heq]].
      eapply kentry_eqb_h_sound; [exact HK | exact (proj1 (Forall_forall _ _) HK X HinX) | exact Heq | exact Hfl].
    + destruct (kimg_sub_covered k K) eqn:Himg; [exact (IMG eq_refl)|]. eapply kunk_covered_sound; [exact HK | exact HK1].
  - destruct (kimg_sub_covered k K) eqn:Himg; [exact (IMG eq_refl)|]. eapply kunk_covered_sound; [exact HK | exact HK1].
Qed.

(* [comment removed for export] *)
Definition is_havoc (lo hi : nat) (t : expr) : option nat :=
  match t with EVar v => if (Nat.leb lo v && Nat.ltb v hi)%bool then Some v else None | _ => None end.

Fixpoint henv (lo hi : nat) (E : env) (rs ts : list expr) : env :=
  match rs, ts with
  | r :: rs', t :: ts' =>
      let E1 := henv lo hi E rs' ts' in
      match is_havoc lo hi t with Some v => upd E1 v (edenot E r) | None => E1 end
  | _, _ => E
  end.

#[using="Type"] Lemma is_havoc_range : forall lo hi t v, is_havoc lo hi t = Some v -> t = EVar v /\ (lo <= v < hi)%nat.
Proof.
  intros lo hi t v H. destruct t; try discriminate. cbn [is_havoc] in H.
  destruct (Nat.leb lo n && Nat.ltb n hi)%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [H1 H2]. apply Nat.leb_le in H1. apply Nat.ltb_lt in H2. split; [reflexivity | lia].
Qed.

#[using="Type"] Lemma henv_agree : forall lo hi E rs ts, env_agree lo E (henv lo hi E rs ts).
Proof.
  intros lo hi E rs. induction rs as [|r rs IH]; intros [|t ts]; cbn [henv]; try apply env_agree_refl.
  destruct (is_havoc lo hi t) as [v|] eqn:Hv; [|apply IH].
  apply is_havoc_range in Hv as [_ Hv]. eapply env_agree_trans; [apply IH|]. eapply env_agree_le; [apply upd_agree | lia].
Qed.

#[using="Type"] Lemma henv_high : forall lo hi E rs ts n, (hi <= n)%nat -> ev (henv lo hi E rs ts) n = ev E n.
Proof.
  intros lo hi E rs. induction rs as [|r rs IH]; intros [|t ts] n Hn; cbn [henv]; try reflexivity.
  destruct (is_havoc lo hi t) as [v|] eqn:Hv; [|apply IH; exact Hn].
  apply is_havoc_range in Hv as [_ Hv]. cbn [upd ev]. destruct (Nat.eqb_spec n v); [lia|]. apply IH. exact Hn.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma regs_match_h_char : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Plo,$6:.Phi,$6:.Pseen,(2?.$6:.)Prs,(2?.$29.)Pts,(2?.$29.)P,(3.$20.(?1.R5.R4.R3.R2.R1.)$22.)(5.(3.$6:.(>0.$29.R3.)(>0.$29.R2.))Pi,$6:.P,(;:.R1.(>0.$29.R3.))(1:.(4:.$6:.Lv,$6:.(5.(3.(23.$6:.)(?2.R9.R8.(;?.$29.R3.R5.(<0.=)))(82.$6:.R1.))(5.(24.(34.$6:.R1.R7.))Pi',$6:.P,(;:.R1.R4.)(24.(3.(23.$6:.)(?2.R;.R:.(;?.$29.R2.R7.(<0.=)))(82.$6:.R3.))))))(5.(3.(23.$6:.)(?2.R8.R7.(;?.$29.R2.R4.(<0.=)))(25.$6:.))(5.(3.$29.(;?.$29.R2.R4.(<0.=))(;?.$29.R2.R5.(<0.=)))(3.$20.(;4.R8.(;?.$29.R2.R4.(<0.=)))$22.)))))")
(* [comment removed for export] *).
Proof.
  intros lo hi seen rs. revert seen. induction rs as [|r rs IH]; intros seen [|t ts] H; cbn [regs_match_h length] in H |- *; try discriminate.
  - split; [reflexivity | intros i Hi; lia].
  - assert (STEP : forall seen', regs_match_h lo hi seen' rs ts = true -> (forall v, In v seen -> In v seen') ->
              (forall v, is_havoc lo hi t = Some v -> In v seen') ->
              length rs = length ts /\ forall i, (Datatypes.S i < Datatypes.S (length ts))%nat ->
                (exists v, is_havoc lo hi (nth (Datatypes.S i) (t :: ts) (ELit 0)) = Some v /\ ~ In v seen /\
                   forall i', (i' < Datatypes.S i)%nat -> is_havoc lo hi (nth i' (t :: ts) (ELit 0)) <> Some v)
                \/ (is_havoc lo hi (nth (Datatypes.S i) (t :: ts) (ELit 0)) = None /\ nth (Datatypes.S i) (t :: ts) (ELit 0) = nth (Datatypes.S i) (r :: rs) (ELit 0)
                    /\ AP.expr_vars_lt lo (nth (Datatypes.S i) (t :: ts) (ELit 0)) = true)).
    { intros seen' Hm Hsub Ht. destruct (IH seen' ts Hm) as [Hlen Hc]. split; [exact Hlen|].
      intros i Hi. cbn [nth]. destruct (Hc i ltac:(lia)) as [[v (Hv & Hns & Hbefore)]|Hn]; [left|right; exact Hn].
      exists v. split; [exact Hv|]. split; [intros Hin; apply Hns; apply Hsub; exact Hin|].
      intros [|i'] Hi'; cbn [nth].
      - intros Heq. apply Hns. apply Ht. exact Heq.
      - apply Hbefore. lia. }
    destruct (is_havoc lo hi t) as [v|] eqn:Hv.
    + destruct t as [|w| | | | | |]; try discriminate. cbn [is_havoc] in Hv.
      destruct (Nat.leb lo w && Nat.ltb w hi)%bool eqn:Hr; [|discriminate]. injection Hv as Hwv. subst v.
      apply andb_prop in H as [Hnew Hm]. apply negb_true_iff in Hnew.
      assert (Hns : ~ In w seen).
      { intros Hin. enough (existsb (Nat.eqb w) seen = true) by congruence. apply existsb_exists. exists w. split; [exact Hin | apply Nat.eqb_refl]. }
      destruct (STEP (w :: seen) Hm ltac:(intros; right; assumption) ltac:(intros v' Hv'; injection Hv' as <-; left; reflexivity)) as [Hlen Hc].
      split; [rewrite Hlen; reflexivity|]. intros [|i] Hi; [|exact (Hc i Hi)].
      left. exists w. cbn [nth is_havoc]. rewrite Hr. split; [reflexivity|]. split; [exact Hns|]. intros i' Hi'. lia.
    + assert (Hm : (expr_eqb r t && AP.expr_vars_lt lo t && regs_match_h lo hi seen rs ts)%bool = true).
      { destruct t; try exact H. cbn [is_havoc] in Hv. destruct (Nat.leb lo n && Nat.ltb n hi)%bool; [discriminate | exact H]. }
      apply andb_prop in Hm as [Hm1 Hm]. apply andb_prop in Hm1 as [He Hvl]. apply expr_eqb_eq in He. subst t.
      destruct (STEP seen Hm ltac:(intros; assumption) ltac:(intros v' Hv'; discriminate Hv')) as [Hlen Hc].
      split; [rewrite Hlen; reflexivity|]. intros [|i] Hi; [|exact (Hc i Hi)].
      right. cbn [nth]. split; [exact Hv|]. split; [reflexivity | exact Hvl].
Qed.

#[using="Type"] Lemma henv_havoc : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Plo,$6:.Phi,$6:.PE,$0.Prs,(2?.$29.)Pts,(2?.$29.)Pi,$6:.Pv,$6:.P,(3.$6:.(>0.$29.R4.)(>0.$29.R3.))P,(;:.R3.(>0.$29.R4.))P,(3.(23.$6:.)(?2.R9.R8.(;?.$29.R4.R5.(<0.=)))(82.$6:.R3.))P,Pi',$6:.P,(;:.R1.R6.)(24.(3.(23.$6:.)(?2.R<.R;.(;?.$29.R2.R8.(<0.=)))(82.$6:.R6.)))(3.(12.&40.)(=9.(?3.R;.R:.R9.R8.R7.)R5.)(52.R9.(;?.$29.R6.R8.(<0.=))))")
(* [comment removed for export] *).
Proof.
  intros lo hi E rs. induction rs as [|r rs IH]; intros [|t ts] i v Hlen Hi Hv Hbefore; cbn [length] in *; try lia.
  cbn [henv]. destruct i as [|i]; cbn [nth] in *.
  - rewrite Hv. apply upd_at.
  - destruct (is_havoc lo hi t) as [v'|] eqn:Ht.
    + cbn [upd ev]. destruct (Nat.eqb_spec v v').
      * subst v'. exfalso. exact (Hbefore 0%nat ltac:(lia) Ht).
      * apply IH; [lia | lia | exact Hv |]. intros i' Hi'. exact (Hbefore (Datatypes.S i') ltac:(lia)).
    + apply IH; [lia | lia | exact Hv |]. intros i' Hi'. exact (Hbefore (Datatypes.S i') ltac:(lia)).
Qed.

#[using="Type"] Lemma regs_match_h_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Plo,$6:.Phi,$6:.PE,$0.Prs,(2?.$29.)Pts,(2?.$29.)PR,(55.&5.(12.&40.))P,(3.$20.(?1.R6.R5.(2=.$6:.)R3.R2.)$22.)P,(3.$6:.(>0.$29.R3.)#20.)P,(60.R6.R5.R3.)(60.(?3.R9.R8.R7.R6.R5.)R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros lo hi E rs ts R H Hlen HR. destruct (regs_match_h_char lo hi [] rs ts H) as [Hl Hc].
  intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0; [exact (eq_trans (HR r) ltac:(unfold sr_get; rewrite Hr0; reflexivity))|].
  pose proof (ridx_range r) as Hlt. specialize (HR r). unfold sr_get in HR. rewrite Hr0 in HR. rewrite HR.
  destruct (Hc (ridx r) ltac:(lia)) as [[v (Hv & _ & Hbefore)]|(Hn & Heq & Hvl)].
  - destruct (is_havoc_range _ _ _ _ Hv) as [Et _]. rewrite Et. cbn [edenot]. symmetry. apply (henv_havoc lo hi E rs ts (ridx r) v Hl ltac:(lia) Hv Hbefore).
  - rewrite Heq in Hvl |- *. eapply (edenot_agree' lo); [apply henv_agree | exact Hvl].
Qed.

(* [comment removed for export] *)
#[using="argH_agree SINV_agree"] Lemma cs_ok_reenv : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pb,$6:.PE,$0.PE',$0.Pcs,$2>.Psr',(2?.$29.)PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.P,(57.R7.R5.R3.R2.R1.)P,(9;.R9.R8.R7.)P,(<:.Vnx0,R:.)P,(3.$20.(9<.R;.(6<.R8.))$22.)P,(3.$20.(<5.R<.(8;.R9.))$22.)P,(3.$20.(<6.R=.(31.(11.$29.$29.)(8<.R:.)(30.R:.)))$22.)P,(3.$20.(;4.R>.(<7.R;.))$22.)P,(3.$20.(<8.R?.(<9.R<.))$22.)P,(3.$20.(<6.R10.(?4.R=.))$22.)P,(60.R?.R=.R<.)(57.R10.(?5.R?.R>.)R=.R<.R;.)")
(* [comment removed for export] *).
Proof.
  intros b E E' cs sr' R FULL model HC Hag Hb Hkn Hmaps Hallow Hbrk Hfd Hsubv HR.
  pose proof (hid_agree b E E' cs model Hag Hb Hallow) as HH.
  rewrite <- (hid_ext E' cs (set_regs cs sr') model eq_refl) in HH.
  pose proof (allowA_agree b E E' cs Hag Hallow) as HA.
  assert (HA2 : allowA E' (set_regs cs sr') = allowA E' cs) by reflexivity. rewrite <- HA2 in HA. clear HA2.
  destruct HC; constructor; cbn [set_regs with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_sub] in *;
    rewrite ?HA; try assumption; try reflexivity.
  - unfold Mr in *. rewrite HH. eapply know_ok_agree'; eassumption.
  - eapply fds_ok_agree; eassumption.
  - eapply maps_match_agree; [exact Hag | exact Hmaps | assumption].
  - eapply holes_agree; [exact Hag | exact Hmaps | assumption].
  - apply Forall_forall. intros m Hin Hk.
    pose proof (proj1 (forallb_forall _ _) Hmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
    unfold amap_den. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
    exact (proj1 (Forall_forall _ _) co_none0 m Hin Hk).
  - apply Forall_forall. intros m Hin Hk a Ha.
    pose proof (proj1 (forallb_forall _ _) Hmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
    rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2) in Ha.
    exact (proj1 (Forall_forall _ _) co_kinds0 m Hin Hk a Ha).
  - rewrite <- (edenot_agree' b E E' _ Hag Hbrk). assumption.
  - intros a. rewrite HH. change (in_ghost E' (set_regs cs sr')) with (in_ghost E' cs). rewrite (in_ghost_agree b E E' cs Hag Hallow). exact (co_zero0 a).
  - eapply SINV_agree; [eapply env_agree_le; [exact Hag | exact Hb] | assumption].
  - (* [comment removed for export] *) eapply nlz_ok_agree; [exact Hag | exact Hmaps | assumption].
  - eapply nlz_ok_agree; [exact Hag | exact Hmaps | assumption].
  - eapply sub_Forall_agree; [exact Hag | exact Hsubv | assumption].
  - (* [comment removed for export] *) eapply def_Forall_agree; [exact Hag | exact Hmaps | assumption].
  - (* [comment removed for export] *) eapply cov_Forall_agree; [exact Hag | exact Hmaps | exact Hsubv | assumption].
Qed.

#[using="SEGS_in_hull HULL_ok argH_agree SINV_agree"] Lemma entails_h_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Plo,$6:.Phi,$6:.PE,$0.Pcs,$2>.PT,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.P,(57.R6.R5.R3.R2.R1.)P,(3.$20.(?6.VA,R9.R8.R6.R5.)$22.)P,(<:.Vnx0,R:.)P,(3.$6:.(>0.$29.(61.(<4.R7.)))#20.)(4:.$0.LE',$0.(5.(9;.R=.R;.R1.)(5.Pn,$6:.P,(<:.R=.R1.)(3.(12.&40.)(=9.R3.R2.)(=9.R=.R2.))(5.(57.R1.R9.R8.R7.R6.)(3.$1.(83.R9.)(83.R:.))))))")
(* [comment removed for export] *).
Proof.
  intros lo hi E cs T R FULL model HC H Hlo Hlen. unfold entails_h in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc.
  match goal with Hl : match s_log (a_ss T) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss T)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
  match goal with Hl : match s_resv (a_ss T) with _ => _ end = true |- _ => rename Hl into HRV; destruct (s_resv (a_ss T)) eqn:HRV'; [discriminate|clear HRV; rename HRV' into HRV] end.
  match goal with Hr : regs_match_h _ _ _ _ _ = true |- _ => rename Hr into Hregs end.
  match goal with Hm : list_eqb amap_eqb _ _ = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hm; rename Hm into Hmaps end.
  match goal with Ha : list_eqb pair_eqb (a_vis cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Hallow end.
  match goal with Hg : list_eqb pair_eqb (a_ghost cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hg; rename Hg into Hghost end.
  match goal with Hs : list_eqb pair_eqb (a_sub cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hs; rename Hs into Hsub end.   (* [comment removed for export] *)
  match goal with Hs : pairs_vars_lt lo (a_sub T) = true |- _ => rename Hs into Hsubv end.
  match goal with Hb : expr_eqb (a_brk cs) _ = true |- _ => apply expr_eqb_eq in Hb; rename Hb into Hbrk end.
  match goal with Hf : afd_eqb _ _ = true |- _ => apply afd_eqb_eq in Hf; rename Hf into Hfd end.
  match goal with Ht : Bool.eqb _ _ = true |- _ => apply eqb_prop in Ht; rename Ht into Htid end.
  match goal with Hk : kn_incl_h _ _ (kn T) = true |- _ => rename Hk into Hkn end.
  repeat match goal with Hz : Z.leb _ _ = true |- _ => apply Z.leb_le in Hz end.
  set (E' := henv lo hi E (s_regs (a_ss cs)) (s_regs (a_ss T))).
  exists E'. split; [apply henv_agree|]. split; [intros; apply henv_high; assumption|]. split; [|symmetry; exact Hpc].
  (* [comment removed for export] *)
  set (Tc := set_regs T (s_regs (a_ss cs))).
  assert (Evis : a_vis Tc = a_vis cs) by (unfold Tc; cbn [set_regs with_ss a_vis]; symmetry; exact Hallow).
  assert (HA : allowA E Tc = allowA E cs) by (unfold allowA; unfold Tc; cbn [set_regs with_ss a_vis a_ghost]; rewrite Hallow, Hghost; reflexivity).
  assert (HH : hid E Tc model = hid E cs model) by (apply hid_ext; exact Evis).
  assert (HC1 : cs_ok E Tc R FULL model).
  { destruct HC; constructor; rewrite ?HA;
      try (unfold Tc; cbn [set_regs with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_sub];
           rewrite <- ?Hmaps, <- ?Hallow, <- ?Hghost, <- ?Hsub, <- ?Hbrk, <- ?Hfd, <- ?Htid; first [assumption | reflexivity | lia]).
    - unfold Mr. rewrite HH. eapply kn_incl_h_sound; [exact co_know0 | exact Hkn].
    - unfold Tc. cbn [set_regs with_ss a_maps a_ylo]. rewrite <- Hmaps. eapply holes_mono; [exact co_holes0 | lia].
    - intros a. rewrite HH. replace (in_ghost E Tc) with (in_ghost E cs) by (unfold in_ghost, in_ghostl, Tc; cbn [set_regs with_ss a_ghost]; rewrite Hghost; reflexivity).
      exact (co_zero0 a). }
  (* [comment removed for export] *)
  assert (ET : T = set_regs Tc (s_regs (a_ss T))).
  { subst Tc. clear - HL HRV. destruct T as [[p sr lg k nx rv] m t y e v g ab br f ti sb]. cbn in HL, HRV. subst lg rv. reflexivity. }
  rewrite ET at 1. eapply (cs_ok_reenv lo); try eassumption.
  - apply henv_agree.
  - unfold pairs_vars_lt, Tc. cbn [set_regs with_ss a_vis a_ghost]. rewrite forallb_app. apply andb_true_intro; split; assumption.
  - apply regs_match_h_sound; [exact Hregs | exact Hlen | exact (co_regs _ _ _ _ _ HC)].   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
#[using="SEGS_in_hull HULL_ok argH_agree SINV_agree"] Lemma diamond_join_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pnx,$6:.Pjoinpc,$1.Prs,(2?.$6:.)Pca,$2>.Pcb,$2>.Pcsj,$2>.P,(3.(23.$2>.)(?7.VA,Vnx0,R6.R5.R4.R3.R2.)(82.$2>.R1.))(5.PE,$0.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.P,(57.R4.R8.R3.R2.R1.)(4:.$0.LE',$0.(5.(5.(9;.Vnx0,R6.R1.)(9;.R=.R6.R1.))(5.(57.R1.R8.R5.R4.R3.)(3.$1.(83.R8.)(83.R:.)))))PE,$0.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.P,(57.R4.R7.R3.R2.R1.)(4:.$0.LE',$0.(5.(5.(9;.Vnx0,R6.R1.)(9;.R=.R6.R1.))(5.(57.R1.R8.R5.R4.R3.)(3.$1.(83.R8.)(83.R9.))))))")
(* [comment removed for export] *).
Proof.
  intros nx joinpc rs ca cb csj H. unfold node_diamond_join in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  match goal with Hl : Nat.eqb (length ?l) 32 = true |- _ => apply Nat.eqb_eq in Hl; rename Hl into Hlen end.
  match goal with Hl : Nat.leb nx0 ?v = true |- _ => apply Nat.leb_le in Hl; rename Hl into Hn0 end.
  split; intros E R FULL model HC.
  - match goal with Hea : entails_h A ?lo ?hi ca ?T = true |- _ =>
      destruct (entails_h_sound lo hi E ca T R FULL model HC Hea Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc) end.
    exists E'. split; [split; eapply env_agree_le; [exact Hag | lia | exact Hag | lia] | split; [exact HC' | exact Hpc]].
  - match goal with Hea : entails_h A ?lo ?hi cb ?T = true |- _ =>
      destruct (entails_h_sound lo hi E cb T R FULL model HC Hea Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc) end.
    exists E'. split; [split; eapply env_agree_le; [exact Hag | lia | exact Hag | lia] | split; [exact HC' | exact Hpc]].
Qed.

#[using="Type"] Lemma loop_ok_facts : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pcs,$2>.PJ,$6:.PN,$29.Pinv,$2>.Pnhi,$1.P,(3.(23.$1.)(?8.Vnx0,R5.R4.R3.R2.)(82.$1.R1.))(5.(3.$20.(<3.Vnx0,R6.)$22.)(5.(<:.(:4.R6.)R5.)(5.(;:.R5.(:4.R3.))(5.(3.(2?.$62.)(63.(<4.R3.))(2=.$62.))(5.(3.$6:.(>0.$29.(61.(<4.R3.)))#20.)(5.(3.$20.(;4.(:4.R6.)R4.)$22.)(5.(3.(23.$1.)(?9.(6<.R6.)R4.)(82.$1.R2.))(1?.R2.$;>.))))))))")
(* [comment removed for export] *).
Proof.
  intros cs J N inv nhi H. unfold loop_ok in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  destruct (xhi (kn cs) N) as [h|] eqn:Hx; [|discriminate]. destruct (Z.ltb h two64) eqn:Hlt; [|discriminate]. injection H as <-.
  apply Z.ltb_lt in Hlt.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  apply Nat.leb_le in X13. apply Nat.ltb_lt in X12.   (* [comment removed for export] *)
  destruct (s_log (a_ss inv)); [|discriminate]. apply Nat.eqb_eq in X8.
  repeat split; try assumption; reflexivity.
Qed.

#[using="Type"] Lemma pc_inst : forall inv J e, pc (inst inv J e) = pc inv.
Proof. reflexivity. Qed.
#[using="Type"] Lemma nxt_inst : forall inv J e, nxt (inst inv J e) = nxt inv.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma check_all_ok : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pchk,P,$2>.P,$?:.$?;.Pk,$?:.Pcss,(2?.$2>.)Ps,$:0.P,(3.$?;.(?<.VA,R4.R3.R2.)(?=.R1.))(5.(4:.$2>.Lcs1,$2>.(5.(34.$2>.R1.R4.)(5.(3.$?;.A2.R6.R1.R5.(?=.R3.))$?>.)))Pcs,$2>.P,(34.$2>.R1.R4.)(3.$?;.A2.R7.R2.R6.(?=.R4.)))")
(* [comment removed for export] *).
Proof.
  intros chk k css s H. unfold check_all in H. destruct css as [|cs0 rest]; [discriminate|].
  destruct (chk cs0 k) as [s0|] eqn:H0; [|discriminate].
  match type of H with fold_left ?F rest (COk s0) = _ =>
  assert (GEN : forall l acc, fold_left F l acc = COk s ->
                 acc = COk s /\ forall cs, In cs l -> chk cs k = COk s) end.
  { induction l as [|c l IHl]; intros acc Hf; cbn [fold_left] in Hf.
    - split; [exact Hf | intros ? []].
    - destruct acc as [s1|c1 q1 r1].
      + destruct (chk c k) as [s'|] eqn:Hc'; [| apply IHl in Hf as [Hf _]; discriminate].
        destruct (shape_eqb s1 s') eqn:Hse; [| apply IHl in Hf as [Hf _]; discriminate].
        apply IHl in Hf as [E1 Hl]. injection E1 as ->. apply shape_eqb_eq in Hse. subst s'.
        split; [reflexivity|]. intros cs [<-|Hin]; [exact Hc' | apply Hl; exact Hin].
      + apply IHl in Hf as [Hf _]. discriminate. }
  apply GEN in H as [E0 Hrest]. injection E0 as ->.
  split; [exists cs0; split; [left; reflexivity | split; [exact H0 | exact I]]|].
  intros cs [<-|Hin]; [exact H0 | apply Hrest; exact Hin].
Qed.

#[using="Type"] Lemma check_vars : forall bfuel fuel lc p cs s,
  CHECK bfuel fuel lc cs p = COk s -> shape_vars_lt nx0 s = true.
Proof.
  intros bfuel fuel. induction fuel as [|fuel IH]; intros lc p cs s Hc; [discriminate|].
  cbn [AP.check] in Hc.
  match type of Hc with (if ?g then _ else _) = _ => destruct g; [discriminate|] end.
  destruct p as [stops k|e mid k1 k2|ce cmid ck1 ck2|db1 db2 dk1 dk2|sb1 sn1 sb2 sn2 k| |K k|jb joff jn k|ixs k|db dn k|gws k|bm k|hrs k|hbK k|r logc fb k|y k|ma mb|ia ib ic|qa qb|ka kb|x args k|xid xargs k|eid eargs k|bid bargs kb1 kb2|lJ lN linv lbody lk| |h| | |fi fsz fk|gi gsz gk|gb gn gk2|ub un uk|hlo hhi hk|ilo ihi ik|djp drs dk|rnm rnk|cpk|vj vjs vlo vka vk|mj|ab an ak|hws hwk|rsr rse rsk|iha ihb ihc].
  - destruct (run_block_gc SEGS IT _ KC bfuel (stops ++ STOPS A) cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (AP.expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
    destruct (erange (kn cs) e) as [[lo hi]|]; [|discriminate].
    destruct (Z.leb lo mid && Z.ltb mid hi)%bool.
    2: { destruct (Z.leb hi mid); [exact (IH _ k1 _ s Hc) | exact (IH _ k2 _ s Hc)]. }
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange e lo mid :: kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange e (mid+1) hi :: kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
    injection Hc as <-. cbn [shape_vars_lt]. rewrite Hv, (IH _ k1 _ s1 H1), (IH _ k2 _ s2 H2). reflexivity.
  - destruct (erange (kn cs) ce) as [[lo hi]|]; [|discriminate].
    destruct (Z.leb lo cmid && Z.ltb cmid hi)%bool.
    2: { cbn [negb] in Hc. destruct (Z.leb hi cmid); [exact (IH _ ck1 _ s Hc) | exact (IH _ ck2 _ s Hc)]. }
    cbn [negb] in Hc. cbv zeta in Hc.
    destruct (kn_contra (kn (set_kn cs (KRange ce lo cmid :: kn cs)))); [exact (IH _ ck2 _ s Hc)|].
    destruct (kn_contra (kn (set_kn cs (KRange ce (cmid + 1) hi :: kn cs)))); [exact (IH _ ck1 _ s Hc)|].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce lo cmid :: kn cs)) ck1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce (cmid+1) hi :: kn cs)) ck2) as [s2|] eqn:H2; [|discriminate].
    destruct (shape_eqb s1 s2); [|discriminate]. injection Hc as <-. exact (IH _ ck1 _ s1 H1).
  - destruct (node_casedisj cs db1 db2) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa dk1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb dk2) as [s2|] eqn:H2; [|discriminate].
    destruct (shape_eqb s1 s2); [|discriminate]. injection Hc as <-. exact (IH _ dk1 _ s1 H1).
  - destruct (node_shdisj A cs sb1 sn1 sb2 sn2) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (kn_contra (kn cs)); [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (fact_ok (kn cs) K); [|discriminate]. exact (IH _ k _ s Hc).
  - destruct (node_join SEGS cs jb joff jn) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - exact (IH _ k _ s Hc).
  - exact (IH _ k _ s Hc).
  - exact (IH _ k _ s Hc).
  - destruct (node_bump cs bm) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (node_havoc nx0 cs hrs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (node_havocbig nx0 cs hbK) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (node_fresh nx0 cs r logc fb) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_sys A nx0 y cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mmap2 A nx0 LIMIT cs) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa ma) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb mb) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-. apply salt2_vars; [exact (IH _ ma _ sa H1) | exact (IH _ mb _ sb H2)].
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mmapin A LIMIT false cs) as [[[csa csb] cscs]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa ia) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb ib) as [sb|] eqn:H2; [|discriminate].
    destruct (check_all A (CHECK bfuel fuel lc) ic cscs) as [sc|] eqn:H3; [|discriminate].
    injection Hc as <-.
    destruct (check_all_ok _ _ _ _ H3) as [(cs1 & Hin1 & Hc1 & _) _].
    apply salt2_vars; [exact (IH _ ia _ sa H1) | apply salt2_vars; [exact (IH _ ib _ sb H2) | exact (IH _ ic _ sc Hc1)]].
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mprotect2 A LIMIT cs) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa qa) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb qb) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-. apply salt2_vars; [exact (IH _ qa _ sa H1) | exact (IH _ qb _ sb H2)].
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_brk2 A LIMIT cs) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa ka) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb kb) as [sb|] eqn:H2; [|discriminate].
    destruct (shape_le sb sa); [|discriminate].   (* [comment removed for export] *)
    injection Hc as <-. apply salt2_vars; [exact (IH _ ka _ sa H1) | exact (IH _ kb _ sb H2)].
  - destruct (node_x SEGS A nx0 x args cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (XN xid xargs cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (XE eid eargs cs) as [[[fd ps] cs1]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc cs1 k) as [s1|] eqn:H1; [|discriminate].
    injection Hc as <-. cbn [shape_vars_lt]. exact (IH _ k cs1 s1 H1).
  - destruct (XB bid bargs cs) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa kb1) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb kb2) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-. cbn [shape_vars_lt]. rewrite (IH _ kb1 _ sa H1), (IH _ kb2 _ sb H2). reflexivity.
  - destruct (loop_ok nx0 cs lJ lN linv) as [nhi|]; [|discriminate].
    destruct (Z.eqb (pc linv) (pc cs) && entails_h A (Datatypes.S lJ) (nxt linv) cs (inst linv lJ (ELit 0)))%bool; [|discriminate].
    destruct (CHECK bfuel fuel (Some (LC (pc cs) (inst linv lJ (eaddz (EVar lJ) 1)) (Datatypes.S lJ) (nxt linv))) (loop_body_state lJ lN nhi linv) lbody) as [sb|]; [|discriminate].
    destruct sb; try discriminate. exact (IH _ lk _ s Hc).
  - destruct lc as [[h nx lo hi|j' js' sk' b' lo']|]; [|discriminate|discriminate].
    destruct (Z.eqb (pc cs) h && entails_h A lo hi cs nx)%bool; [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (HS h) as [ch|]; [|discriminate]. destruct (entails cs ch); [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_exit cs); [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (node_spin SEGS cs); [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (node_fog cs fi fsz) as [cs1|]; [|discriminate]. exact (IH _ fk cs1 s Hc).
  - destruct (node_fognew cs gi gsz) as [cs1|]; [|discriminate]. exact (IH _ gk cs1 s Hc).
  - destruct (node_ghost LIMIT cs gb gn) as [cs1|]; [|discriminate]. exact (IH _ gk2 cs1 s Hc).
  - destruct (node_unvis A cs ub un) as [cs1|]; [|discriminate]. exact (IH _ uk cs1 s Hc).
  - destruct (node_havocbrk nx0 cs hlo hhi) as [cs1|]; [|discriminate]. exact (IH _ hk cs1 s Hc).
  - destruct (node_intro nx0 cs ilo ihi) as [cs1|]; [|discriminate]. exact (IH _ ik cs1 s Hc).
  - destruct (branch_probe IT cs) as [e|]; [|discriminate].
    destruct (erange (kn cs) e) as [[lo hi]|]; [|discriminate].
    destruct (Z.ltb hi 1 || Z.ltb 0 lo)%bool.
    { destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) cs) as [cs1|]; [|discriminate].
      destruct (Z.eqb (pc cs1) djp); [|discriminate]. exact (IH _ dk cs1 s Hc). }
    cbv zeta in Hc.
    destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e lo 0 :: kn cs))) as [ca|]; [|discriminate].
    destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e 1 hi :: kn cs))) as [cb|]; [|discriminate].
    destruct (node_diamond_join A nx0 (nxt cs) djp drs ca cb) as [csj|]; [|discriminate]. exact (IH _ dk csj s Hc).
  - destruct (node_rename _ cs rnm) as [cs1|]; [|discriminate]. exact (IH _ rnk cs1 s Hc).
  - destruct (node_compact _ cs) as [cs1|]; [|discriminate]. exact (IH _ cpk cs1 s Hc).
  - destruct (via_ok nx0 cs vjs vlo); [|discriminate].
    destruct (CHECK bfuel fuel lc vjs vk) as [sk|]; [|discriminate]. exact (IH _ vka _ s Hc).
  - destruct lc as [[h nx lo hi|j' js' sk' b' lo']|]; [discriminate| |discriminate].
    destruct (Nat.eqb mj j' && Z.eqb (pc cs) (pc js') && shape_vars_lt nx0 sk' && entails_h A lo' (nxt js') cs js')%bool eqn:Ht; [|discriminate].
    injection Hc as <-. apply andb_prop in Ht as [Ht _]. apply andb_prop in Ht as [_ Hsv]. exact Hsv.
  - destruct (node_abstractcell A cs ab an) as [cs1|]; [|discriminate]. exact (IH _ ak cs1 s Hc).
  - destruct (node_havocwords nx0 cs hws) as [cs1|]; [|discriminate]. exact (IH _ hwk cs1 s Hc).
  - destruct (node_respell cs rsr rse) as [cs1|]; [|discriminate]. exact (IH _ rsk cs1 s Hc).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mmapin A LIMIT false cs) as [[[csa csb] cscs]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa iha) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb ihb) as [sb|] eqn:H2; [|discriminate].
    destruct (check_all A (CHECK bfuel fuel lc) ihc cscs) as [sc|] eqn:H3; [|discriminate].
    injection Hc as <-.
    destruct (check_all_ok _ _ _ _ H3) as [(cs1 & Hin1 & Hc1 & _) _].
    apply salt2_vars; [exact (IH _ iha _ sa H1) | apply salt2_vars; [exact (IH _ ihb _ sb H2) | exact (IH _ ihc _ sc Hc1)]].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma list_set_nth_maps_match : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pms,(2?.$48.)Pl,(2?.(11.(12.&40.)(12.&40.)))Pi,$6:.Pm,$48.Psz,$1.P,(3.(23.$48.)(??.$48.R5.R3.)(82.$48.R2.))P,(3.$20.(4>.R3.)$33.)P,(5.(2.=R3.)(1?.R3.$;>.))P,(2.(15.&40.(52.R9.(46.R5.)))R4.)P,(93.R:.R9.R8.)(93.R;.(100.$48.R8.(101.R6.)R:.)R9.)")
(* [comment removed for export] *).
Proof.
  intros E ms. induction ms as [|m0 ms IH]; intros l i m sz Hn Hf Hsz Hle HM; [destruct i; discriminate|].
  destruct i as [|i]; cbn [nth_error] in Hn; cbn [list_set_nth maps_match] in *.
  - injection Hn as ->. rewrite Hf in HM. destruct HM as (l' & -> & HM).
    unfold fog_token, is_fog. cbn [am_kind am_len mkind_eqb]. right. exists (amap_den E m), l'.
    split; [reflexivity|]. split; [|exact HM]. unfold uE, amap_den. cbn [snd edenot]. rewrite u64_lit by (unfold two64 in Hsz; lia). exact Hle.
  - destruct (is_fog m0).
    + destruct HM as [HM|(iv & l' & -> & Hs & HM)]; [left; eapply IH; eassumption | right].
      exists iv, l'. split; [reflexivity|]. split; [exact Hs | eapply IH; eassumption].
    + destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | eapply IH; eassumption].
Qed.

#[using="Type"] Lemma list_insert_nth_maps_match : forall E ms l i sz,
  maps_match E ms l -> maps_match E (list_insert_nth i (fog_token sz) ms) l.
Proof.
  intros E ms. induction ms as [|m0 ms IH]; intros l i sz HM.
  - destruct i; cbn [list_insert_nth maps_match]; unfold fog_token, is_fog; cbn [am_kind mkind_eqb]; left; exact HM.
  - destruct i as [|i]; cbn [list_insert_nth].
    + cbn [maps_match]. unfold fog_token at 1. unfold is_fog at 1. cbn [am_kind mkind_eqb]. left. exact HM.
    + cbn [maps_match] in *. destruct (is_fog m0).
      * destruct HM as [HM|(iv & l' & -> & Hs & HM)]; [left; apply IH; exact HM | right].
        exists iv, l'. split; [reflexivity|]. split; [exact Hs | apply IH; exact HM].
      * destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | apply IH; exact HM].
Qed.

#[using="Type"] Lemma In_list_set_nth : forall {T} (l : list T) i x y, In y (list_set_nth i x l) -> y = x \/ In y l.
Proof.
  intros T l. induction l as [|a l IH]; intros i x y H; [destruct i; cbn in H; destruct H|].
  destruct i; cbn in H; destruct H as [H|H]; try (right; left; exact H); try (left; symmetry; exact H).
  - right. right. exact H.
  - destruct (IH _ _ _ H) as [->|H']; [left; reflexivity | right; right; exact H'].
Qed.
#[using="Type"] Lemma In_list_insert_nth : forall {T} (l : list T) i x y, In y (list_insert_nth i x l) -> y = x \/ In y l.
Proof.
  intros T l. induction l as [|a l IH]; intros i x y H.
  - destruct i; cbn in H; destruct H as [H|[]]; left; symmetry; exact H.
  - destruct i; cbn in H; destruct H as [H|H]; try (left; symmetry; exact H); try (right; left; exact H).
    + right. exact H.
    + destruct (IH _ _ _ H) as [->|H']; [left; reflexivity | right; right; exact H'].
Qed.

#[using="Type"] Lemma cs_ok_with_maps : forall E cs R FULL model ms',
  cs_ok E cs R FULL model ->
  maps_match E ms' (vm_maps (m_vmmaps model)) ->
  (forall m, In m ms' -> m = fog_token (match am_len m with ELit z => z | _ => 0 end) \/ In m (a_maps cs)) ->
  cs_ok E (with_maps cs ms') R FULL model.
Proof.
  intros E cs R FULL model ms' HC HM Hsub.
  assert (HMr : Mr E (with_maps cs ms') model FULL = Mr E cs model FULL) by reflexivity.
  assert (HA : allowA E (with_maps cs ms') = allowA E cs) by reflexivity.
  destruct HC; constructor; unfold with_maps; rewrite ?HMr, ?HA;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn] in *; try assumption.
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk. destruct (Hsub m Hin) as [Hm|Hm].
    + rewrite Hm in Hk. cbn in Hk. discriminate.
    + exact (proj1 (Forall_forall _ _) co_holes0 m Hm Hk).
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk. destruct (Hsub m Hin) as [Hm|Hm].
    + rewrite Hm in Hk. cbn in Hk. destruct Hk; discriminate.
    + exact (proj1 (Forall_forall _ _) co_none0 m Hm Hk).
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk. destruct (Hsub m Hin) as [Hm|Hm].
    + rewrite Hm in Hk. cbn in Hk. discriminate.
    + exact (proj1 (Forall_forall _ _) co_kinds0 m Hm Hk).
  - (* [comment removed for export] *) eapply nlz_ok_weaken; [|exact co_nk0]. intros m' Hin' Hf' Hk'. destruct (Hsub m' Hin') as [Hm|Hm].
    + exfalso. rewrite Hm in Hf'. cbn in Hf'. discriminate.
    + exists m'. auto.
  - (* [comment removed for export] *) eapply nlz_ok_weaken; [|exact co_lzk0]. intros m' Hin' Hf' Hk'. destruct (Hsub m' Hin') as [Hm|Hm].
    + exfalso. rewrite Hm in Hf'. cbn in Hf'. discriminate.
    + exists m'. auto.
  - (* [comment removed for export] *) eapply def_Forall_weaken; [|exact co_def0]. intros m' Hin' Hf' Hk'. destruct (Hsub m' Hin') as [Hm|Hm].
    + exfalso. rewrite Hm in Hf'. cbn in Hf'. discriminate.
    + exists m'. auto.
  - (* [comment removed for export] *) eapply cov_Forall_weaken; [|exact co_cov0]. intros m' Hin' Hk'. destruct (Hsub m' Hin') as [Hm|Hm].
    + exfalso. rewrite Hm in Hk'. cbn in Hk'. destruct Hk' as [X|[X|[]]]; discriminate X.
    + exists m'. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cs_ok_sub_filter : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Psub',(2?.(11.$29.$29.))P,(57.R6.R5.R4.R3.R2.)P,Pt,(11.$29.$29.)P,(34.(11.$29.$29.)R1.R3.)(34.(11.$29.$29.)R2.(?4.R8.))P,Pm,$48.Pz,$1.Pt,(11.$29.$29.)P,(34.$48.R3.(8;.R:.))P,(34.$4?.(50.R4.)$53.)P,(5.(2.(6.R=.(45.R5.))R4.)(1?.R4.(18.(6.R=.(45.R5.))(6.R=.(46.R5.)))))P,(34.(11.$29.$29.)R4.(?4.R=.))P,(54.R?.R6.R5.)(34.(11.$29.$29.)R6.R;.)(57.R9.(102.R8.R4.)R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model sub' HC Hsub Hneed.
  assert (HMr : Mr E (with_sub cs sub') model FULL = Mr E cs model FULL) by reflexivity.
  assert (HA : allowA E (with_sub cs sub') = allowA E cs) by reflexivity.
  destruct HC; constructor; unfold with_sub; rewrite ?HMr, ?HA;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_sub kn] in *; try assumption.
  - apply Forall_forall. intros t Ht. exact (proj1 (Forall_forall _ _) co_sub0 t (Hsub t Ht)).
  - apply Forall_forall. intros m Hm Hk z Hz.
    destruct (proj1 (Forall_forall _ _) co_cov0 m Hm Hk z Hz) as [Hn|(t & Ht & Hzt)]; [left; exact Hn | right].
    exists t. split; [exact (Hneed m z t Hm Hk Hz Ht Hzt) | exact Hzt].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma maps_match_set_nth_disjoint : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pms,(2?.$48.)Pl,(2?.(11.(12.&40.)(12.&40.)))Pi,$6:.Pm0,$48.Ptok,$48.Pm,$48.P,(93.R7.R6.R5.)P,(103.R6.)P,(3.(23.$48.)(??.$48.R8.R6.)(82.$48.R5.))P,(3.$20.(4>.R6.)$33.)P,(3.$20.(4>.R6.)$22.)P,(34.$48.R6.(100.$48.R9.R7.R;.))P,(3.$20.(4>.R7.)$33.)(104.(96.R>.R:.)(96.R>.R8.))")
(* [comment removed for export] *).
Proof.
  intros E ms. induction ms as [|h r IH]; intros l i m0 tok m HM Hs Hn Hf0 Hft Hin Hfm; [destruct i; discriminate|].
  destruct i as [|i]; cbn [nth_error] in Hn; cbn [list_set_nth] in Hin; cbn [maps_match] in HM.
  - injection Hn as ->. rewrite Hf0 in HM. destruct HM as (l' & -> & HM). destruct Hin as [<-|Hin]; [congruence|].
    inversion Hs as [|p l0 Hd Hs']; subst. exact (proj1 (Forall_forall _ _) Hd _ (maps_match_In E r l' m HM Hin Hfm)).
  - destruct (is_fog h) eqn:Hfh.
    + destruct Hin as [<-|Hin]; [congruence|].
      destruct HM as [HM|(iv & l' & -> & _ & HM)]; [exact (IH l i m0 tok m HM Hs Hn Hf0 Hft Hin Hfm)|].
      inversion Hs as [|p l0 Hd Hs']; subst. exact (IH l' i m0 tok m HM Hs' Hn Hf0 Hft Hin Hfm).
    + destruct HM as (l' & -> & HM). inversion Hs as [|p l0 Hd Hs']; subst. destruct Hin as [<-|Hin].
      * pose proof (proj1 (Forall_forall _ _) Hd _ (maps_match_In E r l' m0 HM (nth_error_In _ _ Hn) Hf0)) as D. unfold iv_disjoint in *. lia.
      * exact (IH l' i m0 tok m HM Hs' Hn Hf0 Hft Hin Hfm).
Qed.

#[using="SP0_ok"] Lemma fog_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pi,$6:.Psz,$1.Pcs',$2>.P,(57.R8.R7.R6.R5.R4.)P,(3.(23.$2>.)(105.R8.R4.R3.)(82.$2>.R2.))(5.(57.R:.R3.R8.R7.R6.)(3.$1.(83.R3.)(83.R9.)))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model i sz cs' HC H. unfold node_fog in H.
  destruct (nth_error (a_maps cs) i) as [m|] eqn:Hn; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. split; [|reflexivity].
  apply andb_prop in Hc as [Hc Hx]. apply andb_prop in Hc as [Hc Hs2]. apply andb_prop in Hc as [Hnf Hs1].
  apply negb_true_iff in Hnf. apply Z.leb_le in Hs1. apply Z.ltb_lt in Hs2.
  destruct (xhi (kn cs) (am_len m)) as [h|] eqn:Hh; [|discriminate]. apply Z.leb_le in Hx.
  pose proof (xhi_sound SEGS E _ (kn cs) (am_len m) h (co_know _ _ _ _ _ HC) Hh) as Hh'.
  apply cs_ok_sub_filter; [apply cs_ok_with_maps; [exact HC | |] | |].
  - eapply list_set_nth_maps_match; [exact Hn | exact Hnf | lia | lia | exact (co_maps _ _ _ _ _ HC)].
  - intros m' Hin. destruct (In_list_set_nth _ _ _ _ Hin) as [->|Hin']; [left; reflexivity | right; exact Hin'].
  - intros t Ht. unfold fog_sub in Ht. apply filter_In in Ht as [Ht _]. exact Ht.
  - (* [comment removed for export] *)
    intros m' z t Hm' Hk' Hz Ht Hzt. cbn [with_maps a_maps a_sub] in Hm', Ht |- *.
    unfold fog_sub. apply filter_In. split; [exact Ht|]. destruct (split_lit (fst t)) as [tb tk] eqn:Hsp.
    destruct (xinside (kn cs) tb tk (snd t) (am_base m) 0 (am_len m)) eqn:Hxi; [exfalso | reflexivity].
    destruct (xinside_sound SEGS E _ (kn cs) tb tk (snd t) (am_base m) 0 (am_len m) (co_know _ _ _ _ _ HC) Hxi) as [X1 X2].
    unfold estart, elenZ in X1, X2. cbn [a_base a_off] in X1, X2. rewrite Z.add_0_r in X1, X2.
    pose proof (maps_match_In E _ _ m (co_maps _ _ _ _ _ HC) (nth_error_In _ _ Hn) Hnf) as Hden.
    pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ HC) _ Hden) as (_ & _ & _ & _ & HT & _). unfold amap_den in HT. cbn [fst snd] in HT.
    pose proof ATOP_facts as ATB. pose proof (u64_range (edenot E (am_base m))) as Rm. pose proof (u64_range (edenot E (snd t))) as Rt.
    assert (Ut : uE E (fst t) = bv_unsigned (edenot E tb) + tk).
    { unfold uE. rewrite (split_lit_denot E (fst t) tb tk Hsp). apply u64_lit. unfold ATOP in *. lia. }
    assert (Hfm' : is_fog m' = false) by (unfold is_fog; destruct Hk' as [<-|[<-|[]]]; reflexivity).
    pose proof (maps_match_set_nth_disjoint E (a_maps cs) _ i m (fog_token sz) m' (co_maps _ _ _ _ _ HC) (co_seps _ _ _ _ _ HC) Hn Hnf eq_refl Hm' Hfm') as D.
    unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. unfold in_tok in Hzt. unfold uE in *. lia.
Qed.

#[using="Type"] Lemma fognew_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pi,$6:.Psz,$1.Pcs',$2>.P,(57.R8.R7.R6.R5.R4.)P,(3.(23.$2>.)(106.R8.R4.R3.)(82.$2>.R2.))(5.(57.R:.R3.R8.R7.R6.)(3.$1.(83.R3.)(83.R9.)))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model i sz cs' HC H. unfold node_fognew in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. split; [|reflexivity].
  apply cs_ok_with_maps; [exact HC | apply list_insert_nth_maps_match; exact (co_maps _ _ _ _ _ HC) |].
  intros m' Hin. destruct (In_list_insert_nth _ _ _ _ Hin) as [->|Hin']; [left; reflexivity | right; exact Hin'].
Qed.

#[using="Type"] Lemma page_allowedb_app_l : forall l1 l2 p, page_allowedb l1 p = true -> page_allowedb (l1 ++ l2) p = true.
Proof. intros. unfold page_allowedb in *. rewrite existsb_app, H. reflexivity. Qed.
#[using="Type"] Lemma MInv_app_r : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pl1,(2?.(11.$1.$1.))Pl2,(2?.(11.$1.$1.))Pm,$56.P,(5?.R3.R1.)P,(2.(18.(8=.R2.)(8>.(31.(11.$1.$1.)R4.R3.)))(8?.(36.R2.)))(5?.(31.(11.$1.$1.)R5.R4.)R3.)")
(* [comment removed for export] *).
Proof.
  intros l1 l2 m [N1 N2 N3 N4 N5] Hb. constructor; try assumption.
  intros p Hp. apply page_allowedb_app_l. apply N3. exact Hp.
Qed.
#[using="HS XN XE XB SHADOW_ok KC"] Lemma allow1_cost : forall E b n nhi, bv_unsigned (edenot E n) <= nhi -> A_bytes (allow1 E (b, n)) <= vis_cost nhi.
Proof.
  intros E b n nhi Hn. unfold allow1, vis_cost. cbn [A_bytes fst snd]. unfold sh_lo, sh_hi. cbn [fst snd].
  pose proof (u64_range (edenot E b)) as Rb. pose proof (u64_range (edenot E n)) as Rn. unfold uE in *. pose proof SHADOW_ok as So. unfold shadow_ok in So.
  pose proof (pageup_pagedown_gap (bv_unsigned (edenot E b)) (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) ltac:(lia)) as G1.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  pose proof (pageup_pagedown_gap (shadow_off A + bv_unsigned (edenot E b) / 8)
                (shadow_off A + (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) / 8) ltac:(lia)) as G2.
  assert (G3 : (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) / 8 - bv_unsigned (edenot E b) / 8 <= nhi / 8 + 1) by lia.
  lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

#[using="HS XN XE XB SHADOW_ok KC"] Lemma ghost_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pb,$29.Pn,$29.Pcs',$2>.P,(57.R8.R7.R6.R5.R4.)P,(3.(23.$2>.)(107.VLIMIT,R8.R4.R3.)(82.$2>.R2.))(5.(57.R:.R3.R8.R7.R6.)(3.$1.(83.R3.)(83.R9.)))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model b n cs' HC H. unfold node_ghost in H.
  destruct (xhi (kn cs) n) as [nhi|] eqn:Hx; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. split; [|reflexivity].
  apply andb_prop in Hc as [Hc Hb]. apply Z.leb_le in Hb.
  pose proof (xhi_sound SEGS E _ (kn cs) n nhi (co_know _ _ _ _ _ HC) Hx) as Hn.
  set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _ _).
  assert (HMr : Mr E cs' model FULL = Mr E cs model FULL) by reflexivity.
  assert (HA : allowA E cs' = allowA E cs ++ allow_sh E (b, n)).
  { unfold allowA, cs'. cbn [a_vis a_ghost]. rewrite !flat_map_app. cbn [flat_map]. rewrite app_nil_r, app_assoc. reflexivity. }
  assert (HAB : A_bytes (allowA E cs') <= A_bytes (allowA E cs) + vis_cost nhi).
  { rewrite HA, A_bytes_app. pose proof (allow1_cost E b n nhi Hn). pose proof (allow_sh_le E (b, n)). lia. }
  pose proof (co_limit _ _ _ _ _ HC) as HL. pose proof (co_eager _ _ _ _ _ HC) as HE. pose proof (co_abytes _ _ _ _ _ HC) as HAB0.
  destruct HC; constructor; unfold cs'; rewrite ?HMr;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn] in *; try assumption.
  - fold cs'. lia.
  - fold cs'. rewrite HA. apply MInv_app_r; [exact co_minv0|]. rewrite <- HA. fold cs' in HAB. rewrite HL. lia.
  - intros a H1 H2 H3 H4 H5. apply (co_zero0 a H1 H2 H3 H4).
    fold cs' in H5. exact (in_ghost_app_false E cs cs' [(b, n)] _ eq_refl H5).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma seps_In_disjoint0 : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pl,(2?.(11.(12.&40.)(12.&40.)))Pp,(11.(12.&40.)(12.&40.))Pq,(11.(12.&40.)(12.&40.))P,(103.R3.)P,Piv,(11.(12.&40.)(12.&40.))P,(34.(11.(12.&40.)(12.&40.))R1.R5.)(1?.=(15.&40.(19.(12.&40.)(12.&40.)R2.)))P,(34.(11.(12.&40.)(12.&40.))R4.R5.)P,(34.(11.(12.&40.)(12.&40.))R4.R6.)P,(24.(3.(11.(12.&40.)(12.&40.))R6.R5.))(104.R7.R6.)")
(* [comment removed for export] *).
Proof.
  induction l as [|h t IH]; intros p q Hs Hpos Hp Hq Hne; [destruct Hp|].
  inversion Hs as [|h' t' Hf Ht]; subst.
  destruct Hp as [<-|Hp]; destruct Hq as [<-|Hq].
  - exfalso. exact (Hne eq_refl).
  - exact (proj1 (Forall_forall _ _) Hf q Hq).
  - pose proof (proj1 (Forall_forall _ _) Hf p Hp) as D. unfold iv_disjoint in *. lia.
  - apply IH; auto. intros iv Hiv. apply Hpos. right. exact Hiv.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma eager_range_lz_clear : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pm,$48.Plo,$1.Phi,$1.P,(57.R8.R7.R6.R5.R4.)P,(34.$48.R4.(8;.R8.))P,(3.$20.(4>.R5.)$33.)P,(34.$4?.(50.R6.)$108.)P,(2.(4;.(96.R<.R7.))R6.)P,(2.R6.(4<.(96.R=.R8.)))Pe,(11.(12.&40.)(12.&40.))P,(34.(11.(12.&40.)(12.&40.))R1.(3?.R;.))(1:.(2.(4<.R2.)R:.)(1:.(2.R9.(4;.R2.))(2.(4<.R2.)(4;.R2.))))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model m lo hi HC Hm Hf Hk Hlo Hhi e He.
  destruct (co_lzk _ _ _ _ _ HC e He) as (P & iv & Hiv & B1 & B2 & NB).
  pose proof (maps_match_In E _ _ m (co_maps _ _ _ _ _ HC) Hm Hf) as Hden.
  assert (Hne : iv <> amap_den E m) by (intros ->; apply NB; exists m; auto).
  pose proof (seps_In_disjoint0 _ iv (amap_den E m) (co_seps _ _ _ _ _ HC)
                (fun iv' H' => proj1 (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ HC) iv' H')) Hiv Hden Hne) as D.
  unfold iv_disjoint, zB, zE in *. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kzero_x_sound0 : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))Pallkn,(2?.$68.)Pk,(2?.$68.)Pb,$29.Poff,$1.Pn,$29.P,(64.VSEGS,R7.R6.R5.)P,(64.VSEGS,R8.R7.R5.)P,(3.$20.(109.R7.R6.R5.R4.R3.)$22.)(5.Pi,$1.P,(5.(2.=R1.)(1?.R1.(72.R;.R5.)))(3.(23.(12.&8.))A1.R;.(42.&40.(18.(70.R<.(71.R8.R7.))R2.))(82.(12.&8.)(42.&8.=)))(5.(2.=(70.R:.(71.R6.R5.)))(2.(18.(70.R:.(71.R6.R5.))(72.R:.R4.))(91.+2.+40.))))")
(* [comment removed for export] *).
Proof.
  intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  destruct K; try exact (IH Hrest H).
  lazymatch type of H with context [KZero ?za ?zl :: rest] => destruct za as [zb zk]; rename zl into zn end.
  cbn [kzero_x] in H.
  assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kzero_x allkn rest b off n) = true ->
                 (c1 || c2)%bool = true \/ kzero_x allkn rest b off n = true)
    by (intros [|] [|]; cbn; auto).
  apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hz]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hz, F1, F2, F4 |- *. cbn [a_base a_off] in Hz, F1, F2, F4 |- *.
  pose proof (u64_range (edenot E n)) as Hnr.
  assert (CORE : bv_unsigned (edenot E zb) + zk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E zb) + zk + elenZ E zn ->
                 (forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i)) = Some (Z_to_bv 8 0))
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
  { intros A0 B0. split; [|unfold elenZ in *; lia]. intros i Hi.
    replace (bv_unsigned (edenot E b) + off + i) with (bv_unsigned (edenot E zb) + zk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E zb) + zk) + i)) by lia.
    apply Hz. lia. }
  apply orb_prop in H as [H|H].
  - destruct (expr_eqb b zb && Z.leb zk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst zb.
    destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
    destruct (xlo allkn zn) as [zl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
    pose proof (xhi_sound SEGS E M allkn n nh Hall Hxh). pose proof (xlo_sound SEGS E M allkn zn zl Hall Hxl).
    apply CORE; unfold elenZ in *; lia.
  - pose proof (xinside_sound SEGS E M allkn b off n zb zk zn Hall H) as [A0 B0].
    unfold estart in A0, B0. cbn [a_base a_off] in A0, B0. apply CORE; lia.
Qed.

#[using="Type"] Lemma A_bytes_fm_split : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pf,P,(11.$29.$29.)$20.Pl,(2?.(11.$29.$29.))(3.$1.(8>.(10:.(11.$29.$29.)(11.$1.$1.)(10;.R3.)R1.))(18.(8>.(10:.(11.$29.$29.)(11.$1.$1.)(10;.R3.)(73.(11.$29.$29.)R2.R1.)))(8>.(10:.(11.$29.$29.)(11.$1.$1.)(10;.R3.)(73.(11.$29.$29.)Lp,(11.$29.$29.)(3;.A1.R3.R1.)R1.)))))")
(* [comment removed for export] *).
Proof.
  intros E f l. induction l as [|p l IH]; cbn [flat_map List.filter]; [reflexivity|].
  rewrite A_bytes_app, IH. destruct (f p); cbn [negb flat_map]; rewrite ?A_bytes_app; lia.
Qed.

#[using="Type"] Lemma A_bytes_allow1_nonneg : forall E p, 0 <= A_bytes (allow1 E p).
Proof.
  intros E p. unfold allow1. cbn [A_bytes fst snd].
  pose proof (pagedown_le (uE E (fst p))). pose proof (pageup_ge (uE E (fst p) + uE E (snd p))).
  pose proof (pagedown_le (sh_lo E p)). pose proof (pageup_ge (sh_hi E p)).
  pose proof (u64_range (edenot E (snd p))). unfold sh_lo, sh_hi, uE in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

#[using="Type"] Lemma vis_here_eq : forall b n p, vis_here b n p = true -> p = (b, n).
Proof.
  intros b n [pb pn] H. unfold vis_here in H. cbn [fst snd] in H. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. subst. reflexivity.
Qed.

#[using="Type"] Lemma A_bytes_fm_here : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pb,$29.Pn,$29.Pl,(2?.(11.$29.$29.))P,(1;.(11.$29.$29.)Lp,(11.$29.$29.)(3.(11.$29.$29.)R1.(27.$29.$29.R4.R3.))R1.)(3.$1.(8>.(10:.(11.$29.$29.)(11.$1.$1.)(10;.R5.)R2.))(=8.(86.(>0.(11.$29.$29.)R2.))(8>.(10;.R5.(27.$29.$29.R4.R3.)))))")
(* [comment removed for export] *).
Proof.
  intros E b n l H. induction l as [|p l IH]; [reflexivity|].
  apply Forall_cons_iff in H as [-> H]. cbn [flat_map length]. rewrite A_bytes_app, (IH H). rewrite Nat2Z.inj_succ. lia.
Qed.

#[using="SHADOW_ok"] Lemma unvis_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pb,$29.Pn,$29.Pcs',$2>.P,(57.R8.R7.R6.R5.R4.)P,(3.(23.$2>.)(10<.VA,R8.R4.R3.)(82.$2>.R2.))(5.(57.R:.R3.R8.R7.R6.)(3.$1.(83.R3.)(83.R9.)))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model b n cs' HC H. rewrite node_unvis_eq in H. (* [comment removed for export] *) unfold node_unvis_ref in H.
  destruct (split_lit b) as [bb bk] eqn:Hsp.
  destruct (shadow_of A (kn cs) b n) as [[sb sk] sn] eqn:Hsh.
  destruct (xhi (kn cs) b) as [bh|] eqn:Hbh; [|discriminate].
  destruct (xhi (kn cs) n) as [nh|] eqn:Hnh; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  match type of H with Some ?x = Some _ => assert (Hcs : cs' = x) by congruence end. subst cs'. clear H.
  split; [|reflexivity].
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  rename Hc into Hex.
  match goal with Hl : Z.leb 3 (ealign (kn cs) b) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hab end.
  match goal with Hl : Z.leb 3 (ealign (kn cs) n) = true |- _ => apply Z.leb_le in Hl; rename Hl into Han end.
  match goal with Hl : flat_x (kn cs) bb bk n = true |- _ => rename Hl into Hfl end.
  match goal with Hl : Z.leb (bh + nh) ATOPMAX = true |- _ => apply Z.leb_le in Hl; rename Hl into Hceil end.   (* [comment removed for export] *)
  match goal with Hl : flat_x (kn cs) sb sk sn = true |- _ => rename Hl into Hfls end.
  match goal with Hl : kzero_x (kn cs) (kn cs) sb sk sn = true |- _ => rename Hl into Hkz end.
  match goal with Hl : ranges_apart_x (kn cs) (ELit 0) (shadow_off A) (ELit BAND_LEN) bb bk n = true |- _ => rename Hl into Hbapart end.   (* [comment removed for export] *)
  match goal with Hl : Z.leb 12 (ealign (kn cs) b) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hpb end.   (* [comment removed for export] *)
  match goal with Hl : Z.leb 12 (ealign (kn cs) n) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hpn end.
  match goal with Hl : match find_containing _ _ _ _ _ _ with Some _ => true | None => _ end = true |- _ => rename Hl into Hfc end.
  pose proof (co_know _ _ _ _ _ HC) as HK.
  set (M := Mr E cs model FULL) in *.
  (* [comment removed for export] *)
  pose proof (xhi_sound SEGS E M (kn cs) b bh HK Hbh) as Hbh'. pose proof (xhi_sound SEGS E M (kn cs) n nh HK Hnh) as Hnh'.
  pose proof (flat_x_sound E M (kn cs) bb bk n HK Hfl) as (F1 & F2 & F3).
  pose proof (split_lit_denot E b bb bk Hsp) as Hbd.
  set (ub := bv_unsigned (edenot E b)) in *. set (un := bv_unsigned (edenot E n)) in *.
  assert (HB : estart E (SA bb bk) = ub).
  { unfold ub. rewrite Hbd. unfold estart. cbn [a_base a_off]. rewrite u64_lit; [reflexivity|]. unfold estart in F1, F2; cbn [a_base a_off] in F1, F2. lia. }
  rewrite HB in *.
  pose proof (shadow_of_val E M (kn cs) b n sb sk sn HK Hsh Hfls) as [HS0 HSn]. fold ub in HS0. fold un in HSn.
  pose proof SHADOW_ok as So; unfold shadow_ok in So. pose proof (u64_range (edenot E b)) as Rb. fold ub in Rb.
  assert (HSS : estart E (SA sb sk) = shadow_off A + ub / 8).
  { rewrite HS0. rewrite Z.mod_small; [lia|]. unfold ATOPMAX in Hceil.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  set (S := shadow_off A + ub / 8) in *.
  pose proof (ealign_sound SEGS E M (kn cs) b HK) as [Hrb0 Hdb]. pose proof (ealign_sound SEGS E M (kn cs) n HK) as [Hrn0 Hdn].
  fold ub in Hdb. fold un in Hdn.
  assert (D8b : (8 | ub)). { eapply Z.divide_trans; [|exact Hdb]. exists (2 ^ (ealign (kn cs) b - 3)). change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (D8n : (8 | un)). { eapply Z.divide_trans; [|exact Hdn]. exists (2 ^ (ealign (kn cs) n - 3)). change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (Hshhi : shadow_off A + (ub + un) / 8 = S + un / 8).
  { unfold S. destruct D8b as [qb ->]. destruct D8n as [qn ->].
    rewrite Z.div_mul, <- Z.mul_add_distr_r, !Z.div_mul by lia. lia. }
  pose proof (kzero_x_sound0 E M (kn cs) (kn cs) sb sk sn HK HK Hkz) as (Hzero & _ & _). rewrite HSS, HSn in Hzero.
  (* [comment removed for export] *)
  assert (GONE : Forall (fun p => p = (b, n)) (List.filter (vis_here b n) (a_vis cs))).
  { apply Forall_forall. intros p Hp. apply filter_In in Hp as [_ Hp]. apply vis_here_eq. exact Hp. }
  set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _ _).
  (* [comment removed for export] *)
  assert (ALLOW_sub : forall z, in_allow E cs' z = true -> in_allow E cs z = true).
  { intros z Hz. unfold in_allow, in_vis, in_sh in *. unfold cs' in Hz; cbn [a_vis] in Hz.
    apply orb_true_iff in Hz. apply orb_true_iff.
    destruct Hz as [Hz|Hz]; [left|right]; apply existsb_exists in Hz as [q [Hq Hzq]]; apply filter_In in Hq as [Hq _];
      apply existsb_exists; exists q; split; assumption. }
  assert (ALLOW_eq : forall z, ~ (ub <= z < ub + un) -> ~ (S <= z < S + un / 8) -> in_allow E cs' z = in_allow E cs z).
  { intros z Hz1 Hz2. destruct (in_allow E cs' z) eqn:Ha'; [symmetry; apply ALLOW_sub; exact Ha'|].
    destruct (in_allow E cs z) eqn:Ha; [|reflexivity]. exfalso.
    unfold in_allow, in_vis, in_sh in Ha, Ha'. unfold cs' in Ha'; cbn [a_vis] in Ha'.
    apply orb_false_iff in Ha' as [Hv' Hs'].
    assert (Q : forall q, In q (a_vis cs) -> vis_here b n q = false ->
                 In q (List.filter (fun p => negb (vis_here b n p)) (a_vis cs))).
    { intros q Hq Hh. apply filter_In. split; [exact Hq | rewrite Hh; reflexivity]. }
    apply orb_true_iff in Ha. destruct Ha as [Ha|Ha]; apply existsb_exists in Ha as [q [Hq Hzq]].
    - destruct (vis_here b n q) eqn:Hh.
      + apply vis_here_eq in Hh. subst q. cbn [fst snd] in Hzq. apply andb_prop in Hzq as [Z1 Z2].
        apply Z.leb_le in Z1. apply Z.ltb_lt in Z2. apply Hz1. unfold ub, un. unfold uE in Z1, Z2. lia.
      + assert (X : existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool
                      (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) = true).
        { apply existsb_exists. exists q. split; [apply Q; assumption | exact Hzq]. }
        rewrite X in Hv'. discriminate.
    - destruct (vis_here b n q) eqn:Hh.
      + apply vis_here_eq in Hh. subst q. apply andb_prop in Hzq as [Z1 Z2].
        apply Z.leb_le in Z1. apply Z.ltb_lt in Z2. unfold sh_lo, sh_hi in Z1, Z2. cbn [fst snd] in Z1, Z2.
        apply Hz2. unfold S. unfold ub, un in *. unfold uE in Z1, Z2. rewrite Hshhi in Z2. unfold S in Z2. lia.
      + assert (X : existsb (fun p => (sh_lo E p <=? z) && (z <? sh_hi E p))%bool
                      (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) = true).
        { apply existsb_exists. exists q. split; [apply Q; assumption | exact Hzq]. }
        rewrite X in Hs'. discriminate. }
  assert (HID_mono : forall a, hid E cs model a = true -> hid E cs' model a = true).
  { intros a Ha. unfold hid in *. apply orb_true_iff in Ha. apply orb_true_iff. destruct Ha as [Ha|Ha]; [left; exact Ha|right].
    apply negb_true_iff in Ha. apply negb_true_iff. destruct (vis E cs' model a) eqn:Hv; [|reflexivity].
    rewrite (vis_mono E cs' cs model a ALLOW_sub Hv) in Ha. discriminate. }
  assert (HID_eq : forall a, ~ (ub <= bv_unsigned a < ub + un) -> ~ (S <= bv_unsigned a < S + un / 8) ->
                   hid E cs' model a = hid E cs model a).
  { intros a H1 H2. unfold hid, vis. change (a_maps cs') with (a_maps cs). rewrite (ALLOW_eq _ H1 H2). reflexivity. }
  set (M' := Mr E cs' model FULL).
  assert (M_none : forall x, M x = None -> M' x = None).
  { intros x Hx. unfold M, M', Mr, mrestrict in *. destruct (hid E cs model x) eqn:Hh.
    - rewrite (HID_mono x Hh). reflexivity.
    - destruct (hid E cs' model x); [reflexivity | exact Hx]. }
  assert (M_eq : forall x, ~ (ub <= bv_unsigned x < ub + un) -> ~ (S <= bv_unsigned x < S + un / 8) -> M' x = M x).
  { intros x H1 H2. unfold M, M', Mr, mrestrict. rewrite (HID_eq x H1 H2). reflexivity. }
  (* [comment removed for export] *)
  set (k1 := kn_unfill (kn cs) bb bk n).
  set (Mmid := fun x : word => if ((ub <=? bv_unsigned x) && (bv_unsigned x <? ub + un))%bool then M' x else M x).
  assert (Mmid_out : forall x : word, bv_unsigned x < ub \/ ub + elenZ E n <= bv_unsigned x -> Mmid x = M x).
  { intros x Hx. unfold Mmid. unfold elenZ in Hx. fold un in Hx.
    destruct ((ub <=? bv_unsigned x) && (bv_unsigned x <? ub + un))%bool eqn:Hb; [|reflexivity].
    apply andb_prop in Hb as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2. lia. }
  assert (IMG : forall lo hi Mx, (forall x, M x = None -> Mx x = None) ->
            kentry_ok SEGS E M (KImg lo hi) -> kentry_ok SEGS E Mx (KImg lo hi)).
  { intros lo hi Mx Hn HKi. cbn [kentry_ok] in *. destruct HKi as (I1 & I2 & I3). split; [exact I1|]. split; [exact I2|].
    intros i Hi. apply Hn. apply I3. exact Hi. }
  assert (Mmid_none : forall x, M x = None -> Mmid x = None).
  { intros x Hx. unfold Mmid. destruct (_ && _)%bool; [apply M_none; exact Hx | exact Hx]. }
  assert (HK1 : know_ok SEGS E Mmid k1).
  { unfold k1, kn_unfill. cbv zeta. apply Forall_forall. intros K HinK. apply filter_In in HinK as [HinK Hkeep].
    pose proof (proj1 (Forall_forall _ _) HK K HinK) as HKK.
    apply orb_prop in Hkeep as [Himg|Hap].
    - destruct K; try discriminate. apply (IMG _ _ Mmid Mmid_none HKK).
    - rewrite kentry_apart_bp_eq in Hap. eapply kentry_apart_keep; [exact HK | exact HKK | exact Hap |]. rewrite HB. exact Mmid_out. }
  assert (HK2 : know_ok SEGS E M' (kn_unfill k1 sb sk sn)).
  { unfold kn_unfill. cbv zeta. apply Forall_forall. intros K HinK. apply filter_In in HinK as [HinK Hkeep].
    pose proof (proj1 (Forall_forall _ _) HK1 K HinK) as HKK.
    assert (HinK0 : In K (kn cs)) by (unfold k1, kn_unfill in HinK; apply filter_In in HinK as [HinK _]; exact HinK).
    apply orb_prop in Hkeep as [Himg|Hap].
    - destruct K; try discriminate. apply (IMG _ _ M' M_none). exact (proj1 (Forall_forall _ _) HK _ HinK0).
    - rewrite kentry_apart_bp_eq in Hap. eapply kentry_apart_keep; [exact HK1 | exact HKK | exact Hap |].
      rewrite HSS, HSn. intros x Hx. unfold Mmid.
      destruct ((ub <=? bv_unsigned x) && (bv_unsigned x <? ub + un))%bool eqn:Hb; [reflexivity|].
      apply M_eq; [|lia]. intros Hin. assert (X : ((ub <=? bv_unsigned x) && (bv_unsigned x <? ub + un))%bool = true); [|rewrite X in Hb; discriminate].
      apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  (* [comment removed for export] *)
  assert (HA : allowA E cs' = flat_map (allow1 E) (List.filter (fun p => negb (vis_here b n p)) (a_vis cs))
                               ++ flat_map (allow_sh E) (a_ghost cs) ++ allow_sh E (b, n)).
  { unfold allowA, cs'. cbn [a_vis a_ghost]. rewrite !flat_map_app. cbn [flat_map]. rewrite app_nil_r, app_assoc. reflexivity. }
  assert (HA0 : allowA E cs = flat_map (allow1 E) (a_vis cs) ++ flat_map (allow_sh E) (a_ghost cs)).
  { unfold allowA. reflexivity. }
  assert (HAB : A_bytes (allowA E cs') <= A_bytes (allowA E cs)).
  { rewrite HA, HA0, !A_bytes_app.
    rewrite (A_bytes_fm_split E (fun p => negb (vis_here b n p)) (a_vis cs)).
    assert (FF : List.filter (fun p => negb (negb (vis_here b n p))) (a_vis cs) = List.filter (vis_here b n) (a_vis cs)).
    { apply filter_ext. intros q. apply negb_involutive. }
    rewrite FF, (A_bytes_fm_here E b n _ GONE).
    assert (L1 : (1 <= length (List.filter (vis_here b n) (a_vis cs)))%nat).
    { apply existsb_exists in Hex as [q [Hq Hh]].
      assert (Hin : In q (List.filter (vis_here b n) (a_vis cs))) by (apply filter_In; split; assumption).
      destruct (List.filter (vis_here b n) (a_vis cs)); [destruct Hin | cbn; lia]. }
    pose proof (A_bytes_allow1_nonneg E (b, n)). pose proof (allow_sh_le E (b, n)). nia. }
  (* [comment removed for export] *)
  assert (OWN_LZ : forall pg : word, ub <= bv_unsigned pg -> bv_unsigned pg + 4096 <= ub + un -> page_in_ranges pg (m_vm_lazy model) = true -> False).
  { intros pg P1 P2 Hlz.
    unfold page_in_ranges in Hlz. apply existsb_exists in Hlz as [e [He Hb2]]. apply andb_prop in Hb2 as [Q1 Q2].
    apply Z.leb_le in Q1. apply Z.leb_le in Q2. unfold page_size in Q2.
    pose proof (co_lzk _ _ _ _ _ HC e He) as (Pe & _).
    destruct (find_containing (kn cs) (a_maps cs) [KRW; KNONE; KMIXED] bb bk n) as [m|] eqn:Hfind.
    - unfold find_containing in Hfind. apply find_some in Hfind as [Hmin Hmb]. apply andb_prop in Hmb as [Hkind Hins].
      apply andb_prop in Hkind as [Hnf Hkind]. apply negb_true_iff in Hnf. apply existsb_mkind_In in Hkind.
      pose proof (xinside_sound SEGS E M (kn cs) bb bk n (am_base m) 0 (am_len m) HK Hins) as [I1 I2]. rewrite HB in I1, I2.
      unfold estart, elenZ in I1, I2. cbn [a_base a_off] in I1, I2. fold un in I2.
      pose proof (eager_range_lz_clear E cs R FULL model m ub (ub + un) HC Hmin Hnf Hkind
                    ltac:(unfold zB, amap_den; cbn [fst]; lia) ltac:(unfold zE, amap_den; cbn [fst snd]; lia) e He) as D.
      unfold zB, zE in D. lia.
    - (* [comment removed for export] *)
      apply existsb_exists in Hfc as [t [Ht Hx]]. destruct (split_lit (fst t)) as [tb tk] eqn:Hts. apply andb_prop in Hx as [Hft Hx].
      pose proof (flat_x_sound E M (kn cs) tb tk (snd t) HK Hft) as (Ft1 & Ft2 & Ft3).
      pose proof (xinside_sound SEGS E M (kn cs) bb bk n tb tk (snd t) HK Hx) as [I1 I2]. rewrite HB in I1, I2. fold un in I2.
      pose proof (proj1 (Forall_forall _ _) (co_sub _ _ _ _ _ HC) t Ht) as (T0 & _ & _ & TL). cbv zeta in TL. cbv zeta in T0.
      pose proof (u_of_split E (fst t) tb tk Hts ltac:(clear - Ft1 Ft2 Ft3; unfold elenZ in *; lia)) as Ut.
      unfold uE in TL, T0. rewrite Ut in TL. unfold elenZ in I2. pose proof (TL e He) as D. unfold zB, zE in D. lia. }
  assert (PGAL : (4096 | ub) /\ (4096 | un)).
  { split; [eapply Z.divide_trans; [|exact Hdb] | eapply Z.divide_trans; [|exact Hdn]];
      [exists (2 ^ (ealign (kn cs) b - 12)) | exists (2 ^ (ealign (kn cs) n - 12))]; change 4096 with (2 ^ 12); rewrite <- Z.pow_add_r by lia; f_equal; lia. }
  assert (HPG : forall pg, page_allowedb (allowA E cs) pg = true -> page_in_ranges pg (m_vm_lazy model) = true -> page_allowedb (allowA E cs') pg = true).
  { intros pg Hp Hlz. unfold page_allowedb in *. apply existsb_exists in Hp as [iv [Hiv Hpg]]. apply existsb_exists.
    rewrite HA. rewrite HA0 in Hiv. apply in_app_iff in Hiv.
    destruct Hiv as [Hiv|Hiv]; [| exists iv; split; [apply in_app_iff; right; apply in_app_iff; left; exact Hiv| exact Hpg]].
    apply in_flat_map in Hiv as [q [Hq Hiv]]. destruct (vis_here b n q) eqn:Hh.
    - apply vis_here_eq in Hh. subst q. unfold allow1 in Hiv. destruct Hiv as [<-|[<-|[]]].
      + (* [comment removed for export] *) exfalso. cbn [fst snd] in Hpg. apply andb_prop in Hpg as [G1 G2]. apply Z.leb_le in G1. apply Z.leb_le in G2.
        unfold page_size in G2. unfold uE in G1, G2. fold ub un in G1. fold ub un in G2. fold ub in G2. fold un in G2.
        destruct PGAL as [[kb Ekb] [kn' Ekn]].
        assert (PD : pagedown ub = ub) by (unfold pagedown; rewrite Ekb at 1; rewrite Z_div_mult_full by lia; lia).
        assert (PU : pageup (ub + un) = ub + un).
        { unfold pageup. replace (ub + un + 4095) with (4095 + (kb + kn') * 4096) by lia. rewrite Z_div_plus_full by lia. change (4095 / 4096) with 0. lia. }
        rewrite PD in G1. rewrite PU in G2. exact (OWN_LZ pg G1 G2 Hlz).
      + exists (pagedown (sh_lo E (b, n)), pageup (sh_hi E (b, n))). split; [apply in_app_iff; right; apply in_app_iff; right; left; reflexivity| exact Hpg].
    - exists iv. split; [|exact Hpg]. apply in_app_iff. left. apply in_flat_map. exists q. split; [|exact Hiv]. apply filter_In. split; [exact Hq | rewrite Hh; reflexivity]. }
  pose proof (co_minv _ _ _ _ _ HC) as HMI. pose proof (co_abytes _ _ _ _ _ HC) as HAB0. pose proof (co_zero _ _ _ _ _ HC) as HZ0.
  destruct HC; constructor; unfold cs'; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn s_regs s_log s_know mk_ss]; try assumption; try reflexivity.
  all: fold cs'.
  all: match goal with
       | |- know_ok _ _ _ _ => change (Mr E cs' model FULL) with M'; exact HK2
       | |- A_bytes _ <= _ => lia
       | |- MInv _ _ => destruct HMI as [N1 N2 N3 N4 N5]; constructor; try assumption; [intros pg Hpg; apply HPG; [apply N3; exact Hpg | apply N4; exact Hpg] | lia]
       | |- _ => idtac
       end.
  (* [comment removed for export] *) intros a H1 H2 H3 H4 H5.
    (* [comment removed for export] *)
    pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HK Hbapart) as APB.
    unfold estart, elenZ in APB. cbn [a_base a_off edenot] in APB. rewrite (u64_lit 0) in APB by lia.
    rewrite (u64_lit BAND_LEN) in APB by (unfold BAND_LEN; lia). fold ub un in APB.
    assert (HBub : bv_unsigned (edenot E bb) + bk = ub) by (rewrite <- HB; reflexivity).
    rewrite ?HBub in APB.
    assert (NA : ~ (ub <= bv_unsigned a < ub + un)).
    { intros Hin. unfold in_ghost, in_ghostl in H5. unfold cs' in H5; cbn [a_ghost] in H5. rewrite existsb_app in H5.
      assert (X : ((uE E b <=? bv_unsigned a) && (bv_unsigned a <? uE E b + uE E n))%bool = true).
      { unfold uE. fold ub un. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
      cbn [existsb fst snd] in H5. rewrite X in H5. rewrite orb_true_r in H5. cbn [andb] in H5.
      assert (Y : in_band (bv_unsigned a) = false).
      { unfold in_band. apply andb_false_iff. destruct APB as [APB|APB]; [right; apply Z.ltb_ge | left; apply Z.leb_gt]; lia. }
      rewrite Y in H5. discriminate H5. }
    assert (H5' : in_ghost E cs (bv_unsigned a) = false) by (exact (in_ghost_app_false E cs cs' [(b, n)] _ eq_refl H5)).
    destruct (hid E cs model a) eqn:Hh.
    + exact (HZ0 a Hh H2 H3 H4 H5').
    + destruct (Z_le_dec S (bv_unsigned a)) as [L1|L1]; [destruct (Z_lt_dec (bv_unsigned a) (S + un / 8)) as [L2|L2]|].
      * (* [comment removed for export] *)
        pose proof (Hzero (bv_unsigned a - S) ltac:(lia)) as Z0.
        replace (S + (bv_unsigned a - S)) with (bv_unsigned a) in Z0 by lia. rewrite Z_to_bv_bv_unsigned in Z0.
        unfold M, Mr, mrestrict in Z0. rewrite Hh in Z0. exact Z0.
      * rewrite (HID_eq a NA ltac:(lia)) in H1. rewrite Hh in H1. discriminate.
      * rewrite (HID_eq a NA ltac:(lia)) in H1. rewrite Hh in H1. discriminate.
Qed.

#[using="Type"] Lemma vis_hereK_eq : forall b n p, vis_hereK b n p = vis_here b n p.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
#[using="HS XN XE XB SHADOW_ok KC"] Lemma unvis_keep_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pb,$29.Pn,$29.Pcs',$2>.P,(57.R8.R7.R6.R5.R4.)P,(3.(23.$2>.)(10=.VA,R8.R4.R3.)(82.$2>.R2.))(5.(57.R:.R3.R8.R7.R6.)(5.(3.$1.(83.R3.)(83.R9.))(5.(3.(2?.$48.)(8;.R3.)(8;.R9.))(5.(3.(2?.(11.$29.$29.))(?4.R3.)(?4.R9.))(5.(3.(2?.$29.)(61.(<4.R3.))(61.(<4.R9.)))(3.$6:.(:4.R3.)(:4.R9.)))))))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model b n cs' HC H. unfold node_unvis_keep in H.
  assert (VH : vis_hereK b n = vis_here b n) by reflexivity. rewrite VH in H. clear VH.
  destruct (split_lit b) as [bb bk] eqn:Hsp.
  destruct (shadow_of A (kn cs) b n) as [[sb sk] sn] eqn:Hsh.
  destruct (xhi (kn cs) b) as [bh|] eqn:Hbh; [|discriminate].
  destruct (xhi (kn cs) n) as [nh|] eqn:Hnh; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  match type of H with Some ?x = Some _ => assert (Hcs : cs' = x) by congruence end. subst cs'. clear H.
  split; [|repeat split; reflexivity].
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  rename Hc into Hex.
  match goal with Hl : Z.leb 3 (ealign (kn cs) b) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hab end.
  match goal with Hl : Z.leb 3 (ealign (kn cs) n) = true |- _ => apply Z.leb_le in Hl; rename Hl into Han end.
  match goal with Hl : flat_x (kn cs) bb bk n = true |- _ => rename Hl into Hfl end.
  match goal with Hl : Z.leb (bh + nh) ATOPMAX = true |- _ => apply Z.leb_le in Hl; rename Hl into Hceil end.   (* [comment removed for export] *)
  match goal with Hl : flat_x (kn cs) sb sk sn = true |- _ => rename Hl into Hfls end.
  match goal with Hl : kzero_x (kn cs) (kn cs) sb sk sn = true |- _ => rename Hl into Hkz end.
  match goal with Hl : ranges_apart_x (kn cs) (ELit 0) (shadow_off A) (ELit BAND_LEN) bb bk n = true |- _ => rename Hl into Hbapart end.   (* [comment removed for export] *)
  match goal with Hl : Z.leb 12 (ealign (kn cs) b) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hpb end.   (* [comment removed for export] *)
  match goal with Hl : Z.leb 12 (ealign (kn cs) n) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hpn end.
  match goal with Hl : match find_containing _ _ _ _ _ _ with Some _ => true | None => false end = true |- _ => rename Hl into Hfc end.
  pose proof (co_know _ _ _ _ _ HC) as HK.
  set (M := Mr E cs model FULL) in *.
  (* [comment removed for export] *)
  pose proof (xhi_sound SEGS E M (kn cs) b bh HK Hbh) as Hbh'. pose proof (xhi_sound SEGS E M (kn cs) n nh HK Hnh) as Hnh'.
  pose proof (flat_x_sound E M (kn cs) bb bk n HK Hfl) as (F1 & F2 & F3).
  pose proof (split_lit_denot E b bb bk Hsp) as Hbd.
  set (ub := bv_unsigned (edenot E b)) in *. set (un := bv_unsigned (edenot E n)) in *.
  assert (HB : estart E (SA bb bk) = ub).
  { unfold ub. rewrite Hbd. unfold estart. cbn [a_base a_off]. rewrite u64_lit; [reflexivity|]. unfold estart in F1, F2; cbn [a_base a_off] in F1, F2. lia. }
  rewrite HB in *.
  pose proof (shadow_of_val E M (kn cs) b n sb sk sn HK Hsh Hfls) as [HS0 HSn]. fold ub in HS0. fold un in HSn.
  pose proof SHADOW_ok as So; unfold shadow_ok in So. pose proof (u64_range (edenot E b)) as Rb. fold ub in Rb.
  assert (HSS : estart E (SA sb sk) = shadow_off A + ub / 8).
  { rewrite HS0. rewrite Z.mod_small; [lia|]. unfold ATOPMAX in Hceil.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  set (S := shadow_off A + ub / 8) in *.
  pose proof (ealign_sound SEGS E M (kn cs) b HK) as [Hrb0 Hdb]. pose proof (ealign_sound SEGS E M (kn cs) n HK) as [Hrn0 Hdn].
  fold ub in Hdb. fold un in Hdn.
  assert (D8b : (8 | ub)). { eapply Z.divide_trans; [|exact Hdb]. exists (2 ^ (ealign (kn cs) b - 3)). change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (D8n : (8 | un)). { eapply Z.divide_trans; [|exact Hdn]. exists (2 ^ (ealign (kn cs) n - 3)). change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (Hshhi : shadow_off A + (ub + un) / 8 = S + un / 8).
  { unfold S. destruct D8b as [qb ->]. destruct D8n as [qn ->].
    rewrite Z.div_mul, <- Z.mul_add_distr_r, !Z.div_mul by lia. lia. }
  pose proof (kzero_x_sound0 E M (kn cs) (kn cs) sb sk sn HK HK Hkz) as (Hzero & _ & _). rewrite HSS, HSn in Hzero.
  (* [comment removed for export] *)
  assert (GONE : Forall (fun p => p = (b, n)) (List.filter (vis_here b n) (a_vis cs))).
  { apply Forall_forall. intros p Hp. apply filter_In in Hp as [_ Hp]. apply vis_here_eq. exact Hp. }
  set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _ _).
  (* [comment removed for export] *)
  assert (OWN_LZ : forall pg : word, ub <= bv_unsigned pg -> bv_unsigned pg + 4096 <= ub + un -> page_in_ranges pg (m_vm_lazy model) = true -> False).
  { intros pg P1 P2 Hlz.
    unfold page_in_ranges in Hlz. apply existsb_exists in Hlz as [e [He Hb2]]. apply andb_prop in Hb2 as [Q1 Q2].
    apply Z.leb_le in Q1. apply Z.leb_le in Q2. unfold page_size in Q2.
    pose proof (co_lzk _ _ _ _ _ HC e He) as (Pe & _).
    destruct (find_containing (kn cs) (a_maps cs) [KRW; KNONE; KMIXED] bb bk n) as [m|] eqn:Hfind.
    - unfold find_containing in Hfind. apply find_some in Hfind as [Hmin Hmb]. apply andb_prop in Hmb as [Hkind Hins].
      apply andb_prop in Hkind as [Hnf Hkind]. apply negb_true_iff in Hnf. apply existsb_mkind_In in Hkind.
      pose proof (xinside_sound SEGS E M (kn cs) bb bk n (am_base m) 0 (am_len m) HK Hins) as [I1 I2]. rewrite HB in I1, I2.
      unfold estart, elenZ in I1, I2. cbn [a_base a_off] in I1, I2. fold un in I2.
      pose proof (eager_range_lz_clear E cs R FULL model m ub (ub + un) HC Hmin Hnf Hkind
                    ltac:(unfold zB, amap_den; cbn [fst]; lia) ltac:(unfold zE, amap_den; cbn [fst snd]; lia) e He) as D.
      unfold zB, zE in D. lia.
    - discriminate Hfc. }
  assert (PGAL : (4096 | ub) /\ (4096 | un)).
  { split; [eapply Z.divide_trans; [|exact Hdb] | eapply Z.divide_trans; [|exact Hdn]];
      [exists (2 ^ (ealign (kn cs) b - 12)) | exists (2 ^ (ealign (kn cs) n - 12))]; change 4096 with (2 ^ 12); rewrite <- Z.pow_add_r by lia; f_equal; lia. }
  (* [comment removed for export] *)
  assert (HID_app : forall a : word, ub <= bv_unsigned a < ub + un -> forall csx, a_maps csx = a_maps cs -> hid E csx model a = hid E cs model a).
  { intros a Ha csx _. unfold hid, vis.
    assert (NL : page_in_ranges (page_base a) (m_vm_lazy model) = false).
    { destruct (page_in_ranges (page_base a) (m_vm_lazy model)) eqn:Hlz; [exfalso | reflexivity].
      pose proof (page_base_le a) as (P1 & P2 & P3). destruct PGAL as [[kb Ekb] [kn' Ekn]].
      apply (OWN_LZ (page_base a)); [| | exact Hlz].
      - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      - lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    rewrite NL. cbn [negb orb]. reflexivity. }
  (* [comment removed for export] *)
  assert (ALLOW_sub : forall z, in_allow E cs' z = true -> in_allow E cs z = true).
  { intros z Hz. unfold in_allow, in_vis, in_sh in *. unfold cs' in Hz; cbn [a_vis] in Hz.
    apply orb_true_iff in Hz. apply orb_true_iff.
    destruct Hz as [Hz|Hz]; [left|right]; apply existsb_exists in Hz as [q [Hq Hzq]]; apply filter_In in Hq as [Hq _];
      apply existsb_exists; exists q; split; assumption. }
  assert (ALLOW_eq : forall z, ~ (ub <= z < ub + un) -> ~ (S <= z < S + un / 8) -> in_allow E cs' z = in_allow E cs z).
  { intros z Hz1 Hz2. destruct (in_allow E cs' z) eqn:Ha'; [symmetry; apply ALLOW_sub; exact Ha'|].
    destruct (in_allow E cs z) eqn:Ha; [|reflexivity]. exfalso.
    unfold in_allow, in_vis, in_sh in Ha, Ha'. unfold cs' in Ha'; cbn [a_vis] in Ha'.
    apply orb_false_iff in Ha' as [Hv' Hs'].
    assert (Q : forall q, In q (a_vis cs) -> vis_here b n q = false ->
                 In q (List.filter (fun p => negb (vis_here b n p)) (a_vis cs))).
    { intros q Hq Hh. apply filter_In. split; [exact Hq | rewrite Hh; reflexivity]. }
    apply orb_true_iff in Ha. destruct Ha as [Ha|Ha]; apply existsb_exists in Ha as [q [Hq Hzq]].
    - destruct (vis_here b n q) eqn:Hh.
      + apply vis_here_eq in Hh. subst q. cbn [fst snd] in Hzq. apply andb_prop in Hzq as [Z1 Z2].
        apply Z.leb_le in Z1. apply Z.ltb_lt in Z2. apply Hz1. unfold ub, un. unfold uE in Z1, Z2. lia.
      + assert (X : existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool
                      (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) = true).
        { apply existsb_exists. exists q. split; [apply Q; assumption | exact Hzq]. }
        rewrite X in Hv'. discriminate.
    - destruct (vis_here b n q) eqn:Hh.
      + apply vis_here_eq in Hh. subst q. apply andb_prop in Hzq as [Z1 Z2].
        apply Z.leb_le in Z1. apply Z.ltb_lt in Z2. unfold sh_lo, sh_hi in Z1, Z2. cbn [fst snd] in Z1, Z2.
        apply Hz2. unfold S. unfold ub, un in *. unfold uE in Z1, Z2. rewrite Hshhi in Z2. unfold S in Z2. lia.
      + assert (X : existsb (fun p => (sh_lo E p <=? z) && (z <? sh_hi E p))%bool
                      (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) = true).
        { apply existsb_exists. exists q. split; [apply Q; assumption | exact Hzq]. }
        rewrite X in Hs'. discriminate. }
  assert (HID_mono : forall a, hid E cs model a = true -> hid E cs' model a = true).
  { intros a Ha. unfold hid in *. apply orb_true_iff in Ha. apply orb_true_iff. destruct Ha as [Ha|Ha]; [left; exact Ha|right].
    apply negb_true_iff in Ha. apply negb_true_iff. destruct (vis E cs' model a) eqn:Hv; [|reflexivity].
    rewrite (vis_mono E cs' cs model a ALLOW_sub Hv) in Ha. discriminate. }
  assert (HID_eq0 : forall a, ~ (ub <= bv_unsigned a < ub + un) -> ~ (S <= bv_unsigned a < S + un / 8) ->
                   hid E cs' model a = hid E cs model a).
  { intros a H1 H2. unfold hid, vis. change (a_maps cs') with (a_maps cs). rewrite (ALLOW_eq _ H1 H2). reflexivity. }
  assert (HID_eq : forall a, ~ (S <= bv_unsigned a < S + un / 8) -> hid E cs' model a = hid E cs model a).
  { intros a H2. destruct (Z_le_dec ub (bv_unsigned a)) as [L1|L1]; [destruct (Z_lt_dec (bv_unsigned a) (ub + un)) as [L2|L2]|].
    - exact (HID_app a (conj L1 L2) cs' eq_refl).
    - apply HID_eq0; [lia | exact H2].
    - apply HID_eq0; [lia | exact H2]. }
  set (M' := Mr E cs' model FULL).
  assert (M_none : forall x, M x = None -> M' x = None).
  { intros x Hx. unfold M, M', Mr, mrestrict in *. destruct (hid E cs model x) eqn:Hh.
    - rewrite (HID_mono x Hh). reflexivity.
    - destruct (hid E cs' model x); [reflexivity | exact Hx]. }
  assert (M_eq : forall x, ~ (S <= bv_unsigned x < S + un / 8) -> M' x = M x).
  { intros x H2. unfold M, M', Mr, mrestrict. rewrite (HID_eq x H2). reflexivity. }
  (* [comment removed for export] *)
  assert (IMG : forall lo hi Mx, (forall x, M x = None -> Mx x = None) ->
            kentry_ok SEGS E M (KImg lo hi) -> kentry_ok SEGS E Mx (KImg lo hi)).
  { intros lo hi Mx Hn HKi. cbn [kentry_ok] in *. destruct HKi as (I1 & I2 & I3). split; [exact I1|]. split; [exact I2|].
    intros i Hi. apply Hn. apply I3. exact Hi. }
  assert (HK2 : know_ok SEGS E M' (kn_unfill (kn cs) sb sk sn)).
  { unfold kn_unfill. cbv zeta. apply Forall_forall. intros K HinK. apply filter_In in HinK as [HinK Hkeep].
    pose proof (proj1 (Forall_forall _ _) HK K HinK) as HKK.
    apply orb_prop in Hkeep as [Himg|Hap].
    - destruct K; try discriminate. apply (IMG _ _ M' M_none). exact HKK.
    - rewrite kentry_apart_bp_eq in Hap. eapply kentry_apart_keep; [exact HK | exact HKK | exact Hap |].
      rewrite HSS, HSn. intros x Hx. apply M_eq. lia. }
  (* [comment removed for export] *)
  assert (HA : allowA E cs' = flat_map (allow1 E) (List.filter (fun p => negb (vis_here b n p)) (a_vis cs))
                               ++ flat_map (allow_sh E) (a_ghost cs) ++ allow_sh E (b, n)).
  { unfold allowA, cs'. cbn [a_vis a_ghost]. rewrite !flat_map_app. cbn [flat_map]. rewrite app_nil_r, app_assoc. reflexivity. }
  assert (HA0 : allowA E cs = flat_map (allow1 E) (a_vis cs) ++ flat_map (allow_sh E) (a_ghost cs)).
  { unfold allowA. reflexivity. }
  assert (HAB : A_bytes (allowA E cs') <= A_bytes (allowA E cs)).
  { rewrite HA, HA0, !A_bytes_app.
    rewrite (A_bytes_fm_split E (fun p => negb (vis_here b n p)) (a_vis cs)).
    assert (FF : List.filter (fun p => negb (negb (vis_here b n p))) (a_vis cs) = List.filter (vis_here b n) (a_vis cs)).
    { apply filter_ext. intros q. apply negb_involutive. }
    rewrite FF, (A_bytes_fm_here E b n _ GONE).
    assert (L1 : (1 <= length (List.filter (vis_here b n) (a_vis cs)))%nat).
    { apply existsb_exists in Hex as [q [Hq Hh]].
      assert (Hin : In q (List.filter (vis_here b n) (a_vis cs))) by (apply filter_In; split; assumption).
      destruct (List.filter (vis_here b n) (a_vis cs)); [destruct Hin | cbn; lia]. }
    pose proof (A_bytes_allow1_nonneg E (b, n)). pose proof (allow_sh_le E (b, n)). nia. }
  assert (HPG : forall pg, page_allowedb (allowA E cs) pg = true -> page_in_ranges pg (m_vm_lazy model) = true -> page_allowedb (allowA E cs') pg = true).
  { intros pg Hp Hlz. unfold page_allowedb in *. apply existsb_exists in Hp as [iv [Hiv Hpg]]. apply existsb_exists.
    rewrite HA. rewrite HA0 in Hiv. apply in_app_iff in Hiv.
    destruct Hiv as [Hiv|Hiv]; [| exists iv; split; [apply in_app_iff; right; apply in_app_iff; left; exact Hiv| exact Hpg]].
    apply in_flat_map in Hiv as [q [Hq Hiv]]. destruct (vis_here b n q) eqn:Hh.
    - apply vis_here_eq in Hh. subst q. unfold allow1 in Hiv. destruct Hiv as [<-|[<-|[]]].
      + (* [comment removed for export] *) exfalso. cbn [fst snd] in Hpg. apply andb_prop in Hpg as [G1 G2]. apply Z.leb_le in G1. apply Z.leb_le in G2.
        unfold page_size in G2. unfold uE in G1, G2. fold ub un in G1. fold ub un in G2. fold ub in G2. fold un in G2.
        destruct PGAL as [[kb Ekb] [kn' Ekn]].
        assert (PD : pagedown ub = ub) by (unfold pagedown; rewrite Ekb at 1; rewrite Z_div_mult_full by lia; lia).
        assert (PU : pageup (ub + un) = ub + un).
        { unfold pageup. replace (ub + un + 4095) with (4095 + (kb + kn') * 4096) by lia. rewrite Z_div_plus_full by lia. change (4095 / 4096) with 0. lia. }
        rewrite PD in G1. rewrite PU in G2. exact (OWN_LZ pg G1 G2 Hlz).
      + exists (pagedown (sh_lo E (b, n)), pageup (sh_hi E (b, n))). split; [apply in_app_iff; right; apply in_app_iff; right; left; reflexivity| exact Hpg].
    - exists iv. split; [|exact Hpg]. apply in_app_iff. left. apply in_flat_map. exists q. split; [|exact Hiv]. apply filter_In. split; [exact Hq | rewrite Hh; reflexivity]. }
  pose proof (co_minv _ _ _ _ _ HC) as HMI. pose proof (co_abytes _ _ _ _ _ HC) as HAB0. pose proof (co_zero _ _ _ _ _ HC) as HZ0.
  destruct HC; constructor; unfold cs'; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn s_regs s_log s_know mk_ss]; try assumption; try reflexivity.
  all: fold cs'.
  all: match goal with
       | |- know_ok _ _ _ _ => change (Mr E cs' model FULL) with M'; exact HK2
       | |- A_bytes _ <= _ => lia
       | |- MInv _ _ => destruct HMI as [N1 N2 N3 N4 N5]; constructor; try assumption; [intros pg Hpg; apply HPG; [apply N3; exact Hpg | apply N4; exact Hpg] | lia]
       | |- _ => idtac
       end.
  (* [comment removed for export] *) intros a H1 H2 H3 H4 H5.
    (* [comment removed for export] *)
    pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HK Hbapart) as APB.
    unfold estart, elenZ in APB. cbn [a_base a_off edenot] in APB. rewrite (u64_lit 0) in APB by lia.
    rewrite (u64_lit BAND_LEN) in APB by (unfold BAND_LEN; lia). fold ub un in APB.
    assert (HBub : bv_unsigned (edenot E bb) + bk = ub) by (rewrite <- HB; reflexivity).
    rewrite ?HBub in APB.
    assert (NA : ~ (ub <= bv_unsigned a < ub + un)).
    { intros Hin. unfold in_ghost, in_ghostl in H5. unfold cs' in H5; cbn [a_ghost] in H5. rewrite existsb_app in H5.
      assert (X : ((uE E b <=? bv_unsigned a) && (bv_unsigned a <? uE E b + uE E n))%bool = true).
      { unfold uE. fold ub un. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
      cbn [existsb fst snd] in H5. rewrite X in H5. rewrite orb_true_r in H5. cbn [andb] in H5.
      assert (Y : in_band (bv_unsigned a) = false).
      { unfold in_band. apply andb_false_iff. destruct APB as [APB|APB]; [right; apply Z.ltb_ge | left; apply Z.leb_gt]; lia. }
      rewrite Y in H5. discriminate H5. }
    assert (H5' : in_ghost E cs (bv_unsigned a) = false) by (exact (in_ghost_app_false E cs cs' [(b, n)] _ eq_refl H5)).
    destruct (hid E cs model a) eqn:Hh.
    + exact (HZ0 a Hh H2 H3 H4 H5').
    + destruct (Z_le_dec S (bv_unsigned a)) as [L1|L1]; [destruct (Z_lt_dec (bv_unsigned a) (S + un / 8)) as [L2|L2]|].
      * (* [comment removed for export] *)
        pose proof (Hzero (bv_unsigned a - S) ltac:(lia)) as Z0.
        replace (S + (bv_unsigned a - S)) with (bv_unsigned a) in Z0 by lia. rewrite Z_to_bv_bv_unsigned in Z0.
        unfold M, Mr, mrestrict in Z0. rewrite Hh in Z0. exact Z0.
      * rewrite (HID_eq a ltac:(lia)) in H1. rewrite Hh in H1. discriminate.
      * rewrite (HID_eq a ltac:(lia)) in H1. rewrite Hh in H1. discriminate.
Qed.

#[using="HS XN XE XB SHADOW_ok KC"] Lemma unvis_all_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pl,(2?.(11.$29.$29.))Pcs,$2>.Pcs',$2>.P,(57.R7.R2.R6.R5.R4.)P,(3.(23.$2>.)(10>.VA,R4.R3.)(82.$2>.R2.))(5.(57.R9.R3.R8.R7.R6.)(5.(3.$1.(83.R3.)(83.R4.))(5.(3.(2?.$48.)(8;.R3.)(8;.R4.))(5.(3.(2?.(11.$29.$29.))(?4.R3.)(?4.R4.))(5.(3.(2?.$29.)(61.(<4.R3.))(61.(<4.R4.)))(3.$6:.(:4.R3.)(:4.R4.)))))))")
(* [comment removed for export] *).
Proof.
  intros E R FULL model l. induction l as [|p r IH]; intros cs cs' HC H; cbn [unvis_all] in H.
  - injection H as <-. split; [exact HC | repeat split; reflexivity].
  - destruct (node_unvis_keep A cs (fst p) (snd p)) as [cs1|] eqn:H1; [|discriminate].
    destruct (unvis_keep_sound E cs R FULL model (fst p) (snd p) cs1 HC H1) as (HC1 & P1 & M1 & S1 & R1 & N1).
    destruct (IH cs1 cs' HC1 H) as (HC2 & P2 & M2 & S2 & R2 & N2).
    split; [exact HC2 | repeat split; congruence].
Qed.

#[using="argH_agree SINV_agree"] Lemma havocbrk_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Plo,$1.Phi,$1.Pcs',$2>.P,(57.R8.R7.R6.R5.R4.)P,(3.(23.$2>.)(10?.Vnx0,R8.R4.R3.)(82.$2>.R2.))(4:.$0.LE',$0.(5.(5.(9;.Vnx0,R;.R1.)(9;.(:4.R:.)R;.R1.))(5.(57.R1.R4.R9.R8.R7.)(3.$1.(83.R4.)(83.R:.)))))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model lo hi cs' HC H. unfold node_havocbrk in H.
  destruct (xlo (kn cs) (a_brk cs)) as [l|] eqn:Hl; [|discriminate].
  destruct (xhi (kn cs) (a_brk cs)) as [h|] eqn:Hh; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-.
  apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Hf H1]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (xlo_sound SEGS E _ (kn cs) (a_brk cs) l (co_know _ _ _ _ _ HC) Hl) as L1.
  pose proof (xhi_sound SEGS E _ (kn cs) (a_brk cs) h (co_know _ _ _ _ _ HC) Hh) as L2.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (v := nxt cs). set (E' := ext1 E v (vm_brk (m_vmmaps model))).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC'.
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  assert (Hv : edenot E' (EVar v) = vm_brk (m_vmmaps model)) by (cbn [edenot]; unfold E'; apply ext1_at).
  pose proof (co_brk _ _ _ _ _ HC) as HB0.
  set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _ _).
  assert (HMr : Mr E' cs' model FULL = Mr E' cs model FULL) by reflexivity.
  assert (HA : allowA E' cs' = allowA E' cs) by reflexivity.
  destruct HC'; constructor; unfold cs'; rewrite ?HMr, ?HA;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next] in *;
    try assumption; try reflexivity.
  - (* [comment removed for export] *) constructor; [|exact co_know0]. cbn [kentry_ok]. rewrite Hv, HB0. lia.
  - (* [comment removed for export] *) symmetry. exact Hv.
Qed.

(* [comment removed for export] *)
#[using="argH_agree SINV_agree"] Lemma intro_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Plo,$1.Phi,$1.Pcs',$2>.P,(57.R8.R7.R6.R5.R4.)P,(3.(23.$2>.)(110.Vnx0,R8.R4.R3.)(82.$2>.R2.))(4:.$0.LE',$0.(5.(5.(9;.Vnx0,R;.R1.)(9;.(:4.R:.)R;.R1.))(5.(57.R1.R4.R9.R8.R7.)(3.$1.(83.R4.)(83.R:.)))))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model lo hi cs' HC H. unfold node_intro in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-.
  apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Hf H1].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (v := nxt cs). set (E' := ext1 E v (Z_to_bv 64 lo)).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC'.
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  assert (Hv : bv_unsigned (edenot E' (EVar v)) = lo).
  { cbn [edenot]. unfold E'. rewrite ext1_at. unfold two64 in H3. apply u_small. lia. }
  set (cs' := with_ss _ _).
  assert (HMr : Mr E' cs' model FULL = Mr E' cs model FULL) by reflexivity.
  assert (HA : allowA E' cs' = allowA E' cs) by reflexivity.
  destruct HC'; constructor; unfold cs'; rewrite ?HMr, ?HA;
    cbn [with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next] in *;
    try assumption; try reflexivity.
  - (* [comment removed for export] *) constructor; [|exact co_know0]. cbn [kentry_ok]. rewrite Hv. lia.
Qed.

(* [comment removed for export] *)
Section Rename.
  Variable m : list (nat * nat).
  Variables fw bw : list (option nat).
  Hypothesis Hfw : mk_fwd m = Some fw.
  Hypothesis Hbw : mk_bwd m = Some bw.

  #[using="Type"] Lemma mk_fwd_spec_gen : forall m0 t, mk_fwd m0 = Some t -> forall s d, nt_get t s = Some d <-> In (s, d) m0.
  Proof.
    induction m0 as [|[s0 d0] rest IH]; intros t H s d; cbn [mk_fwd] in H.
    - injection H as <-. unfold nt_get. cbn. split; [destruct s; discriminate | tauto].
    - destruct (mk_fwd rest) as [t0|] eqn:E0; [|discriminate].
      destruct (nt_get t0 s0) eqn:Eg; [discriminate|]. injection H as <-.
      rewrite nt_get_set. specialize (IH t0 eq_refl).
      destruct (Nat.eqb_spec s s0) as [->|NE].
      + split.
        * intros X. injection X as <-. left. reflexivity.
        * intros [X|X]; [congruence|]. apply IH in X. congruence.
      + rewrite IH. cbn. split; [tauto|]. intros [X|X]; [congruence|exact X].
  Qed.
  #[using="Type"] Lemma mk_bwd_spec_gen : forall m0 t, mk_bwd m0 = Some t -> forall s d, nt_get t d = Some s <-> In (s, d) m0.
  Proof.
    induction m0 as [|[s0 d0] rest IH]; intros t H s d; cbn [mk_bwd] in H.
    - injection H as <-. unfold nt_get. cbn. split; [destruct d; discriminate | tauto].
    - destruct (mk_bwd rest) as [t0|] eqn:E0; [|discriminate].
      destruct (nt_get t0 d0) eqn:Eg; [discriminate|]. injection H as <-.
      rewrite nt_get_set. specialize (IH t0 eq_refl).
      destruct (Nat.eqb_spec d d0) as [->|NE].
      + split.
        * intros X. injection X as <-. left. reflexivity.
        * intros [X|X]; [congruence|]. apply IH in X. congruence.
      + rewrite IH. cbn. split; [tauto|]. intros [X|X]; [congruence|exact X].
  Qed.
  #[using="Hfw"] Lemma fw_in : forall s d, nt_get fw s = Some d <-> In (s, d) m.
  Proof. exact (mk_fwd_spec_gen m fw Hfw). Qed.
  #[using="Hbw"] Lemma bw_in : forall s d, nt_get bw d = Some s <-> In (s, d) m.
  Proof. exact (mk_bwd_spec_gen m bw Hbw). Qed.

  Definition ren_env (E : env) : env :=
    Env (fun w => match nt_get bw w with Some s => ev E s | None => ev E w end) (eb E).
  Definition ren_ok (v : nat) : bool :=
    match nt_get fw v with Some _ => true | None => match nt_get bw v with Some _ => false | None => true end end.

  #[using="m Hfw Hbw"] Lemma edenot_rename : forall E e, evars_all ren_ok e = true -> edenot (ren_env E) (erename fw e) = edenot E e.
  Proof.
    intros E e. induction e; cbn [evars_all erename edenot]; intros H;
      try reflexivity;
      try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity);
      try (rewrite (IHe H); reflexivity).
    unfold ren_ok in H. destruct (nt_get fw n) as [d|] eqn:Ef.
    - cbn [edenot ren_env ev]. destruct (nt_get bw d) as [s|] eqn:Eb.
      + apply bw_in in Eb. apply fw_in in Ef. pose proof (proj2 (fw_in _ _) Eb) as Ef'.
        assert (s = n) by (apply bw_in in Eb; apply bw_in in Ef; congruence). subst s. reflexivity.
      + exfalso. apply fw_in in Ef. apply (proj2 (bw_in _ _)) in Ef. congruence.
    - cbn [edenot ren_env ev]. destruct (nt_get bw n) as [s|] eqn:Eb; [discriminate|reflexivity].
  Qed.
End Rename.

Section RenameCS.
  Variable m : list (nat * nat).
  Variables fw bw : list (option nat).
  Hypothesis Hfw : mk_fwd m = Some fw.
  Hypothesis Hbw : mk_bwd m = Some bw.
  Variable gb : nat.
  Hypothesis Hgb : (nx0 <= gb)%nat.
  Hypothesis Hm : forallb (fun p => Nat.leb gb (fst p) && Nat.leb gb (snd p)) m = true.

  Let ER := edenot_rename m fw bw Hfw Hbw.

  #[using="m Hbw Hm"] Lemma ren_agree : forall E, env_agree gb E (ren_env bw E).
  Proof.
    intros E. split; [|reflexivity]. intros n Hn. cbn [ren_env ev].
    destruct (nt_get bw n) as [s|] eqn:Eb; [|reflexivity].
    apply (bw_in m bw Hbw) in Eb. exfalso.
    pose proof (proj1 (forallb_forall _ _) Hm (s, n) Eb) as X. cbn [fst snd] in X.
    apply andb_prop in X as [_ X]. apply Nat.leb_le in X. clear Hgb. lia.
  Qed.

  #[using="m Hfw Hbw ER"] Lemma uE_rename : forall E e, evars_all (ren_ok fw bw) e = true -> uE (ren_env bw E) (erename fw e) = uE E e.
  Proof. intros. unfold uE. rewrite (ER E e H). reflexivity. Qed.

  #[using="m Hfw Hbw ER"] Lemma regs_ok_rename : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Psr,(2?.$29.)PR,(55.&5.(12.&40.))P,(3.$20.(111.$29.(112.(113.Vfw,Vbw,))R2.)$22.)P,(60.R4.R3.R2.)(60.(114.Vbw,R5.)(97.$29.$29.(115.Vfw,)R4.)R3.)")
(* [comment removed for export] *).
  Proof.
    intros E sr R Hsr HR r. rewrite (HR r). unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
    revert Hsr. generalize (ridx r) as i. clear HR r.
    induction sr as [|e t IH]; intros i Hsr; [destruct i; reflexivity|].
    cbn [forallb] in Hsr. apply andb_prop in Hsr as [He Ht].
    destruct i as [|i]; cbn [map nth]; [symmetry; exact (ER E e He) | apply IH; exact Ht].
  Qed.

  #[using="Type"] Lemma eb_ren : forall E, eb (ren_env bw E) = eb E.
  Proof. reflexivity. Qed.

  #[using="m Hfw Hbw ER"] Lemma kentry_ok_rename : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))PK,$68.P,(3.$20.(116.(113.Vfw,Vbw,)R1.)$22.)P,(6=.VSEGS,R4.R3.R2.)(6=.VSEGS,(114.Vbw,R5.)R4.(117.Vfw,R3.))")
(* [comment removed for export] *).
  Proof.
    intros E M K HK Hk.
    destruct K as [[ab ak] w v|[ab ak] n|[ab ak] n k|lo hi|ae am|re rlo rhi|[ab ak] wn|[b1 k1] dn1 [b2 k2] dn2|[ab ak] n fc|[ab ak] n];
      unfold krename, arename in *; cbn [kvars_all kentry_ok a_base a_off] in *;
      repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H as [? H] end;
      unfold flat, estart, elenZ, adenot in *; cbn [a_base a_off] in *;
      rewrite ?eb_ren; rewrite ?(ER E) by assumption; exact Hk.
  Qed.

  #[using="m Hfw Hbw ER"] Lemma know_ok_rename : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)P,(3.$20.(111.$68.(116.(113.Vfw,Vbw,))R1.)$22.)P,(64.VSEGS,R4.R3.R2.)(64.VSEGS,(114.Vbw,R5.)R4.(97.$68.$68.(117.Vfw,)R3.))")
(* [comment removed for export] *).
  Proof.
    intros E M k. induction k as [|K rest IH]; intros Hv Hk; [constructor|].
    cbn [forallb] in Hv. apply andb_prop in Hv as [H1 H2]. apply Forall_cons_iff in Hk as [HK Hr].
    cbn [map]. constructor; [apply kentry_ok_rename; assumption | apply IH; assumption].
  Qed.

  Definition pvars_all (l : list (expr * expr)) : bool :=
    forallb (fun p => evars_all (ren_ok fw bw) (fst p) && evars_all (ren_ok fw bw) (snd p)) l.

  #[using="m Hfw Hbw ER"] Lemma allowA_rename : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.Pnx,$6:.P,(3.$20.(118.(8<.R2.))$22.)P,(3.$20.(118.(30.R3.))$22.)(3.(2?.(11.$1.$1.))(5:.(114.Vbw,R5.)(119.Vfw,R4.R3.))(5:.R5.R4.))")
(* [comment removed for export] *).
  Proof.
    intros E cs nx Hv Hg. unfold allowA. cbn [rename_cs a_vis a_ghost]. rewrite !flat_map_concat_map, !map_map.
    f_equal; f_equal; apply map_ext_in; intros p Hin;
      [pose proof (proj1 (forallb_forall _ _) Hv p Hin) as Hp | pose proof (proj1 (forallb_forall _ _) Hg p Hin) as Hp];
      apply andb_prop in Hp as [H1 H2];
      unfold allow1, allow_sh, sh_lo, sh_hi, prename; cbn [fst snd]; rewrite !(uE_rename E) by assumption; reflexivity.
  Qed.

  #[using="Type"] Lemma existsb_map : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PX,StPY,StPf,P,R2.R2.PP,P,R2.$20.Pl,(2?.R4.)(3.$20.(10.R4.R2.(97.R5.R4.R3.R1.))(10.R5.Lx,R5.A1.R3.A1.R4.R1.R1.))")
(* [comment removed for export] *).
  Proof. intros X Y f P l. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
  #[using="Type"] Lemma existsb_ext_in : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PX,StPP,P,R1.$20.PQ,P,R2.$20.Pl,(2?.R3.)P,Px,R4.P,(34.R5.R1.R2.)(3.$20.A1.R5.R2.A1.R4.R2.)(3.$20.(10.R5.R4.R2.)(10.R5.R3.R2.))")
(* [comment removed for export] *).
  Proof. intros X P Q l H. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy. Qed.

  #[using="m Hfw Hbw ER"] Lemma in_allow_rename : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.Pnx,$6:.P,(3.$20.(118.(8<.R2.))$22.)(3.Pz,$1.$20.(40.(114.Vbw,R4.)(119.Vfw,R3.R2.))(40.R4.R3.))")
(* [comment removed for export] *).
  Proof.
    intros E cs nx Hv. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh. cbn [rename_cs a_vis].
    rewrite !existsb_map. f_equal; apply existsb_ext_in; intros p Hin;
      pose proof (proj1 (forallb_forall _ _) Hv p Hin) as Hp; apply andb_prop in Hp as [H1 H2];
      unfold sh_lo, sh_hi, prename; cbn [fst snd]; rewrite !(uE_rename E) by assumption; reflexivity.
  Qed.

  #[using="m Hfw Hbw ER"] Lemma in_ghostl_rename : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.Pnx,$6:.P,(3.$20.(118.(30.R2.))$22.)(3.Pz,$1.$20.(<;.(114.Vbw,R4.)(119.Vfw,R3.R2.))(<;.R4.R3.))")
(* [comment removed for export] *).
  Proof.
    intros E cs nx Hg. apply functional_extensionality. intros z. unfold in_ghostl. cbn [rename_cs a_ghost].
    rewrite existsb_map. apply existsb_ext_in. intros p Hin.
    pose proof (proj1 (forallb_forall _ _) Hg p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
    unfold prename. cbn [fst snd]. rewrite !(uE_rename E) by assumption. reflexivity.
  Qed.
  #[using="m Hfw Hbw ER"] Lemma in_ghost_rename : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.Pnx,$6:.P,(3.$20.(118.(30.R2.))$22.)(3.Pz,$1.$20.(32.(114.Vbw,R4.)(119.Vfw,R3.R2.))(32.R4.R3.))")
(* [comment removed for export] *).
  Proof. intros E cs nx Hg. apply in_ghost_of_l. apply in_ghostl_rename. exact Hg. Qed.

  #[using="nx0 argH_agree m Hfw Hbw gb Hgb Hm ER"] Lemma hid_rename : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.Pnx,$6:.Pmodel,$56.P,(3.$20.(118.(8<.R3.))$22.)(3.Pa,(12.&40.)$20.(59.(114.Vbw,R5.)(119.Vfw,R4.R3.)R2.)(59.R5.R4.R2.))")
(* [comment removed for export] *).
  Proof.
    intros E cs nx model Hv. apply functional_extensionality. intros a. unfold hid, vis.
    rewrite (in_allow_rename E cs nx Hv). rewrite <- (argH_agree E (ren_env bw E) a); [reflexivity|].
    eapply env_agree_le; [apply ren_agree | exact Hgb].
  Qed.

  #[using="m Hfw Hbw ER"] Lemma maps_match_rename : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pms,(2?.$48.)Pl,(2?.(11.(12.&40.)(12.&40.)))P,(3.$20.(111.$48.Lm0,$48.(13.(112.(113.Vfw,Vbw,)(45.R1.))(112.(113.Vfw,Vbw,)(46.R1.)))R2.)$22.)P,(93.R4.R3.R2.)(93.(114.Vbw,R5.)(97.$48.$48.(11:.Vfw,)R4.)R3.)")
(* [comment removed for export] *).
  Proof.
    intros E ms. induction ms as [|[mb ml mk] ms IH]; intros l H HM; cbn [maps_match map] in *; [exact HM|].
    cbn [forallb am_base am_len] in H. apply andb_prop in H as [Hm0 Hr]. apply andb_prop in Hm0 as [H1 H2].
    unfold mrename, is_fog, amap_den in *. cbn [am_kind am_base am_len] in *.
    rewrite ?(uE_rename E) by assumption. rewrite ?(ER E) by assumption.
    destruct (is_tok_kind mk).
    - destruct HM as [HM|(iv & l' & -> & Hsz & HM)]; [left; exact (IH _ Hr HM) | right].
      exists iv, l'. split; [reflexivity|]. split; [exact Hsz | exact (IH _ Hr HM)].
    - destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | exact (IH _ Hr HM)].
  Qed.
  (* [comment removed for export] *)
  #[using="m Hfw Hbw ER"] Lemma holes_rename : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Py,$1.Pl,(2?.(11.(12.&40.)(12.&40.)))Pms,(2?.$48.)P,(3.$20.(111.$48.Lm0,$48.(13.(112.(113.Vfw,Vbw,)(45.R1.))(112.(113.Vfw,Vbw,)(46.R1.)))R1.)$22.)P,(1;.$48.(49.R5.R4.R3.)R2.)(1;.$48.(49.(114.Vbw,R6.)R5.R4.)(97.$48.$48.(11:.Vfw,)R3.))")
(* [comment removed for export] *).
  Proof.
    intros E y l ms H HF. apply Forall_forall. intros m0 Hin Hk. apply in_map_iff in Hin as (m1 & <- & Hin).
    pose proof (proj1 (forallb_forall _ _) H m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
    unfold hole_ok, is_hole, mrename in *. cbn [am_base am_len am_kind] in *. rewrite !(uE_rename E) by assumption.
    exact (proj1 (Forall_forall _ _) HF m1 Hin Hk).
  Qed.

  #[using="m Hfw Hbw ER"] Lemma fds_ok_rename : forall E f model,
    match f with FdFile _ l o => evars_all (ren_ok fw bw) l && evars_all (ren_ok fw bw) o | _ => true end%bool = true ->
    fds_ok E f model -> fds_ok (ren_env bw E) (frename fw f) model.
  Proof.
    intros E f model Hv H. destruct f as [|k len off|]; try exact H.
    apply andb_prop in Hv as [Hl Ho]. cbn [frename].
    destruct H as [p [c (H1 & H2 & H3 & H4 & H5)]]. exists p, c.
    rewrite !(uE_rename E) by assumption. rewrite !(ER E) by assumption. rewrite eb_ren. repeat split; assumption.
  Qed.

  #[using="nx0 argH_agree SINV_agree m Hfw Hbw gb Hgb Hm ER"] Lemma cs_ok_rename : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pnx,$6:.P,(3.$20.(11;.(113.Vfw,Vbw,)R5.)$22.)P,(3.(2?.$62.)(63.(<4.R6.))(2=.$62.))P,(57.R8.R7.R6.R5.R4.)(57.(114.Vbw,R9.)(119.Vfw,R8.R4.)R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros E cs R FULL model nx Hv Hlog HC.
    unfold csvars_all in Hv.
    apply andb_prop in Hv as [Hv Hfd]. apply andb_prop in Hv as [Hv Hbrk]. apply andb_prop in Hv as [Hv Hsubv].   (* [comment removed for export] *)
    apply andb_prop in Hv as [Hv Hgh].
    apply andb_prop in Hv as [Hv Hvis]. apply andb_prop in Hv as [Hv Hmaps]. apply andb_prop in Hv as [Hregs Hkn].
    pose proof (hid_rename E cs nx model Hvis) as HH.
    pose proof (allowA_rename E cs nx Hvis Hgh) as HA.
    assert (HMr : Mr (ren_env bw E) (rename_cs fw cs nx) model FULL = Mr E cs model FULL) by (unfold Mr; rewrite HH; reflexivity).
    destruct HC; constructor; cbn [rename_cs a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_sub kn mk_ss s_regs s_log s_know s_pc s_next] in *;
      rewrite ?HA, ?HMr; try assumption.
    - apply regs_ok_rename; assumption.
    - reflexivity.
    - apply know_ok_rename; assumption.
    - apply fds_ok_rename; assumption.
    - apply maps_match_rename; assumption.
    - apply holes_rename; assumption.
    - (* [comment removed for export] *) apply Forall_forall. intros m0 Hin Hk. apply in_map_iff in Hin as (m1 & <- & Hin).
      pose proof (proj1 (forallb_forall _ _) Hmaps m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
      unfold amap_den, mrename in *. cbn [am_base am_len am_kind] in *. rewrite !(ER E) by assumption.
      exact (proj1 (Forall_forall _ _) co_none0 m1 Hin Hk).
    - (* [comment removed for export] *) apply Forall_forall. intros m0 Hin Hk a Ha. apply in_map_iff in Hin as (m1 & <- & Hin).
      pose proof (proj1 (forallb_forall _ _) Hmaps m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
      unfold mrename in *. cbn [am_base am_len am_kind] in *. rewrite !(ER E) in Ha by assumption.
      exact (proj1 (Forall_forall _ _) co_kinds0 m1 Hin Hk a Ha).
    - rewrite (ER E) by assumption. assumption.
    - intros a. rewrite HH, (in_ghost_rename E cs nx Hgh). exact (co_zero0 a).
    - eapply SINV_agree; [eapply env_agree_le; [apply ren_agree | exact Hgb] | assumption].
    - (* [comment removed for export] *) intros e He. destruct (co_nk0 e He) as (P & iv & Hiv & B1 & B2 & NB). split; [exact P|].
      exists iv. split; [exact Hiv|]. split; [exact B1|]. split; [exact B2|]. intros (m0 & Hin & Hf & Hk & Hd). apply NB.
      apply in_map_iff in Hin as (m1 & <- & Hin). pose proof (proj1 (forallb_forall _ _) Hmaps m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
      exists m1. unfold amap_den, mrename, is_fog in *. cbn [am_base am_len am_kind] in *. rewrite !(ER E) in Hd by assumption. auto.
    - (* [comment removed for export] *) intros e He. destruct (co_lzk0 e He) as (P & iv & Hiv & B1 & B2 & NB). split; [exact P|].
      exists iv. split; [exact Hiv|]. split; [exact B1|]. split; [exact B2|]. intros (m0 & Hin & Hf & Hk & Hd). apply NB.
      apply in_map_iff in Hin as (m1 & <- & Hin). pose proof (proj1 (forallb_forall _ _) Hmaps m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
      exists m1. unfold amap_den, mrename, is_fog in *. cbn [am_base am_len am_kind] in *. rewrite !(ER E) in Hd by assumption. auto.
    - (* [comment removed for export] *) apply Forall_forall. intros t0 Hin. apply in_map_iff in Hin as (t1 & <- & Hin).
      pose proof (proj1 (forallb_forall _ _) Hsubv t1 Hin) as Htt. apply andb_prop in Htt as [H1 H2].
      pose proof (proj1 (Forall_forall _ _) co_sub0 t1 Hin) as X. unfold sub_ok, prename in *. cbn [fst snd] in *.
      rewrite !(uE_rename E) by assumption. exact X.
    - (* [comment removed for export] *) apply Forall_forall. intros m0 Hin Hf Hk a Ha. apply in_map_iff in Hin as (m1 & <- & Hin).
      pose proof (proj1 (forallb_forall _ _) Hmaps m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
      unfold mrename, is_fog in *. cbn [am_base am_len am_kind] in *. rewrite !(ER E) in Ha by assumption.
      exact (proj1 (Forall_forall _ _) co_def0 m1 Hin Hf Hk a Ha).
    - (* [comment removed for export] *) apply Forall_forall. intros m0 Hin Hk z Hz. apply in_map_iff in Hin as (m1 & <- & Hin).
      pose proof (proj1 (forallb_forall _ _) Hmaps m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
      unfold mrename in Hk, Hz. cbn [am_base am_len am_kind] in Hk, Hz. rewrite !(uE_rename E) in Hz by assumption.
      destruct (proj1 (Forall_forall _ _) co_cov0 m1 Hin Hk z Hz) as [Hnn|(t1 & Ht1 & Hzt)]; [left; exact Hnn | right].
      exists (prename fw t1). split; [apply in_map; exact Ht1|].
      pose proof (proj1 (forallb_forall _ _) Hsubv t1 Ht1) as Htt. apply andb_prop in Htt as [T1 T2].
      unfold in_tok, prename in *. cbn [fst snd]. rewrite !(uE_rename E) by assumption. exact Hzt.
  Qed.
End RenameCS.

#[using="argH_agree SINV_agree"] Lemma rename_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pgb,$6:.PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pm,(2?.(11.$6:.$6:.))Pcs',$2>.P,(<:.Vnx0,R8.)P,(57.R8.R7.R6.R5.R4.)P,(3.(23.$2>.)(11<.R:.R8.R4.)(82.$2>.R3.))(4:.$0.LE',$0.(5.(9;.R<.R;.R1.)(5.(57.R1.R5.R9.R8.R7.)(3.$1.(83.R5.)(83.R:.)))))")
(* [comment removed for export] *).
Proof.
  intros gb E cs R FULL model m cs' Hgb HC H. unfold node_rename in H.
  destruct (forallb (fun p => Nat.leb gb (fst p) && Nat.leb gb (snd p)) m) eqn:Hm; [|discriminate].
  destruct (mk_fwd m) as [fw|] eqn:Hfw; [|discriminate].
  destruct (mk_bwd m) as [bw|] eqn:Hbw; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. apply andb_prop in Hc as [Hv Hlog].
  exists (ren_env bw E). split; [exact (ren_agree m bw Hbw gb Hm E)|]. split; [|reflexivity].
  match goal with |- cs_ok _ (with_ss _ (mk_ss _ _ _ ?NX)) _ _ _ =>
    change (cs_ok (ren_env bw E) (rename_cs fw cs NX) R FULL model) end.
  apply (cs_ok_rename m fw bw Hfw Hbw gb Hgb Hm); [exact Hv | exact (co_log _ _ _ _ _ HC) | exact HC].
Qed.

#[using="argH_agree SINV_agree"] Lemma compact_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pgb,$6:.PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pcs',$2>.P,(<:.Vnx0,R7.)P,(57.R7.R6.R5.R4.R3.)P,(3.(23.$2>.)(11=.R9.R7.)(82.$2>.R3.))(4:.$0.LE',$0.(5.(9;.R;.R:.R1.)(5.(57.R1.R5.R8.R7.R6.)(3.$1.(83.R5.)(83.R9.)))))")
(* [comment removed for export] *).
Proof. intros gb E cs R FULL model cs' Hgb HC H. unfold node_compact in H. eapply rename_sound; eassumption. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="SEGS_in_hull HULL_ok"] Lemma abstractcell_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pb,$29.Pn,$1.Pcs',$2>.P,(57.R8.R7.R6.R5.R4.)P,(3.(23.$2>.)(11>.VA,R8.R4.R3.)(82.$2>.R2.))(5.(57.R:.R3.R8.R7.R6.)(3.$1.(83.R3.)(83.R9.)))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model b n cs' HC H. unfold node_abstractcell in H.
  destruct (split_lit b) as [bb bo]. cbv zeta in H.
  destruct (kunk_covered A (kn cs) (KUnk (SA bb bo) (ELit n))) eqn:Hcov; [|discriminate].
  injection H as <-. split; [|apply pc_set_kn].
  apply cs_ok_set_kn; [exact HC|]. constructor.
  - eapply kunk_covered_sound; [exact (co_know _ _ _ _ _ HC) | exact Hcov].
  - eapply know_ok_cutout; [exact (co_know _ _ _ _ _ HC) | intros; reflexivity].
Qed.

#[using="Type"] Lemma hw_apply_true_incl : forall r a x K, In K (hw_apply r a x true) -> In K r.
Proof.
  induction r as [|X r IH]; intros a x K H; [exact H|]. cbn [hw_apply] in H.
  destruct X as [a' w v| | | | | | | | |]; cbn in H;
    try (destruct H as [H|H]; [left; exact H | right; eapply IH; exact H]).
  destruct (saddr_eqb a' a); [right; eapply IH; exact H|].
  destruct H as [H|H]; [left; exact H | right; eapply IH; exact H].
Qed.

#[using="Type"] Lemma hw_apply_true_vars : forall r a x b, AP.kn_vars_lt b r = true -> AP.kn_vars_lt b (hw_apply r a x true) = true.
Proof.
  induction r as [|X r IH]; intros a x b H; [reflexivity|]. cbn [AP.kn_vars_lt] in H. apply andb_prop in H as [HX Hr].
  cbn [hw_apply]. destruct X as [a' w v| | | | | | | | |]; cbn [AP.kn_vars_lt]; rewrite ?HX, ?(IH a x b Hr); try reflexivity.
  destruct (saddr_eqb a' a); [exact (IH a x b Hr)|]. cbn [AP.kn_vars_lt]. rewrite HX, (IH a x b Hr). reflexivity.
Qed.

#[using="Type"] Lemma hw_apply_ok : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.PM,P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)Pa,$78.Px,$6:.P,(64.VSEGS,R5.R4.R3.)P,(3.$20.(9<.R2.R4.)$22.)(5.(64.VSEGS,(>9.R7.R3.(52.R7.(11?.R5.R4.)))R6.(120.R5.R4.R3.$33.))(3.$20.(9<.(121.R3.)(120.R5.R4.R3.$33.))$22.))")
(* [comment removed for export] *).
Proof.
  intros E M k a x. induction k as [|X r IH]; intros HK Hv.
  - split; [constructor | reflexivity].
  - apply Forall_cons_iff in HK as [HX Hr]. cbn [AP.kn_vars_lt] in Hv. apply andb_prop in Hv as [HvX Hvr].
    assert (AG : forall e, env_agree x E (upd E x e)) by (intros; apply upd_agree).
    assert (KEEP : forall e, kentry_ok SEGS (upd E x e) M X).
    { intros e. apply (@Forall_inv _ (kentry_ok SEGS (upd E x e) M) X []).
      eapply (know_ok_agree' x); [apply AG | | constructor; [exact HX | constructor]].
      cbn [AP.kn_vars_lt]. rewrite HvX. reflexivity. }
    assert (KEEPV : AP.kentry_vars_lt (Datatypes.S x) X = true) by (eapply kentry_vars_lt_mono; [exact HvX | lia]).
    cbn [hw_apply hw_val].
    destruct X as [a' w v| | | | | | | | |];
      try (destruct (IH Hr Hvr) as [IH1 IH2]; split; [constructor; [apply KEEP | exact IH1] | cbn [AP.kn_vars_lt]; rewrite KEEPV, IH2; reflexivity]).
    destruct (saddr_eqb a' a) eqn:Hs.
    + (* [comment removed for export] *)
      split.
      * constructor.
        -- cbn [kentry_ok] in HX |- *. destruct HX as (Hw & Hf & Hrd).
           cbn [AP.kentry_vars_lt AP.saddr_vars_lt] in HvX. apply andb_prop in HvX as [Hva Hvv].
           assert (Ea : adenot (upd E x (edenot E v)) a' = adenot E a').
           { unfold adenot. rewrite <- (edenot_agree' x E _ (a_base a') (AG _) Hva). reflexivity. }
           assert (Es : estart (upd E x (edenot E v)) a' = estart E a').
           { unfold estart. rewrite <- (edenot_agree' x E _ (a_base a') (AG _) Hva). reflexivity. }
           split; [exact Hw|]. split; [unfold flat in *; rewrite ?Es; exact Hf|].
           rewrite Ea. cbn [edenot]. rewrite upd_at. exact Hrd.
        -- eapply (know_ok_agree' x); [apply AG | apply hw_apply_true_vars; exact Hvr |].
           apply Forall_forall. intros K HK'. apply hw_apply_true_incl in HK'. exact (proj1 (Forall_forall _ _) Hr K HK').
      * cbn [AP.kn_vars_lt AP.kentry_vars_lt]. cbn [AP.kentry_vars_lt] in KEEPV. apply andb_prop in KEEPV as [Ka _].
        rewrite Ka. cbn [AP.expr_vars_lt]. replace (Nat.ltb x (Datatypes.S x)) with true by (symmetry; apply Nat.ltb_lt; lia). cbn [andb].
        eapply kn_vars_lt_mono'; [apply hw_apply_true_vars; exact Hvr | lia].
    + destruct (IH Hr Hvr) as [IH1 IH2]. split; [constructor; [apply KEEP | exact IH1] | cbn [AP.kn_vars_lt]; rewrite KEEPV, IH2; reflexivity].
Qed.

#[using="Type"] Lemma hw_go_ok : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pbs,(2?.$29.)PE,$0.PM,P,(12.&40.)(23.(12.&8.))Pk,(2?.$68.)Px,$6:.P,(64.VSEGS,R4.R3.R2.)P,(3.$20.(9<.R2.R3.)$22.)(4:.$0.LE',$0.(5.(9;.R4.R7.R1.)(5.(64.VSEGS,R1.R6.(122.R5.R8.R4.))(3.$20.(9<.(>2.R4.(>0.$29.R8.))(122.R5.R8.R4.))$22.))))")
(* [comment removed for export] *).
Proof.
  induction bs as [|b r IH]; intros E M k x HK Hv.
  - exists E. split; [apply env_agree_refl|]. cbn [hw_go length]. rewrite Nat.add_0_r. split; assumption.
  - cbn [hw_go length]. destruct (hw_apply_ok E M k (sa_of b) x HK Hv) as [H1 H2].
    destruct (IH _ M _ (Datatypes.S x) H1 H2) as (E' & Hag & HK' & Hv').
    exists E'. split; [|split; [exact HK' | rewrite <- Nat.add_succ_comm; exact Hv']].
    apply (env_agree_trans _ _ (upd E x (edenot E (hw_val k (sa_of b)))) _); [apply upd_agree | eapply env_agree_le; [exact Hag | lia]].
Qed.

#[using="argH_agree SINV_agree"] Lemma havocwords_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pbs,(2?.$29.)Pcs',$2>.P,(57.R7.R6.R5.R4.R3.)P,(3.(23.$2>.)(123.Vnx0,R7.R3.)(82.$2>.R2.))(4:.$0.LE',$0.(5.(5.(9;.Vnx0,R:.R1.)(9;.(:4.R9.)R:.R1.))(5.(57.R1.R4.R8.R7.R6.)(3.$1.(83.R4.)(83.R9.)))))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model bs cs' HC H. unfold node_havocwords in H.
  destruct (fresh_ok nx0 cs) eqn:Hf; [|discriminate]. injection H as <-.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct (hw_go_ok bs E (Mr E cs model FULL) (kn cs) (nxt cs) (co_know _ _ _ _ _ HC)) as (E' & Hag & HK' & _).
  { rewrite kn_vars_lt_eq. rewrite <- kn_vars_lt_eq. exact Fkn. }
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC2.
  replace (with_ss cs (mk_ss (s_pc (a_ss cs)) (s_regs (a_ss cs)) (hw_go (s_know (a_ss cs)) bs (s_next (a_ss cs))) (s_next (a_ss cs) + length bs)))
    with (set_kn (bump cs (length bs)) (hw_go (kn cs) bs (nxt cs))) by reflexivity.
  apply cs_ok_set_kn.
  - destruct HC2; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
      try assumption; reflexivity.
  - unfold Mr. change (hid E' (bump cs (length bs)) model) with (hid E' cs model).
    rewrite (hid_agree (nxt cs) E E' cs model Hag Fle Fallow). exact HK'.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma respell_ok_sound : forall E M k a e,
  know_ok SEGS E M k -> respell_ok k a e = true -> edenot E a = edenot E e.
Proof.
  intros E M k a e HK H. unfold respell_ok in H.
  destruct (decide_branch k BC_EQ a e) as [[|]|] eqn:Hd.
  - pose proof (decide_branch_sound SEGS E M k BC_EQ a e true HK Hd) as Heq. cbn [branch_taken] in Heq. apply bv_eqb_eq in Heq. exact Heq.
  - destruct (erange k (mkAlu ALU_SUB a e)) as [[lo hi]|] eqn:Hr; [|discriminate].
    apply andb_prop in H as [H0 H1]. apply Z.eqb_eq in H0. apply Z.eqb_eq in H1. subst lo hi.
    pose proof (erange_sound SEGS E M k _ 0 0 HK Hr) as Hb. rewrite mkAlu_denot in Hb.
    cbn [alu64 alu] in Hb. rewrite bv_sub_unsigned in Hb. unfold bv_wrap in Hb.
    pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E e)) as Re.
    apply bv_eq. change (bv_modulus 64) with (2 ^ 64)%Z in Hb. unfold two64 in *.
    assert (Hm : ((bv_unsigned (edenot E a) - bv_unsigned (edenot E e)) mod 2 ^ 64 = 0)%Z) by lia.
    apply Z.mod_divide in Hm; [|lia]. destruct Hm as [q Hq]. assert (q = 0)%Z by nia. subst q. lia.
  - destruct (erange k (mkAlu ALU_SUB a e)) as [[lo hi]|] eqn:Hr; [|discriminate].
    apply andb_prop in H as [H0 H1]. apply Z.eqb_eq in H0. apply Z.eqb_eq in H1. subst lo hi.
    pose proof (erange_sound SEGS E M k _ 0 0 HK Hr) as Hb. rewrite mkAlu_denot in Hb.
    cbn [alu64 alu] in Hb. rewrite bv_sub_unsigned in Hb. unfold bv_wrap in Hb.
    pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E e)) as Re.
    apply bv_eq. change (bv_modulus 64) with (2 ^ 64)%Z in Hb. unfold two64 in *.
    assert (Hm : ((bv_unsigned (edenot E a) - bv_unsigned (edenot E e)) mod 2 ^ 64 = 0)%Z) by lia.
    apply Z.mod_divide in Hm; [|lia]. destruct Hm as [q Hq]. assert (q = 0)%Z by nia. subst q. lia.
Qed.
#[using="Type"] Lemma respell_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "PE,$0.Pcs,$2>.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.Pr,$6:.Pe,$29.Pcs',$2>.P,(57.R8.R7.R6.R5.R4.)P,(3.(23.$2>.)(124.R8.R4.R3.)(82.$2>.R2.))(5.(57.R:.R3.R8.R7.R6.)(3.$1.(83.R3.)(83.R9.)))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model r e cs' HC H. unfold node_respell in H.
  destruct (Nat.ltb 0 r && Nat.ltb r 32 && AP.expr_vars_lt (nxt cs) e && respell_ok (kn cs) (reg cs r) e)%bool eqn:Hc; [|discriminate].
  injection H as <-.
  apply andb_prop in Hc as [Hc Hok]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [H1 H2]. apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2.
  pose proof (respell_ok_sound E _ (kn cs) (reg cs r) e (co_know _ _ _ _ _ HC) Hok) as Heq.
  split; [|reflexivity].
  destruct HC; constructor; cbn [set_reg with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset]; try assumption; try reflexivity.
  apply regs_ok_respell; [assumption | lia | unfold reg in Heq; symmetry; exact Heq].
Qed.

#[using="Type"] Lemma self_jump_word : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pms,$125.P,(3.(23.(12.&40.))(126.R1.)(25.(12.&40.)))P,(3.(23.(12.&20.))(127.VSEGS,(128.R2.))(82.(12.&20.)(42.&20.$129.)))(3.$20.(12:.VSEGS,R3.)$22.)")
(* [comment removed for export] *).
Proof. intros ms Hs Hf. unfold is_self_jump. rewrite Hs, Hf. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma node_spin_sound : forall cs E R FULL model,   (* [comment removed for export] *)
  cs_ok E cs R FULL model -> node_spin SEGS cs = true ->
  srealizes0 SEGS (cfg R (pc cs) FULL model) t_nil.
Proof.
  intros cs E R FULL model HC Hn. unfold node_spin in Hn.
  apply andb_prop in Hn as [Hn Hw]. apply andb_prop in Hn as [H0 H4].
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hf; [|discriminate].
  apply Z.eqb_eq in Hw.
  assert (Hw' : w = Z_to_bv 32 SPIN_WORD).
  { apply bv_eq. rewrite Hw. reflexivity. }
  subst w.
  apply srz0_spin.
  - apply is_self_jump_to_spin. apply self_jump_word; [reflexivity | exact Hf].
  - exact (co_halt _ _ _ _ _ HC).
Qed.

(* [comment removed for export] *)
Definition LCOK (lc : option loopctx) (D : TSet) (E : env) (fs : Fs.Fs) : Prop :=
  match lc with
  | None => True
  | Some (LC h nx lo hi) => ((nx0 <= lo)%nat /\ (lo <= hi)%nat /\ length (s_regs (a_ss nx)) = 32%nat) /\
              forall E' R' F' m', env_agree lo E E' -> cs_ok E' nx R' F' m' -> m_fs m' = fs ->
                srealizes SEGS (cfg R' h F' m') D
  (* [comment removed for export] *)
  | Some (JC j js sk b lo) => ((nx0 <= b)%nat /\ (b <= lo)%nat /\ length (s_regs (a_ss js)) = 32%nat) /\
              forall E' R' F' m', env_agree b E E' -> cs_ok E' js R' F' m' -> m_fs m' = fs ->
                srealizes SEGS (cfg R' (pc js) F' m') (sd D E' fs sk)
  end.

#[using="Type"] Lemma LCOK_bnd : forall lc D E fs, LCOK lc D E fs -> (nx0 <= match lc with Some c => lc_bnd c | None => nx0 end)%nat.
Proof. intros [[h nx lo hi|j js sk b lo]|] D E fs HL; cbn [LCOK lc_bnd] in *; [destruct HL as [(H1 & H2 & _) _]; lia | destruct HL as [(H1 & _ & _) _]; lia | lia]. Qed.

Definition lc_guard (lc : option loopctx) (cs : acs) : bool :=
  match lc with Some c => Nat.leb (lc_bnd c) (nxt cs) | None => true end.

#[using="Type"] Lemma LCOK_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Plc,(23.$12=.)PD,$9>.PE,$0.PE',$0.Pfs,$9?.Pcs,$2>.P,(12>.R6.R5.R4.R2.)P,(3.$20.(12?.R7.R2.)$22.)P,(9;.(:4.R3.)R6.R5.)(12>.R9.R8.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros [[h nx lo hi|j js sk b lo]|] D E E' fs cs HL Hg Hag; [| |exact I]; cbn [LCOK lc_guard lc_bnd] in *;
  apply Nat.leb_le in Hg; destruct HL as [(Hn0 & Hlh & Hlen) HL]; (split; [split; [exact Hn0 | split; [exact Hlh | exact Hlen]]|]);
  intros E2 R' F' m' Hag2; apply HL; (eapply env_agree_trans; [eapply env_agree_le; [exact Hag | lia] | exact Hag2]).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma LCOK_agree_gb : forall lc D E E' fs,
  LCOK lc D E fs -> env_agree (match lc with Some c => lc_bnd c | None => nx0 end) E E' -> LCOK lc D E' fs.
Proof.
  intros [[h nx lo hi|j js sk b lo]|] D E E' fs HL Hag; [| |exact I]; cbn [LCOK lc_bnd] in *;
  destruct HL as [(Hn0 & Hlh & Hlen) HL]; (split; [split; [exact Hn0 | split; [exact Hlh | exact Hlen]]|]);
  intros E2 R' F' m' Hag2; apply HL; (eapply env_agree_trans; [eapply env_agree_le; [exact Hag | lia] | exact Hag2]).
Qed.

(* [comment removed for export] *)
#[using="HOLES_agree"] Lemma cont_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound ()) "Pbfuel,$6:.Pfuel,$6:.Plc,(23.$12=.)Pk,$?:.Pcs,$2>.Pcs',$2>.Ps,$:0.PE,$0.Pmodel,$56.PD,$9>.P,(3.$?;.(130.VSEGS,VIT,VA,Vnx0,VLIMIT,VXN,VXE,VXB,VHS,VKC,R:.R9.R8.R5.R7.)(?=.R4.))P,(12>.R9.R2.R4.(:5.R3.))P,(3.$20.(12?.R:.R8.)$22.)P,A1.R4.(2=.$::.)P,PE,$0.PR,(55.&5.(12.&40.))PFULL,P,(12.&40.)(23.(12.&8.))Pmodel,$56.P,(57.R4.R=.R3.R2.R1.)P,(12>.R11.R:.R5.(:5.R2.))P,A1.R;.(2=.$::.)(:6.VSEGS,(:7.VSEGS,R6.(83.R10.)R5.R4.)(:2.R<.R7.(:5.R4.)R?.))PE',$0.PR',(55.&5.(12.&40.))PFULL',P,(12.&40.)(23.(12.&8.))Pmodel',$56.P,(5.(9;.Vnx0,R<.R4.)(9;.(:4.R?.)R<.R4.))P,(57.R5.R?.R4.R3.R2.)P,(3.$9?.(:5.R3.)(:5.R=.))(:6.VSEGS,(:7.VSEGS,R6.(83.R11.)R5.R4.)(:2.R=.R?.(:5.R>.)R10.))")
(* [comment removed for export] *).
Proof.
  intros bfuel fuel lc k cs cs' s E model D Hc HL Hg HD IH E' R' FULL' model' [Hag Hag2] HC' Hfs.
  rewrite (sd_agree D E E' (m_fs model) s Hag (check_vars _ _ _ _ _ _ Hc)), <- Hfs.
  apply (IH E' R' FULL' model' HC'); [|exact HD]. rewrite Hfs. eapply LCOK_agree; [exact HL | exact Hg | exact Hag2].
Qed.

#[using="HOLES_agree"] Lemma cont_agree0 : forall bfuel fuel lc k cs cs' s E model D,   (* [comment removed for export] *)
  CHECK bfuel fuel lc cs' k = COk s ->
  LCOK lc D E (m_fs model) -> lc_guard lc cs = true -> D [] ->
  (forall E R FULL model, cs_ok E cs' R FULL model -> LCOK lc D E (m_fs model) -> D [] ->
     srealizes0 SEGS (cfg R (pc cs') FULL model) (sd D E (m_fs model) s)) ->
  forall E' R' FULL' model',
    env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
    srealizes0 SEGS (cfg R' (pc cs') FULL' model') (sd D E (m_fs model) s).
Proof.
  intros bfuel fuel lc k cs cs' s E model D Hc HL Hg HD IH E' R' FULL' model' [Hag Hag2] HC' Hfs.
  rewrite (sd_agree D E E' (m_fs model) s Hag (check_vars _ _ _ _ _ _ Hc)), <- Hfs.
  apply (IH E' R' FULL' model' HC'); [|exact HD]. rewrite Hfs. eapply LCOK_agree; [exact HL | exact Hg | exact Hag2].
Qed.

(* [comment removed for export] *)
#[using="IT_ok SEGS_wx SEGS_in_hull HULL_ok SHADOW_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree HOLES_agree HOLES_nil node_x_sound0"] Theorem check_sound0 : forall fuel bfuel lc p cs s,
  CHECK bfuel fuel lc cs p = COk s -> spin_only p = true ->
  forall E R FULL model D, cs_ok E cs R FULL model -> LCOK lc D E (m_fs model) -> D [] ->
  srealizes0 SEGS (cfg R (pc cs) FULL model) (sd D E (m_fs model) s).
Proof.
  induction fuel as [|fuel IH]; intros bfuel lc p cs s Hc Hso E R FULL model D HC HL HD; [discriminate|].
  cbn [AP.check] in Hc.
  match type of Hc with (if negb ?g then _ else _) = _ => destruct g eqn:Hg; [|discriminate] end. cbn [negb] in Hc.
  assert (CONT : forall k cs' s', CHECK bfuel fuel lc cs' k = COk s' -> spin_only k = true ->
            forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' ->
            m_fs model' = m_fs model -> srealizes0 SEGS (cfg R' (pc cs') FULL' model') (sd D E (m_fs model) s')).
  { intros k cs' s' Hk Hgk. eapply cont_agree0; [exact Hk | exact HL | exact Hg | exact HD | intros; eapply IH; eassumption]. }
  destruct p as [stops k|e mid k1 k2|ce cmid ck1 ck2|db1 db2 dk1 dk2|sb1 sn1 sb2 sn2 k| |K k|jb joff jn k|ixs k|db dn k|gws k|bm k|hrs k|hbK k|r logc fb k|y k|ma mb|ia ib ic|qa qb|ka kb|x args k|xid xargs k|eid eargs k|bid bargs kb1 kb2|lJ lN linv lbody lk| |h| | |fi fsz fk|gi gsz gk|gb gn gk2|ub un uk|hlo hhi hk|ilo ihi ik|djp drs dk|rnm rnk|cpk|vj vjs vlo vka vk|mj|ab an ak|hws hwk|rsr rse rsk|iha ihb ihc].
  all: cbn [spin_only] in Hso; try discriminate Hso.
  - (* [comment removed for export] *)
    destruct (run_block_gc SEGS IT _ KC bfuel (stops ++ STOPS A) cs) as [cs1|] eqn:Hrb; [|discriminate].
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    eapply run_block_gc_sound0; [exact Hgb | exact Hrb | exact HC |].
    intros E' R' FULL' model' Hag HC1 Hfs. exact (CONT k cs1 s Hc Hso E' R' FULL' model' Hag HC1 Hfs).
  - (* [comment removed for export] *)
    destruct (node_fresh nx0 cs r logc fb) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_fresh_sound0 r logc fb cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hc Hso).
  - (* [comment removed for export] *)
    apply andb_prop in Hso as [Hx Hso].
    destruct (node_x SEGS A nx0 x args cs) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_x_sound0 x Hx args cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hc Hso).
  - (* [comment removed for export] *)
    destruct (node_spin SEGS cs) eqn:Hn; [|discriminate]. injection Hc as <-. cbn [sd].
    exact (node_spin_sound cs E R FULL model HC Hn).
  - (* [comment removed for export] *)
    destruct (branch_probe IT cs) as [e|] eqn:Hbp; [|discriminate].
    destruct (erange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    destruct (Z.ltb hi 1 || Z.ltb 0 lo)%bool eqn:Hdec.
    { (* [comment removed for export] *)
      destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) cs) as [cs1|] eqn:Hrb; [|discriminate].
      destruct (Z.eqb (pc cs1) djp); [|discriminate].
      eapply run_block_gc_sound0; [exact Hgb | exact Hrb | exact HC |].
      intros E' R' FULL' model' Hag HC1 Hfs. exact (CONT dk cs1 s Hc Hso E' R' FULL' model' Hag HC1 Hfs). }
    cbv zeta in Hc.
    destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e lo 0 :: kn cs))) as [ca|] eqn:Hra; [|discriminate].
    destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e 1 hi :: kn cs))) as [cb|] eqn:Hrb; [|discriminate].
    destruct (node_diamond_join A nx0 (nxt cs) djp drs ca cb) as [csj|] eqn:Hj; [|discriminate].
    destruct (split_sound cs e 0 lo hi E R FULL model HC Hr) as [HCl HCr].
    destruct (diamond_join_sound (nxt cs) djp drs ca cb csj Hj) as [Ja Jb].
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
    + rewrite <- (pc_set_kn cs (KRange e lo 0 :: kn cs)).
      eapply run_block_gc_sound0; [exact Hgb | exact Hra | exact (HCl Hle) |].
      intros E' R' FULL' model' [Hag0 Hag1] HC1 Hfs.
      destruct (Ja E' R' FULL' model' HC1) as (E'' & [Hag2a Hag2b] & HC2 & Hpc2). rewrite <- Hpc2.
      change (env_agree (nxt cs) E E') in Hag1.
      exact (CONT dk csj s Hc Hso E'' R' FULL' model'
               (conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) HC2 Hfs).
    + rewrite <- (pc_set_kn cs (KRange e 1 hi :: kn cs)).
      eapply run_block_gc_sound0; [exact Hgb | exact Hrb | exact (HCr ltac:(lia)) |].
      intros E' R' FULL' model' [Hag0 Hag1] HC1 Hfs.
      destruct (Jb E' R' FULL' model' HC1) as (E'' & [Hag2a Hag2b] & HC2 & Hpc2). rewrite <- Hpc2.
      change (env_agree (nxt cs) E E') in Hag1.
      exact (CONT dk csj s Hc Hso E'' R' FULL' model'
               (conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) HC2 Hfs).
Qed.

(* [comment removed for export] *)
#[using="IT_ok SEGS_wx SEGS_in_hull HULL_ok SHADOW_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree HOLES_agree HOLES_nil node_sys_sound node_brk2_sound node_mmap2_sound node_mmapin_sound node_mprotect2_sound node_exit_sound node_x_sound node_x_sound0 node_join_sound node_ext_sound node_emit_sound node_ext2_sound HS_sound"] Theorem check_sound : forall fuel bfuel lc p cs s,
  CHECK bfuel fuel lc cs p = COk s -> spin_guarded p = true ->
  forall E R FULL model D, cs_ok E cs R FULL model -> LCOK lc D E (m_fs model) -> D [] ->
  srealizes SEGS (cfg R (pc cs) FULL model) (sd D E (m_fs model) s).
Proof.
  induction fuel as [|fuel IH]; intros bfuel lc p cs s Hc Hsg E R FULL model D HC HL HD; [discriminate|].
  cbn [AP.check] in Hc.
  match type of Hc with (if negb ?g then _ else _) = _ => destruct g eqn:Hg; [|discriminate] end. cbn [negb] in Hc.
  assert (CONT : forall k cs' s', CHECK bfuel fuel lc cs' k = COk s' -> spin_guarded k = true ->
            forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' ->
            m_fs model' = m_fs model -> srealizes SEGS (cfg R' (pc cs') FULL' model') (sd D E (m_fs model) s')).
  { intros k cs' s' Hk Hgk. eapply cont_agree; [exact Hk | exact HL | exact Hg | exact HD | intros; eapply IH; eassumption]. }
  assert (SAME : forall k cs' s', CHECK bfuel fuel lc cs' k = COk s' -> spin_guarded k = true -> cs_ok E cs' R FULL model ->
            srealizes SEGS (cfg R (pc cs') FULL model) (sd D E (m_fs model) s')).
  { intros k cs' s' Hk Hgk HC'. refine (CONT k cs' s' Hk Hgk E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' eq_refl). }
  (* [comment removed for export] *)
  assert (CONT0 : forall k cs' s', CHECK bfuel fuel lc cs' k = COk s' -> (spin_only k || spin_guarded k) = true ->
            forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' ->
            m_fs model' = m_fs model -> srealizes0 SEGS (cfg R' (pc cs') FULL' model') (sd D E (m_fs model) s')).
  { intros k cs' s' Hk Hgk. destruct (spin_only k) eqn:Hso.
    - eapply cont_agree0; [exact Hk | exact HL | exact Hg | exact HD | intros; eapply check_sound0; eassumption].
    - cbn [orb] in Hgk. intros E' R' FULL' model' Hag HC' Hfs. apply srealizes_srealizes0. exact (CONT k cs' s' Hk Hgk E' R' FULL' model' Hag HC' Hfs). }
  cbn [spin_guarded] in Hsg.
  destruct p as [stops k|e mid k1 k2|ce cmid ck1 ck2|db1 db2 dk1 dk2|sb1 sn1 sb2 sn2 k| |K k|jb joff jn k|ixs k|db dn k|gws k|bm k|hrs k|hbK k|r logc fb k|y k|ma mb|ia ib ic|qa qb|ka kb|x args k|xid xargs k|eid eargs k|bid bargs kb1 kb2|lJ lN linv lbody lk| |h| | |fi fsz fk|gi gsz gk|gb gn gk2|ub un uk|hlo hhi hk|ilo ihi ik|djp drs dk|rnm rnk|cpk|vj vjs vlo vka vk|mj|ab an ak|hws hwk|rsr rse rsk|iha ihb ihc].
  - (* [comment removed for export] *)
    destruct (run_block_gc SEGS IT _ KC bfuel (stops ++ STOPS A) cs) as [cs1|] eqn:Hrb; [|discriminate].
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    eapply run_block_gc_sound; [exact Hgb | exact Hrb | exact HC |].
    intros E' R' FULL' model' Hag HC1 Hfs. exact (CONT k cs1 s Hc Hsg E' R' FULL' model' Hag HC1 Hfs).
  - (* [comment removed for export] *)
    apply andb_prop in Hsg as [Hsg1 Hsg2].
    destruct (AP.expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
    destruct (erange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
    destruct (Z.leb lo mid && Z.ltb mid hi)%bool.
    2: { (* [comment removed for export] *)
         pose proof (erange_sound SEGS E _ (kn cs) e lo hi (co_know _ _ _ _ _ HC) Hr) as Hb.
         destruct (Z.leb_spec hi mid) as [Hle|Hgt]; [exact (SAME k1 _ s Hc Hsg1 HC) | exact (SAME k2 _ s Hc Hsg2 HC)]. }
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange e lo mid :: kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange e (mid+1) hi :: kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
    injection Hc as <-. cbn [sd].
    destruct (split_sound cs e mid lo hi E R FULL model HC Hr) as [HCl HCr].
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) mid) as [Hle|Hgt].
    + exact (SAME k1 _ s1 H1 Hsg1 (HCl Hle)).
    + exact (SAME k2 _ s2 H2 Hsg2 (HCr ltac:(lia))).
  - (* [comment removed for export] *)
    apply andb_prop in Hsg as [Hsg1 Hsg2].
    destruct (erange (kn cs) ce) as [[lo hi]|] eqn:Hr; [|discriminate].
    destruct (Z.leb lo cmid && Z.ltb cmid hi)%bool.
    2: { cbn [negb] in Hc. destruct (Z.leb hi cmid); [exact (SAME ck1 _ s Hc Hsg1 HC) | exact (SAME ck2 _ s Hc Hsg2 HC)]. }
    cbn [negb] in Hc. cbv zeta in Hc.
    destruct (split_sound cs ce cmid lo hi E R FULL model HC Hr) as [HCl HCr].
    destruct (kn_contra (kn (set_kn cs (KRange ce lo cmid :: kn cs)))) eqn:Hk1.
    { destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
      - exfalso. exact (kn_contra_sound E _ _ (co_know _ _ _ _ _ (HCl Hle)) Hk1).
      - exact (SAME ck2 _ s Hc Hsg2 (HCr ltac:(lia))). }
    destruct (kn_contra (kn (set_kn cs (KRange ce (cmid + 1) hi :: kn cs)))) eqn:Hk2.
    { destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
      - exact (SAME ck1 _ s Hc Hsg1 (HCl Hle)).
      - exfalso. exact (kn_contra_sound E _ _ (co_know _ _ _ _ _ (HCr ltac:(lia))) Hk2). }
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce lo cmid :: kn cs)) ck1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce (cmid+1) hi :: kn cs)) ck2) as [s2|] eqn:H2; [|discriminate].
    destruct (shape_eqb s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-. apply shape_eqb_eq in Hse. subst s2.
    destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
    + exact (SAME ck1 _ s1 H1 Hsg1 (HCl Hle)).
    + exact (SAME ck2 _ s1 H2 Hsg2 (HCr ltac:(lia))).
  - (* [comment removed for export] *)
    apply andb_prop in Hsg as [Hsg1 Hsg2].
    destruct (node_casedisj cs db1 db2) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa dk1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb dk2) as [s2|] eqn:H2; [|discriminate].
    destruct (shape_eqb s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-. apply shape_eqb_eq in Hse. subst s2.
    destruct (casedisj_sound cs db1 db2 csa csb E R FULL model HC Hn) as [[HC' Hpc]|[HC' Hpc]]; rewrite <- Hpc.
    + exact (SAME dk1 _ s1 H1 Hsg1 HC').
    + exact (SAME dk2 _ s1 H2 Hsg2 HC').
  - (* [comment removed for export] *)
    destruct (node_shdisj A cs sb1 sn1 sb2 sn2) as [cs1|] eqn:Hn; [|discriminate].
    destruct (shdisj_sound cs sb1 sn1 sb2 sn2 cs1 E R FULL model HC Hn) as [HC' Hpc]. rewrite <- Hpc.
    exact (SAME k _ s Hc Hsg HC').
  - (* [comment removed for export] *)
    destruct (kn_contra (kn cs)) eqn:Hk; [|discriminate]. exfalso.
    exact (kn_contra_sound E _ (kn cs) (co_know _ _ _ _ _ HC) Hk).
  - (* [comment removed for export] *)
    destruct (fact_ok (kn cs) K) eqn:Hf; [|discriminate].
    exact (SAME k _ s Hc Hsg (fact_sound E cs R FULL model K HC Hf)).
  - (* [comment removed for export] *)
    destruct (node_join SEGS cs jb joff jn) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_join_sound jb joff jn cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hc Hsg).
  - (* [comment removed for export] *)
    exact (SAME k _ s Hc Hsg (forget_sound E cs R FULL model ixs HC)).
  - (* [comment removed for export] *)
    assert (Hpc : pc (node_droprange cs db dn) = pc cs) by (unfold node_droprange; destruct (split_lit db); reflexivity).
    rewrite <- Hpc. exact (SAME k _ s Hc Hsg (droprange_sound E cs R FULL model db dn HC)).
  - (* [comment removed for export] *)
    rewrite <- (pc_set_kn cs (kn_keep (kn cs) gws)).
    exact (SAME k _ s Hc Hsg (cs_ok_set_kn E cs R FULL model _ HC (know_ok_filter E _ _ (kn cs) (co_know _ _ _ _ _ HC)))).
  - (* [comment removed for export] *)
    destruct (node_bump cs bm) as [cs1|] eqn:Hn; [|discriminate].
    destruct (bump_sound E cs R FULL model bm cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME k _ s Hc Hsg HC1).
  - (* [comment removed for export] *)
    destruct (node_havoc nx0 cs hrs) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havoc_sound E cs R FULL model hrs cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT k cs1 s Hc Hsg E' R FULL model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_havocbig nx0 cs hbK) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havocbig_sound E cs R FULL model hbK cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT k cs1 s Hc Hsg E' R FULL model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_fresh nx0 cs r logc fb) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_fresh_sound_pf r logc fb cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hc Hsg).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_sys A nx0 y cs) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_sys_sound y cs cs1 E R FULL model); [exact HC | exact Hec | exact Hn |]. exact (CONT k cs1 s Hc Hsg).
  - (* [comment removed for export] *)
    apply andb_prop in Hsg as [Hsg1 Hsg2].
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mmap2 A nx0 LIMIT cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa ma) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb mb) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-.
    eapply srz_conseq; [| apply sd_salt2; exact HD].
    eapply (node_mmap2_sound cs csa csb E R FULL model); [exact HC | exact Hec | exact Hn | exact (CONT0 ma csa sa H1 Hsg1) | exact (CONT mb csb sb H2 Hsg2)].
  - (* [comment removed for export] *)
    apply andb_prop in Hsg as [Hsg Hsg3]. apply andb_prop in Hsg as [Hsg1 Hsg2].
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mmapin A LIMIT false cs) as [[[csa csb] cscs]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa ia) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb ib) as [sb|] eqn:H2; [|discriminate].
    destruct (check_all A (CHECK bfuel fuel lc) ic cscs) as [sc|] eqn:H3; [|discriminate].
    injection Hc as <-.
    pose proof (proj2 (check_all_ok _ _ _ _ H3)) as Hall.
    eapply srz_conseq; [| eapply t_eq_trans; [| apply sd_salt2; exact HD]; apply t_eq_alt2; [apply t_eq_refl' | apply sd_salt2; exact HD]].
    eapply (node_mmapin_sound cs csa csb cscs E R FULL model);
      [exact HC | exact Hec | exact Hn | exact (CONT0 ia csa sa H1 Hsg1) | exact (CONT ib csb sb H2 Hsg2) |].
    intros csc E' R' FULL' model' Hin. exact (CONT0 ic csc sc (Hall csc Hin) Hsg3 E' R' FULL' model').
  - (* [comment removed for export] *)
    apply andb_prop in Hsg as [Hsg1 Hsg2].
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mprotect2 A LIMIT cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa qa) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb qb) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-.
    eapply srz_conseq; [| apply sd_salt2; exact HD].
    eapply (node_mprotect2_sound cs csa csb E R FULL model); [exact HC | exact Hec | exact Hn | exact (CONT0 qa csa sa H1 Hsg1) | exact (CONT qb csb sb H2 Hsg2)].
  - (* [comment removed for export] *)
    apply andb_prop in Hsg as [Hsg1 Hsg2].
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_brk2 A LIMIT cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa ka) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb kb) as [sb|] eqn:H2; [|discriminate].
    destruct (shape_le sb sa) eqn:Hle; [|discriminate].   (* [comment removed for export] *)
    injection Hc as <-.
    eapply srz_conseq; [| apply sd_salt2; exact HD].
    eapply (node_brk2_sound cs csa csb E R FULL model); [exact HC | exact Hec | exact Hn | exact (CONT ka csa sa H1 Hsg1) | exact (CONT kb csb sb H2 Hsg2) |].
    exact (shape_le_sound _ E (m_fs model) sb sa HD Hle).
  - (* [comment removed for export] *)
    destruct (node_x SEGS A nx0 x args cs) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_x_sound x args cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hc Hsg).
  - (* [comment removed for export] *)
    destruct (XN xid xargs cs) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_ext_sound xid xargs cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hc Hsg).
  - (* [comment removed for export] *)
    destruct (XE eid eargs cs) as [[[fd ps] cs1]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc cs1 k) as [s1|] eqn:H1; [|discriminate]. injection Hc as <-. cbn [sd].
    eapply (node_emit_sound eid eargs cs fd ps cs1 E R FULL model); [exact HC | exact Hn | apply sd_has_nil; exact HD |]. exact (CONT k cs1 s1 H1 Hsg).
  - (* [comment removed for export] *)
    apply andb_prop in Hsg as [Hsg1 Hsg2].
    destruct (XB bid bargs cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa kb1) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb kb2) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-. cbn [sd].
    eapply (node_ext2_sound bid bargs cs csa csb E R FULL model); [exact HC | exact Hn | exact (CONT0 kb1 csa sa H1 Hsg1) | exact (CONT kb2 csb sb H2 Hsg2)].
  - (* [comment removed for export] *)
    apply andb_prop in Hsg as [Hsgb Hsgk].
    destruct (loop_ok nx0 cs lJ lN linv) as [nhi|] eqn:Hlo; [|discriminate].
    destruct (Z.eqb (pc linv) (pc cs) && entails_h A (Datatypes.S lJ) (nxt linv) cs (inst linv lJ (ELit 0)))%bool eqn:Ht; [|discriminate].
    apply andb_prop in Ht as [Hpc Hent]. apply Z.eqb_eq in Hpc.
    destruct (CHECK bfuel fuel (Some (LC (pc cs) (inst linv lJ (eaddz (EVar lJ) 1)) (Datatypes.S lJ) (nxt linv))) (loop_body_state lJ lN nhi linv) lbody) as [sb|] eqn:Hbody; [|discriminate].
    destruct sb; try discriminate. rename Hc into Hk.
    destruct (loop_ok_facts cs lJ lN linv nhi Hlo) as (Ffr & FJ & FJh & Flog & Flen & FvN & FxN & Fnhi).
    destruct (fresh_ok_parts cs Ffr) as (_ & _ & _ & _ & _ & _ & Fle).
    pose proof (xhi_sound SEGS E _ (kn cs) lN nhi (co_know _ _ _ _ _ HC) FxN) as HNv.
    set (Nv := bv_unsigned (edenot E lN)) in *. pose proof (u64_range (edenot E lN)) as RN. fold Nv in RN.
    set (D0 := sd D E (m_fs model) s).
    assert (HD0 : D0 []) by (apply sd_has_nil; exact HD).
    set (h := pc cs) in *.
    (* [comment removed for export] *)
    assert (Q : forall m j E' R' F' m', j = Nv - Z.of_nat m -> 0 <= j -> env_agree (nxt cs) E E' ->
               cs_ok E' (inst linv lJ (ELit j)) R' F' m' -> m_fs m' = m_fs model ->
               srealizes SEGS (cfg R' h F' m') D0).
    { induction m as [|m IHm]; intros j E' R' F' m' Hj Hj0 Hag HCj Hfs.
      - (* [comment removed for export] *)
        assert (HNe : edenot E' lN = edenot E' (ELit j)).
        { cbn [edenot]. rewrite <- (edenot_agree' (nxt cs) E E' lN Hag FvN). apply bv_eq. rewrite u_small by lia. cbn in Hj. lia. }
        assert (HCN : cs_ok E' (inst linv lJ lN) R' F' m').
        { apply (proj2 (cs_ok_inst E' lJ lN linv R' F' m' ltac:(lia) Flog)). rewrite HNe.
          apply (proj1 (cs_ok_inst E' lJ (ELit j) linv R' F' m' ltac:(lia) Flog)). exact HCj. }
        unfold D0. rewrite (sd_agree D E E' (m_fs model) s ltac:(eapply env_agree_le; [exact Hag | exact Fle]) (check_vars _ _ _ _ _ _ Hk)).
        rewrite <- Hfs. replace h with (pc (inst linv lJ lN)) by (unfold h; rewrite pc_inst; exact Hpc).
        apply (IH bfuel lc lk _ s Hk Hsgk E' R' F' m' D HCN); [|exact HD].
        rewrite Hfs. eapply LCOK_agree; [exact HL | exact Hg | exact Hag].
      - (* [comment removed for export] *)
        set (E'' := upd E' lJ (Z_to_bv 64 j)).
        assert (Hjlt : j < Nv) by lia.
        assert (HCinv : cs_ok E'' linv R' F' m').
        { unfold E''. replace (Z_to_bv 64 j) with (edenot E' (ELit j)) by reflexivity.
          apply (proj1 (cs_ok_inst E' lJ (ELit j) linv R' F' m' ltac:(lia) Flog)). exact HCj. }
        assert (Hag'' : env_agree (nxt cs) E E'').
        { eapply env_agree_trans; [exact Hag|]. eapply env_agree_le; [apply upd_agree | exact FJ]. }
        assert (HNE'' : edenot E'' lN = edenot E lN) by (symmetry; eapply (edenot_agree' (nxt cs)); [exact Hag'' | exact FvN]).
        assert (HJ'' : ev E'' lJ = Z_to_bv 64 j) by (unfold E''; apply upd_at).
        assert (HCb : cs_ok E'' (loop_body_state lJ lN nhi linv) R' F' m').
        { unfold loop_body_state, add_kn. apply cs_ok_set_kn; [exact HCinv|]. apply Forall_app. split; [|exact (co_know _ _ _ _ _ HCinv)].
          constructor; [|constructor; [|constructor]]; cbn [kentry_ok edenot].
          - rewrite HJ'', u_small by lia. lia.
          - unfold esub. rewrite mkAlu_denot, u_sub64. cbn [edenot]. rewrite HNE'', HJ''. fold Nv. rewrite u_small by lia.
            rewrite Z.mod_small by lia. lia. }
        replace h with (pc (loop_body_state lJ lN nhi linv)) by exact Hpc.
        refine (IH bfuel _ lbody _ SNext Hbody Hsgb E'' R' F' m' D0 HCb _ HD0).
        (* [comment removed for export] *)
        cbn [LCOK]. split.
        { split; [lia|]. split; [lia|]. unfold inst. cbn [a_ss s_regs mk_ss]. rewrite length_map. exact Flen. }
        intros E3 R3 F3 m3 Hag3 HC3 Hfs3.
        assert (HJ3 : ev E3 lJ = Z_to_bv 64 j) by (rewrite <- HJ''; symmetry; apply (proj1 Hag3); lia).
        assert (Hnext : edenot E3 (eaddz (EVar lJ) 1) = Z_to_bv 64 (j + 1)).
        { unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. rewrite HJ3. apply bv_eq. rewrite u_add64, !u_small by lia. rewrite Z.mod_small by lia. reflexivity. }
        set (E4 := upd E3 lJ (Z_to_bv 64 (j + 1))).
        apply (IHm (j + 1) E4 R3 F3 m3); [lia | lia | | | rewrite Hfs3; exact Hfs].
        + eapply env_agree_trans; [exact Hag''|]. eapply env_agree_trans; [eapply env_agree_le; [exact Hag3 | lia]|].
          eapply env_agree_le; [apply upd_agree | exact FJ].
        + apply (proj2 (cs_ok_inst E4 lJ (ELit (j + 1)) linv R3 F3 m3 ltac:(lia) Flog)).
          unfold E4. cbn [edenot]. rewrite upd_upd. rewrite <- Hnext.
          apply (proj1 (cs_ok_inst E3 lJ (eaddz (EVar lJ) 1) linv R3 F3 m3 ltac:(lia) Flog)). exact HC3. }
    (* [comment removed for export] *)
    destruct (entails_h_sound (Datatypes.S lJ) (nxt linv) E cs (inst linv lJ (ELit 0)) R FULL model HC Hent ltac:(lia)
                ltac:(unfold inst; cbn [a_ss s_regs mk_ss]; rewrite length_map; exact Flen)) as (E1 & Hag1 & _ & HC1 & _).
    unfold D0 in Q. apply (Q (Z.to_nat Nv) 0 E1 R FULL model); [lia | lia | eapply env_agree_le; [exact Hag1 | lia] | exact HC1 | reflexivity].
  - (* [comment removed for export] *)
    destruct lc as [[h nx lo hi|j' js' sk' b' lo']|]; [|discriminate|discriminate].
    destruct (Z.eqb (pc cs) h && entails_h A lo hi cs nx)%bool eqn:Ht; [|discriminate]. injection Hc as <-. cbn [sd].
    apply andb_prop in Ht as [Hpc Hent]. apply Z.eqb_eq in Hpc.
    cbn [LCOK] in HL. destruct HL as [(Hn0 & Hlh & Hlen) HL]. cbn [lc_guard lc_bnd] in Hg. apply Nat.leb_le in Hg.
    destruct (entails_h_sound lo hi E cs nx R FULL model HC Hent Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc').
    rewrite Hpc. exact (HL E' R FULL model Hag HC' eq_refl).
  - (* [comment removed for export] *)
    destruct (HS h) as [ch|] eqn:Hh; [|discriminate].
    destruct (entails cs ch) eqn:He; [|discriminate]. injection Hc as <-. cbn [sd].
    destruct (entails_sound E cs ch R FULL model HC He) as [HC' Hpc].
    rewrite <- Hpc. exact (HS_sound h ch Hh E R FULL model HC').
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_exit cs) as [code|] eqn:Hn; [|discriminate]. injection Hc as <-. cbn [sd].
    eapply node_exit_sound; eassumption.
  - (* [comment removed for export] *)
    discriminate Hsg.
  - (* [comment removed for export] *)
    destruct (node_fog cs fi fsz) as [cs1|] eqn:Hn; [|discriminate].
    destruct (fog_sound E cs R FULL model fi fsz cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME fk _ s Hc Hsg HC1).
  - (* [comment removed for export] *)
    destruct (node_fognew cs gi gsz) as [cs1|] eqn:Hn; [|discriminate].
    destruct (fognew_sound E cs R FULL model gi gsz cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME gk _ s Hc Hsg HC1).
  - (* [comment removed for export] *)
    destruct (node_ghost LIMIT cs gb gn) as [cs1|] eqn:Hn; [|discriminate].
    destruct (ghost_sound E cs R FULL model gb gn cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME gk2 _ s Hc Hsg HC1).
  - (* [comment removed for export] *)
    destruct (node_unvis A cs ub un) as [cs1|] eqn:Hn; [|discriminate].
    destruct (unvis_sound E cs R FULL model ub un cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME uk _ s Hc Hsg HC1).
  - (* [comment removed for export] *)
    destruct (node_havocbrk nx0 cs hlo hhi) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havocbrk_sound E cs R FULL model hlo hhi cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT hk cs1 s Hc Hsg E' R FULL model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_intro nx0 cs ilo ihi) as [cs1|] eqn:Hn; [|discriminate].
    destruct (intro_sound E cs R FULL model ilo ihi cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT ik cs1 s Hc Hsg E' R FULL model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (branch_probe IT cs) as [e|] eqn:Hbp; [|discriminate].
    destruct (erange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    destruct (Z.ltb hi 1 || Z.ltb 0 lo)%bool eqn:Hdec.
    { (* [comment removed for export] *)
      destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) cs) as [cs1|] eqn:Hrb; [|discriminate].
      destruct (Z.eqb (pc cs1) djp); [|discriminate].
      eapply run_block_gc_sound; [exact Hgb | exact Hrb | exact HC |].
      intros E' R' FULL' model' Hag HC1 Hfs. exact (CONT dk cs1 s Hc Hsg E' R' FULL' model' Hag HC1 Hfs). }
    cbv zeta in Hc.
    destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e lo 0 :: kn cs))) as [ca|] eqn:Hra; [|discriminate].
    destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e 1 hi :: kn cs))) as [cb|] eqn:Hrb; [|discriminate].
    destruct (node_diamond_join A nx0 (nxt cs) djp drs ca cb) as [csj|] eqn:Hj; [|discriminate].
    destruct (split_sound cs e 0 lo hi E R FULL model HC Hr) as [HCl HCr].
    destruct (diamond_join_sound (nxt cs) djp drs ca cb csj Hj) as [Ja Jb].
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
    + rewrite <- (pc_set_kn cs (KRange e lo 0 :: kn cs)).
      eapply run_block_gc_sound; [exact Hgb | exact Hra | exact (HCl Hle) |].
      intros E' R' FULL' model' [Hag0 Hag1] HC1 Hfs.
      destruct (Ja E' R' FULL' model' HC1) as (E'' & [Hag2a Hag2b] & HC2 & Hpc2). rewrite <- Hpc2.
      change (env_agree (nxt cs) E E') in Hag1.
      exact (CONT dk csj s Hc Hsg E'' R' FULL' model'
               (conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) HC2 Hfs).
    + rewrite <- (pc_set_kn cs (KRange e 1 hi :: kn cs)).
      eapply run_block_gc_sound; [exact Hgb | exact Hrb | exact (HCr ltac:(lia)) |].
      intros E' R' FULL' model' [Hag0 Hag1] HC1 Hfs.
      destruct (Jb E' R' FULL' model' HC1) as (E'' & [Hag2a Hag2b] & HC2 & Hpc2). rewrite <- Hpc2.
      change (env_agree (nxt cs) E E') in Hag1.
      exact (CONT dk csj s Hc Hsg E'' R' FULL' model'
               (conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) HC2 Hfs).
  - (* [comment removed for export] *)
    destruct (node_rename _ cs rnm) as [cs1|] eqn:Hn; [|discriminate].
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    destruct (rename_sound _ E cs R FULL model rnm cs1 Hgb HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    rewrite (sd_agree D E E' (m_fs model) s (env_agree_le _ _ _ _ Hag Hgb) (check_vars _ _ _ _ _ _ Hc)).
    eapply IH; [exact Hc | exact Hsg | exact HC1 | eapply LCOK_agree_gb; [exact HL | exact Hag] | exact HD].
  - (* [comment removed for export] *)
    destruct (node_compact _ cs) as [cs1|] eqn:Hn; [|discriminate].
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    destruct (compact_sound _ E cs R FULL model cs1 Hgb HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    rewrite (sd_agree D E E' (m_fs model) s (env_agree_le _ _ _ _ Hag Hgb) (check_vars _ _ _ _ _ _ Hc)).
    eapply IH; [exact Hc | exact Hsg | exact HC1 | eapply LCOK_agree_gb; [exact HL | exact Hag] | exact HD].
  - (* [comment removed for export] *)
    apply andb_prop in Hsg as [Hsga Hsgk].
    destruct (via_ok nx0 cs vjs vlo) eqn:Hv; [|discriminate].
    destruct (CHECK bfuel fuel lc vjs vk) as [sk|] eqn:Hk; [|discriminate].
    unfold via_ok in Hv. repeat match type of Hv with (_ && _)%bool = true => apply andb_prop in Hv as [Hv ?X] end.
    match goal with Hl : match s_log (a_ss vjs) with _ => _ end = true |- _ => clear Hl end.
    match goal with Hl : Nat.eqb (length _) 32 = true |- _ => apply Nat.eqb_eq in Hl; rename Hl into Hlen end.
    repeat match goal with Hl : Nat.leb _ _ = true |- _ => apply Nat.leb_le in Hl end.
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    assert (Hgb' : (match lc with Some c => lc_bnd c | None => nx0 end <= nxt cs)%nat).
    { destruct lc as [c|]; [apply Nat.leb_le; exact Hg | lia]. }
    apply (IH bfuel (Some (JC vj vjs sk (nxt cs) vlo)) vka cs s Hc Hsga E R FULL model D HC); [|exact HD].
    cbn [LCOK]. split; [split; [lia | split; [lia | exact Hlen]]|].
    intros E' R' F' m' Hag HC' Hfs. rewrite <- Hfs.
    apply (IH bfuel lc vk vjs sk Hk Hsgk E' R' F' m' D HC'); [|exact HD].
    rewrite Hfs. eapply LCOK_agree_gb; [exact HL|]. eapply env_agree_le; [exact Hag | exact Hgb'].
  - (* [comment removed for export] *)
    destruct lc as [[h nx lo hi|j' js' sk' b' lo']|]; [discriminate| |discriminate].
    destruct (Nat.eqb mj j' && Z.eqb (pc cs) (pc js') && shape_vars_lt nx0 sk' && entails_h A lo' (nxt js') cs js')%bool eqn:Ht; [|discriminate].
    injection Hc as <-.
    apply andb_prop in Ht as [Ht Hent]. apply andb_prop in Ht as [Ht Hsv]. apply andb_prop in Ht as [_ Hpc]. apply Z.eqb_eq in Hpc.
    cbn [LCOK] in HL. destruct HL as [(Hn0 & Hbl & Hlen) HJ].
    destruct (entails_h_sound lo' (nxt js') E cs js' R FULL model HC Hent ltac:(clear -Hn0 Hbl; lia) Hlen) as (E' & Hag & _ & HC' & Hpc').
    assert (Hn0l : (nx0 <= lo')%nat) by lia.
    rewrite (sd_agree D E E' (m_fs model) sk' (env_agree_le nx0 lo' E E' Hag Hn0l) Hsv). rewrite Hpc.
    exact (HJ E' R FULL model (env_agree_le _ _ _ _ Hag Hbl) HC' eq_refl).
  - (* [comment removed for export] *)
    destruct (node_abstractcell A cs ab an) as [cs1|] eqn:Hn; [|discriminate].
    destruct (abstractcell_sound E cs R FULL model ab an cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME ak _ s Hc Hsg HC1).
  - (* [comment removed for export] *)
    destruct (node_havocwords nx0 cs hws) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havocwords_sound E cs R FULL model hws cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT hwk cs1 s Hc Hsg E' R FULL model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_respell cs rsr rse) as [cs1|] eqn:Hn; [|discriminate].
    destruct (respell_sound E cs R FULL model rsr rse cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME rsk _ s Hc Hsg HC1).
  - (* [comment removed for export] *)
    apply andb_prop in Hsg as [Hsg Hsg3]. apply andb_prop in Hsg as [Hsg1 Hsg2].
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mmapin A LIMIT false cs) as [[[csa csb] cscs]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa iha) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb ihb) as [sb|] eqn:H2; [|discriminate].
    destruct (check_all A (CHECK bfuel fuel lc) ihc cscs) as [sc|] eqn:H3; [|discriminate].
    injection Hc as <-.
    pose proof (proj2 (check_all_ok _ _ _ _ H3)) as Hall.
    eapply srz_conseq; [| eapply t_eq_trans; [| apply sd_salt2; exact HD]; apply t_eq_alt2; [apply t_eq_refl' | apply sd_salt2; exact HD]].
    eapply (node_mmapin_sound cs csa csb cscs E R FULL model);
      [exact HC | exact Hec | exact Hn | exact (CONT0 iha csa sa H1 Hsg1) | exact (CONT ihb csb sb H2 Hsg2) |].
    intros csc E' R' FULL' model' Hin. exact (CONT0 ihc csc sc (Hall csc Hin) Hsg3 E' R' FULL' model').
Qed.

End Sound.
End APS.
