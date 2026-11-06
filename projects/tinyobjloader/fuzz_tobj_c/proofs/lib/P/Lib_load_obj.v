(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sstate"; "ss_next"; "sobj"; "SVar"; "ss_facts"; "smatch"; "sprop"; "holds"; "SLit"; "obj_range"; "sv_eqb"; "SPBranch"; "SPNot"; "agree_below"; "sprop_eqb"; "sv_below"; "@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "true"; "pair"; "Some"; "fst"; "option"; "cons"; "nat"; "snd"; "nil"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "LQ"; "SP"; "LQJ"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs"; "NP"; "P0_lo"; "Pre_lo"; "tv0"; "tv_ar"; "FUEL"; "K_desd"; "X_des"; "am0d"; "amL"; "cps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "agree_vals"; "jpost"; "import_post"; "pos_add_nat"; "J_ofP"; "call_check"; "call_checkP"; "call_link"; "call_linkP"; "import_okP"; "import_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "JGA_pre"; "amode"; "PostsCA"; "JGA"; "AHead"; "PDAh"; "ANone"; "am_below"; "hdr_obj"; "JLGA"; "ameas"; "ejcertA"; "nodeA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Stdlib.Lists.List"; "In"; "existsb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "L_free"; "L_malloc_null"; "L_malloc_ok"; "Pre_free"; "Pre_malloc"; "V_RES"; "ok_sideK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs"; "P0_hf"; "HF_P"; "Pre_hf"; "tv_pre"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "uleq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_glue"; "Posts_lo"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_after"; "call_checkT"; "pclF"; "robjs_check"; "tv_below"; "malloc_contracts"; "malloc_contracts_ex"; "remove_nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup"; "P0_ad"; "PDA_ad"; "Pre_ad"; "ahd"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index"; "P0_bli"; "PD_bli_darr"; "Pre_bli0"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize_shape"; "P0_fs"; "PDA_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_vn"; "P0_hvn"; "PD_hvn"; "Pre_hvn"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.Lib_handle_vt"; "P0_hvt"; "PD_hvt"; "Pre_hvt"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_intern_rest"; "P0_ir"; "PDA_ir"; "Pre_ir"; "ahd"; "tv0";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_nodes"; "cutsE"; "exitsE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_next_token"; "Pre_nt"; "Posts_nt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.Lib_opt_push1"; "P0_op"; "PD_op"; "Pre_op"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.Lib_opt_push3w"; "P0_op"; "PD_op"; "Pre_op"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_double"; "Pre_sd"; "Posts_sd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_int"; "Pre_si"; "Posts_si"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "jnode"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose"; "P0_bd"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "PDAnone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVx"; "emeasZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_builder_dispose"; "Pre_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_defs"; "Pre_fs"; "ahd"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs"; "Pre_hl"; "Pre_hp"; "tvL_pre"; "tvP_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1"; "PD_bd"; "PD_hf"; "PD_hl"; "PD_hp"; "PD_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve"; "P0_vr"; "Pre_vr"; "tv0"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjUnbase ObjXform TobjJV TobjJVx TobjArena TobjJVA TobjJVAx TobjJVAy BuilderDispose ArenaDestroy.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle_f OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_intern_rest OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_next_token OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize_shape OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_builder_dispose.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_c8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_sites2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G4.Lib_load_obj_c1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G5.Lib_load_obj_c2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G4.Lib_load_obj_c3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G3.Lib_load_obj_c4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G4.Lib_load_obj_c5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G6.Lib_load_obj_c6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G7.Lib_load_obj_c7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_c8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G7.Lib_load_obj_c9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G6.Lib_load_obj_c10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G3.Lib_load_obj_c11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G5.Lib_load_obj_x1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G5.Lib_load_obj_x2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G6.Lib_load_obj_x3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index_darr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr.

Lemma triple_skip : ltac2:(tb__ "0|0|
S36OF_;S35S35S36R3R1A1R3R2A1F_;Fw;S38S0R4R3R2A4F_;FQ';FP;Fok;").
Proof. intros ok P Q' H. eapply triple_conseq; [exact H | intros w Hw; exact Hw | apply triple_refl]. Qed.
Lemma etriple_skip : ltac2:(tb__ "0|0|
S35S35S36R3R1A1R3R2A1F_;Fw;S37S0R3R2A3F_;FQ';FP;").
Proof. intros P Q' H w Hw. exists w. split; [apply wsteps_refl | exact (H w Hw)]. Qed.

Section Sum.
Variable Kc : ltac2:(tb__ "0|0|
S15S53A1S52OF_;F_;").
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segs C_P.

Let nA : ltac2:(tb__ "0|0|
S16S5S16S15S16S4S4A2A1S46A2A2Sa5Fn;") := ltac2:(tb__ "0|0|
S51S0S1S2aVKc;Vrho0;S2bVFB;A1VFB;A7").
Let JGv (tv : list (sv * sv)) (am : amode) : jpred := ltac2:(tb__ "0|0|
S48S0S1S2aVKc;Vrho0;S2bVFB;A1VFB;Vtv;Vam;A9").
Let Q : assn := ltac2:(tb__ "0|0|
S39S0S2aVrho0;S6eVKc;VFB;A2A4").

Lemma ejcert_ok : ltac2:(tb__ "0|0|
S27S17S50S0S2aS2fS34S2aS93S94A7S18A3").
Proof using .
  apply (ejcertA_of_cuts segs NP FUEL cps NP cutsE exitsE). intros i n H.
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_Pre_lo |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_mnull |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_mok |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_A4 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_loop |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_skip |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_tok |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_disp102 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_disp103 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_disp104 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_disp105 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_disp106 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_disp107 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_disp108 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_disp109 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_disp110 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_disp111 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_disp112 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_disp113 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_disp114 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_disp115 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_disp116 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_disp117 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_disp118 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_dfl |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_um2 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_um3 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_um4 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_um5 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_um6 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_mm2 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_mm3 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_mm4 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_mm5 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_mm6 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_us1 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_us2 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_hf1 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_hf2 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_hl1 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_hl2 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_hp1 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_vn1 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_vn2 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_vn3 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_vt1 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_vt2 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_ir0 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_ir1 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_fs2a |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_fs2b |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_fs2c |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_fs2d |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_nt0 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_nt1 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_s2 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_si0 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_si1 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd0n |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd0a |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd0b |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd0c |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd1n |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd1a |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd1b |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd1c |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd2n |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd2a |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd2b |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd2c |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd3n |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd3a |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd3b |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd3c |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd4n |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd4a |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd4b |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd4c |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd5n |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd5a |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd5b |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd5c |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd6n |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd6a |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd6b |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd6c |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd7n |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd7a |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd7b |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_sd7c |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_avk |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_avf |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_avg |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_op1 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_op3 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_fsa |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_fsb |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_fsc |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_fsd |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_col |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_cvk |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_cvf |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_cvg |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_fin0 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_fin1 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_fin2 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_fin3 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_fin4 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_fin5 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_fin6 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_adf0 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_ado0 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_adf1 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_ado1 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_adf2 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_ado2 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_adf3 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_ado3 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_adf4 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_ado4 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_adf5 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_ado5 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_adf6 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_ado6 |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_bd |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_bd |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_fl |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_chk |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_K_desd |].
  destruct i as [|i]; [cbn [cutsE nth_error] in H; injection H as <-; exact ec_T_fa |].
  destruct i; cbn [cutsE nth_error] in H; discriminate.
Qed.

Section SumT.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S23S5S3S35S71SbScR2A1S9R3A1A3VTR;S22S0R5R4R3A4R2A2M0F_;G0F_;FQ';Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q') -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S35S35S35S36R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_post : ltac2:(tb__ "0|0|
S35S35S35S36R3R1A1R3R2A1F_;Fw;VTR;R4R3A2VTR;R5R3A2F_;F_;FQ';FQ;FP;").
Hypothesis TR_skip : ltac2:(tb__ "0|0|
S35S35S36R3R1A1R3R2A1F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn), (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS35S35R3VTR;R3R2A2F_;VTR;S36S28R5R4R1A1A2Lw;R2A2F_;FQ';FP;FX;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S23S23S5S5S62S15S7A1M0S15S16S5S3bA2M1A1S35S3S27S1cG0A1S6dR7R6R5A3S1aG0R4A2A3S27S17S40R8R7R6R5S72G1S5S1bS5S3bA2R4A4A5S18A3S3VTR;S22S0RbR9R1A4S39S0S6R9A1R1R6A4A2Frho1;S15S53A1M2S67S52SaS0R7RdS19G2S68R3S69R2R1A2A4A4R10R8R4R2A3R10S61S60R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S5S3bG2S67S52S3G2S67S52S54G1S19S5S3bR9R8A4R10A3SaS0RfR15S19G2S68R8S69R7R6A2A4A4R18R10R9R7A3S3aS6R16A1S61S60R11R14R9A3R15A2R7A3SaS0R8RdS19G2S68R7S69R6R5A2A4A4RdS61S60R13R16RbA3R17A2R9R8R6A4S28S43R14RcR17R18R19RfRaA7S3S42R15RdR18R19R1aR1bR10R1RbA9VTR;S22S0S3eR10S61S60R16R19ReA3R1aA2RcA3S3cR1aS6R1bA1R11S6R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S22S0ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_callJ : ltac2:(tb__ "0|3|
S23S23S23S23S5S5S62S15S7A1M0S15S6aA1S35S3S27S1cG0A1S6dR7R6R5A3S1aG0R4A2A3S27S17S3fR8R7R6R5R4A5S18A3S3VTR;S22S0RdR9R1A4S26S0RcS6R9A1R1R6A5A2Frho1;S15S53A1M1S67S52SaS0R7RdS19G1S68R3S69R2R1A2A4A4R12R8R4R2A3R12S61S60R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S6aS3S3G1S67S52G1S52S54S6aR8RfA3SaS0ReR14S19G1S68R6S69R5R4A2A4A4R19RfR7R5A3S41R10R7R13R14R15R16S6bRbA1RaR9A9R19RaR6R5A3R19RcR7R6A3F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S6aS3S54S6aR2RaA3S12S6RfA1M2R9R2A3VTR;S22S0R11S3cReG2S6bR4A1S6R10A1RdA5R3A4RbA2F_;F_;Frho';FL;VTR;S22S0R11RdR7A4R8A2F_;F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fs;FPre;FC;FJc';FJp';FJp;FJ;").
Hypothesis C_hf : ltac2:(tb__ "0|1|
S15S16S2S2A2A1S3VTR;S22S0S45S0S1VKc;S63R2A1R2S66S49S8P12bM0A1A1A7S65S64A1R1A4S39S0P12cR1S47S0S1VKc;S63S4aSb4G0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_hl : ltac2:(tb__ "0|1|
S15S16S2S2A2A1S3VTR;S22S0S45S0S1VKc;S63R2A1R2Sb1S49S8P12bM0A1A1A7SafR1A4S39S0P12cR1S47S0S1VKc;S63S4aSb5G0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_hp : ltac2:(tb__ "0|1|
S15S16S2S2A2A1S3VTR;S22S0S45S0S1VKc;S63R2A1R2Sb2S49S8P12bM0A1A1A7Sb0R1A4S39S0P12cR1S47S0S1VKc;S63S4aSb6G0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_vn : ltac2:(tb__ "0|1|
S15S16S2S2A2A1S3VTR;S22S0S45S0S1VKc;S86R2A1R2S89S49S8P63M0A1A1A7S88R1A4S39S0P64R1S47S0S1VKc;S86S4aS87G0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_vt : ltac2:(tb__ "0|1|
S15S16S2S2A2A1S3VTR;S22S0S45S0S1VKc;S8aR2A1R2S8dS49S8P63M0A1A1A7S8cR1A4S39S0P64R1S47S0S1VKc;S8aS4aS8bG0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_vr : ltac2:(tb__ "0|3|
S15S16S2S2A2A1M0S3VTR;S22S0S45S0S1VKc;G0Sb8L_;M1R2A1R2SbaS49S8P63M2A1A1A7Sb9R1A4S39S0P64R1S47S0S1VKc;G1S4aSb7G2A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_op1 : ltac2:(tb__ "0|1|
S15S16S2S2A2A1S3VTR;S22S0S45S0S1VKc;S97R2A1R2S9aS49S8P63M0A1A1A7S99R1A4S39S0P64R1S47S0S1VKc;S97S4aS98G0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_op3 : ltac2:(tb__ "0|1|
S15S16S2S2A2A1S3VTR;S22S0S45S0S1VKc;S9bR2A1R2S9eS49S8P63M0A1A1A7S9dR1A4S39S0P64R1S47S0S1VKc;S9bS4aS9cG0A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_bd : ltac2:(tb__ "0|3|
S15S16S2S2A2A1M0S3VTR;S22S0S45S0S1VKc;G0Sa6L_;M1R2A1R2Sa7U0A1S49S8Pc7M2A1A1A7SabR1A4S39S0Pc8R1S47S0S1VKc;G1S4aSb3G2A2R2A6A4A2Frho1;FFBc;").
Hypothesis C_bli : ltac2:(tb__ "0|0|
S15S16S2S2A2A1S3VTR;S22S0S45S0S1VKc;S80R2A1R2S83S4bA7S82R1A4S39S0P64R1S47S0S1VKc;S80Sa9S81A1R2A6A4A2Frho1;FFBc;").
Hypothesis C_ir : ltac2:(tb__ "0|0|
S15S16S2S2A2A1S3VTR;S22S0S45S0S1VKc;S8eR2A1R2S92S91A7S90R1A4S39S0P64R1S47S0S1VKc;S8eS8fR2A6A4A2Frho1;FFBc;").
Hypothesis C_fs : ltac2:(tb__ "0|0|
S15S16S2S2A2A1S3VTR;S22S0S45S0S1VKc;S84R2A1R2SaeSadA7SacR1A4S39S0Pc8R1S47S0S1VKc;S84S85R2A6A4A2Frho1;FFBc;").
Hypothesis C_ad : ltac2:(tb__ "0|0|
S15S16S2S2A2A1S3VTR;S22S0S45S0S1VKc;S7bR2A1R2S7fS7eA7S7dR1A4S39S0P64R1S47S0S1VKc;S7bS7cR2A6A4A2Frho1;FFBc;").
Hypothesis C_nt : ltac2:(tb__ "0|1|
S15S16S4S4A2A1S46S3S3VTR;S25S0S15S53A1S52S48S0S1S2aVKc;Vrho0;S2bVFB;A1VFB;R6R5R4R2R1AcLmd;Ltr;M0S95R1A4S24S0G0S6S95A1R1S96A5A2Frho1;Frho;Fam;Ftv;").
Hypothesis C_si : ltac2:(tb__ "0|1|
S15S16S4S4A2A1S46S3S3VTR;S25S0S15S53A1S52S48S0S1S2aVKc;Vrho0;S2bVFB;A1VFB;R6R5R4R2R1AcLmd;Ltr;M0Sa1R1A4S24S0G0S6Sa1A1R1Sa2A5A2Frho1;Frho;Fam;Ftv;").
Hypothesis C_sd : ltac2:(tb__ "0|1|
S15S16S4S4A2A1S46S3S3VTR;S25S0S15S53A1S52S48S0S1S2aVKc;Vrho0;S2bVFB;A1VFB;R6R5R4R2R1AcLmd;Ltr;M0S9fR1A4S24S0G0S6S9fA1R1Sa0A5A2Frho1;Frho;Fam;Ftv;").
Hypothesis MALLOCX : ltac2:(tb__ "0|b|
S5S62S15S7A1M0S3S15S16S4S4A2M1A1S46S7S17Fx;S35S27S1cG0A1S6dR8S5cS57A1M2R7A3S1aG0R6A2A3S27S17S74S1S2aR9G2R8R7S1dS5S59S57A1M3S1dS5S5aS57A1M4S20S5A1A3A3A7S18A3S27S17Sa3S2aS6RaA1A2S18A3S27S17S77S6RbA1R7A2S18A3S27S17S4cS6RcA1R7A2S18A3S27S17S14S6RdA1S5fRcPcM5A2A2S18A3S27S4S5fS44RdSa8G4S6ReA1M6A4S5dA2S8S3dG6UaM7A2A1A3S27S17S76S9RfA1RbS21S1eA1S7S17S17L_;S4dRbR1A2S18RaR1A1X17x2Lo;RdA5S18A3S7S2S54S7R2R10A3S27S17RdR3A1S18A3S2bVFB;Vrho0;A2S3aS2aVrho0;R12A3S71SbScR13A1S9R16A1A3S28S6fS1bS2S2SeR14R7A2M8A3R6A2S70R6S1fS2S2G8A3A2A2S75S0S1Vrho0;VFB;R7A5F_;F_;F_;F_;F_;F_;Fa;Fo;S27S17S6cS9R11A1SdZ1A1Z0S5fR10G5A2A4S18A3S3S3aS6R13A1R10R1A3VTR;S22S0S48S0S1S2aVKc;Vrho0;S2bVFB;A1M9VFB;R10RfA9MaS73R14R13R12G3A4R2A4RdA2F_;Frho';S3S3aS6R14A1R11R1A3VTR;S22S0S48S0S1S2aVKc;Vrho0;G9VFB;S1dG1S19S4S4S8S3dS6R15A1G7A2A1S5fR14G5A2A4R11A3R10A9S73R15R14R13G4A4R2A4ReA2F_;Frho';VTR;S22S0GaR14R11A4RdA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ';Fextra;Fam;Ftv;Frho;FR;Fs;FCl;").
Hypothesis FREE : ltac2:(tb__ "0|6|
S5S62S15S7A1M0S3S15S16S4S4A2M1A1S46S1eG1S7S17Fx;S35S27S1cG0A1S6dRaS5bS57A1M2R9A3S1aG0R8A2A3S27S17S74S1S2aRbG2RaR9S1dS5S58S57A1M3S20S5A1A3A7S18A3S27S17Sa3S2aS6RcA1A2S18A3S27S17S77S6RdA1R9A2S18A3S27S17S4cS6ReA1R9A2S18A3S27S1cG1A1S56G1RbR9A3S1aG1R8A2A3S27S17SfS1bS4S4R9A3S5fRfPcA2A2S18A3S27S17SfS1fS4S4RaA3S5fR10PdA2A2S18A3S27S17S55SbS13S11S10Sa4S1bS4S4RbA3SdZ0A1A3A1A1S9R12A1A3S18A3S27S17S76S9R13A1RfS1aS1eRdA2S7S17S17L_;S4dRfR1A2S18RcR1A1X17x2Lo;R11A5S18A3S7S2S54S7R2R14A3S27S17RfR3A1S18A3S2bVFB;Vrho0;A2S3aS2aVrho0;R16A3S71SbScR17A1S9R1aA1A3S28S6fS1bS2S2SeR18R7A2M4A3R6A2S70R6S1fS2S2G4A3A2A2S75S0S1Vrho0;VFB;R7A5F_;F_;F_;F_;F_;F_;Fa;Fo;S3S3aS6R16A1R13R1A3VTR;S22S0S48S0S1S2aVKc;Vrho0;S2bVFB;A1M5VFB;S7aG1R11R13A3R12A9S73R17R16R15G3A4R2A4ReA2F_;Frho';VTR;S22S0S48S0S1S2aVKc;Vrho0;G5VFB;R12R11A9R16R13A4RdA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ';Fextra;Ft;Fi;Fam;Ftv;Frho;FR;Fs;FCl;").
Hypothesis DES : ltac2:(tb__ "0|1|
S3VTR;S22S0S48S0S1S2aVKc;Vrho0;S2bVFB;A1M0VFB;S2eS33A9S31R1A4S36S29S3S3S22S0S48S0S1S2aVKc;Vrho0;G0VFB;S2eS32A9S30R1R2A5Lrho';A2Lw;A2Frho;").
Hypothesis REENTERw : ltac2:(tb__ "0|5|
S5S15S16S4S4A2A1M0S46S2S4S3S2S36S54S16S16S5S16G0S46A2M1A2M2S16S2S4A2M3A2S19G2G3S19S5G1R8S19G0S46R7R6A4A4S19S2S4R5R4A4A4S93A3S28S6fZ0SaaR6R5R4A3M4A2S70G4R3A2A2S22S0S48S0S1S2aVKc;Vrho0;S2bVFB;A1VFB;R9R8A9RaR5R3A5VFAM;R5R4A2F_;F_;F_;Fw;Fb;Frho;FvT;FrT;Fam;Ftv;FT;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S2S2S36S6fR3R2A2VFAM;R4R2A2VFAM;R4R3A2F_;F_;Fw;Fb2;Fb1;").
Hypothesis POST : ltac2:(tb__ "0|1|
S5S15S16S4S4A2A1S46S3S2S54S16S5S3bA2S19S5S3bR5S4eS0S1VKc;S2bVFB;A1M0VFB;R4R3A7A4S6eVKc;VFB;A2A3VTR;S22S0S48S0S1S2aVKc;Vrho0;G0VFB;R5R4A9R6R3A4VFAM;R2A1A2F_;Fb;Frho;Fam;Ftv;FP;").

Lemma exits_okT : ltac2:(tb__ "0|4|
S5S15S16S4S4A2A1M0S46S16S2S4A2M1S3S54S16S16S5S16G0S46A2M2A2M3G1A2S19G3G1S19S5G2R5S19G0S46R4R3A4A4R2A4S94A3VTR;S22S0VJGv;R5R4A2R6R2A4VFAM;S4fS19G3G1S19S5G2R6S19G0S46R5R4A4A4R3A4R2A2A1A2F_;Frho;FrvX;FamX;FtvX;FX;").
Proof using C_ad C_bd C_bli C_fs C_hf C_hl C_hp C_ir C_nt C_op1 C_op3 C_sd C_si C_vn C_vr C_vt DES FAM_mono FREE MALLOCX ML POST REENTERw TR_callJ TR_callP TR_ex TR_exw TR_facts TR_post TR_pre TR_pureh TR_skip.
  pose proof TR_facts as _U0. pose proof TR_ex as _U1. pose proof TR_pre as _U2. pose proof TR_post as _U3. pose proof TR_skip as _U4. pose proof TR_exw as _U5. pose proof TR_pureh as _U6. pose proof TR_callP as _U7. pose proof TR_callJ as _U8. pose proof C_hf as _U9. pose proof C_hl as _U10. pose proof C_hp as _U11. pose proof C_vn as _U12. pose proof C_vt as _U13. pose proof C_vr as _U14. pose proof C_op1 as _U15. pose proof C_op3 as _U16. pose proof C_bd as _U17. pose proof C_bli as _U18. pose proof C_ir as _U19. pose proof C_fs as _U20. pose proof C_ad as _U21. pose proof C_nt as _U22. pose proof C_si as _U23. pose proof C_sd as _U24. pose proof MALLOCX as _U25. pose proof FREE as _U26. pose proof DES as _U27. pose proof REENTERw as _U28. pose proof FAM_mono as _U29. pose proof POST as _U30.
  intros X tvX amX rvX rho Hin. cbn [exitsE In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; injection H as <- <- <- <-.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_E_m Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_P_err Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_X_bli0 Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_X_bliT Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_X_disp Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x1.L_E_hf Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x1.L_E_hl Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x1.L_E_hp Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x1.L_E_vn Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x1.L_E_vt Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x1.L_E_ir Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x1.L_E_fs2 Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x1.L_E_nt Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x1.L_E_si Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x2.L_E_sd0 Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x2.L_E_sd1 Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x2.L_E_sd2 Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x2.L_E_sd3 Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x2.L_E_sd4 Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x2.L_E_sd5 Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x2.L_E_sd6 Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x2.L_E_sd7 Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x2.L_E_av Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x2.L_X_op1 Kc FB rho0); assumption.
  - apply (P.Lib_load__G5.Lib_load_obj_x2.L_E_op3 Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_E_fs Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_E_cv Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_E_ad0 Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_E_ad1 Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_E_ad2 Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_E_ad3 Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_E_ad4 Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_E_ad5 Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_E_ad6 Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_E_bd Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_E_fl Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_X_l0 Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_X_des Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_E_fa Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_X_ok Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_X_err Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_P_ok Kc FB rho0); assumption.
  - apply (P.Lib_load__G6.Lib_load_obj_x3.L_P_err Kc FB rho0); assumption.
Qed.
End SumT.

Section Safety.
Variable ok : world -> Prop.
Hypothesis HS : ltac2:(tb__ "0|0|
S5eS0Vok;VKc;A3").
Hypothesis MC : ltac2:(tb__ "0|0|
S78S0S1S57A3").
Hypothesis DESs : arena_destroy_stmt.

Theorem load_obj_sum : ltac2:(tb__ "0|0|
S38S0Vok;S22S0S45S0S1VKc;S2bVFB;A1VFB;S2dS4bA7S2cVrho0;A4S39S0S2aVrho0;S6eVKc;VFB;A2A4A4").
Proof using DESs HS MC ML.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JGAE segs C_P NP Kc rho0 (P0_lo FB) FB ML FUEL cps NP cutsE exitsE ok Q (proj1 HS)
                (ejcertA_jcertA segs NP _ _ _ _ _ ejcert_ok)) with (rvT := (1000, z0)); [|left; reflexivity].
       apply (exits_okT (triple segs ok) (fun _ w => SPfamGJ segs (map nA (map (@adrop) cutsE)) w \/ Q w)
                (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
                (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun P Q0 Q' HQ H => @triple_conseq segs ok P P Q0 Q' (fun w Hw => Hw) HQ H)
                (triple_skip ok)
                (fun A P Q' H => @triple_ex segs ok A P Q' H)
                (triple_pureh segs ok)
                (call_soundP segs ok) (call_soundJ segs ok)).
       - intros FBc rho1. apply (JGA_frame_sum segs C_P Kc P.Lib_handle__G1.Lib_handle_f_defs.P0_hf (P.Lib_handle__G1.Lib_handle_f_defs.Pre_hf P.Lib_handle__G1.Lib_handle_f_defs.HF_P) P.Lib_handle__G1.Lib_handle_f_defs.tv_pre PD_hf 300 299 ML); [reflexivity | intros F F' r Hs H; revert H; apply (P0txt_mono _ _ F F' r Hs) | intros FBc' rho1'; rewrite <- (Posts_hf_PD Kc FBc'); apply Lib_handle_f.handle_f_sum; assumption].
       - intros FBc rho1. apply (JGA_frame_sum segs C_P Kc P.Lib_handle__G1.Lib_handle_f_defs.P0_hf P.Lib_handle__G1.Lib_handle_lp_defs.Pre_hl P.Lib_handle__G1.Lib_handle_lp_defs.tvL_pre PD_hl 300 299 ML); [reflexivity | intros F F' r Hs H; revert H; apply (P0txt_mono _ _ F F' r Hs) | intros FBc' rho1'; rewrite <- (Posts_hl_PD Kc FBc'); apply P.Lib_handle__G7.Lib_handle_l.handle_l_sum; assumption].
       - intros FBc rho1. apply (JGA_frame_sum segs C_P Kc P.Lib_handle__G1.Lib_handle_f_defs.P0_hf P.Lib_handle__G1.Lib_handle_lp_defs.Pre_hp P.Lib_handle__G1.Lib_handle_lp_defs.tvP_pre PD_hp 300 299 ML); [reflexivity | intros F F' r Hs H; revert H; apply (P0txt_mono _ _ F F' r Hs) | intros FBc' rho1'; rewrite <- (Posts_hp_PD Kc FBc'); apply P.Lib_handle__G7.Lib_handle_p.handle_p_sum; assumption].
       - intros FBc rho1. apply (JGA_frame_sum segs C_P Kc P.Lib_handle__G1.Lib_handle_vn.P0_hvn P.Lib_handle__G1.Lib_handle_vn.Pre_hvn P.Lib_handle__G1.Lib_handle_vn.tv0 P.Lib_handle__G1.Lib_handle_vn.PD_hvn 100 99 ML); [reflexivity | intros F F' r Hs H; revert H; apply (P0txt_mono _ _ F F' r Hs) | intros FBc' rho1'; rewrite <- (P.Lib_handle__G1.Lib_handle_vn.Posts_hvn_PD Kc FBc'); apply P.Lib_handle__G1.Lib_handle_vn.handle_vn_sum; assumption].
       - intros FBc rho1. apply (JGA_frame_sum segs C_P Kc P.Lib_handle__G2.Lib_handle_vt.P0_hvt P.Lib_handle__G2.Lib_handle_vt.Pre_hvt P.Lib_handle__G2.Lib_handle_vt.tv0 P.Lib_handle__G2.Lib_handle_vt.PD_hvt 100 99 ML); [reflexivity | intros F F' r Hs H; revert H; apply (P0txt_mono _ _ F F' r Hs) | intros FBc' rho1'; rewrite <- (P.Lib_handle__G2.Lib_handle_vt.Posts_hvt_PD Kc FBc'); apply P.Lib_handle__G2.Lib_handle_vt.handle_vt_sum; assumption].
       - intros FBc rho1. apply (JGA_frame_sum segs C_P Kc (fun _ : list (Z * Z) => P.Lib_vec__G1.Lib_vec_reserve.P0_vr) P.Lib_vec__G1.Lib_vec_reserve.Pre_vr P.Lib_vec__G1.Lib_vec_reserve.tv0 PD_vr 100 99 ML); [reflexivity | intros F F' r _ H; exact H | intros FBc' rho1'; rewrite <- (Posts_vr_PD Kc FBc'); apply P.Lib_vec__G1.Lib_vec_reserve.vec_reserve_sum; assumption].
       - intros FBc rho1. apply (JGA_frame_sum segs C_P Kc P.Lib_opt__G1.Lib_opt_push1.P0_op P.Lib_opt__G1.Lib_opt_push1.Pre_op P.Lib_opt__G1.Lib_opt_push1.tv0 P.Lib_opt__G1.Lib_opt_push1.PD_op 100 99 ML); [reflexivity | intros F F' r _ H; exact H | intros FBc' rho1'; rewrite <- (P.Lib_opt__G1.Lib_opt_push1.Posts_op_PD Kc FBc'); apply P.Lib_opt__G1.Lib_opt_push1.opt_push1_sum; assumption].
       - intros FBc rho1. apply (JGA_frame_sum segs C_P Kc P.Lib_opt__G1.Lib_opt_push3w.P0_op P.Lib_opt__G1.Lib_opt_push3w.Pre_op P.Lib_opt__G1.Lib_opt_push3w.tv0 P.Lib_opt__G1.Lib_opt_push3w.PD_op 100 99 ML); [reflexivity | intros F F' r _ H; exact H | intros FBc' rho1'; rewrite <- (P.Lib_opt__G1.Lib_opt_push3w.Posts_op_PD Kc FBc'); apply P.Lib_opt__G1.Lib_opt_push3w.opt_push3_sum; assumption].
       - intros FBc rho1. apply (JGA_frame_sum segs C_P Kc (fun _ : list (Z * Z) => BuilderDispose.P0_bd) Lib_builder_dispose.Pre_bd (BuilderDispose.tvL 0) PD_bd 200 199 ML); [reflexivity | intros F F' r _ H; exact H | intros FBc' rho1'; rewrite <- (Posts_bd_PD Kc FBc'); apply Lib_builder_dispose.builder_dispose_sum; assumption].
       - intros FBc rho1. apply (JG_sum_none segs C_P Kc P0_bli PD_bli_darr ok 100 Pre_bli0 P.Lib_build__G1.Lib_build_line_index.tv0). intros FBc' rho1'. rewrite <- (Posts_bli_darr_PD Kc FBc'). apply bli_darr_ok; assumption.
       - intros FBc rho1. rewrite <- (Lib_intern_rest.Posts_ir_PDA Kc FBc). apply Lib_intern_rest.intern_rest_sum; assumption.
       - intros FBc rho1. rewrite <- (Lib_finalize_shape.Posts_fs_PDA Kc FBc). apply Lib_finalize_shape.finalize_shape_sum; assumption.
       - intros FBc rho1. rewrite <- (Lib_arena_dup.Posts_ad_PDA Kc FBc). apply Lib_arena_dup.arena_dup_sum; assumption.
       - intros tv am rho rho1. apply Lib_next_token.next_token_sum. eapply ok_frame_imp; [|exact (proj1 HS)]. intros tr md (Ai & (_ & HK & _) & _). exact HK.
       - intros tv am rho rho1. apply P.Lib_scan__G1.Lib_scan_int.scan_int_sum. eapply ok_frame_imp; [|exact (proj1 HS)]. intros tr md (Ai & (_ & HK & _) & _). exact HK.
       - intros tv am rho rho1. apply P.Lib_scan__G1.Lib_scan_double.scan_double_sum. eapply ok_frame_imp; [|exact (proj1 HS)]. intros tr md (Ai & (_ & HK & _) & _). exact HK.
       - intros Cl s R rho tv am extra Q'. intros. eapply (malloc_site_extA segs C_P EC_P NP Kc rho0 (P0_lo FB) FB ML ok Cl s R rho tv am extra Q' HS MC); eassumption.
       - intros Cl s R rho tv am i t extra Q'. intros. eapply (free_site_extA segs C_P EC_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) ok Cl s R rho tv am i t extra Q' HS MC); eassumption.
       - intros rho. apply DESs; assumption.
       - intros T tv am rT vT rho b w Hin Hm Hw. left. exists T, (JGv tv am), rho. split; [|exact Hw]. exact (in_map nA (map adrop cutsE) (T, (tv, am)) (in_map adrop cutsE (T, (tv, am), (rT, vT)) Hin)).
       - intros b1 b2 w Hb X. exact X.
       - intros P tv am rho b Hin. apply (exit_postGA segs C_P NP Kc (P0_lo FB) FB ok rho0 tv am (Posts_lo Kc FB) P). exact Hin.
  }
  intros w Hw. apply JGA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis Hvi : vm_insensitive Kc.
Hypothesis MCX : ltac2:(tb__ "0|0|
S79S0S1S57A3").
Hypothesis DESx : arena_destroy_ex_stmt.

Theorem load_obj_sum_ex : ltac2:(tb__ "0|0|
S37S0S22S0S45S0S1VKc;S2bVFB;A1VFB;S2dS4bA7S2cVrho0;A4S39S0S2aVrho0;S6eVKc;VFB;A2A4A3").
Proof using DESx Hvi MCX ML.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JGA segs C_P NP Kc rho0 (P0_lo FB) FB ML FUEL cps NP cutsE exitsE Q ejcert_ok) with (rvT := (1000, z0)); [|left; reflexivity].
       apply (exits_okT (etriple segs) (fun b w => SPfamEJ segs (map (enodeA segs C_P NP Kc rho0 (P0_lo FB) FB) cutsE) b w \/ Q w)
                (etriple_factsJ segs) (etriple_SPJ_ex segs)
                (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H)
                (fun P Q0 Q' HQ H => @etriple_conseq segs P P Q0 Q' (fun w Hw => Hw) HQ H)
                etriple_skip
                (fun A P Q' H => @etriple_ex segs A P Q' H)
                (etriple_pureh segs)
                (call_completeP segs) (call_completeJ segs)).
       - intros FBc rho1. apply (JGA_frame_sum_ex segs C_P Kc P.Lib_handle__G1.Lib_handle_f_defs.P0_hf (P.Lib_handle__G1.Lib_handle_f_defs.Pre_hf P.Lib_handle__G1.Lib_handle_f_defs.HF_P) P.Lib_handle__G1.Lib_handle_f_defs.tv_pre PD_hf 300 299 ML); [reflexivity | intros F F' r Hs H; revert H; apply (P0txt_mono _ _ F F' r Hs) | intros FBc' rho1'; rewrite <- (Posts_hf_PD Kc FBc'); apply Lib_handle_f.handle_f_sum_ex; assumption].
       - intros FBc rho1. apply (JGA_frame_sum_ex segs C_P Kc P.Lib_handle__G1.Lib_handle_f_defs.P0_hf P.Lib_handle__G1.Lib_handle_lp_defs.Pre_hl P.Lib_handle__G1.Lib_handle_lp_defs.tvL_pre PD_hl 300 299 ML); [reflexivity | intros F F' r Hs H; revert H; apply (P0txt_mono _ _ F F' r Hs) | intros FBc' rho1'; rewrite <- (Posts_hl_PD Kc FBc'); apply P.Lib_handle__G7.Lib_handle_l.handle_l_sum_ex; assumption].
       - intros FBc rho1. apply (JGA_frame_sum_ex segs C_P Kc P.Lib_handle__G1.Lib_handle_f_defs.P0_hf P.Lib_handle__G1.Lib_handle_lp_defs.Pre_hp P.Lib_handle__G1.Lib_handle_lp_defs.tvP_pre PD_hp 300 299 ML); [reflexivity | intros F F' r Hs H; revert H; apply (P0txt_mono _ _ F F' r Hs) | intros FBc' rho1'; rewrite <- (Posts_hp_PD Kc FBc'); apply P.Lib_handle__G7.Lib_handle_p.handle_p_sum_ex; assumption].
       - intros FBc rho1. apply (JGA_frame_sum_ex segs C_P Kc P.Lib_handle__G1.Lib_handle_vn.P0_hvn P.Lib_handle__G1.Lib_handle_vn.Pre_hvn P.Lib_handle__G1.Lib_handle_vn.tv0 P.Lib_handle__G1.Lib_handle_vn.PD_hvn 100 99 ML); [reflexivity | intros F F' r Hs H; revert H; apply (P0txt_mono _ _ F F' r Hs) | intros FBc' rho1'; rewrite <- (P.Lib_handle__G1.Lib_handle_vn.Posts_hvn_PD Kc FBc'); apply P.Lib_handle__G1.Lib_handle_vn.handle_vn_sum_ex; assumption].
       - intros FBc rho1. apply (JGA_frame_sum_ex segs C_P Kc P.Lib_handle__G2.Lib_handle_vt.P0_hvt P.Lib_handle__G2.Lib_handle_vt.Pre_hvt P.Lib_handle__G2.Lib_handle_vt.tv0 P.Lib_handle__G2.Lib_handle_vt.PD_hvt 100 99 ML); [reflexivity | intros F F' r Hs H; revert H; apply (P0txt_mono _ _ F F' r Hs) | intros FBc' rho1'; rewrite <- (P.Lib_handle__G2.Lib_handle_vt.Posts_hvt_PD Kc FBc'); apply P.Lib_handle__G2.Lib_handle_vt.handle_vt_sum_ex; assumption].
       - intros FBc rho1. apply (JGA_frame_sum_ex segs C_P Kc (fun _ : list (Z * Z) => P.Lib_vec__G1.Lib_vec_reserve.P0_vr) P.Lib_vec__G1.Lib_vec_reserve.Pre_vr P.Lib_vec__G1.Lib_vec_reserve.tv0 PD_vr 100 99 ML); [reflexivity | intros F F' r _ H; exact H | intros FBc' rho1'; rewrite <- (Posts_vr_PD Kc FBc'); apply P.Lib_vec__G1.Lib_vec_reserve.vec_reserve_sum_ex; assumption].
       - intros FBc rho1. apply (JGA_frame_sum_ex segs C_P Kc P.Lib_opt__G1.Lib_opt_push1.P0_op P.Lib_opt__G1.Lib_opt_push1.Pre_op P.Lib_opt__G1.Lib_opt_push1.tv0 P.Lib_opt__G1.Lib_opt_push1.PD_op 100 99 ML); [reflexivity | intros F F' r _ H; exact H | intros FBc' rho1'; rewrite <- (P.Lib_opt__G1.Lib_opt_push1.Posts_op_PD Kc FBc'); apply P.Lib_opt__G1.Lib_opt_push1.opt_push1_sum_ex; assumption].
       - intros FBc rho1. apply (JGA_frame_sum_ex segs C_P Kc P.Lib_opt__G1.Lib_opt_push3w.P0_op P.Lib_opt__G1.Lib_opt_push3w.Pre_op P.Lib_opt__G1.Lib_opt_push3w.tv0 P.Lib_opt__G1.Lib_opt_push3w.PD_op 100 99 ML); [reflexivity | intros F F' r _ H; exact H | intros FBc' rho1'; rewrite <- (P.Lib_opt__G1.Lib_opt_push3w.Posts_op_PD Kc FBc'); apply P.Lib_opt__G1.Lib_opt_push3w.opt_push3_sum_ex; assumption].
       - intros FBc rho1. apply (JGA_frame_sum_ex segs C_P Kc (fun _ : list (Z * Z) => BuilderDispose.P0_bd) Lib_builder_dispose.Pre_bd (BuilderDispose.tvL 0) PD_bd 200 199 ML); [reflexivity | intros F F' r _ H; exact H | intros FBc' rho1'; rewrite <- (Posts_bd_PD Kc FBc'); apply Lib_builder_dispose.builder_dispose_sum_ex; assumption].
       - intros FBc rho1. apply (JG_sum_none_ex segs C_P Kc P0_bli PD_bli_darr 100 Pre_bli0 P.Lib_build__G1.Lib_build_line_index.tv0). intros FBc' rho1'. rewrite <- (Posts_bli_darr_PD Kc FBc'). apply bli_darr_ex_ok; assumption.
       - intros FBc rho1. rewrite <- (Lib_intern_rest.Posts_ir_PDA Kc FBc). apply Lib_intern_rest.intern_rest_sum_ex; assumption.
       - intros FBc rho1. rewrite <- (Lib_finalize_shape.Posts_fs_PDA Kc FBc). apply Lib_finalize_shape.finalize_shape_sum_ex; assumption.
       - intros FBc rho1. rewrite <- (Lib_arena_dup.Posts_ad_PDA Kc FBc). apply Lib_arena_dup.arena_dup_sum_ex; assumption.
       - intros tv am rho rho1. apply Lib_next_token.next_token_sum_ex.
       - intros tv am rho rho1. apply P.Lib_scan__G1.Lib_scan_int.scan_int_sum_ex.
       - intros tv am rho rho1. apply P.Lib_scan__G1.Lib_scan_double.scan_double_sum_ex.
       - intros Cl s R rho tv am extra Q'. intros. eapply (malloc_site_extA_ex segs C_P EC_P NP Kc rho0 (P0_lo FB) FB ML Cl s R rho tv am extra Q' Hvi MCX); eassumption.
       - intros Cl s R rho tv am i t extra Q'. intros. eapply (free_site_extA_ex segs C_P EC_P NP Kc rho0 (P0_lo FB) FB ML (TobjJVA.NP_ok_intro NP eq_refl) Cl s R rho tv am i t extra Q' Hvi MCX); eassumption.
       - intros rho. apply DESx; assumption.
       - intros T tv am rT vT rho b w Hin Hm Hw. left. exists (enodeA segs C_P NP Kc rho0 (P0_lo FB) FB (T, (tv, am), (rT, vT))), rho. split; [exact (in_map _ _ _ Hin)|]. split; [exact Hw | exact Hm].
       - intros b1 b2 w Hb [X|X]; [left | right; exact X]. destruct X as (n & r & Hn & Hs & Hmz). exists n, r. split; [exact Hn|]. split; [exact Hs | lia].
       - intros P tv am rho b Hin. apply (eexit_postGA segs C_P NP Kc (P0_lo FB) FB rho0 tv am (Posts_lo Kc FB) P). exact Hin.
  }
  intros w Hw. apply JGA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
