(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader fact, the zero-filled stack window DRV_ZWIN): the recorded proof of printf1_run replaced by the text proof of jsoncons/fuzz_bigint's As0DrvPrintf1.v with this unit's addresses, and the stack window of its statement narrowed to DRV_ZWIN. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA Pm8IcptLayout PmIcptDrvA DrvKitA DrvNodesLazyK As0DrvKitA Pm8DrvEntry Pm8Drv_defs Pm8DrvLib Pm8DrvRead Pm8DrvPiece Pm8DiagLoopK Pm8DrvStdio Pm8DrvPrintfK FrmInv Pm8FrmInv.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require L5Defs L5KnA ArtMem Pm8ArtFsInv.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8DrvP_dpA Pm8DrvP_dpB_notty Pm8DrvP_dpCd.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Rpl.
Ltac2 rplG () : string array := Array.of_list ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Npos"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.list"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.rdn"; "OSSVerify.jsoncons.fuzz_json_cursor.images.Asan.M.loaded_segments"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Numbers.BinNums.Zpos"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Corelib.Numbers.BinNums.Z0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvPrintfK.SOBUF"; "Corelib.Numbers.BinNums.xH"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvStdio.rdn_tr"; "Stdlib.ZArith.Znat.Nat2Z.is_nonneg"; "Corelib.Init.Datatypes.cons"; "Stdlib.micromega.ZMicromega.ZArithProof"; "Stdlib.micromega.ZMicromega.RatProof"; "Stdlib.micromega.RingMicromega.PsatzAdd"; "Stdlib.micromega.RingMicromega.PsatzIn"; "Corelib.Init.Datatypes.O"; "Stdlib.micromega.ZMicromega.DoneProof"; "Corelib.Init.Datatypes.nil"; "Stdlib.micromega.VarMap.Branch"; "Stdlib.micromega.VarMap.Elt"; "Stdlib.micromega.VarMap.t"; "Stdlib.micromega.Tauto.IMPL"; "Stdlib.micromega.RingMicromega.Formula"; "Stdlib.micromega.Tauto.eKind"; "Corelib.Init.Datatypes.unit"; "Stdlib.micromega.Tauto.isProp"; "Stdlib.micromega.Tauto.AND"; "Stdlib.micromega.Tauto.A"; "Stdlib.micromega.RingMicromega.Build_Formula"; "Stdlib.micromega.EnvRing.PEX"; "Stdlib.micromega.RingMicromega.OpLe"; "Corelib.Init.Datatypes.tt"; "Stdlib.micromega.RingMicromega.OpLt"; "Stdlib.micromega.EnvRing.PEadd"; "Corelib.Init.Datatypes.None"; "Stdlib.micromega.EnvRing.PEc"; "Stdlib.micromega.Tauto.BFormula"; "Stdlib.micromega.ZMicromega.ZTautoChecker_sound"; "Corelib.Init.Logic.eq_refl"; "Stdlib.micromega.ZMicromega.ZTautoChecker"; "Stdlib.micromega.VarMap.find"; "Corelib.Init.Logic.f_equal2"; "stdpp.bitvector.definitions.BV"; "stdpp.bitvector.definitions.Z_to_bv_obligation_1"; "Corelib.Numbers.BinNums.N"; "stdpp.bitvector.definitions.bv_unsigned"; "stdpp.bitvector.definitions.bv_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymDriveX.ECALLW"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "Corelib.Init.Datatypes.prod"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.fframe"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.credit"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvLib.dinv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AgentLib.u64_lit"; "Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.div_mod"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.mod_pos_bound"; "Stdlib.ZArith.BinInt.Z.mod_neg_bound"; "Stdlib.omega.PreOmega.Z.div_0_r_ext"; "Stdlib.omega.PreOmega.Z.mod_0_r_ext"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvLib.nolazy_of_inv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvLib.di_inv"; "Corelib.Init.Logic.eq_ind_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIface.in_block"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.DrvNodesLazyK.nolazy_rng"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "Corelib.Init.Logic.or_introl"; "Stdlib.micromega.Tauto.X"; "Corelib.Init.Logic.or_intror"; "Stdlib.micromega.EnvRing.PEsub"; "Stdlib.micromega.VarMap.Empty"; "LinuxProcessSemantics.LinuxProcessSem.State.page_in_ranges"; "LinuxProcessSemantics.LinuxProcessSem.State.page_base_of"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Logic.eq_ind"; "Stdlib.ZArith.BinInt.Z.add_0_r"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanAcct.mrestrict"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.ahid"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.getr"; "Corelib.Init.Logic.I"; "stdpp.bitvector.definitions.BvWf"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvPrintf1.stdout0A"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FrmInv.FrmInv.fp_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.FPState"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanAcct.same_but_materialized"; "Stdlib.Lists.List.In"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8Drv_defs.c_kept"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvPrintfK.stdoutA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvPrintf1.stdoutXA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvPrintf1.Wpf1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SpinAlg.srealizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.mkst"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.seg_rom"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.ShapeAlg.t_emit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Spec.W"; "Corelib.Init.Datatypes.pair"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvStdio.PR_CELLS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvStdio.pr_cell_vis"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.ArtMem.art_bytes1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.asan.Pm8DrvP_dpA.AS0DRVP_dpA.dpA_conc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.asan.Pm8DrvP_dpA.AS0DRVP_dpA.aligned"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.writable"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvLib.store_ok_defined"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.defined"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.img_clear"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvStdio.stk_sh0"; "Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg"; "Stdlib.micromega.RingMicromega.PsatzMulC"; "Stdlib.micromega.EnvRing.Pc"; "Corelib.Numbers.BinNums.Zneg"; "Stdlib.micromega.RingMicromega.PsatzMulE"; "Stdlib.micromega.RingMicromega.PsatzC"; "Stdlib.micromega.ZMicromega.CutProof"; "Stdlib.micromega.Tauto.NOT"; "Stdlib.micromega.RingMicromega.OpEq"; "Stdlib.micromega.EnvRing.PEmul"; "Corelib.Init.Logic.False"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5KnA.L5KA.zeros_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8ArtFsInv.cell_zero_bytes"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvStdio.img_sh0"; "Stdlib.micromega.ZifyClasses.rew_iff"; "Stdlib.micromega.ZifyClasses.and_morph"; "Stdlib.micromega.ZifyClasses.eq_iff"; "Stdlib.micromega.ZifyClasses.mkrel"; "Corelib.Init.Logic.iff_refl"; "Stdlib.micromega.ZifyClasses.mkapp"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8ArtFsInv.ART_POISON"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Lists.ListDef.Forall_cons"; "Stdlib.micromega.Tauto.OR"; "Corelib.Lists.ListDef.Forall_nil"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.IcptIfaceA.icl_poison"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8IcptLayout.aicl_poison"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.HeapIfaceA.byte_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.u64_at"; "Corelib.Init.Logic.and_ind"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.u8_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.L5Defs.L5.u32_at"; "Corelib.Init.Logic.ex"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.StoreOk.mem_grows"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CatSim.msteps"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.asan.Pm8DrvP_dpA.AS0DRVP_dpA.KS_dpA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvPiece.drv_piece"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8Drv_defs.IMG_W_A"; "Stdlib.ZArith.BinInt.Z.eq_dec"; "Corelib.Init.Specif.sumbool"; "Corelib.Init.Logic.ex_intro"; "Corelib.Init.Logic.conj"; "Corelib.Init.Logic.or_ind"; "Corelib.Init.Logic.False_ind"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvLib.CWA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.StoreOk.store_ok_mono"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvPrintf1.TRf"; "Stdlib.micromega.ZifyClasses.mkapp2"; "Stdlib.micromega.ZifyClasses.inj"; "Stdlib.micromega.ZifyInst.Inj_Z_Z"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagLoopK.sbm_fds'"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.DrvNodesLazyK.rz_ioctl_winsz_lz"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvPrintf1.fetch_ioctlA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymDriveX.is_ecall_ECALLW"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvLib.di_halt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.regupd"; "LinuxProcessSemantics.LinuxProcessSem.State.errno_ret"; "LinuxProcessSemantics.LinuxProcessSem.State.ENOTTY"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.getr_other"; "Stdlib.ZArith.BinInt.Z.opp"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AgentLib.errno_ret_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.getr_same"; "Corelib.Numbers.BinNums.positive"; "Corelib.Init.Logic.True"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.asan.Pm8DrvP_dpB_notty.AS0DRVP_dpB_notty.dpB_notty_conc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.asan.Pm8DrvP_dpB_notty.AS0DRVP_dpB_notty.aligned"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.asan.Pm8DrvP_dpB_notty.AS0DRVP_dpB_notty.KS_dpB_notty"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvStdio.img_cell"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvPrintf1.nl_imgA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvLib.dinv_lzinv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.As0DrvKitA.lzinv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanAcct.H_off_segments"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanAcct.lazy_cover"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanAcct.A_wf"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanAcct.MInv"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvPrintf1.FPX_1.Printf1.nl_pt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagLoopK.wv_loop"; "Stdlib.micromega.ZifyClasses.rew_iff_rev"; "Corelib.Init.Peano.le"; "Stdlib.ZArith.Znat.Nat2Z.inj_le"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.app"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagLoopK.wv_regs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagLoopK.wv_buf"; "Stdlib.setoid_ring.Ring_polynom.PExpr"; "Stdlib.setoid_ring.ZArithRing.Zr_ring_lemma1"; "Stdlib.setoid_ring.Ring_tac.ring_subst_niter"; "Stdlib.setoid_ring.Ring_polynom.PEsub"; "Stdlib.setoid_ring.Ring_polynom.PEX"; "Stdlib.setoid_ring.Ring_polynom.PEc"; "Stdlib.setoid_ring.Ring_polynom.PEadd"; "Stdlib.setoid_ring.Ring_polynom.mk_monpol_list"; "Stdlib.ZArith.BinInt.Z.eqb"; "Stdlib.ZArith.BinInt.Z.quotrem"; "Stdlib.setoid_ring.Ring_polynom.Mon"; "Stdlib.setoid_ring.Ring_polynom.Pol"; "Stdlib.setoid_ring.Ring_polynom.Peq"; "Stdlib.setoid_ring.Ring_polynom.norm_subst"; "stdpp.tactics.f_equal_help"; "Stdlib.ZArith.BinInt.Z.max"; "Stdlib.micromega.ZifyInst.of_nat_to_nat_eq"; "Stdlib.ZArith.BinInt.Z.max_spec"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagLoopK.wv_iov"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagLoopK.WV_KEEP"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvLib.dinv_frame"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvLib.sbm_vml"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.As0DrvKitA.sbm_halted_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvLib.ahid_sbm"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.leb"; "Corelib.Init.Datatypes.andb_prop"; "Stdlib.ZArith.BinInt.Z.eqb_eq"; "Stdlib.ZArith.BinInt.Z.leb_le"; "Corelib.Init.Datatypes.orb"; "Stdlib.Bool.Bool.orb_prop"; "Corelib.Init.Logic.iff"; "Corelib.Classes.Morphisms.subrelation_proper"; "Corelib.Classes.Morphisms.respectful"; "Corelib.Classes.Morphisms_Prop.or_iff_morphism"; "Corelib.Program.Basics.impl"; "Corelib.Classes.Morphisms.subrelation_respectful"; "Corelib.Classes.Morphisms.subrelation_refl"; "Corelib.Classes.Morphisms.iff_impl_subrelation"; "Corelib.Classes.Morphisms.reflexive_proper_proxy"; "Corelib.Classes.Morphisms.reflexive_reflexive_proxy"; "Corelib.Classes.RelationClasses.iff_Reflexive"; "Corelib.Classes.Morphisms.Reflexive_partial_app_morphism"; "Corelib.Init.Logic.eq_trans"; "Corelib.Init.Logic.eq_sym"; "stdpp.bitvector.definitions.Z_to_bv_bv_unsigned"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.asan.Pm8DrvP_dpCd.AS0DRVP_dpCd.aligned"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.asan.Pm8DrvP_dpCd.AS0DRVP_dpCd.dpCd_conc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.u64_range"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.asan.Pm8DrvP_dpCd.AS0DRVP_dpCd.KS_dpCd"; "Stdlib.Bool.Bool.orb_true_iff"; "Stdlib.Bool.Bool.andb_true_iff"; "Corelib.Classes.Morphisms_Prop.and_iff_morphism"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8FrmInv.Pm8FrmInv.msteps_fp_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AsanAcct.same_but_materialized_trans"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DrvPrintf1.le4_m1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.Pm8DiagLoopK.wv_done"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_addi"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymDrive.v_addi_pc4"].

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Definition stdout0A (MV : word -> option byte) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 1 "U15;Y6;00;A1;o1;#0;Y3;0;A1;i0;A1;o1;#2;A1;i5;#3;A1;i2;#4;N4;A1;o9;Y20;57a50;Y2;1;N8;A1;o9;Y10;000;A2;k8;#1;o12;Y3;2;A2;k17;r3;r2;Pd;Ri15;Pk;Ri18;P~RA2;k16;o12;r2;P~RA2;k16;A2;k17;r3;A1;k19;r2;r6;A3;i4;i20;A4;k21;k7;r9;A2;k8;#1;A2;k17;r8;r4;r3;o22;LMV;RP~RA1;i0;#1;A1;i2;#3;A2;i3;A3;i4;#5;A4;k6;k7;r1;A2;k8;#1;A1;o9;Y20;57adc;#6;A2;o10;#4;A2;k11;#6;A2;k8;#1;A1;o9;Y31;7fffffff;A2;i3;A3;i4;#5;A4;k6;k7;r1;A2;k8;#1;#7;#6;A2;o10;#4;A2;k11;#6;A2;k8;#1;A1;o9;#8;A2;i3;A3;i4;#5;A4;k6;k7;r1;A2;k8;#1;A1;o9;Y20;57ab0;#9;A2;o10;#4;A2;k11;#9;A2;k8;#1;#10;A2;i3;A3;i4;#5;A4;k6;k7;r1;A2;k8;#1;A1;o9;Y20;57a70;#9;A2;o10;#4;A2;k11;#9;#11;A2;i3;A3;i4;#5;A4;k6;k7;r1;A2;k8;#1;A1;o9;Y20;57ad8;#6;A2;o10;#4;A2;k11;#6;#11;A2;i3;A3;i4;#5;A4;k6;k7;r1;A2;k8;#1;A1;o9;Y20;57aa8;#9;A2;o10;#4;A2;k11;#9;A2;k8;#1;k13;A2;i3;A3;i4;#5;A4;k6;k7;r1;A2;k8;#1;A1;o9;Y20;57ae0;#6;A2;o10;#4;A2;k11;#6;A2;k8;#1;A1;o9;#12;A2;i3;A3;i4;#5;A4;k6;k7;r1;A2;k8;#1;A1;o9;Y20;57a98;#9;A2;o10;#4;A2;k11;#9;A2;k8;#1;A1;o9;Y20;3c4c0;A2;i3;A3;i4;#5;A4;k6;k7;r1;A2;k8;#1;A1;o9;Y20;57ac8;#6;A2;o10;#4;A2;k11;#6;A2;k8;#1;A1;o9;o14;A2;i3;Pa;Ri15;Pn;Ri15;P~RA2;k16;#7;r2;P~RA2;k16;#13;A2;k17;#7;A1;o9;Y7;68;#14;Pa;Ri15;Pn;Ri15;P~RA2;k16;k13;r2;P~RA2;k16;#13;A2;k17;k13;#10;#14;").

Definition stdoutXA (MV : word -> option byte) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 1 "S8;A1;o1;Y6;00;Y3;0;A1;i0;A1;o1;#1;A1;i5;#2;A1;i2;#3;N8;N4;A2;o10;#3;A2;k11;#5;A2;k8;#0;o12;LMV;RP~RA1;i0;#0;A1;i2;#2;A2;i3;A3;i4;#4;A4;k6;k7;r1;A2;k8;#0;A1;o9;Y20;57a98;#5;A2;o10;#3;A2;k11;#5;A2;k8;#0;A1;o9;Y20;3b7d4;A2;i3;A3;i4;#4;A4;k6;k7;r1;A2;k8;#0;A1;o9;Y20;57ac8;#6;A2;o10;#3;A2;k11;#6;A2;k8;#0;A1;o9;o14;A2;i3;A3;i4;#4;A4;k6;k7;r1;A2;k8;#0;A1;o9;Y20;57aa8;#5;A2;o10;#3;A2;k11;#5;A2;k8;#0;k13;A2;i3;A3;i4;#4;A4;k6;k7;r1;A2;k8;#0;A1;o9;Y20;57a58;#5;#7;A3;i4;#4;A4;k6;k7;r1;A2;k8;#0;A1;o9;Y20;57a60;#5;#7;").

Definition Wpf1 (S a : Z) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 2 "S1;A1;o9;Y20;57a50;LS;Ri15;La;Ri15;A2;i23;A2;i3;A2;k16;A2;k24;r2;A1;o9;Y11;4a0;r1;A2;k25;r1;r2;A2;i23;A2;i3;A2;k16;#0;r1;A2;k25;r1;A2;k17;#0;A1;o9;Y7;68;A2;i3;A2;k16;k13;r1;A2;k25;r1;A2;k17;k13;A1;o9;Y10;000;").

Lemma TRf : forall (MVa MVb : word -> option byte) (W : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> MVb (Z_to_bv 64 a) = MVa (Z_to_bv 64 a)) ->
  forall a (n : nat) bs, rdn ASEGS MVa (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> ~ W i) -> rdn ASEGS MVb (Z_to_bv 64 a) n = Some bs.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S23;Y6;00;A1;o1;#0;Y3;0;A1;i0;A1;o1;#2;A1;i2;#3;P~RA1;i0;#1;#4;Y1;0;A2;k26;A1;o9;#6;A1;o9;#0;A2;k8;#1;r3;A1;i5;#3;A2;k16;o12;r4;N3;N2;A2;o34;i15;o35;N1;A1;i42;i15;A2;o49;i15;#6;A2;o49;i15;o14;A3;o53;i15;#16;A2;o49;i15;Y1;1;A1;o54;i44;A1;o9;Y64;0000000000000000;A2;o55;i15;#20;A2;o55;i15;o12;LMVa;R#5;LMVb;R#5;LW;RP~Ri15;pLFR;RPa;Ri15;P~RA2;i3;A2;k16;o12;r1;A2;k25;r1;#7;P~RA1;k27;A1;r3;r2;A3;i4;#4;A1;r5;#8;A1;r6;#8;La;Ri15;Ln;Ri18;Lbs;R#9;LHr;RA3;i4;A1;i2;#9;A4;k6;k7;r7;#8;r2;A2;o10;#9;r1;LHa;R#10;LHn;RA2;k16;A2;k17;r5;A1;k19;r4;#7;LHo;RPi;Ri15;P~RA2;i3;A2;k16;r7;r1;A2;k25;r1;A2;k17;r7;A1;k19;r6;A1;k27;A1;r10;r2;A9;k28;r11;r10;r7;r6;r5;r4;r3;r2;Li;Ri15;LHi;RA2;i3;A2;k16;r8;r1;A2;k25;r1;A2;k17;r8;A1;k19;r7;A3;r10;r2;Ecstr;RA1;k29;r8;A2;k16;o12;A1;k19;r8;E__arith;RL__x3;Ri15;L__x2;Ri15;L__x1;Ri15;E__wit;RA3;o30;i31;A2;o32;A3;o33;i15;A2;o34;i15;#11;A3;o33;i15;A2;o34;i15;#12;#13;o36;A3;o30;i31;A2;o32;A3;o33;i15;A2;o34;i15;N4;A3;o33;i15;A2;o34;i15;#14;#13;o36;A1;o37;i31;A1;i5;i31;E__varmap;RA4;o38;i15;A2;o39;i15;r3;r2;A2;o39;i15;r4;A1;i40;i15;E__ff;RA8;o41;#15;k43;i44;i44;o45;A7;o46;#15;k43;i44;i44;o45;A7;o47;#15;k43;i44;i44;o45;A4;o48;i15;#16;o50;#17;o51;A7;o47;#15;k43;i44;i44;o45;A4;o48;i15;#17;o52;#18;o51;#19;A8;o41;#15;k43;i44;i44;o45;A7;o47;#15;k43;i44;i44;o45;A4;o48;i15;#18;o50;#21;o51;#19;A8;o41;#15;k43;i44;i44;o45;A7;o47;#15;k43;i44;i44;o45;A4;o48;i15;#22;o50;#16;o51;#19;A7;o46;#15;k43;i44;i44;o45;A7;o47;#15;k43;i44;i44;o45;A4;o48;i15;#22;o50;#17;o51;A7;o47;#15;k43;i44;i44;o45;A4;o48;i15;#17;o52;#21;o51;A2;k56;#15;o45;A4;k57;r1;r3;cvA2;o58;i20;o22;A3;i4;i20;A2;k59;r1;r3;o22;A3;k60;i15;o12;r2;P__x3;Ri15;P__x2;Ri15;P__x1;Ri15;P~RA2;i3;A2;k16;r2;r1;A2;k25;r1;A2;k17;r2;r3;P~RA2;k16;A2;k17;r3;r4;#20;P~R#10;A2;i3;#10;A2;k25;r4;#20;A6;r1;A1;k19;r10;r11;r4;r3;r6;r7;A2;r3;r2;r1;").
Qed.

Lemma le4_m1 : word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615) = word_to_le_bytes 4 (Z_to_bv 64 4294967295).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S36;Y3;0;A1;o1;#0;A1;i0;#1;A1;i5;#2;A1;o30;#2;Y7;7f;A1;o9;#5;A1;o9;Y63;7fffffffffffffff;A3;o62;#1;#6;A2;k63;#1;#7;Y31;7fffffff;A1;o9;#9;A3;o62;#1;#6;A2;k63;#1;#10;Y55;7fffffffffffff;A3;o62;#1;#6;A2;k63;#1;A1;o9;#12;Y47;7fffffffffff;A3;o62;#1;#6;A2;k63;#1;A1;o9;#14;Y39;7fffffffff;A3;o62;#1;#6;A2;k63;#1;A1;o9;#16;A1;o37;#2;A3;o30;#2;#17;#18;A3;o30;#2;#15;#19;Y23;7fffff;A3;o62;#1;#6;A2;k63;#1;A1;o9;#21;Y15;7fff;A3;o62;#1;#6;A2;k63;#1;A1;o9;#23;A3;o62;#1;#6;A2;k63;#1;#6;A3;o30;#2;#25;#18;A3;o30;#2;#24;#26;A1;i0;r1;A1;i0;r2;A3;i4;i15;A2;k65;r4;r3;A2;k65;r4;r2;P~RA3;i4;i15;A2;k65;r3;r2;A2;k65;r3;r1;A3;i4;A1;i0;r4;r3;r2;Ln;Ri64;Lb1;R#28;Lb2;R#29;m3;RNL~RA2;i3;P~RA3;i4;A1;i0;r3;r2;r1;#30;#31;P~R#30;A3;i4;A1;i0;r5;r4;r3;A3;k66;r3;r2;r1;1;L~RP~RA3;i4;A1;i0;r3;r2;r1;#30;L~RP~RA3;i4;i15;A2;k65;r4;r3;A2;k65;r4;r2;A3;i4;A1;i0;r5;r4;r3;r1;Pn;Ri64;Pb1;R#28;Pb2;R#29;#31;N4;A1;o1;Y6;00;cvA10;k61;#2;#3;#3;#4;#8;#11;A3;o30;#2;#13;#20;A3;o30;#2;#22;#27;EH;R#32;#33;A4;r1;#1;#8;#11;A2;o58;i15;A2;k65;#1;#11;A10;k61;#2;#3;#3;#4;#13;#22;#20;#27;EH;R#32;#33;A4;r1;#1;#13;#22;A2;o58;i15;A2;k65;#1;#22;A10;k61;#2;#3;#3;#4;#15;#24;#19;#26;EH;R#32;#33;A4;r1;#1;#15;#24;A2;o58;i15;A2;k65;#1;#24;A10;k61;#2;#3;#3;#4;#17;#25;#18;#18;EH;R#32;#33;A4;r1;#1;#17;#25;A2;o58;i15;A2;k65;#1;#25;A2;o58;#3;#18;A3;i4;#3;A2;k11;#34;A2;k8;#35;#7;A2;k11;#34;A2;k8;#35;#10;").
Qed.
Lemma nl_imgA : rdn ASEGS (fun _ => None) (Z_to_bv 64 86427) 1 = Some [Z_to_bv 8 10].
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S8;Y3;0;A1;o1;#0;A1;i0;#1;A1;i5;#2;A1;i2;#3;Y3;2;A2;o10;#3;A3;o30;#2;A2;k8;#1;A1;o9;#5;A1;o37;#2;A1;o1;Y6;00;cvA2;o58;#4;#6;A3;i4;#4;A4;k6;k7;L~RA1;i0;#7;A1;o54;#2;A2;k8;#7;A1;o9;Y16;519b;N1;#6;").
Qed.
Lemma fetch_ioctlA : fetch_word ASEGS (Z_to_bv 64 0x13c51c) = Some ECALLW.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S4;Y5;00;A1;i0;A1;o1;#0;A1;i2;#1;A2;o10;#1;k67;cvA2;o58;#2;#3;A3;i4;#2;A2;k68;k7;A2;k8;A1;o1;Y6;00;A1;o9;Y20;3c51c;#3;").
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Printf1.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_ok L ar C scfg HI.
  Hypothesis ICok : aicpt_ok L ar IL scfg HI.
  Hypothesis ILY : as0_icpt_layout IL.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Hypothesis Hpr : incl PR_CELLS (asc_cells C).
  Variable M0 : word -> option byte.
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).
  #[local] Notation rom := (seg_rom ASEGS).

  Lemma nl_pt : forall LB LK cr A M (model : Model) x, dinvA LB LK cr A M model -> 0 <= x < 2 ^ 64 -> (x < 0x6b3000 \/ usp - 8388608 <= x) ->
    page_in_ranges (page_base_of x) (m_vm_lazy model) = false.
  Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S90;A1;i5;A2;i69;i15;i15;Y6;00;A1;o1;#1;Y3;0;A2;k16;o12;r2;Y1;0;A2;k26;A1;o9;#5;A1;o9;#1;A1;o9;Y22;2b3000;A2;k65;#2;vsp0;Y23;000000;A1;o9;#9;A2;k24;#8;#10;Y4;0;A1;o9;#12;A2;k75;#8;#13;A2;k76;#8;#13;A2;k16;o12;#15;P~RA2;k16;o12;#8;P~RA2;k16;o12;#13;#16;A2;k77;#8;#13;A3;i4;i15;#13;o12;A2;k79;#8;#13;P~RA1;k27;#19;A3;i4;i15;#8;A2;k17;A2;k78;#13;#20;#15;A2;k80;#8;#13;P~RA2;k25;o12;#13;A2;i3;#16;A2;k25;#15;#13;A2;k81;#8;#13;P~RA2;k25;#13;o12;A2;i3;A2;k25;#13;#15;A2;k16;#15;o12;A2;k82;#8;#13;P~R#19;A3;i4;i15;#20;o12;A2;k83;#8;#13;P~R#19;A3;i4;i15;#15;#8;A2;k16;o12;r12;A1;o9;Y64;0000000000000000;A2;k16;o12;r13;A2;k25;r13;#31;A2;k16;o12;r14;A2;k25;r15;#31;A1;o37;i31;A1;i5;i31;A2;o39;i15;r2;A1;i40;i15;A1;i42;i15;A2;o49;i15;o14;A2;o55;i15;#31;A7;o47;#40;k43;i44;i44;o45;A4;o48;i15;#41;o52;#42;o51;A1;o54;i44;A2;o55;i15;o12;A7;o47;#40;k43;i44;i44;o45;A4;o48;i15;#45;o50;#41;o51;A2;k56;#40;o45;A4;k57;r1;r3;cvA2;o58;i20;o22;A3;i4;i20;A2;k59;r1;r3;o22;A3;k60;i15;o12;r2;A2;k25;r1;#31;A2;k16;o12;r3;A2;k8;#2;r5;A1;o9;o14;A2;k16;o12;r15;A2;o55;i15;#52;A2;i3;A2;k16;o12;r1;A2;k25;r1;#52;A2;k65;#2;A2;k8;#2;r7;A2;k17;#56;r2;A2;k17;r1;r3;A2;k17;r9;r3;A2;k17;r10;r4;A2;k25;#60;#7;A2;k16;#11;#60;A2;k87;r16;#60;A2;i23;#62;#63;A2;k25;r12;#52;A2;k17;r19;r13;A2;k25;r15;#52;A2;k16;o12;r22;A2;k25;r22;#31;A2;k17;r23;r17;A2;k16;o12;r24;A2;k25;r25;#31;N2;A3;o30;i31;A2;o32;A3;o33;i15;A2;o34;i15;N3;A3;o33;i15;A2;o34;i15;#73;A2;o34;i15;o35;o36;#36;A4;o38;i15;A2;o39;i15;r3;r2;A2;o39;i15;r4;A2;o49;i15;#5;A2;o55;i15;#7;A1;o9;Y46;3fff80000000;A2;o55;i15;#78;Y1;1;A2;o49;i15;#80;A6;o91;#40;k43;i44;i44;o45;r6;Y47;000000000000;A2;k16;#8;A1;o9;#83;A3;o93;i15;#41;A2;o55;i15;#10;A2;k65;#2;A2;k8;#2;r8;A2;k17;#86;r2;A2;i3;A2;k16;o12;o12;A2;k25;o12;#52;A1;k89;r10;LLB;R#0;LLK;RA1;i5;k70;Lcr;Rk71;LA;R#0;LM;RP~RA1;i0;#2;A1;i2;A1;i0;A1;o1;#3;Lmodel;Ri72;Lx;Ri15;LD;RA10;i73;var;vHI;vsp0;vM0;r7;r6;r5;r4;r3;r2;LHx;RA2;i3;#4;A2;k25;r2;#6;LHc;RA2;i23;A2;k25;r3;#7;A2;k16;#11;r3;EU;RA2;k74;r4;E__sat1;R#14;#17;EH;R#18;#21;EH0;R#22;#23;EH1;R#24;#25;EH2;R#26;#27;EH3;R#28;#29;Eq;R#20;i15;Er;R#15;i15;m3;RNL~RA2;i3;#30;A2;k25;r12;#31;A2;i3;#32;#33;r10;1;L~R#30;L~RA2;k25;r13;#31;A2;LH4;R#34;LH5;R#35;E__arith;RL__x1;Ri15;E__wit;R#36;#37;E__varmap;R#38;#39;E__ff;RA8;o41;#40;k43;i44;i44;o45;#43;#44;A8;o41;#40;k43;i44;i44;o45;#46;#44;A7;o46;#40;k43;i44;i44;o45;#46;#43;#47;#48;P__x1;Ri15;P~R#49;P~R#4;A2;i3;#50;A2;k25;r3;#31;A3;r1;r17;r2;r3;r2;r1;A3;i4;i15;A2;k65;#2;A2;k8;#2;r4;r4;EX;RA21;k84;vscfg;vL;var;vC;vIL;vHI;vHIok;vsp0;vHsp;vDL;r11;A1;o37;k70;r10;r9;r8;r7;r6;#51;#52;A11;k85;var;vHI;vsp0;vM0;r11;r10;r9;r8;r7;r6;r4;A6;k86;i15;r5;Lz;Ri15;A2;k16;A2;k17;r1;#52;#6;E__sat1;R#14;#17;EH;R#18;#21;EH0;R#22;#23;EH1;R#24;#25;EH2;R#26;#27;EH3;R#28;#29;Eq;R#20;i15;Er;R#15;i15;m3;RNL~RA2;i3;#32;#33;A2;k16;A2;k17;r14;#52;#31;r11;1;L~R#32;L~RA2;k25;r14;#31;A2;LH4;R#53;LH5;RA2;k25;r16;#31;E__arith;RL__x1;Ri15;E__wit;R#36;#37;E__varmap;R#38;#39;E__ff;RA8;o41;#40;k43;i44;i44;o45;#43;#44;A7;o47;#40;k43;i44;i44;o45;A4;o48;i15;A3;o53;i15;#41;#54;o50;#42;o51;#47;#48;P__x1;Ri15;P~R#49;A2;k16;A2;k17;r2;#52;#31;A2;r1;r18;r2;r2;r1;A2;k65;#2;#51;r1;P~RPk;Ri15;P~R#55;A2;i23;A2;k25;#57;#7;A2;i23;A2;k16;#11;#57;A2;k87;r13;#57;A3;k88;A1;k89;r7;A2;k8;#2;r6;#52;EY;RLk;Ri15;LHk;R#55;A6;k86;i15;r8;Lz;Ri15;A2;i23;A2;k25;#58;#7;A2;i23;A2;k16;#11;#58;A2;k87;r15;#58;m23;RNL~RA2;i23;A2;k25;r8;#7;A2;k16;#11;r8;A2;i23;A2;k25;#59;#7;A2;i23;A2;k16;#11;#59;A2;k87;r15;#59;r5;2;L~RA2;k25;r8;#7;A1;LH;RA2;k25;r9;#7;A3;o90;#61;#64;E__sat1;R#14;#17;EH0;R#18;#21;EH1;R#22;#23;EH2;R#24;#25;EH3;R#26;#27;EH4;R#28;#29;Eq;R#20;i15;Er;R#15;i15;m3;RNL~RA2;i3;#30;#65;A2;k25;#66;#7;r11;1;L~R#30;L~RA2;k25;r13;#52;A2;LH5;R#34;LH6;R#67;m3;RNL~RA2;i3;#68;#69;A2;k25;#70;#7;r20;1;L~R#68;L~RA2;k25;r23;#31;A2;LH7;R#71;LH8;R#72;E__arith;RL__p1;RpL__x3;Ri15;L__x2;Ri15;L__x1;Ri15;E__wit;R#74;#37;E__varmap;R#75;#39;E__ff;RA8;o41;#40;k43;i44;i44;o45;A7;o47;#40;k43;i44;i44;o45;A4;o48;i15;#76;o52;#54;o51;#44;A8;o41;#40;k43;i44;i44;o45;A7;o47;#40;k43;i44;i44;o45;A4;o48;i15;#41;o52;#77;o51;#44;A8;o41;#40;k43;i44;i44;o45;A7;o46;#40;k43;i44;i44;o45;A7;o47;#40;k43;i44;i44;o45;A4;o48;i15;#79;o50;#81;o51;#82;#44;A7;o47;#40;k43;i44;i44;o45;A4;o48;i15;A3;o53;i15;#41;#76;o52;#77;o51;#47;#48;P__p1;RpP__x3;Ri15;P__x2;Ri15;P__x1;Ri15;P~RA2;k25;r2;#52;P~RA2;k25;r2;#7;P~RA2;i3;A2;k16;#78;r5;r6;A2;k25;A2;k17;r4;r5;#7;A7;r1;#84;#8;r21;r27;r6;r18;vHsp;r2;r1;r2;r1;r1;L~RA2;k16;#11;r8;A1;LH;RA2;k16;#11;r9;A3;o92;#61;#64;A3;o90;#62;#63;E__sat1;R#14;#17;EH0;R#18;#21;EH1;R#22;#23;EH2;R#24;#25;EH3;R#26;#27;EH4;R#28;#29;Eq;R#20;i15;Er;R#15;i15;m3;RNL~RA2;i3;#30;#65;A2;k16;#11;#66;r11;1;L~R#30;L~RA2;k25;r13;#52;A2;LH5;R#34;LH6;R#67;m3;RNL~RA2;i3;#68;#69;A2;k16;#11;#70;r20;1;L~R#68;L~RA2;k25;r23;#31;A2;LH7;R#71;LH8;R#72;E__arith;RL__p1;RpL__x3;Ri15;L__x2;Ri15;L__x1;Ri15;E__wit;R#74;#37;E__varmap;R#75;#39;E__ff;RA8;o41;#40;k43;i44;i44;o45;A7;o47;#40;k43;i44;i44;o45;A4;o48;i15;#45;o50;#81;o51;#44;A8;o41;#40;k43;i44;i44;o45;A7;o47;#40;k43;i44;i44;o45;A4;o48;i15;#85;o50;#76;o51;#44;A8;o41;#40;k43;i44;i44;o45;A7;o46;#40;k43;i44;i44;o45;A7;o47;#40;k43;i44;i44;o45;A4;o48;i15;#79;o50;#41;o51;#82;#44;A7;o47;#40;k43;i44;i44;o45;A4;o48;i15;#85;o50;A3;o53;i15;#76;#81;o51;#47;#48;P__p1;RpP__x3;Ri15;P__x2;Ri15;P__x1;Ri15;P~R#50;P~RA2;k16;A2;k24;r2;#10;r3;P~RA2;i3;A2;k16;#78;r3;r6;A2;k16;A2;k24;r4;#10;A2;k17;r5;r6;A7;r1;#84;r21;r27;#8;r7;r18;vHsp;r2;r1;r2;r1;r1;#86;r4;Pk;Ri15;P~R#55;A2;i23;A2;k25;#87;#7;A2;i23;A2;k16;#11;#87;A2;k87;r14;#87;EX;RA3;r2;r1;o12;E__sat1;R#14;#17;EH;R#18;#21;EH0;R#22;#23;EH1;R#24;#25;EH2;R#26;#27;EH3;R#28;#29;Eq;R#20;i15;Er;R#15;i15;m3;RNL~RA2;i3;#53;#35;#88;r13;1;L~R#53;L~RA2;k25;r16;#31;A2;LH4;RA2;k16;o12;r17;LH5;RA2;k25;r18;#31;EX;RA1;r14;r13;A3;k88;A1;k89;r20;A2;k8;#2;r19;#52;E__arith;RE__wit;R#36;#37;E__varmap;RA1;o94;i15;#39;E__ff;RA7;o46;#40;k43;i44;i44;o45;A7;o47;#40;k43;i44;i44;o45;A4;o48;i15;#45;o50;#45;o51;A7;o47;#40;k43;i44;i44;o45;A4;o48;i15;#45;o52;#54;o51;#47;#48;#88;r1;r2;r1;A3;i4;i20;A2;k95;A1;k96;A2;k17;#56;o12;A1;k89;r8;o97;EX;RA6;k98;i15;#86;Lz;Ri15;A3;i4;i20;A2;k95;A1;k96;A2;k17;r1;o12;#89;o97;r1;r8;r4;A3;i4;i20;A2;k95;A1;k96;A2;k17;r8;o12;A1;k89;r9;o97;EX;RA6;k98;i15;A2;k17;r9;o12;Lz;Ri15;A3;i4;i20;A2;k95;A1;k96;r1;A1;k89;r11;o97;r1;r9;A1;k99;r9;A3;i4;i20;A2;k95;A1;k96;r9;#89;o97;r1;").
Qed.

  Lemma printf1_run : forall LB LK cr A M (model : Model) R (S canz : Z) K,
    dinvA LB LK cr A M model ->
    let MV := mrestrict (ahid A model) M in
    usp - 4096 <= S -> S + 32 <= usp -> S mod 16 = 0 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 717176 -> getr R 2%bv = Z_to_bv 64 S -> getr R 10%bv = Z_to_bv 64 86425 -> getr R 11%bv = Z_to_bv 64 (S + 24) ->
    (* WINDOW, old beside new: was [usp - 8388608 <= a]; DRV_ZWIN (Pm8DrvEntry). *)
    (forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true) ->
    (forall i, 65536 <= i < 1392640 -> MV (Z_to_bv 64 i) = None) ->
    rdn ASEGS MV (Z_to_bv 64 7015056) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    rdn ASEGS MV (Z_to_bv 64 (S + 24)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    stdout0A MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    K [] ->
    FrmInv.fp_ok fx ->
    (forall (fx' : PropExec.FPState) R' M1 (model1 : Model),
        FrmInv.fp_ok fx' ->
        dinvA LB LK cr A M1 model1 -> same_but_materialized model model1 ->
        (forall r, In r c_kept -> getr R' r = getr R r) ->
        getr R' 10%bv = Z_to_bv 64 2 ->
        stdoutA 0 (mrestrict (ahid A model1) M1) -> stdoutXA (mrestrict (ahid A model1) M1) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf1 S a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf1 S a -> mrestrict (ahid A model1) M1 (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
        (forall a : word, MV a <> None -> mrestrict (ahid A model1) M1 a <> None) ->
        srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 0xaf178) M1 rom) model1) K) ->
    srealizes ASEGS scfg (mkCfg (@mkst fx R (Z_to_bv 64 0x6a58c) M rom) model) (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) K).
  (* Proof: fuzz_bigint's text proof of this lemma ([As0DrvPrintf1.v] / [Bo0DrvPrintf1.v]) with this
     unit's addresses (read from this unit's walk statements, PR_CELLS, IMG_W_A and stdout cells),
     replacing the recorded term: it applied [wv_loop] and [dinv_frame], which now take the
     channel-reader premise ([di_rdr], [sbm_rdrA]). *)
  Proof.
    intros LB LK cr A M model R S canz K D MV HS1 HS2 HS16 Hcan R1 R2 R10 R11 WIN IMG CAN ARG SO FD1 HK0 HFP KONT.
    pose proof Hsp as Hsp'. destruct SO as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FW & BW).
    assert (PCg : forall LK' cr' A' M' (model' : Model), dinvA LB LK' cr' A' M' model' -> forall a n v, In (a, n, v) PR_CELLS ->
                  rdn ASEGS (mrestrict (ahid A' model') M') (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros LK' cr' A' M' model' D' a n v Hin; exact (pr_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hpr M0 _ _ _ _ _ _ a n v D' Hin)).
    assert (P1g : forall LK' cr' A' M' (model' : Model), dinvA LB LK' cr' A' M' model' -> forall a v, In (a, 1, v) PR_CELLS -> 0 <= v < 2 ^ 64 ->
                  rdn ASEGS (mrestrict (ahid A' model') M') (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros LK' cr' A' M' model' D' a v Hin Hv. rewrite <- (ArtMem.art_bytes1 v Hv). exact (PCg _ _ _ _ _ D' a 1 v Hin). }
    set (V := fun n : nat => match n with 2%nat => S | 40%nat => canz | _ => 0 end).
    destruct (AS0DRVP_dpA.dpA_conc fx R MV V) as
(fx1 & R1' & MV1 & AGR & _ & AFRZ & AMS & AKS & Ar1 & Ar2 & Ar5 & Ar8 & Ar9 & Ar10 & Ar11 & Ar12 & Ar13 & Ar14 & Ar15 & Ar16 & Ar17 & Ar18 & Ar19 & Ar20 & Ar21 & Ar22 & Ar23 & Ar24 & Ar25 & Ar26 & Ar27 & Aa892264 & Am1096 & Am1088 & Am1080 & Am1064 & Am1056 & Am1048 & Am1040 & Am1032 & Am1024 & Am1016 & Aa892232 & Am1104 & Aa6361368 & Am832 & Am1072 & Am1000 & Am976 & Am992 & Am1008 & Am984 & Am896 & Am464 & Am968 & Am960 & Am904 & Am928 & Am576 & Am912 & Am920 & Am936 & Am952 & Am944 & Am568 & Am560 & Am552 & Am544 & Am536 & Am528 & Am520 & Am512 & Am504 & Am496 & Am488 & Am480 & Am472 & Aa892224 & Aa892208 & Aa892200 & Aa892248 & Aa892328 & Aa892192 & Am176 & Am184 & Am192 & Am200 & Am168 & Am456 & Am160 & Am152 & Am144 & Am136 & Am128 & Am120 & Am112 & Am104 & Am96 & Am88 & Am80 & Am72 & Am64 & Am56 & Am40 & Am32 & Am24 & Am16 & Am8 & Ad1 & Ad2 & Ad3 & Ad4).
    all: cbn [V].
    all: try assumption.
    all: try (clear - Hsp' HS1 HS2 Hcan; lia).
    - intros d k Hd Hk. apply (WIN (S - 3232) 3232); lia.
    - intros i Hi. apply (store_ok_defined sp0); [lia|]. apply (WIN (S - 3232) 3232); lia.
    -
      intros i Hi. apply (stk_sh0 scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ _ D).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      clear - Hsp' Hal HS1 HS2 HS16 Hi. lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    -
      apply Pm8ArtFsInv.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x15180 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    -
      apply Pm8ArtFsInv.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x6b1240 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - intros d k Hd Hk. apply (FW 1407568 4); lia.
    - intros d k Hd Hk. apply (FW 1407576 8); lia.
    - intros d k Hd Hk. apply (FW 1407584 8); lia.
    - intros d k Hd Hk. apply (FW 1407600 8); lia.
    - intros d k Hd Hk. apply (FW 1407608 8); lia.
    - intros d k Hd Hk. apply (FW 1407624 8); lia.
    - intros d k Hd Hk. apply (FW 1407640 8); lia.
    - intros d k Hd Hk. apply (FW 1407704 4); lia.
    - intros d k Hd Hk. apply (BW 7017072 1); unfold SOBUF; lia.
    - apply (P1g _ _ _ _ _ D); [unfold PR_CELLS; cbn [In]; tauto | lia].
    - apply (P1g _ _ _ _ _ D); [unfold PR_CELLS; cbn [In]; tauto | lia].
    - exact (PCg _ _ _ _ _ D 0x15c9b8 8 0x7fff8000 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PCg _ _ _ _ _ D 0x154fd8 8 0x142a00 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PCg _ _ _ _ _ D 0x154fe0 8 0x13c71c ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - apply (P1g _ _ _ _ _ D); [unfold PR_CELLS; cbn [In]; tauto | lia].
    - exact (PCg _ _ _ _ _ D 0x155158 8 0x144f04 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PCg _ _ _ _ _ D 0x155160 8 0x145308 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    -
      unfold V in AFRZ, AMS; cbn beta iota in AFRZ, AMS. cbn [V] in *.
      set (WA := fun a : Z => S - 3232 <= a < S \/ 1407568 <= a < 1407572 \/ 1407576 <= a < 1407592 \/ 1407600 <= a < 1407616 \/ 1407624 <= a < 1407632 \/ 1407640 <= a < 1407648 \/ 1407704 <= a < 1407708 \/ a = 7017072).
      assert (FRA : forall a, 0 <= a < 2 ^ 64 -> ~ WA a -> MV1 (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
      { intros a Ha Hn. apply AFRZ; [exact Ha | | | | | | | | | |]; intros X; apply Hn; unfold WA; lia. }
      apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model fx fx1 R (Z_to_bv 64 0x6a58c) R1' (Z_to_bv 64 0x13c51c) MV1 WA _ D AMS AGR FRA).
      { intros a Ha. unfold CWA. destruct Ha as [Ha|Ha]; [right; left; clear - Hsp' HS1 HS2 Ha; lia|]. right; right.
        destruct (Z.eq_dec a 7017072) as [->|Ne].
        - exists 0x690a80, 0x6b1f08. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
        - exists 0x157960, 0x157c60. split; [unfold IMG_W_A; cbn [In]; tauto | clear - Ha Ne; lia]. }
      intros M1 model1 D1 SBM1 VIS1 FRM1.
      subst MV1.
      set (MVa := mrestrict (ahid A model1) M1) in *.
      assert (WIN1 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVa (Z_to_bv 64 (a + d)) k = true)
        by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MVa _ AGR); apply (WIN a n); assumption).
      assert (FW1 : forall a n, 1407568 <= a -> a + n <= 1407568 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVa (Z_to_bv 64 (a + d)) k = true)
        by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MVa _ AGR); apply (FW a n); assumption).
      assert (BW1 : forall a n, SOBUF <= a -> a + n <= SOBUF + 1024 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVa (Z_to_bv 64 (a + d)) k = true)
        by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MVa _ AGR); apply (BW a n); assumption).
      assert (IMG1 : forall i, 65536 <= i < 1392640 -> MVa (Z_to_bv 64 i) = None).
      { intros i Hi. rewrite FRA; [apply IMG; exact Hi | lia | unfold WA; clear - Hsp' HS1 HS2 Hi; lia]. }
      assert (CAN1 : rdn ASEGS MVa (Z_to_bv 64 7015056) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz))).
      { apply (TRf _ _ _ FRA _ _ _ CAN); [lia | cbn; lia | intros i Hi X; unfold WA in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (F1a : rdn ASEGS MVa (Z_to_bv 64 1407708) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))).
      { apply (TRf _ _ _ FRA _ _ _ F1); [lia | cbn; lia | intros i Hi X; unfold WA in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (F3a : rdn ASEGS MVa (Z_to_bv 64 1407664) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024))).
      { apply (TRf _ _ _ FRA _ _ _ F3); [lia | cbn; lia | intros i Hi X; unfold WA in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (F6a : rdn ASEGS MVa (Z_to_bv 64 1407656) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 SOBUF))).
      { apply (TRf _ _ _ FRA _ _ _ F6); [lia | cbn; lia | intros i Hi X; unfold WA in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (F9a : rdn ASEGS MVa (Z_to_bv 64 1407688) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1))).
      { apply (TRf _ _ _ FRA _ _ _ F9); [lia | cbn; lia | intros i Hi X; unfold WA in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (FD1a : fd_lookup (m_fds model1) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) by (rewrite (sbm_fds' _ _ SBM1); exact FD1).
      eapply (rz_ioctl_winsz_lz ASEGS scfg R1' _ M1 model1 ECALLW (Z_to_bv 64 1) (FdChannel (Z_to_bv 64 1)));
        [exact fetch_ioctlA | apply is_ecall_ECALLW | exact (di_halt _ _ _ _ _ _ _ _ _ _ D1) | exact Ar17 | exact Ar10 | rewrite u64_lit by lia; lia
        | exact FD1a | reflexivity | exact Ar11 |].
      rewrite v_addi_pc4 by lia. change (0x13c51c + 4) with 0x13c520.
      set (R1b := regupd R1' 10%bv (errno_ret ENOTTY)).
      assert (RBo : forall r : reg, r <> 10%bv -> getr R1b r = getr R1' r) by (intros r Hr; unfold R1b; apply getr_other; exact Hr).
      assert (RB10 : getr R1b 10%bv = Z_to_bv 64 18446744073709551591).
      { unfold R1b. rewrite getr_same by (intros X; discriminate X). rewrite errno_ret_lit. apply bv_eq. reflexivity. }
      set (VB := fun n : nat => match n with 2%nat => S - 1104 | 40%nat => canz | _ => 0 end).
      assert (Bg2 : getr R1b (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (S - 1104)) by (rewrite RBo by (intros X; discriminate X); exact Ar2).
      assert (Bg8 : getr R1b (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 7015056) by (rewrite RBo by (intros X; discriminate X); exact Ar8).
      assert (Bg9 : getr R1b (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1) by (rewrite RBo by (intros X; discriminate X); exact Ar9).
      assert (Bg13 : getr R1b (Z_to_bv 5 (Z.of_nat 13)) = Z_to_bv 64 86427) by (rewrite RBo by (intros X; discriminate X); exact Ar13).
      assert (Bg15 : getr R1b (Z_to_bv 5 (Z.of_nat 15)) = Z_to_bv 64 1) by (rewrite RBo by (intros X; discriminate X); exact Ar15).
      assert (Bg16 : getr R1b (Z_to_bv 5 (Z.of_nat 16)) = Z_to_bv 64 1407568) by (rewrite RBo by (intros X; discriminate X); exact Ar16).
      assert (Bg18 : getr R1b (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 86427) by (rewrite RBo by (intros X; discriminate X); exact Ar18).
      assert (Bg19 : getr R1b (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 1) by (rewrite RBo by (intros X; discriminate X); exact Ar19).
      assert (Bg20 : getr R1b (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 0) by (rewrite RBo by (intros X; discriminate X); exact Ar20).
      assert (Bg21 : getr R1b (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 86428) by (rewrite RBo by (intros X; discriminate X); exact Ar21).
      assert (Bg22 : getr R1b (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 1) by (rewrite RBo by (intros X; discriminate X); exact Ar22).
      destruct (AS0DRVP_dpB_notty.dpB_notty_conc fx1 R1b MVa VB ltac:(cbn [VB]; clear - Hsp' HS1 HS2; lia) Hcan Bg2 Bg8 Bg9 RB10 Bg13 Bg15 Bg16 Bg18 Bg19 Bg20 Bg21 Bg22
                  ltac:(cbn [VB]; clear - Hsp' HS1 HS2; lia)) as
(fx2 & R2' & MV2 & BGR & _ & BFRZ & BMS & BKS & Br1 & Br2 & Br8 & Br9 & Br10 & Br11 & Br12 & Br13 & Br17 & Br18 & Br19 & Br21 & Br22 & Bm80 & Bm88 & Bm96 & Bm104 & Bm72 & Bm64 & Bm56 & Bm48 & Bm40 & Bm32 & Bm24 & Bm16 & Bm8 & Ba892336 & Bd1).
      all: cbn [VB].
      { unfold AS0DRVP_dpB_notty.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
      { intros d k Hd Hk. apply (WIN1 (S - 1104 - 112) 112); clear - Hsp' HS1 HS2 Hd Hk; lia. }
      { intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN1 (S - 1104 - 112) 112); clear - Hsp' HS1 HS2 Hi; lia. }
      { exact IMG1. }
      { intros d k Hd Hk. apply (FW1 1407712 4); lia. }
      { exact CAN1. }
      { exact Aa892232. }
      { exact Aa892248. }
      { exact F9a. }
      unfold VB in BFRZ, BMS; cbn beta iota in BFRZ, BMS. cbn [VB] in *.
      set (WB := fun a : Z => S - 1216 <= a < S - 1104 \/ 1407712 <= a < 1407716).
      assert (FRB : forall a, 0 <= a < 2 ^ 64 -> ~ WB a -> MV2 (Z_to_bv 64 a) = MVa (Z_to_bv 64 a)).
      { intros a Ha Hn. apply BFRZ; [exact Ha | |]; intros X; apply Hn; unfold WB; clear - X; lia. }
      apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M1 model1 fx1 fx2 R1b (Z_to_bv 64 0x13c520) R2' (Z_to_bv 64 0x13b85c) MV2 WB _ D1 BMS BGR FRB).
      { intros a Ha. unfold CWA. destruct Ha as [Ha|Ha]; [right; left; clear - Hsp' HS1 HS2 Ha; lia|]. right; right.
        exists 0x157960, 0x157c60. split; [unfold IMG_W_A; cbn [In]; tauto | clear - Ha; lia]. }
      intros M2 model2 D2 SBM2 VIS2 FRM2.
      subst MV2. set (MVb := mrestrict (ahid A model2) M2) in *.
      assert (WIN2 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVb (Z_to_bv 64 (a + d)) k = true)
        by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MVa MVb _ BGR); apply (WIN1 a n); assumption).
      assert (IMG2 : forall i, 65536 <= i < 1392640 -> MVb (Z_to_bv 64 i) = None).
      { intros i Hi. rewrite FRB; [apply IMG1; exact Hi | lia | unfold WB; clear - Hsp' HS1 HS2 Hi; lia]. }
      assert (F9b : rdn ASEGS MVb (Z_to_bv 64 1407688) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1))).
      { apply (TRf _ _ _ FRB _ _ _ F9a); [lia | cbn; lia | intros i Hi X; unfold WB in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (DATA1 : rdn ASEGS MVb (Z_to_bv 64 7017072) 1 = Some [Z_to_bv 8 48]).
      { apply (TRf _ _ _ FRB _ _ _ Aa6361368); [lia | cbn; lia | intros i Hi X; unfold WB in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (DATA2 : rdn ASEGS MVb (Z_to_bv 64 86427) 1 = Some [Z_to_bv 8 10]).
      { apply (img_cell MVb 86427 1 _ nl_imgA); [lia | cbn; lia | intros i Hi; apply IMG2; cbn in Hi; lia]. }
      assert (FD1b : fd_lookup (m_fds model2) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) by (rewrite (sbm_fds' _ _ SBM2); exact FD1a).
      pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D2) as (HH2 & HL2 & HA2 & HM2 & Hh2).
      set (q := S - 1104 - 104) in *.
      assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
      assert (Hf : 0 <= 1407568 /\ (1407568 + 124 <= q \/ q + 32 + 16 <= 1407568 + 120) /\ 1407568 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
      assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model2) = false).
      { intros x Hx. apply (nl_pt _ _ _ _ _ _ x D2); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
      unfold W. change (map (WriteEv (Z_to_bv 64 1)) [Z_to_bv 8 48; Z_to_bv 8 10]) with (map (WriteEv (Z_to_bv 64 1)) ([Z_to_bv 8 48] ++ [Z_to_bv 8 10])).
      apply (wv_loop scfg (ahid A model2) A HH2 (m_vm_lazy model2) HL2 HA2 1407568 1 ltac:(lia) q (q + 32) Hq Hf NLq K HK0 2%nat true R2' M2 model2 q 2 7017072 1 86427 1 [Z_to_bv 8 48] [Z_to_bv 8 10]).
      { cbn. lia. }
      { reflexivity. }
      { exact HM2. }
      { exact Hh2. }
      { exact FD1b. }
      { exact (di_rdr _ _ _ _ _ _ _ _ _ _ D2). }
      { unfold wv_regs. repeat split; try assumption. }
      { fold MVb. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
        split; [exact Bm104|]. split; [replace (q + 8) with (S - 1104 - 96) by (unfold q; ring); exact Bm96|].
        split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN2 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
        split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA1|];
                intros x Hx; apply (nl_pt _ _ _ _ _ _ x D2); lia|].
        split; [intros X; discriminate X|]. intros _.
        split; [replace (q + 16) with (S - 1104 - 88) by (unfold q; ring); exact Bm88|].
        split; [replace (q + 24) with (S - 1104 - 80) by (unfold q; ring); exact Bm80|].
        split; [|lia].
        unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA2|].
        intros x Hx; apply (nl_pt _ _ _ _ _ _ x D2); lia. }
      { lia. }
      { exact F9b. }
      intros R3 M3 model3 MI3 SBM3 KR3 FRM3 FRV3 GRM3 GRV3.
      assert (D3 : dinvA LB LK cr A M3 model3).
      { apply (dinv_frame scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M2 M3 model2 model3 D2).
        - intros a Ha Hn. apply FRM3; [exact Ha|]. intros X. apply Hn. unfold CWA. right; left. unfold q in X. clear - Hsp' HS1 HS2 X. lia.
        - exact GRM3.
        - exact (sbm_vml _ _ SBM3).
        - exact MI3.
        - rewrite (sbm_halted_eq _ _ SBM3). exact Hh2.
        - exact (sbm_rdrA _ _ SBM3). }
      pose proof (ahid_sbm A model2 model3 SBM3) as AH3.
      set (MVc := mrestrict (ahid A model3) M3) in *.
      assert (EQc : mrestrict (ahid A model2) M3 = MVc) by (unfold MVc; rewrite AH3; reflexivity).
      rewrite EQc in FRV3, GRV3. fold MVb in FRV3, GRV3.
      set (SC := S - 1104 - 112) in *.
      assert (FRca : forall i, 0 <= i < 2 ^ 64 -> ~ (SC <= i < S - 1104) -> ~ (1407712 <= i < 1407716) -> MVc (Z_to_bv 64 i) = MVa (Z_to_bv 64 i)).
      { intros i Hi N1 N2. rewrite FRV3 by (unfold q, SC in *; clear - Hi N1; lia). apply FRB; [exact Hi | unfold WB, SC in *; clear - N1 N2; lia]. }
      assert (cellA : forall off k (n : nat) bs, rdn ASEGS MVa (Z_to_bv 64 (S - k)) n = Some bs ->
                (off + k =? 1216) && (Z.of_nat n <=? k) && (k <=? 1104) = true -> rdn ASEGS MVc (Z_to_bv 64 (SC + off)) n = Some bs).
      { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
        apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (SC + off) with (S - k) by (unfold SC; lia).
        apply (rdn_tr MVa MVc _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
        intros i Hi. apply FRca; unfold SC; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
      assert (cellB : forall off k (n : nat) bs, rdn ASEGS MVb (Z_to_bv 64 (S - 1104 - k)) n = Some bs ->
                (off + k =? 112) && (Z.of_nat n <=? k) && (k <=? 72) = true -> rdn ASEGS MVc (Z_to_bv 64 (SC + off)) n = Some bs).
      { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
        apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (SC + off) with (S - 1104 - k) by (unfold SC; lia).
        apply (rdn_tr MVb MVc _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
        intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
      assert (cellL : forall a (n : nat) bs, rdn ASEGS MVa (Z_to_bv 64 a) n = Some bs ->
                (0 <=? a) && (a + Z.of_nat n <=? 10000000) && ((a + Z.of_nat n <=? 1407712) || (1407716 <=? a)) = true -> rdn ASEGS MVc (Z_to_bv 64 a) n = Some bs).
      { intros a n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
        apply Z.leb_le in Hb1, Hb2. apply orb_prop in Hb3. rewrite !Z.leb_le in Hb3.
        apply (rdn_tr MVa MVc _ _ _ Hr); [exact Hb1 | lia|].
        intros i Hi. apply FRca; unfold SC; clear - Hsp' HS1 HS2 Hb1 Hb2 Hb3 Hi; lia. }
      assert (WIN3 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVc (Z_to_bv 64 (a + d)) k = true)
        by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MVb MVc _ GRV3); apply (WIN2 a n); assumption).
      assert (FW3 : forall a n, 1407568 <= a -> a + n <= 1407568 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVc (Z_to_bv 64 (a + d)) k = true)
        by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MVb MVc _ GRV3); apply (store_ok_mono ASEGS k MVa MVb _ BGR); apply (FW1 a n); assumption).
      assert (IMG3 : forall i, 65536 <= i < 1392640 -> MVc (Z_to_bv 64 i) = None).
      { intros i Hi. rewrite FRV3; [apply IMG2; exact Hi | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
      assert (ST910489 : rdn ASEGS MVc (Z_to_bv 64 1431193) 1 = Some [Z_to_bv 8 1]) by (apply (P1g _ _ _ _ _ D3); [unfold PR_CELLS; cbn [In]; tauto | lia]).
      assert (ST881824 : rdn ASEGS MVc (Z_to_bv 64 1397080) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1330948)))
        by exact (PCg _ _ _ _ _ D3 0x155158 8 0x144f04 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
      assert (R3k : forall r : reg, In r WV_KEEP -> getr R3 r = getr R2' r) by exact KR3.
      assert (R2k : forall x, In x AS0DRVP_dpB_notty.KS_dpB_notty -> getr R2' (Z_to_bv 5 (Z.of_nat x)) = getr R1' (Z_to_bv 5 (Z.of_nat x))).
      { intros x Hx. rewrite (BKS x Hx). apply RBo. intros X. unfold AS0DRVP_dpB_notty.KS_dpB_notty in Hx. cbn [In] in Hx.
        repeat (destruct Hx as [<-|Hx]; [discriminate X|]). exact Hx. }
      set (VC := fun n : nat => match n with
                 | 2%nat => SC | 40%nat => canz
                 | 8%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 8))) | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9)))
                 | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
                 | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
                 | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22))) | 23%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 23)))
                 | 24%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 24))) | 25%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 25)))
                 | 26%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 26))) | 27%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 27)))
                 | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18))) | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19)))
                 | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20))) | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
                 | 125%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 25))) | 127%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 27)))
                 | _ => 0 end).
      assert (Cg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VC 2%nat)) by (eapply eq_trans; [exact (R3k 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Br2]).
      assert (Cg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 1) by (eapply eq_trans; [exact (R3k 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Br8]).
      assert (Cg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1407568) by (eapply eq_trans; [exact (R3k 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Br9]).
      assert (Cg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7015056) by (eapply eq_trans; [exact (R3k 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Br21]).
      assert (Cg23 : getr R3 (Z_to_bv 5 (Z.of_nat 23)) = Z_to_bv 64 86427).
      { eapply eq_trans; [exact (R3k 23%bv ltac:(unfold WV_KEEP; cbn [In]; tauto))|]. eapply eq_trans; [|exact Ar23]. apply (R2k 23%nat). unfold AS0DRVP_dpB_notty.KS_dpB_notty. cbn [In]. tauto. }
      assert (Cg24 : getr R3 (Z_to_bv 5 (Z.of_nat 24)) = Z_to_bv 64 1).
      { eapply eq_trans; [exact (R3k 24%bv ltac:(unfold WV_KEEP; cbn [In]; tauto))|]. eapply eq_trans; [|exact Ar24]. apply (R2k 24%nat). unfold AS0DRVP_dpB_notty.KS_dpB_notty. cbn [In]. tauto. }
      assert (Cg26 : getr R3 (Z_to_bv 5 (Z.of_nat 26)) = Z_to_bv 64 1).
      { eapply eq_trans; [exact (R3k 26%bv ltac:(unfold WV_KEEP; cbn [In]; tauto))|]. eapply eq_trans; [|exact Ar26]. apply (R2k 26%nat). unfold AS0DRVP_dpB_notty.KS_dpB_notty. cbn [In]. tauto. }
      assert (Cg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VC 118%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
      assert (Cg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VC 119%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
      assert (Cg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VC 120%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
      assert (Cg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VC 122%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
      assert (Cg25 : getr R3 (Z_to_bv 5 (Z.of_nat 25)) = Z_to_bv 64 (VC 125%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
      assert (Cg27 : getr R3 (Z_to_bv 5 (Z.of_nat 27)) = Z_to_bv 64 (VC 127%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
      assert (HSC : 0 <= VC 2%nat < 2 ^ 64) by (cbn [VC]; unfold SC; clear - Hsp' HS1 HS2; lia).
      assert (HSCr : 140735332552704 <= VC 2%nat <= 140737488355328) by (cbn [VC]; unfold SC; clear - Hsp' HS1 HS2; lia).
      assert (HSCa : AS0DRVP_dpCd.aligned (VC 2%nat) 16).
      { cbn [VC]. unfold AS0DRVP_dpCd.aligned, SC. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
      assert (CWR : L5Defs.L5.writable ASEGS MVc (VC 2%nat - 2016) 2160).
      { cbn [VC]. intros d k Hd Hk. apply (WIN3 (SC - 2016) 2160); unfold SC; clear - Hsp' HS1 HS2 Hd Hk; lia. }
      assert (CDF : L5Defs.L5.defined MVc (VC 2%nat - 2016) 2160).
      { cbn [VC]. intros i Hi. apply (store_ok_defined sp0); [unfold SC; clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (SC - 2016) 2160); unfold SC; clear - Hsp' HS1 HS2 Hi; lia. }
      assert (Cv1088 : L5Defs.L5.u64_at ASEGS MVc (VC 2%nat + 1088) (VC 2%nat + 1240)).
      { cbn [VC]. replace (SC + 1240) with (S + 24) by (unfold SC; ring). exact (cellA 1088 128 _ _ Am128 eq_refl). }
      assert (Cv1144 : L5Defs.L5.u64_at ASEGS MVc (VC 2%nat + 1144) (VC 2%nat + 1240)).
      { cbn [VC]. replace (SC + 1240) with (S + 24) by (unfold SC; ring). exact (cellA 1144 72 _ _ Am72 eq_refl). }
      destruct (AS0DRVP_dpCd.dpCd_conc fx2 R3 MVc VC
           HSC (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) Hcan
           (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) Cg2 Cg8 Cg9 Cg18 Cg19 Cg20 Cg21 Cg22 Cg23 Cg24 Cg25 Cg26 Cg27 HSCr HSCa CWR CDF IMG3
           (fun d k Hd Hk => FW3 1407568 4 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1407600 8 ltac:(lia) ltac:(lia) d k Hd Hk)
           (fun d k Hd Hk => FW3 1407608 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1407624 8 ltac:(lia) ltac:(lia) d k Hd Hk) (cellL _ _ _ F6a eq_refl) (cellL _ _ _ F3a eq_refl)
           (cellL _ _ _ CAN1 eq_refl) (cellB 40 72 _ _ Bm72 eq_refl) (cellB 104 8 _ _ Bm8 eq_refl) (cellB 96 16 _ _ Bm16 eq_refl) (cellB 88 24 _ _ Bm24 eq_refl) (cellB 80 32 _ _ Bm32 eq_refl)
           (cellB 72 40 _ _ Bm40 eq_refl) (cellB 64 48 _ _ Bm48 eq_refl) (cellB 56 56 _ _ Bm56 eq_refl) (cellB 48 64 _ _ Bm64 eq_refl) (cellA 120 1096 _ _ Am1096 eq_refl)
           (cellA 136 1080 _ _ Am1080 eq_refl) (cellA 128 1088 _ _ Am1088 eq_refl) ST910489 ST881824 (cellA 200 1016 _ _ Am1016 eq_refl) (cellA 192 1024 _ _ Am1024 eq_refl)
           (cellA 184 1032 _ _ Am1032 eq_refl) (cellA 176 1040 _ _ Am1040 eq_refl) (cellA 168 1048 _ _ Am1048 eq_refl) (cellA 160 1056 _ _ Am1056 eq_refl) (cellA 152 1064 _ _ Am1064 eq_refl)
           (cellA 304 912 _ _ Am912 eq_refl) (cellA 640 576 _ _ Am576 eq_refl) (cellA 744 472 _ _ Am472 eq_refl) (cellA 736 480 _ _ Am480 eq_refl) (cellA 728 488 _ _ Am488 eq_refl)
           (cellA 720 496 _ _ Am496 eq_refl) (cellA 712 504 _ _ Am504 eq_refl) (cellA 704 512 _ _ Am512 eq_refl) (cellA 696 520 _ _ Am520 eq_refl) (cellA 688 528 _ _ Am528 eq_refl)
           (cellA 680 536 _ _ Am536 eq_refl) (cellA 672 544 _ _ Am544 eq_refl) (cellA 664 552 _ _ Am552 eq_refl) (cellA 656 560 _ _ Am560 eq_refl) (cellA 648 568 _ _ Am568 eq_refl)
           (cellL _ _ _ Aa892192 eq_refl) (cellA 1056 160 _ _ Am160 eq_refl) (cellA 1112 104 _ _ Am104 eq_refl) (cellA 1104 112 _ _ Am112 eq_refl) (cellA 1096 120 _ _ Am120 eq_refl) Cv1088
           (cellA 1080 136 _ _ Am136 eq_refl) (cellA 1072 144 _ _ Am144 eq_refl) (cellA 1064 152 _ _ Am152 eq_refl) (cellA 1160 56 _ _ Am56 eq_refl) (cellA 1152 64 _ _ Am64 eq_refl) Cv1144
           (cellA 1136 80 _ _ Am80 eq_refl) (cellA 1208 8 _ _ Am8 eq_refl) (cellA 1200 16 _ _ Am16 eq_refl) (cellA 1192 24 _ _ Am24 eq_refl)) as
(fx3 & R4 & MV4 & CGR & _ & CFRZ & CMS & CKS & Cr1 & Cr2 & Cr8 & Cr9 & Cr10 & Cr11 & Cr12 & Cr13 & Cr14 & Cr15 & Cr18 & Cr19 & Cr20 & Cr21 & Cr22 & Cr23 & Cr24 & Cr25 & Cr26 & Cr27 & Ca892192 & Ca892232 & Ca892248 & Ca892224).
      unfold VC in CFRZ, CMS; cbn beta iota in CFRZ, CMS. cbn [VC] in *.
      set (WC := fun a : Z => SC - 2016 <= a < SC - 2016 + 2160 \/ 1407568 <= a < 1407572 \/ 1407600 <= a < 1407616 \/ 1407624 <= a < 1407632).
      assert (FRC : forall a, 0 <= a < 2 ^ 64 -> ~ WC a -> MV4 (Z_to_bv 64 a) = MVc (Z_to_bv 64 a)).
      { intros a Ha Hn. apply CFRZ; [exact Ha | | | | |]; intros X; apply Hn; unfold WC; clear - X; lia. }
      apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M3 model3 fx2 fx3 R3 (Z_to_bv 64 0x13b868) R4 (Z_to_bv 64 0xaf178) MV4 WC _ D3 CMS CGR FRC).
      { intros a Ha. unfold CWA. destruct Ha as [Ha|Ha]; [right; left; unfold SC in Ha; clear - Hsp' HS1 HS2 Ha; lia|]. right; right.
        exists 0x157960, 0x157c60. split; [unfold IMG_W_A; cbn [In]; tauto | clear - Ha; lia]. }
      intros M4 model4 D4 SBM4 VIS4 FRM4.
      assert (cellL4 : forall a (n : nat) bs, rdn ASEGS MVc (Z_to_bv 64 a) n = Some bs ->
                (0 <=? a) && (a + Z.of_nat n <=? 10000000) && ((a + Z.of_nat n <=? 1407568) || (1407632 <=? a) || ((1407572 <=? a) && (a + Z.of_nat n <=? 1407600)) || ((1407616 <=? a) && (a + Z.of_nat n <=? 1407624))) = true ->
                rdn ASEGS MV4 (Z_to_bv 64 a) n = Some bs).
      { intros a n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
        apply Z.leb_le in Hb1, Hb2. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in Hb3.
        apply (rdn_tr MVc MV4 _ _ _ Hr); [exact Hb1 | lia|].
        intros i Hi. apply FRC; [lia|]. unfold WC, SC. clear - Hsp' HS1 HS2 Hb1 Hb2 Hb3 Hi. lia. }
      assert (HFP3 : FrmInv.fp_ok fx3).
      (* the FPState arguments are given: [eapply] would fill the class-typed [fx] by
         instance search with the newest [fx3] *)
      { exact (Pm8FrmInv.msteps_fp_ok fx2 fx3 _ _ _ _ _ _ _ _ CMS
                 (Pm8FrmInv.msteps_fp_ok fx1 fx2 _ _ _ _ _ _ _ _ BMS
                    (Pm8FrmInv.msteps_fp_ok fx fx1 _ _ _ _ _ _ _ _ AMS HFP))). }
      apply (KONT fx3 R4 M4 model4 HFP3 D4).
      + exact (same_but_materialized_trans _ _ _ SBM1 (same_but_materialized_trans _ _ _ SBM2 (same_but_materialized_trans _ _ _ SBM3 SBM4))).
      +
        assert (K34 : forall x, (x = 3 \/ x = 4)%nat -> getr R4 (Z_to_bv 5 (Z.of_nat x)) = getr R (Z_to_bv 5 (Z.of_nat x))).
        { intros x [-> | ->].
          all: (eapply eq_trans; [apply CKS; unfold AS0DRVP_dpCd.KS_dpCd; cbn [In]; repeat first [left; reflexivity | right]|]).
          all: (eapply eq_trans; [apply R3k; unfold WV_KEEP; cbn [In]; repeat first [left; apply bv_eq; reflexivity | right]|]).
          all: (eapply eq_trans; [apply R2k; unfold AS0DRVP_dpB_notty.KS_dpB_notty; cbn [In]; repeat first [left; reflexivity | right]|]).
          all: (apply AKS; unfold AS0DRVP_dpA.KS_dpA; cbn [In]; repeat first [left; reflexivity | right]). }
        intros r Hr. unfold c_kept in Hr. cbn [In] in Hr.
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr2|]; rewrite R2; f_equal; unfold SC; ring|].
        destruct Hr as [<-|Hr]; [exact (K34 3%nat ltac:(left; reflexivity))|].
        destruct Hr as [<-|Hr]; [exact (K34 4%nat ltac:(right; reflexivity))|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr8|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr9|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr18|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr19|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr20|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr21|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr22|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr23|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr24|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr25|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr26|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr27|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr.
      + exact Cr10.
      +
        rewrite VIS4. unfold stdoutA.
        split; [exact Ca892192|].
        split; [exact (cellL4 _ _ _ (cellL _ _ _ F3a eq_refl) eq_refl)|].
        split; [exact Ca892224|].
        split; [exact Ca892232|].
        split; [exact Ca892248|].
        split; [exact (cellL4 _ _ _ (cellL _ _ _ F1a eq_refl) eq_refl)|].
        split.
        { apply (cellL4 1407712 4%nat); [|reflexivity]. rewrite <- le4_m1.
          apply (rdn_tr MVb MVc _ _ _ Ba892336); [lia | cbn; lia|]. intros i Hi. apply FRV3; [cbn in Hi; lia|]. unfold q. cbn in Hi. clear - Hsp' HS1 HS2 Hi. lia. }
        split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MVc MV4 _ CGR); apply (FW3 a n); assumption|].
        split.
        { intros a n H1 H2 d k Hd Hk. apply (store_ok_mono ASEGS k MVc MV4 _ CGR). apply (store_ok_mono ASEGS k MVb MVc _ GRV3).
          apply (store_ok_mono ASEGS k MVa MVb _ BGR). apply (BW1 a n); assumption. }
        intros i Hi. lia.
      +
        rewrite VIS4. unfold stdoutXA.
        split; [exact (cellL4 _ _ _ (cellL _ _ _ Aa892264 eq_refl) eq_refl)|].
        split; [exact (cellL4 _ _ _ (cellL _ _ _ F9a eq_refl) eq_refl)|].
        split; [exact (cellL4 _ _ _ (cellL _ _ _ F6a eq_refl) eq_refl)|].
        split; [exact (cellL4 _ _ _ (cellL _ _ _ Aa892200 eq_refl) eq_refl) | exact (cellL4 _ _ _ (cellL _ _ _ Aa892208 eq_refl) eq_refl)].
      +
        intros a Ha Hn.
        rewrite FRM4 by (exact Ha || (intros X; apply Hn; unfold Wpf1, WC, SC, SOBUF in *; clear - Hsp' HS1 HS2 X; lia)).
        rewrite FRM3 by (exact Ha || (intros X; apply Hn; unfold Wpf1, q, SOBUF in *; clear - Hsp' HS1 HS2 X; lia)).
        rewrite FRM2 by (exact Ha || (intros X; apply Hn; unfold Wpf1, WB, SOBUF in *; clear - Hsp' HS1 HS2 X; lia)).
        apply FRM1; [exact Ha|]. intros X; apply Hn; unfold Wpf1, WA, SOBUF in *; clear - Hsp' HS1 HS2 X; lia.
      +
        intros a Ha Hn. rewrite VIS4.
        rewrite FRC by (exact Ha || (intros X; apply Hn; unfold Wpf1, WC, SC, SOBUF in *; clear - Hsp' HS1 HS2 X; lia)).
        rewrite FRV3 by (exact Ha || (intros X; apply Hn; unfold Wpf1, q, SOBUF in *; clear - Hsp' HS1 HS2 X; lia)).
        rewrite FRB by (exact Ha || (intros X; apply Hn; unfold Wpf1, WB, SOBUF in *; clear - Hsp' HS1 HS2 X; lia)).
        apply FRA; [exact Ha|]. intros X; apply Hn; unfold Wpf1, WA, SOBUF in *; clear - Hsp' HS1 HS2 X; lia.
      + intros a Ha. rewrite VIS4. apply CGR. apply GRV3. apply BGR. apply AGR. exact Ha.
  Qed.
End Printf1.
End FPX_1.
