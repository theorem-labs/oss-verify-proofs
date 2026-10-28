(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_x4body_iface RF_huf_x4body_kit RF_huf_x4body_kit2 RF_huf_kx_ez.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x4body () := "C5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zregC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4ztabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac4zshzK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission6Common5KXTac;tab_img_chkC5ARocqVerifyHarness?AgentSubmission6Common5KXTac=ztab_fact_imgK47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op205C5ARocqVerifyHarness?AgentSubmission6Common4KXGo>Forall_map_iffC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02C5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoI47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4body:x4_ctz_tabC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9ztab_factC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC47Corelib4Init5Logic5proj2C47Corelib4Init5Peano2ltC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission6Common4KXGo6all_roC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>wr_at_apart_roC47Corelib4Init5Logic6eq_indK46Stdlib9micromega=RingMicromega5Psatz02C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC45stdpp9bitvector;definitions;bv_unsignedK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr02K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr01K47Corelib7Numbers7BinNums1Z03K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr01C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_valsC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge6kx_envC5ARocqVerifyHarness?AgentSubmission6Common5KXTac7kE_atomC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX22evC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6shz_okK47Corelib5Lists7ListDef6Forall01K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk05K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp01K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk09K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp02K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk03K5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk04K5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk01C5ARocqVerifyHarness?AgentSubmission6Common4KXGo6shz_ofC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission6Common4KXGo;atom_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac;read_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zk_entC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9kentry_okK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission6Common4KXGo9zk_img_okK46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zdenC5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zsaK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ARocqVerifyHarness?AgentSubmission6Common4KXGo;zk_range_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>atom_ranges_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge<reads_scopedC46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C47Corelib4Init3Nat3addC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission6Common5KXTac>read_ranges_okC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7know_okC47Corelib4Init5Logic5proj1C5ARocqVerifyHarness?AgentSubmission6Common4KXGo7tabs_ofC5ARocqVerifyHarness?AgentSubmission6Common5KXTac:tab_rangesC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6tab_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac3zleC5ARocqVerifyHarness?AgentSubmission6Common4KXGo5zt_okK47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission6Common5KXTac=tab_ranges_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac9region_okC5ARocqVerifyHarness?AgentSubmission6Common5KXTac6zr_regC5ARocqVerifyHarness?AgentSubmission6Common4KXGo>zr_ok_bytes_atC5ARocqVerifyHarness?AgentSubmission6Common4KXGo7all_romC5ARocqVerifyHarness?AgentSubmission6Common4KXGo9zr_ok_imgC5ARocqVerifyHarness?AgentSubmission6Common4KXGoCForall2_map_Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge9zatoms_ltC46Stdlib5Lists4List7forallbK46Stdlib5Lists4List7Forall201C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_regs_okC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge2zxC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge5lnormC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4mkRlC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS7regs_okK6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry04K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry07K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry08K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state01C5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:rfull_mkRlC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sym_execC5ARocqVerifyHarness?AgentSubmission6Common5KXTac8sc_auto2C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List6filterC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9scs_denotC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8sc_denotC5ARocqVerifyHarness?AgentSubmission6Common5KXTac<kx_scs_bulk2C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25s_logC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS8log_flatC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_regs_keepC6ARocqVerifyHarness?AgentSubmission6Common7KXSound3KXS9mem_denotC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26edenotC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflI47Corelib4Init5Logic2or00C56Stdlib5Arith8PeanoNat3Nat3ltbC5ARocqVerifyHarness?AgentSubmission6Common5KXTac2kEC5ARocqVerifyHarness?AgentSubmission6Common6KXPost=log_inside_ezC5ARocqVerifyHarness?AgentSubmission6Common6KXPost@log_inside_ez_okC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_munch_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem<kx_wmono_logC5ARocqVerifyHarness?AgentSubmission6Common6KXPost;kx_log_wr_bC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_log_wr_okC5ARocqVerifyHarness?AgentSubmission6Common5KXMem>kx_mem_inv_logC5ARocqVerifyHarness?AgentSubmission6Common5KXMem6replayC5ARocqVerifyHarness?AgentSubmission6Common5KXMem?kx_u8arr_replayC5ARocqVerifyHarness?AgentSubmission6Common5KXMem=replay_lengthK47Corelib4Init5Logic2ex01C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26erangeC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4body;x4_nb_boundC56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission6Common6KXPost9kx_mul_m1C5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge7kx_regsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost8kE_atomsC5ARocqVerifyHarness?AgentSubmission6Common6KXPost?kx_regs_keep_okC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26s_regsC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24s_pcC5ARocqVerifyHarness?AgentSubmission6Common8KXBridge:kx_run_evtC5ARocqVerifyHarness?AgentSubmission6Common4KXGo:kx_pendingC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr03K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr05C5ARocqVerifyHarness?AgentSubmission6Common4KXGo:zk_disj_okC5ARocqVerifyHarness?AgentSubmission6Common4KXGo8zk_wr_okC47Corelib4Init5Logic6eq_symK46Stdlib5Lists4List7Forall202K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry01K6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond06C6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26a_baseC5ARocqVerifyHarness?AgentSubmission6Common6KXPost2ezC6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25a_offC5ARocqVerifyHarness?AgentSubmission6Common6KXPost<kx_erange_evC5ARocqVerifyHarness?AgentSubmission6Common6KXPost7kx_pickI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX25saddr00K47Corelib4Init9Datatypes4bool02I5ARocqVerifyHarness?AgentSubmission6Common5KXTac2zk00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26kentry00K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith4Znat5Nat2Z6inj_leI5ARocqVerifyHarness?AgentSubmission6Common8KXBridge4zexp00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX24expr00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX26sentry00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX28sidecond00I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv3Sem2w0I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX23env00I46Stdlib5Lists4List6Exists00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX29sym_state00I6ARocqVerifyHarness?AgentSubmission6Common6KXExec3KX27scripts00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission5UbsanCRF_huf_x4body_iface<x4_body_stmt".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma x4_ctz_tab : forall mm, mem_inv usegs mm -> ztab_fact usegs mm 0x104e0 64 1 [(0, 0, 63)].
Proof.
  intros mm MI. apply ztab_fact_img; [exact MI | lia | vm_compute; reflexivity].
Qed.

Lemma x4_nb_bound : forall u, 0 <= u <= 63 -> 0 <= u / 8 <= 7.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4body ()) [] "h04__x1h17__arithh24__ffh34__p1h48__varmaph55__with61Hh72Huh81up;2p;1p;6p;3p;4p;5p;7p;8g00Adj20Tg007Uj13Tg008:j17Tg00KDj26Tg004Yj18Tg00K_j2:Tg009Xj1RTg00:Xj1HTg00L<j2CTg00;Vj1BTg00<4j1ATg00<_j24Tg00LZj2>Tg00M=j6TTg00Maj1STg00>Qj2QTg00?3j2NTg00?Mj2MTg00@9j3GTg00@Sj3FTg00A2j4DTg00;8j1ETg00NCj22Tg00N_j4ITg00O@j3JTg00Ocj2KTg00P@j5@Tg00Plj4LTg00=Bj4<Tg00=mj7?Tg00QGj7OTg00Qkj8PTg00F6R0f1R1g00I=f0R2C<p=;P1g00G^R3g00H=R4P4g00H]R5P2g00IdF?p=1f2R6P3P4P4P5P1P2FOp==f3R7P3P4P4P5P6P1P2GPp=5P0P1g00ROP2C<p=9g00FTR8/02R9g00D\R:#3#3R;#3#3#3#7R<,02R='6%8:#8#8#7R>,:1R?,08%7;R;,0?P1P>p-0R@g00G2RA#RRB%HARA1C01RC%B0RD%A0RE1408RF1>0:R:';,1ERGPEP3P4P4P5P7ETR75=E%S4R4PGC51QE5R5P2P6g00JDRGg00JdR3'N1M26=GG3dAF081CDR3b2b4b5X00W316911081[^00^3@P2106<P6P1O3b1PBPA%E0PD140>R9,9F,1EP5P3b2b4b5128>P2b1RFCIP1P>P>PFPBPAPCPDPE140<,;:,1E9=E7P4AJ099,9:,1EC5P5P3b2b4b5X00X3@161=1K>>,21[^00^3@P21086P6P1O3b1D@12?>1:6>/2>PBPAPCPDPE19:9,1EP4140;,;:,1EC5P5P3b2b4b5X00122>101;[^00P2f4/:>P1O2b1UP2O1b6CLW7X80o"). Qed.

Lemma x4_and7 : forall x : word, bv_unsigned (alu64 ALU_AND x (Z_to_bv 64 7)) mod 64 <= 7.
Proof.
  intros x. rewrite u_and64. change (bv_unsigned (Z_to_bv 64 7)) with 7.
  pose proof (Z.land_ones (bv_unsigned x) 3 ltac:(lia)) as Y. change (Z.ones 3) with 7 in Y. rewrite Y.
  pose proof (Z.mod_pos_bound (bv_unsigned x) (2^3) ltac:(lia)) as B. change (2^3) with 8 in B |- *.
  rewrite (Z.mod_small (bv_unsigned x mod 8) 64) by lia. lia.
Qed.

Lemma x4_evt_R : forall segs Q R R' F pc fc (mm rom : word -> option byte),
  evt segs Q (MS R' F pc fc None mm rom) -> R' = R -> evt segs Q (MS R F pc fc None mm rom).
Proof. intros segs Q R R' F pc fc mm rom H E. subst. exact H. Qed.

Ltac x4b_lits :=
  repeat match goal with
  | |- context [?a mod ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (a mod b) in change (a mod b) with v
  | |- context [2 ^ ?k] => is_Zlit k; let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v
  end.

Ltac x4b_atoms :=
  lazymatch goal with KXA : forall j, (j < length ?zv)%nat -> ev ?E j = _ |- _ =>
    let na := eval vm_compute in (length zv) in
    repeat match goal with
    | |- context [ev E ?j] =>
        let t := eval vm_compute in (Nat.ltb j na) in
        lazymatch t with true => rewrite (KXA j) by (apply Nat.ltb_lt; vm_compute; reflexivity) end
    end;
    cbn [nth]; rewrite ?Z_to_bv_bv_unsigned
  end.

Ltac x4b_rng :=
  repeat match goal with |- context [bv_unsigned (ev ?E ?j)] =>
    lazymatch goal with _ : 0 <= bv_unsigned (ev E j) <= _ |- _ => fail | _ => let H := fresh "RG" in kx_range (EVar j) H end
  end.

Ltac x4b_est DT0 DT47 :=
  lazymatch goal with |- context [estart ?E ?a] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      let na := eval vm_compute in (length zv) in
      change E with (kE zv xs);
      rewrite (estart_ez_kE zv xs a);
      [ | cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; x4b_lits; kx_abstract;
          clear - DT0 DT47; Z.div_mod_to_equations; lia ];
      cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; x4b_lits; kx_abstract;
      clear - DT0 DT47; Z.div_mod_to_equations; lia
    end
  end.

Ltac x4b_amt XAMT HT LT TOK ECB DT0 DT47 :=
  lazymatch goal with |- bv_unsigned (ev ?E ?j) mod 64 <= 11 =>
    let H := fresh "RD" in kx_read_eq j H; rewrite H; clear H; rewrite adenot_wa;
    lazymatch goal with |- context [rdval _ ?m (wa ?A) 2 false] =>
      apply (XAMT m _ _ _ A HT LT TOK ECB) end;
    x4b_est DT0 DT47
  end.

Ltac x4b_ip1 :=
  lazymatch goal with |- 8 <= bv_unsigned (alu64 ALU_ADD (ev ?E ?a) (ev ?E ?b)) =>
    let H := fresh "RG" in kx_range (EAlu ALU_ADD (EVar a) (EVar b)) H; cbn [edenot] in H; lia end.

Ltac x4b_br XBNE XSLL XIP XAMT HT LT TOK ECB DT0 DT47 :=
  lazymatch goal with
  | |- branch_taken BC_NE (edenot ?E ?X) (edenot ?E (ELit 0)) = true =>
      change (edenot E (ELit 0)) with (Z_to_bv 64 0); apply XBNE; cbn [edenot];
      first [ apply XIP; [ x4b_ip1 | x4b_rng; lia ]
            | apply XSLL; [ x4b_atoms; assumption | x4b_amt XAMT HT LT TOK ECB DT0 DT47 .. ] ]
  end.

Ltac x4b_ipcell :=
  cbn [nth_error];
  lazymatch goal with |- Some (Z_to_bv 64 ?u) = Some (Z_to_bv 64 (?a - ?nb)) =>
    is_evar nb; unify nb (a - u); do 2 f_equal; lia end.

Ltac x4b_opcell := cbn [nth_error]; do 2 f_equal; lia.

Lemma x4_m64_2 : forall z, (z mod 2^64) mod 2 = z mod 2.
Proof. intro z. apply Z.mod_mod_divide. exists (2^63). reflexivity. Qed.

Lemma x4_ev_add : forall x y : word, bv_unsigned x mod 2 = 0 -> bv_unsigned y mod 2 = 0 ->
  bv_unsigned (alu64 ALU_ADD x y) mod 2 = 0.
Proof. intros x y HX HY. rewrite u_add64, x4_m64_2, Z.add_mod, HX, HY by lia. reflexivity. Qed.

Lemma x4_ev_mul : forall c (y : word), c mod 2 = 0 -> 0 <= c < 2^64 ->
  bv_unsigned (mul_div M_MUL (Z_to_bv 64 c) y) mod 2 = 0.
Proof.
  intros c y HC RC. rewrite u_mul64, x4_m64_2, u_lit64a.
  rewrite (Z.mod_small c) by lia. rewrite Z.mul_mod, HC by lia. reflexivity.
Qed.

Lemma x4_ev_andm2 : forall x : word, bv_unsigned (alu64 ALU_AND x (Z_to_bv 64 (-2))) mod 2 = 0.
Proof.
  intro x. rewrite u_and64.
  pose proof (Z.land_ones (Z.land (bv_unsigned x) (bv_unsigned (Z_to_bv 64 (-2)))) 1 ltac:(lia)) as Y.
  change (Z.ones 1) with 1 in Y. change (2^1) with 2 in Y. rewrite <- Y, <- Z.land_assoc.
  change (Z.land (bv_unsigned (Z_to_bv 64 (-2))) 1) with 0. apply Z.land_0_r.
Qed.

Lemma x4_add1_or : forall x : word, bv_unsigned x mod 2 = 0 ->
  alu64 ALU_ADD x (Z_to_bv 64 1) = alu64 ALU_OR x (Z_to_bv 64 1).
Proof.
  intros x HX. apply bv_eq. rewrite u_add64, u_or64. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2^64) in R.
  assert (L : Z.land (bv_unsigned x) 1 = 0).
  { pose proof (Z.land_ones (bv_unsigned x) 1 ltac:(lia)) as Y. change (Z.ones 1) with 1 in Y.
    change (2^1) with 2 in Y. rewrite Y. exact HX. }
  rewrite Z.mod_small by (clear - HX R; Z.div_mod_to_equations; lia).
  rewrite (Z.add_nocarry_lxor _ _ L). apply Z.lxor_lor. exact L.
Qed.

Ltac x4b_even :=
  lazymatch goal with
  | |- bv_unsigned (alu64 ALU_ADD _ _) mod 2 = 0 => apply x4_ev_add; x4b_even
  | |- bv_unsigned (mul_div M_MUL (Z_to_bv 64 ?c) _) mod 2 = 0 => apply x4_ev_mul; [reflexivity | lia]
  | |- bv_unsigned (alu64 ALU_AND _ (Z_to_bv 64 (-2))) mod 2 = 0 => apply x4_ev_andm2
  end.

Ltac x4b_rel XREL :=
  lazymatch goal with
  | |- bv_unsigned _ mod 512 <> 0 =>
      cbn [edenot];
      lazymatch goal with
      | |- bv_unsigned (alu64 ALU_SLL (alu64 ALU_ADD ?x (Z_to_bv 64 1)) _) mod 512 <> 0 =>
          rewrite (x4_add1_or x) by x4b_even
      | |- _ => idtac
      end;
      apply XREL; apply x4_and7
  end.

Lemma x4_nb2 : forall v S i, 0 <= v <= 63 -> 0 <= S + i - (i + (S + -1 * (v mod 2 ^ 64 / 2 ^ (3 mod 64)))) <= 7.
Proof.
  intros v S i H. change (3 mod 64) with 3. change (2 ^ 3) with 8.
  rewrite Z.mod_small by lia. Z.div_mod_to_equations. lia.
Qed.

Ltac x4b_nb :=
  lazymatch goal with |- context [bv_unsigned (ev ?E ?j)] =>
    let H := fresh "RG" in kx_range (EVar j) H; apply x4_nb2; clear - H; lia end.

Ltac x4b_mkR :=
  f_equal;
  lazymatch goal with
  | |- ?x = ?y =>
      first [ is_evar x; unify x y; exact eq_refl
            | constr_eq x y; exact eq_refl
            | lazymatch goal with |- Z_to_bv 64 ?a = Z_to_bv 64 ?b =>
                assert (EQ : a = b) by (x4b_lits; lia); rewrite EQ; exact eq_refl end ]
  end.

Ltac x4b_leaf MU FA2 HO' HOL XREL :=
  lazymatch goal with
  | |- munch _ _ _ => exact MU
  | |- u64arr _ _ _ _ => exact FA2
  | |- length _ = 15%nat => reflexivity
  | |- exists _, u8arr _ _ _ _ /\ _ => eexists; split; [exact HO' | exact HOL]
  | |- nth_error _ ?k = Some (Z_to_bv 64 (_ - _)) => x4b_ipcell
  | |- nth_error _ ?k = Some _ => first [x4b_opcell | cbn [nth_error]; reflexivity]
  | |- bv_unsigned _ mod 512 <> 0 => x4b_rel XREL
  | |- 0 <= _ <= 7 => x4b_nb
  | |- mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => x4b_mkR
  | |- _ => first [assumption | idtac]
  end.

Ltac x4b_frame H HB :=
  lazymatch goal with
  | KXLF : log_flat ?E ?log, HK : know_ok ?segs ?E ?m ?kn |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      let na := eval vm_compute in (length zv) in
      lazymatch type of H with
      | rw_cells _ m ?A ?cs =>
          apply (kx_rw_cells_log segs E m log A cs) in H;
          [ | exact KXLF
            | change E with (kE zv xs); apply log_apart_ez_ok;
              cbn [log_apart_ez log_inside_ez inside]; cbv [ez a_base a_off]; change (length zv) with na;
              cbv [nth Nat.ltb Nat.leb];
              repeat (first [exact I | split]); HB ]
      end
    end
  end.
Ltac x4b_cell H HB :=
  lazymatch goal with
  | HLF : log_flat ?E ?log |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      let na := eval vm_compute in (length zv) in
      lazymatch type of H with
      | rw_cells ?segs m (?A0 + ?off) [?c0] =>
          let A := constr:(A0 + off) in
          let rec go pre l :=
            lazymatch l with
            | SE (SA (EVar 0) ?o) 8%nat ?v :: ?rest =>
                tryif constr_eq o off then
                  (let a := constr:(SA (EVar 0) o) in
                   let Hn := fresh "HC" in
                   assert (Hn : rw_cells segs (mem_denot E m (pre ++ SE a 8 v :: rest)) A [C8 (edenot E v)])
                     by (eapply (kx_cell_store8 segs E m pre a v rest A);
                         [ change (pre ++ SE a 8 v :: rest) with log; exact HLF
                         | exact H
                         | change E with (kE zv xs); kx_estart_z zv
                         | change E with (kE zv xs); apply log_apart_ez_ok; kx_log_z zv ]);
                   change (pre ++ SE a 8 v :: rest) with log in Hn;
                   kxz_cell_value Hn zv E xs v;
                   clear H; rename Hn into H)
                else (let pre' := eval cbn [app] in (pre ++ [SE (SA (EVar 0) o) 8%nat v]) in go pre' rest)
            | ?e :: ?rest => let pre' := eval cbn [app] in (pre ++ [e]) in go pre' rest
            | [] => x4b_frame H HB
            end in
          let l := eval hnf in log in
          go constr:(@nil sentry) l
      end
    end
  end.

Theorem x4_body_proof : x4_body_stmt.
Proof.
  unfold x4_body_stmt.
  intros Q mm F fc gp tp s5 s9 b0 b1 b2 b3 j9 j14 j15 j18 j19 j20 j22 j26 j27
         SP DT4 DST dcap SS n IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 obuf tbl sbuf cells fa
         MI HT LT TOK ECB HO LO HS LS DT0 DT47 D0 D47 S0 S47 DJT DJS DTA SPR TSP DSP SSP
         HFA LFA F0 F1 F2 F3 F5 F6 F7 F8 F10 F11 F12 F13 BM0 BM1 BM2 BM3
         I0a I0b I1a I1b I2a I2b I3a I3b O0a O0b O1a O1b O2a O2b O3a O3b K.
  destruct fa as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|w12 [|w13 [|w14 [|w15 fa]]]]]]]]]]]]]]]];
    cbn [length] in LFA; try lia.
  cbn [nth_error] in F0, F1, F2, F3, F5, F6, F7, F8, F10, F11, F12, F13.
  injection F0 as ->. injection F1 as ->. injection F2 as ->. injection F3 as ->.
  injection F5 as ->. injection F6 as ->. injection F7 as ->. injection F8 as ->.
  injection F10 as ->. injection F11 as ->. injection F12 as ->. injection F13 as ->.
  assert (EO0 : exists o, OP0 = DST + o) by (exists (OP0 - DST); lia). destruct EO0 as (o0 & ->).
  assert (EO1 : exists o, OP1 = DST + o) by (exists (OP1 - DST); lia). destruct EO1 as (o1 & ->).
  assert (EO2 : exists o, OP2 = DST + o) by (exists (OP2 - DST); lia). destruct EO2 as (o2 & ->).
  assert (EO3 : exists o, OP3 = DST + o) by (exists (OP3 - DST); lia). destruct EO3 as (o3 & ->).
  assert (EI0 : exists i, IP0 = SS + i) by (exists (IP0 - SS); lia). destruct EI0 as (i0 & ->).
  assert (EI1 : exists i, IP1 = SS + i) by (exists (IP1 - SS); lia). destruct EI1 as (i1 & ->).
  assert (EI2 : exists i, IP2 = SS + i) by (exists (IP2 - SS); lia). destruct EI2 as (i2 & ->).
  assert (EI3 : exists i, IP3 = SS + i) by (exists (IP3 - SS); lia). destruct EI3 as (i3 & ->).
  pose proof (x4k_u64arr_c8 usegs mm (SP + -224) _ ltac:(replace (SP + -224) with (SP - 224) by lia; exact HFA)) as FC.
  cbn [map] in FC.
  pose proof (munch_refl [(DST, DST + dcap); (SP - 224, SP - 104)] mm) as MU.
  pose proof (wmono_refl usegs mm) as WM.
  pose proof HFA as (HFB & HFW). clear HFA.
  assert (HFW2 : wr_at usegs mm (SP - 224) 120) by exact HFW. clear HFW.
  rewrite <- (Z_to_bv_bv_unsigned b0), <- (Z_to_bv_bv_unsigned b1), <- (Z_to_bv_bv_unsigned b2),
    <- (Z_to_bv_bv_unsigned b3) in HFB.
  pose proof HFB as HFB2. set (fbs := u64s _) in HFB2.
  assert (LFB : length fbs = 120%nat) by (subst fbs; rewrite u64s_length; reflexivity).
  pose proof (x4_ctz_tab mm MI) as CTZ.
  assert (AP1 : SP - 224 + 120 <= 0x104e0 \/ 0x104e0 + Z.of_nat 64 <= SP - 224 \/ 120 <= 0)
    by (eapply wr_at_apart_ro; first [exact MI | exact HFW2 | lia | vm_compute; reflexivity]).
  assert (AP2 : SP - 224 + 120 <= 0x10490 \/ 0x10490 + Z.of_nat 8 <= SP - 224 \/ 120 <= 0)
    by (eapply wr_at_apart_ro; first [exact MI | exact HFW2 | lia | vm_compute; reflexivity]).
  assert (AP3 : DST + dcap <= 0x104e0 \/ 0x104e0 + Z.of_nat 64 <= DST \/ dcap <= 0)
    by (rewrite <- LO; eapply wr_at_apart_ro; first [exact MI | exact (proj2 HO) | lia | vm_compute; reflexivity]).
  assert (AP4 : DST + dcap <= 0x10490 \/ 0x10490 + Z.of_nat 8 <= DST \/ dcap <= 0)
    by (rewrite <- LO; eapply wr_at_apart_ro; first [exact MI | exact (proj2 HO) | lia | vm_compute; reflexivity]).
  pose proof x4k2_bne as XBNE. pose proof x4k2_sll5_nz as XSLL. pose proof x4k2_ip_nz as XIP.
  pose proof x4k2_reload_nz as XREL. pose proof x4k2_amt as XAMT.
  unfold x4k2_bne_stmt in XBNE. unfold x4k2_sll5_nz_stmt in XSLL. unfold x4k2_ip_nz_stmt in XIP.
  unfold x4k2_reload_nz_stmt in XREL. unfold x4k2_amt_stmt in XAMT.
  replace (- DT4 - 1) with (-1 * DT4 - 1) by lia.
  kx_rund [0x18cd0] 700%nat
    [KZRange o0 0 140737488355328; KZRange o1 0 140737488355328; KZRange o2 0 140737488355328; KZRange o3 0 140737488355328;
     KZRange (dcap - o0) 5 140737488355328; KZRange (dcap - o1) 5 140737488355328;
     KZRange (dcap - o2) 5 140737488355328; KZRange (dcap - o3) 5 140737488355328;
     KZRange (DST + o0) 1 140737488355328; KZRange (DST + o1) 1 140737488355328;
     KZRange (DST + o2) 1 140737488355328; KZRange (DST + o3) 1 140737488355328;
     KZRange i0 7 140737488355328; KZRange i1 7 140737488355328; KZRange i2 7 140737488355328; KZRange i3 7 140737488355328;
     KZRange (n - i0) 8 140737488355328; KZRange (n - i1) 8 140737488355328;
     KZRange (n - i2) 8 140737488355328; KZRange (n - i3) 8 140737488355328;
     KZRange (SS + i0) 8 140737488355328; KZRange (SS + i1) 8 140737488355328;
     KZRange (SS + i2) 8 140737488355328; KZRange (SS + i3) 8 140737488355328;
     KZRange dcap 5 140737488355328; KZRange n 15 140737488355328;
     KZRange DST 1 140737488355328; KZRange SS 1 140737488355328;
     KZRange DT4 1 140737488355328; KZAlign DT4 2; KZRange SP 512 140737488355328;
     KZTab 0x104e0 64 1 [(0, 0, 63)]; KZImg 0x104e0 0x10520; KZImg 0x10490 0x10498;
     KZWr DST dcap; KZWr (SP - 224) 120;
     KZWord (SP - 224) 8 (DST + o0); KZWord (SP - 216) 8 (DST + o1); KZWord (SP - 208) 8 (DST + o2); KZWord (SP - 200) 8 (DST + o3);
     KZWord (SP - 184) 8 (SS + i0); KZWord (SP - 176) 8 (SS + i1); KZWord (SP - 168) 8 (SS + i2); KZWord (SP - 160) 8 (SS + i3);
     KZWord (SP - 144) 8 (bv_unsigned b0); KZWord (SP - 136) 8 (bv_unsigned b1);
     KZWord (SP - 128) 8 (bv_unsigned b2); KZWord (SP - 120) 8 (bv_unsigned b3);
     KZDisj DST dcap DT4 4096; KZDisj DST dcap SS n; KZDisj DST dcap (SP - 224) 120;
     KZDisj (SP - 224) 120 DT4 4096; KZDisj (SP - 224) 120 SS n;
     KZDisj (SP - 224) 120 0x104e0 64; KZDisj (SP - 224) 120 0x10490 8;
     KZDisj DST dcap 0x104e0 64; KZDisj DST dcap 0x10490 8]
    [(DT4, 4096); (SS, n); (SP - 224, 120); (0x104e0, 64); (0x10490, 8)]
    (repeat true 91).
  all: try (x4b_br XBNE XSLL XIP XAMT HT LT TOK ECB DT0 DT47).
  try clear DJT. try clear DJS. try clear AP1. try clear AP2. try clear AP3. try clear AP4.
  try clear XBNE. try clear XSLL. try clear XIP. try clear XAMT. try clear CTZ. try clear HFB2. try clear HFB.
  kx_post_regs.
  kx_munch MU.
  kx_post_mem_free.
  lazymatch goal with KXLF : log_flat ?E ?lg |- _ =>
    pose proof (kx_u8arr_replay usegs E mm lg DST obuf HO KXLF) as HO';
    pose proof (replay_length E lg DST obuf) as HOL end.
  kx_cells_split FC.
  repeat match goal with
  | HLF : log_flat ?E ?log, H : rw_cells ?segs mm ?A [?c] |- context [MS _ _ _ _ _ (mem_denot ?E mm ?log) _] =>
      x4b_cell H ltac:(cbn [cells_size csize];
                       first [ clear - DSP SPR D0 D47 O0a O0b O1a O1b O2a O2b O3a O3b; lia | lia ])
  end.
  lazymatch goal with |- context [MS _ _ _ _ _ ?M _] =>
    eassert (FA1 : rw_cells usegs M (SP + -224)
                     [C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _])
      by kx_cells_merge end.
  lazymatch type of FA1 with
  | rw_cells _ ?M ?A [C8 ?x0; C8 ?x1; C8 ?x2; C8 ?x3; C8 ?x4; C8 ?x5; C8 ?x6; C8 ?x7; C8 ?x8; C8 ?x9; C8 ?x10;
                      C8 ?x11; C8 ?x12; C8 ?x13; C8 ?x14] =>
      pose proof (x4k_c8_u64arr usegs M A [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14] FA1) as FA2
  end.
  eapply x4_evt_R; [ eapply K | ].
  all: x4b_leaf MU FA2 HO' HOL XREL.
Qed.
