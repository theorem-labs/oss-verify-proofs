(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec AgentLib AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Eb0DefsK Eb0PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK HandoffCellsK HandoffRolesK
  Eb0HandoffK Eb0HSK_0 Eb0HSK_1 Eb0MainTableK Eb0HandoffInstK ErbArtHandoffK ErbArtHandoffInstK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import HeapIface HeapIfaceA HeapIfaceAEx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_ErbStkShK () := "K47Corelib4Init5Logic2eq01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9ErbStkShK9stksh_chkC13~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0HSK_04HS_0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0HSK_14HS_1C13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>ErbArtHandoffK4topEC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK2uEC13~~~C56Stdlib6ZArith6BinInt1Z3maxC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA<in_shadow_ofC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK2knC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK:kentry_eqbC13~~~C46Stdlib5Lists4List7existsbC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K;lin_nowrapRC13~~~C47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>HandoffBridgeK9hb_knb_InC13~~~C46Stdlib5Lists4List2InC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK5SINV0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK5argH0C13~~~K47Corelib7Numbers7BinNums8positive01K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K5saddr01C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>HandoffBridgeK9hb_zero_kC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AxSymExec3SoundK5AX2SK5elenZC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AxSymExec3SoundK5AX2SK4flatC13~~~C56Stdlib6ZArith6BinInt1Z2ltI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AxSymExec3SoundK5AX2SK6estartC13~~~C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K6edenotC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>HandoffBridgeK6hb_linC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>HandoffBridgeK2LZC13~~~K47Corelib4Init9Datatypes3nat02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>HandoffBridgeK2VZC13~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>HandoffBridgeK7hbi_sp0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK7geo_stkC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>ErbArtHandoffK4botEC13~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K2evC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9u64_rangeC13~~~C47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z5le_geC56Stdlib6ZArith6BinInt1Z5ge_leI46Stdlib;setoid_ring<Ring_polynom5PExpr00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list02K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr05I46Stdlib;setoid_ring<Ring_polynom3Pol00C56Stdlib6ZArith6BinInt1Z3divK46Stdlib;setoid_ring<Ring_polynom5PExpr07K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_mulK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z;div_le_monoC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA7byte_atC13~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib;setoid_ring<Ring_polynom5PExpr06C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK47Corelib4Init5Logic4True01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9ErbStkShK7K_STKSHC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K6kentry00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9ErbStkShK5E_SHBC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9ErbStkShK5E_SHLC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK6ASEGS0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK5ASAN0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK5LIMITC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK4APH0C13~~~K47Corelib4Init9Datatypes3nat01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK5e_sp0C13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiI47Corelib4Init5Logic4True00I46Stdlib;setoid_ring<Ring_polynom3Mon00I47Corelib4Init5Logic5False00K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_fitsC47Corelib4Init5Peano2ltC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eb0HandoffInstK3HSAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9ErbStkShK:stksh_mainC13~~~C56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegI89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK5cs_ok00C13~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K3env00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9ErbStkShK;stksh_chk_0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK9geo_chk_0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9ErbStkShK;stksh_chk_1C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK9geo_chk_1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9ErbStkShK=stksh_main_hiC13~~~". Local Ltac lia := L5FastLiaT.plia2.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition E_SHB : expr := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EVar 10)).
Definition E_SHL : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EVar 10))) (ELit 17592187092992).
Definition K_STKSH : kentry := KZero (SA E_SHB 2146402304) E_SHL.

Definition stksh_chk (cs : acs) : bool :=
  let k := kn cs in (existsb (kentry_eqb K_STKSH) k && lin_nowrapR k E_SHB && lin_nowrapR k E_SHL)%bool.

Lemma stksh_chk_0 : stksh_chk HS_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ErbStkShK ()) [] "p;2p;1p;3g0000j22Tg000Jj11Tg001Xj30Tg0022R0g002RR1'2g0032#1=001do"). Qed.
Lemma stksh_chk_1 : stksh_chk HS_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ErbStkShK ()) [] "p;2p;1p;3g0000j22Tg000Jj11Tg001Xj30Tg0022R0g002RR1'2g004:#1=001do"). Qed.

Section StkSh.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  #[local] Notation usp := (bv_unsigned sp).

  Variable cs : acs.
  Hypothesis SCHK : stksh_chk cs = true.
  Hypothesis GCHK : geo_chk cs = true.
  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis HC : CSOK E cs R FULL model.

  Ltac LINEQS e H :=
    let Hn := fresh in
    assert (Hn : lin_nowrapR (kn cs) e = true)
      by (let G := fresh in pose proof SCHK as G; unfold stksh_chk in G; repeat (let X := fresh in apply andb_prop in G as [G X]); assumption);
    pose proof (hb_lin ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model e HC Hn) as H; clear Hn;
    unfold LZ in H;
    match type of H with context [lin_of ?x] => let l := eval vm_compute in (lin_of x) in change (lin_of x) with l in H end;
    cbv [AX2SK.lden AX2SK.tden fst snd AX2SK.uE] in H; cbn [edenot] in H;
    repeat match type of H with context [bv_unsigned (ev E ?n)] => change (bv_unsigned (ev E n)) with (VZ E n) in H end;
    rewrite ?Z.add_0_r in H.

  #[using="brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit SCHK GCHK R model HC"] Theorem stksh_main : forall x,
    in_shadow_of (usp - 8388608) (Z.max usp (uE E (topE cs)) - (usp - 8388608)) x -> byte_at FULL x 0.
  Proof.
    intros x Hx.
    assert (Hin : In K_STKSH (kn cs)).
    { apply hb_knb_In. pose proof SCHK as G. unfold stksh_chk in G. repeat (let X := fresh in apply andb_prop in G as [G X]). assumption. }
    destruct (hb_zero_k ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ _ HC Hin) as [Hf Hz].
    unfold estart, elenZ in Hz. cbn [a_base a_off] in Hz.
    remember (bv_unsigned (edenot E E_SHB)) as shb eqn:Eb. remember (bv_unsigned (edenot E E_SHL)) as shl eqn:El.
    LINEQS E_SHB L1. rewrite <- Eb in L1. LINEQS E_SHL L2. rewrite <- El in L2.
    pose proof (hbi_sp0 ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E cs R FULL model HC) as U0.
    destruct (geo_stk sp brk0 rdraw argv envp uid hw fs cs GCHK E R FULL model HC) as (_ & _ & _ & _ & TOP).
    assert (SR : 0x7fff80000000 <= usp <= 2 ^ 47) by (destruct Hsp as (H1 & H2 & H3); unfold sp_window_lo, sp_window_hi in H1, H2; lia).
    pose proof (Z.ge_le _ _ (Z.le_ge _ _ (proj1 (u64_range (ev E 6))))) as V6. change (bv_unsigned (ev E 6)) with (VZ E 6) in V6.
    unfold in_shadow_of, S, SB in Hx.
    set (mx := Z.max usp (uE E (topE cs))) in *.
    replace (usp - 8388608 + (mx - (usp - 8388608)) - 1) with (mx - 1) in Hx by ring.
    assert (D1 : shb - 1048576 <= (usp - 8388608) / 8).
    { replace (shb - 1048576) with ((8 * shb - 8388608) / 8) by (replace (8 * shb - 8388608) with ((shb - 1048576) * 8) by ring; apply Z.div_mul; lia).
      apply Z.div_le_mono; lia. }
    assert (D2 : (mx - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
    change ((2 ^ 47 - 1) / 8) with 17592186044415 in D2.
    unfold byte_at. replace x with (shb + 2146402304 + (x - (shb + 2146402304))) by ring. apply Hz. lia.
  Qed.
  (* [comment removed for export] *)
  #[using="brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit cs SCHK GCHK E R model HC"] Theorem stksh_main_hi : forall x,
    in_shadow_of (usp - 8388608) (2 ^ 47 - (usp - 8388608)) x -> byte_at FULL x 0.
  Proof.
    intros x Hx.
    assert (Hin : In K_STKSH (kn cs)).
    { apply hb_knb_In. pose proof SCHK as G. unfold stksh_chk in G. repeat (let X := fresh in apply andb_prop in G as [G X]). assumption. }
    destruct (hb_zero_k ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ _ HC Hin) as [Hf Hz].
    unfold estart, elenZ in Hz. cbn [a_base a_off] in Hz.
    remember (bv_unsigned (edenot E E_SHB)) as shb eqn:Eb. remember (bv_unsigned (edenot E E_SHL)) as shl eqn:El.
    LINEQS E_SHB L1. rewrite <- Eb in L1. LINEQS E_SHL L2. rewrite <- El in L2.
    pose proof (hbi_sp0 ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E cs R FULL model HC) as U0.
    destruct (geo_stk sp brk0 rdraw argv envp uid hw fs cs GCHK E R FULL model HC) as (_ & _ & _ & _ & TOP).
    assert (SR : 0x7fff80000000 <= usp <= 2 ^ 47) by (destruct Hsp as (H1 & H2 & H3); unfold sp_window_lo, sp_window_hi in H1, H2; lia).
    pose proof (Z.ge_le _ _ (Z.le_ge _ _ (proj1 (u64_range (ev E 6))))) as V6. change (bv_unsigned (ev E 6)) with (VZ E 6) in V6.
    unfold in_shadow_of, S, SB in Hx.
    set (mx := 2 ^ 47) in *.
    replace (usp - 8388608 + (mx - (usp - 8388608)) - 1) with (mx - 1) in Hx by ring.
    assert (D1 : shb - 1048576 <= (usp - 8388608) / 8).
    { replace (shb - 1048576) with ((8 * shb - 8388608) / 8) by (replace (8 * shb - 8388608) with ((shb - 1048576) * 8) by ring; apply Z.div_mul; lia).
      apply Z.div_le_mono; lia. }
    assert (D2 : (mx - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
    change ((2 ^ 47 - 1) / 8) with 17592186044415 in D2.
    unfold byte_at. replace x with (shb + 2146402304 + (x - (shb + 2146402304))) by ring. apply Hz. lia.
  Qed.
End StkSh.

(* [comment removed for export] *)
Theorem as0_stksh_main :
  forall sp brk0 rdraw argv envp uid hw fs, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  forall h, (h < 2)%nat -> forall E R FULL model,
    APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT (SINV0 APH0 sp rdraw brk0 argv envp uid hw) (argH0 APH0 sp rdraw argv envp uid hw) fs E (HSA h) R FULL model ->
    forall x, in_shadow_of (bv_unsigned sp - 8388608) (Z.max (bv_unsigned sp) (APSK.uE E (topE (HSA h))) - (bv_unsigned sp - 8388608)) x -> byte_at FULL x 0.
Proof.
ltac2:(KReplay.run1 (kr_t_ErbStkShK ()) [] "p'0h02HCh12Hhh21xh34__p1h44__x1h51hh61Eh74FULLh82H0h94Hfith:3Hh0h;3Hsph<3Hvah=3Hveh>1Rh?7__arithh@4__ffhA8__varmaphB5__withC4argvhD4brk0hE4cstrhF4envphG2fshH2hwhI5modelhJ1ni001nhK5rdrawhL2sphM3uidhN2z0p;1p;3p;2p;Dp;4p;6p;8p;7p;;p;<g005Bj19Tg005gj1CTg00L7j1JTg00^aj1HTg01YXj1`Tg01ZMj1\Tg01[Dj1YTg01\;j3XTg00SgR0j10Tg01]8R1j27Tg00Ecj1UTg01]Pj2QTg00LZj1nTg01^<j11Tg006Ej2;Tg006oj1DTg007Mj26Tg007jj1<Tg0098j2:Tg00:Ij2=Tg00:fj3BTg016Qj3ATg01_JlDLTg01`YR2j1?Tg00NTj28Tg00K[R3j2@Tg0000j2FTg01a9j4VTg01a`j1TTg00\<j2>Tg013Zj2RTg001Xj3GTg00AJj2ITg014<j2STg00^Aj1mTg017^j2lTg00_Aj1kTg00__j1iTg00n:j2ETg00`Jj2hTg018<j4PTg00`mj1cTg01?Zj3NTg01@`j6_Tg00b2j2^Tg00bTj2aTg00c@j3bTg00c_j4]Tg00COj8dTg00DYj7eTg01bEl;[Tg01c[l<fTg01d@l<gTg018gj7ZTg019oj8jTf0R4#9#9p=2g01R`R5f6R6f5R7f4R8f3R9f2R:f1R;P4Gdp=5P5P7P8P9P:P;P4Fep=3g01OCg01PMg01QVf7R5P6P7P8P9P:P;P4M;[p=4g01deR<P<g01BFR=P=P0P2P2P9g01eDP:P;P4M<fp=KP<P=P1P2P3g01ehP7P8P9P:P;P4M<gp=WP;g01CKR3g01CjR2P2g01DJR1P4g01DjFZp=OP9P3P2P2P1P:P;P4Gjp=Mg01IjR0#9R>#2R?#9#2R@#CRA#JRBg01fJ%C?#JR?#H#HRCg01gJ%`5%\7%Y7f:RD?X56g01ShRE#0RF#0RG,74RHg01h8%U>#C/QB%n?\Bg01iIfAR?f?RIf@RJf>RKf=RLf<RMf;RNF5P?PIPKPLPMPNE3PDP9%17P:P;P4G4P<fDROfBRPfCRQP?PJPIPKF5POPPP?PJPIPKE3PLP6%1;P7P8P9G4fFRR,;ARS%9@#2#2#2#2#2#2#2#2#DR@'6RTf8RU%19#<':,=S/6T;B4g01AhRT9A5;[^2=]0^1HP617EGPQP?PPPJPIPKPLF5PQP?PJPIPKPLE3PMP7%1EP8P9P:G4POPQPPP?PJPIPKPLPMPNPDf9REg0032g01j?g01kOP6P7P8P9P4MDLW0W1P<%04RH/7GPRPOfERSPQPPP?PJF5PRPOPQPPP?PJE3PIPU%0;RV#1P5P6P7G4fH,;ARW/6@RX%09RY#1#<,:D,=W/6X;B4AAE;T[^2=]0]1P417FGPSPQPOPPP?PJPIF5PSPQPPP?PJPIE3PKP5%1FP6P7P8G4PRPSPOPQPPP?PJPIPKPLPMPNg004:g01lfg01n6PUP5P6P7P4MDLW0W1%0H/7GfGRHPSPRPOPQPPP?F5PHPSPOPQPPP?E3PJPE%0V#1PUP5P6G4fI,;ARU/6@R@%0Y#1#<,:N,=U/6@;B4%08R@#0RU/7G%?8RN%D0RY'8/8Y%D>R>'@RVPU184YX2=RUPUPNO1RJO1PUP@PJPUP8PN1F=NCKCKPGP>1F=>EWP9CVPV%T7%?7,>TfL,;ARV%06#0#1#<,:KRK'R1@VK1=VKRG=G=K'I1>KVAG=GV'I'SfM,;A%05#0#1#<,:I'=P=p-0R5g01I>RA#m%HA1l=;%k=%i=RAP=1E=Tg01Bd1h=0R0CP,OA%c2RGPAP=1E=YRV9N=0=N=Vg01HW1E=>CP,OAPGPAP3P2P2P1P9E_CMCM1^A1P4P:g0022RAg002RR1'F1a4:=GA1dAb=T;C]b@bAbBX4=W31>T418;Y/8Y/@>P9[[^4=^35P4AAI6T%?EP9P8O4b?bNb8bEb:UX2=W0W1X5<P4O1n0110000020011100XJ<P4O1n0110000020011100P7P4O2W0WIW7W>W6W1X5<W9W=W<W;WGXHBXMBXFCWCWKXDBWLo"). Qed.

Theorem as0_stksh_main_hi :
  forall sp brk0 rdraw argv envp uid hw fs, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  forall h, (h < 2)%nat -> forall E R FULL model,
    APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT (SINV0 APH0 sp rdraw brk0 argv envp uid hw) (argH0 APH0 sp rdraw argv envp uid hw) fs E (HSA h) R FULL model ->
    forall x, in_shadow_of (bv_unsigned sp - 8388608) (2 ^ 47 - (bv_unsigned sp - 8388608)) x -> byte_at FULL x 0.
Proof.
ltac2:(KReplay.run1 (kr_t_ErbStkShK ()) [] "p'0h02HCh12Hhh21xh32Hah44__p1h54__x1h61hh71Eh84FULLh94Hfith:3Hh0h;3Hsph<3Hvah=3Hveh>1Rh?7__arithh@4__ffhA6__sat0hB6__sat1hC8__varmaphD5__withE4argvhF4brk0hG4cstrhH4envphI2fshJ2hwhK5modelhL1ni001nhM5rdrawhN2sphO3uidp;1p;3p;2p;Dp;4p;6p;8p;7p;;p;<g005Bj19Tg005gj1>Tg00L7j1FTg00^aj1?Tg01YXj1aTg01ZMj1[Tg01[Dj1XTg01\;j3WTg00SgR0j11Tg01]8R1j27Tg00Ecj1=Tg01]Pj2MTg00LZj1kTg01^<j13Tg006Ej2CTg006oj1<Tg007Mj24Tg00\Xj2YTg00:fj3BTg016Qj3ATg01oMlDHTg01`YR2j1@Tg00NTj2:Tg00K[R3j2;Tg0000j2DTg01a9j4PTg01a`j1OTg00\<j28Tg00]5j2NTg00]]j3QTg00^Aj1RTg017^j2STg00_Aj1TTg00__j1UTg00n:j2ETg00`Jj2jTg018<j4LTg00`mj1iTg01?Zj3ITg01@`j6hTg00b2j2gTg00bTj2`Tg001Xj3_Tg00c@j3^Tg00c_j4]Tg00COj8bTg00DYj7cTg01bEl;\Tg01c[l<dTg01d@l<eTg018gj7ZTg019oj8fTf0R4#9#9p=0g01R`R5f6R6f5R7f4R8f3R9f2R:f1R;P4Gbp=2P5P7P8P9P:P;P4Fcp=5g01OCg01PMg01QVf7R5P6P7P8P9P:P;P4M;\p=6g01deR<P<g01BFR=P=P0P2P2P9g01eDP:P;P4M<dp=GP<P=P1P2P3g01ehP7P8P9P:P;P4M<ep=VP;g01CKR3g01CjR2P2g01DJR1P4g01DjFZp=KP9P3P2P2P1P:P;P4Gfp=Jg01IjR0#9R>#0R?#9#0R@#>RA#FRBg01fJ%>?#FR?#?#?RCg01gJ%a5%[7%X7f:RD?W56g01ShRE#1RF#1RG,74RHg01h8%=>RI#>/MB%k?\Bg01iIfAR?f?RJf@RKf>RLf=RMf<RNf;ROF2P?PJPLPMPNPOE5PDP9%37P:P;P4G6P<fDRPfBRQfCRRP?PKPJPLF2PPPQP?PKPJPLE5PMP6%3;P7P8P9G6fFRS,CA%9@#0#0#0#0#0#0#0#0#<R@'4RT%<>R>%=I#=#=#<RI'YRU/4T;B4g01AhRT9A5;[^2=]0^1HP617EGPRP?PQPKPJPLPMF2PRP?PKPJPLPME5PNP7%3EP8P9P:G6PPPRPQP?PKPJPLPMPNPOPDf9RDg0032g01j?g01kOP6P7P8P9P4MDHW0W1P<%14RE/7GPSPPfERHPRPQP?PKF2PSPPPRPQP?PKE5PJf8RV%1;RW#3P5P6P7G6fH,CA/4@RX14UX;B4AAD;T[^2=]0]1P417FGPHPRPPPQP?PKPJF2PHPRPQP?PKPJE5PLP5%3FP6P7P8G6PSPHPPPRPQP?PKPJPLPMPNPOg004:g01lfg01n6PVP5P6P7P4MDHW0W1%1E/7GfGREPHPSPPPRPQP?F2PEPHPPPRPQP?E5PKPD%1W#3PVP5P6G6fI,CA/4@R@14U@;B4%18R@#1RA/7G%@8R5%<0RV':/:V/;>RWPA1:4VX2=RAPAP5O1RKO1PAP@PKPAP8P51D=5CGCGPGP>1D=>EVP9CPPW%O7%@7,8T1N>I1;T>18TI1;TU[[18T>RWg01WKRGAQ>I;UW318TU\G^3Wp-0RWg01I>RG#R%?G1S=;%T=%U=RGP=1E=Tg01Bd1j=0R0CL,KG%i2RUPGP=1E=VRI9I=0=I=Ig01HW1E=>CL,KGPUPGP3P2P2P1P9EhCJCJ1gG1P4P:g0022RGg002RR1'D1`4:=_G1dA^=T;C]b@bCbDX5=W418T41:;V/:V/;>P9[[^5=^4WP4AAJ6T%@DP9P8O4b?bAbBbGb:UX2=W0W1X6<P4O1n0110000020011100XL<P4O1n0110000020011100P7P4O2W0WKW8W>W7W1X6<W9W=W<W;WIXJBXOBXHCWEWMXFBWNo"). Qed.
