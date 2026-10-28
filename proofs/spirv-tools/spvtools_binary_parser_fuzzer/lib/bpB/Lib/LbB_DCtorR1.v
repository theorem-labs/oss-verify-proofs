(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 RtB_Iface RtB_IMemset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DCtorR5.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section CtorR1.

  Local Notation DSC_R2 := LbB_DCtorK.DSC_R2 (only parsing).
  Local Notation DSC_R3 := LbB_DCtorK.DSC_R3 (only parsing).
  Local Notation DSC_R4 := LbB_DCtorK.DSC_R4 (only parsing).
  Local Notation DSC_R5 := LbB_DCtorK.DSC_R5 (only parsing).
  Local Notation DSC_R6 := LbB_DCtorK.DSC_R6 (only parsing).
  Local Notation DSC_R7 := LbB_DCtorK.DSC_R7 (only parsing).
  Local Notation DSC_R8 := LbB_DCtorK.DSC_R8 (only parsing).
  Local Notation DSC_RET := LbB_DCtorK.DSC_RET (only parsing).
  Local Notation shb := LbB_DCtorK.shb (only parsing).
  Local Notation shdj := LbB_DCtorK.shdj (only parsing).
  Local Notation SHK := LbB_DCtorK.SHK (only parsing).
  Local Notation kshd := LbB_DCtorK.kshd (only parsing).
  Local Notation shz := LbB_DCtorK.shz (only parsing).
  Local Notation kshz := LbB_DCtorK.kshz (only parsing).
  Local Notation shobj := LbB_DCtorK.shobj (only parsing).
  Local Notation shk_okb := LbB_DCtorK.shk_okb (only parsing).
  Local Notation SHK_ok := LbB_DCtorK.SHK_ok (only parsing).
  Local Notation vtkn := LbB_DCtorK.vtkn (only parsing).
  Local Notation kst_ctor := LbB_DCtorK.kst_ctor (only parsing).
  Local Notation RT0 := LbB_DCtorK.RT0 (only parsing).
  Local Notation CT_STACK := LbB_DCtorK.CT_STACK (only parsing).
  Local Notation sub_off := LbB_DCtorK.sub_off (only parsing).
  Local Notation app_win_sh_apart := LbB_DCtorK.app_win_sh_apart (only parsing).
  Local Notation app_win_hull_apart := LbB_DCtorK.app_win_hull_apart (only parsing).
  Local Notation inb_In' := LbB_DCtorK.inb_In' (only parsing).
  Local Notation keptf := LbB_DCtorK.keptf (only parsing).
  Local Notation rtbl_keptf := LbB_DCtorK.rtbl_keptf (only parsing).
  Local Notation rsub_keptf := LbB_DCtorK.rsub_keptf (only parsing).
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (ds ppos pcons pstr pstr2 err lo : Z)
            (pos : list word) (j1 j2 : list byte).
  Hypothesis Ha0 : a0 = Z_to_bv 64 ds.
  Hypothesis Ha1 : a1 = Z_to_bv 64 ppos.
  Hypothesis Ha2 : a2 = Z_to_bv 64 pcons.
  Hypothesis Ha3 : a3 = Z_to_bv 64 pstr.
  Hypothesis Ha4 : a4 = Z_to_bv 64 (err mod 2 ^ 64).
  Hypothesis Ha5 : a5 = Z_to_bv 64 pstr2.
  Hypothesis Herr : - 2 ^ 31 <= err < 0.

  Hypothesis DSA : addressable m0 ds DS_SIZE.
  Hypothesis DSW : wr_at asegs m0 ds DS_SIZE.
  Hypothesis DSO : app_obj ds DS_SIZE.
  Hypothesis DS8 : ds mod 8 = 0.
  Hypothesis DSV : shvis m0 ds (ds + DS_SIZE).
  Hypothesis PPA : addressable m0 ppos 24.
  Hypothesis PPO : app_obj ppos 24.
  Hypothesis PP8 : ppos mod 8 = 0.
  Hypothesis PPV : shvis m0 ppos (ppos + 24).
  Hypothesis PPC : u64arr asegs m0 ppos pos.
  Hypothesis PPL : length pos = 3%nat.
  Hypothesis S1A : addressable m0 pstr 24.
  Hypothesis S1O : app_obj pstr 24.
  Hypothesis S18 : pstr mod 8 = 0.
  Hypothesis S1V : shvis m0 pstr (pstr + 24).
  Hypothesis S1C : rw_cells asegs m0 pstr [C2 (Z_to_bv 64 0); CB 22 j1].
  Hypothesis S2A : addressable m0 pstr2 24.
  Hypothesis S2O : app_obj pstr2 24.
  Hypothesis S28 : pstr2 mod 8 = 0.
  Hypothesis S2V : shvis m0 pstr2 (pstr2 + 24).
  Hypothesis S2C : rw_cells asegs m0 pstr2 [C2 (Z_to_bv 64 0); CB 22 j2].
  Hypothesis PCA : addressable m0 pcons 48.
  Hypothesis PCO : app_obj pcons 48.
  Hypothesis PC8 : pcons mod 8 = 0.
  Hypothesis PCC : rw_cells asegs m0 (pcons + 32) [C8 (Z_to_bv 64 0)].
  Hypothesis DISJ : forall a, ds <= a < ds + DS_SIZE -> ~ (ppos <= a < ppos + 24) /\ ~ (pstr <= a < pstr + 24)
                         /\ ~ (pstr2 <= a < pstr2 + 24) /\ ~ (pcons <= a < pcons + 48).

  Hypothesis STK : stk asegs m0 lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - CT_STACK.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SPHI : bv_unsigned sp <= AAPP_HI.
  Hypothesis SPOBJ : forall O n, O = ds /\ n = DS_SIZE \/ O = ppos /\ n = 24 \/ O = pstr /\ n = 24 \/ O = pstr2 /\ n = 24
                                 \/ O = pcons /\ n = 48 ->
                     O + n <= bv_unsigned sp - CT_STACK \/ bv_unsigned sp <= O.
  Hypothesis OHI : forall O n, O = ds /\ n = DS_SIZE \/ O = ppos /\ n = 24 \/ O = pstr /\ n = 24 \/ O = pstr2 /\ n = 24 ->
                   O + n + 64 <= AAPP_HI.

  Hypothesis MI0 : mem_inv asegs m0.
  Hypothesis AC0 : ACONST m0.
  Hypothesis LV0 : LINV_P5 m0.

  Variable Hr : asr.
  Hypothesis HHr : asan_rt_hyps Hr.

  Local Notation disj_of_apart := (@LbB_DCtorK.disj_of_apart lo) (only parsing).
  Local Notation Wc := (@LbB_DCtorK.Wc ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) (only parsing).
  Local Notation Pct := (@LbB_DCtorK.Pct sp ds ppos pcons pstr pstr2 lo pos j1 j2) (only parsing).
  Local Notation Pct_m0 := (@LbB_DCtorK.Pct_m0 sp m0 ds ppos pcons pstr pstr2 err lo pos j1 j2 Herr DSA DSW DSV PPA PPV PPC S1A S1V S1C S2A S2V S2C PCA PCC STK AC0 LV0) (only parsing).
  Local Notation cwin := (@LbB_DCtorK.cwin sp ds) (only parsing).
  Local Notation sp_range := (@LbB_DCtorK.sp_range HCEIL sp m0 ds ppos pcons pstr pstr2 err lo pos PPL STK CEIL LO SPHI) (only parsing).
  Local Notation cwin_app := (@LbB_DCtorK.cwin_app HCEIL sp m0 ds ppos pcons pstr pstr2 err lo pos DSO PPL STK CEIL LO SPHI) (only parsing).
  Local Notation aconst_ok_cwin := (@LbB_DCtorK.aconst_ok_cwin HCEIL sp m0 ds ppos pcons pstr pstr2 err lo pos DSO PPL STK CEIL LO SPHI) (only parsing).
  Local Notation cwin_sh_apart := (@LbB_DCtorK.cwin_sh_apart HCEIL sp m0 ds ppos pcons pstr pstr2 err lo pos DSO PPL STK CEIL LO SPHI) (only parsing).
  Local Notation disj_cwin := (@LbB_DCtorK.disj_cwin sp ds) (only parsing).
  Local Notation outside_cwin := (@LbB_DCtorK.outside_cwin sp ds) (only parsing).
  Local Notation ACONST_cwin := (@LbB_DCtorK.ACONST_cwin HCEIL sp m0 ds ppos pcons pstr pstr2 err lo pos DSO PPL STK CEIL LO SPHI) (only parsing).
  Local Notation Pct_munch := (@LbB_DCtorK.Pct_munch HCEIL sp m0 ds ppos pcons pstr pstr2 err lo pos j1 j2 Herr DSO PPO PPL S1O S2O PCO DISJ STK CEIL LO SPHI SPOBJ) (only parsing).
  Local Notation vtkn_ok := (@LbB_DCtorK.vtkn_ok sp ds ppos pcons pstr pstr2 err pos PPL) (only parsing).
  Local Notation evW := (@LbB_DCtorK.evW ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds ppos pcons pstr pstr2 err pos PPL) (only parsing).
  Local Notation gz_of_addr := (@LbB_DCtorK.gz_of_addr sp ds ppos pcons pstr pstr2 err pos PPL) (only parsing).
  Local Notation Pct_gz := (@LbB_DCtorK.Pct_gz sp ds ppos pcons pstr pstr2 err lo pos j1 j2 PPL) (only parsing).
  Local Notation ev32 := (@LbB_DCtorK.ev32 ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds ppos pcons pstr pstr2 err pos Ha0 PPL) (only parsing).
  Local Notation ev36 := (@LbB_DCtorK.ev36 ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds ppos pcons pstr pstr2 err pos Ha2 PPL) (only parsing).
  Local Notation ev37 := (@LbB_DCtorK.ev37 ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds ppos pcons pstr pstr2 err pos Ha3 PPL) (only parsing).
  Local Notation ev38 := (@LbB_DCtorK.ev38 ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds ppos pcons pstr pstr2 err pos Ha5 PPL) (only parsing).
  Local Notation shobj_val := (@LbB_DCtorK.shobj_val ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds ppos pcons pstr pstr2 err pos Ha0 Ha2 Ha3 Ha5 Herr DSO PPL S1O S2O PCO) (only parsing).
  Local Notation shz_ok := (@LbB_DCtorK.shz_ok ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds ppos pcons pstr pstr2 err lo pos j1 j2 Ha0 Ha2 Ha3 Ha5 Herr DSO PPL S1O S2O PCO) (only parsing).
  Local Notation kshz_ok := (@LbB_DCtorK.kshz_ok ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds ppos pcons pstr pstr2 err lo pos j1 j2 Ha0 Ha2 Ha3 Ha5 Herr DSO PPL S1O S2O PCO) (only parsing).
  Local Notation shdj_ok := (@LbB_DCtorK.shdj_ok HCEIL ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 ds ppos pcons pstr pstr2 err lo pos Ha0 Ha2 Ha3 Ha5 Herr DSO PPL S1O S2O PCO STK CEIL LO SPHI) (only parsing).
  Local Notation kshd_ok := (@LbB_DCtorK.kshd_ok HCEIL ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 ds ppos pcons pstr pstr2 err lo pos Ha0 Ha2 Ha3 Ha5 Herr DSO PPL S1O S2O PCO STK CEIL LO SPHI) (only parsing).
  Local Notation kst_ok := (@LbB_DCtorK.kst_ok HCEIL ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 ds ppos pcons pstr pstr2 err lo pos j1 j2 Ha0 Ha2 Ha3 Ha5 Herr DSO PPO PPL S1O S2O PCO DISJ STK CEIL LO SPHI SPOBJ) (only parsing).
  Local Notation HB1c := (@LbB_DCtorK.HB1c ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) (only parsing).
  Local Notation HB2c := (@LbB_DCtorK.HB2c ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds ppos pcons pstr pstr2 err pos Ha0 DSO PPL) (only parsing).
  Local Notation HW1c := (@LbB_DCtorK.HW1c HCEIL sp m0 ds ppos pcons pstr pstr2 err lo pos PPL STK CEIL LO SPHI) (only parsing).
  Local Notation HW2c := (@LbB_DCtorK.HW2c sp ds ppos pcons pstr pstr2 err pos DSO PPL) (only parsing).
  Local Notation WDJc := (@LbB_DCtorK.WDJc sp ds ppos pcons pstr pstr2 err pos PPL SPOBJ) (only parsing).
  Local Notation Pct_step := (@LbB_DCtorK.Pct_step HCEIL sp m0 ds ppos pcons pstr pstr2 err lo pos j1 j2 Herr DSO PPO PPL S1O S2O PCO DISJ STK CEIL LO SPHI SPOBJ) (only parsing).
  Local Notation CW := (@LbB_DCtorK.CW sp ds) (only parsing).
  Local Notation Pw := (@LbB_DCtorK.Pw sp m0 ds ppos pcons pstr pstr2 lo pos j1 j2) (only parsing).
  Local Notation Pw_m0 := (@LbB_DCtorK.Pw_m0 sp m0 ds ppos pcons pstr pstr2 err lo pos j1 j2 Herr DSA DSW DSV PPA PPV PPC S1A S1V S1C S2A S2V S2C PCA PCC STK AC0 LV0) (only parsing).
  Local Notation Pw_step := (@LbB_DCtorK.Pw_step HCEIL sp m0 ds ppos pcons pstr pstr2 err lo pos j1 j2 Herr DSO PPO PPL S1O S2O PCO DISJ STK CEIL LO SPHI SPOBJ) (only parsing).
  Local Notation rtbl0 := (@LbB_DCtorK.rtbl0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) (only parsing).
  Local Notation wr_keys_stk := (@LbB_DCtorK.wr_keys_stk HCEIL sp m0 ds ppos pcons pstr pstr2 err lo pos j1 j2 PPL STK CEIL LO SPHI) (only parsing).
  Local Notation wr_keys_ds := (@LbB_DCtorK.wr_keys_ds sp ds ppos pcons pstr pstr2 err lo pos j1 j2 PPL) (only parsing).
  Local Notation ctor_P := (@LbB_DCtorK.ctor_P ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 ds ppos pcons pstr pstr2 err lo pos j1 j2) (only parsing).
  Local Notation ctor_call := (@LbB_DCtorK.ctor_call HCEIL ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 ds ppos pcons pstr pstr2 err lo pos j1 j2 Herr DSO PPO PPL S1O S2O PCO DISJ STK CEIL LO SPHI SPOBJ) (only parsing).
  Local Notation dst_facts := (@LbB_DCtorK.dst_facts HCEIL sp m0 ds ppos pcons pstr pstr2 err lo pos j1 j2 DSO PPL STK CEIL LO SPHI SPOBJ OHI) (only parsing).
  Local Notation src_facts := (@LbB_DCtorK.src_facts sp ds ppos pcons pstr pstr2 lo pos j1 j2 PPO S1O S2O DISJ SPOBJ OHI) (only parsing).
  Local Notation stk_call := (@LbB_DCtorK.stk_call HCEIL sp m0 ds ppos pcons pstr pstr2 err lo pos j1 j2 PPL STK CEIL LO SPHI) (only parsing).
  Local Notation ctor_memset := (@LbB_DCtorK.ctor_memset HCEIL ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 ds ppos pcons pstr pstr2 err lo pos j1 j2 Herr DSO PPO PPL S1O S2O PCO DISJ STK CEIL LO SPHI SPOBJ OHI Hr HHr) (only parsing).
  Local Notation ctor_memcpy := (@LbB_DCtorK.ctor_memcpy HCEIL ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 ds ppos pcons pstr pstr2 err lo pos j1 j2 Herr DSO PPO PPL S1O S2O PCO DISJ STK CEIL LO SPHI SPOBJ OHI Hr HHr) (only parsing).

  Notation spz := (bv_unsigned sp) (only parsing).

  Ltac evw := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, Wc;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Ltac wnorm HspE := rewrite ?Ha0, ?Ha1, ?Ha2, ?Ha3, ?Ha5, ?HspE; rewrite ?w_mul, ?w_add, ?w_addm, ?v_addi_Z by lia.

  Ltac kfix_ok HspE :=
    unfold know_ok; repeat (apply Forall_cons; [ eapply kshadow0; [ evw; wnorm HspE; reflexivity | lia | sh0_from_gz ] | ]);
    apply Forall_nil.

  Ltac scw HspE :=
    cbn [sc_denot]; unfold flat, elenZ;
    repeat (erewrite estart_sh; [| evw; wnorm HspE; reflexivity | lia]);
    unfold estart; cbn [a_base a_off]; evw; wnorm HspE; rewrite ?u64_of_Z by lia; cbn [edenot];
    repeat match goal with
    | |- context [?a / 8] =>
        let t := fresh "t" in let Ht := fresh "Ht" in
        pose proof (div8_bound a ltac:(lia)) as Ht; set (t := a / 8) in *; clearbody t
    end;
    rewrite ?u64_of_Z by lia; unfold SHBASE; lia.

  Ltac tnorm H :=
    lazymatch type of H with
    | ftbl ?W ?B ?m ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    | rtbl ?W ?R ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    end.

  Ltac rget HRT r HspE H :=
    lazymatch type of HRT with
    | rtbl ?W ?R ?RT =>
        let e := eval vm_compute in (match List.find (fun re => bv_eqb (fst re) r) RT with Some re => snd re | None => ELit 0 end) in
        assert (H : PropExec.getr R r = edenot (wenv W) e)
          by (apply (rtbl_In W R RT r e HRT); apply inb_In'; vm_compute; reflexivity);
        unfold wenv in H; cbn [edenot] in H; unfold HLib.Eseed, reg_ev, Wc in H;
        lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
              Init.Nat.add Nat.sub nth app] in H;
        rewrite ?Ha0, ?Ha1, ?Ha2, ?Ha3, ?Ha5, ?HspE in H; rewrite ?w_mul, ?w_add, ?w_addm, ?v_addi_Z in H by lia
    end.

  Ltac dkrun HRT HSF HDF HP HMI fuel stops :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HDF with ftbl _ _ _ ?DF =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let kb := constr:(kst_ctor ++ fkn (EVar 33) SF ++ fkn (EVar 32) DF) in
        let kf := eval vm_compute in (kfix stops pc (HLib.srs sr_id RT) kb) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] ((kst_ctor ++ kf) ++ fkn (EVar 33) SF ++ fkn (EVar 32) DF) 60) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wc) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 32) (s_log SSr) DF) in
          eapply (dk_run Wc (EVar 33) (EVar 32) spz ds (-8192) 0 0 DS_SIZE eq_refl eq_refl HB1c HB2c HW1c HW2c WDJc Pw Pw_step
                    Q R F pc fc m ro RT SF DF [] (kst_ctor ++ kf) fuel stops (SCR [] [] []) 60%N SSr scs scr' RT' ks1 ks2);
          [ assumption | exact HRT | vm_compute; reflexivity | exact HSF | exact HDF | exact HP | exact HMI
          | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
          | apply (wr_keys_stk m); [exact (proj1 HP) | vm_compute; reflexivity] | apply (wr_keys_ds m); [exact (proj1 HP) | vm_compute; reflexivity]
          | unfold know_ok; apply Forall_app; split; [apply kst_ok; exact (proj1 HP) | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end
    end.

  Ltac dside spv :=
    change (bv_unsigned sp) with spv;
    lazymatch goal with
    | |- fin _ _ _ = true => rewrite ?sub_off; vm_compute; reflexivity
    | |- _ mod _ = _ => unfold DSC_R2, DSC_R3, DSC_R4, DSC_R5, DSC_R6, DSC_R7, DSC_R8; reflexivity
    | |- _ => unfold DS_SIZE, AINTRIN_STACK, DSC_R2, DSC_R3, DSC_R4, DSC_R5, DSC_R6, DSC_R7, DSC_R8 in *; lia
    end.

  Ltac dkf HP HspE :=
    lazymatch type of HP with ?Pw ?m =>
      let Z1 := fresh "Z" in let Z2 := fresh "Z" in let Z3 := fresh "Z" in let Z4 := fresh "Z" in let Z5 := fresh "Z" in
      pose proof (Pct_gz m (proj1 HP)) as (Z1 & Z2 & Z3 & Z4 & Z5); unfold DS_SIZE in Z1; kfix_ok HspE
    end.

  Ltac dregs HRT HspE G10 G11 G12 G2 G1 :=
    try clear G10; try clear G11; try clear G12; try clear G2; try clear G1;
    rget HRT (10%bv : reg) HspE G10; rget HRT (11%bv : reg) HspE G11; rget HRT (12%bv : reg) HspE G12;
    rget HRT (2%bv : reg) HspE G2; rget HRT (1%bv : reg) HspE G1.

  Ltac dcall_ms icpt spv RF HRT HSF HDF HP HMI G10 G11 G12 G2 G1 :=
    lazymatch type of G10 with _ = Z_to_bv 64 ?d =>
    lazymatch type of G12 with _ = Z_to_bv 64 ?n =>
    lazymatch type of G2 with _ = Z_to_bv 64 ?spc =>
    lazymatch type of G1 with _ = Z_to_bv 64 ?ret =>
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      change (Z_to_bv 64 pc) with (Z_to_bv 64 (if icpt then AMEMSET_STUB else AASAN_MEMSET));
      eapply (ctor_memset _ icpt _ _ _ _ _ d n ret spc RF HRT HSF HDF HP HMI G10 G11 G12 G2 G1);
        [ first [dside spv | match goal with |- ?G => idtac "DSFAIL" G end; fail 1] .. | ]
    end end end end end.

  Ltac dcall_mc spv RF HRT HSF HDF HP HMI G10 G11 G12 G2 G1 src SRC LEN :=
    lazymatch type of G10 with _ = Z_to_bv 64 ?d =>
    lazymatch type of G11 with _ = Z_to_bv 64 ?sa =>
    lazymatch type of G2 with _ = Z_to_bv 64 ?spc =>
    lazymatch type of G1 with _ = Z_to_bv 64 ?ret =>
      eapply (ctor_memcpy _ _ _ _ _ _ d sa src ret spc RF HRT HSF HDF HP HMI G10 G11 G12 G2 G1 ltac:(clear; tauto) SRC LEN);
        [ first [dside spv | match goal with |- ?G => idtac "DSFAIL" G end; fail 1] .. | ]
    end end end end.

  Ltac dres_zero HDF RES HDF' :=
    lazymatch type of RES with rw_cells _ ?m2 ?d [CB (Z.to_nat ?n) _] =>
      rewrite ?sub_off in HDF;
      let j := eval vm_compute in (Z.to_nat (n / 8)) in
      let r := eval vm_compute in (n mod 8) in
      let HZ := fresh "HZ" in
      lazymatch r with
      | 0 => pose proof (ftbl_zres Wc ds m2 d n j eq_refl RES) as HZ
      | _ => pose proof (ftbl_zres1 Wc ds m2 d n ltac:(lia) RES) as HZ
      end;
      rewrite ?sub_off in HZ;
      pose proof (ftbl_app _ _ _ _ _ HDF HZ) as HDF'; clear HDF HZ RES; tnorm HDF'
    end.

  Ltac clear_nonarith :=
    repeat match goal with
    | H : ?T |- _ =>
        lazymatch T with
        | @eq _ _ _ => fail | Z.le _ _ => fail | Z.lt _ _ => fail | Z.ge _ _ => fail | Z.gt _ _ => fail
        | _ /\ _ => fail | _ \/ _ => fail | ~ _ => fail
        | _ => lazymatch type of T with Prop => clear H | _ => fail end
        end
    end.

  Ltac dstk spv HSF := change (bv_unsigned sp) with spv in HSF; rewrite ?sub_off in HSF; tnorm HSF.

  Lemma ctor_evt :
    evt asegs ctor_P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 ADS_CTOR) fc None m0 (seg_rom asegs)).
Proof.
  pose proof rtbl0 as HRT0.
  assert (HSF0 : ftbl Wc spz m0 []) by apply ftbl_nil.
  assert (HDF0 : ftbl Wc ds m0 []) by apply ftbl_nil.
  pose proof Pw_m0 as HP0.
  pose proof (rfull_mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as RF0.
  pose (spv := bv_unsigned sp).
  assert (HspE : sp = Z_to_bv 64 spv) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof sp_range as (SR1 & SR2 & SR3 & SR4).
  pose proof aceil_facts as (AC1 & AC2 & AC3 & AC4).
  pose proof DSO as (DO1 & DO2 & DO3).
  pose proof PPO as (PO1 & PO2 & PO3).
  pose proof S1O as (QO1 & QO2 & QO3).
  pose proof S2O as (UO1 & UO2 & UO3).
  pose proof PCO as (KO1 & KO2 & KO3).
  unfold AIMG_TOP, AAPP_HI, ALOWSH_LO, AHI_LO, DS_SIZE, CT_STACK in DO1, DO2, DO3, PO1, PO2, PO3, QO1, QO2, QO3, UO1, UO2, UO3, KO1, KO2, KO3, SR3, SR4.
  dkrun HRT0 HSF0 HDF0 HP0 MI0 600%nat [AMEMSET_STUB].
  { dkf HP0 HspE. }
  { split_scs; scw HspE. }
  intros R1 m1 RF1 HRT1 HSF1 HDF1 HP1 HMI1 MU1 WM1.
  cbn [s_pc].
  tnorm HSF1. tnorm HDF1.
  dregs HRT1 HspE G10 G11 G12 G2 G1.
  dcall_ms true spv RF1 HRT1 HSF1 HDF1 HP1 HMI1 G10 G11 G12 G2 G1.
  intros R1' m1' RF1' HRT1' HSF1' HDF1' HP1' HMI1' RES1.
  dres_zero HDF1' RES1 HDF1''.
  tnorm HRT1'. dstk spv HSF1'.
  dkrun HRT1' HSF1' HDF1'' HP1' HMI1' 600%nat [AASAN_MEMSET].
  { dkf HP1' HspE. }
  { split_scs; scw HspE. }
  intros R2 m2 RF2 HRT2 HSF2 HDF2 HP2 HMI2 MU2 WM2.
  cbn [s_pc].
  tnorm HSF2. tnorm HDF2.
  dregs HRT2 HspE G10 G11 G12 G2 G1.
  dcall_ms false spv RF2 HRT2 HSF2 HDF2 HP2 HMI2 G10 G11 G12 G2 G1.
  intros R2' m2' RF2' HRT2' HSF2' HDF2' HP2' HMI2' RES2.
  dres_zero HDF2' RES2 HDF2''.
  tnorm HRT2'. dstk spv HSF2'.
  dkrun HRT2' HSF2' HDF2'' HP2' HMI2' 600%nat [AASAN_MEMSET].
  { dkf HP2' HspE. }
  { split_scs; scw HspE. }
  intros R3 m3 RF3 HRT3 HSF3 HDF3 HP3 HMI3 MU3 WM3.
  cbn [s_pc].
  tnorm HSF3. tnorm HDF3.
  dregs HRT3 HspE G10 G11 G12 G2 G1.
  dcall_ms false spv RF3 HRT3 HSF3 HDF3 HP3 HMI3 G10 G11 G12 G2 G1.
  intros R3' m3' RF3' HRT3' HSF3' HDF3' HP3' HMI3' RES3.
  dres_zero HDF3' RES3 HDF3''.
  tnorm HRT3'. dstk spv HSF3'.
  dkrun HRT3' HSF3' HDF3'' HP3' HMI3' 600%nat [AMEMSET_STUB].
  { dkf HP3' HspE. }
  { split_scs; scw HspE. }
  intros R4 m4 RF4 HRT4 HSF4 HDF4 HP4 HMI4 MU4 WM4.
  cbn [s_pc].
  tnorm HSF4. tnorm HDF4.
  dregs HRT4 HspE G10 G11 G12 G2 G1.
  lazymatch type of G10 with _ = Z_to_bv 64 ?d => lazymatch type of G12 with _ = Z_to_bv 64 ?n =>
    pose proof (ftbl_fsplit Wc ds m4 (d - ds) n _ HDF4) as HDF4s end end.
  rewrite ?sub_off in HDF4s. tnorm HDF4s.
  dcall_ms true spv RF4 HRT4 HSF4 HDF4s HP4 HMI4 G10 G11 G12 G2 G1.
  intros R4' m4' RF4' HRT4' HSF4' HDF4' HP4' HMI4' RES4.
  dres_zero HDF4' RES4 HDF4''.
  tnorm HRT4'. dstk spv HSF4'.
  eapply LbB_DCtorR5.cut5; eassumption.
Qed.
End CtorR1.
