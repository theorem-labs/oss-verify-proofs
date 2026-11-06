(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablLib.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablImgU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module Tabl_StrcmpU1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablLib.

Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Img := TablImgU1.
Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation L := Img.Ly.L.

Definition SC_ENTRY : Z := 0xe3330.
Definition SC_LOOP  : Z := 0xe3348.
Definition SC_END   : Z := 0xe3360.
Definition SN_ENTRY : Z := 0xe3690.
Definition SN_LOOP  : Z := 0xe36a4.
Definition SN_END1  : Z := 0xe36cc.
Definition SN_END2  : Z := 0xe36dc.
Definition SN_END3  : Z := 0xe36e4.
Definition S_STOPS : list Z := [SC_LOOP; SC_END; SN_LOOP; SN_END1; SN_END2; SN_END3].

Definition name_ok (M : mem) (p n : Z) : Prop :=
  0 < p /\ p + n + 1 <= 2 ^ 47 /\ 0 <= n /\
  (forall i, 0 <= i < n -> exists c, 0 < c < 256 /\ CRep.fld SEGS M (p + i) 1 c) /\ CRep.fld SEGS M (p + n) 1 0.

Section Str.
  Context {fx : FPState}.
  Variables (M : mem) (A LA p n : Z).
  Hypothesis HRO : ro_clear L M.
  Hypothesis CS : ro_cstr SEGS L A LA.
  Hypothesis NM : name_ok M p n.
  #[local] Abbreviation st R pc := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)).

  Lemma lit_bounds : 0x10000 <= A /\ 0 <= LA /\ A + LA + 8 <= 2 ^ 47.
  Proof using A LA CS. destruct CS as (X & Y & Z' & _). lia. Qed.
  Lemma name_bounds : 0 < p /\ p + n + 1 <= 2 ^ 47 /\ 0 <= n.
  Proof using M p n NM. destruct NM as (X & Y & Z' & _). lia. Qed.

  Lemma lit_byte : forall i, 0 <= i <= LA -> exists c, 0 <= c < 256 /\ cellw SEGS M (A + i) 1 c /\ (c = 0 <-> i = LA).
  Proof using M A LA HRO CS.
    intros i Hi. destruct CS as (_ & _ & _ & HM). destruct (HM M HRO) as (S & Z0 & _).
    destruct (Z.eq_dec i LA) as [->|NE].
    - exists 0. split; [lia|]. split; [split; [cbn; lia | exact Z0] | lia].
    - destruct (S i ltac:(lia)) as (c & Hc & F). exists c. split; [lia|]. split; [split; [cbn; lia | exact F] | lia].
  Qed.
  Lemma name_byte : forall i, 0 <= i <= n -> exists c, 0 <= c < 256 /\ cellw SEGS M (p + i) 1 c /\ (c = 0 <-> i = n).
  Proof using M p n NM.
    intros i Hi. destruct NM as (_ & _ & _ & S & Z0).
    destruct (Z.eq_dec i n) as [->|NE].
    - exists 0. split; [lia|]. split; [split; [cbn; lia | exact Z0] | lia].
    - destruct (S i ltac:(lia)) as (c & Hc & F). exists c. split; [lia|]. split; [split; [cbn; lia | exact F] | lia].
  Qed.

  Lemma sc_step : forall R pc i,
    (pc = SC_ENTRY /\ i = 0 \/ pc = SC_LOOP) -> 0 <= i <= LA -> i <= n ->
    getr R 10%bv = Z_to_bv 64 (A + i) -> getr R 11%bv = Z_to_bv 64 (p + i) ->
    exists R', kept R R' /\
      ( msteps SEGS (st R pc) (st R' SC_END)
      \/ (i < LA /\ i < n /\ msteps SEGS (st R pc) (st R' SC_LOOP) /\
          getr R' 10%bv = Z_to_bv 64 (A + i + 1) /\ getr R' 11%bv = Z_to_bv 64 (p + i + 1)) ).
  Proof using fx M A LA p n HRO CS NM.
    intros R pc i Hpc Hi Hin H10 H11. pose proof lit_bounds as (B0 & B1 & B2). pose proof name_bounds as (N0 & N1 & N2).
    destruct (lit_byte i Hi) as (c & Hc & Cc & Hcz). destruct (name_byte i ltac:(lia)) as (d & Hd & Cd & Hdz).
    pose (E := Eseed R [Z_to_bv 64 (A + i); Z_to_bv 64 (p + i); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                        Z_to_bv 64 c; Z_to_bv 64 d]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    destruct (Z.eq_dec c 0) as [Cz|Cnz].
    -
      destruct Hpc as [[-> ->]| ->].
      + xrun HR HK 30%nat S_STOPS (SCR [true] [EVar 40; EVar 41] []) 42%N.
        { split_scs; try sc_auto1; first [sc_rd Cc | sc_rd Cd | cbn [sc_denot]; evs; rewrite br_eq by lia; bool_lia]. }
        exists R'. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl) | left; exact Hms].
      + xrun HR HK 30%nat S_STOPS (SCR [true] [EVar 40; EVar 41] []) 42%N.
        { split_scs; try sc_auto1; first [sc_rd Cc | sc_rd Cd | cbn [sc_denot]; evs; rewrite br_eq by lia; bool_lia]. }
        exists R'. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl) | left; exact Hms].
    - destruct (Z.eq_dec c d) as [Ceq|Cne].
      +
        assert (i < LA) by lia. assert (d <> 0) by lia. assert (i < n) by lia.
        destruct Hpc as [[-> ->]| ->].
        * xrun HR HK 30%nat S_STOPS (SCR [false; false] [EVar 40; EVar 41] []) 42%N.
          { split_scs; try sc_auto1; first [sc_rd Cc | sc_rd Cd | cbn [sc_denot]; evs; rewrite ?br_eq, ?br_ne by lia; bool_lia]. }
          exists R'. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl) | right]. split; [lia|]. split; [lia|]. split; [exact Hms|].
          rreg HR' 10%bv A10. rreg HR' 11%bv A11. rewrite A10, A11, !w_add by lia. split; f_equal; lia.
        * xrun HR HK 30%nat S_STOPS (SCR [false; true] [EVar 40; EVar 41] []) 42%N.
          { split_scs; try sc_auto1; first [sc_rd Cc | sc_rd Cd | cbn [sc_denot]; evs; rewrite ?br_eq, ?br_ne by lia; bool_lia]. }
          exists R'. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl) | right]. split; [lia|]. split; [lia|]. split; [exact Hms|].
          rreg HR' 10%bv A10. rreg HR' 11%bv A11. rewrite A10, A11, !w_add by lia. split; f_equal; lia.
      +
        destruct Hpc as [[-> ->]| ->].
        * xrun HR HK 30%nat S_STOPS (SCR [false; true] [EVar 40; EVar 41] []) 42%N.
          { split_scs; try sc_auto1; first [sc_rd Cc | sc_rd Cd | cbn [sc_denot]; evs; rewrite ?br_eq, ?br_ne by lia; bool_lia]. }
          exists R'. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl) | left; exact Hms].
        * xrun HR HK 30%nat S_STOPS (SCR [false; false] [EVar 40; EVar 41] []) 42%N.
          { split_scs; try sc_auto1; first [sc_rd Cc | sc_rd Cd | cbn [sc_denot]; evs; rewrite ?br_eq, ?br_ne by lia; bool_lia]. }
          exists R'. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl) | left; exact Hms].
  Qed.

  Lemma sc_loop : forall (k : nat) R pc i,
    (pc = SC_ENTRY /\ i = 0 \/ pc = SC_LOOP) -> 0 <= i <= LA -> i <= n -> LA - i <= Z.of_nat k ->
    getr R 10%bv = Z_to_bv 64 (A + i) -> getr R 11%bv = Z_to_bv 64 (p + i) ->
    exists R', kept R R' /\ msteps SEGS (st R pc) (st R' SC_END).
  Proof using fx M A LA p n HRO CS NM.
    induction k as [|k IH]; intros R pc i Hpc Hi Hin Hk H10 H11.
    - destruct (sc_step R pc i Hpc Hi Hin H10 H11) as (R' & K & [MS|(LT & _)]); [|lia].
      exists R'. auto.
    - destruct (sc_step R pc i Hpc Hi Hin H10 H11) as (R1 & K1 & [MS1|(LT & LTn & MS1 & A10 & A11)]).
      + exists R1. auto.
      + destruct (IH R1 SC_LOOP (i + 1) ltac:(right; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(rewrite A10; f_equal; lia) ltac:(rewrite A11; f_equal; lia)) as (R' & K' & MS').
        exists R'. split; [exact (keeps_cs_trans _ _ _ K1 K')|]. eapply msteps_trans; [exact MS1 | exact MS'].
  Qed.

  Lemma sc_end : forall R (ret : word), getr R 1%bv = ret -> ret_ok ret ->
    exists R', kept R R' /\ msteps SEGS (st R SC_END) (@mkst fx R' ret M (seg_rom SEGS)).
  Proof using fx M.
    intros R ret Hra Hret.
    pose (E := Eseed R (@nil word)).
    assert (HR : regs_ok E sr_id R) by apply regs_ok_seed.
    assert (HK : know_ok SEGS E M []) by constructor.
    xrun HR HK 10%nat (@nil Z) (SCR [] [] []) 42%N. { split_scs; try sc_auto1. }
    assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
    exists R'. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)|].
    eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret].
  Qed.

  Theorem strcmp_lit : forall R (ret : word),
    getr R 10%bv = Z_to_bv 64 A -> getr R 11%bv = Z_to_bv 64 p -> getr R 1%bv = ret -> ret_ok ret ->
    exists R', msteps SEGS (st R SC_ENTRY) (@mkst fx R' ret M (seg_rom SEGS)) /\ kept R R'.
  Proof using fx M A LA p n HRO CS NM.
    intros R ret H10 H11 Hra Hret. pose proof lit_bounds as (B0 & B1 & B2). pose proof name_bounds as (N0 & N1 & N2).
    destruct (sc_loop (Z.to_nat LA) R SC_ENTRY 0 ltac:(left; split; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(rewrite H10; f_equal; lia) ltac:(rewrite H11; f_equal; lia)) as (R1 & K1 & MS1).
    destruct (sc_end R1 ret ltac:(rewrite <- Hra; apply K1; (first [solve [clear; cbn; tauto] | cbn; tauto])) Hret) as (R2 & K2 & MS2).
    exists R2. split; [eapply msteps_trans; [exact MS1 | exact MS2] | exact (keeps_cs_trans _ _ _ K1 K2)].
  Qed.

  Lemma sn_step : forall R i c k0,
    0 <= i < LA -> i <= n -> i < k0 -> k0 < 2 ^ 62 -> cellw SEGS M (A + i) 1 c -> 0 < c < 256 ->
    getr R 10%bv = Z_to_bv 64 (A + i + 1) -> getr R 11%bv = Z_to_bv 64 (p + i) -> getr R 12%bv = Z_to_bv 64 (k0 - i - 1) ->
    getr R 13%bv = Z_to_bv 64 c ->
    exists R', kept R R' /\
      ( (msteps SEGS (st R SN_LOOP) (st R' SN_END1) /\ exists j, 0 <= j <= n /\ getr R' 11%bv = Z_to_bv 64 (p + j))
      \/ (i + 1 < LA /\ i < n /\ i + 1 < k0 /\ msteps SEGS (st R SN_LOOP) (st R' SN_LOOP) /\
          exists c', cellw SEGS M (A + i + 1) 1 c' /\ 0 < c' < 256 /\
          getr R' 10%bv = Z_to_bv 64 (A + i + 2) /\ getr R' 11%bv = Z_to_bv 64 (p + i + 1) /\
          getr R' 12%bv = Z_to_bv 64 (k0 - i - 2) /\ getr R' 13%bv = Z_to_bv 64 c') ).
  Proof using fx M A LA p n HRO CS NM.
    intros R i c k0 Hi Hin Hik Hk0 Cc Hc H10 H11 H12 H13. pose proof lit_bounds as (B0 & B1 & B2). pose proof name_bounds as (N0 & N1 & N2).
    destruct (name_byte i ltac:(lia)) as (d & Hd & Cd & Hdz).
    destruct (lit_byte (i + 1) ltac:(lia)) as (c' & Hc' & Cc' & Hcz'). rewrite Z.add_assoc in Cc' || idtac.
    pose (E := Eseed R [Z_to_bv 64 (A + i + 1); Z_to_bv 64 (p + i); Z_to_bv 64 (k0 - i - 1); Z_to_bv 64 c; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                        Z_to_bv 64 d; Z_to_bv 64 c']).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (12%bv, EVar 34); (13%bv, EVar 35)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    Ltac sn_sc Cc Cd := split_scs; try sc_auto1;
      first [ sc_rd Cc | sc_rd Cd
            | cbn [sc_denot]; evs; rewrite ?br_eq, ?br_ne by lia; bool_lia
            | idtac ].
    assert (CNT : forall b : bool, (if b then k0 - i - 1 = 0 else k0 - i - 1 <> 0) ->
                  sc_denot SEGS M E (SCBr b BC_EQ (EAlu ALU_SLTU (ELit 0) (EVar 34)) (ELit 0))).
    { intros b Hb. cbn [sc_denot]. evs. rewrite w_sltu by lia. rewrite br_eq by (try lia; destruct (0 <? k0 - i - 1); lia).
      destruct b; destruct (Z.ltb_spec 0 (k0 - i - 1)); first [bool_lia | exfalso; lia]. }
    destruct (Z.eq_dec c d) as [Ceq|Cne].
    -
      assert (Hdn : d <> 0) by lia. assert (Hin' : i < n) by lia.
      destruct (Z.eq_dec (k0 - i - 1) 0) as [Kz|Knz].
      + xrun HR HK 30%nat S_STOPS (SCR [false; false; true] [EVar 40; EVar 41] []) 42%N.
        { sn_sc Cd Cc'. apply CNT. exact Kz. }
        exists R'. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl) | left]. split; [exact Hms|].
        exists i. split; [lia|]. rreg HR' 11%bv A11. exact A11.
      + destruct (Z.eq_dec c' 0) as [Cz'|Cnz'].
        * xrun HR HK 30%nat S_STOPS (SCR [false; false; false; false] [EVar 40; EVar 41] []) 42%N.
          { sn_sc Cd Cc'. apply CNT. exact Knz. }
          exists R'. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl) | left]. split; [exact Hms|].
          exists (i + 1). split; [lia|]. rreg HR' 11%bv A11. rewrite A11, w_add by lia. f_equal. lia.
        * xrun HR HK 30%nat S_STOPS (SCR [false; false; false; true] [EVar 40; EVar 41] []) 42%N.
          { sn_sc Cd Cc'. apply CNT. exact Knz. }
          exists R'. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl) | right].
          split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hms|]. exists c'. split; [exact Cc'|]. split; [lia|].
          rreg HR' 10%bv A10. rreg HR' 11%bv A11. rreg HR' 12%bv A12. rreg HR' 13%bv A13.
          rewrite A10, A11, A12, A13. rewrite ?w_add, ?w_addm by lia. repeat split; f_equal; lia.
    - xrun HR HK 30%nat S_STOPS (SCR [true] [EVar 40; EVar 41] []) 42%N.
      { sn_sc Cd Cc'. }
      exists R'. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl) | left]. split; [exact Hms|].
      exists i. split; [lia|]. rreg HR' 11%bv A11. exact A11.
  Qed.

  Lemma sn_loop : forall (k : nat) R i c k0,
    0 <= i < LA -> i <= n -> i < k0 -> k0 < 2 ^ 62 -> LA - i <= Z.of_nat k -> cellw SEGS M (A + i) 1 c -> 0 < c < 256 ->
    getr R 10%bv = Z_to_bv 64 (A + i + 1) -> getr R 11%bv = Z_to_bv 64 (p + i) -> getr R 12%bv = Z_to_bv 64 (k0 - i - 1) ->
    getr R 13%bv = Z_to_bv 64 c ->
    exists R', kept R R' /\ msteps SEGS (st R SN_LOOP) (st R' SN_END1) /\ exists j, 0 <= j <= n /\ getr R' 11%bv = Z_to_bv 64 (p + j).
  Proof using fx M A LA p n HRO CS NM.
    induction k as [|k IH]; intros R i c k0 Hi Hin Hik Hk0 Hm Cc Hc H10 H11 H12 H13; [lia|].
    destruct (sn_step R i c k0 Hi Hin Hik Hk0 Cc Hc H10 H11 H12 H13) as (R1 & K1 & [(MS1 & J)|(L1 & L2 & L3 & MS1 & c' & Cc' & Hc' & A10 & A11 & A12 & A13)]).
    - exists R1. auto.
    - destruct (IH R1 (i + 1) c' k0 ltac:(lia) ltac:(lia) ltac:(lia) Hk0 ltac:(lia) ltac:(replace (A + (i + 1)) with (A + i + 1) by lia; exact Cc') Hc'
                  ltac:(rewrite A10; f_equal; lia) ltac:(rewrite A11; f_equal; lia) ltac:(rewrite A12; f_equal; lia) A13) as (R' & K' & MS' & J').
      exists R'. split; [exact (keeps_cs_trans _ _ _ K1 K')|]. split; [eapply msteps_trans; [exact MS1 | exact MS']| exact J'].
  Qed.

  Lemma sn_end13 : forall R (ret : word) pc j, (pc = SN_END1 \/ pc = SN_END3) -> 0 <= j <= n ->
    getr R 11%bv = Z_to_bv 64 (p + j) -> getr R 1%bv = ret -> ret_ok ret ->
    exists R', kept R R' /\ msteps SEGS (st R pc) (@mkst fx R' ret M (seg_rom SEGS)).
  Proof using fx M p n NM.
    intros R ret pc j Hpc Hj H11 Hra Hret. pose proof name_bounds as (N0 & N1 & N2).
    destruct (name_byte j Hj) as (d & Hd & Cd & _).
    pose (E := Eseed R [Z_to_bv 64 (p + j); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 d]).
    assert (HR : regs_ok E (srs sr_id [(11%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    destruct Hpc as [-> | ->].
    all: xrun HR HK 10%nat (@nil Z) (SCR [] [EVar 40] []) 42%N.
    1,3: split_scs; first [sc_rd Cd | sc_fl].
    all: assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
    all: exists R'; split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)|].
    all: eapply msteps_trans; [exact Hms|]; eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret].
  Qed.

  Theorem strncmp_lit : forall R (ret : word) k0,
    0 <= k0 < 2 ^ 62 ->
    getr R 10%bv = Z_to_bv 64 A -> getr R 11%bv = Z_to_bv 64 p -> getr R 12%bv = Z_to_bv 64 k0 -> getr R 1%bv = ret -> ret_ok ret ->
    exists R', msteps SEGS (st R SN_ENTRY) (@mkst fx R' ret M (seg_rom SEGS)) /\ kept R R'.
  Proof using fx M A LA p n HRO CS NM.
    intros R ret k0 Hk0 H10 H11 H12 Hra Hret. pose proof lit_bounds as (B0 & B1 & B2). pose proof name_bounds as (N0 & N1 & N2).
    destruct (lit_byte 0 ltac:(lia)) as (c & Hc & Cc & Hcz). rewrite Z.add_0_r in Cc.
    pose (E := Eseed R [Z_to_bv 64 A; Z_to_bv 64 p; Z_to_bv 64 k0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 c]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (12%bv, EVar 34)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    destruct (Z.eq_dec k0 0) as [Kz|Knz].
    -
      xrun HR HK 10%nat [SC_LOOP; SN_LOOP] (SCR [true] [EVar 40] []) 42%N.
      { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite br_eq by lia; bool_lia. }
      assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
      exists R'. split; [| exact (kept_of_syms _ _ _ _ HR' eq_refl)].
      eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret].
    - destruct (Z.eq_dec c 0) as [Cz|Cnz].
      +
        xrun HR HK 10%nat S_STOPS (SCR [false; true] [EVar 40] []) 42%N.
        { split_scs; try sc_auto1; first [sc_rd Cc | cbn [sc_denot]; evs; rewrite br_eq by lia; bool_lia]. }
        destruct (sn_end13 R' ret SN_END3 0 ltac:(right; reflexivity) ltac:(lia)
                    ltac:(rreg HR' 11%bv A11; rewrite A11; f_equal; lia) ltac:(rewrite <- Hra; apply (kept_of_syms _ _ _ _ HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto])) Hret)
          as (R2 & K2 & MS2).
        exists R2. split; [eapply msteps_trans; [exact Hms | exact MS2] | exact (keeps_cs_trans _ _ _ (kept_of_syms _ _ _ _ HR' eq_refl) K2)].
      + xrun HR HK 10%nat S_STOPS (SCR [false; false] [EVar 40] []) 42%N.
        { split_scs; try sc_auto1; first [sc_rd Cc | cbn [sc_denot]; evs; rewrite br_eq by lia; bool_lia]. }
        rreg HR' 10%bv A10. rreg HR' 11%bv A11. rreg HR' 12%bv A12. rreg HR' 13%bv A13.
        destruct (sn_loop (Z.to_nat LA) R' 0 c k0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Cc) ltac:(lia)
                    ltac:(rewrite A10, w_add by lia; f_equal; lia) ltac:(rewrite A11; f_equal; lia) ltac:(rewrite A12, w_addm by lia; f_equal; lia) A13)
          as (R2 & K2 & MS2 & j & Hj & B11).
        destruct (sn_end13 R2 ret SN_END1 j ltac:(left; reflexivity) Hj B11
                    ltac:(rewrite <- Hra; symmetry; symmetry; apply (keeps_cs_trans _ _ _ (kept_of_syms _ _ _ _ HR' eq_refl) K2); (first [solve [clear; cbn; tauto] | cbn; tauto])) Hret) as (R3 & K3 & MS3).
        exists R3. split; [| exact (keeps_cs_trans _ _ _ (keeps_cs_trans _ _ _ (kept_of_syms _ _ _ _ HR' eq_refl) K2) K3)].
        eapply msteps_trans; [exact Hms|]. eapply msteps_trans; [exact MS2 | exact MS3].
  Qed.
End Str.
End Tabl_StrcmpU1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibEff
  SymExec3 SymExec3Sound SymRun3 MmapSim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep StrLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablRep TablStmts TablLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_ImportU1.Tabl_StrcmpU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablImgU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Img := TablImgU1.
Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation L := Img.Ly.L.
Abbreviation ti := Img.ti.
Abbreviation tc := Img.tc.

Definition IT_ENTRY : Z := 0x6da2c.
Definition IT_STOPS : list Z := [SC_ENTRY; SN_ENTRY].

Fixpoint cstrlen_img (fuel : nat) (a : Z) : Z :=
  match fuel with
  | O => 0
  | S f => match rom_rd SEGS a 1 with
           | Some [c] => if c =? 0 then 0 else 1 + cstrlen_img f (a + 1)
           | _ => 0
           end
  end.

Ltac lit_cstr A H :=
  let n := eval vm_compute in (cstrlen_img 300 A) in
  assert (H : ro_cstr SEGS L A n /\ n <= 256)
    by (apply (ro_cstr_of_chk SEGS L ti Img.rodata); [cbn; lia | cbn; lia | vm_compute; reflexivity]).

Definition calleeI : list reg := [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition keptI (R R' : bvmap 5 word) : Prop := forall r, In r calleeI -> getr R' r = getr R r.
Lemma keptI_trans : forall R1 R2 R3, keptI R1 R2 -> keptI R2 R3 -> keptI R1 R3.
Proof. intros R1 R2 R3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.
Lemma keptI_of_kept : forall R R', kept R R' -> keptI R R'.
Proof. intros R R' K r Hr. apply K. cbn in Hr |- *. intuition. Qed.
Lemma kept_assemble : forall R R', keptI R R' ->
  getr R' 1%bv = getr R 1%bv -> getr R' 2%bv = getr R 2%bv -> getr R' 8%bv = getr R 8%bv -> kept R R'.
Proof.
  intros R R' K H1 H2 H8 r Hr. cbn in Hr.
  repeat (destruct Hr as [<-|Hr]; [first [exact H1 | exact H2 | exact H8 | apply K; (first [solve [clear; cbn; tauto] | cbn; tauto])]|]). destruct Hr.
Qed.

Lemma adv : forall {fx : FPState} (s1 s2 : machine_state) (retw : word) (K : bvmap 5 word -> mem -> Z -> Prop),
  msteps SEGS s1 s2 ->
  (exists R' M' r, msteps SEGS s2 (@mkst fx R' retw M' (seg_rom SEGS)) /\ K R' M' r) ->
  (exists R' M' r, msteps SEGS s1 (@mkst fx R' retw M' (seg_rom SEGS)) /\ K R' M' r).
Proof.
  intros fx s1 s2 retw K MS (R' & M' & r & MS' & HK). exists R', M', r. split; [eapply msteps_trans; [exact MS | exact MS'] | exact HK].
Qed.

Section Walk.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.
  Variables (R : bvmap 5 word) (M M1 : mem) (p n sp : Z) (ret : word).
  Hypothesis HRO1 : ro_clear L M1.
  Hypothesis NM1 : name_ok M1 p n.
  Hypothesis Cra : cell8 SEGS M1 (sp - 8) (bv_unsigned (getr R 1%bv)).
  Hypothesis Cs0 : cell8 SEGS M1 (sp - 16) (bv_unsigned (getr R 8%bv)).
  Hypothesis Hsp : 2 ^ 20 <= sp < 2 ^ 47.
  Hypothesis Hp : 0 < p < 2 ^ 47.

  Lemma walk_know : forall Rk, getr Rk 8%bv = Z_to_bv 64 p -> getr Rk 2%bv = Z_to_bv 64 (sp - 16) ->
    let E := Eseed Rk [Z_to_bv 64 p; Z_to_bv 64 (sp - 16); getr R 1%bv; getr R 8%bv] in
    regs_ok E (srs sr_id [(8%bv, EVar 32); (2%bv, EVar 33)]) Rk /\
    know_ok SEGS E M1 [KWord (SA (EVar 33) 8) 8 (EVar 34); KWord (SA (EVar 33) 0) 8 (EVar 35); KImg (ti_ro_lo ti) (ti_ro_hi ti)].
  Proof using R M1 p sp HRO1 Cra Cs0 Hsp.
    intros Rk H8 H2 E. split.
    - apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption.
    - constructor; [|constructor; [|constructor; [|constructor]]].
      + eapply (kword_var _ E M1 33%N (sp - 16) 8 8); [replace (sp - 16 + 8) with (sp - 8) by lia; exact Cra | lia | evs; reflexivity | lia | lia | cbn; lia | evs; symmetry; apply Z_to_bv_bv_unsigned].
      + eapply (kword_var _ E M1 33%N (sp - 16) 0 8); [rewrite Z.add_0_r; exact Cs0 | lia | evs; reflexivity | lia | lia | cbn; lia | evs; symmetry; apply Z_to_bv_bv_unsigned].
      + apply (kimg_ro SEGS L E M1 _ _ HRO1 Img.rodata); cbn; lia.
  Qed.
End Walk.

Lemma keptI_of_syms : forall R vals sr R', regs_ok (Eseed R vals) sr R' -> syms_id sr calleeI = true -> keptI R R'.
Proof. intros R vals sr R' HR Hs r Hr. exact (syms_id_sound R vals sr R' calleeI HR Hs r Hr). Qed.

Ltac walk_fin HRO1 NM1 Cra Cs0 Hsp0 Hra Hret FR1 DF1 HRk KI :=
  idtac;
  lazymatch type of NM1 with name_ok _ ?p ?n =>
  lazymatch type of KI with keptI ?R _ =>
  lazymatch type of Cs0 with cell8 _ _ (?sp - 16) _ =>
  lazymatch goal with |- exists R' M' r, msteps _ (@mkst ?fx ?Rk (Z_to_bv 64 ?pc) ?M1 _) _ /\ _ =>
  let pcv := eval vm_compute in pc in
  let atcall := eval vm_compute in (orb (Z.eqb pcv SC_ENTRY) (Z.eqb pcv SN_ENTRY)) in
  lazymatch atcall with
  | false =>

      let A10 := fresh "A10" in let A1 := fresh "A1" in let A2 := fresh "A2" in let A8 := fresh "A8" in
      rreg HRk 10%bv A10; rreg HRk 1%bv A1; rreg HRk 2%bv A2; rreg HRk 8%bv A8;
      let closer := idtac;
        split; [ eapply ret_run; [vm_compute; reflexivity | rewrite A1; exact Hra | exact Hret] |];
        split; [ apply kept_assemble; [ eapply keptI_trans; [exact KI | eapply (keptI_of_syms _ _ _ _ HRk); reflexivity]
                                      | rewrite A1; reflexivity | rewrite A2, zbv_add, Hsp0; f_equal; lia | rewrite A8; reflexivity ] |];
        split; [ exact A10 |];
        split; [ lia |];
        split; [ exact FR1 | exact DF1 ] in
      lazymatch type of A10 with
      | _ = Z_to_bv 64 ?v =>
          exists Rk, M1, v; closer
      | _ = mul_div M_MUL (Z_to_bv 64 16) (alu64 ALU_SLTU ?a ?b) =>
          destruct (sltu_b2w a b) as [[|] Et]; rewrite Et in A10; unfold b2w in A10; rewrite zbv_mul in A10;
          [exists Rk, M1, 16; closer | exists Rk, M1, 0; closer]
      end
  | true =>
      let A10 := fresh "A10" in let A11 := fresh "A11" in let A12 := fresh "A12" in let A1 := fresh "A1" in
      let A8 := fresh "A8" in let A2 := fresh "A2" in
      rreg HRk 10%bv A10; rreg HRk 11%bv A11; rreg HRk 12%bv A12; rreg HRk 1%bv A1; rreg HRk 8%bv A8; rreg HRk 2%bv A2;
      rewrite ?zbv_add in A2;
      lazymatch type of A10 with _ = Z_to_bv 64 ?Alit =>
      lazymatch type of A1 with _ = Z_to_bv 64 ?RET =>
        let CS := fresh "CS" in lit_cstr Alit CS;
        let R2 := fresh "Rw" in let MS2 := fresh "MSw" in let K2 := fresh "Kw" in
        let iscmp := eval vm_compute in (Z.eqb pcv SC_ENTRY) in
        lazymatch iscmp with
        | true =>
            destruct (strcmp_lit M1 Alit _ p n HRO1 (proj1 CS) NM1 Rk (Z_to_bv 64 RET) A10 A11 A1
                        ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity)) as (R2 & MS2 & K2)
        | false =>
            lazymatch type of A12 with _ = Z_to_bv 64 ?kv =>
            destruct (strncmp_lit M1 Alit _ p n HRO1 (proj1 CS) NM1 Rk (Z_to_bv 64 RET) kv ltac:(lia) A10 A11 A12 A1
                        ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity)) as (R2 & MS2 & K2)
            end
        end;
        eapply adv; [exact MS2|];
        let KI2 := fresh "KI" in
        assert (KI2 : keptI R R2) by (eapply keptI_trans; [exact KI | eapply keptI_trans; [eapply (keptI_of_syms _ _ _ _ HRk); reflexivity | apply keptI_of_kept; exact K2]]);
        let S0 := fresh "S0" in let SP := fresh "SP" in
        assert (S0 : getr R2 8%bv = Z_to_bv 64 p) by (rewrite <- A8; apply K2; (first [solve [clear; cbn; tauto] | cbn; tauto]));
        assert (SP : getr R2 2%bv = Z_to_bv 64 (sp - 16)) by (rewrite (K2 2%bv ltac:(first [solve [clear; cbn; tauto] | cbn; tauto])); rewrite A2; f_equal; lia);
        clear MS2 A10 A11 A12 A1 A8 A2 CS HRk KI K2;
        let HR2 := fresh "HRw" in let HK2 := fresh "HKw" in
        lazymatch goal with Hsp2 : 2 ^ 20 <= sp < 2 ^ 47 |- _ =>
        destruct (walk_know R M1 p sp HRO1 Cra Cs0 Hsp2 R2 S0 SP) as [HR2 HK2] end;
        xtree HR2 HK2 40%nat IT_STOPS 40%N (@nil bool) (@nil expr) ltac:(try sc_auto1)
          ltac:(idtac;
                match goal with Hl : log_flat _ _ |- _ => clear Hl end;
                lazymatch goal with Hmsn : msteps _ (@mkst _ R2 _ _ _) (@mkst _ ?Rn _ _ _) |- _ =>
                lazymatch goal with HRn : regs_ok _ _ Rn |- _ =>
                  eapply adv; [exact Hmsn|]; clear Hmsn;
                  walk_fin HRO1 NM1 Cra Cs0 Hsp0 Hra Hret FR1 DF1 HRn KI2
                end end)
          ltac:(br_kill)
      end end
  end end end end end
with walk_dummy := idtac.

Theorem import_type_get_spec {AC : AllocCeiling} : forall MI : MallocIface SEGS L, import_type_get_stmt SEGS L MI tc.
Proof.
  intros MI fx A R M model p n sp ret AI HRO Ha0 Hsp Hp0 Hpn Hn Hdef Hbytes Hnul Hpl Hdisj Hroom Hce Hsp47 Hsp16 Hra Hret.
  pose proof ac_bounds_lit as HAC. cbn [tc_import_stack Img.tc] in *.
  change (tc_import_type_get tc) with IT_ENTRY.

  pose (E := Eseed R [Z_to_bv 64 sp; Z_to_bv 64 p]).
  assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33)]) R).
  { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
  assert (HK : know_ok SEGS E M [KWr (SA (EVar 32) (-16)) (ELit 16); KAlign (EVar 32) 16]).
  { constructor; [|constructor; [|constructor]].
    - eapply (kwr_stack_sub _ E M 32%N sp 64 16); [evs; reflexivity | reflexivity | lia | lia | lia | exact Hroom].
    - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hsp16]. }
  xrun HR HK 30%nat IT_STOPS (SCR [] [] []) 40%N. { split_scs; try sc_auto1. }
  match type of Hms with msteps _ _ (mkst _ _ ?M1' _) => set (M1 := M1') in Hms end.

  assert (EM1 : M1 = wbytes (wbytes M (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 (getr R 1%bv))) (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 (getr R 8%bv))).
  { subst M1. evs. rewrite !v_addi_Z by lia. reflexivity. }
  clearbody M1. subst M1.
  set (M1 := wbytes (wbytes M (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 (getr R 1%bv))) (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 (getr R 8%bv))) in *.
  assert (FR1 : frame_eq (fun a => zwin (sp - 64) sp a) M M1).
  { subst M1. intros a Ha. unfold zwin in Ha. pose proof (bv_unsigned_in_range _ a) as Xa. unfold bv_modulus in Xa. change (2 ^ Z.of_N 64) with (2 ^ 64) in Xa.
    rewrite (MemSplit.wbytes_outside _ _ _ a). 2,3: rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; lia.
    rewrite (MemSplit.wbytes_outside _ _ _ a). 2,3: rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; lia.
    reflexivity. }
  assert (DF1 : forall a : word, M a <> None -> M1 a <> None).
  { subst M1. intros a Ha. apply defined_wbytes8; [lia|lia|]. apply defined_wbytes8; [lia|lia|exact Ha]. }
  assert (HRO1 : ro_clear L M1).
  { eapply ro_clear_frame; [exact HRO | exact FR1 |]. intros a [Hi _] Hw. unfold zwin in Hw.
    destruct Hi as (lo & hi & Hin & Hr). cbn in Hin. destruct Hin as [E0|[]]. injection E0 as <- <-. lia. }
  assert (NM1 : name_ok M1 p n).
  { split; [lia|]. split; [lia|]. split; [lia|]. split.
    - intros i Hi. destruct (Hbytes i Hi) as (c & Hc & F). exists c. split; [exact Hc|].
      eapply fld_agree; [lia | cbn; lia | exact F |]. eapply agree_on_of_frame_eq; [exact FR1|].
      intros a Ha. unfold zwin in Ha. cbn in Ha. split; [lia|]. intros W. exact (Hdisj a ltac:(unfold zwin; lia) W).
    - eapply fld_agree; [lia | cbn; lia | exact Hnul |]. eapply agree_on_of_frame_eq; [exact FR1|].
      intros a Ha. unfold zwin in Ha. cbn in Ha. split; [lia|]. intros W. exact (Hdisj a ltac:(unfold zwin; lia) W). }
  assert (C8 : cell8 SEGS M1 (sp - 8) (bv_unsigned (getr R 1%bv)) /\ cell8 SEGS M1 (sp - 16) (bv_unsigned (getr R 8%bv))).
  { subst M1. pose proof (bv_unsigned_in_range _ (getr R 1%bv)) as X1. pose proof (bv_unsigned_in_range _ (getr R 8%bv)) as X8.
    unfold bv_modulus in X1, X8. change (2 ^ Z.of_N 64) with (2 ^ 64) in X1, X8. split.
    - split; [cbn; lia|]. unfold CRep.fld.
      rewrite CatExec.rdn_wbytes_out. 2,3,4: rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; cbn; lia.
      rewrite Z_to_bv_bv_unsigned. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia.
    - split; [cbn; lia|]. unfold CRep.fld. rewrite Z_to_bv_bv_unsigned. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
  destruct C8 as [Cra Cs0].

  assert (KI1 : keptI R R) by (intros r _; reflexivity).
  assert (Hp : 0 < p < 2 ^ 47) by lia. assert (Hsp2 : 2 ^ 20 <= sp < 2 ^ 47) by lia.
  rename HR' into HR1. rename R' into R1. clear Hlf.
  eapply adv; [exact Hms|]. clear Hms.
  walk_fin HRO1 NM1 Cra Cs0 Hsp Hra Hret FR1 DF1 HR1 KI1.
Qed.
