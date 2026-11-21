(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: made from Drv/S1CxxLink.v for the budget-premise witness: the same proofs over BudgetWit.SRealizes.srealizes, the released srealizes with a no-allocation-call check at each node; only module paths change. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the consumer lemmas restated on the run's whole input, with their proofs written out in place of recorded proofs). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import Overlay RunsLib S1BootDefs S1Boot S1StartInit_defs S1CxxTable.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.BudgetWit.Drv Require Import S1Start.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.BudgetWit Require KReplayB.
Ltac2 kr_t_S1CxxLink () := "C59OSSVerify5KrLib3Drv7RunsLib;runs_equivFC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib3Drv7RunsLib:runs_equivC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7RunsLib>runs_equivF_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indI47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib3Drv@S1StartInit_defs9init_runsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:S1CxxTable5D_CXXC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib3Drv7Overlay7runs_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Drv6S1Boot2D8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7RunsLib@runs_equiv_soundC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib9BudgetWit3Drv7S1Start7D_main1C15~~~~~C59OSSVerify5KrLib3Drv7Overlay:apply_runsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00c69OSSVerify5KrLib9BudgetWit3Drv9S1CxxLink<init_runs_okC15~~~~~c69OSSVerify5KrLib9BudgetWit3Drv9S1CxxLink8D_CXX_okC15~~~~~c69OSSVerify5KrLib9BudgetWit3Drv9S1CxxLink;d_cxx_equivC15~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C59OSSVerify5KrLib3Drv7Overlay;lookup_byteC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Drv7RunsLib?apply_runs_pinsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib9BudgetWit3Drv9S1CxxLink=D_main1_tableC15~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib3Drv7RunsLib4pinsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib3Drv7RunsLib:runs_clearC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=Z_to_bv_smallC49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7RunsLibDrdn_apply_runs_clearC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib3Drv7RunsLibCapply_runs_clear_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7Overlay;lookup_runsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib9BudgetWit3Drv9S1CxxLink<D_main1_pinsC15~~~~~C59OSSVerify5KrLib3Drv7RunsLib;rdn_of_pinsC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma d_cxx_equiv : runs_equiv init_runs D_CXX = true.
Proof.
ltac2:(KReplayB.run1 (kr_t_S1CxxLink ()) [] "h01bp;2p;3p;6g0000j25Tg000lj30Tg001Fj22Tg001`j21Tg002[j24Tg003Zj63Tg0046R0g004VR1g005YR2'5R3f0g006RR4500X001204A0034d11121412E3o"). Qed.

Lemma init_runs_ok : runs_ok init_runs = true.
Proof.
ltac2:(KReplayB.run1 (kr_t_S1CxxLink ()) [] "p;2p;1p;3g001Fj22Tg0072j11Tg000lj30Tg0046R0g006RR1'2g004V#1=001do"). Qed.

Lemma D_CXX_ok : runs_ok D_CXX = true.
Proof.
ltac2:(KReplayB.run1 (kr_t_S1CxxLink ()) [] "p;2p;1p;3g001Fj22Tg0072j11Tg000lj30Tg0046R0g006RR1'2g005Y#1=001do"). Qed.

(* LPS 75d69e00 (revision #38) folded [av]/[ev]/[hw] into the single [ProcInput].
   [S1Start.D_main1] and [S1Boot.D8] now read [inp sp0 tid rdraw], so the five
   consumer lemmas below are restated on [inp] and their proofs are written out
   in full against the generic [Drv/RunsLib] facts.  They are the same facts as
   before: with [inp] carrying [in_argv]/[in_envp]/[in_hwcap], the old
   three-binder form is no longer expressible, and nothing here is weakened. *)

Lemma cxx_u_small64 : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

Lemma D_main1_table : forall (inp : ProcInput) (sp0 tid : word) (rdraw : EntryDraw) (a : word),
  D_main1 inp sp0 tid rdraw a = apply_runs D_CXX (D8 inp sp0 tid rdraw) a.
Proof.
  intros inp sp0 tid rdraw a. unfold D_main1.
  apply runs_equiv_sound; [exact init_runs_ok | exact D_CXX_ok | exact d_cxx_equiv].
Qed.

Lemma D_main1_pins : forall (inp : ProcInput) (sp0 tid : word) (rdraw : EntryDraw),
  pins D_CXX (D_main1 inp sp0 tid rdraw).
Proof.
  intros inp sp0 tid rdraw.
  pose proof (apply_runs_pins D_CXX (D8 inp sp0 tid rdraw) D_CXX_ok) as HP.
  unfold pins in *. intros y b Hy Hl. rewrite D_main1_table. apply HP; assumption.
Qed.

Lemma D_main1_clear : forall segs (inp : ProcInput) (sp0 tid : word) (rdraw : EntryDraw) lo n,
  runs_clear D_CXX lo n = true -> 0 <= lo < 2 ^ 64 -> lo + Z.of_nat n <= 2 ^ 64 ->
  rdn segs (D_main1 inp sp0 tid rdraw) (Z_to_bv 64 lo) n = rdn segs (D8 inp sp0 tid rdraw) (Z_to_bv 64 lo) n.
Proof.
  intros segs inp sp0 tid rdraw lo n Hc Hlo Hhi.
  transitivity (rdn segs (apply_runs D_CXX (D8 inp sp0 tid rdraw)) (Z_to_bv 64 lo) n).
  - apply rdn_ext; [rewrite cxx_u_small64 by lia; lia|].
    intros x _. apply D_main1_table.
  - apply rdn_apply_runs_clear; [exact D_CXX_ok | exact Hc | exact Hlo | exact Hhi].
Qed.

Lemma D_main1_clear_at : forall (inp : ProcInput) (sp0 tid : word) (rdraw : EntryDraw) lo n (x : Z),
  runs_clear D_CXX lo n = true -> 0 <= x < 2 ^ 64 -> lo <= x < lo + Z.of_nat n ->
  D_main1 inp sp0 tid rdraw (Z_to_bv 64 x) = D8 inp sp0 tid rdraw (Z_to_bv 64 x).
Proof.
  intros inp sp0 tid rdraw lo n x Hc Hx Hr. rewrite D_main1_table.
  exact (apply_runs_clear_at D_CXX (D8 inp sp0 tid rdraw) lo n x D_CXX_ok Hc Hx Hr).
Qed.

Lemma D_main1_hit : forall segs (inp : ProcInput) (sp0 tid : word) (rdraw : EntryDraw) (x : Z) n zs,
  0 <= x -> x + Z.of_nat n <= 2 ^ 64 -> lookup_runs D_CXX x n = Some zs ->
  rdn segs (D_main1 inp sp0 tid rdraw) (Z_to_bv 64 x) n = Some (map (Z_to_bv 8) zs).
Proof.
  intros segs inp sp0 tid rdraw x n zs Hx Hn HL.
  exact (rdn_of_pins segs D_CXX (D_main1 inp sp0 tid rdraw) n x zs
           (D_main1_pins inp sp0 tid rdraw) Hx Hn HL).
Qed.
