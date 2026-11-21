(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed SL_nodup, byte_hit_sound, byte_zero_sound and 6 more; taken in part from projects/jsoncons/fuzz_bson_parser_max/proofs/lib/SegRunStrlen.v at theorem-labs/oss-verify-proofs@f92feaf8b7e6, 165 lines within its lines 29-274. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AsanPlanSound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode.
Module SumsSpecLib.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemsetLib.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AsanPlanSound. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AsanPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSound.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.AsanPlanSoundSums.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kept_ok_of_regs_agree : forall (clob : list reg) regs regs',
  (forall r, In r clob -> In (AX2.ridx r) AP.caller_saved) ->
  regs_agree (fun r => In r clob) regs regs' -> APSX.kept_ok regs regs'.
Proof. intros clob regs regs' Hsub Hag r Hr0 Hnin. apply Hag. intros Hin. apply Hnin. apply Hsub. exact Hin. Qed.

Ltac in_list := cbn [In]; repeat (first [left; (reflexivity || (apply bv_eq; reflexivity)) | right]).

Ltac clob_sub :=
  let r := fresh "r" in let H := fresh "H" in
  intros r H; cbn [In] in H;
  repeat (destruct H as [<-|H]; [in_list|]); destruct H.

Lemma ms_clob_sub : forall r, In r ms_clob -> In (AX2.ridx r) AP.caller_saved.
Proof. unfold ms_clob. clob_sub. Qed.

(* [comment removed for export] *)
Lemma kept_ok_of_keeps : forall regs regs', keeps regs regs' -> APSX.kept_ok regs regs'.
Proof.
  intros regs regs' Hk r Hr0 Hnin. apply Hk.
  pose proof (AX2S.ridx_range r) as Hrr.
  assert (Hr : AX2.ridx r <> 0%nat).
  { intros X. apply Hr0. rewrite (APSX.reg_of_ridx r 0 X). apply bv_eq. reflexivity. }
  unfold AP.caller_saved in Hnin. cbn [In] in Hnin.
  assert (E : exists k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat /\ AX2.ridx r = k).
  { exists (AX2.ridx r). split; [|reflexivity]. cbn [In]. lia. }
  destruct E as (k & Hink & Hrk). rewrite (APSX.reg_of_ridx r k Hrk).
  cbn [In] in Hink. unfold callee_kept.
  repeat (destruct Hink as [<-|Hink]; [in_list|]). destruct Hink.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Derive.
Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable SEGS : list Segment.

(* [comment removed for export] *)
Lemma fill_spec_of_memset : forall (entry : Z),
  (forall mem0 (d cv ret : word) (n : Z) rom,
    (0 <= n)%Z -> (bv_unsigned d + n < 2 ^ 64)%Z ->
    store_ok SEGS mem0 d (Z.to_nat n) = true -> ret_ok ret ->
    forall regs, getr regs 10%bv = d -> getr regs 11%bv = cv -> getr regs 12%bv = Z_to_bv 64 n -> getr regs 1%bv = ret ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 rom)
                  (mkst regs' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
      /\ getr regs' 10%bv = d /\ ms_agree regs regs') ->
  APSX.fill_spec SEGS entry AX2.two64.
Proof.
  intros entry SUM mem0 s c n regs ret Hn Hnw Hst Hc Hret R1 R10 R11 R12.
  destruct (SUM mem0 s c ret n (seg_rom SEGS) Hn Hnw Hst Hret regs R10 R11 R12 R1) as (regs' & Hms & H10 & Hag).
  exists regs'. split; [exact Hms|]. split; [|exact H10].
  eapply kept_ok_of_regs_agree; [apply ms_clob_sub | exact Hag].
Qed.
End Derive.


End SumsSpecLib.
From Stdlib Require ZArith NArith List Lia Bool Znumtheory. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module SegRunStrlen.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AsanPlanSound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.FPSteps OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AsanPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.AsanPlanSoundSums OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_SegRunStrlen () := "C47Corelib7Program6Basics4flipC46Stdlib5Lists4List2InK47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic3notK46Stdlib5Lists4List5NoDup01I46Stdlib5Lists4List5NoDup00C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib5Lists4List5NoDup02I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01c69OSSVerify5KrLib7Mh_0137<SegRunStrlen3SRS2SLC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC:sr_vars_ltC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib=AsanPlanSound3APS8ext_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS>ext_list_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS=sr_vars_lt_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Peano2ltK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?nth_sr_vars_lt'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS=edenot_agree'C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26sr_updC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S:ridx_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24ridxC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib5Arith8PeanoNat3Nat8eqb_specI47Corelib4Init9Datatypes7reflect00C69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX;reg_of_ridxC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6in_decI47Corelib4Init6Specif7sumbool00C46Stdlib5Lists4List6In_nthC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib5Lists7ListDef3nthC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib4Init3Nat3addK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib=AsanPlanSound3APS;ext_list_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8sr_freshC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?nth_sr_fresh_inC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedC46Stdlib9micromega;ZifyClasses9not_morphK46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26sr_getC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX@nth_sr_fresh_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S:nth_sr_updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXAregs_ok_pointwiseC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC8sr_freshC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init5Logic2or01K47Corelib4Init5Logic4True01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqI69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eq_decc69OSSVerify5KrLib7Mh_0137<SegRunStrlen3SRS8SL_nodupC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib7Numbers7BinNums1N00K47Corelib4Init9Datatypes4bool02C46Stdlib5Lists4List2hdC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z:shiftl_0_lC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2;know_lookupC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24lres01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C59OSSVerify5KrLib?AxSymExec3Sound4AX2SAknow_lookup_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9scs_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C56Stdlib6ZArith6BinInt1Z3powc69OSSVerify5KrLib7Mh_0137<SegRunStrlen3SRS5lez_1C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC49OSSVerify5KrLib8PropExec8u8_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S4extzC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leI69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24lres00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28sidecond00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C69OSSVerify5KrLib7Mh_01306SegRun2SR=bytes_nonzeroC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z6eq_decC56Stdlib6ZArith6BinInt1Z7add_0_rc69OSSVerify5KrLib7Mh_0137<SegRunStrlen3SRS>byte_hit_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideC56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z<divide_transC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24lres02C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indI4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24lres03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR9byte_zeroC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC69OSSVerify5KrLib7Mh_01306SegRun2SR>words_readableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2;kn_readableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2SAkn_readable_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR:ro_coveredC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List>existsb_existsC56Stdlib6ZArith6BinInt1Z3lebK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry09C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S3rd1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26a_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25a_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S6estartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR;strlen_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR6closedC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_01306SegRun2SR;step_strlenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR3INVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR4wdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26s_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR9STEP_POSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26s_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR:wl_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25s_logC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR<closed_partsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24s_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ret_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR3regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29split_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28facts_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23xhiC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29sym_state01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01306SegRun2SR=some_pair_injC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26ealignC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC59OSSVerify5KrLib?AxSymExec3Sound4AX2S;facts_of_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR;reg_sound10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9xhi_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXAw_split_lit_denotC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01126LibSym8u64_of_ZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX>w_flat_x_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S<ealign_soundC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z9pow_add_rC46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z9mul_assocC56Stdlib6ZArith6BinInt1Z7mod_modC56Stdlib6ZArith6BinInt1Z7add_0_lC56Stdlib6ZArith6BinInt1Z7add_modC56Stdlib6ZArith6BinInt1Z9add_assocc69OSSVerify5KrLib7Mh_0137<SegRunStrlen3SRS:estart_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX9adenot_SAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lt_totalc69OSSVerify5KrLib7Mh_0137<SegRunStrlen3SRS9flat_byteC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0137<SegRunStrlen3SRSCbytes_nonzero_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0137<SegRunStrlen3SRS?byte_zero_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0137<SegRunStrlen3SRSDwords_readable_soundC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injc69OSSVerify5KrLib7Mh_0137<SegRunStrlen3SRS8rdn1_rd1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S;rdn_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX7rdn_nthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idC69OSSVerify5KrLib7Mh_01306SegRun2SR=ret_lit_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith4Znat5Nat2Z2idc69OSSVerify5KrLib7Mh_0137<SegRunStrlen3SRS@ro_covered_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR:wden_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0137<SegRunStrlen3SRSAregs_after_strlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS>know_ok_agree'C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR@strlen_step_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC6flat_xC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29sym_state00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25two64C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR4went00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26sentry00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_Z".
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module SRS.
Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SL : list nat := [11; 12; 13; 14; 15; 16]%nat.

Lemma SL_nodup : List.NoDup SL.
Proof.
  unfold SL. repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H|]). apply List.NoDup_nil.
Qed.

Lemma regs_after_strlen : forall E sr R R' nx (kz : Z),
  regs_ok E sr R -> APC.sr_vars_lt nx sr = true ->
  (forall r : bv 5, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv ->
     getr R' r = getr R r) ->
  getr R' 10%bv = Z_to_bv 64 kz ->
  regs_ok (APS.ext_list E nx (map (fun r => getr R' (Z_to_bv 5 (Z.of_nat r))) SL))
          (sr_upd (APC.sr_fresh sr SL nx) 10 (ELit kz)) R'.
Proof.
  intros E sr R R' nx kz HR Hsv Hkept Ha0.
  set (E' := APS.ext_list E nx (map (fun r => getr R' (Z_to_bv 5 (Z.of_nat r))) SL)).
  pose proof (APS.ext_list_agree E nx (map (fun r => getr R' (Z_to_bv 5 (Z.of_nat r))) SL)) as Hag. fold E' in Hag.
  rewrite APS.sr_vars_lt_eq in Hsv.
  assert (OLD : forall i, (i < 32)%nat -> edenot E' (nth i sr (ELit 0)) = edenot E (nth i sr (ELit 0))).
  { intros i Hi. symmetry. apply (APS.edenot_agree' nx); [exact Hag|]. apply APSX.nth_sr_vars_lt'; assumption. }
  apply APSX.regs_ok_pointwise. intros r Hr0.
  pose proof (ridx_range r) as Hrr.
  rewrite nth_sr_upd.
  destruct (Nat.eqb_spec (ridx r) 10) as [H10|H10].
  { rewrite (APSX.reg_of_ridx r 10 H10). cbn [edenot]. exact Ha0. }
  destruct (in_dec Nat.eq_dec (ridx r) SL) as [Hin|Hnin].
  - destruct (In_nth SL (ridx r) 0%nat Hin) as (j & Hj & Hnth).
    rewrite <- Hnth at 1. rewrite APSX.nth_sr_fresh_in by (apply SL_nodup || exact Hj).
    cbn [edenot]. unfold E'. rewrite APS.ext_list_at by (rewrite length_map; exact Hj).
    rewrite (map_nth (fun r0 => getr R' (Z_to_bv 5 (Z.of_nat r0))) SL 0%nat j) || idtac.
    replace (nth j (map (fun r0 : nat => getr R' (Z_to_bv 5 (Z.of_nat r0))) SL) (Z_to_bv 64 0))
      with (getr R' (Z_to_bv 5 (Z.of_nat (nth j SL 0%nat)))).
    2:{ clear - Hj. unfold SL in *. cbn [length] in Hj.
        do 6 (destruct j as [|j]; [reflexivity|]). lia. }
    rewrite Hnth. rewrite <- (APSX.reg_of_ridx r _ eq_refl). reflexivity.
  - rewrite APSX.nth_sr_fresh_out by exact Hnin. rewrite OLD by exact Hrr.
    assert (NE : forall n, In n (10%nat :: SL) -> r <> Z_to_bv 5 (Z.of_nat n)).
    { intros n Hn X. subst r. unfold SL in Hn. cbn [In] in Hn.
      assert (RX : forall m, (m < 32)%nat -> ridx (Z_to_bv 5 (Z.of_nat m)) = m).
      { intros m Hm. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
        rewrite Z.mod_small by lia. lia. }
      repeat (destruct Hn as [<-|Hn]; [rewrite RX in * by lia; apply Hnin || apply H10; cbn; auto 10; fail|]).
      exact Hn. }
    rewrite (Hkept r); try (intros X; subst r; first [apply H10; reflexivity | apply Hnin; cbn; tauto]).
    pose proof (HR r) as X. unfold sr_get in X.
    destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
    exact X.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lez_1 : forall b : byte, bytes_le_to_Z [b] = bv_unsigned b.
Proof.
ltac2:(KReplay.run1 (kr_t_SegRunStrlen ()) ["WithSegs"] "h01zh11bp;1p;2p;3p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p101W[p4p710p8g003Cj10Tg00Icj1>Tg00JAj18Tg01@dj23Tg01X2j24Tg004Fj31Tg00:Vj2;Tg01XOj17Tg00aHj62Tg003hj16Tg01Y0j25Tg01YPj19Tg001Dj1:Tg001dj3=Tg01Z4j1<Tg00F4#0#0#0R0#>R1#8R2g00B4R3g00HER4f1,31R5f0R6'4=135X03P31316R1A1365X031;311414%71E2%60R0,54%90E2%:29=26#<=131eW1o"). Qed.

(* [comment removed for export] *)
Lemma byte_hit_sound : forall E m k sb off z h,
  know_ok segs E m k ->
  know_lookup segs k sb off 1 false [] [] = LHit (ELit z) [] h ->
  flat E (SA sb off) 1 ->
  exists b, rdn segs m (adenot E (SA sb off)) 1 = Some [b] /\ bv_unsigned b = z mod 2 ^ 64.
Proof.
  intros E m k sb off z h HK HL Hfl.
  pose proof (know_lookup_sound segs E m k sb off 1 false [] [] HK ltac:(lia) ltac:(lia)) as X.
  rewrite HL in X. destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
  destruct bs as [|b [|]]; try discriminate. exists b. split; [exact Hrd|].
  unfold extz in Hv. rewrite lez_1 in Hv. cbn [edenot] in Hv.
  apply (f_equal bv_unsigned) in Hv. rewrite !Z_to_bv_unsigned in Hv. unfold bv_wrap in Hv.
  change (bv_modulus 64) with (2 ^ 64) in Hv. pose proof (u8_range b).
  rewrite Z.mod_small in Hv by lia. exact Hv.
Qed.

Lemma bytes_nonzero_sound : forall E m fk k sb nb off,
  know_ok segs E m k ->
  SR.bytes_nonzero segs fk k sb off nb = true ->
  (forall i, 0 <= i < Z.of_nat nb -> flat E (SA sb (off + i)) 1) ->
  forall i, 0 <= i < Z.of_nat nb ->
    exists b, rdn segs m (adenot E (SA sb (off + i))) 1 = Some [b] /\ bv_unsigned b <> 0.
Proof.
  intros E m fk k sb nb. induction nb as [|nb IH]; intros off HK H Hfl i Hi; [lia|].
  cbn [SR.bytes_nonzero] in H.
  destruct (know_lookup segs k sb off 1 false [] []) as [v scs h| | ] eqn:HL; try discriminate.
  destruct v as [z| | | | | | |]; try discriminate. destruct scs; [|discriminate].
  apply andb_true_iff in H as [Hz Hrest]. apply negb_true_iff in Hz. apply Z.eqb_neq in Hz.
  destruct (Z.eq_dec i 0) as [->|Hi0].
  - rewrite Z.add_0_r. destruct (byte_hit_sound E m k sb off z h HK HL) as (b & Hrd & Hb).
    { specialize (Hfl 0 ltac:(lia)). rewrite Z.add_0_r in Hfl. exact Hfl. }
    exists b. split; [exact Hrd|]. rewrite Hb. intros X. apply Hz.
    apply (proj2 (Z.mod_divide z 256 ltac:(lia))). apply (Z.divide_trans _ (2 ^ 64)); [exists (2 ^ 56); reflexivity|].
    apply (proj1 (Z.mod_divide z (2 ^ 64) ltac:(lia))). exact X.
  - destruct (IH (off + 1) HK Hrest) with (i := i - 1) as (b & Hrd & Hb).
    + intros i' Hi'. replace (off + 1 + i') with (off + (1 + i')) by lia. apply Hfl. lia.
    + lia.
    + exists b. replace (off + i) with (off + 1 + (i - 1)) by lia. split; assumption.
Qed.

Lemma byte_zero_sound : forall E m k sb off,
  know_ok segs E m k -> SR.byte_zero segs k sb off = true -> flat E (SA sb off) 1 ->
  exists b, rdn segs m (adenot E (SA sb off)) 1 = Some [b] /\ bv_unsigned b = 0.
Proof.
  intros E m k sb off HK H Hfl. unfold SR.byte_zero in H.
  destruct (know_lookup segs k sb off 1 false [] []) as [v scs h| | ] eqn:HL; try discriminate.
  destruct v as [z| | | | | | |]; try discriminate. destruct scs; [|discriminate]. apply Z.eqb_eq in H.
  destruct (byte_hit_sound E m k sb off z h HK HL Hfl) as (b & Hrd & Hb).
  exists b. split; [exact Hrd|]. pose proof (u8_range b).
  rewrite <- (Z.mod_small (bv_unsigned b) 256) by lia. rewrite Hb.
  rewrite Z.mod_mod_divide; [exact H|]. exists (2 ^ 56). reflexivity.
Qed.

Lemma words_readable_sound : forall E m fk k sb nb off,
  know_ok segs E m fk -> know_ok segs E m k ->
  SR.words_readable segs fk k sb off nb = true ->
  forall i, 0 <= i < Z.of_nat nb ->
    flat E (SA sb (off + i)) 1 /\ exists b, rdn segs m (adenot E (SA sb (off + i))) 1 = Some [b].
Proof.
  intros E m fk k sb nb. induction nb as [|nb IH]; intros off HKf HK H i Hi; [lia|].
  cbn [SR.words_readable] in H. apply andb_true_iff in H as [H1 Hrest].
  destruct (Z.eq_dec i 0) as [->|Hi0].
  - rewrite Z.add_0_r.
    destruct (kn_readable_sound segs E m fk m k sb off 1 HKf HK ltac:(lia) ltac:(lia) H1) as (Hfl & bs & Hrd & Hlen).
    split; [exact Hfl|]. destruct bs as [|b [|]]; try discriminate. exists b. exact Hrd.
  - destruct (IH (off + 1) HKf HK Hrest (i - 1) ltac:(lia)) as (Hfl & b & Hrd).
    replace (off + i) with (off + 1 + (i - 1)) by lia. split; [exact Hfl | exists b; exact Hrd].
Qed.

Lemma ro_covered_sound : forall E m k ro_lo ro_hi,
  know_ok segs E m k -> SR.ro_covered ro_lo ro_hi k = true ->
  forall i, ro_lo <= i < ro_hi -> m (Z_to_bv 64 i) = None.
Proof.
  intros E m k ro_lo ro_hi HK H i Hi. unfold SR.ro_covered in H.
  apply existsb_exists in H as (K & Hin & HKc).
  destruct K; try discriminate. apply andb_true_iff in HKc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as Hok. cbn [kentry_ok] in Hok.
  destruct Hok as (_ & _ & Hnone). apply Hnone. lia.
Qed.

Lemma rdn1_rd1 : forall m (a : word) b, rdn segs m a 1 = Some [b] -> rd1 segs m a <> None.
Proof.
  intros m a b H. unfold rd1. cbn [rdn] in H.
  destruct (m a) as [x|]; [discriminate|]. destruct (seg_rom segs a); discriminate.
Qed.

Lemma flat_byte : forall E sb sk n i, flat E (SA sb sk) n -> 0 <= i < n -> flat E (SA sb (sk + i)) 1.
Proof.
ltac2:(KReplay.run1 (kr_t_SegRunStrlen ()) ["WithSegs"] "h02Hah14__p1h24__p2h34__x1h44__x2h54__x3h64__x4h71Eh82Hfh92Hih:7__arithh;4__ffh<6__sat0h=6__sat1h>8__varmaph?5__with@1ihA1nhB2sbhC2skp;2p;3p;1p;4p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p101W[p4p710p8g01^]j2ITg01_`j3HTg00oUj24Tg00c\j20Tg003Cj17Tg003hj1@Tg01i@j2VTg01fMj2RTg01ihj3PTg000ej1:Tg01:Nj29Tg01;7j3;Tg01;`j2JTg001Dj1aTg001dj3ATg006gj1[Tg0113j2FTg007Gj1YTg01>4j4DTg007ej1XTg008Cj1WTg00>cj2?Tg002^j1UTg011Qj2<Tg00?Fj4>Tg008nj1OTg01MGj38Tg00Icj1NTg01k=j3MTg00:4j2LTg00:Vj2QTg00;0j2KTg004Fj3STg00;\j3TTg00<;j4bTg0101j22Tg01:2j2=Tg00W3j2GTg01@dj2ETg02_0j1`Tg02`2j1_Tg00@1j7^Tg01Mjj7\Tg009Pj6ZTg00@Uj8]Tg00HER0f0R1'=p=1g00B4R2f1R3g01QLP1C>p=6P3g00BRR4g00C1R5P5g00CQR6P1g00DXF^p=3f2R7P4P5P5P6P3P1F\p=5P3P4P5P5P6P1EZp=Bf3R8P4P5P5P6P7P3P1G]p=Cg01SGg01ODf4R41I87;H3%131437'0g00F4R9#7R:#@R;%7:R<#7#7#7#7R=#@R>'V140;%1>1R;>R?,40[[%1;R@g0222RAAP;>3UW0%1?\A^0@p-0R@g00FYRAg00E8R>#:RB#:RC#:RD#:,92192C192>R>5;25;2g01V1RC'J192D192B=;2>5;2/JCRC%aA9AAC5AA3A%[AP2P21F24P7%Y2CDP31F28CD%X2%W2RA1?20RC%U9,<2R>'6,3AP2P>g01R3RB1<2<R<C>,3A55A%O5R5PA1<29RD1<2:R:582RE,6C,3Af6RF,BAf7RG,BAA82E<1?2;%N=R=5M2R;'6,3A55A55A55AP5A82:>982DRD,6C,3AP2PDPBP;C>,3A%@9R9,?2RB,6C,3AA82DB/6;,3A55A55A55ACCCC1LA6P1P7g00GERAg00GeR6'Q1K17=SA6dAT203Cbb;b>b?X32X42X52X62X1@W2%171478'01237R3#1f5R01234/=?,0F'0'01284,27R3#1143?%19R61239/=?'0'0'0[[^32^42^52^62^1@^2@P1%1Ff9f8'G,E=R1/2G/4?PFP0PGP1P8P4O8b:b<b=1247,I0R0#`,GF,E=%_0'2R=#114=?12=9/=?,06'0'0eAHF09eW9W8X@2XA2XC2WBW7o"). Qed.

Lemma estart_off : forall E sb sk i, estart E (SA sb (sk + i)) = estart E (SA sb sk) + i.
Proof.
ltac2:(KReplay.run1 (kr_t_SegRunStrlen ()) ["WithSegs"] "h04__x1h14__x2h24__x3h31Eh47__arithh54__ffh68__varmaph75__with81ih92sbh:2skp;1p;2p;4p;3p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p101W[p4p710p8g001Dj1ITg006gj1HTg0113j28Tg01>4j4?Tg007ej1GTg008Cj1DTg011Qj25Tg003Cj11Tg002^j1@Tg01MGj32Tg00?Fj4>Tg00@1j7=Tg00:4j2<Tg00:Vj2FTg00;0j2ETg004Fj33Tg00;\j3CTg00<;j4BTg0101j20Tg00Icj1ATg00W3j24Tg01@dj26Tg01^]j29Tg02_0j1:Tg02`2j17Tg02a3j2;Tg01SGg01ODg00B4R0g00FYR1#I%H1P0f2R1,80f1R2f3R3,80C?%G0%D0R4g00BRg00C1R5P5g00CQR5P0g00F4R6,50R7%16R8,50R9%@6,50R6520520g00D1A2079=206C>g00DXF=1<45f0R5P1g00GER4g00GeR6'F1E51=346dg00HE=C02CBb5b6b7X00X10X201021,051052/01530^00^10^20P5P2P1%18#1#1#1#1#AR8f4/43'6O3b41025,91R6#:,43,68%76'01912R2#:,43,68%72'0/05530e1;361;32/05530eX80W:W9W3o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem strlen_step_sound : forall x_len ro_lo ro_hi,
  SR.strlen_spec segs ro_lo ro_hi x_len -> SR.strlen_step_stmt segs x_len ro_lo ro_hi.
Proof.
  intros x_len ro_lo ro_hi STRLEN fx kz ss w ss' w' E R M Hcl H [HR HK].
  pose proof Hcl as Hcl0. unfold SR.closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 Fw0]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  destruct (SR.closed_parts ss w Hcl) as (Fsr & Fkn & Fw & Flog).
  cbv zeta beta delta [SR.step_strlen] in H.
  destruct (Z.eqb (s_pc ss) x_len) eqn:Hpc; [|discriminate]. cbn [negb] in H. apply Z.eqb_eq in Hpc.
  destruct (SR.ret_lit ss) as [ret|] eqn:Hret; [|discriminate].
  destruct (split_lit (SR.reg ss 10)) as [sb sk] eqn:Hsp.
  destruct (xhi (facts_of (s_know ss)) (SR.reg ss 10)) as [shi|] eqn:Hshi; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply SR.some_pair_inj in H as [<- <-].
  repeat (apply andb_true_iff in Hc as [Hc ?X]).
  rename X into Hro. rename X0 into Hfl. rename X1 into Hwr. rename X2 into Hzb. rename X3 into Hnzb. rename X4 into Hal. rename X5 into Hhi.
  apply Z.leb_le in Hc. apply Z.ltb_lt in Hhi. apply Z.leb_le in Hal. unfold two64 in Hhi.
  set (k := s_know ss) in *. set (fk := facts_of k) in *. set (m := SR.wden segs E M w) in *. set (nx := s_next ss) in *.
  set (n := sk + kz - (sk + kz) mod 8 + 8 - sk) in *.
  pose proof (Z.mod_pos_bound (sk + kz) 8 ltac:(lia)) as HM8.
  assert (Hn1 : kz + 1 <= n <= kz + 8) by (subst n; lia).
  pose proof (facts_of_ok segs E m k HK) as HKf. fold fk in HKf.
  (* [comment removed for export] *)
  pose proof (SR.reg_sound10 E ss R HR) as R10.
  pose proof (xhi_sound segs E m fk (SR.reg ss 10) shi HKf Hshi) as XS.
  rewrite (APSX.w_split_lit_denot E (SR.reg ss 10) sb sk Hsp) in R10, XS.
  set (S := estart E (SA sb sk)) in *.
  change (bv_unsigned (edenot E sb) + sk) with S in R10, XS.
  pose proof (u64_range (Z_to_bv 64 S)) as HS0.
  assert (Hnlt : 0 <= n < 2 ^ 64) by (clear - Hn1 Hc Hhi XS HS0; lia).
  assert (Hlen : bv_unsigned (edenot E (ELit n)) = n) by (cbn [edenot]; apply u64_of_Z; exact Hnlt).
  destruct (APSX.w_flat_x_sound segs E m fk sb sk (ELit n) HKf Hfl) as (Slo & Shi & _). rewrite Hlen in Shi.
  fold S in Slo, Shi.
  assert (HS64 : 0 <= S < 2 ^ 64) by (clear - Slo Shi Hn1 Hc; lia).
  rewrite (u64_of_Z S HS64) in XS.
  set (s := Z_to_bv 64 S) in *.
  assert (Hus : bv_unsigned s = S) by (subst s; apply u64_of_Z; exact HS64).
  assert (FL : flat E (SA sb sk) n) by (unfold flat; fold S; clear - HS64 Shi Hn1 Hc; lia).
  (* [comment removed for export] *)
  destruct (ealign_sound segs E m k sb HK) as [Hal64 Hdiv].
  assert (B8 : bv_unsigned (edenot E sb) mod 8 = 0).
  { destruct Hdiv as [q Hq]. rewrite Hq.
    assert (P : 2 ^ ealign k sb = 2 ^ (ealign k sb - 3) * 8).
    { replace (ealign k sb) with (ealign k sb - 3 + 3) at 1 by lia. rewrite Z.pow_add_r by lia. reflexivity. }
    rewrite P, Z.mul_assoc. apply Z_mod_mult. }
  assert (MODS : forall x, (S + x) mod 8 = (sk + x) mod 8).
  { intros x. subst S. unfold estart. cbn [a_base a_off].
    rewrite <- Z.add_assoc. rewrite Z.add_mod, B8, Z.add_0_l by lia. apply Z.mod_mod. lia. }
  (* [comment removed for export] *)
  assert (BYTE : forall i, 0 <= i < n ->
            exists b, rdn segs m (Z_to_bv 64 (S + i)) 1 = Some [b]
                      /\ (i < kz -> bv_unsigned b <> 0) /\ (i = kz -> bv_unsigned b = 0)).
  { intros i Hi.
    assert (AD : adenot E (SA sb (sk + i)) = Z_to_bv 64 (S + i)) by (rewrite APSX.adenot_SA, estart_off; reflexivity).
    destruct (Z.lt_total i kz) as [Hlt|[Heq|Hgt]].
    - destruct (bytes_nonzero_sound E m fk k sb (Z.to_nat kz) sk HK Hnzb) with (i := i) as (b & Hrd & Hb).
      + intros i' Hi'. eapply flat_byte; [exact FL | lia].
      + lia.
      + rewrite AD in Hrd. exists b. split; [exact Hrd|]. split; [intros _; exact Hb | intros; lia].
    - subst i. destruct (byte_zero_sound E m k sb (sk + kz) HK Hzb ltac:(eapply flat_byte; [exact FL | lia])) as (b & Hrd & Hb).
      rewrite AD in Hrd. exists b. split; [exact Hrd|]. split; [intros; lia | intros _; exact Hb].
    - destruct (words_readable_sound E m fk k sb (Z.to_nat (sk + kz - (sk + kz) mod 8 + 8 - (sk + kz + 1))) (sk + kz + 1) HKf HK Hwr
                  (i - kz - 1) ltac:(lia)) as (_ & b & Hrd).
      replace (sk + kz + 1 + (i - kz - 1)) with (sk + i) in Hrd by lia.
      rewrite AD in Hrd. exists b. split; [exact Hrd|]. split; intros; lia. }
  destruct (rdn_defined segs m (Z.to_nat n) s) as (buf & Hbuf & Hlbuf).
  { rewrite Hus. clear - Shi Hnlt. lia. }
  { intros j Hj. destruct (BYTE (Z.of_nat j) ltac:(lia)) as (b & Hrd & _). rewrite Hus. eapply rdn1_rd1. exact Hrd. }
  assert (NTH : forall i, 0 <= i < n -> exists b, nth (Z.to_nat i) buf (Z_to_bv 8 0) = b
                  /\ (i < kz -> bv_unsigned b <> 0) /\ (i = kz -> bv_unsigned b = 0)).
  { intros i Hi. destruct (BYTE i Hi) as (b & Hrd & Hb1 & Hb2). exists b.
    pose proof (APSX.rdn_nth segs m (Z.to_nat n) s buf (Z.to_nat i) ltac:(rewrite Hus; clear - Shi Hnlt; lia) Hbuf ltac:(lia)) as X.
    rewrite Hus, Z2Nat.id in X by lia. rewrite Hrd in X. injection X as <-. split; [reflexivity | split; assumption]. }
  (* [comment removed for export] *)
  destruct (SR.ret_lit_sound E ss R ret HR Hret) as (R1 & Hrok & Hret64).
  assert (R10' : getr R 10%bv = s) by exact R10.
  destruct (STRLEN fx m s buf kz (seg_rom segs) R (Z_to_bv 64 ret) ltac:(rewrite Hlbuf; exact Hbuf)) as (regs' & Hms & Hkept & Ha0).
  { rewrite Hus, Hlbuf, Z2Nat.id by lia.
    pose proof (Z.div_mod (S + kz) 8 ltac:(lia)) as D1. rewrite (MODS kz) in D1. subst n. clear - D1 HM8 Hc. lia. }
  { rewrite Hus, Hlbuf, Z2Nat.id by lia. clear - XS Hhi. lia. }
  { exact Hc. }
  { destruct (NTH kz ltac:(lia)) as (b & <- & _ & Hb). apply Hb. reflexivity. }
  { intros j Hj. destruct (NTH (Z.of_nat j) ltac:(lia)) as (b & Hb & Hnz & _). rewrite Nat2Z.id in Hb. rewrite Hb. apply Hnz. lia. }
  { eapply ro_covered_sound; [exact HK | exact Hro]. }
  { exact Hrok. }
  { exact R1. }
  { exact R10'. }
  (* [comment removed for export] *)
  set (E' := APS.ext_list E nx (map (fun r => getr regs' (Z_to_bv 5 (Z.of_nat r))) SL)).
  pose proof (APS.ext_list_agree E nx (map (fun r => getr regs' (Z_to_bv 5 (Z.of_nat r))) SL)) as Hag. fold E' in Hag.
  exists fx, E', regs'.
  split; [exact Hag|]. split; [cbn [s_next]; lia|].
  assert (Hw : SR.wden segs E' M w = m) by (symmetry; eapply SR.wden_agree; [exact Hag | exact Fw]).
  split.
  - split.
    + cbn [s_regs s_next]. apply (regs_after_strlen E (s_regs ss) R regs' nx kz HR Fsr0 Hkept Ha0).
    + cbn [s_know]. rewrite Hw. eapply APS.know_ok_agree'; [exact Hag | exact Fkn0 | exact HK].
  - cbn [s_pc]. rewrite Hw, Hpc. exact Hms.
Qed.

End WithSegs.
End SRS.

End SegRunStrlen.
From LinuxProcessSemantics.Riscv Require Prelude Instr. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan.
Module SegPlanAuto.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SGA.
Section WithImage.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable IT : itab.
Variable x_cpy x_set x_len ro_lo ro_hi : Z.
Variable BFUEL : nat.
Variable STOPS : list Z.
Variable ENDS : list Z.        (* [comment removed for export] *)
Variable A : APC.atable.             (* [comment removed for export] *)
Variable F : list SGP.region.

Definition STEP (st : SR.sstep) := SGP.step1 segs IT x_cpy x_set x_len ro_lo ro_hi BFUEL F st.
Definition is_lit (e : expr) : bool := match e with ELit _ => true | _ => false end.
Inductive aitem := AStep (st : SR.sstep) | ACopyX | AFillX.
Fixpoint mkplan (l : list aitem) (tail : SGP.splan) : SGP.splan :=
  match l with
  | [] => tail
  | AStep st :: r => SGP.PStep st (mkplan r tail)
  | ACopyX :: r => SGP.PCopyX (mkplan r tail)
  | AFillX :: r => SGP.PFillX (mkplan r tail)
  end.
(* [comment removed for export] *)
Definition special (ss : sym_state) : option (aitem * sym_state) :=
  if Z.eqb (s_pc ss) x_cpy then
    (if is_lit (SR.reg ss 12) then
       match STEP SR.SCopy ss with Some s' => Some (AStep SR.SCopy, s') | None => None end
     else match SGP.copyx x_cpy A F ss with Some s' => Some (ACopyX, s') | None => None end)
  else if Z.eqb (s_pc ss) x_set then
    (if is_lit (SR.reg ss 12) then
       match STEP SR.SFill ss with Some s' => Some (AStep SR.SFill, s') | None => None end
     else match SGP.fillx x_set F ss with Some s' => Some (AFillX, s') | None => None end)
  else match itab_lookup IT (s_pc ss) with
       | Some (Instr.FStore Instr.FMT_D _ _ _) => match STEP (SR.SFsdSeq 32) ss with Some s' => Some (AStep (SR.SFsdSeq 32), s') | None => None end
       | Some (Instr.FLoad Instr.FMT_D _ _ _) => match STEP (SR.SFldSeq 32) ss with Some s' => Some (AStep (SR.SFldSeq 32), s') | None => None end
       | _ => None
       end.
Fixpoint auto (n : nat) (ss : sym_state) : list aitem * (Z * sym_state) :=
  match n with
  | O => ([], (90, ss))
  | S m =>
    if existsb (Z.eqb (s_pc ss)) ENDS then ([], (93, ss)) else
    match special ss with
    | Some (it, s') => let '(l, r) := auto m s' in (it :: l, r)
    | None =>
        match STEP (SR.SBlock STOPS) ss with
        | Some ss' =>
            if negb (Z.eqb (s_pc ss') (s_pc ss)) then let '(l, r) := auto m ss' in (AStep (SR.SBlock STOPS) :: l, r)
            else ([], (91, ss'))
        | None => ([], (92, ss))
        end
    end
  end.
End WithImage.
End SGA.

End SegPlanAuto.
