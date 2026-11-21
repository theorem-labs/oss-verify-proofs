(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (11 recorded proofs replaced by written proofs (malloc_small_ctrl_eq, usages_length, usages_nth and 8 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp F_malloc_enf AllocSlot_iface Malloc_iface F_malloc_join.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_malloc_small () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C35stdpp6option;from_optionC47Corelib4Init9Datatypes2IDC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAmalloc_small_ctrlC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc>F_malloc_small9coarse_scC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5ctz32C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z3ltbK47Corelib4Init9Datatypes6option02K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I59OSSVerify5KrLib4Spec6Malloc;layout_hook00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib4Spec6Malloc4FUELC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00C46Stdlib5Lists4List:length_seqK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib6Malloc9MallocRep6usagesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorC47Corelib4Init9Datatypes:option_mapC56Stdlib5Arith8PeanoNat3Nat3ltbC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC56Stdlib5Arith8PeanoNat3Nat6ltb_ltC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List=nth_error_seqC46Stdlib5Lists4List=nth_error_mapC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z?bits_above_log2C46Stdlib4Bool4Bool<andb_false_rK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z?pow2_bits_falseC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorK46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z4evenC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z4EvenC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z9even_specC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic2ex01C46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z4onesC47Corelib7Classes?RelationClasses?iff_equivalenceK47Corelib4Init5Logic4True01I47Corelib4Init5Logic2ex00c59OSSVerify5KrLib6Malloc>F_malloc_small:lor1_checkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC47Corelib4Init9Datatypes3orbC59OSSVerify5KrLib6Malloc@F_malloc_enframe<forallb_zseqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltc59OSSVerify5KrLib6Malloc>F_malloc_small?lor1_check_trueC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc>F_malloc_small@lor1_range_checkC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propc59OSSVerify5KrLib6Malloc>F_malloc_smallElor1_range_check_trueC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02I47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums1N01".
Import ListNotations.
Open Scope Z_scope.

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition coarse_sc (st : mstate) (sc : Z) : Z :=
  match active st sc with
  | Some _ => sc
  | None =>
    if (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) then
      let usage1 := usage st (Z.lor sc 1) in
      let usage1 := match active st (Z.lor sc 1) with
                    | None => usage1 + 3
                    | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc 1))) in
                                if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
                    end in
      if usage1 <=? 12 then Z.lor sc 1 else sc
    else sc
  end.

Lemma malloc_small_ctrl_eq {R} lay st n (k : mstate -> option (aptr * Z) -> Malloc.M R) bail :
  malloc_small_ctrl lay st n k bail =
  let sc := coarse_sc st (size_to_class n) in
  let g := active st sc in
  let mask := match g with Some gp => m_avail (get_meta_rec st gp) | None => 0 end in
  let first := lowbit mask in
  match g, negb (first =? 0) with
  | Some gp, true => k (upd_meta gp (m_set_avail (mask - first)) st) (Some (gp, ctz32 first))
  | _, _ =>
    alloc_slot lay FUEL st sc n (fun st1 idx =>
      if idx <? 0 then k st1 None
      else match active st1 sc with
           | Some gp => k st1 (Some (gp, idx))
           | None => SVis (EUndef UBadPtr) (fun _ => bail)
           end) bail
  end.
Proof. reflexivity. Qed.

Lemma usages_length : forall st, length (usages st) = 48%nat.
Proof. intros. unfold usages. rewrite length_map, length_seq. reflexivity. Qed.
Lemma usages_nth : forall st sc, 0 <= sc < 48 -> nth_error (usages st) (Z.to_nat sc) = Some (wz (usage st sc)).
Proof.
  intros st sc Hsc. unfold usages. rewrite nth_error_map, nth_error_seq.
  replace (Z.to_nat sc <? 48)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma lxor_sign_small x : 0 <= x < 2^63 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof.
  intros Hx. change 9223372036854775808 with (2^63).
  rewrite <- Z.add_nocarry_lxor. 2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec i 63) as [->|NE].
    - replace (Z.testbit x 63) with false; [reflexivity|]. symmetry. apply Z.bits_above_log2; [lia|].
      destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
    - rewrite Z.pow2_bits_false by lia. apply andb_false_r. }
  reflexivity.
Qed.

Lemma land_ones64 y : Z.land y 18446744073709551615 = y mod 2^64.
Proof. change 18446744073709551615 with (Z.ones 64). apply Z.land_ones. lia. Qed.

Lemma land_1_even x : (Z.land x 1 = 0) <-> Z.even x = true.
Proof.
  change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2^1) with 2.
  rewrite Z.even_spec. split.
  - intros H. exists (x / 2). lia.
  - intros [k ->]. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

Section COARSE.
Variables (st : mstate) (LB : list block) (m1 : mem) (t : N).
Let st1 := set_tick t st.
Hypothesis MF : MFACTS st LB.
End COARSE.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lor1_check : bool :=
  forallb (fun sc => negb ((4 <=? sc) && (sc <? 32) && Z.even sc) || (size_class sc <=? size_class (Z.lor sc 1))) (zseq 0 48).
Lemma lor1_check_true : lor1_check = true.
Proof. vm_compute. reflexivity. Qed.

Lemma size_class_lor1 sc : 4 <= sc < 32 -> Z.even sc = true -> size_class sc <= size_class (Z.lor sc 1).
Proof.
  intros H E. pose proof (forallb_zseq _ 0 48 sc lor1_check_true ltac:(lia) ltac:(lia)) as X. cbv beta in X.
  replace (4 <=? sc) with true in X by (symmetry; apply Z.leb_le; lia).
  replace (sc <? 32) with true in X by (symmetry; apply Z.ltb_lt; lia). rewrite E in X. cbn [andb negb orb] in X.
  apply Z.leb_le. exact X.
Qed.

Definition lor1_range_check : bool := forallb (fun sc => (0 <=? Z.lor sc 1) && (Z.lor sc 1 <? 48)) (zseq 0 48).
Lemma lor1_range_check_true : lor1_range_check = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lor1_range sc : 0 <= sc < 48 -> 0 <= Z.lor sc 1 < 48.
Proof.
  intros H. pose proof (forallb_zseq _ 0 48 sc lor1_range_check_true ltac:(lia) ltac:(lia)) as X. cbv beta in X.
  apply andb_prop in X. destruct X as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. lia.
Qed.

Lemma coarse_sc_cases st sc : 0 <= sc < 48 ->
  coarse_sc st sc = sc \/ (coarse_sc st sc = Z.lor sc 1 /\ 4 <= sc < 32 /\ Z.even sc = true).
Proof.
  intros H. unfold coarse_sc. destruct (active st sc); [left; reflexivity|].
  destruct ((4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0)) eqn:E; [|left; reflexivity].
  apply andb_prop in E. destruct E as [E E5]. apply andb_prop in E. destruct E as [E E4].
  apply andb_prop in E. destruct E as [E E3]. apply andb_prop in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  cbv zeta. destruct (_ <=? 12); [right|left]; auto.
Qed.

Section SMALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (bail : Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis MF : MFACTS st LB.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64 - AS_STACK FUEL.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.
End SMALL.


End CANSEC1.
