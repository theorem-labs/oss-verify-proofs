(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (30 recorded proofs replaced by written proofs (size_of_class_24, batches_bytes_app, batches_bytes_cons and 27 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ARep ARepQ ARepFrame AHeapP AKit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ARepQP () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C46Stdlib5Lists4List2hdC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC46Stdlib5Lists4List6nth_okK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec8AsanCtrl=batches_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib4Spec8AsanCtrl6b_sizeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List:fold_rightI59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init9Datatypes3nat02C47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega;ZifyClasses;rew_iff_revc59OSSVerify5KrLib5BothW6ARepQPBbatches_bytes_consC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes6lengthC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib4Spec8AsanCtrl=Q_BATCH_BYTESC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib4Init9Datatypes3nat01c59OSSVerify5KrLib5BothW6ARepQPAbatches_bytes_nilC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib5Lists4List2Inc59OSSVerify5KrLib5BothW6ARepQP@batches_bytes_lbC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05I47Corelib4Init5Logic3and00K46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init5Logic2or00C59OSSVerify5KrLib5BothW5ARepQ7qb_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ;abatch_addrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_appC59OSSVerify5KrLib5BothW5ARepQ6qaddrsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ARepQ7qbatchc00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4lastC46Stdlib5Lists4List9last_lastc59OSSVerify5KrLib5BothW6ARepQP:qaddrs_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5qlastC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib5BothW5ARepQ6qfirstC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib5Lists4List9app_assocC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsCeq_rewrite_relationC46Stdlib5Lists4List:removelastC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC46Stdlib5Lists4ListCapp_removelast_lastc59OSSVerify5KrLib5BothW6ARepQP;last_app_neC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_appC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega6VarMap1t01C46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib5BothW5ARepQ5qhdrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ4qhdrC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addI59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib5BothW5ARepQ8qentriesC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C59OSSVerify5KrLib4Spec8AsanCtrl8b_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5qb_ksC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7combineK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5BothW5ARepQ;abatches_toC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ<abatch_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8abatchesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6ARepQPBabatches_to_lengthC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init5Logic7and_indC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib4Init5Logic3iffC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes?RelationClasses=iff_ReflexiveC59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib4Spec8AsanCtrl7b_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameAdisjoint_from_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame;cells_frameC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03c59OSSVerify5KrLib5BothW6ARepQP<qhdrs_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib5BothW9ARepFrame<u64arr_frameC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib5BothW9ARepFrame:junk_frameC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7Q_BATCHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic2or01c59OSSVerify5KrLib5BothW6ARepQPBabatch_cells_frameC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02c59OSSVerify5KrLib5BothW6ARepQPAabatches_to_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7aqcacheC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6ARepQP>abatches_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6aintalC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib3Lib5Frame@disjoint_outsideC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4AKit>bytes_at_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_FLAGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_BASEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst<AIA_MAP1_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_MAP1C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00C59OSSVerify5KrLib5BothW5ARepQ@aquar_glob_constC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst6AQ_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7Q_CACHEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AQ_MUTEXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8qcoupledC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5q_locC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6q_globC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ9qentry_okC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xb_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6q_pendC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6in_mapC47Corelib4Init5Logic5proj1C59OSSVerify5KrLib5BothW5ARepQ9qprim_idsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ARepQ5qconc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8AQUAR_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst9aq_tcacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP>quar_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9quar_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ4qnumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_allocC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;Forall_implc59OSSVerify5KrLib5BothW6ARepQPDdisjoint_from_ForallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6ARepQPCqcoupled_bslot_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ4q_iaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6ARepQPFaquar_glob_const_frameC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_app_iffc59OSSVerify5KrLib5BothW6ARepQP=aqcache_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6ARepQP<aintal_frameC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep5xbusy01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst9AQ_GCACHEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9AINSTANCEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6ARepQP@size_of_class_24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5AQUARC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6ARepQP>AQUAR_frame_atC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K46Stdlib5Lists4List5NoDup01C47Corelib4Init5Logic6eq_symK47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib5BothW5ARepQ6qconc0C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma size_of_class_24 : size_of_class K_BATCH_CLASS = 8192.
Proof. vm_compute. reflexivity. Qed.

Lemma batches_bytes_app : forall l1 l2, batches_bytes (l1 ++ l2) = batches_bytes l1 + batches_bytes l2.
Proof. induction l1 as [|b l1 IH]; intros l2; cbn; [reflexivity| rewrite IH; unfold batches_bytes; lia]. Qed.
Lemma batches_bytes_cons : forall b l, batches_bytes (b :: l) = b_size b + batches_bytes l.
Proof. reflexivity. Qed.
Lemma batches_bytes_nil : batches_bytes [] = 0.
Proof. reflexivity. Qed.

Lemma batches_bytes_lb : forall l, Forall (fun b => Q_BATCH_BYTES <= b_size b) l -> Q_BATCH_BYTES * Z.of_nat (length l) <= batches_bytes l.
Proof.
  induction l as [|b l IH]; intros HF; cbn [length]; [rewrite batches_bytes_nil; lia|].
  rewrite batches_bytes_cons. inversion HF; subst. specialize (IH ltac:(assumption)). unfold Q_BATCH_BYTES in *. lia.
Qed.
Lemma batches_bytes_In : forall l b, Forall (fun b => Q_BATCH_BYTES <= b_size b) l -> In b l -> Q_BATCH_BYTES <= b_size b <= batches_bytes l.
Proof.
  induction l as [|a l IH]; intros b HF Hin; [destruct Hin|].
  rewrite batches_bytes_cons. inversion HF; subst. pose proof (batches_bytes_lb l ltac:(assumption)) as LB.
  destruct Hin as [<-|Hin]; [unfold Q_BATCH_BYTES in *; lia|]. specialize (IH b ltac:(assumption) Hin). unfold Q_BATCH_BYTES in *; lia.
Qed.

Lemma qaddrs_app : forall L qs1 qs2, qaddrs L (qs1 ++ qs2) = qaddrs L qs1 ++ qaddrs L qs2.
Proof. intros. unfold qaddrs. apply map_app. Qed.
Lemma qfirst_cons : forall L q qs, qfirst L (q :: qs) = abatch_addr L (qb_slot q).
Proof. reflexivity. Qed.
Lemma qfirst_nil : forall L, qfirst L [] = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_ARepQP ()) ["CANSEC1"] "h01Lp;2p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9p1001ip4p710p1002Fp4p710R0p8p1002dp4p70R1g003[R2p4p710p8P1p10045p4p710p8P1p1004Lp4p710p8P1p1004hp4p710p8p1005Fp4p710P0p8P2j20Tg00g^g008>g00Gn'0W0o"). Qed.
Lemma qlast_nil : forall L, qlast L [] = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_ARepQP ()) ["CANSEC1"] "h01Lp;2p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9p1001ip4p710p1002Fp4p710R0p8p1002dp4p70R1g003[R2p4p710p8P1p10045p4p710p8P1p1004Lp4p710p8P1p1004hp4p710p8p1005Fp4p710P0p8P2j20Tg00g^g008>g00Gn'0W0o"). Qed.
Lemma qlast_app1 : forall L qs q, qlast L (qs ++ [q]) = abatch_addr L (qb_slot q).
Proof. intros. unfold qlast. rewrite qaddrs_app. cbn [qaddrs map]. apply last_last. Qed.
Lemma qfirst_app : forall L qs1 qs2, qs1 <> [] -> qfirst L (qs1 ++ qs2) = qfirst L qs1.
Proof. intros L [|q qs1] qs2 NE; [congruence| reflexivity]. Qed.
Lemma last_app_ne : forall {A} (l1 l2 : list A) d, l2 <> [] -> last (l1 ++ l2) d = last l2 d.
Proof.
  intros A l1 l2 d NE. rewrite (app_removelast_last d NE) at 1. rewrite app_assoc, last_last.
  reflexivity.
Qed.
Lemma qlast_app : forall L qs1 qs2, qs2 <> [] -> qlast L (qs1 ++ qs2) = qlast L qs2.
Proof.
  intros L qs1 qs2 NE. unfold qlast. rewrite qaddrs_app. apply last_app_ne.
  unfold qaddrs. destruct qs2; [congruence| discriminate].
Qed.

Lemma qhdrs_length : forall L chs ks, length ks = length chs -> length (qhdrs L chs ks) = length chs.
Proof.
  induction chs as [|ch chs IH]; intros [|k ks] LEN; cbn in *; try lia.
  rewrite length_app, IH by lia. cbn. lia.
Qed.
Lemma qhdrs_cons : forall L ch chs k ks, qhdrs L (ch :: chs) (k :: ks) = qhdrs L chs ks ++ [qhdr L ch k].
Proof. reflexivity. Qed.

Lemma qentries_app : forall bs1 qs1 bs2 qs2, length qs1 = length bs1 ->
  qentries (bs1 ++ bs2) (qs1 ++ qs2) = qentries bs1 qs1 ++ qentries bs2 qs2.
Proof.
  induction bs1 as [|b bs1 IH]; intros [|q qs1] bs2 qs2 LEN; cbn in *; try lia; [reflexivity|].
  rewrite IH by lia. rewrite app_assoc. reflexivity.
Qed.

Lemma abatches_to_length : forall L m bs qs nxt, abatches_to L m bs qs nxt -> length qs = length bs.
Proof.
  induction bs as [|b bs IH]; intros [|q qs] nxt AB; cbn in *; try tauto.
  destruct AB as [_ AB]. rewrite (IH qs nxt AB). reflexivity.
Qed.
Lemma abatches_length : forall L m bs qs, abatches L m bs qs -> length qs = length bs.
Proof. intros. eapply abatches_to_length. exact H. Qed.

(* [comment removed for export] *)
Lemma abatches_to_app : forall L m bs1 qs1 bs2 qs2 nxt, length qs1 = length bs1 ->
  abatches_to L m (bs1 ++ bs2) (qs1 ++ qs2) nxt <-> abatches_to L m bs1 qs1 (hd nxt (qaddrs L qs2)) /\ abatches_to L m bs2 qs2 nxt.
Proof.
  induction bs1 as [|b bs1 IH]; intros [|q qs1] bs2 qs2 nxt LEN; cbn in *; try lia; [tauto|].
  rewrite IH by lia. rewrite qaddrs_app.
  assert (E : hd nxt (qaddrs L qs1 ++ qaddrs L qs2) = hd (hd nxt (qaddrs L qs2)) (qaddrs L qs1)).
  { destruct qs1; cbn; reflexivity. }
  rewrite E. tauto.
Qed.
Lemma abatches_to_last : forall L m b q nxt, abatches_to L m [b] [q] nxt <-> abatch_cells L m b q nxt.
Proof. intros. cbn. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma disjoint_from_Forall : forall W A n,
  Forall (fun iv => snd iv <= A \/ A + n <= fst iv) W -> disjoint_from W A n.
Proof. induction W as [|[lo hi] W IH]; intros A n HF; cbn; [exact I|]. inversion HF; subst. cbn in *. split; [lia| apply IH; assumption]. Qed.

Section Frames.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.

Lemma abatch_cells_frame : forall b q nx,
  abatch_cells L m b q nx -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES -> abatch_cells L m' b q nx.
Proof.
  intros b q nx (H1 & H2 & H3 & H4 & H5 & H6) D. unfold abatch_cells. cbv zeta. unfold Q_BATCH_BYTES, Q_BATCH in *.
  split; [| split; [| split; [| split; [exact H4| split; [exact H5| exact H6]]]]].
  - eapply cells_frame; [exact H1 | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D| lia| lia| lia].
  - eapply u64arr_frame; [exact H2 | exact MU | exact WM |]. rewrite length_map, qhdrs_length by exact H5. rewrite <- H4.
    eapply disjoint_from_sub; [exact D| lia| lia| lia].
  - eapply junk_frame; [exact H3 | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D| lia| lia| lia].
Qed.

Lemma abatches_to_frame : forall bs qs nxt,
  abatches_to L m bs qs nxt -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches_to L m' bs qs nxt.
Proof.
  induction bs as [|b bs IH]; intros [|q qs] nxt AB D; cbn in *; try tauto.
  destruct AB as [AC AB]. split.
  - eapply abatch_cells_frame; [exact AC| apply D; left; reflexivity].
  - apply IH; [exact AB|]. intros q' Hq'. apply D. right. exact Hq'.
Qed.
Lemma abatches_frame : forall bs qs,
  abatches L m bs qs -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches L m' bs qs.
Proof. intros. eapply abatches_to_frame; eassumption. Qed.

Lemma aqcache_frame : forall C bs qs bytes,
  aqcache L m C bs qs bytes -> disjoint_from W C 32 ->
  (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> aqcache L m' C bs qs bytes.
Proof.
  intros C bs qs bytes [QC AB] D DB. split.
  - eapply cells_frame; [exact QC | exact MU | exact WM | exact D].
  - eapply abatches_frame; [exact AB | exact DB].
Qed.

Lemma aintal_frame : forall ia,
  aintal ia m -> disjoint_from W AIA_FLAG 4 -> disjoint_from W AIA_BASE AIA_SIZE -> aintal ia m'.
Proof.
  intros ia (F & S & Z0) DF DB. unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in *. split; [| split].
  - eapply cells_frame; [exact F | exact MU | exact WM | exact DF].
  - eapply stk_transport_disjoint; [exact S | exact MU | exact WM |]. exact DB.
  - intros Hia j Hj. eapply bytes_at_agree; [exact (Z0 Hia j Hj)|].
    intros i Hi. apply MU. rewrite length_le8 in Hi. unfold AIA_MAP1, AIA_MAP1_LEN in *. cbn in Hj.
    rewrite wa_unsigned by lia.
    eapply disjoint_outside; [exact DB| lia].
Qed.

Lemma aquar_glob_const_frame :
  aquar_glob_const m -> disjoint_from W AQ_MAX 24 -> disjoint_from W AQ_MUTEX 4 -> aquar_glob_const m'.
Proof.
  intros [A B] D1 D2. split.
  - eapply cells_frame; [exact A | exact MU | exact WM | exact D1].
  - eapply cells_frame; [exact B | exact MU | exact WM | exact D2].
Qed.
End Frames.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qcoupled_bslot_busy : forall L st X Q q,
  qcoupled L st X Q -> In q (q_loc Q ++ q_glob Q) ->
  exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_class b = K_BATCH_CLASS /\ xb_slot b = qb_slot q.
Proof.
  intros L st X Q q (_ & _ & _ & _ & _ & BS & _) Hin. apply (proj1 (BS (qb_slot q))). apply in_map. exact Hin.
Qed.

Theorem AQUAR_frame_at : forall L st st' X X' Q m m' W,
  AQUAR_at L st X Q m -> munch W m m' -> wmono bsegs m m' -> quar_untouched L X W -> quar_same st st' X X' ->
  AQUAR_at L st' X' Q m'.
Proof.
  intros L st st' X X' Q m m' W (GC & TC & GL & IA & CP & NUM) MU WM UT (E1 & E2 & E3 & E4 & E5 & FW & BW).
  unfold AQUAR_at. rewrite E1, E2, E3, E4.
  (* [comment removed for export] *)
  assert (DT : disjoint_from W (aq_tcache L) 32).
  { apply disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (A & _). unfold aq_tcache. cbn in A |- *. lia. }
  assert (DG : disjoint_from W AQ_MAX 24 /\ disjoint_from W AQ_MUTEX 4 /\ disjoint_from W AQ_GCACHE 32).
  { unfold AQ_MAX, AQ_MUTEX, AQ_GCACHE, AINSTANCE in *.
    repeat split; apply disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & A & _); unfold AINSTANCE in A; cbn in A |- *; lia. }
  destruct DG as (DG1 & DG2 & DG3).
  assert (DI1 : disjoint_from W AIA_FLAG 4 /\ disjoint_from W AIA_BASE AIA_SIZE).
  { unfold AIA_FLAG, AIA_BASE, AIA_SIZE in *.
    split; apply disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & _ & A & B & _); cbn in A, B |- *; lia. }
  destruct DI1 as [DF DB].
  assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
  { intros q Hq. destruct (qcoupled_bslot_busy L st X Q q CP Hq) as (b & Hb & Sb & Cb & Kb).
    apply disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (_ & _ & _ & _ & A).
    specialize (A b Hb). rewrite Sb in A. unfold xb_alloc in A. rewrite Cb, Kb, size_of_class_24 in A.
    unfold abatch_addr, Q_BATCH_BYTES. cbn. exact A. }
  split; [| split; [| split; [| split; [| split]]]].
  - eapply aquar_glob_const_frame; eassumption.
  - eapply aqcache_frame; [exact MU | exact WM | exact TC | exact DT |]. intros q Hq. apply DQ. apply in_app_iff. left. exact Hq.
  - eapply aqcache_frame; [exact MU | exact WM | exact GL | exact DG3 |]. intros q Hq. apply DQ. apply in_app_iff. right. exact Hq.
  - eapply aintal_frame; eassumption.
  - (* [comment removed for export] *)
    destruct CP as (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN).
    unfold qcoupled. cbv zeta. rewrite E1, E3.
    split; [exact LN1|]. split; [exact LN2|]. split.
    { eapply Forall_impl; [| exact OK]. intros [ch k] HOK. unfold qentry_ok in *. cbn [fst snd] in *.
      destruct ch as [c n | mb ms n]; [| exact I]. destruct HOK as (b1 & ctx & Hin). exists b1, ctx.
      specialize (FW _ Hin). cbn in FW. exact FW. }
    split; [exact ND1|]. split; [exact ND2|]. split.
    { intros k. rewrite (BS k). split; intros (b & Hb & Sb & R); exists b; (split; [| split; [exact Sb| exact R]]).
      - specialize (FW b Hb). rewrite Sb in FW. exact FW.
      - specialize (BW b Hb). rewrite Sb in BW. exact BW. }
    split; [| exact NN].
    intros c k. rewrite (PS c k). split; intros (b & Hb & Sb & R); exists b; (split; [| split; [exact Sb| exact R]]).
    + specialize (FW b Hb). rewrite Sb in FW. exact FW.
    + specialize (BW b Hb). rewrite Sb in BW. exact BW.
  - unfold qnum in *. rewrite E1, E2, E3, E4. exact NUM.
Qed.
Theorem AQUAR_frame : forall L st st' X X' m m' W,
  AQUAR L st X m -> munch W m m' -> wmono bsegs m m' -> quar_untouched L X W -> quar_same st st' X X' ->
  AQUAR L st' X' m'.
Proof. intros L st st' X X' m m' W [Q AQ] MU WM UT QS. exists Q. exact (AQUAR_frame_at L st st' X X' Q m m' W AQ MU WM UT QS). Qed.

(* [comment removed for export] *)
Lemma AQUAR_init : forall L st X m,
  a_qloc st = [] -> a_qloc_bytes st = 0 -> a_qglob st = [] -> a_qglob_bytes st = 0 ->
  aquar_glob_const m ->
  rw_cells bsegs m (aq_tcache L) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m AQ_GCACHE [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  aintal false m ->
  (forall b, In b (x_busy X) -> exists p, xb_st b = BLive p) ->
  AQUAR L st X m.
Proof.
  intros L st X m Q1 Q2 Q3 Q4 GC TC GL IA LIVE. exists qconc0. unfold AQUAR_at. rewrite Q1, Q2, Q3, Q4. cbn [q_loc q_glob q_ia q_pend qconc0].
  split; [exact GC|]. split; [split; [exact TC| exact I]|]. split; [split; [exact GL| exact I]|]. split; [exact IA|]. split.
  - unfold qcoupled. cbn. rewrite Q1, Q3. cbn. repeat split; try constructor; try (intros; tauto).
    + intros [b (Hb & Sb & _)]. destruct (LIVE b Hb) as [p E]. congruence.
    + intros [b (Hb & Sb & _)]. destruct (LIVE b Hb) as [p E]. congruence.
  - unfold qnum. rewrite Q1, Q2, Q3, Q4. cbn. unfold Q_CACHE, Q_MAX. repeat split; try lia. constructor.
Qed.
End CANSEC1.
