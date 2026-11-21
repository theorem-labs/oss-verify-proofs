(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (9 recorded proofs replaced by written proofs (land_4095, round_up_pg_aligned, round_up_pg_eq and 6 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim STree Malloc KInv.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_KStep () := "K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive02I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z9land_onesC47Corelib4Init5Logic8eq_ind_rI46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega5Tauto8GFormula07K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z;mod_opp_l_zK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03c59OSSVerify5KrLib4Spec5KStep9land_4095C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5KStep7PGSZ_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC46Stdlib6ZArith4ZdivAZ_div_mod_eq_fullC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_neg_boundI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr04C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op205C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeK47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00c59OSSVerify5KrLib4Spec5KStep<page_size_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode>mmap_len_boundC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv:Z_mod_multC59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib5Nodes=alloc_ceilingC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5NodesAalloc_ceiling_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes@alloc_ceiling_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5NodesDalloc_ceiling_lo_valC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00".
Import ListNotations.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma PGSZ_eq : PGSZ = 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_KStep ()) [] "p;1p;2g0000j13Tg000Nj22Tg000hj11Tf0#1#1p=0g001Mg001k#0#0#0#0#0#0#3'2o"). Qed.
Lemma page_size_eq : page_size = 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_KStep ()) [] "p;1p;2g0000j13Tg000Nj22Tg000hj11Tf0#1#1p=0g001Mg001k#0#0#0#0#0#0#3'2o"). Qed.

Lemma land_4095 : forall x, Z.land x 4095 = x mod 4096.
Proof. intros x. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma round_up_pg_aligned : forall x, x mod 4096 = 0 -> round_up_pg x = x.
Proof.
  intros x Hx. unfold round_up_pg. rewrite PGSZ_eq. change (4096 - 1) with 4095. rewrite land_4095.
  assert ((- x) mod 4096 = 0). { apply Z.mod_opp_l_z; lia. } lia.
Qed.

Lemma round_up_pg_eq : forall x, round_up_pg x = page_round_up_Z x.
Proof.
  intros x. unfold round_up_pg, page_round_up_Z. rewrite PGSZ_eq, page_size_eq. change (4096 - 1) with 4095. rewrite land_4095.
  pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)) as H1.
  pose proof (Z_div_mod_eq_full (-x) 4096) as H2.
  pose proof (Z_div_mod_eq_full (x + 4095) 4096) as H3.
  pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as H4.
  nia.
Qed.

Lemma mmap_len_ge : forall l, 0 < l -> l <= mmap_len l < l + 4096.
Proof. intros. apply mmap_len_bound. assumption. Qed.

Lemma mmap_len_aligned : forall l, (mmap_len l) mod 4096 = 0.
Proof. intros. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. apply Z_mod_mult. Qed.

Lemma mmap_len_of_aligned : forall l, 0 <= l -> l mod 4096 = 0 -> mmap_len l = l.
Proof. intros l Hl Ha. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. pose proof (Z_div_mod_eq_full l 4096). pose proof (Z_div_mod_eq_full (l + 4095) 4096). pose proof (Z.mod_pos_bound (l+4095) 4096). nia. Qed.

(* [comment removed for export] *)
Lemma alloc_ceiling_lt : alloc_ceiling < 2^63.
Proof. rewrite alloc_ceiling_val. lia. Qed.
Lemma alloc_ceiling_lo_lt : alloc_ceiling_lo <= alloc_ceiling.
Proof. rewrite alloc_ceiling_val, alloc_ceiling_lo_val. lia. Qed.
(* [comment removed for export] *)
Lemma alloc_top_lt64 : forall h, alloc_top h < 2^64 - 2^23.
Proof. intros h. unfold alloc_top, stack_max_size. pose proof (bv_unsigned_in_range 64 (vm_init_sp h)) as R. unfold bv_modulus in R. cbn in R. lia. Qed.
