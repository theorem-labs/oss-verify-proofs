(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (4 recorded proofs replaced by written proofs (enf_facts, enf0_st_eq, meta_word_mod4096 and 1 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_A3 ASlot_W1 ASlot_W10 ASlot_W12.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_W13 () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C47Corelib4Init9Datatypes3fstC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC35stdpp4base6lookupI35stdpp4gmap4gmap00I59OSSVerify5KrLib6Malloc9Malloc_fp7slot_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic2or00C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:enframe_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes2idC35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib4Spec6Malloc8set_sizeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib4Spec6Malloc4wr32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C59OSSVerify5KrLib4Spec6Malloc4wr16C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W137enf0_stC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W139enf_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1N01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib6Malloc<MallocKit_AB5mw_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_wordC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<m_set_maplenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z8land_0_lK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op203I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z3lorC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z:land_assocC56Stdlib6ZArith6BinInt1Z@land_lor_distr_lC56Stdlib6ZArith6BinInt1Z9land_onesC45stdpp9bitvector;definitions@Z_to_bv_unsignedC35stdpp7tactics<f_equal_helpC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC59OSSVerify5KrLib3Lib3Mem3le1C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section ENF.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx j : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P := B + 16 + stride * idx.
Let N := UNIT * size_class j - IB.
Hypothesis UA : unk_agree st o m1.
Hypothesis J : 0 <= j < 48.
Hypothesis HA : active st j = Some g.
Hypothesis MSL : meta_slot st g.
Hypothesis MW : mw_ok mr.
Hypothesis SCg : m_sizeclass mr = j.
Hypothesis STR : stride = UNIT * size_class j.
Hypothesis SO : slot_ok st g b r idx N.
Hypothesis TK : ticks_ok st.

Lemma enf_facts : m_mem mr = Some b /\ (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b mod 16 = 0
  /\ 0 <= idx <= m_last_idx mr /\ m_last_idx mr < 32
  /\ snd b + 16 + stride * (m_last_idx mr + 1) <= round_up_pg (r_len r) /\ 16 <= stride /\ stride mod 16 = 0
  /\ (forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b -> snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b')
  /\ cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0
  /\ (forall off, 0 <= off -> 16 * off + N + 4 <= stride -> (stride * idx + 16 * off) / 16 < 65536).
Proof.
  destruct SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0 NS NOGRP HDR0 Q16 SSL MSL' AVr FRr FBr MPL SCr].
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16 |- *. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16 |- *.
  repeat (split; [assumption|]). exact Q16.
Qed.
(* [comment removed for export] *)
Definition enf0_st : mstate :=
  wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
    (wr8 (fst b, snd b + (16 + stride * idx) + -3) idx
      (wr16 (fst b, snd b + (16 + stride * idx) + -2) ((snd b + (16 + stride * idx) - (snd b + 16)) / 16) st)).

Lemma enf0_st_eq : fst (enframe_at st g idx N 0) = enf0_st /\ snd (enframe_at st g idx N 0) = (fst b, snd b + (16 + stride * idx)).
Proof.
  pose proof enf_facts as (Hmem & _).
  assert (STN : stride = N + 4) by (rewrite STR; unfold N, UNIT, IB; lia).
  unfold enframe_at. change (get_meta_rec st g) with mr. rewrite Hmem. cbn [default from_option id]. fold stride.
  change (negb (0 =? 0)) with false. cbv iota beta. unfold aadd. cbn [fst snd].
  unfold set_size. cbn [fst snd].
  replace (snd b + (UNIT + stride * idx) + (stride - IB) - (snd b + (UNIT + stride * idx)) - N) with 0 by (unfold UNIT, IB; lia).
  cbn [Z.eqb negb Z.leb]. unfold enf0_st, UNIT. split; reflexivity.
Qed.
(* [comment removed for export] *)
Lemma meta_word_mod4096 r0 : mw_ok r0 -> meta_word r0 mod 4096 = meta_word (m_set_maplen 0 r0).
Proof.
  intros (LI & FB & SC & ML). unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen m_set_maplen].
  rewrite Z.land_0_l. Z.div_mod_to_equations. lia.
Qed.

Lemma le1_lor_m64 a : 0 <= a < 32 -> le1 (Z_to_bv 64 (Z.lor a 18446744073709551552)) = [b8 (Z.lor a 192)].
Proof.
  intros Ha. unfold le1. cbn [Z_to_le_bytes]. f_equal. unfold b8. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8). change (bv_modulus 64) with (2^64).
  rewrite <- !(Z.land_ones _ 8) by lia. change (Z.ones 8) with 255.
  rewrite <- (Z.land_ones (Z.lor a 18446744073709551552) 64) by lia.
  change (Z.ones 64) with 18446744073709551615.
  rewrite !Z.land_lor_distr_l. rewrite <- !Z.land_assoc.
  change (Z.land 18446744073709551615 255) with 255. change (Z.land 18446744073709551552 255) with 192.
  change (Z.land 192 255) with 192. reflexivity.
Qed.

(* [comment removed for export] *)
Definition pp : aptr := (fst b, snd b + (16 + stride * idx)).
End ENF.


End CANSEC1.
