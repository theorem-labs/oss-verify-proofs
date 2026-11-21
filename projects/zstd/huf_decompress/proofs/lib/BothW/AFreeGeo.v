(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (9 recorded proofs replaced by written proofs (slot_geo, slot_sep_objects, slot_rng and 6 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ARep ARepQ ARepFrame ALayout AHeapP AModelFacts.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AFreeGeo () := "C59OSSVerify5KrLib5BothW9ARepFrameCsize_of_class_factsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib5BothW4ARep7aregionC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C46Stdlib5Lists4List2InC59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init9Datatypes6option00I35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupK59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib5BothW9ARepFrame>slot_in_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<slot_alignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout=alayout_spaceC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3appK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib5BothW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayoutAalayout_slot_disjC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeGeo8slot_geoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4arngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout7al_dtlsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib5BothW4ARep8afreearrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_chunks_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF7rng_subC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib5BothW9ARepFrame8shad_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame9shlen_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4RSECC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW7ALayout:alayout_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib5BothW9ARepFrame>slots_disjointC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z;lt_ge_casesK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec8AsanCtrl6rz_logC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeGeo<rz_log_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib5BothW;AModelFacts:rz_size_eqC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1N01C59OSSVerify5KrLib4Spec8AsanCtrl3rupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeGeo=rz_size_factsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeGeoBrounded_size_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8granulesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section Slot.
Variables (L : alayout) (st : astate) (X : aconc) (c k : Z).
Hypothesis ALO : alayout_ok L.
Hypothesis WF : awf L st X.
Hypothesis HC : 1 <= c < K_NUM_CLASSES.
Hypothesis KR : 0 <= k < ndist st c.

Let S := size_of_class c.
Let AB := aslot_addr L c k.

Lemma slot_geo :
     16 <= S <= 65536 /\ S mod 16 = 0 /\ AB mod 16 = 0
  /\ aregion L c <= AB /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)
  /\ c_allocated_user (get_cls st c) <= c_mapped_user (get_cls st c) /\ c_mapped_user (get_cls st c) <= K_FREEARR_OFF
  /\ al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE
  /\ 0x10007fff8000 <= AB /\ AB + S <= ATOP
  /\ aregion L c mod 8 = 0 /\ c_mapped_user (get_cls st c) mod 8 = 0.
Proof.
  pose proof (size_of_class_facts c HC) as [S1 S2].
  destruct WF as (SBE & PAE & SAL & SLO & SHI & PERC & _).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & _).
  pose proof (slot_in_region L st c k ltac:(fold S; lia) ltac:(lia) KR) as (G1 & G2 & G3).
  pose proof (slot_aligned L c k SAL HC) as AL16.
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  assert (R8 : aregion L c mod 8 = 0 /\ c_mapped_user (get_cls st c) mod 8 = 0).
  { generalize SAL A4. clear. unfold aregion, K_REGION, K_USER_MAP, K_ALIGN. intros. Z.div_mod_to_equations. lia. }
  assert (RS : al_space_beg L <= aregion L c /\ aregion L c + K_FREEARR_OFF <= al_space_beg L + K_SPACE_SIZE).
  { generalize HC. clear. unfold aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, K_NUM_CLASSES. change (2^37) with 137438953472. change (2^32) with 4294967296. intros. lia. }
  subst S AB. generalize S1 S2 A1 A2 G1 G2 G3 AL16 SP1 SP2 R8 RS. clear. unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF. intros. repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma slot_sep_objects :
     (al_t L + 4096 <= AB \/ AB + S <= al_t L) /\ (al_ctx L + 65536 <= AB \/ AB + S <= al_ctx L)
  /\ (al_nodes L + 1048576 <= AB \/ AB + S <= al_nodes L) /\ (al_store L + 8388608 <= AB \/ AB + S <= al_store L)
  /\ (al_fake L + 11571200 <= AB \/ AB + S <= al_fake L).
Proof.
  pose proof slot_geo as (S1 & _ & _ & _ & _ & _ & _ & G7 & G8 & _).
  exact (alayout_slot_disj L AB S ALO G7 G8 ltac:(lia)).
Qed.

Lemma slot_rng : forall RNG, arng L RNG st -> rng RNG AB S /\ rng RNG (shad AB) (shlen S).
Proof.
  intros RNG (_ & _ & _ & _ & _ & _ & _ & _ & _ & RC & _). destruct (RC c HC) as (R1 & R2 & _).
  pose proof slot_geo as (S1 & S2 & AL & G1 & G2 & G3 & G4 & _ & _ & _ & _ & R8 & M8).
  split.
  - eapply rng_sub; [exact R1| lia| lia].
  - eapply rng_sub; [exact R2| |].
    + rewrite !shad_div. generalize G1 R8. clear. intros. Z.div_mod_to_equations. lia.
    + rewrite !shad_div, !shlen_div. generalize G1 G2 G3 R8 M8 S1. clear. intros. Z.div_mod_to_equations. lia.
Qed.
End Slot.

(* [comment removed for export] *)
Lemma slots_sep_any : forall L st X c1 k1 c2 k2,
  alayout_ok L -> awf L st X -> 1 <= c1 < K_NUM_CLASSES -> 1 <= c2 < K_NUM_CLASSES ->
  0 <= k1 < ndist st c1 -> 0 <= k2 < ndist st c2 -> (c1 <> c2 \/ k1 <> k2) ->
  aslot_addr L c1 k1 + size_of_class c1 <= aslot_addr L c2 k2 \/ aslot_addr L c2 k2 + size_of_class c2 <= aslot_addr L c1 k1.
Proof.
  intros L st X c1 k1 c2 k2 ALO WF H1 H2 K1 K2 NE.
  pose proof (slot_geo L st X c1 k1 ALO WF H1 K1) as (S1 & _ & _ & G1 & G2 & G3 & G4 & _).
  pose proof (slot_geo L st X c2 k2 ALO WF H2 K2) as (T1 & _ & _ & F1 & F2 & F3 & F4 & _).
  destruct (Z.eq_dec c1 c2) as [<-|NC].
  - apply (slots_disjoint L c1 k1 k2); lia.
  - generalize S1 G1 G2 G3 G4 T1 F1 F2 F3 F4 NC. clear. unfold aregion, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296.
    intros. destruct (Z.lt_ge_cases c1 c2); [left| right]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros n. unfold rz_log. repeat (destruct (_ <=? _)); lia. Qed.
Lemma rz_size_facts : forall n, 0 <= n -> 16 <= rz_size n <= 2048 /\ rz_size n mod 16 = 0.
Proof.
  intros n Hn. rewrite rz_size_eq. pose proof (rz_log_range n) as R.
  assert (E : exists i, (i <= 7)%nat /\ rz_log n = Z.of_nat i) by (exists (Z.to_nat (rz_log n)); split; lia).
  destruct E as (i & Hi & ->). do 8 (destruct i as [|i]; [cbn; lia|]). lia.
Qed.

Lemma rounded_size_facts : forall n, 0 <= n -> n <= rounded_size n /\ 8 <= rounded_size n /\ rounded_size n mod 8 = 0 /\ rup n 8 <= rounded_size n
  /\ rounded_size n <= n + 15.
Proof.
  intros n Hn. unfold rounded_size, rup. Z.div_mod_to_equations. nia.
Qed.

Section Chunk.
Variables (L : alayout) (st : astate) (X : aconc) (c k n : Z).
Hypothesis ALO : alayout_ok L.
Hypothesis WF : awf L st X.
Hypothesis HC : 1 <= c < K_NUM_CLASSES.
Hypothesis KR : 0 <= k < ndist st c.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : rounded_size n + rz_size n <= size_of_class c.
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let hm := UB - 16.

Lemma chunk_geo :
     hm mod 16 = 0 /\ UB mod 16 = 0 /\ AB + 16 <= UB /\ AB <= hm
  /\ 0x10007fff8000 <= hm /\ UB + rup n 8 <= AB + S /\ AB + S <= ATOP /\ hm + 16 + rup n 8 <= ATOP /\ n <= 65536 /\ n <= Q_MAX
  /\ 0x10007fff8000 <= AB /\ n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0 /\ 8 <= S - rz_size n.
Proof.
  pose proof (slot_geo L st X c k ALO WF HC KR) as (S1 & S2 & AL & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
  pose proof (rz_size_facts n N0) as [RZ1 RZ2]. pose proof (rounded_size_facts n N0) as (RS1 & RS2 & RS3 & RS4 & RS5).
  subst S AB UB hm. generalize S1 S2 AL G1 G2 G7 G8 RZ1 RZ2 RS1 RS2 RS3 RS4 RS5 FIT N0. clear. unfold Q_MAX, rup. intros. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma chunk_shadow_geo :
     shad UB = shad AB + shlen (rz_size n) /\ 2 <= shlen (rz_size n)
  /\ shlen (rup n 8) = granules n /\ 0 <= shlen (rup n 8)
  /\ shlen (rz_size n) + granules n <= shlen S
  /\ 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fff8000
  /\ shad (aregion L c) <= shad AB /\ shad AB + shlen S <= shad (aregion L c) + shlen (c_mapped_user (get_cls st c)).
Proof.
  pose proof (slot_geo L st X c k ALO WF HC KR) as (S1 & S2 & AL & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).
  pose proof (rz_size_facts n N0) as [RZ1 RZ2]. pose proof (rounded_size_facts n N0) as (RS1 & RS2 & RS3 & RS4 & RS5).
  subst S AB UB hm. unfold granules. rewrite !shad_div, !shlen_div.
  generalize S1 S2 AL G1 G2 G3 G4 G5 G6 G7 G8 R8 M8 RZ1 RZ2 RS1 RS2 RS3 RS4 RS5 FIT N0. clear. unfold ASHOFF, rup, K_FREEARR_OFF, K_SPACE_SIZE. intros.
  Z.div_mod_to_equations. lia.
Qed.
End Chunk.
End CANSEC1.
