(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (37 recorded proofs replaced by written proofs (u32s_length, u64s_length, u32s_app and 34 more)). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Arr () := "C47Corelib7Program6Basics4flipC46Stdlib5Lists4List:length_appC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib3Lib3Arr4u32sC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3mulK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib3Lib3Mem:length_le4C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocc59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano;f_equal_natC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsCeq_rewrite_relationC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib4Init5Peano2ltI47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega:ZMicromega;ZArithProof01C47Corelib4Init5Logic7f_equalC46Stdlib5Lists4List9nth_errorI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C46Stdlib5Lists4List6nth_okC47Corelib4Init5Logic3notC46Stdlib5Lists4List>nth_error_SomeC47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3subC47Corelib5Lists7ListDef5skipnC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagI47Corelib4Init5Peano2le00C46Stdlib5Lists4List:skipn_all2C46Stdlib5Lists4List9skipn_appC46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List8firstn_0C46Stdlib5Lists4List;firstn_all2C46Stdlib5Lists4List:firstn_appC59OSSVerify5KrLib3Lib3Mem9upd_bytesC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_lec59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesc59OSSVerify5KrLib3Lib3Arr<nth_error_ltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib3Arr?nth_error_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem=bytes_at_readC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqc59OSSVerify5KrLib3Lib3Arr4u8roC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib3Lib3Mem>wr_at_store_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib3Lib3MemEbytes_at_write_insideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib3Arr=upd_app_splitC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib3Lib3Mem<bytes_at_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;wr_at_writeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib3Arr:upd_lengthC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03c59OSSVerify5KrLib3Lib3Arr;u32s_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib3Arr8u32s_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib3Arr:u32s_splitC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib5Lists4List9app_nil_lC46Stdlib5Lists4List7skipn_0C59OSSVerify5KrLib3Lib3Mem@bytes_at_ov_readC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05c59OSSVerify5KrLib3Lib3Arr=upd_bytes_midC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib3Arr;u64s_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib3Arr8u64s_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib3Arr:u64s_splitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib3Lib3MemDbytes_at_write_otherC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes:comparison00C59OSSVerify5KrLib3Lib3Mem>bytes_at_boundC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat7add_0_rK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphK46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame?wr_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

Fixpoint u32s (ws : list word) : list byte :=
  match ws with [] => [] | w :: ws' => le4 w ++ u32s ws' end.
Fixpoint u64s (ws : list word) : list byte :=
  match ws with [] => [] | w :: ws' => le8 w ++ u64s ws' end.

Lemma u32s_length : forall ws, length (u32s ws) = (4 * length ws)%nat.
Proof. induction ws; cbn -[le4]; [reflexivity|]. rewrite app_length, length_le4, IHws. lia. Qed.
Lemma u64s_length : forall ws, length (u64s ws) = (8 * length ws)%nat.
Proof. induction ws; cbn -[le8]; [reflexivity|]. rewrite app_length, length_le8, IHws. lia. Qed.

Lemma u32s_app : forall a b, u32s (a ++ b) = u32s a ++ u32s b.
Proof. induction a; intros; cbn -[le4]; [reflexivity|]. rewrite IHa, app_assoc. reflexivity. Qed.
Lemma u64s_app : forall a b, u64s (a ++ b) = u64s a ++ u64s b.
Proof. induction a; intros; cbn -[le8]; [reflexivity|]. rewrite IHa, app_assoc. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint upd {X} (l : list X) (i : nat) (x : X) : list X :=
  match l, i with
  | [], _ => []
  | _ :: l', O => x :: l'
  | y :: l', S i' => y :: upd l' i' x
  end.

Lemma upd_length : forall {X} (l : list X) i x, length (upd l i x) = length l.
Proof. induction l; intros [|i] x; cbn; auto. Qed.

Lemma upd_app_split : forall {X} (l : list X) i x, (i < length l)%nat ->
  exists pre y post, l = pre ++ y :: post /\ length pre = i /\ upd l i x = pre ++ x :: post.
Proof.
  induction l as [|z l IH]; intros i x Hi; cbn in Hi; [lia|].
  destruct i as [|i].
  - exists [], z, l. repeat split; reflexivity.
  - destruct (IH i x ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
    exists (z :: pre), y, post. split; [rewrite E at 1; reflexivity|]. split; [cbn; lia|].
    cbn. rewrite Hupd. reflexivity.
Qed.

Lemma nth_error_split : forall {X} (l : list X) i y, nth_error l i = Some y ->
  exists pre post, l = pre ++ y :: post /\ length pre = i.
Proof.
  induction l as [|z l IH]; intros [|i] y H; cbn in H; try discriminate.
  - inversion H; subst. exists [], l. split; reflexivity.
  - destruct (IH i y H) as (pre & post & -> & Hlen). exists (z :: pre), post. split; [reflexivity| cbn; lia].
Qed.

Lemma nth_error_lt : forall {X} (l : list X) i y, nth_error l i = Some y -> (i < length l)%nat.
Proof. intros X l i y H. apply nth_error_Some. rewrite H. discriminate. Qed.

Lemma upd_bytes_mid : forall (a b c bs : list byte), length bs = length b ->
  upd_bytes (a ++ b ++ c) (length a) bs = a ++ bs ++ c.
Proof.
  intros a b c bs H. unfold upd_bytes.
  rewrite firstn_app, firstn_all2, Nat.sub_diag, firstn_O, app_nil_r by lia.
  rewrite skipn_app, skipn_all2 by lia. cbn [app].
  replace (length a + length bs - length a)%nat with (length b) by lia.
  rewrite skipn_app, skipn_all2, Nat.sub_diag by lia. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

Definition u8arr (m : word -> option byte) (A : Z) (bs : list byte) : Prop :=
  bytes_at segs m A bs /\ wr_at segs m A (Z.of_nat (length bs)).
Definition u32arr (m : word -> option byte) (A : Z) (ws : list word) : Prop :=
  bytes_at segs m A (u32s ws) /\ wr_at segs m A (4 * Z.of_nat (length ws)).
Definition u64arr (m : word -> option byte) (A : Z) (ws : list word) : Prop :=
  bytes_at segs m A (u64s ws) /\ wr_at segs m A (8 * Z.of_nat (length ws)).

(* [comment removed for export] *)
Definition u8ro (m : word -> option byte) (A : Z) (bs : list byte) : Prop := bytes_at segs m A bs.

(* [comment removed for export] *)
Lemma u8arr_read : forall m A bs (i : Z) b a,
  u8arr m A bs -> nth_error bs (Z.to_nat i) = Some b -> (0 <= i)%Z -> a = wa (A + i) ->
  ov_read_bytes segs m a 1 = Some [b].
Proof.
  intros m A bs i b a [Hb _] Hn Hi ->.
  pose proof (nth_error_lt _ _ _ Hn).
  rewrite (bytes_at_read segs m A bs i 1 Hb) by lia.
  destruct (nth_error_split _ _ _ Hn) as (pre & post & E & Hlen). rewrite E at 1.
  rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity.
Qed.

Lemma u8ro_read : forall m A bs (i : Z) b a,
  u8ro m A bs -> nth_error bs (Z.to_nat i) = Some b -> (0 <= i)%Z -> a = wa (A + i) ->
  ov_read_bytes segs m a 1 = Some [b].
Proof.
  intros m A bs i b a Hb Hn Hi ->.
  pose proof (nth_error_lt _ _ _ Hn).
  rewrite (bytes_at_read segs m A bs i 1 Hb) by lia.
  destruct (nth_error_split _ _ _ Hn) as (pre & post & E & Hlen). rewrite E at 1.
  rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity.
Qed.

Lemma u8arr_store_ok : forall m A bs (i : Z) a,
  u8arr m A bs -> (0 <= i < Z.of_nat (length bs))%Z -> a = wa (A + i) ->
  store_ok segs m a 1 = true.
Proof. intros m A bs i a [_ Hw] Hi ->. eapply wr_at_store_ok; eauto; lia. Qed.

Lemma u8arr_write : forall m A bs (i : Z) (b : byte),
  u8arr m A bs -> (0 <= i < Z.of_nat (length bs))%Z ->
  u8arr (write_to_mem m (wa (A + i)) [b]) A (upd bs (Z.to_nat i) b).
Proof.
  intros m A bs i b [Hb Hw] Hi. split.
  - eapply bytes_at_ext. { apply (bytes_at_write_inside segs m A bs i [b] Hb); [lia| cbn; lia]. }
    destruct (upd_app_split bs (Z.to_nat i) b ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
    rewrite Hupd. rewrite E at 1. unfold upd_bytes. rewrite firstn_app, firstn_all2, Hlen, Nat.sub_diag by lia. cbn.
    rewrite app_nil_r. f_equal. change (y :: post) with ([y] ++ post). rewrite app_assoc, skipn_app.
    rewrite skipn_all2 by (rewrite app_length, Hlen; cbn; lia). rewrite app_length, Hlen. cbn.
    replace (Z.to_nat i + 1 - (Z.to_nat i + 1))%nat with 0%nat by lia. reflexivity.
  - rewrite upd_length. apply wr_at_write. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma u32s_split : forall ws i w, nth_error ws i = Some w ->
  exists pre post, ws = pre ++ w :: post /\ length pre = i /\
    u32s ws = u32s pre ++ le4 w ++ u32s post /\ length (u32s pre) = (4 * i)%nat.
Proof.
  intros ws i w H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen).
  exists pre, post. rewrite u32s_app. cbn -[le4]. rewrite u32s_length. repeat split; lia.
Qed.

Lemma u32arr_read : forall m A ws (i : Z) w a,
  u32arr m A ws -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 4 * i) ->
  ov_read_bytes segs m a 4 = Some (le4 w).
Proof.
  intros m A ws i w a [Hb _] Hn Hi ->.
  destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (4 * i)%Z with (Z.of_nat (4 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read segs m A (u32s ws) (4 * Z.to_nat i) 4 Hb).
  2:{ rewrite Eu, !app_length, length_le4, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
  rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma u32arr_store_ok : forall m A ws (i : Z) a,
  u32arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z -> a = wa (A + 4 * i) ->
  store_ok segs m a 4 = true.
Proof. intros m A ws i a [_ Hw] Hi ->. eapply wr_at_store_ok; eauto; lia. Qed.

Lemma u32arr_write : forall m A ws (i : Z) (v : word),
  u32arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z ->
  u32arr (write_to_mem m (wa (A + 4 * i)) (le4 v)) A (upd ws (Z.to_nat i) v).
Proof.
  intros m A ws i v [Hb Hw] Hi.
  destruct (upd_app_split ws (Z.to_nat i) v ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
  split.
  - eapply bytes_at_ext.
    { apply (bytes_at_write_inside segs m A (u32s ws) (4 * i) (le4 v) Hb); [lia|].
      rewrite length_le4, u32s_length. lia. }
    rewrite Hupd, E, !u32s_app. cbn [u32s].
    replace (Z.to_nat (4 * i)) with (length (u32s pre)) by (rewrite u32s_length; lia).
    apply upd_bytes_mid. rewrite !length_le4. reflexivity.
  - rewrite upd_length. apply wr_at_write. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma u64s_split : forall ws i w, nth_error ws i = Some w ->
  exists pre post, ws = pre ++ w :: post /\ length pre = i /\
    u64s ws = u64s pre ++ le8 w ++ u64s post /\ length (u64s pre) = (8 * i)%nat.
Proof.
  intros ws i w H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen).
  exists pre, post. rewrite u64s_app. cbn -[le8]. rewrite u64s_length. repeat split; lia.
Qed.

Lemma u64arr_read : forall m A ws (i : Z) w a,
  u64arr m A ws -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 8 * i) ->
  ov_read_bytes segs m a 8 = Some (le8 w).
Proof.
  intros m A ws i w a [Hb _] Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read segs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !app_length, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma u64arr_store_ok : forall m A ws (i : Z) a,
  u64arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z -> a = wa (A + 8 * i) ->
  store_ok segs m a 8 = true.
Proof. intros m A ws i a [_ Hw] Hi ->. eapply wr_at_store_ok; eauto; lia. Qed.

Lemma u64arr_write : forall m A ws (i : Z) (v : word),
  u64arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z ->
  u64arr (write_to_mem m (wa (A + 8 * i)) (le8 v)) A (upd ws (Z.to_nat i) v).
Proof.
  intros m A ws i v [Hb Hw] Hi.
  destruct (upd_app_split ws (Z.to_nat i) v ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
  split.
  - eapply bytes_at_ext.
    { apply (bytes_at_write_inside segs m A (u64s ws) (8 * i) (le8 v) Hb); [lia|].
      rewrite length_le8, u64s_length. lia. }
    rewrite Hupd, E, !u64s_app. cbn [u64s].
    replace (Z.to_nat (8 * i)) with (length (u64s pre)) by (rewrite u64s_length; lia).
    apply upd_bytes_mid. rewrite !length_le8. reflexivity.
  - rewrite upd_length. apply wr_at_write. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma u8arr_frame : forall m A bs a xs,
  u8arr m A bs -> (0 <= a)%Z -> (a + Z.of_nat (length xs) <= 2^64)%Z ->
  (A + Z.of_nat (length bs) <= a \/ a + Z.of_nat (length xs) <= A)%Z ->
  u8arr (write_to_mem m (wa a) xs) A bs.
Proof. intros m A bs a xs [Hb Hw] ? ? ?. split; [apply bytes_at_write_other; assumption| apply wr_at_write; assumption]. Qed.

Lemma u32arr_frame : forall m A ws a xs,
  u32arr m A ws -> (0 <= a)%Z -> (a + Z.of_nat (length xs) <= 2^64)%Z ->
  (A + 4 * Z.of_nat (length ws) <= a \/ a + Z.of_nat (length xs) <= A)%Z ->
  u32arr (write_to_mem m (wa a) xs) A ws.
Proof.
  intros m A ws a xs [Hb Hw] ? ? ?. split; [|apply wr_at_write; assumption].
  apply bytes_at_write_other; try assumption. rewrite u32s_length. lia.
Qed.

Lemma u64arr_frame : forall m A ws a xs,
  u64arr m A ws -> (0 <= a)%Z -> (a + Z.of_nat (length xs) <= 2^64)%Z ->
  (A + 8 * Z.of_nat (length ws) <= a \/ a + Z.of_nat (length xs) <= A)%Z ->
  u64arr (write_to_mem m (wa a) xs) A ws.
Proof.
  intros m A ws a xs [Hb Hw] ? ? ?. split; [|apply wr_at_write; assumption].
  apply bytes_at_write_other; try assumption. rewrite u64s_length. lia.
Qed.

Lemma u8arr_bound : forall m A bs, u8arr m A bs -> (0 <= A /\ A + Z.of_nat (length bs) <= 2^64)%Z.
Proof. intros m A bs [Hb _]. eapply bytes_at_bound; eauto. Qed.
Lemma u32arr_bound : forall m A ws, u32arr m A ws -> (0 <= A /\ A + 4 * Z.of_nat (length ws) <= 2^64)%Z.
Proof. intros m A ws [Hb _]. pose proof (bytes_at_bound _ _ _ _ Hb). rewrite u32s_length in H. lia. Qed.
Lemma u64arr_bound : forall m A ws, u64arr m A ws -> (0 <= A /\ A + 8 * Z.of_nat (length ws) <= 2^64)%Z.
Proof. intros m A ws [Hb _]. pose proof (bytes_at_bound _ _ _ _ Hb). rewrite u64s_length in H. lia. Qed.

Lemma u8ro_frame : forall m A bs a xs,
  u8ro m A bs -> (0 <= a)%Z -> (a + Z.of_nat (length xs) <= 2^64)%Z ->
  (A + Z.of_nat (length bs) <= a \/ a + Z.of_nat (length xs) <= A)%Z ->
  u8ro (write_to_mem m (wa a) xs) A bs.
Proof. intros m A bs a xs Hb ? ? ?. unfold u8ro. apply bytes_at_write_other; assumption. Qed.

(* [comment removed for export] *)
Lemma u8arr_of_rw_cells : forall m A n bs,
  rw_cells segs m A [CB n bs] -> u8arr m A bs.
Proof.
  intros m A n bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hn _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. subst n.
  split; assumption.
Qed.

Lemma rw_cells_of_u8arr : forall m A bs,
  u8arr m A bs -> rw_cells segs m A [CB (length bs) bs].
Proof.
  intros m A bs [Hb Hw]. split.
  - split. { cbn. split; [reflexivity|exact I]. }
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma upd_firstn_skipn : forall {X} (l : list X) i x, (i < length l)%nat ->
  upd l i x = firstn i l ++ x :: skipn (S i) l.
Proof.
  intros X l. induction l as [|y l IH]; intros [|i] x Hi; cbn in Hi |- *; try lia; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.

Lemma nth_error_upd_same : forall {X} (l : list X) i x, (i < length l)%nat ->
  nth_error (upd l i x) i = Some x.
Proof.
  intros X l. induction l as [|y l IH]; intros [|i] x Hi; cbn in Hi |- *; try lia; [reflexivity|].
  apply IH. lia.
Qed.

Lemma nth_error_upd_other : forall {X} (l : list X) i j x, i <> j ->
  nth_error (upd l i x) j = nth_error l j.
Proof.
  intros X l. induction l as [|y l IH]; intros [|i] [|j] x Hij; cbn; try reflexivity; [lia|].
  apply IH. lia.
Qed.

(* [comment removed for export] *)
Lemma u8arr_transport : forall W m m' A bs,
  u8arr m A bs -> munch W m m' -> wmono segs m m' ->
  disjoint_from W A (Z.of_nat (length bs)) -> u8arr m' A bs.
Proof.
  intros W m m' A bs [Hb Hw] MU WM Hd. split.
  - eapply bytes_at_transport; eauto.
  - eapply wr_at_transport; eauto.
Qed.
Lemma u32arr_transport : forall W m m' A ws,
  u32arr m A ws -> munch W m m' -> wmono segs m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr m' A ws.
Proof.
  intros W m m' A ws [Hb Hw] MU WM Hd. split.
  - eapply bytes_at_transport; eauto. rewrite u32s_length, Nat2Z.inj_mul. exact Hd.
  - eapply wr_at_transport; eauto.
Qed.
Lemma u64arr_transport : forall W m m' A ws,
  u64arr m A ws -> munch W m m' -> wmono segs m m' ->
  disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr m' A ws.
Proof.
  intros W m m' A ws [Hb Hw] MU WM Hd. split.
  - eapply bytes_at_transport; eauto. rewrite u64s_length, Nat2Z.inj_mul. exact Hd.
  - eapply wr_at_transport; eauto.
Qed.
Lemma u8ro_transport : forall W m m' A bs,
  u8ro m A bs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (length bs)) -> u8ro m' A bs.
Proof. intros W m m' A bs Hb MU Hd. eapply bytes_at_transport; eauto. Qed.

End WithSegs.
