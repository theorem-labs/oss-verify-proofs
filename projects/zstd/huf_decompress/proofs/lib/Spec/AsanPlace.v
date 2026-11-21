(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (6 recorded proofs replaced by written proofs (zsizes_app, zargmin, pgup_facts and 3 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import MState.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import AsanInv.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanPlace () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes3appc59OSSVerify5KrLib4Spec9AsanPlace6zsizesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01C47Corelib4Init9Datatypes3sndK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic8eq_ind_rK47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes8list_indI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib4Init5Logic3notC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2or01C47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC56Stdlib6ZArith6BinInt1Z2gtI47Corelib4Init6Specif7sumbool00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes6option02K47Corelib4Init5Logic2or02K46Stdlib9micromega6VarMap1t01C47Corelib4Init9Datatypes3fstK46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init5Logic2or00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op206K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05c59OSSVerify5KrLib4Spec9AsanPlace4pgupC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega=RingMicromega3Op205C47Corelib4Init9Datatypes6lengthI47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z6of_natc59OSSVerify5KrLib4Spec9AsanPlace:pgup_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2geC47Corelib4Init5Logic8iff_reflK47Corelib5Lists7ListDef6Forall01c59OSSVerify5KrLib4Spec9AsanPlace7zargminC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8in_splitC47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List:Forall_appC46Stdlib5Lists4List?Forall_cons_iffc59OSSVerify5KrLib4Spec9AsanPlace:zsizes_appC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07C47Corelib4Init5Logic3iffC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List=Forall_forallC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz03K47Corelib5Lists7ListDef6Forall02C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z3subC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op204C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succI46Stdlib5Lists4List6Exists00C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC46Stdlib5Lists4List6filterC46Stdlib5Lists4List9filter_Inc59OSSVerify5KrLib4Spec9AsanPlace5meetsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1c59OSSVerify5KrLib4Spec9AsanPlace8free_gapC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geK47Corelib4Init9Datatypes4bool02C46Stdlib5Lists4List7existsbK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeK47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib4Spec9AsanPlace4zentC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC47Corelib4Init9Datatypes4negbC45stdpp9bitvector;definitions;bv_unsignedC46Stdlib4Bool4Bool=negb_true_iffK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool;andb_true_rC47Corelib5Lists7ListDef3map".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint zsizes (l : list (Z * Z)) : Z := match l with [] => 0 | e :: l' => snd e + zsizes l' end.

Lemma zsizes_app : forall l1 l2, zsizes (l1 ++ l2) = zsizes l1 + zsizes l2.
Proof. induction l1 as [|e l1 IH]; intros; cbn; [reflexivity| rewrite IH; lia]. Qed.

Lemma zargmin : forall (l : list (Z * Z)), l <> [] -> exists e, In e l /\ forall e', In e' l -> fst e <= fst e'.
Proof.
  induction l as [|e l IH]; intros Hne; [congruence|].
  destruct l as [|e2 l2].
  - exists e. split; [left; reflexivity|]. intros e' [<-|[]]. lia.
  - destruct (IH ltac:(discriminate)) as (m & Hm & Hmin).
    destruct (Z_le_gt_dec (fst e) (fst m)).
    + exists e. split; [left; reflexivity|]. intros e' [<-|Hin]; [lia|]. specialize (Hmin e' Hin). lia.
    + exists m. split; [right; exact Hm|]. intros e' [<-|Hin]; [lia|]. apply Hmin. exact Hin.
Qed.

Definition pgup (x : Z) : Z := (x + 4095) / 4096 * 4096.
Lemma pgup_facts : forall x, pgup x mod 4096 = 0 /\ x <= pgup x <= x + 4095.
Proof. intros x. unfold pgup. split; [apply Z_mod_mult|]. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma free_gap : forall (n : nat) (l : list (Z * Z)) (lo hi G : Z),
  length l = n -> 0 <= G -> Forall (fun e => 0 <= snd e) l ->
  (hi - lo) - zsizes l >= (Z.of_nat n + 1) * (G + 4095) ->
  exists g, g mod 4096 = 0 /\ lo <= g /\ g + G <= hi /\ Forall (fun e => g + G <= fst e \/ fst e + snd e <= g) l.
Proof.
  induction n as [|n IH]; intros l lo hi G Hlen HG Hpos Hroom.
  - destruct l; [|discriminate]. cbn [zsizes] in Hroom.
    exists (pgup lo). pose proof (pgup_facts lo) as [HM HR].
    split; [exact HM|]. split; [lia|]. split; [lia| constructor].
  - destruct l as [|e0 l0]; [discriminate|].
    destruct (zargmin (e0 :: l0) ltac:(discriminate)) as (m & Hm & Hmin).
    apply in_split in Hm as (l1 & l2 & El). rewrite El in *.
    assert (Hlen' : length (l1 ++ l2) = n) by (rewrite length_app in *; cbn in Hlen; lia).
    assert (Hpos' : Forall (fun e => 0 <= snd e) (l1 ++ l2)).
    { apply Forall_app in Hpos as [P1 P2]. apply Forall_cons_iff in P2 as [_ P2]. apply Forall_app. split; assumption. }
    assert (Hm0 : 0 <= snd m). { apply Forall_app in Hpos as [_ P2]. apply Forall_cons_iff in P2 as [P _]. exact P. }
    rewrite zsizes_app in Hroom. cbn [zsizes] in Hroom.
    destruct (Z_le_gt_dec (lo + G + 4095) (fst m)) as [Hfar|Hnear].
    + (* [comment removed for export] *)
      exists (pgup lo). pose proof (pgup_facts lo) as [HM HR].
      split; [exact HM|]. split; [lia|].
      assert (ZS : 0 <= zsizes l1 /\ 0 <= zsizes l2).
      { apply Forall_app in Hpos' as [P1 P2]. split; [clear -P1; induction l1 as [|x l1 IH1]| clear -P2; induction l2 as [|x l2 IH1]]; cbn; try lia;
          match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H as [Hx H]; specialize (IH1 H); lia end. }
      split; [nia|].
      rewrite Forall_forall. intros e' He'. left. specialize (Hmin e' He'). lia.
    + (* [comment removed for export] *)
      set (lo' := Z.max lo (fst m + snd m)).
      destruct (IH (l1 ++ l2) lo' hi G Hlen' HG Hpos') as (g & G1 & G2 & G3 & G4).
      { subst lo'. rewrite zsizes_app. nia. }
      exists g. split; [exact G1|]. split; [lia|]. split; [exact G3|].
      apply Forall_app in G4 as [G4a G4b]. apply Forall_app. split; [exact G4a|]. constructor; [|exact G4b].
      right. lia.
Qed.

(* [comment removed for export] *)
Definition meets (lo hi : Z) (e : Z * Z) : bool := (fst e <? hi) && (lo <? fst e + snd e).

Lemma free_gap_filter : forall (l : list (Z * Z)) (lo hi G N T : Z),
  0 <= G -> Forall (fun e => 0 <= snd e) l ->
  Z.of_nat (length (List.filter (meets lo hi) l)) <= N -> zsizes (List.filter (meets lo hi) l) <= T ->
  0 <= N -> (hi - lo) - T >= (N + 1) * (G + 4095) ->
  exists g, g mod 4096 = 0 /\ lo <= g /\ g + G <= hi /\ Forall (fun e => g + G <= fst e \/ fst e + snd e <= g) l.
Proof.
  intros l lo hi G N T HG Hpos HN HT HN0 Hroom.
  destruct (free_gap (length (List.filter (meets lo hi) l)) (List.filter (meets lo hi) l) lo hi G eq_refl HG) as (g & G1 & G2 & G3 & G4).
  - apply Forall_forall. intros e He. apply filter_In in He as [He _]. exact (proj1 (Forall_forall _ _) Hpos e He).
  - nia.
  - exists g. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
    apply Forall_forall. intros e He.
    destruct (meets lo hi e) eqn:Em.
    + apply (proj1 (Forall_forall _ _) G4). apply filter_In. split; assumption.
    + unfold meets in Em. apply andb_false_iff in Em as [Em|Em]; [apply Z.ltb_ge in Em; left| apply Z.ltb_ge in Em; right]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zent (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (snd e)).

Lemma region_free_of_clear : forall (maps : list (word * word)) (g G : Z),
  0 <= g -> 0 <= G -> g + G < 2^64 ->
  Forall (fun e => g + G <= fst e \/ fst e + snd e <= g) (map zent maps) ->
  region_free maps (Z_to_bv 64 g) (Z_to_bv 64 G) = true.
Proof.
  induction maps as [|[a sz] maps IH]; intros g G Hg HG Hhi HF; [reflexivity|].
  cbn [map zent fst snd] in HF. apply Forall_cons_iff in HF as [H1 HF].
  cbn [region_free]. rewrite (IH g G Hg HG Hhi HF), andb_true_r.
  unfold iv_overlap. rewrite !unsigned_lit by lia. unfold zent in H1. cbn [fst snd] in H1.
  apply negb_true_iff. apply andb_false_iff.
  destruct H1 as [H1|H1]; [right| left]; apply Z.ltb_ge; lia.
Qed.

