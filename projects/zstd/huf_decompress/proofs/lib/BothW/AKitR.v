(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (15 recorded proofs replaced by written proofs (words4_of_bytes_ok, u32arr_of_CB, u32arr_of_junk and 12 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ABytes ARep ARepKit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AKitR () := "C47Corelib7Program6Basics4flipC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02c59OSSVerify5KrLib5BothW5AKitR?words4_of_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9and_morphK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init3Nat3addC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib3Lib3Arr4u32sC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ABytes<le4_of_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib5Lists4List9app_nil_rI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW5AKitRBwords4_of_bytes_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2or00c59OSSVerify5KrLib5BothW5AKitR<u32arr_of_CBC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z3maxK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib3Lib3Arr;u32s_lengthC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c59OSSVerify5KrLib5BothW5AKitRBrw_cells_of_u32arrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC46Stdlib5Lists4List=length_firstnI47Corelib4Init5Peano2le00C47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Peano2ltC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init5Logic3notC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specK46Stdlib9micromega7EnvRing5PExpr07C47Corelib5Lists7ListDef5skipnC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib5Lists4List<firstn_skipnC46Stdlib5Lists4List>nth_error_app1C59OSSVerify5KrLib3Lib3Arr8u32s_appC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib5Lists4List<length_skipnC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List>nth_error_app2C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib5Lists4List:firstn_allC56Stdlib5Arith8PeanoNat3Nat8sub_diagC46Stdlib5Lists4List:firstn_appC46Stdlib5Lists4List:length_appc59OSSVerify5KrLib5BothW5AKitR=u32arr_firstnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW5AKitR=u32arr_skipn'C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9skipn_appC46Stdlib5Lists4List9skipn_allC46Stdlib5Lists4List9in_or_appC46Stdlib5Lists4List2InI47Corelib5Lists7ListDef6Forall00I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List=Forall_forallK47Corelib4Init5Logic2or02C46Stdlib5Lists4List=firstn_firstnK47Corelib4Init5Logic2or01C47Corelib4Init5Logic5proj1C46Stdlib5Lists4ListAfirstn_skipn_commc59OSSVerify5KrLib5BothW5AKitRCForall_firstn_skipnC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7and_indC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List=Exists_existsc59OSSVerify5KrLib5BothW5AKitR;outside_In'C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef:Forall_indC59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Fixpoint words4_of_bytes (bs : list byte) : list word :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: rest => le_bytes_to_word [b0;b1;b2;b3] :: words4_of_bytes rest
  | _ => []
  end.

Lemma words4_of_bytes_ok : forall k bs, length bs = (4 * k)%nat ->
  u32s (words4_of_bytes bs) = bs /\ length (words4_of_bytes bs) = k.
Proof.
  induction k as [|k IH]; intros bs L.
  - destruct bs; [split; reflexivity| cbn in L; lia].
  - destruct bs as [|b0 [|b1 [|b2 [|b3 rest]]]]; cbn in L; try lia.
    destruct (IH rest ltac:(lia)) as [U Lk].
    cbn [words4_of_bytes u32s length]. rewrite le4_of_bytes by reflexivity. cbn. rewrite U, Lk. split; reflexivity.
Qed.

Lemma u32arr_of_CB : forall m A k bs,
  rw_cells bsegs m A [CB (4 * k) bs] -> u32arr bsegs m A (words4_of_bytes bs) /\ length (words4_of_bytes bs) = k.
Proof.
  intros m A k bs [[WF BA] WR]. cbn in WF. destruct WF as [L _].
  destruct (words4_of_bytes_ok k bs ltac:(lia)) as [U Lk].
  split; [|exact Lk]. split.
  - rewrite U. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA. exact BA.
  - rewrite Lk. cbn [cells_size csize Nat.add] in WR. replace (4 * Z.of_nat k) with (Z.of_nat (4 * k + 0)) by lia. exact WR.
Qed.

Lemma u32arr_of_junk : forall m A n, junk_at m A (4 * n) -> 0 <= n ->
  exists ws, u32arr bsegs m A ws /\ length ws = Z.to_nat n.
Proof.
  intros m A n [bs H] Hn. replace (Z.to_nat (4 * n)) with (4 * Z.to_nat n)%nat in H by lia.
  destruct (u32arr_of_CB m A (Z.to_nat n) bs H) as [U L]. exists (words4_of_bytes bs). split; assumption.
Qed.

Lemma rw_cells_of_u32arr : forall m A ws,
  u32arr bsegs m A ws -> rw_cells bsegs m A [CB (4 * length ws) (u32s ws)].
Proof.
  intros m A ws [B W]. split; [split|].
  - cbn. split; [apply u32s_length| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. replace (Z.of_nat (4 * length ws + 0)) with (4 * Z.of_nat (length ws)) by lia. exact W.
Qed.

Lemma junk_of_u32arr : forall m A ws, u32arr bsegs m A ws -> junk_at m A (4 * Z.of_nat (length ws)).
Proof.
  intros m A ws U. exists (u32s ws). replace (Z.to_nat (4 * Z.of_nat (length ws))) with (4 * length ws)%nat by lia.
  apply rw_cells_of_u32arr. exact U.
Qed.

Lemma u32arr_firstn : forall m A ws k, u32arr bsegs m A ws -> (k <= length ws)%nat ->
  u32arr bsegs m A (firstn k ws).
Proof.
  intros m A ws k [[B0 [B1 B]] [W0 [W1 W]]] K. rewrite u32s_length in B1.
  split.
  - split; [lia|]. split; [rewrite u32s_length, length_firstn; lia|].
    intros i Hi. rewrite u32s_length, length_firstn in Hi.
    specialize (B i ltac:(rewrite u32s_length; lia)). rewrite B.
    rewrite <- (firstn_skipn k ws) at 1. rewrite u32s_app, nth_error_app1 by (rewrite u32s_length, length_firstn; lia). reflexivity.
  - split; [lia|]. split; [rewrite length_firstn; lia|].
    intros i Hi. rewrite length_firstn in Hi. apply W. lia.
Qed.

Lemma u32arr_skipn' : forall m A ws k, u32arr bsegs m A ws -> (k <= length ws)%nat ->
  u32arr bsegs m (A + 4 * Z.of_nat k) (skipn k ws).
Proof.
  intros m A ws k [[B0 [B1 B]] [W0 [W1 W]]] K. rewrite u32s_length in B1.
  split.
  - split; [lia|]. split; [rewrite u32s_length, length_skipn; lia|].
    intros i Hi. rewrite u32s_length, length_skipn in Hi.
    specialize (B (4 * k + i)%nat ltac:(rewrite u32s_length; lia)).
    replace (A + Z.of_nat (4 * k + i)) with (A + 4 * Z.of_nat k + Z.of_nat i) in B by lia. rewrite B.
    rewrite <- (firstn_skipn k ws) at 1. rewrite u32s_app, nth_error_app2 by (rewrite u32s_length, length_firstn; lia).
    rewrite u32s_length, length_firstn. f_equal. lia.
  - split; [lia|]. split; [rewrite length_skipn; lia|].
    intros i Hi. rewrite length_skipn in Hi. specialize (W (4 * Z.of_nat k + i) ltac:(lia)).
    replace (A + (4 * Z.of_nat k + i)) with (A + 4 * Z.of_nat k + i) in W by lia. exact W.
Qed.

Lemma u32arr_app_inv : forall m A ws1 ws2, u32arr bsegs m A (ws1 ++ ws2) ->
  u32arr bsegs m A ws1 /\ u32arr bsegs m (A + 4 * Z.of_nat (length ws1)) ws2.
Proof.
  intros m A ws1 ws2 U. split.
  - replace ws1 with (firstn (length ws1) (ws1 ++ ws2)) by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn; rewrite app_nil_r; reflexivity).
    apply u32arr_firstn; [exact U| rewrite length_app; lia].
  - pose proof (u32arr_skipn' m A (ws1 ++ ws2) (length ws1) U ltac:(rewrite length_app; lia)) as V.
    rewrite skipn_app, skipn_all, Nat.sub_diag in V. exact V.
Qed.

(* [comment removed for export] *)
Lemma junk_of_cb : forall m A k bs, rw_cells bsegs m A [CB (Z.to_nat k) bs] -> junk_at m A k.
Proof. intros m A k bs H. exists bs. exact H. Qed.

Lemma junk_at_eq : forall m A A' n n', junk_at m A n -> A = A' -> n = n' -> junk_at m A' n'.
Proof. intros m A A' n n' H <- <-. exact H. Qed.

Lemma Forall_firstn_skipn : forall {A} (P : A -> Prop) (l : list A) n k h,
  Forall P (firstn n l) -> (k + h <= n)%nat -> Forall P (firstn h (skipn k l)).
Proof.
  intros A P l n k h HF LE. rewrite firstn_skipn_comm.
  apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) HF x).
  assert (IN : In x (firstn (k + h) l)).
  { rewrite <- (firstn_skipn k (firstn (k + h) l)). apply in_or_app. right. exact Hx. }
  rewrite <- (firstn_skipn (k + h) (firstn n l)) . apply in_or_app. left.
  rewrite firstn_firstn. replace (Nat.min (k + h) n) with (k + h)%nat by lia. exact IN.
Qed.

Lemma u32arr_addr_eq : forall m A A' ws, u32arr bsegs m A ws -> A = A' -> u32arr bsegs m A' ws.
Proof. intros m A A' ws H <-. exact H. Qed.

(* [comment removed for export] *)
Lemma outside_In' : forall W x jv, outside W x -> In jv W -> ~ (fst jv <= x < snd jv).
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x jv Ho Hin; [tauto|].
  destruct Ho as [H1 H2]. destruct Hin as [<-|Hin]; [exact H1| exact (IH _ _ H2 Hin)].
Qed.
Lemma sub_fp_by_incl' : forall W W',
  Forall (fun iv => Exists (fun jv => fst jv <= fst iv /\ snd iv <= snd jv) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x Ho. induction HF as [|[lo hi] W HE HF IH]; cbn; [exact I|].
  split; [| exact IH]. apply Exists_exists in HE. destruct HE as (jv & Hin & H1 & H2). cbn in H1, H2.
  pose proof (outside_In' W' x jv Ho Hin). lia.
Qed.
(* [comment removed for export] *)
End CANSEC1.
(* [comment removed for export] *)
Ltac find_ivw_syn :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_tl; find_ivw_syn ].
Ltac find_ivw_tac tac :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_hd; cbn [fst snd]; solve [tac]
        | apply Exists_cons_tl; find_ivw_tac tac ].
Ltac find_ivw tac := first [ find_ivw_syn | find_ivw_tac tac ].
Ltac solve_sub_fpw tac :=
  apply sub_fp_by_incl'; repeat (apply Forall_cons; [find_ivw tac|]); apply Forall_nil.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma munch_trans_w : forall W W1 W2 m m1 m', munch W1 m m1 -> munch W2 m1 m' -> sub_fp W1 W -> sub_fp W2 W -> munch W m m'.
Proof. intros W W1 W2 m m1 m' A B S1 S2. eapply munch_trans; [eapply munch_weaken; [exact S1| exact A] | eapply munch_weaken; [exact S2| exact B]]. Qed.
End CANSEC2.
