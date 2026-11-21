(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (7 recorded proofs replaced by written proofs (dd_key_some, dd_has_add, dd_cov_empty and 4 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import PropExec CatExec MemSplit AxSymExec3 AxSymExec3Sound AsanPlanCore.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_LogDedupe () := "C69OSSVerify5KrLib2AS:AxSymExec33AX26pt_gssC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib2AS:AxSymExec33AX26pt_gsoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX2;pt_get_leafC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2AS<AsanPlanCore3APC6dd_keyC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K69OSSVerify5KrLib2AS:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic7f_equalK47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1Z03K69OSSVerify5KrLib2AS:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX24expr04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX24expr06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX24expr07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX24expr08C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic9False_indI47Corelib7Numbers7BinNums8positive00I69OSSVerify5KrLib2AS:AxSymExec33AX25saddr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I69OSSVerify5KrLib2AS:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00I47Corelib4Init9Datatypes4bool00C69OSSVerify5KrLib2AS<AsanPlanCore3APC6dd_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS<AsanPlanCore3APC6dd_hasC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2AS<AsanPlanCore3APC6dd_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26pt_getC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C69OSSVerify5KrLib2AS<AsanPlanCore3APC6dd_othC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS<AsanPlanCore3APC6ddseen01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List7existsbC56Stdlib6PArith6BinPos3Pos6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C69OSSVerify5KrLib2AS:AxSymExec33AX26pt_setC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib4Bool4Bool8orb_propC56Stdlib5Arith8PeanoNat3Nat6eqb_eqc59OSSVerify5KrLib2AS9LogDedupe;dd_key_someC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02I47Corelib4Init5Logic2or00C69OSSVerify5KrLib2AS:AxSymExec33AX29saddr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S<saddr_eqb_eqC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes4andbK47Corelib4Init9Datatypes4bool01I69OSSVerify5KrLib2AS<AsanPlanCore3APC6ddseen00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K69OSSVerify5KrLib2AS:AxSymExec33AX25ptree01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9LogDedupe6dd_covC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2ex00I69OSSVerify5KrLib2AS:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S8log_flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS<AsanPlanCore3APC9log_dd_goC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S9mem_denotC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX26sentry01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00C69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S6estartC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S6flat_uC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib2AS7CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9LogDedupe:dd_has_addC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib2AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib2AS8MemSplit>wbytes_outsideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3nthC59OSSVerify5KrLib2AS8MemSplit=wbytes_insideC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03I69OSSVerify5KrLib2AS:AxSymExec33AX26sentry00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00C69OSSVerify5KrLib2AS<AsanPlanCore3APC6log_ddC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9LogDedupe<dd_cov_emptyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9LogDedupe?mem_denot_dd_goC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityc59OSSVerify5KrLib2AS9LogDedupe>log_flat_dd_goC1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC.
Open Scope Z_scope.

Lemma dd_key_some : forall a p, dd_key a = Some p -> a = SA (ELit 0) (Zpos p).
Proof.
  intros [b k] p H. unfold dd_key in H.
  repeat match type of H with context [match ?t with _ => _ end] => destruct t; try discriminate end.
  injection H as <-. reflexivity.
Qed.

Lemma dd_has_add : forall s a w a' w',
  dd_has (dd_add s a w) a' w' = true -> (a' = a /\ w' = w) \/ dd_has s a' w' = true.
Proof.
  intros s a w a' w' H. unfold dd_has, dd_add in *.
  destruct (dd_key a) as [p|] eqn:Ka; destruct (dd_key a') as [p'|] eqn:Ka'; cbn [dd_lit dd_oth] in H.
  - destruct (Pos.eq_dec p' p) as [->|Hne].
    + rewrite pt_gss in H. cbn [existsb] in H. apply orb_prop in H as [H|H].
      * left. apply Nat.eqb_eq in H. split; [|exact H]. rewrite (dd_key_some _ _ Ka), (dd_key_some _ _ Ka'). reflexivity.
      * right. revert H. destruct (pt_get (dd_lit s) p); intro H; [exact H | discriminate].
    + right. rewrite pt_gso in H by exact Hne. exact H.
  - right. exact H.
  - right. exact H.
  - cbn [existsb fst snd] in H. apply orb_prop in H as [H|H]; [left | right; exact H].
    apply andb_prop in H as [H1 H2]. apply saddr_eqb_eq in H1. apply Nat.eqb_eq in H2. split; assumption.
Qed.

(* [comment removed for export] *)
Definition dd_cov (E : env) (s : ddseen) (x : word) : Prop :=
  exists a w, dd_has s a w = true
              /\ bv_unsigned (adenot E a) <= bv_unsigned x < bv_unsigned (adenot E a) + Z.of_nat w.

Lemma dd_cov_empty : forall E x, ~ dd_cov E (DDS PTLeaf []) x.
Proof.
  intros E x (a & w & H & _). unfold dd_has in H. cbn [dd_lit dd_oth] in H.
  destruct (dd_key a); [rewrite pt_get_leaf in H|]; cbn in H; discriminate.
Qed.

Lemma mem_denot_dd_go : forall E base log s, log_flat E log ->
  forall x, ~ dd_cov E s x -> mem_denot E base (log_dd_go s log) x = mem_denot E base log x.
Proof.
  intros E base log. induction log as [|[a w v] older IH]; intros s Hlf x Hx; [reflexivity|].
  cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfa & Hlf').
  assert (HA : bv_unsigned (adenot E a) + Z.of_nat (length (word_to_le_bytes w (edenot E v))) <= 2 ^ 64).
  { rewrite length_N_to_le_bytes, (flat_u E a _ Hfa). destruct Hfa as (?&?&?&?). lia. }
  assert (Hnew : forall a' w', dd_has (dd_add s a w) a' w' = true ->
            bv_unsigned (adenot E a') <= bv_unsigned x < bv_unsigned (adenot E a') + Z.of_nat w' ->
            bv_unsigned (adenot E a) <= bv_unsigned x < bv_unsigned (adenot E a) + Z.of_nat w).
  { intros a' w' Hh' Hr. apply dd_has_add in Hh' as [[-> ->]|Hh']; [exact Hr|].
    exfalso. apply Hx. exists a', w'. split; assumption. }
  cbn [log_dd_go]. destruct (dd_has s a w) eqn:Hh; cbn [mem_denot].
  - (* [comment removed for export] *)
    rewrite wbytes_outside; [apply IH; assumption | exact HA |].
    rewrite length_N_to_le_bytes.
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (adenot E a))) as [L|G]; [left; exact L|].
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (adenot E a) + Z.of_nat w)) as [L2|G2]; [|right; exact G2].
    exfalso. apply Hx. exists a, w. split; [exact Hh | lia].
  - (* [comment removed for export] *)
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (adenot E a))) as [L|G].
    + rewrite !wbytes_outside by (first [exact HA | left; exact L]).
      apply IH; [exact Hlf'|]. intros (a' & w' & Hh' & Hr). pose proof (Hnew a' w' Hh' Hr). lia.
    + destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (adenot E a) + Z.of_nat w)) as [L2|G2].
      * rewrite !wbytes_inside by (first [exact HA | rewrite length_N_to_le_bytes; lia]). reflexivity.
      * rewrite !wbytes_outside by (first [exact HA | right; rewrite length_N_to_le_bytes; exact G2]).
        apply IH; [exact Hlf'|]. intros (a' & w' & Hh' & Hr). pose proof (Hnew a' w' Hh' Hr). lia.
Qed.

Lemma mem_denot_dd : forall E base log, log_flat E log -> mem_denot E base (log_dd log) = mem_denot E base log.
Proof.
  intros E base log Hlf. apply functional_extensionality. intro x.
  apply mem_denot_dd_go; [exact Hlf | apply dd_cov_empty].
Qed.

Lemma log_flat_dd_go : forall E log s, log_flat E log -> log_flat E (log_dd_go s log).
Proof.
  intros E log. induction log as [|[a w v] older IH]; intros s H; [exact I|].
  cbn [log_flat] in H. destruct H as (H1 & H2 & H3). cbn [log_dd_go].
  destruct (dd_has s a w); [apply IH; exact H3|].
  cbn [log_flat]. split; [exact H1|]. split; [exact H2|]. apply IH. exact H3.
Qed.

Lemma log_flat_dd : forall E log, log_flat E log -> log_flat E (log_dd log).
Proof. intros E log H. apply log_flat_dd_go. exact H. Qed.
