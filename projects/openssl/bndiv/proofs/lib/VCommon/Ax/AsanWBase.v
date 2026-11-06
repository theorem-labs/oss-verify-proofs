(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec CatSim ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition words_ok (segs : list Segment) (base : Z) (ws : list (Z * Z)) : bool :=
  forallb (fun ow => match fetch_word segs (Z_to_bv 64 (base + fst ow)) with
                     | Some x => Z.eqb (bv_unsigned x) (snd ow)
                     | None => false
                     end) ws.

Lemma words_get : forall segs base ws (o w : Z),
  words_ok segs base ws = true -> In (o, w) ws -> (0 <= w < 2 ^ 32)%Z ->
  fetch_word segs (Z_to_bv 64 (base + o)) = Some (Z_to_bv 32 w).
Proof.
  intros segs base ws o w H Hin Hw. unfold words_ok in H. rewrite forallb_forall in H.
  specialize (H _ Hin). cbn [fst snd] in H.
  destruct (fetch_word segs (Z_to_bv 64 (base + o))) as [x|]; [|discriminate].
  apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite <- H. rewrite Z_to_bv_unsigned.
  symmetry. apply bv_wrap_small. change (bv_modulus 32) with (2 ^ 32)%Z. rewrite H. exact Hw.
Qed.

(* [comment removed for export] *)
Ltac wdec :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_compute; reflexivity
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition FR (rs : list reg) (S S' : machine_state) : Prop :=
  ms_svc_pending S' = None /\ ms_rom S' = ms_rom S /\ ms_fregs S' = ms_fregs S /\ ms_fcsr S' = ms_fcsr S /\
  ms_resv S' = ms_resv S /\ ms_mem S' = ms_mem S /\ (forall r, ~ In r rs -> rg S' r = rg S r).

Lemma FR_setx : forall rs S S1 rd v p r m,
  FR rs S S1 -> (rd = 0 \/ In rd rs) -> r = ms_resv S1 -> m = ms_mem S1 -> FR rs S (setx S1 rd v p r m).
Proof.
  intros rs S S1 rd v p r m (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hrd -> ->.
  split; [reflexivity|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [exact H5|]. split; [exact H6|].
  intros r Hr. rewrite <- (H7 r Hr).
  destruct Hrd as [->|Hin]; [apply rg_setx_x0|].
  apply rg_setx_other. intros ->. exact (Hr Hin).
Qed.

Lemma FR_refl : forall rs S, ms_svc_pending S = None -> FR rs S S.
Proof. intros rs S H. unfold FR. repeat split; try reflexivity; exact H. Qed.

Lemma pc_setx : forall ms rd v p r m, ms_pc_val (setx ms rd v p r m) = p.
Proof. reflexivity. Qed.
Lemma svc_setx : forall ms rd v p r m, ms_svc_pending (setx ms rd v p r m) = None.
Proof. reflexivity. Qed.
Lemma mem_setx : forall ms rd v p r m, ms_mem (setx ms rd v p r m) = m.
Proof. reflexivity. Qed.
Lemma resv_setx : forall ms rd v p r m, ms_resv (setx ms rd v p r m) = r.
Proof. reflexivity. Qed.

Lemma inval_cases : forall a r, inval a r = r \/ inval a r = None.
Proof. intros a [r|]; cbn [inval]; [destruct (Z.eqb _ _); [right|left]; reflexivity | left; reflexivity]. Qed.

Lemma rg_0 : forall ms, rg ms 0 = w0.
Proof. reflexivity. Qed.

Lemma FR_trans : forall rs S S1 S2, FR rs S S1 -> FR rs S1 S2 -> FR rs S S2.
Proof.
  intros rs S S1 S2 (H1 & H2 & H3 & H4 & H5 & H6 & H7) (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  split; [exact G1|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
  split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite (G7 r Hr). exact (H7 r Hr).
Qed.

Lemma FR_mono : forall rs rs' S S', FR rs S S' -> (forall r, In r rs -> In r rs') -> FR rs' S S'.
Proof.
  intros rs rs' S S' (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hinc.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [exact H5|]. split; [exact H6|].
  intros r Hr. apply H7. intros Hin. exact (Hr (Hinc r Hin)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pcw (b o : Z) : word := Z_to_bv 64 (b + o).

Lemma pcw_lit : forall b o, pcw b o = Z_to_bv 64 (b + o).
Proof. reflexivity. Qed.

Lemma pcw_add : forall b o d, pcw b o + Z_to_bv 64 d = pcw b (o + d).
Proof. intros b o d. unfold pcw. rewrite zw_add. f_equal. lia. Qed.
Lemma pcw_sext : forall b o {n} (imm : bv n), pcw b o + sext 64 imm = pcw b (o + bv_signed imm).
Proof. intros b o n imm. unfold pcw. rewrite zw_add_sext. f_equal. lia. Qed.

(* [comment removed for export] *)
Lemma ret_pcw : forall b o, (0 <= b)%Z -> (b + o < 2 ^ 64)%Z -> (0 <= o)%Z -> (b mod 4 = 0)%Z -> (o mod 4 = 0)%Z ->
  bv_and (pcw b o + sext 64 (@BV 12 0 I)) (bv_not w1) = pcw b o.
Proof.
  intros b o B0 B1 Ho B4 Hm. rewrite pcw_sext. change (bv_signed (@BV 12 0 I)) with 0%Z. rewrite Z.add_0_r.
  apply bv_eq. unfold pcw. rewrite bv_and_unsigned, bv_not_unsigned. unfold w1.
  rewrite !bvu_z by lia. change (bv_wrap 64 (Z.lnot 1)) with (Z.ones 64 - 1)%Z.
  assert (E : (Z.land (b + o) (Z.ones 64 - 1) = b + o)%Z).
  { assert (Hev : ((b + o) mod 2 = 0)%Z).
    { clear -B4 Hm. lia. }
    change (Z.ones 64 - 1)%Z with (Z.lxor (Z.ones 64) 1).
    apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lxor_spec.
    destruct (Z.eq_dec n 0) as [->|Hn0].
    - assert (Hq : (b + o = 2 * ((b + o) / 2))%Z) by (pose proof (Z.div_mod (b + o) 2 ltac:(lia)); lia).
      rewrite Hq, Z.testbit_even_0. reflexivity.
    - rewrite (Z.testbit_ones 64 n) by lia. rewrite Z.bits_above_log2 with (a := 1%Z) by (cbn; lia).
      destruct (Z_lt_ge_dec n 64) as [Hlt|Hge].
      + replace ((0 <=? n) && (n <? 64))%bool with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt || apply Z.leb_le; lia).
        cbn [xorb]. rewrite andb_true_r. reflexivity.
      + replace ((0 <=? n) && (n <? 64))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
        cbn [xorb]. rewrite andb_false_r. symmetry.
        destruct (Z.eq_dec (b + o) 0) as [E0|E0]; [rewrite E0; apply Z.testbit_0_l|].
        apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
        pose proof (Z.pow_le_mono_r 2 64 n ltac:(lia) ltac:(lia)). lia. }
  rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lits :=
  repeat match goal with
  | |- context [bv_signed ?imm] =>
      is_closed_term imm; let v := eval vm_compute in (bv_signed imm) in change (bv_signed imm) with v
  | |- context [pcw ?b ?e] =>
      lazymatch e with
      | (?x + ?y)%Z => is_closed_term x; is_closed_term y;
                       let v := eval vm_compute in (x + y)%Z in change (x + y)%Z with v
      end
  end.

(* [comment removed for export] *)
Ltac cnorm :=
  repeat match goal with
  | |- context [alu64 ?op ?x ?y] =>
      is_closed_term op; is_closed_term x; is_closed_term y;
      let v := eval vm_compute in (bv_unsigned (alu64 op x y)) in
      replace (alu64 op x y) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity)
  | |- context [Z_to_bv 64 ?e] =>
      is_closed_term e;
      lazymatch e with
      | Zpos _ => fail | Z0 => fail | Zneg _ => fail
      | _ => let v := eval vm_compute in e in change e with v
      end
  end.

(* [comment removed for export] *)
Ltac rgn :=
  repeat first
   [ rewrite rg_setx_same by reflexivity
   | rewrite rg_setx_other by discriminate
   | rewrite rg_0 ].

(* [comment removed for export] *)
Ltac pcn :=
  rewrite ?pc_setx, ?svc_setx, ?mem_setx, ?resv_setx;
  repeat first [ rewrite pcw_add | rewrite pcw_sext ];
  lits.

Ltac fetch_tac F :=
  first [ exact F
        | match goal with H : ms_pc_val ?S = _ |- fetch_word _ (ms_pc_val ?S) = _ => rewrite H; exact F end ].

(* [comment removed for export] *)
Ltac wst ACC F D :=
  eapply rzc_acc;
  [ assumption
  | first [ reflexivity | assumption ]
  | eapply ACC; [ fetch_tac F | reflexivity | exact D ]
  | apply acc_ok_nil
  | try (match goal with H : ms_pc_val ?S = _ |- context [ms_pc_val ?S] => rewrite H end); pcn ].
