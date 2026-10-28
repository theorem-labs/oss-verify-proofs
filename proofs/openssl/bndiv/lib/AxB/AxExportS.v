(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Mem Cells.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface RT_state RT_main_shape.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.VCommon Require Import FastWord.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExBytes AxLazy AxLin AxVal.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.VCommon.Ax Require ExLoad.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AxA Require Import AxExportQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
Record bforms : Type := BForms {
  bf_sp0 : lin; bf_top : lin; bf_PRB : lin; bf_SB : lin; bf_PAB : lin; bf_T : lin; bf_TCX : lin; bf_DTV : lin;
  bf_FSB : lin; bf_DNB : lin; bf_SSB : lin; bf_f0 : Z; bf_tid : lin
}.

Definition lb_form (F : bforms) (b : lbase) : lin :=
  match b with
  | LB_lit => (0, []) | LB_sp0 => bf_sp0 F | LB_top => bf_top F | LB_PRB => bf_PRB F | LB_SB => bf_SB F
  | LB_RIS => laddc (bf_SB F) (2 ^ 37) | LB_PAB => bf_PAB F | LB_T => bf_T F | LB_TCX => bf_TCX F | LB_DTV => bf_DTV F
  | LB_FSB => bf_FSB F | LB_DNB => bf_DNB F | LB_SSB => bf_SSB F | LB_ACEIL => laddc (bf_sp0 F) (- STACK_WIN)
  end.

(* [comment removed for export] *)
Definition ldiv8 (f : lin) : option lin :=
  if forallb (fun t => snd t mod 8 =? 0) (snd f) then Some (fst f / 8, map (fun t => (fst t, snd t / 8)) (snd f)) else None.

Definition sa_form (F : bforms) (a : saddr) : option lin :=
  match a with
  | SA b off => Some (laddc (lb_form F b) off)
  | SAsh b off shoff => match ldiv8 (laddc (lb_form F b) off) with Some g => Some (laddc g (SHB + shoff)) | None => None end
  end.

Section Den.
Variable ρ : valuation.
Variable F : bforms.
Variable maps0 : list (word * word).
Variable al0 : list (Z * Z).

Definition L_of : layoutA :=
  mkLayoutA (leval ρ (bf_sp0 F)) (leval ρ (bf_top F)) (leval ρ (bf_PRB F)) (leval ρ (bf_SB F)) (leval ρ (bf_PAB F))
            (leval ρ (bf_T F)) (leval ρ (bf_TCX F)) (leval ρ (bf_DTV F)) (leval ρ (bf_FSB F)) (leval ρ (bf_DNB F))
            (leval ρ (bf_SSB F)) (bf_f0 F) (leval ρ (bf_tid F)) maps0 al0.

Lemma den_base_form (b : lbase) : den_base L_of b = leval ρ (lb_form F b).
Proof.
  destruct b; cbn [den_base lb_form L_of l_sp0 l_top l_PRB l_SB l_PAB l_T l_TCX l_DTV l_FSB l_DNB l_SSB]; try reflexivity.
  - rewrite leval_laddc. reflexivity.
  - unfold l_ACEIL, L_of. cbn [l_sp0]. rewrite leval_laddc. lia.
Qed.

Lemma teval_div8 (ts : terms) : forallb (fun t => snd t mod 8 =? 0) ts = true ->
  teval ρ ts = 8 * teval ρ (map (fun t => (fst t, snd t / 8)) ts).
Proof.
  induction ts as [|[x a] r IH]; intros H; [reflexivity|]. cbn [forallb snd] in H. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. cbn [map teval fst snd]. rewrite (IH H2).
  pose proof (Z.div_mod a 8 ltac:(lia)) as D. rewrite H1 in D. nia.
Qed.

Lemma ldiv8_sound (f g : lin) : ldiv8 f = Some g -> leval ρ g = leval ρ f / 8.
Proof.
  unfold ldiv8. destruct (forallb (fun t => snd t mod 8 =? 0) (snd f)) eqn:E; [|discriminate]. intros H. injection H as <-.
  unfold leval. cbn [fst snd]. rewrite (teval_div8 _ E). rewrite (Z.mul_comm 8), Z.div_add by lia. reflexivity.
Qed.

Lemma sa_form_sound (a : saddr) (f : lin) : sa_form F a = Some f -> leval ρ f = den_addr L_of a.
Proof.
  destruct a as [b off|b off shoff]; cbn [sa_form den_addr].
  - intros H. injection H as <-. rewrite leval_laddc, den_base_form. reflexivity.
  - destruct (ldiv8 (laddc (lb_form F b) off)) as [g|] eqn:E; [|discriminate]. intros H. injection H as <-.
    rewrite leval_laddc, (ldiv8_sound _ _ E), leval_laddc, den_base_form. unfold shad. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition exp_lit (w : nat) (v : Z) : list xbe := map (fun j => EL (zbyte (v mod 2 ^ 64) j)) (seq 0 w).
Definition exp_form (w : nat) (f : lin) : list xbe := map (fun j => EF (snd f) (wofZ (fst f)) j) (seq 0 w).

Definition wok (w : nat) : bool := Nat.eqb w 1 || Nat.eqb w 2 || Nat.eqb w 4 || Nat.eqb w 8.

Definition exp_cell (c : scell) : option (list xbe) :=
  match c with
  | SC_lit w v => if wok w then Some (exp_lit w v) else None
  | SC_ptr a => match sa_form F a with Some f => Some (exp_form 8 f) | None => None end
  | SC_num w LN_f0 => if wok w then Some (exp_lit w (bf_f0 F)) else None
  | SC_num w LN_tid => if wok w then Some (exp_form w (bf_tid F)) else None
  | SC_bytes bs => Some (map (fun b => EL (b mod 256)) bs)
  | SC_any n => Some (repeat EA n)
  end.

Fixpoint exp_cells (cs : list scell) : option (list xbe) :=
  match cs with
  | [] => Some []
  | c :: r => match exp_cell c, exp_cells r with Some a, Some b => Some (a ++ b) | _, _ => None end
  end.

(* [comment removed for export] *)
Lemma le_bytes_unique (k : nat) (V : Z) (bs : list byte) : 0 <= V -> length bs = k ->
  (forall j, (j < k)%nat -> bv_unsigned (nth j bs (Z_to_bv 8 0)) = zbyte V j) -> bs = Z_to_le_bytes k V.
Proof.
  intros HV HL H. apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [rewrite length_Z_to_le_bytes; exact HL|].
  intros j Hj. rewrite HL in Hj. apply bv_eq. rewrite (H j Hj), (ExLoad.Z_to_le_bytes_nth k V j HV Hj). reflexivity.
Qed.

Lemma F2_seq (P : nat -> byte -> Prop) (f : nat -> xbe) (R : xbe -> byte -> Prop) :
  (forall j b, R (f j) b -> P j b) ->
  forall (k s : nat) (bs : list byte), Forall2 R (map f (seq s k)) bs ->
  length bs = k /\ forall j, (j < k)%nat -> P (s + j)%nat (nth j bs (Z_to_bv 8 0)).
Proof.
  intros HP. induction k as [|k IH]; intros s bs H; cbn [seq map] in H.
  - inversion H; subst. split; [reflexivity | intros j Hj; lia].
  - inversion H as [|? b ? bs' Hb Hr]; subst. destruct (IH (S s) bs' Hr) as [L1 L2]. split; [cbn [length]; lia|].
    intros j Hj. destruct j as [|j]; cbn [nth]; [rewrite Nat.add_0_r; exact (HP _ _ Hb)|].
    replace (s + S j)%nat with (S s + j)%nat by lia. apply L2. lia.
Qed.

Lemma exp_lit_bytes (w : nat) (v : Z) (bs : list byte) : Forall2 (xbe_den ρ) (exp_lit w v) bs ->
  bs = Z_to_le_bytes w (v mod 2 ^ 64).
Proof.
  intros H. pose proof (Z.mod_pos_bound v (2 ^ 64) ltac:(lia)) as Hv.
  destruct (F2_seq (fun j b => bv_unsigned b = zbyte (v mod 2 ^ 64) j) (fun j => EL (zbyte (v mod 2 ^ 64) j)) (xbe_den ρ)
              ltac:(intros j b Hb; cbn [xbe_den] in Hb; subst b; rewrite Z_to_bv_unsigned; apply bv_wrap_small; pose proof (zbyte_range (v mod 2 ^ 64) j); change (bv_modulus 8) with 256; lia)
              w 0%nat bs H) as [L1 L2].
  apply le_bytes_unique; [lia | exact L1 | exact L2].
Qed.

Lemma exp_form_bytes (w : nat) (f : lin) (bs : list byte) : Forall2 (xbe_den ρ) (exp_form w f) bs ->
  bs = Z_to_le_bytes w (leval ρ f mod 2 ^ 64).
Proof.
  intros H. pose proof (Z.mod_pos_bound (leval ρ f) (2 ^ 64) ltac:(lia)) as Hv.
  assert (Es : smod ρ (snd f) (wofZ (fst f)) = leval ρ f mod 2 ^ 64).
  { unfold smod, leval. rewrite wZ_wofZ. unfold FastWord.two64. rewrite Zplus_mod_idemp_r. f_equal. lia. }
  destruct (F2_seq (fun j b => bv_unsigned b = zbyte (leval ρ f mod 2 ^ 64) j) (fun j => EF (snd f) (wofZ (fst f)) j) (xbe_den ρ)
              ltac:(intros j b Hb; cbn [xbe_den] in Hb; rewrite Es in Hb; exact Hb) w 0%nat bs H) as [L1 L2].
  apply le_bytes_unique; [lia | exact L1 | exact L2].
Qed.

Lemma wcell_bytes (w : nat) (v : Z) : wok w = true -> cbytes (wcell w v) = Z_to_le_bytes w (v mod 2 ^ 64) /\ cell_wf (wcell w v).
Proof.
  unfold wok. intros H.
  assert (Hc : w = 1%nat \/ w = 2%nat \/ w = 4%nat \/ w = 8%nat).
  { repeat (apply orb_prop in H as [H|H]); apply Nat.eqb_eq in H; auto. }
  assert (Eu : bv_unsigned (Z_to_bv 64 v) = v mod 2 ^ 64) by (rewrite Z_to_bv_unsigned; reflexivity).
  destruct Hc as [->|[->|[->| ->]]]; cbn [wcell cbytes cell_wf]; (split; [|exact I]).
  - cbn [Z_to_le_bytes]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
    change (2 ^ 64) with (2 ^ 8 * 2 ^ 56). rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. symmetry. apply Z.mod_mod. lia.
  - unfold le2. rewrite Eu. reflexivity.
  - unfold le4. rewrite Eu. reflexivity.
  - unfold le8, word_to_le_bytes. rewrite Eu. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exp_cell_sound (c : scell) (es : list xbe) (bs : list byte) : exp_cell c = Some es -> Forall2 (xbe_den ρ) es bs ->
  exists junk, cell_wf (den_cell L_of c junk) /\ cbytes (den_cell L_of c junk) = bs.
Proof.
  destruct c as [w v|a|w n|l|n]; cbn [exp_cell den_cell]; intros He HF.
  - destruct (wok w) eqn:Ew; [|discriminate]. injection He as <-. exists []. destruct (wcell_bytes w v Ew) as [E1 E2].
    split; [exact E2|]. rewrite E1. symmetry. exact (exp_lit_bytes w v bs HF).
  - destruct (sa_form F a) as [f|] eqn:Ef; [|discriminate]. injection He as <-. exists []. split; [exact I|].
    cbn [cbytes]. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. rewrite (exp_form_bytes 8 f bs HF), (sa_form_sound a f Ef). reflexivity.
  - destruct n.
    + destruct (wok w) eqn:Ew; [|discriminate]. injection He as <-. exists []. cbn [den_num L_of l_f0].
      destruct (wcell_bytes w (bf_f0 F) Ew) as [E1 E2]. split; [exact E2|]. rewrite E1. symmetry. exact (exp_lit_bytes w _ bs HF).
    + destruct (wok w) eqn:Ew; [|discriminate]. injection He as <-. exists []. cbn [den_num L_of l_tid].
      destruct (wcell_bytes w (leval ρ (bf_tid F)) Ew) as [E1 E2]. split; [exact E2|]. rewrite E1. symmetry. exact (exp_form_bytes w _ bs HF).
  - injection He as <-. exists []. cbn [cell_wf cbytes]. split; [apply length_map|].
    clear -HF. revert bs HF. induction l as [|z l IH]; intros bs HF; cbn [map] in *; inversion HF as [|? b ? bs' Hb Hr]; subst; [reflexivity|].
    f_equal; [|exact (IH _ Hr)]. cbn [xbe_den] in Hb. subst b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 8) with 256. symmetry. apply Z.mod_mod. lia.
  - injection He as <-. exists bs. cbn [cell_wf cbytes]. split; [|reflexivity].
    rewrite <- (Forall2_length HF). apply repeat_length.
Qed.

(* [comment removed for export] *)
Theorem exp_cells_sound (cs : list scell) : forall (es : list xbe) (bs : list byte), exp_cells cs = Some es ->
  Forall2 (xbe_den ρ) es bs ->
  exists junks, cells_wf (den_cells L_of cs junks) /\ cells_bytes (den_cells L_of cs junks) = bs.
Proof.
  induction cs as [|c r IH]; intros es bs He HF; cbn [exp_cells] in He.
  - injection He as <-. inversion HF; subst. exists []. split; [exact I | reflexivity].
  - destruct (exp_cell c) as [a|] eqn:Ea; [|discriminate]. destruct (exp_cells r) as [b|] eqn:Eb; [|discriminate]. injection He as <-.
    apply Forall2_app_inv_l in HF as (b1 & b2 & F1 & F2 & ->).
    destruct (exp_cell_sound c a b1 Ea F1) as (junk & W1 & B1). destruct (IH b b2 eq_refl F2) as (junks & W2 & B2).
    exists (junk :: junks). cbn [den_cells hd tl cells_wf cells_bytes]. split; [split; assumption|]. rewrite B1, B2. reflexivity.
Qed.

Lemma exp_cells_size (cs : list scell) : forall (es : list xbe) junks, exp_cells cs = Some es -> cells_wf (den_cells L_of cs junks) ->
  length es = cells_size (den_cells L_of cs junks).
Proof.
  induction cs as [|c r IH]; intros es junks He Hw; cbn [exp_cells] in He.
  - injection He as <-. reflexivity.
  - destruct (exp_cell c) as [a|] eqn:Ea; [|discriminate]. destruct (exp_cells r) as [b|] eqn:Eb; [|discriminate]. injection He as <-.
    cbn [den_cells cells_wf cells_size] in *. destruct Hw as [W1 W2]. rewrite length_app, (IH b (tl junks) eq_refl W2). f_equal.
    clear -Ea W1. destruct c as [w v|a0|w n|l|n]; cbn [exp_cell den_cell] in *.
    + destruct (wok w) eqn:Ew; [|discriminate]. injection Ea as <-. unfold exp_lit. rewrite length_map, length_seq.
      unfold wok in Ew. repeat (apply orb_prop in Ew as [Ew|Ew]); apply Nat.eqb_eq in Ew; subst w; reflexivity.
    + destruct (sa_form F a0); [|discriminate]. injection Ea as <-. reflexivity.
    + destruct n; (destruct (wok w) eqn:Ew; [|discriminate]); injection Ea as <-; unfold exp_lit, exp_form; rewrite length_map, length_seq;
        unfold wok in Ew; repeat (apply orb_prop in Ew as [Ew|Ew]); apply Nat.eqb_eq in Ew; subst w; reflexivity.
    + injection Ea as <-. rewrite length_map. cbn [csize]. reflexivity.
    + injection Ea as <-. rewrite repeat_length. reflexivity.
Qed.

End Den.
