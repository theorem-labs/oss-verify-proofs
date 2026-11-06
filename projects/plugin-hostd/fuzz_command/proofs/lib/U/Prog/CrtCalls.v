From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv rec_calls_equal_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition rc_of (c : rcall) (P : list (Z * Z)) : rc_entry :=
  (fst c, combine (map (fun pn => Z_to_bv 64 (fst pn)) P) (snd c)).

Fixpoint rcs (cs : list rcall) (Ps : list (list (Z * Z))) : list rc_entry :=
  match cs, Ps with
  | c :: cs', P :: Ps' => rc_of c P :: rcs cs' Ps'
  | _, _ => []
  end.

Lemma cstr_eqb_refl : forall s, cstr_eqb s s = true.
Proof. intros s. unfold cstr_eqb. destruct (list_eq_dec Z.eq_dec _ _) as [_|N]; [reflexivity | congruence]. Qed.

Lemma args_eqb_combine : forall (strs : list (list byte)) (xs ys : list word),
  length xs = length strs -> length ys = length strs -> args_eqb (combine xs strs) (combine ys strs) = true.
Proof.
  induction strs as [|s strs IH]; intros [|x xs] [|y ys] Hx Hy; cbn in Hx, Hy; try discriminate; [reflexivity|].
  cbn [combine args_eqb snd]. rewrite cstr_eqb_refl. cbn [andb]. apply IH; lia.
Qed.

Lemma calls_eqb_rcs : forall cs Ps Qs,
  length Ps = length cs -> length Qs = length cs ->
  (forall i c P, nth_error cs i = Some c -> nth_error Ps i = Some P -> length P = length (snd c)) ->
  (forall i c Q, nth_error cs i = Some c -> nth_error Qs i = Some Q -> length Q = length (snd c)) ->
  calls_eqb (rcs cs Ps) (rcs cs Qs) = true.
Proof.
  induction cs as [|c cs IH]; intros [|P Ps] [|Q Qs] HP HQ LP LQ; cbn in HP, HQ; try discriminate; [reflexivity|].
  cbn [rcs calls_eqb rc_of fst snd]. rewrite Z.eqb_refl. cbn [andb].
  rewrite args_eqb_combine; [| rewrite length_map; exact (LP 0%nat c P eq_refl eq_refl)
                            | rewrite length_map; exact (LQ 0%nat c Q eq_refl eq_refl)].
  cbn [andb]. apply IH; [lia | lia | |].
  - intros i c' P' E1 E2. exact (LP (S i) c' P' E1 E2).
  - intros i c' Q' E1 E2. exact (LQ (S i) c' Q' E1 E2).
Qed.

Lemma rcs_length : forall cs Ps, length Ps = length cs -> length (rcs cs Ps) = length cs.
Proof.
  induction cs as [|c cs IH]; intros [|P Ps] H; cbn in H |- *; try discriminate; [reflexivity|].
  f_equal. apply IH. lia.
Qed.

Lemma rcs_nth : forall cs Ps i e, nth_error (rcs cs Ps) i = Some e ->
  exists c P, nth_error cs i = Some c /\ nth_error Ps i = Some P /\ e = rc_of c P.
Proof.
  induction cs as [|c cs IH]; intros [|P Ps] i e H; cbn in H; try (destruct i; discriminate).
  destruct i as [|i]; cbn in H |- *.
  - injection H as <-. exists c, P. auto.
  - exact (IH Ps i e H).
Qed.

Lemma combine_nth : forall {X Y} (xs : list X) (ys : list Y) k x y,
  nth_error (combine xs ys) k = Some (x, y) -> nth_error xs k = Some x /\ nth_error ys k = Some y.
Proof.
  intros X Y xs. induction xs as [|a xs IH]; intros [|b ys] k x y H; cbn in H; try (destruct k; discriminate).
  destruct k as [|k]; cbn in H |- *; [injection H as <- <-; auto | exact (IH ys k x y H)].
Qed.

Lemma calls_at_rcs : forall bl m lo hi a cs Ps,
  (length cs <= 16)%nat -> length Ps = length cs ->
  (forall i c P, nth_error cs i = Some c -> nth_error Ps i = Some P ->
     call_at rsegs bl m (a + 56 * Z.of_nat i) c P /\ apart lo hi (a + 56 * Z.of_nat i) 56 /\
     (forall pn, In pn P -> apart lo hi (fst pn) (snd pn))) ->
  calls_at m lo hi a (rcs cs Ps).
Proof.
  intros bl m lo hi a cs Ps HL HP H. split; [rewrite rcs_length by exact HP; exact HL|].
  intros i e Ee. destruct (rcs_nth cs Ps i e Ee) as (c & P & Ec & EP & ->).
  destruct (H i c P Ec EP) as ((Hfn & Hn & Hl & Hb0 & Hb1 & _ & Hk) & Hap & HPa).
  unfold REC_FN_COUNT, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
  assert (LC : length (combine (map (fun pn => Z_to_bv 64 (fst pn)) P) (snd c)) = length (snd c)).
  { rewrite length_combine, length_map, Hl. lia. }
  unfold rc_of, entry_at. cbn [fst snd].
  split; [lia|]. split; [rewrite LC; exact Hn|].
  split; [apply bytes_at_app; split; [rewrite Z.add_0_r in Hb0; exact Hb0|]; rewrite length_le4, LC; exact Hb1|].
  split; [exact Hap|].
  intros k [x s] Ek. destruct (combine_nth _ _ k x s Ek) as [Ex Es].
  rewrite nth_error_map in Ex. destruct (nth_error P k) as [pn|] eqn:Ep; [|discriminate].
  cbn in Ex. injection Ex as <-.
  destruct (Hk k s pn Es Ep) as (B1 & _ & _ & Hsz & B2 & N0).
  pose proof (bytes_at_bound rsegs m _ _ B2) as R2. rewrite length_app in R2. cbn [length] in R2.
  pose proof (HPa pn (nth_error_In P k Ep)) as Ap.
  unfold arg_at. cbn [fst snd].
  split; [exact B1|].
  rewrite unsigned_lit by lia.
  split; [exact B2|]. split; [exact N0|].
  unfold apart in *. lia.
Qed.
