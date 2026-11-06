From Stdlib Require Import String Ascii ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strlen_c bcmp_c rec_shape_of_c.
Import ListNotations.
Open Scope Z_scope.

Lemma g_shapes_image : image_bytes rsegs G_SHAPES 448 = Some g_shapes_bytes.
Proof.
  destruct (image_bytes rsegs G_SHAPES 448) as [bs|] eqn:E; [|vm_compute in E; discriminate].
  f_equal. apply map_unsigned_inj. revert E. vm_compute. intros E. injection E as <-. reflexivity.
Qed.

Definition rowb (r : Z * string * Z) : list byte :=
  match r with (na, _, rp) => le8 (Z_to_bv 64 na) ++ le8 (Z_to_bv 64 rp) end.

Lemma g_shapes_bytes_eq : g_shapes_bytes = concat (map rowb shape_rows).
Proof. reflexivity. Qed.

Lemma g_shapes_length : length g_shapes_bytes = 448%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma shape_rows_length : length shape_rows = 28%nat.
Proof. reflexivity. Qed.

Lemma rowb_length : forall r, length (rowb r) = 16%nat.
Proof. intros [[na nm] rp]. cbn [rowb]. rewrite length_app, !length_le8. reflexivity. Qed.

Lemma skipn_concat16 : forall (x : list (Z * string * Z)) i,
  skipn (16 * i) (concat (map rowb x)) = concat (map rowb (skipn i x)).
Proof.
  intros x. induction x as [|y x IH]; intros i.
  - cbn [map concat]. rewrite !skipn_nil. reflexivity.
  - destruct i as [|i]; [reflexivity|].
    cbn [map concat skipn]. rewrite skipn_app, skipn_all2 by (rewrite rowb_length; lia). cbn [app].
    rewrite rowb_length. replace (16 * S i - 16)%nat with (16 * i)%nat by lia. apply IH.
Qed.

Lemma firstn8_le8 : forall (x : word) l, firstn 8 (le8 x ++ l) = le8 x.
Proof.
  intros x l. rewrite firstn_app, length_le8, Nat.sub_diag, firstn_O, app_nil_r.
  apply firstn_all2. rewrite length_le8. lia.
Qed.

Lemma skipn8_le8 : forall (x : word) l, skipn 8 (le8 x ++ l) = l.
Proof.
  intros x l. rewrite skipn_app, skipn_all2 by (rewrite length_le8; lia). rewrite length_le8, Nat.sub_diag.
  reflexivity.
Qed.

Lemma row_index : forall n r rest, skipn n shape_rows = r :: rest -> (n < 28)%nat.
Proof.
  intros n r rest Hs. pose proof (f_equal (@length _) Hs) as L. rewrite length_skipn, shape_rows_length in L.
  cbn [length] in L. lia.
Qed.

Lemma row_read : forall mc n na nm rp rest,
  bytes_at rsegs mc G_SHAPES g_shapes_bytes -> skipn n shape_rows = (na, nm, rp) :: rest ->
  ov_read_bytes rsegs mc (wa (G_SHAPES + 16 * Z.of_nat n)) 8 = Some (le8 (Z_to_bv 64 na)) /\
  ov_read_bytes rsegs mc (wa (G_SHAPES + 16 * Z.of_nat n + 8)) 8 = Some (le8 (Z_to_bv 64 rp)).
Proof.
  intros mc n na nm rp rest HB Hs. pose proof (row_index n _ _ Hs) as Hn.
  assert (SK : skipn (16 * n) g_shapes_bytes = le8 (Z_to_bv 64 na) ++ le8 (Z_to_bv 64 rp) ++ concat (map rowb rest)).
  { rewrite g_shapes_bytes_eq, skipn_concat16, Hs. cbn [map concat rowb]. rewrite app_assoc. reflexivity. }
  split.
  - rewrite (bytes_at_read rsegs mc G_SHAPES g_shapes_bytes (16 * Z.of_nat n) 8 HB)
      by (rewrite ?g_shapes_length; lia).
    replace (Z.to_nat (16 * Z.of_nat n)) with (16 * n)%nat by lia. rewrite SK, firstn8_le8. reflexivity.
  - rewrite <- Z.add_assoc.
    rewrite (bytes_at_read rsegs mc G_SHAPES g_shapes_bytes (16 * Z.of_nat n + 8) 8 HB)
      by (rewrite ?g_shapes_length; lia).
    replace (Z.to_nat (16 * Z.of_nat n + 8)) with (8 + 16 * n)%nat by lia.
    rewrite <- skipn_skipn, SK, skipn8_le8, firstn8_le8. reflexivity.
Qed.

Definition name_slack (r : Z * string * Z) : list byte :=
  match r with
  | (na, nm, _) =>
      match image_bytes rsegs (na + Z.of_nat (length (str_bytes nm)) + 1) 7 with Some bs => bs | None => [] end
  end.

Definition row_ok (r : Z * string * Z) : bool :=
  match r with
  | (na, nm, rp) =>
      ro_bytes_b rsegs na (str_bytes nm ++ Z_to_bv 8 0 :: name_slack r) &&
      Nat.eqb (length (name_slack r)) 7 &&
      forallb (fun b => negb (bv_unsigned b =? 0)) (str_bytes nm) &&
      Nat.leb (length (str_bytes nm)) 16 &&
      (0 <=? na) && (na + 32 <=? 2^64) && (0 <=? rp) && (rp <? 2^64)
  end.

Lemma rows_ok : forallb row_ok shape_rows = true.
Proof. vm_compute. reflexivity. Qed.

Lemma row_ok_at : forall n r rest, skipn n shape_rows = r :: rest -> row_ok r = true.
Proof.
  intros n r rest Hs. pose proof rows_ok as H. rewrite forallb_forall in H. apply H.
  rewrite <- (firstn_skipn n shape_rows), Hs. apply in_or_app. right. left. reflexivity.
Qed.

Lemma name_facts : forall mc na nm rp, mem_inv rsegs mc -> row_ok (na, nm, rp) = true ->
  bytes_at rsegs mc na (str_bytes nm ++ Z_to_bv 8 0 :: name_slack (na, nm, rp)) /\
  ~ In (Z_to_bv 8 0) (str_bytes nm) /\
  (- (na + Z.of_nat (length (str_bytes nm)) + 1)) mod 8 <= Z.of_nat (length (name_slack (na, nm, rp))) /\
  (length (str_bytes nm) <= 16)%nat /\ 0 <= na < 2^64 /\ 0 <= rp < 2^64.
Proof.
  intros mc na nm rp MI H. unfold row_ok in H.
  repeat match type of H with
  | (_ && _) = true => apply andb_prop in H; let H2 := fresh "H" in destruct H as [H H2]
  end.
  repeat match goal with
  | H' : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H'
  | H' : Nat.leb _ _ = true |- _ => apply Nat.leb_le in H'
  | H' : Z.leb _ _ = true |- _ => apply Z.leb_le in H'
  | H' : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H'
  end.
  set (sl := name_slack (na, nm, rp)) in *.
  split; [|split; [|split; [|split; [|split]]]].
  - apply ro_bytes_at; [exact MI | lia | rewrite length_app; cbn [length]; lia |].
    apply ro_bytes_b_sound. assumption.
  - intros HIn.
    match goal with H' : forallb _ (str_bytes nm) = true |- _ =>
      rewrite forallb_forall in H'; specialize (H' _ HIn); vm_compute in H'; discriminate H' end.
  - pose proof (Z.mod_pos_bound (- (na + Z.of_nat (length (str_bytes nm)) + 1)) 8 ltac:(lia)). lia.
  - assumption.
  - lia.
  - lia.
Qed.

Lemma memcmp_model_self : forall l n, (n <= length l)%nat -> memcmp_model l l n = Some 0.
Proof.
  induction l as [|a l IH]; intros [|n] Hn; cbn in *; try reflexivity; try lia.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

Lemma memcmp_model_zero : forall l r vv, length l = length r -> memcmp_model l r (length l) = Some vv ->
  vv = 0 -> l = r.
Proof.
  induction l as [|a l IH]; intros [|b r] vv Hl Hm Hv; cbn in *; try discriminate; try reflexivity.
  destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
  - f_equal; [apply bv_eq; exact E|]. eapply IH; [lia | exact Hm | exact Hv].
  - injection Hm as <-. lia.
Qed.

Lemma memcmp_model_range : forall l r n vv, memcmp_model l r n = Some vv -> -256 < vv < 256.
Proof.
  intros l r n. revert l r. induction n as [|n IH]; intros [|a l] [|b r] vv Hm; cbn in Hm; try discriminate.
  - injection Hm as <-. lia.
  - injection Hm as <-. lia.
  - injection Hm as <-. lia.
  - injection Hm as <-. lia.
  - destruct (bv_unsigned a =? bv_unsigned b); [eapply IH; exact Hm|].
    injection Hm as <-. pose proof (byte_range a). pose proof (byte_range b). lia.
Qed.

Lemma bytes_eqb_spec : forall x y, bytes_eqb x y = true <-> x = y.
Proof.
  intros x y. unfold bytes_eqb.
  destruct (list_eq_dec Z.eq_dec (map bv_unsigned x) (map bv_unsigned y)) as [E|E]; split; intros H;
    try discriminate; try reflexivity.
  - apply map_unsigned_inj. exact E.
  - subst y. contradiction (E eq_refl).
Qed.

Lemma bytes_eqb_len : forall x y, length x <> length y -> bytes_eqb x y = false.
Proof.
  intros x y H. destruct (bytes_eqb x y) eqn:E; [|reflexivity].
  apply bytes_eqb_spec in E. subst. contradiction (H eq_refl).
Qed.

Lemma eqb_lit64 : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma eqb_lit_var : forall x (y : word), 0 <= x < 2^64 -> bv_eqb (Z_to_bv 64 x) y = Z.eqb x (bv_unsigned y).
Proof. intros x y Hx. unfold bv_eqb. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma eqb_lit_signed : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (2^63) with 9223372036854775808 in Hx, Hy.
  destruct (Z.eqb_spec x y) as [E|E]; [subst; apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E'. apply E. Z.div_mod_to_equations. lia.
Qed.

Lemma skipn_succ_cons : forall {X} (l rest : list X) n r, skipn n l = r :: rest -> skipn (S n) l = rest.
Proof.
  intros X l. induction l as [|y l IH]; intros rest n r H; destruct n; cbn in *; try discriminate.
  - inversion H; reflexivity.
  - eapply IH. exact H.
Qed.

Section Loop.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 verb len : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (lo : Z) (v : list byte).
Hypothesis STRLEN : strlen_contract.
Hypothesis BCMP : bcmp_contract.
Hypothesis HG : bytes_at rsegs m G_SHAPES g_shapes_bytes.
Hypothesis DG : G_SHAPES + 448 <= bv_unsigned sp + -64 \/ bv_unsigned sp <= G_SHAPES.
Hypothesis HLV : Z.of_nat (length v) = bv_unsigned len.
Hypothesis HV : bv_unsigned len <= 16 ->
  bytes_at rsegs m (bv_unsigned verb) v /\
  (bv_unsigned verb + bv_unsigned len <= bv_unsigned sp + -64 \/ bv_unsigned sp <= bv_unsigned verb).
Hypothesis LO : lo + 64 <= bv_unsigned sp.

Definition shape_post : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (shape_find shape_rows v)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp).

Lemma shape_exit : forall mc junk rac t0c t1c t2c s0c a0c a1c a2c a3c a4c a5c a6c a7c s2c s3c s4c s5c t3c t4c t5c t6c,
  rw_cells rsegs mc (bv_unsigned sp + -64) [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv rsegs mc -> munch [(bv_unsigned sp + -64, bv_unsigned sp)] m mc -> wmono rsegs m mc ->
  stk rsegs mc lo (bv_unsigned sp + -64) ->
  evt rsegs shape_post
    (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0c t1c t2c s0c (Z_to_bv 64 (shape_find shape_rows v))
             a0c a1c a2c a3c a4c a5c a6c a7c s2c s3c s4c s5c s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c)
        F (Z_to_bv 64 0x15480) fc None mc (seg_rom rsegs)).
Proof.
  intros mc junk rac t0c t1c t2c s0c a0c a1c a2c a3c a4c a5c a6c a7c s2c s3c s4c s5c t3c t4c t5c t6c FR MI MU WM ST.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 9 step.
  release_frame FR ST (bv_unsigned sp).
  step.
  finish.
Qed.

Lemma shape_loop : forall rest n mc junk rac t0c t1c t2c s3c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c,
  skipn n shape_rows = rest -> rest <> [] ->
  shape_find shape_rows v = shape_find rest v ->
  rw_cells rsegs mc (bv_unsigned sp + -64) [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv rsegs mc -> munch [(bv_unsigned sp + -64, bv_unsigned sp)] m mc -> wmono rsegs m mc ->
  stk rsegs mc lo (bv_unsigned sp + -64) ->
  evt rsegs shape_post
    (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0c t1c t2c len (Z_to_bv 64 SHAPE_LIT)
             a0c a1c a2c a3c a4c a5c a6c a7c verb s3c (Z_to_bv 64 (28 - Z.of_nat n))
             (Z_to_bv 64 (G_SHAPES + 8 + 16 * Z.of_nat n)) s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c)
        F (Z_to_bv 64 0x15448) fc None mc (seg_rom rsegs)).
Proof.
  induction rest as [|[[na nm] rp] rest IH];
    intros n mc junk rac t0c t1c t2c s3c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c Hs Hne Hf FR MI MU WM ST;
    [congruence|].
  pose proof (row_index n _ _ Hs) as Hn.
  pose proof (row_ok_at n _ _ Hs) as ROK.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word len) as Rlen. unfold inr64 in Rlen.
  pose proof g_shapes_length as GL.
  pose proof (skipn_succ_cons _ _ _ _ Hs) as Hs'.
  assert (LR : (n + S (length rest) = 28)%nat).
  { pose proof (f_equal (@length _) Hs) as L. rewrite length_skipn, shape_rows_length in L. cbn [length] in L. lia. }
  assert (NEXT : forall mc' rac' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
    shape_find shape_rows v = shape_find rest v ->
    rw_cells rsegs mc' (bv_unsigned sp + -64) [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    mem_inv rsegs mc' -> munch [(bv_unsigned sp + -64, bv_unsigned sp)] m mc' -> wmono rsegs m mc' ->
    stk rsegs mc' lo (bv_unsigned sp + -64) ->
    evt rsegs shape_post
      (MS (mkR rac' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2' len (Z_to_bv 64 SHAPE_LIT)
               a0' a1' a2' a3' a4' a5' a6' a7' verb (Z_to_bv 64 na) (Z_to_bv 64 (28 - Z.of_nat n))
               (Z_to_bv 64 (G_SHAPES + 8 + 16 * Z.of_nat n)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x1546c) fc None mc' (seg_rom rsegs))).
  { intros mc' rac' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Hf' FR' MI' MU' WM' ST'.
    step. step. step.
    rewrite eqb_lit64 by lia.
    destruct (Z.eqb_spec (28 - Z.of_nat n + -1) 0) as [E0|E0]; cbn [negb].
    - assert (EN : rest = []) by (destruct rest; [reflexivity | cbn [length] in LR; lia]). rewrite EN in Hf'.
      step.
      replace (Z_to_bv 64 SHAPE_LIT) with (Z_to_bv 64 (shape_find shape_rows v)) by (rewrite Hf'; reflexivity).
      eapply shape_exit; eassumption.
    - replace (Z_to_bv 64 (28 - Z.of_nat n + -1)) with (Z_to_bv 64 (28 - Z.of_nat (S n))) by (f_equal; lia).
      replace (Z_to_bv 64 (G_SHAPES + 8 + 16 * Z.of_nat n + 16))
        with (Z_to_bv 64 (G_SHAPES + 8 + 16 * Z.of_nat (S n))) by (f_equal; lia).
      eapply IH; try eassumption.
      destruct rest; [cbn [length] in LR; lia | discriminate]. }
  assert (HGc : bytes_at rsegs mc G_SHAPES g_shapes_bytes).
  { eapply bytes_at_transport; [exact HG | exact MU |]. cbn [disjoint_from]. rewrite GL. split; [lia | exact I]. }
  destruct (row_read mc n na nm rp rest HGc Hs) as [RD1 _].
  destruct (name_facts mc na nm rp MI ROK) as (NB & NZ & NSL & NL & Rna & Rrp).
  clear ROK.
  replace (G_SHAPES + 16 * Z.of_nat n) with (G_SHAPES + 8 + 16 * Z.of_nat n + -8) in RD1 by lia.
  step. clear RD1. step. step.
  eapply evt_cut.
  { eapply STRLEN with (str := str_bytes nm) (slack := name_slack (na, nm, rp)).
    - rewrite unsigned_lit by lia. exact NB.
    - exact NZ.
    - rewrite unsigned_lit by lia. exact NSL.
    - exact MI. }
  post_call rsegs mc.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
  clear POST.
  step.
  rewrite eqb_lit_var by lia.
  destruct (Z.eqb_spec (Z.of_nat (length (str_bytes nm))) (bv_unsigned len)) as [EL|EL]; cbn [negb].
  2: {
    apply NEXT; try assumption.
    rewrite Hf. cbn [shape_find]. rewrite bytes_eqb_len by (intros E; apply EL; rewrite E, HLV; reflexivity).
    reflexivity. }
  destruct (HV ltac:(lia)) as [HVB DV].
  assert (HVc : bytes_at rsegs m1 (bv_unsigned verb) v).
  { eapply bytes_at_transport; [exact HVB | exact MU |]. cbn [disjoint_from]. rewrite HLV. split; [lia | exact I]. }
  clear HVB.
  pose proof (proj1 (bytes_at_app rsegs m1 na (str_bytes nm) (Z_to_bv 8 0 :: name_slack (na, nm, rp))) NB) as [NBs _].
  assert (LV : length (str_bytes nm) = length v) by lia.
  destruct (memcmp_model_total (str_bytes nm) v (length (str_bytes nm)) ltac:(lia) ltac:(lia)) as [vv Hvv].
  step. step. step. step.
  eapply evt_cut.
  { eapply BCMP with (ls := str_bytes nm) (rs := v) (v := vv).
    - rewrite unsigned_lit by lia. exact NBs.
    - exact HVc.
    - replace (Z.to_nat (bv_unsigned len)) with (length (str_bytes nm)) by lia. exact Hvv.
    - exact MI1. }
  post_call rsegs m1.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
  match goal with H : mem_inv rsegs m2 |- _ => rename H into MI2 end.
  step.
  rewrite (eqb_lit_signed vv 0) by (pose proof (memcmp_model_range _ _ _ _ Hvv); lia).
  destruct (Z.eqb_spec vv 0) as [E0|E0]; cbn [negb].
  - pose proof (memcmp_model_zero _ _ _ LV Hvv E0) as EQ.
    destruct (row_read m2 n na nm rp rest HGc Hs) as [_ RD2].
    replace (G_SHAPES + 16 * Z.of_nat n + 8) with (G_SHAPES + 8 + 16 * Z.of_nat n) in RD2 by lia.
    step.
    assert (EF : shape_find shape_rows v = rp).
    { rewrite Hf. cbn [shape_find]. rewrite (proj2 (bytes_eqb_spec _ _) EQ). reflexivity. }
    replace (Z_to_bv 64 rp) with (Z_to_bv 64 (shape_find shape_rows v)) by (rewrite EF; reflexivity).
    eapply shape_exit; eassumption.
  - apply NEXT; try assumption.
    rewrite Hf. cbn [shape_find].
    assert (EB : bytes_eqb (str_bytes nm) v = false).
    { destruct (bytes_eqb (str_bytes nm) v) eqn:B; [|reflexivity].
      apply bytes_eqb_spec in B. rewrite <- B in Hvv. rewrite memcmp_model_self in Hvv by lia.
      injection Hvv as <-. contradiction (E0 eq_refl). }
    rewrite EB. reflexivity.
Qed.

End Loop.

Theorem rec_shape_of_holds : strlen_contract -> bcmp_contract -> rec_shape_of_contract.
Proof.
  intros STRLEN BCMP. unfold rec_shape_of_contract, REC_SHAPE_OF, REC_SHAPE_OF_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo v
    MI ST LO HG DG HLV HV.
  assert (HG0 : True -> bytes_at rsegs m G_SHAPES g_shapes_bytes) by (intros _; exact HG).
  clear HG.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  carve_frame 64%nat ST.
  do 15 step.
  replace (Z_to_bv 64 141008) with (Z_to_bv 64 (G_SHAPES + 8 + 16 * Z.of_nat 0)) by reflexivity.
  replace (Z_to_bv 64 28) with (Z_to_bv 64 (28 - Z.of_nat 0)) by reflexivity.
  eapply (shape_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m lo v STRLEN BCMP (HG0 I))
    with (rest := shape_rows) (n := 0%nat).
  all: first [ eassumption | reflexivity | discriminate | lia ].
Qed.
