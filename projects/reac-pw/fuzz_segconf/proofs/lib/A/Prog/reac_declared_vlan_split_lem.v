(* reac_declared_vlan_split on fuzz_segconf image A: the facts of its walk that do not name the machine.

   1. vs_code: SegModel.vlan_split in the order the compiled code tests it (0x89bf4 dot NULL, 0x89bf8 dot =
      segment, 0x89c14 dot[1] = 0, the digit loop 0x89c24-0x89c4c, the range test 0x89c80, name_ok 0x89d0c), and
      vs_code_eq: the two agree on a NUL-free segment of at most 15 bytes (the contract's premise). On such a
      segment the code's tests of plen + 1 against cap = 16 (0x89cbc, 0x89cc4) and of strlen against 16 (0x89cd8)
      never fire: vs_plen_small, vs_len_test.
   2. The byte lists of the wrappers' contracts (list byte) and SegModel's texts (list Z): zb, zs_zb.
   3. The branch words of the tests, as the walk reads them (unsigned 64-bit compares): vs_digit_test (0x89c28,
      `a4 - 48 >u 9`), vs_range_test (0x89c80, `v - 4095 >=u -4094`), vs_len_test (0x89cd8,
      `len - 16 <u -17`). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 1. the model in the code's order                                                                          *)
(* ---------------------------------------------------------------------------------------------------------- *)

Definition vs_code (s : list Z) : option (list Z * Z) :=
  match strrchr s DOT with
  | None => None
  | Some di =>
    if (di =? 0)%nat then None else
    match skipn (S di) s with
    | [] => None
    | _ :: _ =>
      if negb (forallb isdigit (skipn (S di) s)) then None else
      if (strtol10 (skipn (S di) s) <? 1) || (4094 <? strtol10 (skipn (S di) s)) then None else
      if name_ok (firstn di s) then Some (firstn di s, strtol10 (skipn (S di) s)) else None
    end
  end.

Lemma vs_di_lt : forall s di, nulfree s -> strrchr s DOT = Some di -> (di < length s)%nat.
Proof. intros s di Hn Hd. apply strrchr_lt in Hd. rewrite cut_nul_id in Hd by exact Hn. exact Hd. Qed.

Lemma vs_code_eq : forall s, nulfree s -> (length s < 16)%nat -> vlan_split s = vs_code s.
Proof.
  intros s Hn Hl. unfold vlan_split, vs_code.
  destruct (strrchr s DOT) as [di|] eqn:Hd; [|reflexivity].
  pose proof (vs_di_lt s di Hn Hd) as Hdi.
  destruct (Nat.eqb_spec di 0) as [H0|H0]; cbn [orb]; [reflexivity|].
  assert (Ht : nulfree (skipn (S di) s)) by (apply nulfree_skipn, Hn).
  rewrite (hd0_eq0 _ Ht). rewrite (cut_nul_id _ Ht).
  destruct (skipn (S di) s) as [|t tl] eqn:Es; [reflexivity|].
  destruct (forallb isdigit (t :: tl)); cbn [negb]; [|reflexivity].
  destruct ((strtol10 (t :: tl) <? 1) || (4094 <? strtol10 (t :: tl))) eqn:Hr; [reflexivity|].
  apply orb_false_iff in Hr as [Hr1 Hr2]. apply Z.ltb_ge in Hr1. apply Z.ltb_ge in Hr2.
  destruct (Nat.ltb_spec 16 (di + 1)); [lia|]. cbn [orb].
  rewrite (strlen_id _ Hn). destruct (Nat.ltb_spec 16 (length s + 1)); [lia|].
  destruct (name_ok (firstn di s)); cbn [negb]; [|reflexivity].
  rewrite Z.mod_small by lia. reflexivity.
Qed.

(* the exits of the code, each as the walk meets it *)
Lemma vs_none_dot : forall s, strrchr s DOT = None -> vs_code s = None.
Proof. intros s H. unfold vs_code. rewrite H. reflexivity. Qed.
Lemma vs_none_first : forall s, strrchr s DOT = Some 0%nat -> vs_code s = None.
Proof. intros s H. unfold vs_code. rewrite H. reflexivity. Qed.
Lemma vs_none_empty : forall s di, strrchr s DOT = Some di -> skipn (S di) s = [] -> vs_code s = None.
Proof. intros s di H He. unfold vs_code. rewrite H, He. destruct (di =? 0)%nat; reflexivity. Qed.
Lemma vs_none_nodigit : forall s di, strrchr s DOT = Some di ->
  forallb isdigit (skipn (S di) s) = false -> vs_code s = None.
Proof.
  intros s di H Hf. unfold vs_code. rewrite H, Hf. destruct (di =? 0)%nat; [reflexivity|].
  destruct (skipn (S di) s); reflexivity.
Qed.
Lemma vs_none_range : forall s di, strrchr s DOT = Some di ->
  (strtol10 (skipn (S di) s) <? 1) || (4094 <? strtol10 (skipn (S di) s)) = true -> vs_code s = None.
Proof.
  intros s di H Hr. unfold vs_code. rewrite H, Hr. destruct (di =? 0)%nat; [reflexivity|].
  destruct (skipn (S di) s); [reflexivity|]. destruct (negb _); reflexivity.
Qed.
Lemma vs_name : forall s di, strrchr s DOT = Some di -> di <> 0%nat -> skipn (S di) s <> [] ->
  forallb isdigit (skipn (S di) s) = true ->
  (strtol10 (skipn (S di) s) <? 1) || (4094 <? strtol10 (skipn (S di) s)) = false ->
  vs_code s = if name_ok (firstn di s) then Some (firstn di s, strtol10 (skipn (S di) s)) else None.
Proof.
  intros s di H H0 Hne Hd Hr. unfold vs_code. rewrite H.
  destruct (Nat.eqb_spec di 0) as [E|E]; [contradiction|].
  destruct (skipn (S di) s) as [|t tl] eqn:Es; [contradiction|]. rewrite Hd, Hr. reflexivity.
Qed.

(* the plen tests of 0x89cbc / 0x89cc4 never fire: di < |s| <= 15 *)
Lemma vs_plen_small : forall s di, nulfree s -> (length s < 16)%nat -> strrchr s DOT = Some di ->
  0 <= Z.of_nat di + 1 <= 15.
Proof. intros s di Hn Hl Hd. pose proof (vs_di_lt s di Hn Hd). lia. Qed.

(* the tail the digit loop reads: its length and its place in the segment *)
Lemma vs_tail_len : forall (s : list Z) (di : nat), (di < length s)%nat ->
  length (skipn (S di) s) = (length s - S di)%nat.
Proof. intros s di _. apply length_skipn. Qed.

(* a digit of the tail is a byte of the segment, at S di + k *)
Lemma vs_tail_nth : forall (s : list Z) (di k : nat), nth k (skipn (S di) s) 0 = nth (S di + k) s 0.
Proof.
  intros s di k. revert s. induction di as [|di IH]; intros s.
  - destruct s as [|x s]; [destruct k; reflexivity | reflexivity].
  - destruct s as [|x s]; [destruct k; reflexivity | exact (IH s)].
Qed.

(* the loop's verdict after j digits: the first j bytes of the tail are digits *)
Lemma vs_forallb_firstn_S : forall (l : list Z) j, (j < length l)%nat ->
  forallb isdigit (firstn (S j) l) = forallb isdigit (firstn j l) && isdigit (nth j l 0).
Proof.
  induction l as [|x l IH]; intros j Hj; cbn [length] in Hj; [lia|].
  destruct j as [|j]; cbn [firstn forallb nth].
  - rewrite andb_true_r. reflexivity.
  - rewrite IH by lia. rewrite andb_assoc. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 2. texts as byte lists                                                                                     *)
(* ---------------------------------------------------------------------------------------------------------- *)

Definition zb (l : list Z) : list byte := map (Z_to_bv 8) l.

Lemma zs_zb : forall l, Forall (fun z => 0 <= z < 256) l -> seg_spec.zs (zb l) = l.
Proof.
  induction l as [|z l IH]; intros H; [reflexivity|].
  inversion H as [|z' l' Hz Hl]; subst. unfold seg_spec.zs, zb in *. cbn [map].
  rewrite (IH Hl). f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. exact Hz.
Qed.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros l. apply length_map. Qed.

Lemma zb_nul_free : forall l, Forall (fun z => 0 <= z < 256) l -> nulfree l -> ~ In (Z_to_bv 8 0) (zb l).
Proof.
  intros l Hr Hn Hin. unfold zb in Hin. apply in_map_iff in Hin as (z & Hz & Hzl).
  apply Hn. pose proof (proj1 (Forall_forall _ _) Hr z Hzl) as Hb.
  assert (Ez : z = 0).
  { apply (f_equal bv_unsigned) in Hz. rewrite !Z_to_bv_unsigned in Hz. unfold bv_wrap in Hz.
    change (bv_modulus 8) with 256 in Hz. rewrite (Z.mod_small z) in Hz by exact Hb. exact Hz. }
  rewrite <- Ez. exact Hzl.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 3. the branch words                                                                                         *)
(* ---------------------------------------------------------------------------------------------------------- *)

(* 0x89c24 `addi a4,a4,-48`, 0x89c28 `bltu a3,a4` with a3 = 9: taken (to the return of 0) iff the byte is no digit *)
Lemma vs_digit_test : forall b, 0 <= b < 256 -> (9 <? (b - 48) mod 2 ^ 64) = negb (isdigit b).
Proof.
  intros b Hb. unfold isdigit.
  destruct (Z_lt_le_dec b 48) as [Hl|Hl].
  - rewrite <- (Z.mod_add (b - 48) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia.
    replace (48 <=? b) with false by (symmetry; apply Z.leb_gt; lia). cbn. apply Z.ltb_lt. lia.
  - rewrite Z.mod_small by lia. replace (48 <=? b) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
    destruct (Z.leb_spec b 57); destruct (Z.ltb_spec 9 (b - 48)); cbn; first [reflexivity | lia].
Qed.

(* 0x89c70-0x89c80: a0 = v - 4095, a1 = -4094 (lui 0xfffff; addiw 2), `bgeu a0,a1`: taken (to 0x89cb0) iff
   1 <= v <= 4094, for any signed 64-bit v (strtol's value, here 0 <= v < 10^14) *)
Lemma vs_range_test : forall v, 0 <= v < 2 ^ 63 ->
  (2 ^ 64 - 4094 <=? (v - 4095) mod 2 ^ 64) = (1 <=? v) && (v <=? 4094).
Proof.
  intros v Hv.
  destruct (Z_lt_le_dec v 4095) as [Hl|Hl].
  - rewrite <- (Z.mod_add (v - 4095) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia.
    replace (v <=? 4094) with true by (symmetry; apply Z.leb_le; lia). rewrite andb_true_r.
    destruct (Z.leb_spec 1 v); destruct (Z.leb_spec (2 ^ 64 - 4094) (v - 4095 + 1 * 2 ^ 64)); first [reflexivity | lia].
  - rewrite Z.mod_small by lia. replace (v <=? 4094) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite andb_false_r. apply Z.leb_gt. lia.
Qed.

(* 0x89cd0-0x89cd8: a0 = len - 16, a1 = -17, `bltu a0,a1`: never taken for len < 16 *)
Lemma vs_len_test : forall n, 0 <= n < 16 -> ((n - 16) mod 2 ^ 64 <? 2 ^ 64 - 17) = false.
Proof.
  intros n Hn. rewrite <- (Z.mod_add (n - 16) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia.
  apply Z.ltb_ge. lia.
Qed.

(* *vid = v as the `sh` stores it: the low 16 bits of v, which are v itself for v in [1, 4094] *)
Lemma vs_vid_small : forall v, 1 <= v <= 4094 -> v mod 65536 = v.
Proof. intros v Hv. apply Z.mod_small. lia. Qed.
