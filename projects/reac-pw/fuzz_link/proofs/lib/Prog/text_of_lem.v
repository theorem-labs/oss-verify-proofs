(* Pure facts the text_of walk (lib/Prog/text_of.v) uses: byte reads out of a bytes_at, finite checks
   over small integer ranges (the compiler's division by 11 and by 320), the sign extension of a
   byte, the `texts` table and its eleven strings as the plain image holds them (every value below
   is checked against the image by vm_compute; nothing is stated by hand), and the bound of
   strnlen. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0 MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec link_mem.
Import ListNotations.
Open Scope Z_scope.

(* ---- lists ---- *)

Lemma tl_nth_skipn : forall {A} k (l : list A) i, nth_error (skipn k l) i = nth_error l (k + i).
Proof. intros A k. induction k as [|k IH]; intros [|x l] i; cbn; try reflexivity. destruct i; reflexivity. apply IH. Qed.

Lemma tl_nth_firstn : forall {A} k (l : list A) i, (i < k)%nat -> nth_error (firstn k l) i = nth_error l i.
Proof.
  intros A k. induction k as [|k IH]; intros [|x l] [|i] Hi; cbn; try reflexivity; try lia.
  apply IH. lia.
Qed.

(* ---- bytes ---- *)

Lemma tl_rd1 : forall segs m a bs k b, bytes_at segs m a bs -> nth_error bs k = Some b ->
  ov_read_bytes segs m (wa (a + Z.of_nat k)) 1 = Some [b].
Proof.
  intros segs m a bs k b H E.
  assert (Hk : (k < length bs)%nat) by (apply nth_error_Some; rewrite E; discriminate).
  rewrite (bytes_at_ov_read segs m a bs k 1 H) by lia.
  f_equal. clear H. revert k E Hk. induction bs as [|x bs IH]; intros [|k] E Hk; cbn in *; try discriminate.
  - inversion E; reflexivity.
  - apply IH; [exact E | lia].
Qed.

Lemma tl_bytes_at_skipn : forall segs m a bs k, bytes_at segs m a bs -> (k <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat k) (skipn k bs).
Proof.
  intros segs m a bs k (Ha & Hl & H) Hk. unfold bytes_at. rewrite length_skipn.
  split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite tl_nth_skipn. reflexivity.
Qed.

Lemma tl_bytes_at_firstn : forall segs m a bs k, bytes_at segs m a bs -> bytes_at segs m a (firstn k bs).
Proof.
  intros segs m a bs k (Ha & Hl & H). unfold bytes_at. rewrite length_firstn.
  split; [lia|]. split; [lia|]. intros i Hi.
  rewrite tl_nth_firstn by lia. apply H. lia.
Qed.

(* ---- finite checks ---- *)

Lemma tl_zcheck : forall (f g : Z -> Z) (n : nat),
  forallb (fun k => Z.eqb (f (Z.of_nat k)) (g (Z.of_nat k))) (seq 0 n) = true ->
  forall z, 0 <= z < Z.of_nat n -> f z = g z.
Proof.
  intros f g n H z Hz. rewrite forallb_forall in H.
  specialize (H (Z.to_nat z) ltac:(apply in_seq; lia)). cbv beta in H. rewrite Z2Nat.id in H by lia.
  apply Z.eqb_eq. exact H.
Qed.

Lemma tl_zcheck2 : forall (f g : Z -> Z -> Z) (n1 n2 : nat),
  forallb (fun i => forallb (fun j => Z.eqb (f (Z.of_nat i) (Z.of_nat j)) (g (Z.of_nat i) (Z.of_nat j)))
                      (seq 0 n2)) (seq 0 n1) = true ->
  forall x y, 0 <= x < Z.of_nat n1 -> 0 <= y < Z.of_nat n2 -> f x y = g x y.
Proof.
  intros f g n1 n2 H x y Hx Hy. rewrite forallb_forall in H.
  specialize (H (Z.to_nat x) ltac:(apply in_seq; lia)). cbv beta in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat y) ltac:(apply in_seq; lia)). cbv beta in H. rewrite !Z2Nat.id in H by lia.
  apply Z.eqb_eq. exact H.
Qed.

(* ---- the sign extension `lb` makes ---- *)

Lemma tl_sxb_u : forall b : byte,
  bv_unsigned (sxb b) = if bv_unsigned b <? 128 then bv_unsigned b else bv_unsigned b + 18446744073709551360.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  assert (E : Z_to_bv 8 (bv_unsigned b) = b).
  { apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply (bv_unsigned_in_range 8). }
  rewrite <- E at 1. clear E. revert R. generalize (bv_unsigned b). intros u R.
  eapply (tl_zcheck (fun u => bv_unsigned (sxb (Z_to_bv 8 u)))
                    (fun u => if u <? 128 then u else u + 18446744073709551360) 256);
    [vm_compute; reflexivity | lia].
Qed.

Lemma tl_sxb_pos : forall b : byte, bv_unsigned b < 128 -> sxb b = Z_to_bv 64 (bv_unsigned b).
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  apply bv_eq. rewrite tl_sxb_u. destruct (Z.ltb_spec (bv_unsigned b) 128) as [_|C]; [|lia].
  rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma tl_sxb_lt : forall b : byte, bv_unsigned b < 128 <-> bv_unsigned (sxb b) < 2 ^ 63.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  rewrite tl_sxb_u. destruct (Z.ltb_spec (bv_unsigned b) 128); split; intros; lia.
Qed.

(* ---- the `texts` table (fuzz_link.c:120-123) and its strings ---- *)

Definition TL_TEXTS : Z := 133104.
Lemma TL_TEXTS_is : TL_TEXTS = A_TEXTS. Proof. reflexivity. Qed.

(* the eleven pointers; tl_texts_img checks them against the image *)
Definition TL_PTRS : list Z :=
  [0x10368; 0x10341; 0x10488; 0x102a8; 0x10517; 0x10429; 0x10520; 0x1056f; 0x10329; 0x10497; 0x10554].
Definition tl_ptr (j : nat) : Z := nth j TL_PTRS 0.
Definition TL_TB : list byte := concat (map (fun p => le8 (Z_to_bv 64 p)) TL_PTRS).

Definition rom_eq (a : Z) (bs : list byte) : bool :=
  forallb (fun i => match seg_rom rsegs (wa (a + Z.of_nat i)), nth_error bs i with
                    | Some b, Some c => Z.eqb (bv_unsigned b) (bv_unsigned c)
                    | _, _ => false
                    end) (seq 0 (length bs)).

Lemma tl_texts_img : rom_eq TL_TEXTS TL_TB = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tl_TB_len : length TL_TB = 88%nat.
Proof. reflexivity. Qed.

Lemma tl_bytes_at_rom : forall m a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat -> mrd rsegs m (wa (a + Z.of_nat i)) = seg_rom rsegs (wa (a + Z.of_nat i))) ->
  rom_eq a bs = true -> bytes_at rsegs m a bs.
Proof.
  intros m a bs H0 H1 H HR. split; [exact H0|]. split; [exact H1|]. intros i Hi. rewrite H by exact Hi.
  unfold rom_eq in HR. rewrite forallb_forall in HR. specialize (HR i ltac:(apply in_seq; lia)). cbv beta in HR.
  destruct (seg_rom rsegs (wa (a + Z.of_nat i))) as [b|]; [|discriminate].
  destruct (nth_error bs i) as [c|]; [|discriminate].
  apply Z.eqb_eq in HR. f_equal. apply bv_eq. exact HR.
Qed.

Lemma tl_texts_read : forall m k, bytes_at rsegs m 133104 TL_TB -> 0 <= k < 11 ->
  ov_read_bytes rsegs m (wa (133104 + 8 * k)) 8 = Some (le8 (Z_to_bv 64 (tl_ptr (Z.to_nat k)))).
Proof.
  intros m k H Hk.
  rewrite (bytes_at_read rsegs m 133104 TL_TB (8 * k) 8 H) by (try lia; rewrite tl_TB_len; lia).
  f_equal.
  assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10)
    by lia.
  repeat (destruct C as [C|C]; [subst k; vm_compute; reflexivity|]). subst k. vm_compute. reflexivity.
Qed.

(* a C string read out of the image *)
Fixpoint rom_str (a : Z) (fuel : nat) : option (list byte) :=
  match fuel with
  | O => None
  | S f => match seg_rom rsegs (wa a) with
           | Some b => if Z.eqb (bv_unsigned b) 0 then Some []
                       else match rom_str (a + 1) f with Some t => Some (b :: t) | None => None end
           | None => None
           end
  end.

Definition tl_str (j : nat) : list byte := match rom_str (tl_ptr j) 64 with Some t => t | None => [] end.

Definition ro_range (a n : Z) : bool := forallb (fun i => ro_addr rsegs (wa (a + Z.of_nat i))) (seq 0 (Z.to_nat n)).

Definition text_ok (j : nat) : bool :=
  let p := tl_ptr j in let t := tl_str j in
  rom_eq p (t ++ [zb 0]) && ro_range p (Z.of_nat (length t) + 1) &&
  negb (existsb (fun b => Z.eqb (bv_unsigned b) 0) t) &&
  (A_RO_LO <=? p) && (p + Z.of_nat (length t) + 8 <=? A_RO_END) && (Z.of_nat (length t) <? 320).

Lemma tl_text_ok : forall j, (j < 11)%nat -> text_ok j = true.
Proof.
  intros j Hj. do 11 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma tl_cstr_ro : forall m p t, MemNorm.ro_agree rsegs m -> 0 <= p -> p + Z.of_nat (length t) + 1 <= 2 ^ 64 ->
  ro_range p (Z.of_nat (length t) + 1) = true -> rom_eq p (t ++ [zb 0]) = true ->
  existsb (fun b => Z.eqb (bv_unsigned b) 0) t = false -> cstr_at m p t.
Proof.
  intros m p t RO H0 H1 HRR HE HN. split.
  - apply tl_bytes_at_rom; [exact H0 | rewrite length_app; cbn; lia | | exact HE].
    intros i Hi. rewrite length_app in Hi. cbn in Hi. apply RO.
    unfold ro_range in HRR. rewrite forallb_forall in HRR. apply HRR. apply in_seq. lia.
  - intros Hin. assert (HT : existsb (fun b => Z.eqb (bv_unsigned b) 0) t = true)
      by (apply existsb_exists; exists (zb 0); split; [exact Hin | reflexivity]).
    congruence.
Qed.

Lemma tl_text_facts : forall m j, MemNorm.ro_agree rsegs m -> (j < 11)%nat ->
  cstr_at m (tl_ptr j) (tl_str j) /\ Z.of_nat (length (tl_str j)) < 320 /\
  A_RO_LO <= tl_ptr j /\ tl_ptr j + Z.of_nat (length (tl_str j)) + 8 <= A_RO_END.
Proof.
  intros m j RO Hj. pose proof (tl_text_ok j Hj) as H. unfold text_ok in H. cbv zeta in H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H6. apply Z.leb_le in H5. apply Z.leb_le in H4. apply negb_true_iff in H3.
  unfold A_RO_LO, A_RO_END in *.
  split; [apply tl_cstr_ro; try assumption; lia|]. lia.
Qed.

(* ---- strnlen ---- *)

Lemma tl_strnlen : forall (k : Z) (buf : list byte), 0 <= k <= Z.of_nat (length buf) ->
  0 <= strnlen_res k buf <= k /\ ~ In (zb 0) (firstn (Z.to_nat (strnlen_res k buf)) buf).
Proof.
  intros k buf Hk. unfold strnlen_res.
  destruct (find_byte 0 (firstn (Z.to_nat k) buf)) as [i|] eqn:F.
  - destruct (find_byte_Some _ _ _ F) as (Hl & _ & Hmin). rewrite length_firstn in Hl.
    split; [lia|]. rewrite Nat2Z.id. intros Hin.
    apply In_nth_error in Hin as (j & Hj).
    assert (Hji : (j < i)%nat).
    { assert (Hn : nth_error (firstn i buf) j <> None) by (rewrite Hj; discriminate).
      apply nth_error_Some in Hn. rewrite length_firstn in Hn. lia. }
    rewrite tl_nth_firstn in Hj by lia.
    apply (Hmin j (zb 0) Hji); [rewrite tl_nth_firstn by lia; exact Hj | reflexivity].
  - split; [lia|]. intros Hin. apply In_nth_error in Hin as (j & Hj).
    exact (find_byte_None _ _ F j (zb 0) Hj eq_refl).
Qed.

Lemma tl_strnlen_memchr : forall (P k : Z) (buf : list byte), 0 < P -> P + k <= 2 ^ 64 -> 0 <= k ->
  (memchr_res P 0 k buf = 0 -> strnlen_res k buf = k) /\
  (memchr_res P 0 k buf <> 0 -> strnlen_res k buf = memchr_res P 0 k buf - P).
Proof.
  intros P k buf HP Hk Hk0. unfold memchr_res, strnlen_res.
  destruct (find_byte 0 (firstn (Z.to_nat k) buf)) as [i|] eqn:F.
  - destruct (find_byte_Some _ _ _ F) as (Hl & _ & _). split; intros; lia.
  - split; intros; lia.
Qed.

Lemma tl_nth_ex : forall {A} (l : list A) k, (k < length l)%nat -> exists b, nth_error l k = Some b.
Proof.
  intros A l k H. destruct (nth_error l k) as [b|] eqn:E; [exists b; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma tl_memchr_range : forall (P k : Z) (buf : list byte), 0 <= k ->
  memchr_res P 0 k buf = 0 \/ P <= memchr_res P 0 k buf < P + k.
Proof.
  intros P k buf Hk. unfold memchr_res.
  destruct (find_byte 0 (firstn (Z.to_nat k) buf)) as [i|] eqn:F; [|left; reflexivity].
  right. destruct (find_byte_Some _ _ _ F) as (Hl & _ & _). rewrite length_firstn in Hl. lia.
Qed.

Lemma tl_le1_zero : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Lemma tl_zlb1_zero : Z_to_le_bytes 1 0 = [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.
