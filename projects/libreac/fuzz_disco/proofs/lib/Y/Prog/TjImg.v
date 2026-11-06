From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00 YO0f.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK04 YG00 YG0f YG0n YG0d YM05 YI16 YImgTop YP0b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI0w YI0z YI12 YC80 YC4a YC8i YC8g YRo YB1v YCbj.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacBoxName TjCuts TjBox.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition tji_in_b (a b : Z) (l : list (Z * Z)) : bool :=
existsb (fun p => (fst p =? a) && (snd p =? b)) l.
Lemma tji_in_b_ok : forall l a b, tji_in_b a b l = true -> In (a, b) l.
Proof.
intros l a b H. unfold tji_in_b in H. apply existsb_exists in H as ([x y] & Hin & Hb). cbn [fst snd] in Hb.
apply andb_true_iff in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. exact Hin.
Qed.
Definition tji_byte_b (s : list Z) : bool := forallb (fun c => (0 <? c) && (c <? 256)) s.
Lemma tji_byte_b_ok : forall s, tji_byte_b s = true -> Forall (fun c => 0 < c < 256) s.
Proof.
intros s H. unfold tji_byte_b in H. apply Forall_forall. intros c Hc.
pose proof (proj1 (forallb_forall _ _) H c Hc) as Hb. cbv beta in Hb.
apply andb_true_iff in Hb as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
Qed.
Definition tji_rom_b (a : Z) (bs : list Z) : bool :=
forallb (fun i => match seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat i)) with
  | Some b => bv_unsigned b =? nth i bs 0 | None => false end) (seq 0 (length bs)).
Lemma tji_rom_b_ok : forall a bs, tji_rom_b a bs = true -> tj_rom_bytes (PI := PB_tfib) a bs.
Proof.
intros a bs H i Hi. unfold tji_rom_b in H.
assert (Hs : In i (seq 0 (length bs))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) H i Hs) as H1. cbv beta in H1.
change (@pa_segs _ lib_both3_0_listing PB_tfib) with tfibsegs.
revert H1. destruct (seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; intro H1; [|discriminate H1].
cbn [option_map]. apply Z.eqb_eq in H1. rewrite H1. reflexivity.
Qed.
Definition tji_ro_b (q n : Z) : bool :=
existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? q) && (q + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs
|| ((0xa0280 <=? q) && (q + n <=? 0xa15a8)).
Lemma tji_ro_b_ok : forall q n, tji_ro_b q n = true -> forall x, q <= x < q + n ->
in_roP (@pa_segs _ lib_both3_0_listing PB_tfib) (@pa_relro_lo _ lib_both3_0_listing PB_tfib) (@pa_relro_hi _ lib_both3_0_listing PB_tfib) x.
Proof.
intros q n H x Hx. unfold in_roP.
change (@pa_segs _ lib_both3_0_listing PB_tfib) with tfibsegs.
change (@pa_relro_lo _ lib_both3_0_listing PB_tfib) with 0xa0280.
change (@pa_relro_hi _ lib_both3_0_listing PB_tfib) with 0xa15a8.
unfold tji_ro_b in H. apply orb_true_iff in H as [H|H].
- left. apply existsb_exists in H as (s & Hs & Hb). exists s.
  apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.leb_le in H2. repeat split; auto; lia.
- right. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma tji_rng_ok : forall q n, tji_ro_b q n = true -> tj_rbn_rng (PI := PB_tfib) q n.
Proof. intros q n H x Hx. exact (tji_ro_b_ok q n H x Hx). Qed.
Definition tji_pad_b (lo hi : Z) : bool :=
forallb (fun i => match seg_rom tfibsegs (Z_to_bv 64 (lo + 1 + Z.of_nat i)) with Some _ => true | None => false end)
  (seq 0 (Z.to_nat (hi - lo - 1))).
Lemma tji_pad_b_ok : forall lo hi, tji_pad_b lo hi = true -> forall x, lo < x < hi -> seg_rom tfibsegs (Z_to_bv 64 x) <> None.
Proof.
intros lo hi H x Hx. unfold tji_pad_b in H.
assert (Hs : In (Z.to_nat (x - lo - 1)) (seq 0 (Z.to_nat (hi - lo - 1)))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) H _ Hs) as H1. cbv beta in H1.
replace (lo + 1 + Z.of_nat (Z.to_nat (x - lo - 1))) with x in H1 by lia.
intro HN. rewrite HN in H1. discriminate H1.
Qed.
Lemma tji_val : forall k, (k < tfib_nobj)%nat -> @pa_val _ lib_both3_0_listing PB_tfib (A_OBJ k) = tfib_obj k.
Proof. intros k Hk. exact (tfib_val0_obj k Hk). Qed.
Definition tji_ro_at_b (k : nat) (s : list Z) : bool :=
Nat.ltb k tfib_nobj && tji_in_b (tfib_obj k) (Z.of_nat (length s) + 1) tfib_globs &&
tji_ro_b (tfib_obj k) (Z.of_nat (length s) + 1) &&
(IMG_LO + 64 <=? tfib_obj k) && (tfib_obj k + Z.of_nat (length s) + 1 + 64 <=? IMG_TOP) &&
tji_byte_b s && tji_rom_b (tfib_obj k) (s ++ [0]).
Lemma tji_ro_at_b_ok : forall k s, tji_ro_at_b k s = true -> tj_ro_at (PI := PB_tfib) k s.
Proof.
intros k s H. unfold tji_ro_at_b in H.
apply andb_true_iff in H as [H H6]. apply andb_true_iff in H as [H H5]. apply andb_true_iff in H as [H H4].
apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H H2]. apply andb_true_iff in H as [H0 H1].
apply Nat.ltb_lt in H0. apply tji_in_b_ok in H1. apply Z.leb_le in H3. apply Z.leb_le in H4.
unfold tj_ro_at. rewrite (tji_val k H0).
split; [exact H1|]. split; [intros x Hx; apply (tji_ro_b_ok (tfib_obj k) (Z.of_nat (length s) + 1) H2); lia|].
split; [exact H3|]. split; [exact H4|]. split; [apply tji_byte_b_ok; exact H5|].
apply tji_rom_b_ok. exact H6.
Qed.
Lemma tj_strs_tfib : tj_strs (PI := PB_tfib).
Proof.
unfold tj_strs.
repeat (apply conj; [apply tji_ro_at_b_ok; vm_compute; reflexivity|]).
unfold tj_ro_kd. rewrite (tji_val 17) by (unfold tfib_nobj; lia).
split; [apply tji_in_b_ok; vm_compute; reflexivity|].
split; [apply (tji_ro_b_ok (tfib_obj 17) 8); vm_compute; reflexivity|].
apply tji_rom_b_ok. vm_compute. reflexivity.
Qed.
Definition tji_word_b (a v : Z) : bool :=
forallb (fun k => match seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k)) with
  | Some b => bv_eqb b (Z_to_bv 8 (YO0f.le_byte v 8 k)) | None => false end) (seq 0 8).
Lemma tji_word_b_ok : forall a v, tji_word_b a v = true -> tj_rbn_word (PI := PB_tfib) a v.
Proof.
intros a v H k Hk. unfold tji_word_b in H.
assert (Hs : In k (seq 0 8)) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) H k Hs) as H1. cbv beta in H1.
change (@pa_segs _ lib_both3_0_listing PB_tfib) with tfibsegs.
revert H1. destruct (seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; intro H1; [|discriminate H1].
f_equal. apply bv_eq. unfold bv_eqb in H1. apply Z.eqb_eq in H1. exact H1.
Qed.
Definition tji_str_b (q sz : Z) (s : list Z) : bool :=
tji_in_b q sz tfib_globs && tji_ro_b q sz && (Z.of_nat (length s) + 1 <=? sz) && (IMG_LO + 64 <=? q) && (q + sz + 64 <=? IMG_TOP) &&
tji_byte_b s && tji_rom_b q (s ++ [0]) &&
tji_pad_b (q + Z.of_nat (length s)) (q + Z.of_nat (length s) - (q + Z.of_nat (length s)) mod 8 + 8).
Lemma tji_str_b_ok : forall q sz s, tji_str_b q sz s = true -> tj_rbn_str (PI := PB_tfib) q sz s.
Proof.
intros q sz s H. unfold tji_str_b in H.
apply andb_true_iff in H as [H H8]. apply andb_true_iff in H as [H H7]. apply andb_true_iff in H as [H H6].
apply andb_true_iff in H as [H H5]. apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [H H3].
apply andb_true_iff in H as [H1 H2].
unfold tj_rbn_str.
split; [apply tji_in_b_ok; exact H1|]. split; [exact (tji_rng_ok _ _ H2)|].
split; [apply Z.leb_le; exact H3|]. split; [apply Z.leb_le; exact H4|]. split; [apply Z.leb_le; exact H5|].
split; [apply tji_byte_b_ok; exact H6|]. split; [apply tji_rom_b_ok; exact H7|].
intros x Hx. change (@pa_segs _ lib_both3_0_listing PB_tfib) with tfibsegs. exact (tji_pad_b_ok _ _ H8 x Hx).
Qed.
Lemma tj_rbn_rom_tfib : tj_rbn_rom (PI := PB_tfib).
Proof.
unfold tj_rbn_rom. split; [apply (tji_rng_ok MC_CONSTS_LO (MC_CONSTS_HI - MC_CONSTS_LO)); vm_compute; reflexivity|].
exists 0x211c0, 0x211e0, 0x21200.
rewrite ?tji_val by (unfold tfib_nobj; lia).
repeat match goal with |- _ /\ _ => split end.
all: lazymatch goal with
| |- tj_rbn_word _ _ => apply tji_word_b_ok
| |- tj_rbn_str _ _ _ => apply tji_str_b_ok
| |- tj_rbn_rng _ _ => apply tji_rng_ok
| |- In _ _ => apply tji_in_b_ok
| |- Z.le _ _ => apply Z.leb_le
| |- _ => idtac
end; vm_compute; reflexivity.
Qed.
End d.
