From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK04 YG00 YG0f YG0n YG0d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym DiscoSyms DiscoList DiscoAddr DiscoRoList DiscoPa DiscoBase DiscoRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoImg TjCuts TjBoxRom.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnShared.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
Definition tj_pad_stmt : Prop :=
forall k s, tj_ro_at k s -> forall x, VAL (A_OBJ k) + Z.of_nat (length s) < x < str_end (VAL (A_OBJ k)) s -> seg_rom SEGS (Z_to_bv 64 x) <> None.
End f.
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
forallb (fun i => match seg_rom disco_segs (Z_to_bv 64 (a + Z.of_nat i)) with
  | Some b => bv_unsigned b =? nth i bs 0 | None => false end) (seq 0 (length bs)).
Lemma tji_rom_b_ok : forall a bs, tji_rom_b a bs = true -> @tj_rom_bytes rc PB_disco a bs.
Proof.
intros a bs H i Hi. unfold tji_rom_b in H.
assert (Hs : In i (seq 0 (length bs))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) H i Hs) as H1. cbv beta in H1.
change (@pa_segs rc disco_listing PB_disco) with disco_segs.
revert H1. destruct (seg_rom disco_segs (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; intro H1; [|discriminate H1].
cbn [option_map]. apply Z.eqb_eq in H1. rewrite H1. reflexivity.
Qed.
Definition tji_pad_b (lo hi : Z) : bool :=
forallb (fun i => match seg_rom disco_segs (Z_to_bv 64 (lo + 1 + Z.of_nat i)) with Some _ => true | None => false end)
  (seq 0 (Z.to_nat (hi - lo - 1))).
Lemma tji_pad_b_ok : forall lo hi, tji_pad_b lo hi = true -> forall x, lo < x < hi -> seg_rom disco_segs (Z_to_bv 64 x) <> None.
Proof.
intros lo hi H x Hx. unfold tji_pad_b in H.
assert (Hs : In (Z.to_nat (x - lo - 1)) (seq 0 (Z.to_nat (hi - lo - 1)))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) H _ Hs) as H1. cbv beta in H1.
replace (lo + 1 + Z.of_nat (Z.to_nat (x - lo - 1))) with x in H1 by lia.
intro HN. rewrite HN in H1. discriminate H1.
Qed.
Lemma tji_val : forall k, (k < disco_nobj)%nat -> @pa_val rc disco_listing PB_disco (A_OBJ k) = disco_obj k.
Proof. intros k Hk. exact (disco_obj_val k Hk). Qed.
Definition tji_ro_at_b (k : nat) (s : list Z) : bool :=
Nat.ltb k disco_nobj && tji_in_b (disco_obj k) (Z.of_nat (length s) + 1) disco_globs &&
(IMG_LO + 64 <=? disco_obj k) && (disco_obj k + Z.of_nat (length s) + 1 + 64 <=? IMG_TOP) &&
tji_byte_b s && tji_rom_b (disco_obj k) (s ++ [0]).
Lemma tji_ro_at_b_ok : forall k s, tji_ro_at_b k s = true -> @tj_ro_at rc PB_disco k s.
Proof.
intros k s H. unfold tji_ro_at_b in H.
apply andb_true_iff in H as [H H5]. apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [H H3].
apply andb_true_iff in H as [H H2]. apply andb_true_iff in H as [H0 H1].
apply Nat.ltb_lt in H0. apply tji_in_b_ok in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
unfold tj_ro_at. rewrite (tji_val k H0).
split; [exact H1|]. split.
{ intros x Hx. apply (disco_ro_in_ro (PI := PB_disco) (disco_obj k) (Z.of_nat (length s) + 1)); [|lia].
  unfold disco_ro_all, disco_ro_ranges. apply in_or_app. left. apply in_or_app. left. exact H1. }
split; [exact H2|]. split; [exact H3|]. split; [apply tji_byte_b_ok; exact H4|].
apply tji_rom_b_ok. exact H5.
Qed.
Lemma tj_strs_disco : @tj_strs rc PB_disco.
Proof.
unfold tj_strs.
repeat (apply conj; [apply tji_ro_at_b_ok; vm_compute; reflexivity|]).
unfold tj_ro_kd. rewrite (tji_val 17) by (unfold disco_nobj; lia).
split; [apply tji_in_b_ok; vm_compute; reflexivity|]. split.
{ intros x Hx. apply (disco_ro_in_ro (PI := PB_disco) (disco_obj 17) 8); [|exact Hx].
  unfold disco_ro_all, disco_ro_ranges. apply in_or_app. left. apply in_or_app. right. apply tji_in_b_ok. vm_compute. reflexivity. }
apply tji_rom_b_ok. vm_compute. reflexivity.
Qed.
Definition tji_word_b (a v : Z) : bool :=
forallb (fun k => match seg_rom disco_segs (Z_to_bv 64 (a + Z.of_nat k)) with
  | Some b => bv_eqb b (Z_to_bv 8 (YO0f.le_byte v 8 k)) | None => false end) (seq 0 8).
Lemma tji_word_b_ok : forall a v, tji_word_b a v = true -> @tj_rbn_word rc PB_disco a v.
Proof.
intros a v H k Hk. unfold tji_word_b in H.
assert (Hs : In k (seq 0 8)) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) H k Hs) as H1. cbv beta in H1.
change (@pa_segs rc disco_listing PB_disco) with disco_segs.
revert H1. destruct (seg_rom disco_segs (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; intro H1; [|discriminate H1].
f_equal. apply bv_eq. unfold bv_eqb in H1. apply Z.eqb_eq in H1. exact H1.
Qed.
Definition tji_str_b (q sz : Z) (s : list Z) : bool :=
tji_in_b q sz disco_globs && ((sz mod 8 =? 0) || tji_in_b (q + sz) (8 - sz mod 8) disco_glob_tails) &&
(Z.of_nat (length s) + 1 <=? sz) && (IMG_LO + 64 <=? q) && (q + sz + 64 <=? IMG_TOP) &&
tji_byte_b s && tji_rom_b q (s ++ [0]) &&
tji_pad_b (q + Z.of_nat (length s)) (q + Z.of_nat (length s) - (q + Z.of_nat (length s)) mod 8 + 8).
Lemma tji_str_b_ok : forall q sz s, tji_str_b q sz s = true -> @tj_rbn_str rc PB_disco q sz s.
Proof.
intros q sz s H. unfold tji_str_b in H.
apply andb_true_iff in H as [H H7]. apply andb_true_iff in H as [H H6]. apply andb_true_iff in H as [H H5].
apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H H2].
apply andb_true_iff in H as [H1 Ht].
unfold tj_rbn_str.
split.
{ split; [apply tji_in_b_ok; exact H1|].
  apply orb_true_iff in Ht as [Ht | Ht]; [left; apply Z.eqb_eq; exact Ht | right; apply tji_in_b_ok; exact Ht]. }
split; [apply Z.leb_le; exact H2|].
split; [apply Z.leb_le; exact H3|]. split; [apply Z.leb_le; exact H4|].
split; [apply tji_byte_b_ok; exact H5|]. split; [apply tji_rom_b_ok; exact H6|].
intros x Hx. change (@pa_segs rc disco_listing PB_disco) with disco_segs. exact (tji_pad_b_ok _ _ H7 x Hx).
Qed.
Lemma tj_rbn_rom_disco : @tj_rbn_rom rc PB_disco.
Proof.
unfold tj_rbn_rom. exists 0x211c0, 0x211e0, 0x21200.
rewrite ?tji_val by (unfold disco_nobj; lia).
repeat match goal with |- _ /\ _ => split end.
all: lazymatch goal with
| |- @tj_rbn_word _ _ _ _ => apply tji_word_b_ok
| |- @tj_rbn_str _ _ _ _ _ => apply tji_str_b_ok
| |- In _ _ => apply tji_in_b_ok
| |- Z.le _ _ => apply Z.leb_le
| |- _ => idtac
end; vm_compute; reflexivity.
Qed.
Definition tji_gpad_b (r : Z * Z) : bool :=
tji_pad_b (fst r + snd r - 1) (fst r + snd r - 1 - (fst r + snd r - 1) mod 8 + 8).
Lemma tji_gpad_all : forallb tji_gpad_b disco_globs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tji_gpad : forall q n x, In (q, n + 1) disco_globs -> q + n < x < q + n - (q + n) mod 8 + 8 ->
seg_rom disco_segs (Z_to_bv 64 x) <> None.
Proof.
intros q n x Hin Hx. pose proof (proj1 (forallb_forall _ _) tji_gpad_all _ Hin) as H.
unfold tji_gpad_b in H. cbn [fst snd] in H.
replace (q + (n + 1) - 1) with (q + n) in H by lia.
exact (tji_pad_b_ok _ _ H x Hx).
Qed.
Lemma tj_pad_disco : @tj_pad_stmt PB_disco.
Proof.
intros k s H x Hx. destruct H as [Hin _]. unfold str_end in Hx.
exact (tji_gpad _ _ x Hin Hx).
Qed.
Lemma tj_ro_kd_sep_disco :
@pa_val rc disco_listing PB_disco (A_OBJ 17) + 8 <= @pa_val rc disco_listing PB_disco (A_OBJ 1) /\
@pa_val rc disco_listing PB_disco (A_OBJ 17) + 8 <= @pa_val rc disco_listing PB_disco (A_OBJ 0) /\
@pa_val rc disco_listing PB_disco (A_OBJ 17) + 8 <= @pa_val rc disco_listing PB_disco (A_OBJ 66) /\
@pa_val rc disco_listing PB_disco (A_OBJ 17) + 8 <= @pa_val rc disco_listing PB_disco (A_OBJ 67).
Proof.
rewrite !tji_val by (unfold disco_nobj; lia).
repeat split; apply Z.leb_le; vm_compute; reflexivity.
Qed.
End d.
