From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YP0b YM05 YG0d YB1v YI0z YI12 YC4a YC8g YRo YXcalls YCbj.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3JsonCallee.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition jsy_rom_b (a : Z) (n : nat) (f : nat -> Z) : bool :=
forallb (fun k => match seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k)) with Some b => bv_unsigned b =? f k | None => false end) (seq 0 n).
Lemma jsy_rom_ok : forall a n f, jsy_rom_b a n f = true -> forall k, (k < n)%nat ->
seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (f k)).
Proof.
intros a n f H k Hk. unfold jsy_rom_b in H.
assert (Hs : In k (seq 0 n)) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) H k Hs) as Hb. cbv beta in Hb.
revert Hb. destruct (seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; intro Hb; [|discriminate Hb].
apply Z.eqb_eq in Hb. rewrite <- Hb, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Definition jsy_glob_b (q sz : Z) : bool := existsb (fun p => (fst p =? q) && (snd p =? sz)) tfib_globs.
Lemma jsy_glob_ok : forall q sz, jsy_glob_b q sz = true -> In (q, sz) tfib_globs.
Proof.
intros q sz H. apply existsb_exists in H as ([q' sz'] & Hin & Hb). cbn [fst snd] in Hb.
apply andb_true_iff in Hb as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst q' sz'. exact Hin.
Qed.
Definition jsy_ro_b (q sz : Z) : bool :=
existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? q) && (q + sz <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs
|| ((0xa0280 <=? q) && (q + sz <=? 0xa15a8)).
Lemma jsy_ro : forall q sz x, jsy_ro_b q sz = true -> q <= x < q + sz ->
in_img tfibsegs x /\ in_roP tfibsegs 0xa0280 0xa15a8 x.
Proof.
intros q sz x H Hx. unfold jsy_ro_b in H. apply orb_true_iff in H as [H|H].
- apply existsb_exists in H as (s & Hs & Hb). apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [Hw H1].
  apply negb_true_iff in Hw. apply Z.leb_le in H1. apply Z.leb_le in H2.
  unfold in_img, in_roP. split; [exists s; split; [exact Hs | lia] | left; exists s; split; [exact Hs | split; [exact Hw | lia]]].
- apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [apply tfib_relro_img; lia | unfold in_roP; right; lia].
Qed.
Definition jsy_present_b (q sz : Z) : bool :=
forallb (fun i => match seg_rom tfibsegs (Z_to_bv 64 (q + Z.of_nat i)) with Some _ => true | None => false end) (seq 0 (Z.to_nat sz)).
Lemma jsy_tail : forall a n x, jsy_present_b (a + n + 1) (7 - (a + n) mod 8) = true ->
a + n < x < a + n - (a + n) mod 8 + 8 -> seg_rom tfibsegs (Z_to_bv 64 x) <> None.
Proof.
intros a n x H Hx. unfold jsy_present_b in H.
assert (Hs : In (Z.to_nat (x - (a + n + 1))) (seq 0 (Z.to_nat (7 - (a + n) mod 8)))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) H _ Hs) as H1. cbv beta in H1.
replace (a + n + 1 + Z.of_nat (Z.to_nat (x - (a + n + 1)))) with x in H1 by lia.
intro HN. rewrite HN in H1. discriminate H1.
Qed.
Definition jsy_str_b (a : Z) (s : list Z) : bool :=
forallb (fun c => (0 <? c) && (c <? 256)) s &&
jsy_glob_b a (Z.of_nat (length s) + 1) &&
jsy_ro_b a (Z.of_nat (length s) + 1) &&
jsy_rom_b a (length (s ++ [0])) (fun k => nth k (s ++ [0]) 0) &&
jsy_present_b (a + Z.of_nat (length s) + 1) (7 - (a + Z.of_nat (length s)) mod 8).
Lemma jsy_g_b : jsy_glob_b 0xa0660 24 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jsy_r_b : jsy_ro_b 0xa0660 24 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jsy_w1_b : jsy_rom_b 0xa0660 8 (YO0f.le_byte 0x21000 8) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jsy_w2_b : jsy_rom_b (0xa0660 + 8) 8 (YO0f.le_byte 0x21020 8) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jsy_w3_b : jsy_rom_b (0xa0660 + 16) 8 (YO0f.le_byte 0x21140 8) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jsy_s1_b : jsy_str_b 0x21000 [116; 114; 117; 101] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jsy_s2_b : jsy_str_b 0x21020 [102; 97; 108; 115; 101] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jsy_s3_b : jsy_str_b 0x21140 [110; 117; 108; 108] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jsy_s4_b : jsy_str_b 0x21120 [34; 92; 47; 98; 102; 110; 114; 116; 117] = true.
Proof. vm_compute. reflexivity. Qed.
Section c. Context {rc : YM05.RunCeil}.
Lemma jsy_v20 : @pa_val _ lib_both3_0_listing PB_tfib (A_OBJ 20) = 0xa0660.
Proof. exact (tfib_val0_obj 20 ltac:(unfold tfib_nobj; lia)). Qed.
Lemma jsy_v19 : @pa_val _ lib_both3_0_listing PB_tfib (A_OBJ 19) = 0x21120.
Proof. exact (tfib_val0_obj 19 ltac:(unfold tfib_nobj; lia)). Qed.
Lemma jsy_word_ok : forall a w, jsy_rom_b a 8 (YO0f.le_byte w 8) = true -> @tjson_rom_word _ PB_tfib a w.
Proof. intros a w H k Hk. exact (jsy_rom_ok _ _ _ H k Hk). Qed.
Lemma jsy_str_ok : forall a s, jsy_str_b a s = true -> @tjson_scalar_rostr _ PB_tfib a s.
Proof.
intros a s H. unfold jsy_str_b in H.
apply andb_true_iff in H as [H HT]. apply andb_true_iff in H as [H HR]. apply andb_true_iff in H as [H HO].
apply andb_true_iff in H as [HF HG].
pose proof (jsy_glob_ok _ _ HG) as HIn.
unfold tjson_scalar_rostr. split; [|split; [exact HIn | split; [|split]]].
- apply Forall_forall. intros c Hc. pose proof (proj1 (forallb_forall _ _) HF c Hc) as Hb. cbv beta in Hb.
  apply andb_true_iff in Hb as [B1 B2]. apply Z.ltb_lt in B1. apply Z.ltb_lt in B2. lia.
- intros x Hx. apply (jsy_ro _ _ x HO). lia.
- intros k Hk. exact (jsy_rom_ok _ _ _ HR k Hk).
- intros x Hx. exact (jsy_tail _ _ x HT Hx).
Qed.
Lemma tjson_scalar_roimg_tfib : @tjson_scalar_roimg _ PB_tfib.
Proof.
unfold tjson_scalar_roimg. rewrite jsy_v20, jsy_v19.
exists 0x21000, 0x21020, 0x21140.
split; [exact (jsy_glob_ok _ _ jsy_g_b)|]. split; [reflexivity|].
split; [intros x Hx; exact (jsy_ro _ _ x jsy_r_b Hx)|].
split; [exact (jsy_word_ok _ _ jsy_w1_b)|]. split; [exact (jsy_word_ok _ _ jsy_w2_b)|].
split; [exact (jsy_word_ok _ _ jsy_w3_b)|].
split; [exact (jsy_str_ok _ _ jsy_s1_b)|]. split; [exact (jsy_str_ok _ _ jsy_s2_b)|].
split; [exact (jsy_str_ok _ _ jsy_s3_b)|].
exact (jsy_str_ok _ _ jsy_s4_b).
Qed.
End c.
