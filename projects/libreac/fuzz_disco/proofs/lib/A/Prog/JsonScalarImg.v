From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable DiscoSyms DiscoList DiscoAddr DiscoRoList DiscoPa DiscoBase DiscoImg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JsonScalar.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition jsi_rom_b (a : Z) (n : nat) (f : nat -> Z) : bool :=
forallb (fun k => match seg_rom disco_segs (Z_to_bv 64 (a + Z.of_nat k)) with Some b => bv_unsigned b =? f k | None => false end) (seq 0 n).
Lemma jsi_rom_ok : forall a n f, jsi_rom_b a n f = true -> forall k, (k < n)%nat ->
seg_rom disco_segs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (f k)).
Proof.
intros a n f H k Hk. unfold jsi_rom_b in H.
assert (Hs : In k (seq 0 n)) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) H k Hs) as Hb. cbv beta in Hb.
revert Hb. destruct (seg_rom disco_segs (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; intro Hb; [|discriminate Hb].
apply Z.eqb_eq in Hb. rewrite <- Hb, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Definition jsi_glob_b (q sz : Z) : bool := existsb (fun p => (fst p =? q) && (snd p =? sz)) disco_globs.
Lemma jsi_glob_ok : forall q sz, jsi_glob_b q sz = true -> In (q, sz) disco_globs.
Proof.
intros q sz H. apply existsb_exists in H as ([q' sz'] & Hin & Hb). cbn [fst snd] in Hb.
apply andb_true_iff in Hb as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst q' sz'. exact Hin.
Qed.
Lemma jsi_ro : forall q sz x, In (q, sz) disco_globs -> q <= x < q + sz ->
in_img disco_segs x /\ in_roP disco_segs disco_relro_lo disco_relro_hi x.
Proof.
intros q sz x Hin Hx.
assert (Hall : In (q, sz) disco_ro_all)
  by (unfold disco_ro_all, disco_ro_ranges; apply in_or_app; left; apply in_or_app; left; exact Hin).
destruct (disco_ro_ok q sz x Hall Hx) as [(s & Hs & Hw & Hr) | Hr].
- split; [exists s; split; [exact Hs | exact Hr] | left; exists s; split; [exact Hs | split; [exact Hw | exact Hr]]].
- split; [exact (disco_relro_img x Hr) | right; exact Hr].
Qed.
Lemma jsi_tail : forall a n x, ro_present_b (a + n + 1) (7 - (a + n) mod 8) = true ->
a + n < x < a + n - (a + n) mod 8 + 8 -> seg_rom disco_segs (Z_to_bv 64 x) <> None.
Proof.
intros a n x H Hx. unfold ro_present_b in H.
assert (Hs : In (Z.to_nat (x - (a + n + 1))) (seq 0 (Z.to_nat (7 - (a + n) mod 8)))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) H _ Hs) as H1. cbv beta in H1.
replace (a + n + 1 + Z.of_nat (Z.to_nat (x - (a + n + 1)))) with x in H1 by lia.
intro HN. rewrite HN in H1. discriminate H1.
Qed.
Definition jsi_str_b (a : Z) (s : list Z) : bool :=
forallb (fun c => (0 <? c) && (c <? 256)) s &&
jsi_glob_b a (Z.of_nat (length s) + 1) &&
jsi_rom_b a (length (s ++ [0])) (fun k => nth k (s ++ [0]) 0) &&
ro_present_b (a + Z.of_nat (length s) + 1) (7 - (a + Z.of_nat (length s)) mod 8).
Lemma jsi_g_b : jsi_glob_b 0xa02c0 24 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jsi_w1_b : jsi_rom_b 0xa02c0 8 (YO0f.le_byte 0x21000 8) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jsi_w2_b : jsi_rom_b (0xa02c0 + 8) 8 (YO0f.le_byte 0x21020 8) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jsi_w3_b : jsi_rom_b (0xa02c0 + 16) 8 (YO0f.le_byte 0x21140 8) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jsi_s1_b : jsi_str_b 0x21000 [116; 114; 117; 101] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jsi_s2_b : jsi_str_b 0x21020 [102; 97; 108; 115; 101] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jsi_s3_b : jsi_str_b 0x21140 [110; 117; 108; 108] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jsi_s4_b : jsi_str_b 0x21120 [34; 92; 47; 98; 102; 110; 114; 116; 117] = true.
Proof. vm_compute. reflexivity. Qed.
Section c. Context {rc : YM05.RunCeil}.
Lemma jsi_v20 : @pa_val _ disco_listing PB_disco (A_OBJ 20) = 0xa02c0.
Proof. exact (disco_obj_val 20 ltac:(unfold disco_nobj; lia)). Qed.
Lemma jsi_v19 : @pa_val _ disco_listing PB_disco (A_OBJ 19) = 0x21120.
Proof. exact (disco_obj_val 19 ltac:(unfold disco_nobj; lia)). Qed.
Lemma jsi_word_ok : forall a w, jsi_rom_b a 8 (YO0f.le_byte w 8) = true -> @tjson_rom_word _ PB_disco a w.
Proof. intros a w H k Hk. exact (jsi_rom_ok _ _ _ H k Hk). Qed.
Lemma jsi_str_ok : forall a s, jsi_str_b a s = true -> @tjson_scalar_rostr _ PB_disco a s.
Proof.
intros a s H. unfold jsi_str_b in H.
apply andb_true_iff in H as [H HT]. apply andb_true_iff in H as [H HR]. apply andb_true_iff in H as [HF HG].
pose proof (jsi_glob_ok _ _ HG) as HIn.
unfold tjson_scalar_rostr. split; [|split; [exact HIn | split; [|split]]].
- apply Forall_forall. intros c Hc. pose proof (proj1 (forallb_forall _ _) HF c Hc) as Hb. cbv beta in Hb.
  apply andb_true_iff in Hb as [B1 B2]. apply Z.ltb_lt in B1. apply Z.ltb_lt in B2. lia.
- intros x Hx. apply (jsi_ro _ _ x HIn). lia.
- intros k Hk. exact (jsi_rom_ok _ _ _ HR k Hk).
- intros x Hx. exact (jsi_tail _ _ x HT Hx).
Qed.
Lemma tjson_scalar_roimg_disco : @tjson_scalar_roimg _ PB_disco.
Proof.
unfold tjson_scalar_roimg. rewrite jsi_v20, jsi_v19.
exists 0x21000, 0x21020, 0x21140.
pose proof (jsi_glob_ok _ _ jsi_g_b) as HIn.
split; [exact HIn|]. split; [reflexivity|]. split; [intros x Hx; apply (jsi_ro _ _ x HIn); lia|].
split; [exact (jsi_word_ok _ _ jsi_w1_b)|]. split; [exact (jsi_word_ok _ _ jsi_w2_b)|].
split; [exact (jsi_word_ok _ _ jsi_w3_b)|].
split; [exact (jsi_str_ok _ _ jsi_s1_b)|]. split; [exact (jsi_str_ok _ _ jsi_s2_b)|].
split; [exact (jsi_str_ok _ _ jsi_s3_b)|].
exact (jsi_str_ok _ _ jsi_s4_b).
Qed.
End c.
