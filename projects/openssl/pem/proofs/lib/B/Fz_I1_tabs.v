(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Mem.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Layout RT_iface I_ut Fz_I1_img Fz_I1_defs Fz_I1_load.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint rom_bytes (n : nat) (a : Z) : list byte :=
  match n with O => [] | S n' => match seg_rom bsegs (wa a) with Some b => b | None => Z_to_bv 8 0 end :: rom_bytes n' (a + 1) end.
Definition rom_u64 (a : Z) : Z := bytes_le_to_Z (rom_bytes 8 a).

Lemma rom_bytes_length : forall n a, length (rom_bytes n a) = n.
Proof. induction n as [|n IH]; intros a; cbn [rom_bytes length]; [reflexivity| rewrite IH; reflexivity]. Qed.
Lemma rom_u64_range : forall a, 0 <= rom_u64 a < 2^64.
Proof. intros a. unfold rom_u64. pose proof (img_ble_range (rom_bytes 8 a)) as H. rewrite rom_bytes_length in H. exact H. Qed.

(* [comment removed for export] *)
Fixpoint els_chk (a : Z) (t : nat) : bool :=
  match t with
  | O => true
  | S t' => img_bytes_b a (le8 (Z_to_bv 64 (rom_u64 a))) && Bool.eqb (rom_u64 a =? 0) (Nat.eqb t' 0) && els_chk (a + 16) t'
  end.

Lemma els_chk_spec : forall t a, els_chk a t = true -> forall i, 0 <= i < Z.of_nat t ->
  img_bytes_b (a + 16 * i) (le8 (Z_to_bv 64 (rom_u64 (a + 16 * i)))) = true /\ (rom_u64 (a + 16 * i) = 0 <-> i = Z.of_nat t - 1).
Proof.
  induction t as [|t IH]; intros a H i Hi; [lia|].
  cbn [els_chk] in H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2].
  destruct (Z.eq_dec i 0) as [->|NZ].
  - rewrite Z.mul_0_r, Z.add_0_r. split; [exact H1|]. apply Bool.eqb_prop in H2.
    destruct t; cbn [Nat.eqb] in H2; [apply Z.eqb_eq in H2; split; intros; [cbn; lia| exact H2]|].
    split; [intros E; apply Z.eqb_eq in E; rewrite E in H2; discriminate| intros E; lia].
  - destruct (IH (a + 16) H3 (i - 1) ltac:(lia)) as [X1 X2]. replace (a + 16 + 16 * (i - 1)) with (a + 16 * i) in X1, X2 by lia.
    split; [exact X1|]. rewrite X2. lia.
Qed.

Definition els_okb (str : Z) (n : nat) : bool :=
  (str mod 8 =? 0) && (IMG_UT_LO <=? str) && (str + 16 * (Z.of_nat n + 1) <=? IMG_UT_HI) && els_chk str (S n).

Lemma els_table_ut : forall (GOBJ : Z -> Z -> Prop) str n b sz, GOBJ b sz -> b <= str -> str + 16 * (Z.of_nat n + 1) <= b + sz -> els_okb str n = true ->
  els_table GOBJ str (Z.of_nat n).
Proof.
  intros GOBJ str n b sz G GB GS OK j Hj. unfold els_okb in OK.
  apply andb_prop in OK. destruct OK as [OK CHK]. apply andb_prop in OK. destruct OK as [OK HI]. apply andb_prop in OK. destruct OK as [AL LO].
  apply Z.eqb_eq in AL. apply Z.leb_le in LO. apply Z.leb_le in HI.
  destruct (els_chk_spec (S n) str CHK j ltac:(lia)) as [IMG EZ]. rewrite Nat2Z.inj_succ in EZ.
  exists (rom_u64 (str + 16 * j)). split; [apply rom_u64_range|].
  split. { intros m MI U. apply (ut_ro_cells m (str + 16 * j) [C8 (Z_to_bv 64 (rom_u64 (str + 16 * j)))] U ltac:(cbn; exact (conj I I)) ltac:(cbn [cells_bytes cbytes]; rewrite app_nil_r; exact IMG)
             ltac:(lia) ltac:(cbn [cells_bytes cbytes length app le8 word_to_le_bytes Z_to_le_bytes]; lia)). }
  split; [rewrite EZ; lia|]. split; [clear - AL Hj; Z.div_mod_to_equations; lia|]. split; [unfold IMG_UT_LO in *; lia|]. split; [unfold IMG_UT_HI, SEGTOP_A in *; lia|].
  split; [exists b, sz; split; [exact G| lia]|].
  intros Hjn. split; [clear - AL Hj; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. exists b, sz. split; [exact G| lia].
Qed.

(* [comment removed for export] *)
Lemma els_table_rom0 : forall (GOBJ : Z -> Z -> Prop) str b sz, GOBJ b sz -> b <= str -> str + 16 <= b + sz -> str mod 8 = 0 -> 0x10000 <= str -> str + 16 <= SEGTOP_A ->
  ro_bytes bsegs str (le8 (Z_to_bv 64 0)) -> els_table GOBJ str 0.
Proof.
  intros GOBJ str b sz G GB GS AL LO HI RB j Hj. assert (J : j = 0) by lia. subst j. rewrite Z.mul_0_r, Z.add_0_r.
  exists 0. split; [lia|].
  split. { intros m MI _. split; [cbn; exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply (ro_bytes_at bsegs m str _ MI); [lia| cbn; unfold SEGTOP_A in *; lia| exact RB]. }
  split; [lia|]. split; [exact AL|]. split; [exact LO|]. split; [exact HI|]. split; [exists b, sz; split; [exact G| lia]| intros; lia].
Qed.

(* [comment removed for export] *)
Lemma els_okb_libraries : els_okb 0x567360 43 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_reasons : els_okb 0x5676c0 39 = true. Proof. vm_compute. reflexivity. Qed.
Lemma buf_table_rom : ro_bytes bsegs 0xf1c20 (le8 (Z_to_bv 64 0)). Proof. cbn. repeat split; vm_compute; reflexivity. Qed.
(* [comment removed for export] *)
Lemma els_okb_BN : els_okb 0x5d3780 22 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_RSA : els_okb 0x5d3940 81 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_DH : els_okb 0x5d3fa0 31 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_EVP : els_okb 0x5d4220 125 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_OBJ : els_okb 0x5d4be0 3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_PEM : els_okb 0x5d4c40 34 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_DSA : els_okb 0x5d4f00 16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_X509 : els_okb 0x5d5060 47 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_ASN1 : els_okb 0x5d5420 117 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_CONF : els_okb 0x5d5d40 27 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_CRYPTO : els_okb 0x5d5f60 31 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_COMP : els_okb 0x5d61e0 10 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_EC : els_okb 0x5d62c0 76 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_BIO : els_okb 0x5d68c0 47 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_PKCS7 : els_okb 0x5d6c80 38 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_X509V3 : els_okb 0x5d6f80 73 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_PKCS12 : els_okb 0x5d7540 22 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_RAND : els_okb 0x5d7700 45 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_DSO : els_okb 0x5d7a80 16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_TS : els_okb 0x5d7be0 39 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_HTTP : els_okb 0x5d7f00 32 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_OCSP : els_okb 0x5d81a0 25 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_UI : els_okb 0x5d83a0 13 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_CMS : els_okb 0x5d84a0 102 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_CRMF : els_okb 0x5d8ca0 30 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_CMP : els_okb 0x5d8f00 106 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_CT : els_okb 0x5d9760 17 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_ESS : els_okb 0x5d98c0 9 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_ASYNC : els_okb 0x5d9980 4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_SM2 : els_okb 0x5d9a00 14 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_OSSL_STORE : els_okb 0x5d9b20 25 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_PROP : els_okb 0x5d9d20 11 = true. Proof. vm_compute. reflexivity. Qed.
Lemma els_okb_PROV : els_okb 0x5d9e00 160 = true. Proof. vm_compute. reflexivity. Qed.
