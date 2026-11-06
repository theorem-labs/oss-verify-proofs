(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac.
From OSSVerify.Proofs.openssl.punycode.lib.LibU Require Import UCode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_mc stops := wp_go 0x2bc8ec 257%nat C_memcpy_eq C_memcpy stops.

Lemma mod_once : forall m k, 0 < k -> k <= m < 2 * k -> m mod k = m - k.
Proof. intros m k Hk H. symmetry. apply Z.mod_unique with 1; lia. Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Memcpy.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (d s n : Z).
Hypothesis Hn : 0 <= n < 32.
Hypothesis Hs : 0 <= s /\ s + n < 2 ^ 64.
Hypothesis Hd : 0 <= d /\ d + n < 2 ^ 64.
Hypothesis Hrd : rd_ok M s n.
Hypothesis Hwr : wr_ok USEGS M d n.

Definition KS : list nat := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28]%nat.
Definition FP (x : word) : Prop := inr x d n.
Variable l0 : regfile.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KS l0 l' ->
  unch M M' FP -> mem_grows M M' ->
  reach USEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

Definition MI (M' : mem) : Prop := unch M M' FP /\ mem_grows M M'.

(* [comment removed for export] *)
Ltac mem_steps HG :=
  repeat lazymatch goal with
    | |- exists v, load_ok _ ?Mc ?aw ?k v /\ _ =>
        let v := fresh "v" in let Hv := fresh "Hv" in
        assert (exists v, load_ok USEGS Mc aw k v) as [v Hv]
          by (rewrite ?addi_W; eapply load_rd; [eapply rd_ok_grows; [|exact Hrd]; solve_grows | lia..]);
        exists v; split; [exact Hv|]; clear Hv
    | |- store_ok _ ?Mc ?aw ?k = true /\ _ =>
        split; [rewrite ?addi_W; eapply wr_ok_store; [eapply wr_ok_grows; [|exact Hwr]; solve_grows | lia | lia]|]
    end.

Ltac leaf_K Hse HU HG :=
  rewrite ?addi_W;
  let Hra := fresh "Hra" in
  pose proof (Hse 1%nat ltac:(cbv; intuition lia)) as Hra; cbn [rget lget] in Hra;
  match type of Hra with ?x = _ => subst x end;
  apply K; [reflexivity | eapply same_except_trans; [exact Hse | same_ex]
           | solve_unch ltac:(unfold FP, inr in *; lia) | solve_grows].

(* [comment removed for export] *)
Lemma tail2 : forall j m l M', MI M' -> 0 <= j -> 0 <= m < 2 ^ 64 -> j + m mod 4 = n ->
  length l = 32%nat -> same_except KS l0 l ->
  rget l 11 = W (s + j) -> rget l 12 = W m -> rget l 13 = W (d + j) ->
  reach USEGS rom (Z_to_bv 64 0x2bccac) l M' Post.
Proof.
  intros j m l M' [HU HG] Hj Hm Hrel Hl Hse H11 H12 H13. regs_open l Hl. subst a1 a2 a3.
  destruct (bit_test m 1 2 eq_refl Hm ltac:(lia)) as [B2y B2n].
  destruct (bit_test m 0 1 eq_refl Hm ltac:(lia)) as [B1y B1n].
  assert (E1 : m mod 1 = 0) by apply Z.mod_1_r.
  change (2 * 2) with 4 in *. change (2 * 1) with 2 in *.
  pose proof (Z.mod_pos_bound m 2 ltac:(lia)) as R2.
  wp_mc (@nil Z). split; intros Hb.
  - specialize (B2y Hb). clear B2n Hb. mem_steps HG. split; intros Hb.
    + specialize (B1n Hb). clear B1y Hb. leaf_K Hse HU HG.
    + specialize (B1y Hb). clear B1n Hb. mem_steps HG. leaf_K Hse HU HG.
  - specialize (B2n Hb). clear B2y Hb. split; intros Hb.
    + specialize (B1y Hb). clear B1n Hb. mem_steps HG. leaf_K Hse HU HG.
    + specialize (B1n Hb). clear B1y Hb. leaf_K Hse HU HG.
Qed.

(* [comment removed for export] *)
Ltac leaf_to L jj mm Hse :=
  rewrite ?addi_W;
  eapply (L jj mm); [ split; [solve_unch ltac:(unfold FP, inr in *; lia) | solve_grows] | lia | lia | lia | reflexivity
                    | eapply same_except_trans; [exact Hse | same_ex] | .. ];
  cbn [rget lget]; try reflexivity; f_equal; lia.

(* [comment removed for export] *)
Lemma copy4m : forall j m l M', MI M' -> 0 <= j -> 0 <= m < 2 ^ 64 -> j + 4 + m mod 4 = n ->
  length l = 32%nat -> same_except KS l0 l ->
  rget l 11 = W (s + j) -> rget l 12 = W m -> rget l 13 = W (d + j) ->
  reach USEGS rom (Z_to_bv 64 0x2bcc80) l M' Post.
Proof.
  intros j m l M' [HU HG] Hj Hm Hrel Hl Hse H11 H12 H13. regs_open l Hl. subst a1 a2 a3.
  pose proof (Z.mod_pos_bound m 4 ltac:(lia)) as R4.
  wp_mc [0x2bccac]. mem_steps HG. leaf_to tail2 (j + 4) m Hse.
Qed.

(* [comment removed for export] *)
Lemma blk8m : forall j m l M', MI M' -> 0 <= j -> 0 <= m < 2 ^ 64 -> j + 8 + m mod 8 = n ->
  length l = 32%nat -> same_except KS l0 l ->
  rget l 11 = W (s + j) -> rget l 12 = W m -> rget l 13 = W (d + j) ->
  reach USEGS rom (Z_to_bv 64 0x2bcc2c) l M' Post.
Proof.
  intros j m l M' [HU HG] Hj Hm Hrel Hl Hse H11 H12 H13. regs_open l Hl. subst a1 a2 a3.
  destruct (bit_test m 2 4 eq_refl Hm ltac:(lia)) as [By Bn]. change (2 * 4) with 8 in *.
  pose proof (Z.mod_pos_bound m 4 ltac:(lia)) as R4. pose proof (Z.mod_pos_bound m 8 ltac:(lia)) as R8.
  wp_mc [0x2bcc80; 0x2bccac]. mem_steps HG. split; intros Hb.
  - specialize (Bn Hb). clear By Hb. leaf_to tail2 (j + 8) m Hse.
  - specialize (By Hb). clear Bn Hb. leaf_to copy4m (j + 8) m Hse.
Qed.

(* [comment removed for export] *)
Lemma test8m : forall j m l M', MI M' -> 0 <= j -> 0 <= m < 2 ^ 64 -> j + m mod 16 = n ->
  length l = 32%nat -> same_except KS l0 l ->
  rget l 11 = W (s + j) -> rget l 12 = W m -> rget l 13 = W (d + j) ->
  reach USEGS rom (Z_to_bv 64 0x2bcc24) l M' Post.
Proof.
  intros j m l M' [HU HG] Hj Hm Hrel Hl Hse H11 H12 H13. regs_open l Hl. subst a1 a2 a3.
  destruct (bit_test m 3 8 eq_refl Hm ltac:(lia)) as [B8y B8n]. change (2 * 8) with 16 in *.
  destruct (bit_test m 2 4 eq_refl Hm ltac:(lia)) as [B4y B4n]. change (2 * 4) with 8 in *.
  pose proof (Z.mod_pos_bound m 4 ltac:(lia)) as R4. pose proof (Z.mod_pos_bound m 8 ltac:(lia)) as R8.
  wp_mc [0x2bcc2c; 0x2bcc80; 0x2bccac]. split; intros Hb.
  - specialize (B8n Hb). clear B8y Hb. split; intros Hb.
    + specialize (B4y Hb). clear B4n Hb. leaf_to copy4m j m Hse.
    + specialize (B4n Hb). clear B4y Hb. leaf_to tail2 j m Hse.
  - specialize (B8y Hb). clear B8n Hb. leaf_to blk8m j m Hse.
Qed.

(* [comment removed for export] *)
Lemma blk16m : forall j m l M', MI M' -> 0 <= j -> 0 <= m < 2 ^ 64 -> j + 16 + m mod 16 = n ->
  length l = 32%nat -> same_except KS l0 l ->
  rget l 11 = W (s + j) -> rget l 12 = W m -> rget l 13 = W (d + j) ->
  reach USEGS rom (Z_to_bv 64 0x2bcb98) l M' Post.
Proof.
  intros j m l M' [HU HG] Hj Hm Hrel Hl Hse H11 H12 H13. regs_open l Hl. subst a1 a2 a3.
  pose proof (Z.mod_pos_bound m 16 ltac:(lia)) as R16.
  wp_mc [0x2bcc24]. mem_steps HG. leaf_to test8m (j + 16) m Hse.
Qed.

(* [comment removed for export] *)
Lemma mis_entry : forall j m l M', MI M' -> 0 <= j -> 0 <= m < 32 -> j + m = n ->
  length l = 32%nat -> same_except KS l0 l ->
  rget l 11 = W (s + j) -> rget l 12 = W m -> rget l 13 = W (d + j) ->
  reach USEGS rom (Z_to_bv 64 0x2bc93c) l M' Post.
Proof.
  intros j m l M' [HU HG] Hj Hm Hrel Hl Hse H11 H12 H13. regs_open l Hl. subst a1 a2 a3.
  assert (Hm64 : 0 <= m < 2 ^ 64) by lia.
  destruct (bit_test m 3 8 eq_refl Hm64 ltac:(lia)) as [B8y B8n]. change (2 * 8) with 16 in *.
  destruct (bit_test m 2 4 eq_refl Hm64 ltac:(lia)) as [B4y B4n]. change (2 * 4) with 8 in *.
  pose proof (Z.mod_pos_bound m 4 ltac:(lia)) as R4. pose proof (Z.mod_pos_bound m 8 ltac:(lia)) as R8.
  wp_mc [0x2bc960; 0x2bcb98; 0x2bcc2c; 0x2bcc80; 0x2bccac]. rewrite !Wu by lia.
  split; intros Hb; [exfalso; lia|]. clear Hb. split; intros Hb.
  - pose proof (mod_once m 16 ltac:(lia) ltac:(lia)) as E16. leaf_to blk16m j m Hse.
  - pose proof (Z.mod_small m 16 ltac:(lia)) as E16. split; intros Hb2.
    + specialize (B8y Hb2). clear B8n Hb2. leaf_to blk8m j m Hse.
    + specialize (B8n Hb2). clear B8y Hb2. split; intros Hb3.
      * specialize (B4y Hb3). clear B4n Hb3. leaf_to copy4m j m Hse.
      * specialize (B4n Hb3). clear B4y Hb3. leaf_to tail2 j m Hse.
Qed.

(* [comment removed for export] *)
Lemma al_tail : forall j m l M', MI M' -> 0 <= j -> 0 <= m < 16 -> j + m = n ->
  length l = 32%nat -> same_except KS l0 l ->
  rget l 11 = W (s + j) -> rget l 12 = W m -> rget l 13 = W (d + j) ->
  reach USEGS rom (Z_to_bv 64 0x2bca48) l M' Post.
Proof.
  intros j m l M' [HU HG] Hj Hm Hrel Hl Hse H11 H12 H13. regs_open l Hl. subst a1 a2 a3.
  assert (Hm64 : 0 <= m < 2 ^ 64) by lia.
  destruct (bit_test m 2 4 eq_refl Hm64 ltac:(lia)) as [B4y B4n]. change (2 * 4) with 8 in *.
  pose proof (Z.mod_pos_bound m 4 ltac:(lia)) as R4. pose proof (Z.mod_pos_bound m 8 ltac:(lia)) as R8.
  wp_mc [0x2bccac]. rewrite !Wu by lia. split; intros Hb.
  - pose proof (Z.mod_small m 8 ltac:(lia)) as E8. split; intros Hb2.
    + specialize (B4n Hb2). clear B4y Hb2. leaf_to tail2 j m Hse.
    + specialize (B4y Hb2). clear B4n Hb2. mem_steps HG. leaf_to tail2 (j + 4) m Hse.
  - pose proof (mod_once m 8 ltac:(lia) ltac:(lia)) as E8. mem_steps HG. split; intros Hb2.
    + specialize (B4n Hb2). clear B4y Hb2. leaf_to tail2 (j + 8) m Hse.
    + specialize (B4y Hb2). clear B4n Hb2. mem_steps HG. leaf_to tail2 (j + 8 + 4) m Hse.
Qed.

(* [comment removed for export] *)
Lemma loop16 : forall j m l M', MI M' -> 0 <= j -> 16 <= m < 32 -> j + m = n ->
  length l = 32%nat -> same_except KS l0 l ->
  rget l 11 = W (s + j) -> rget l 12 = W m -> rget l 13 = W (d + j) -> rget l 14 = W 15 ->
  reach USEGS rom (Z_to_bv 64 0x2bca18) l M' Post.
Proof.
  intros j m l M' [HU HG] Hj Hm Hrel Hl Hse H11 H12 H13 H14. regs_open l Hl. subst a1 a2 a3 a4.
  wp_mc [0x2bca18; 0x2bca48]. mem_steps HG. rewrite ?addi_W. rewrite !Wu by lia.
  split; intros Hb; [exfalso; lia|]. clear Hb. leaf_to al_tail (j + 16) (m - 16) Hse.
Qed.

Lemma al_entry : forall j m l M', MI M' -> 0 <= j -> 0 <= m < 32 -> j + m = n ->
  length l = 32%nat -> same_except KS l0 l ->
  rget l 11 = W (s + j) -> rget l 12 = W m -> rget l 13 = W (d + j) ->
  reach USEGS rom (Z_to_bv 64 0x2bca0c) l M' Post.
Proof.
  intros j m l M' [HU HG] Hj Hm Hrel Hl Hse H11 H12 H13. regs_open l Hl. subst a1 a2 a3.
  wp_mc [0x2bca18; 0x2bca48]. rewrite !Wu by lia. split; intros Hb.
  - leaf_to al_tail j m Hse.
  - rewrite ?addi_W. eapply (loop16 j m); [ split; [solve_unch ltac:(unfold FP, inr in *; lia) | solve_grows] | lia | lia | lia | reflexivity
                    | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try reflexivity; f_equal; lia.
Qed.

(* [comment removed for export] *)
Lemma post_align : forall j m l M', MI M' -> 0 <= j -> 0 <= m < 32 -> j + m = n ->
  length l = 32%nat -> same_except KS l0 l ->
  rget l 11 = W (s + j) -> rget l 12 = W m -> rget l 13 = W (d + j) ->
  reach USEGS rom (Z_to_bv 64 0x2bc934) l M' Post.
Proof.
  intros j m l M' [HU HG] Hj Hm Hrel Hl Hse H11 H12 H13. regs_open l Hl. subst a1 a2 a3.
  wp_mc [0x2bca0c; 0x2bc93c]. split; intros Hb; clear Hb.
  - leaf_to al_entry j m Hse.
  - leaf_to mis_entry j m Hse.
Qed.

(* [comment removed for export] *)
Lemma aloop : forall k j l M', n - j = Z.of_nat k -> MI M' -> 0 <= j < n ->
  length l = 32%nat -> same_except KS l0 l ->
  rget l 11 = W (s + j) -> rget l 12 = W (n - j) -> rget l 13 = W (d + j) ->
  rget l 14 = W (s + j + 1) -> rget l 15 = W 1 ->
  reach USEGS rom (Z_to_bv 64 0x2bc904) l M' Post.
Proof.
  induction k as [k IH] using lt_wf_ind; intros j l M' Hk [HU HG] Hj Hl Hse H11 H12 H13 H14 H15.
  regs_open l Hl. subst a1 a2 a3 a4 a5.
  wp_mc [0x2bc904; 0x2bc934]. mem_steps HG. split; intros Hb; clear Hb.
  - leaf_to post_align (j + 1) (n - j - 1) Hse.
  - rewrite !Wu by lia. split; intros Hb.
    + rewrite ?addi_W.
      eapply (IH (Z.to_nat (n - (j + 1)))) with (j := j + 1);
        [ lia | lia | split; [solve_unch ltac:(unfold FP, inr in *; lia) | solve_grows] | lia | reflexivity
        | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try reflexivity; f_equal; lia.
    + leaf_to post_align (j + 1) (n - j - 1) Hse.
Qed.

Lemma memcpy_body : forall l, length l = 32%nat -> l = l0 ->
  rget l 10 = W d -> rget l 11 = W s -> rget l 12 = W n ->
  reach USEGS rom (Z_to_bv 64 0x2bc8ec) l M Post.
Proof.
  intros l Hl El H10 H11 H12. assert (Hse : same_except KS l0 l) by (subst l; apply same_except_refl).
  clear El. regs_open l Hl. subst a0 a1 a2.
  assert (HMI : MI M) by (split; [apply unch_refl | apply mem_grows_refl]). destruct HMI as [HU HG].
  wp_mc [0x2bc904; 0x2bc934; 0x2bc93c; 0x2bca0c]. split; intros Hb; clear Hb.
  - split; intros Hb; clear Hb.
    + leaf_to mis_entry 0 n Hse.
    + leaf_to al_entry 0 n Hse.
  - rewrite !Wu by lia. split; intros Hb.
    + leaf_to post_align 0 n Hse.
    + rewrite ?addi_W.
      eapply (aloop (Z.to_nat (n - 0)) 0);
        [ lia | split; [solve_unch ltac:(unfold FP, inr in *; lia) | solve_grows] | lia | reflexivity
        | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try reflexivity; f_equal; lia.
Qed.

End Memcpy.

(* [comment removed for export] *)
Theorem memcpy_cps : forall rom Post M d s n l,
  0 <= n < 32 -> 0 <= s /\ s + n < 2 ^ 64 -> 0 <= d /\ d + n < 2 ^ 64 ->
  rd_ok M s n -> wr_ok USEGS M d n ->
  length l = 32%nat -> rget l 10 = W d -> rget l 11 = W s -> rget l 12 = W n ->
  (forall l' M', length l' = 32%nat -> same_except KS l l' -> unch M M' (FP d n) -> mem_grows M M' ->
                 reach USEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach USEGS rom (Z_to_bv 64 0x2bc8ec) l M Post.
Proof. intros rom Post M d s n l; intros. eapply (memcpy_body rom Post M d s n) with (l0 := l); eauto. Qed.

(* [comment removed for export] *)
