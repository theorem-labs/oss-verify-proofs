(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface AllocSim
     AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlanSoundSums L5Defs L5Core.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5K.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Definition CS : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Lemma regs_preserved_by_index (R R' : bvmap 5 word) :
  (forall i, In i CS -> getr R' (reg i) = getr R (reg i)) -> regs_preserved R R'.
Proof.
  intros K r Hr. rewrite <- (ridx_roundtrip r). apply K.
  unfold callee_saved_idx in Hr. unfold ridx. set (z := bv_unsigned r) in *. cbn in Hr.
  repeat (destruct Hr as [Hr|Hr]; [rewrite <- Hr; cbn; tauto|]). destruct Hr.
Qed.

Lemma regs_preserved_index (R R' : bvmap 5 word) i :
  regs_preserved R R' -> In i CS -> getr R' (reg i) = getr R (reg i).
Proof.
  intros P Hi. apply P. unfold callee_saved_idx. cbn in Hi.
  repeat (destruct Hi as [<-|Hi]; [cbn; tauto|]). destruct Hi.
Qed.

Lemma client_inner L LB sp scr sp' scr' a :
  client_addr L LB sp scr a -> sp - scr <= sp' - scr' -> sp' <= sp -> client_addr L LB sp' scr' a.
Proof.
  intros CA H1 H2. destruct CA as [IB|[[S1 S2]|IM]]. left; exact IB. right; left; split; [exact S1|lia]. right; right; exact IM.
Qed.

Lemma kept_ok_index (R R' : bvmap 5 word) i : APSX.kept_ok R R' -> In i CS -> getr R' (reg i) = getr R (reg i).
Proof.
  intros K Hi. apply K.
  - intros E. apply (f_equal bv_unsigned) in E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E.
    change (bv_unsigned (0%bv : bv 5)) with 0 in E. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [vm_compute in E; discriminate|]). destruct Hi.
  - unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. unfold APC.caller_saved.
    cbn in Hi. repeat (destruct Hi as [<-|Hi]; [vm_compute; intros HH; repeat (destruct HH as [HH|HH]; [discriminate|]); exact HH|]). destruct Hi.
Qed.

Lemma kept_sub (R R' : bvmap 5 word) (ks ks' : list nat) :
  (forall i, In i ks -> getr R' (reg i) = getr R (reg i)) -> incl ks' ks -> forall i, In i ks' -> getr R' (reg i) = getr R (reg i).
Proof. intros K Hi i Hin. apply K. apply Hi. exact Hin. Qed.

Lemma ret_ok_lit (r : Z) : L5.ra_ok r -> Hoare.ret_ok (Z_to_bv 64 r).
Proof.
  intros [Hr He]. apply Hoare.ret_ok_even. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small r (2 ^ 64)) by lia. exact He.
Qed.

Lemma lit_neq (a b : Z) : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a <> b -> Z_to_bv 64 a <> Z_to_bv 64 b.
Proof.
  intros Ha Hb Hne E. apply Hne. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 64) with (2 ^ 64) in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma In_of_mem (j : nat) (l : list nat) : existsb (Nat.eqb j) l = true -> In j l.
Proof. intros H. apply existsb_exists in H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx. Qed.

Ltac inlist H := cbn in H; repeat (destruct H as [<-|H]; [apply In_of_mem; reflexivity|]); destruct H.

Lemma u64_zero_of_fill segs M (dst : Z) (k : nat) (j : Z) :
  0 <= dst -> dst + Z.of_nat k <= 2 ^ 64 -> 0 <= j -> j + 8 <= Z.of_nat k ->
  L5.u64_at segs (wbytes M (Z_to_bv 64 dst) (repeat (Z_to_bv 8 0) k)) (dst + j) 0.
Proof.
  intros Hd Hk Hj Hjk. unfold L5.u64_at. change (word_to_le_bytes 8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0 : byte) 8).
  apply APSX.rdn_overlay_all. { rewrite L5.unsigned_lit by lia. cbn. lia. }
  intros i Hi. rewrite L5.unsigned_lit by lia.
  replace (dst + j + i) with (bv_unsigned (Z_to_bv 64 dst) + Z.of_nat (Z.to_nat (j + i))) by (rewrite L5.unsigned_lit by lia; lia).
  rewrite AX2S.wbytes_nth. f_equal. apply nth_repeat. rewrite L5.unsigned_lit by lia. rewrite repeat_length. lia. rewrite repeat_length. cbn in Hi. lia.
Qed.

Lemma wbytes_fill_out segs M (dst : Z) (k : nat) (a : Z) (n : nat) :
  0 <= dst < 2 ^ 64 -> dst + Z.of_nat k <= 2 ^ 64 -> 0 <= a < 2 ^ 64 -> a + Z.of_nat n <= 2 ^ 64 ->
  (a + Z.of_nat n <= dst \/ dst + Z.of_nat k <= a) ->
  rdn segs (wbytes M (Z_to_bv 64 dst) (repeat (Z_to_bv 8 0) k)) (Z_to_bv 64 a) n = rdn segs M (Z_to_bv 64 a) n.
Proof.
  intros Hd Hk Ha Hn Hap. apply rdn_wbytes_out; rewrite ?L5.unsigned_lit by lia; rewrite ?repeat_length; lia.
Qed.

Definition limb_bytes (ws : list Z) : list byte := flat_map (fun w => word_to_le_bytes 8 (Z_to_bv 64 w)) ws.

Lemma limb_bytes_length ws : length (limb_bytes ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]. reflexivity. cbn [limb_bytes flat_map]. rewrite length_app, length_N_to_le_bytes. unfold limb_bytes in IH. rewrite IH. cbn [length]. lia. Qed.

Lemma rdn_of_limbs_at segs M : forall ws q, L5.limbs_at segs M q ws -> 0 <= q -> q + 8 * Z.of_nat (length ws) <= 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 q) (8 * length ws)%nat = Some (limb_bytes ws).
Proof.
  induction ws as [|w ws IH]; intros q HL Hq Hn. reflexivity.
  cbn [length] in Hn. replace (8 * length (w :: ws))%nat with (8 + 8 * length ws)%nat by (cbn [length]; lia).
  change (limb_bytes (w :: ws)) with (word_to_le_bytes 8 (Z_to_bv 64 w) ++ limb_bytes ws).
  apply SeqExec.rdn_app.
  - pose proof (HL 0%nat ltac:(cbn; lia)) as H0. cbn [nth] in H0. unfold L5.u64_at in H0. rewrite Z.add_0_r in H0. exact H0.
  - unfold nat_to_word.
    replace (Z_to_bv 64 q + Z_to_bv 64 (Z.of_nat 8))%bv with (Z_to_bv 64 (q + 8)).
    2: { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
         rewrite <- Z.add_mod by lia. reflexivity. }
    apply IH. intros i Hi. replace (q + 8 + 8 * Z.of_nat i) with (q + 8 * Z.of_nat (S i)) by lia.
    change (nth i ws 0) with (nth (S i) (w :: ws) 0). apply HL. cbn; lia. lia. lia.
Qed.

Lemma limbs_at_of_wbytes segs : forall ws M dst, 0 <= dst -> dst + 8 * Z.of_nat (length ws) < 2 ^ 64 ->
  L5.limbs_at segs (wbytes M (Z_to_bv 64 dst) (limb_bytes ws)) dst ws.
Proof.
  induction ws as [|w ws IH]; intros M dst Hd Hn. apply L5C.limbs_at_nil.
  cbn [length] in Hn.
  change (limb_bytes (w :: ws)) with (word_to_le_bytes 8 (Z_to_bv 64 w) ++ limb_bytes ws).
  rewrite AllocSim.wbytes_app. rewrite length_N_to_le_bytes. unfold nat_to_word.
  replace (Z_to_bv 64 dst + Z_to_bv 64 (Z.of_nat 8))%bv with (Z_to_bv 64 (dst + 8)).
  2: { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
       rewrite <- Z.add_mod by lia. reflexivity. }
  intros i Hi. destruct i as [|i].
  - cbn [nth]. unfold L5.u64_at. rewrite Z.add_0_r.
    rewrite rdn_wbytes_out. 2: { left. rewrite !L5.unsigned_lit by lia. cbn. lia. } 2: { rewrite L5.unsigned_lit by lia. cbn. lia. }
    2: { rewrite L5.unsigned_lit by lia. rewrite limb_bytes_length. lia. }
    rewrite <- (length_N_to_le_bytes 8 (Z_to_bv 64 w)) at 1. apply SeqExec.rdn_wbytes_hit. rewrite L5.unsigned_lit by lia. rewrite length_N_to_le_bytes. lia.
  - cbn [nth]. replace (dst + 8 * Z.of_nat (S i)) with (dst + 8 + 8 * Z.of_nat i) by lia. apply IH. lia. lia. cbn in Hi. lia.
Qed.

Lemma wbytes_limbs_out segs M dst ws (a : Z) (n : nat) :
  0 <= dst < 2 ^ 64 -> dst + 8 * Z.of_nat (length ws) <= 2 ^ 64 -> 0 <= a < 2 ^ 64 -> a + Z.of_nat n <= 2 ^ 64 ->
  (a + Z.of_nat n <= dst \/ dst + 8 * Z.of_nat (length ws) <= a) ->
  rdn segs (wbytes M (Z_to_bv 64 dst) (limb_bytes ws)) (Z_to_bv 64 a) n = rdn segs M (Z_to_bv 64 a) n.
Proof.
  intros Hd Hn Ha Han Hap. apply rdn_wbytes_out; rewrite ?L5.unsigned_lit by lia; rewrite ?limb_bytes_length; lia.
Qed.
Lemma wbytes_limbs_out1 M dst ws (a : Z) :
  0 <= dst < 2 ^ 64 -> dst + 8 * Z.of_nat (length ws) <= 2 ^ 64 -> 0 <= a < 2 ^ 64 ->
  ~ (dst <= a < dst + 8 * Z.of_nat (length ws)) -> wbytes M (Z_to_bv 64 dst) (limb_bytes ws) (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros Hd Hn Ha Hna. apply AX2S.wbytes_out; rewrite ?L5.unsigned_lit, ?limb_bytes_length by lia; lia.
Qed.

Lemma byte_cases (P : Z -> bool) : forallb (fun i => P (Z.of_nat i)) (seq 0 256) = true -> forall fb, 0 <= fb < 256 -> P fb = true.
Proof.
  intros H fb Hfb. rewrite forallb_forall in H. replace fb with (Z.of_nat (Z.to_nat fb)) by lia. apply H. apply in_seq. lia.
Qed.

Lemma rl1 : (1%bv : bv 5) = reg 1. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl2 : (2%bv : bv 5) = reg 2. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl3 : (3%bv : bv 5) = reg 3. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl4 : (4%bv : bv 5) = reg 4. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl5 : (5%bv : bv 5) = reg 5. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl6 : (6%bv : bv 5) = reg 6. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl7 : (7%bv : bv 5) = reg 7. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl8 : (8%bv : bv 5) = reg 8. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl9 : (9%bv : bv 5) = reg 9. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl10 : (10%bv : bv 5) = reg 10. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl11 : (11%bv : bv 5) = reg 11. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl12 : (12%bv : bv 5) = reg 12. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl13 : (13%bv : bv 5) = reg 13. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl14 : (14%bv : bv 5) = reg 14. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl15 : (15%bv : bv 5) = reg 15. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl16 : (16%bv : bv 5) = reg 16. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl17 : (17%bv : bv 5) = reg 17. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl18 : (18%bv : bv 5) = reg 18. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl19 : (19%bv : bv 5) = reg 19. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl20 : (20%bv : bv 5) = reg 20. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl21 : (21%bv : bv 5) = reg 21. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl22 : (22%bv : bv 5) = reg 22. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl23 : (23%bv : bv 5) = reg 23. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl24 : (24%bv : bv 5) = reg 24. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl25 : (25%bv : bv 5) = reg 25. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl26 : (26%bv : bv 5) = reg 26. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl27 : (27%bv : bv 5) = reg 27. Proof. apply bv_eq. reflexivity. Qed.

End L5K.
