(** Facts for the UBSan walk of expect_of (fuzz_headamp.c:109-157; UBSan LLVMFuzzerTestOneInput 0x14198 -> 0x14784)
    beyond the image-independent ones of Prog/HeadCheck/Facts.v and PairFacts.v: strncmp(k, "reac.headamp.", 13)
    under the UBSan library's strncmp_model, the key test `snez; addi -1; and` of the compiled pod_string, the
    pointer-overflow bounds the sanitizer compares against (`~p`, kept as 2^64 - 1 - p), and x->rc's four bytes of the
    32-bit -1. No function of a binary is proved here. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Accessors Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import Facts PairFacts.
Import ListNotations.
Open Scope Z_scope.

(** ** strncmp(k, "reac.headamp.", 13) under the UBSan library's model *)
(** The UBSan library's strncmp model (U/Spec/StrFun.v) is the plain one (Spec/StrFun.v) word for word. *)
Lemma strncmp_walk_u : forall l r k, U.Spec.StrFun.strncmp_walk l r k = lib.Spec.StrFun.strncmp_walk l r k.
Proof. intros l r k. reflexivity. Qed.

Lemma strncmp_model_u : forall l r n, U.Spec.StrFun.strncmp_model l r n = lib.Spec.StrFun.strncmp_model l r n.
Proof. intros l r n. reflexivity. Qed.

(** strncmp(k, prefix, 13) on the C string k: a byte difference, 0 exactly when k has the prefix. *)
Lemma strncmp_prefix_u : forall k, ~ In NUL k ->
  exists v, U.Spec.StrFun.strncmp_model (k ++ [NUL]) (HA_PREFIX ++ [NUL]) 13 = Some v /\ -256 < v < 256 /\
            (v = 0 <-> ha_prefix k = true).
Proof. intros k HK. rewrite strncmp_model_u. exact (strncmp_prefix k HK). Qed.

(** ** pod_string's last-byte test: `lbu; snez; addi -1; and` with the body address *)
Lemma snez_mask : forall (b : byte) A, 0 <= A < 2^64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 0) (zxb b)) + -1)))
                     (bv_unsigned (Z_to_bv 64 A)))
  = Z_to_bv 64 (if bv_unsigned b =? 0 then A else 0).
Proof.
  intros b A HA. rewrite v_sltu_b2z. unfold zxb. pose proof (byte_range b) as Hb.
  rewrite (unsigned_lit (bv_unsigned b)) by lia. rewrite (unsigned_lit A) by lia.
  change (bv_unsigned (Z_to_bv 64 0)) with 0.
  destruct (Z.ltb_spec 0 (bv_unsigned b)) as [H|H].
  - replace (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.b2z true)) + -1))) with 0 by reflexivity.
    rewrite Z.land_0_l. rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
  - replace (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.b2z false)) + -1))) with (Z.ones 64) by reflexivity.
    rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
    reflexivity.
Qed.

(** ** The pointer-overflow bounds *)
(** A bound ~p less k (`sub` / `addi -k` of the walk), while p + k stays below 2^64. *)
Lemma unsigned_sub_bound : forall (x : word) d k, bv_unsigned x = 2^64 - d -> 0 <= k -> 0 < d -> d + k < 2^64 ->
  bv_unsigned (Z_to_bv 64 (bv_unsigned x - k)) = 2^64 - (d + k).
Proof. intros x d k H H1 H2 H3. rewrite H. rewrite unsigned_lit by lia. lia. Qed.

Lemma unsigned_not : forall p, 0 <= p < 2^64 -> bv_unsigned (Z_to_bv 64 (2^64 - 1 - p)) = 2^64 - 1 - p.
Proof. intros p Hp. apply unsigned_lit. lia. Qed.

(** ** x->rc *)
(** `srli s9, -1, 32` stores the four bytes of the 32-bit -1. *)
Lemma le4_m1 : le4 (Z_to_bv 64 4294967295) = le4 (Z_to_bv 64 (-1)).
Proof.
  unfold le4. rewrite !unsigned_lit_wrap.
  rewrite <- (Z_to_le_bytes_mod 4 (4294967295 mod 2^64) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (-1 mod 2^64) 32) by (cbn; lia).
  reflexivity.
Qed.
