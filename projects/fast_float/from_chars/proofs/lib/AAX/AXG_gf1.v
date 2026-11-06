(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_np3 AXG_np4 AXG_nf1 AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np4 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.AXG_npb OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma gsrlw1 : forall R V mc, nth 2 V 0 = mc -> 0 <= mc < 2^31 ->
  bv_unsigned (edenot (Ez R V) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1))) = mc / 2.
Proof.
  intros R V mc Hv Hm. cbn [edenot]. rewrite w_srlw. unfold v_srlw, ext_val.
  rewrite (zatom R V 34 mc eq_refl Hv) by lia. rewrite ext_Z_lo32_small by lia.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 mc)) with (bv_unsigned (wa mc)). rewrite (u_wa_small mc) by lia.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). rewrite (Z.mod_small mc) by lia.
  change (1 mod 32) with 1. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  change (32%N) with (8 * N.of_nat 4)%N. rewrite swrap32_small by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  change (bv_unsigned (Z_to_bv 64 (mc / 2))) with (bv_unsigned (wa (mc / 2))).
  apply u_wa_small. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
Qed.

(* [comment removed for export] *)
Lemma cls30 : forall c, 1 <= c <= 30 -> c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/
  c = 14 \/ c = 15 \/ c = 16 \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30.
Proof. intros c H. lia. Qed.
Ltac cls30_go c H := let X := fresh "X" in pose proof (cls30 c H) as X; repeat (destruct X as [->|X]); [.. | subst c].

Lemma gmc_rng : forall c, 1 <= c <= 30 -> 2 <= mc_tbl c <= 16 /\ mc_tbl c mod 2 = 0.
Proof. intros c H. cls30_go c H; cbn; lia. Qed.
Lemma gmc_big : forall c, 17 <= c <= 30 -> mc_tbl c = 2.
Proof. intros c H. assert (H' : 1 <= c <= 30) by lia. cls30_go c H'; first [reflexivity | lia]. Qed.
Lemma gsz_rng : forall c, 1 <= c <= 30 -> 32 <= sz_tbl c <= 65536 /\ sz_tbl c mod 16 = 0 /\ sz_tbl c * (mc_tbl c / 2) <= 262144.
Proof. intros c H. cls30_go c H; cbn; lia. Qed.
Lemma gsz_small : forall c, 1 <= c <= 16 -> sz_tbl c = 32 * c.
Proof. intros c H. assert (H' : 1 <= c <= 30) by lia. cls30_go c H'; first [reflexivity | lia]. Qed.
Lemma gnew_rng : forall c, 1 <= c <= 30 -> 4 <= 262144 / sz_tbl c <= 8192 /\ 262144 / sz_tbl c * sz_tbl c <= 262144.
Proof. intros c H. cls30_go c H; cbn; lia. Qed.

(* [comment removed for export] *)
Definition gL3a (c CA n RI RB FA : Z) : list (Z * nat * Z) := [(-456, 8%nat, sz_tbl c); (-448, 8%nat, 1525856); (-440, 8%nat, 96458); (-432, 8%nat, RB); (-424, 8%nat, 1); (-416, 8%nat, 262144); (-408, 8%nat, 481768); (-400, 4%nat, 50); (-352, 8%nat, RB); (-344, 8%nat, 262144); (-336, 8%nat, RB); (-328, 8%nat, RB); (-320, 8%nat, 262144); (-312, 8%nat, 515004); (-304, 8%nat, RB); (-296, 8%nat, CA + 2560); (-288, 8%nat, RI); (-280, 8%nat, 280928); (-272, 8%nat, n); (-264, 8%nat, CA + 80 * c + 16); (-256, 8%nat, FA); (-248, 8%nat, 2305843009213693952); (-240, 8%nat, RI + 8); (-232, 8%nat, 923480); (-224, 8%nat, RI); (-216, 8%nat, 280564)].
Definition gmAc (m : word -> option byte) (SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 : Z) : word -> option byte :=
  wchainS (wbytes (wchainS (ic_mem (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) CA) SP (L2a c CA n g21 g22 g23 g24 g25 g26 g27))
                  (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976))) SP (gL3a c CA n RI RB FA).
Lemma gL3a_small : forall c CA n RI RB FA, 2 <= c <= 16 -> gL3a c CA n RI RB FA = L3a c CA n RI RB FA.
Proof. intros. unfold gL3a, L3a. rewrite gsz_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition BIGSZ_E : expr :=
  EAlu ALU_ADD (EAlu ALU_SLL (ELit 512) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-16))) (ELit 1)))
    (EAlu ALU_AND (EAlu ALU_SRA (EMd M_MUL (ELit (-9223372036854775808)) (EVar 33)) (ELit 63))
       (EAlu ALU_SRL (EAlu ALU_SLL (ELit 512) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-16))) (ELit 1))) (ELit 1))).
Lemma ev33 : forall R V, ev (Ez R V) 33 = wa (nth 1 V 0).
Proof. intros. reflexivity. Qed.
Lemma bigsz_eval : forall R V c, nth 1 V 0 = c -> 17 <= c <= 30 -> bv_unsigned (edenot (Ez R V) BIGSZ_E) = sz_tbl c.
Proof.
  intros R V c Hv Hc. unfold BIGSZ_E. cbn [edenot]. rewrite !ev33, Hv. clear Hv.
  assert (H' : 1 <= c <= 30) by lia. cls30_go c H'; first [lia | vm_compute; reflexivity].
Qed.

Lemma cls_of_rng : forall nd, 1 <= nd <= 65536 -> 1 <= cls_of nd <= 30.
Proof.
  intros nd H. unfold cls_of. destruct (Z.leb nd 512) eqn:E; [apply Z.leb_le in E | apply Z.leb_gt in E].
  - destruct (cls_small nd ltac:(lia)) as [_ Hr]. lia.
  - pose proof (cid_range nd ltac:(lia)). lia.
Qed.

Lemma gnc_le_new : forall c, 1 <= c <= 30 -> mc_tbl c / 2 <= 262144 / sz_tbl c.
Proof. intros c H. cls30_go c H; vm_compute; congruence. Qed.
Lemma gnc_lt_new : forall c, 1 <= c <= 30 -> mc_tbl c / 2 + 1 <= 262144 / sz_tbl c.
Proof. intros c H. cls30_go c H; vm_compute; congruence. Qed.

(* [comment removed for export] *)
Fixpoint tbl_cls_aux (k : nat) (c nd : Z) : Z :=
  match k with O => c | S k' => if Z.leb nd (sz_tbl c) then c else tbl_cls_aux k' (c + 1) nd end.
Definition tbl_cls (nd : Z) : Z := tbl_cls_aux 30 1 nd.
Lemma cls_of_tbl_big : forall nd, 513 <= nd <= 65536 -> cid nd = tbl_cls nd.
Proof.
  intros nd H.
  assert (A : allb (fun x => (65536 <? x) || (cid x =? tbl_cls x)) 513 16 = true) by (vm_compute; reflexivity).
  pose proof (allb_ok _ _ _ A nd ltac:(change (2 ^ Z.of_nat 16) with 65536; lia)) as B. cbv beta in B.
  apply orb_prop in B as [B|B]; [apply Z.ltb_lt in B; lia | apply Z.eqb_eq in B; exact B].
Qed.
Ltac szn H := repeat match type of H with context [sz_tbl ?e] => let v := eval vm_compute in (sz_tbl e) in change (sz_tbl e) with v in H end.
Lemma tbl_cls_spec : forall c nd, 1 <= c <= 30 -> sz_tbl (c - 1) < nd <= sz_tbl c -> tbl_cls nd = c.
Proof.
  intros c nd Hc H. cls30_go c Hc.
  all: repeat match type of H with context [sz_tbl ?e] => let v := eval vm_compute in (sz_tbl e) in change (sz_tbl e) with v in H end.
  all: unfold tbl_cls; cbn [tbl_cls_aux]; repeat match goal with |- context [sz_tbl ?e] => let v := eval vm_compute in (sz_tbl e) in change (sz_tbl e) with v end.
  all: repeat match goal with |- context [Z.leb ?n ?k] => first [ rewrite (proj2 (Z.leb_gt n k)) by lia | rewrite (proj2 (Z.leb_le n k)) by lia ] end; try reflexivity; lia.
Qed.
Lemma cls_of_tbl : forall c nd, 1 <= c <= 30 -> sz_tbl (c - 1) < nd <= sz_tbl c -> cls_of nd = c.
Proof.
  intros c nd Hc H. unfold cls_of. destruct (Z.leb nd 512) eqn:E; [apply Z.leb_le in E | apply Z.leb_gt in E].
  - assert (Hs : c <= 16) by (cls30_go c Hc; szn H; lia).
    rewrite (gsz_small c ltac:(lia)) in H.
    assert (Hp : sz_tbl (c - 1) = 32 * (c - 1)) by (destruct (Z.eq_dec c 1) as [->|N]; [reflexivity | apply gsz_small; lia]).
    rewrite Hp in H. symmetry. apply Z.div_unique with (r := nd + 31 - 32 * c); lia.
  - assert (Hn : nd <= 65536) by (cls30_go c Hc; szn H; lia).
    rewrite (cls_of_tbl_big nd ltac:(lia)). apply tbl_cls_spec; assumption.
Qed.
