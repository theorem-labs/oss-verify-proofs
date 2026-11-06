(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr Agree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac AllocA0.
Import ListNotations.
Open Scope Z_scope.

Section AP.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Variable AI : am_if FI.
Local Notation K := (am_K FI AI).
Local Notation BL := (list (block K)).

#[using="Type"] Lemma apres_stk : forall (LB : BL) q m m' lo hi,
  apres FI AI LB q m m' -> stk asegs m lo hi -> aclient_range FI AI LB q lo (hi - lo) -> stk asegs m' lo hi.
Proof.
  intros LB q m m' lo hi AP (H1 & H2 & Hs) HR. split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (Hs a Ha) as [Hw [b Hb]]. assert (Hc : aclient FI AI LB q a) by (apply HR; lia).
  split; [exact (proj2 (AP a ltac:(lia) Hc) Hw)|]. exists b. exact (apres_mrd FI AI LB q m m' a b AP ltac:(lia) Hc Hb).
Qed.
#[using="Type"] Lemma apres_u64arr : forall (LB : BL) q m m' A ws,
  apres FI AI LB q m m' -> u64arr asegs m A ws -> aclient_range FI AI LB q A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
Proof.
  intros LB q m m' A ws AP [B W] HR. split.
  - eapply (apres_bytes_at FI AI); [exact AP| exact B|]. rewrite u64s_length, Nat2Z.inj_mul. exact HR.
  - eapply (apres_wr_at FI AI); [exact AP| exact W| exact HR].
Qed.
#[using="Type"] Lemma apres_u32arr : forall (LB : BL) q m m' A ws,
  apres FI AI LB q m m' -> u32arr asegs m A ws -> aclient_range FI AI LB q A (4 * Z.of_nat (length ws)) -> u32arr asegs m' A ws.
Proof.
  intros LB q m m' A ws AP [B W] HR. split.
  - eapply (apres_bytes_at FI AI); [exact AP| exact B|]. rewrite u32s_length, Nat2Z.inj_mul. exact HR.
  - eapply (apres_wr_at FI AI); [exact AP| exact W| exact HR].
Qed.

#[using="Type"] Lemma aclient_range_block_shadow : forall (LB : BL) q A n b, In b LB ->
  sh (blk_addr b) <= A -> A + n <= sh (blk_addr b) + Z.of_nat (length (block_shadow (blk_size b))) -> aclient_range FI AI LB q A n.
Proof. intros LB q A n b HIN H1 H2 a Ha. do 5 right. exists b. split; [exact HIN|]. lia. Qed.

#[using="Type"] Lemma lb_remove_In : forall (k : K) (LB : BL) b, In b LB -> blk_id b <> k -> In b (lb_remove (am_K_eqb FI AI) k LB).
Proof.
  induction LB as [|b0 LB IH]; intros b HIN NE; [destruct HIN|].
  unfold lb_remove in *. rewrite list.filter_cons. destruct (decide _) as [D|D].
  - destruct HIN as [->|HIN]; [left; reflexivity| right; apply IH; assumption].
  - destruct HIN as [->|HIN]; [| apply IH; assumption].
    exfalso. apply D. apply Is_true_true_2. apply negb_true_iff.
    destruct (am_K_eqb FI AI (blk_id b) k) eqn:E; [| reflexivity].
    apply (am_K_eqb_eq FI AI) in E. contradiction.
Qed.

#[using="Type"] Lemma aclient_range_weaken : forall (LB LB' : BL) q q' A n,
  aclient_range FI AI LB q A n -> (forall b, In b LB -> In b LB') -> q' <= q -> aclient_range FI AI LB' q' A n.
Proof.
  intros LB LB' q q' A n HR SUB HQ a Ha. specialize (HR a Ha). unfold aclient, in_block in *.
  destruct HR as [H|[H|[H|[H|[H|H]]]]].
  - left. lia.
  - right; left. exact H.
  - right; right; left. destruct H as (b & HIN & Hb). exists b. split; [apply SUB; exact HIN| exact Hb].
  - right; right; right; left. exact H.
  - right; right; right; right; left. exact H.
  - do 5 right. destruct H as (b & HIN & Hb). exists b. split; [apply SUB; exact HIN| exact Hb].
Qed.
End AP.

Ltac in_bt :=
  lazymatch goal with
  | |- In _ (lb_remove _ _ _) => eapply lb_remove_In; [ in_bt | first [ assumption | congruence | (intros ?X; inversion X; fail) ] ]
  | |- In _ (_ :: _) => (left; reflexivity) + (right; in_bt)
  | |- In _ _ => eassumption
  end.

Ltac ap_sizes :=
  cbn [blk_addr blk_size blk_id fst snd];
  rewrite ?length_app;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_app, ?length_map, ?repeat_length, ?cells_size_shadow; cbn [length].

Ltac aclient_extra := fail.

Ltac aclient_band AMS l h :=
  eapply (aclient_range_static _ _ _ _ _ _ l h); [ apply AMS; unfold a0_static; lia | ap_sizes; lia | ap_sizes; lia ].

Ltac aclient_solve :=
  lazymatch goal with
  | |- aclient_range _ _ _ _ _ _ =>
      first
        [ apply aclient_range_above; ap_sizes; lia
        | aclient_extra
        | match goal with
          | AMS : (forall lo hi : Z, a0_static lo hi -> am_static _ _ lo hi) |- _ =>
              first [ aclient_band AMS 0x10000 0xaca48 | aclient_band AMS 0xaf320 0xafa20
                    | aclient_band AMS 0x5d6b80 0x5e6bc0 | aclient_band AMS 0x5e6c00 0x5e6ca0
                    | aclient_band AMS 0x5e7508 0x5e7510 | aclient_band AMS 0x6075f0 0x6075f8
                    | aclient_band AMS 0x607600 0x607820 | aclient_band AMS 0x1463e0 0x1463e1 | aclient_band AMS 0x607820 0x607824
                    | aclient_band AMS 0x607840 0x607848 | aclient_band AMS 0x607c00 0x6080c0
                    | aclient_band AMS 0x7fffa000 0x800b9200
                    | eapply (aclient_range_static _ _ _ _ _ _ (sh alloc_ceiling - sh alloc_ceiling mod 8) 0x10007fff8000); [ apply AMS; apply a0_static_s6 | ap_sizes; lia | ap_sizes; lia ] ]
          end
        | solve [ eapply aclient_range_block; [ in_bt | ap_sizes; lia | ap_sizes; lia ] ]
        | solve [ eapply aclient_range_block_shadow; [ in_bt | ap_sizes; lia | ap_sizes; lia ] ]
        | eapply aclient_range_fs; ap_sizes; lia
        | eapply aclient_range_fs_shadow; ap_sizes; lia ]
  end.

Ltac apres_extra AP m := fail.

Ltac apres_transport AP :=
  lazymatch type of AP with
  | apres ?FI ?AI ?LB ?q ?m ?m' =>
      repeat match goal with
      | H : rw_cells asegs m ?A ?cs |- _ =>
          first [ apply (apres_rw_cells FI AI LB q m m' A cs AP) in H; [ | aclient_solve ]
                | idtac "note: apres_transport drops (not a client range of the call):" H; clear H ]
      | H : bytes_at asegs m ?A ?bs |- _ =>
          first [ apply (apres_bytes_at FI AI LB q m m' A bs AP) in H; [ | aclient_solve ]
                | idtac "note: apres_transport drops (not a client range of the call):" H; clear H ]
      | H : wr_at asegs m ?A ?n |- _ =>
          first [ apply (apres_wr_at FI AI LB q m m' A n AP) in H; [ | aclient_solve ]
                | idtac "note: apres_transport drops (not a client range of the call):" H; clear H ]
      | H : u64arr asegs m ?A ?ws |- _ =>
          first [ apply (apres_u64arr FI AI LB q m m' A ws AP) in H; [ | aclient_solve ]
                | idtac "note: apres_transport drops (not a client range of the call):" H; clear H ]
      | H : u32arr asegs m ?A ?ws |- _ =>
          first [ apply (apres_u32arr FI AI LB q m m' A ws AP) in H; [ | aclient_solve ]
                | idtac "note: apres_transport drops (not a client range of the call):" H; clear H ]
      | H : stk asegs m ?lo ?hi |- _ =>
          first [ apply (apres_stk FI AI LB q m m' lo hi AP) in H; [ | aclient_solve ]
                | clear H ]
      | _ => apres_extra AP m
      end
  | _ => fail "apres_transport: not an apres hypothesis"
  end.

Section TEST.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Variable AI : am_if FI.
Hypothesis AMS : forall lo hi : Z, a0_static lo hi -> am_static FI AI lo hi.

Goal forall (LB : list (block (am_K FI AI))) (k k2 : am_K FI AI) (B n q lo : Z) (m m' : mem) (v e : word) (bs junk : list byte) (ws : list word),
  k2 <> k ->
  apres FI AI (lb_remove (am_K_eqb FI AI) k ((k, 77, 5) :: (k2, B, n) :: LB)) q m m' ->
  rw_cells asegs m (q + 16) [C8 v; C8 v] ->
  rw_cells asegs m 0x5e750c [C4 e] ->
  rw_cells asegs m B [CB (Z.to_nat n) bs] -> 0 <= n ->
  u64arr asegs m (q + 64) ws ->
  rw_cells asegs m (q - 64) [CB 8 junk] ->
  stk asegs m (q + 128) (q + 256) ->
  rw_cells asegs m' (q + 16) [C8 v; C8 v] /\ rw_cells asegs m' 0x5e750c [C4 e] /\ rw_cells asegs m' B [CB (Z.to_nat n) bs]
  /\ u64arr asegs m' (q + 64) ws /\ stk asegs m' (q + 128) (q + 256).
Proof.
  intros LB k k2 B n q lo m m' v e bs junk ws NE AP H1 H2 H3 Hn H4 H5 H6.
  apres_transport AP.
  repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.
End TEST.
