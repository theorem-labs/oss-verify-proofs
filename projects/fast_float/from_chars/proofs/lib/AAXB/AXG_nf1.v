(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_np3.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Definition mc_tbl (c : Z) : Z := match c with 1 => 16 | 2 => 16 | 3 => 16 | 4 => 16 | 5 => 12 | 6 => 10 | 7 => 8 | 8 => 8 | 9 => 6 | 10 => 6 | 11 => 4 | 12 => 4 | 13 => 4 | 14 => 4 | 15 => 4 | 16 => 4 | 17 => 2 | 18 => 2 | 19 => 2 | 20 => 2 | 21 => 2 | 22 => 2 | 23 => 2 | 24 => 2 | 25 => 2 | 26 => 2 | 27 => 2 | 28 => 2 | 29 => 2 | 30 => 2 | 31 => 16 | _ => 0 end.
Definition sz_tbl (c : Z) : Z := match c with 1 => 32 | 2 => 64 | 3 => 96 | 4 => 128 | 5 => 160 | 6 => 192 | 7 => 224 | 8 => 256 | 9 => 288 | 10 => 320 | 11 => 352 | 12 => 384 | 13 => 416 | 14 => 448 | 15 => 480 | 16 => 512 | 17 => 768 | 18 => 1024 | 19 => 1536 | 20 => 2048 | 21 => 3072 | 22 => 4096 | 23 => 6144 | 24 => 8192 | 25 => 12288 | 26 => 16384 | 27 => 24576 | 28 => 32768 | 29 => 49152 | 30 => 65536 | 31 => 64 | _ => 0 end.

(* [comment removed for export] *)
Fixpoint wchainR (m : word -> option byte) (B : Z) (L : list (Z * nat * Z)) : word -> option byte :=
  match L with
  | [] => m
  | (k, w, v) :: L' => wbytes (wchainR m B L') (wa (B + k)) (word_to_le_bytes w (wa v))
  end.
Definition wl_ok (L : list (Z * nat * Z)) : bool :=
  forallb (fun '(k, w, v) => (Z.leb 0 k && Z.leb (k + Z.of_nat w) 4096 && Nat.leb 1 w && Nat.leb w 8)%bool) L.
(* [comment removed for export] *)
Fixpoint wl_rd (L : list (Z * nat * Z)) (k : Z) (w : nat) (v : Z) : bool :=
  match L with
  | [] => false
  | (k', w', v') :: L' => if (Z.eqb k' k && Nat.eqb w' w && Z.eqb v' v)%bool then true
                          else if (Z.leb (k' + Z.of_nat w') k || Z.leb (k + Z.of_nat w) k')%bool then wl_rd L' k w v else false
  end.
Lemma rd_wchainR : forall L m B k w v, 0 <= B -> B + 4096 <= 2^64 -> wl_ok L = true -> 0 <= k -> k + Z.of_nat w <= 4096 -> (1 <= w <= 8)%nat ->
  wl_rd L k w v = true -> rd (wchainR m B L) (B + k) w v.
Proof.
  induction L as [|[[k' w'] v'] L IH]; intros m B k w v HB1 HB2 Hwf Hk1 Hk2 Hw H; cbn [wl_rd] in H; [discriminate|].
  cbn [wl_ok forallb] in Hwf. apply andb_prop in Hwf as [Hw1 Hwf].
  repeat match type of Hw1 with (_ && _)%bool = true => apply andb_prop in Hw1 as [Hw1 ?] end.
  repeat match goal with X : Z.leb _ _ = true |- _ => apply Z.leb_le in X | X : Nat.leb _ _ = true |- _ => apply Nat.leb_le in X end.
  cbn [wchainR].
  destruct (Z.eqb k' k && Nat.eqb w' w && Z.eqb v' v)%bool eqn:E.
  - apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1, E3. apply Nat.eqb_eq in E2. subst.
    apply wb_rd_hit; lia.
  - destruct (Z.leb (k' + Z.of_nat w') k || Z.leb (k + Z.of_nat w) k')%bool eqn:D; [|discriminate].
    apply orb_prop in D as [D|D]; apply Z.leb_le in D.
    all: apply wb_rd_other; [lia | lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia | apply IH; assumption].
Qed.
Lemma wchainR_frame : forall L m B x, 0 <= B -> B + 4096 <= 2^64 -> wl_ok L = true -> 0 <= x < 2^64 -> ~ (B <= x < B + 4096) ->
  wchainR m B L (wa x) = m (wa x).
Proof.
  induction L as [|[[k' w'] v'] L IH]; intros m B x HB1 HB2 Hwf Hx H; [reflexivity|].
  cbn [wl_ok forallb] in Hwf. apply andb_prop in Hwf as [Hw1 Hwf].
  repeat match type of Hw1 with (_ && _)%bool = true => apply andb_prop in Hw1 as [Hw1 ?] end.
  repeat match goal with X : Z.leb _ _ = true |- _ => apply Z.leb_le in X | X : Nat.leb _ _ = true |- _ => apply Nat.leb_le in X end.
  cbn [wchainR]. rewrite wb_other; [apply IH; assumption | exact Hx | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
Qed.
Lemma wchainR_grows : forall L m B, mem_grows m (wchainR m B L).
Proof. induction L as [|[[k w] v] L IH]; intros m B; [apply mem_grows_refl | cbn [wchainR]; apply grows_wb; apply IH]. Qed.

(* [comment removed for export] *)
Definition ic_list : list (Z * nat * Z) := [(2488, 8%nat, 64); (2484, 4%nat, 16); (2408, 8%nat, 65536); (2404, 4%nat, 2); (2328, 8%nat, 49152); (2324, 4%nat, 2); (2248, 8%nat, 32768); (2244, 4%nat, 2); (2168, 8%nat, 24576); (2164, 4%nat, 2); (2088, 8%nat, 16384); (2084, 4%nat, 2); (2008, 8%nat, 12288); (2004, 4%nat, 2); (1928, 8%nat, 8192); (1924, 4%nat, 2); (1848, 8%nat, 6144); (1844, 4%nat, 2); (1768, 8%nat, 4096); (1764, 4%nat, 2); (1688, 8%nat, 3072); (1684, 4%nat, 2); (1608, 8%nat, 2048); (1604, 4%nat, 2); (1528, 8%nat, 1536); (1524, 4%nat, 2); (1448, 8%nat, 1024); (1444, 4%nat, 2); (1368, 8%nat, 768); (1364, 4%nat, 2); (1288, 8%nat, 512); (1284, 4%nat, 4); (1208, 8%nat, 480); (1204, 4%nat, 4); (1128, 8%nat, 448); (1124, 4%nat, 4); (1048, 8%nat, 416); (1044, 4%nat, 4); (968, 8%nat, 384); (964, 4%nat, 4); (888, 8%nat, 352); (884, 4%nat, 4); (808, 8%nat, 320); (804, 4%nat, 6); (728, 8%nat, 288); (724, 4%nat, 6); (648, 8%nat, 256); (644, 4%nat, 8); (568, 8%nat, 224); (564, 4%nat, 8); (488, 8%nat, 192); (484, 4%nat, 10); (408, 8%nat, 160); (404, 4%nat, 12); (328, 8%nat, 128); (324, 4%nat, 16); (248, 8%nat, 96); (244, 4%nat, 16); (168, 8%nat, 64); (164, 4%nat, 16); (88, 8%nat, 32); (84, 4%nat, 16)].
Definition ic_mem (m : word -> option byte) (CA : Z) : word -> option byte := wchainR m CA ic_list.

Lemma ic_grows : forall m CA, mem_grows m (ic_mem m CA).
Proof. intros. apply wchainR_grows. Qed.
Lemma ic_frame : forall m CA x, 0 <= CA -> CA + 4096 <= 2^64 -> 0 <= x < 2^64 -> ~ (CA <= x < CA + 4096) -> ic_mem m CA (wa x) = m (wa x).
Proof. intros. apply wchainR_frame; [assumption | assumption | vm_compute; reflexivity | assumption | assumption]. Qed.

Lemma ic_rd : forall m CA c, 0 <= CA -> CA + 4096 <= 2^64 -> 1 <= c <= 31 ->
  rd (ic_mem m CA) (CA + 80 * c + 4) 4 (mc_tbl c) /\ rd (ic_mem m CA) (CA + 80 * c + 8) 8 (sz_tbl c).
Proof.
  intros m CA c H1 H2 Hc. unfold ic_mem.
  replace (CA + 80 * c + 4) with (CA + (80 * c + 4)) by ring. replace (CA + 80 * c + 8) with (CA + (80 * c + 8)) by ring.
  assert (Hcs : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16 \/
                c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30 \/ c = 31) by lia.
  assert (Hwf : wl_ok ic_list = true) by (vm_compute; reflexivity).
  repeat (destruct Hcs as [Hcs|Hcs]; [subst c; split; (apply rd_wchainR; [lia | lia | exact Hwf | lia | cbn; lia | lia | vm_compute; reflexivity])|]).
  subst c. split; (apply rd_wchainR; [lia | lia | exact Hwf | lia | cbn; lia | lia | vm_compute; reflexivity]).
Qed.

(* [comment removed for export] *)
Fixpoint wchainS (m : word -> option byte) (S : Z) (L : list (Z * nat * Z)) : word -> option byte :=
  match L with
  | [] => m
  | (k, w, v) :: L' => wbytes (wchainS m S L') (wa (S + k)) (word_to_le_bytes w (wa v))
  end.
Definition wsl_ok (L : list (Z * nat * Z)) : bool :=
  forallb (fun '(k, w, v) => (Z.leb (-8192) k && Z.leb (k + Z.of_nat w) 8192 && Nat.leb 1 w && Nat.leb w 8)%bool) L.
Fixpoint wl_chk (L : list (Z * nat * Z)) (k : Z) (w : nat) : option Z :=
  match L with
  | [] => None
  | (k', w', v') :: L' => if (Z.eqb k' k && Nat.eqb w' w)%bool then Some v'
                          else if (Z.leb (k' + Z.of_nat w') k || Z.leb (k + Z.of_nat w) k')%bool then wl_chk L' k w else None
  end.
Lemma rd_wchainS : forall L m S k w v, 8192 <= S -> S + 8192 <= 2^64 -> wsl_ok L = true -> -8192 <= k -> k + Z.of_nat w <= 8192 -> (1 <= w <= 8)%nat ->
  wl_chk L k w = Some v -> rd (wchainS m S L) (S + k) w v.
Proof.
  induction L as [|[[k' w'] v'] L IH]; intros m S k w v HB1 HB2 Hwf Hk1 Hk2 Hw H; cbn [wl_chk] in H; [discriminate|].
  cbn [wsl_ok forallb] in Hwf. apply andb_prop in Hwf as [Hw1 Hwf].
  repeat match type of Hw1 with (_ && _)%bool = true => apply andb_prop in Hw1 as [Hw1 ?] end.
  repeat match goal with X : Z.leb _ _ = true |- _ => apply Z.leb_le in X | X : Nat.leb _ _ = true |- _ => apply Nat.leb_le in X end.
  cbn [wchainS].
  destruct (Z.eqb k' k && Nat.eqb w' w)%bool eqn:E.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Nat.eqb_eq in E2. subst.
    apply wb_rd_hit; lia.
  - destruct (Z.leb (k' + Z.of_nat w') k || Z.leb (k + Z.of_nat w) k')%bool eqn:D; [|discriminate].
    apply orb_prop in D as [D|D]; apply Z.leb_le in D.
    all: apply wb_rd_other; [lia | lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia | apply IH; assumption].
Qed.
Lemma wchainS_frame : forall L m S x, 8192 <= S -> S + 8192 <= 2^64 -> wsl_ok L = true -> 0 <= x < 2^64 -> ~ (S - 8192 <= x < S + 8192) ->
  wchainS m S L (wa x) = m (wa x).
Proof.
  induction L as [|[[k' w'] v'] L IH]; intros m S x HB1 HB2 Hwf Hx H; [reflexivity|].
  cbn [wsl_ok forallb] in Hwf. apply andb_prop in Hwf as [Hw1 Hwf].
  repeat match type of Hw1 with (_ && _)%bool = true => apply andb_prop in Hw1 as [Hw1 ?] end.
  repeat match goal with X : Z.leb _ _ = true |- _ => apply Z.leb_le in X | X : Nat.leb _ _ = true |- _ => apply Nat.leb_le in X end.
  cbn [wchainS]. rewrite wb_other; [apply IH; assumption | exact Hx | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
Qed.
(* [comment removed for export] *)
Definition wsl_in (L : list (Z * nat * Z)) (lo hi : Z) : bool :=
  forallb (fun '(k, w, v) => (Z.leb lo k && Z.leb (k + Z.of_nat w) hi)%bool) L.
Lemma wchainS_frame_in : forall L m S lo hi x, 0 <= S + lo -> S + hi <= 2^64 -> wsl_in L lo hi = true -> wsl_ok L = true -> 0 <= x < 2^64 ->
  ~ (S + lo <= x < S + hi) -> wchainS m S L (wa x) = m (wa x).
Proof.
  induction L as [|[[k' w'] v'] L IH]; intros m S lo hi x HB1 HB2 Hin Hwf Hx H; [reflexivity|].
  cbn [wsl_ok wsl_in forallb] in Hwf, Hin. apply andb_prop in Hwf as [Hw1 Hwf]. apply andb_prop in Hin as [Hi1 Hin].
  repeat match type of Hw1 with (_ && _)%bool = true => apply andb_prop in Hw1 as [Hw1 ?] end.
  repeat match type of Hi1 with (_ && _)%bool = true => apply andb_prop in Hi1 as [Hi1 ?] end.
  repeat match goal with X : Z.leb _ _ = true |- _ => apply Z.leb_le in X | X : Nat.leb _ _ = true |- _ => apply Nat.leb_le in X end.
  cbn [wchainS]. rewrite wb_other; [apply (IH m S lo hi); assumption | exact Hx | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
Qed.
Lemma wchainS_grows : forall L m S, mem_grows m (wchainS m S L).
Proof. induction L as [|[[k w] v] L IH]; intros m S; [apply mem_grows_refl | cbn [wchainS]; apply grows_wb; apply IH]. Qed.
Lemma wchainS_app : forall L1 L2 m S, wchainS m S (L1 ++ L2) = wchainS (wchainS m S L2) S L1.
Proof. induction L1 as [|[[k w] v] L1 IH]; intros L2 m S; [reflexivity | cbn [app wchainS]; rewrite IH; reflexivity]. Qed.

(* [comment removed for export] *)
Lemma new_rng : forall c, 2 <= c <= 16 -> 512 <= 262144 / (32 * c) <= 4096 /\ 262144 / (32 * c) * (32 * c) <= 262144.
Proof.
  intros c Hc. split; [split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound] | rewrite Z.mul_comm; apply Z.mul_div_le]; lia.
Qed.
(* [comment removed for export] *)
