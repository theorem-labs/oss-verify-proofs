(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA RA_seql.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp2qs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua AIcpya4 AIcp3q7 AIcpii0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpq85.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpii0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85.AIcpa3z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition FILE_LO : Z := 0xad840.  Definition FILE_HI : Z := 0xae380.
Definition SBUF_LO : Z := 0x608ac0.  Definition SBUF_HI : Z := 0x60a000.

Fixpoint wfok (W : list ivl) : Prop :=
  match W with
  | [] => True
  | (lo, hi) :: W' => (kHighMemBeg_z <= lo \/ (FILE_LO <= lo /\ hi <= FILE_HI) \/ (SBUF_LO <= lo /\ hi <= SBUF_HI)
                      \/ (0x60a000 <= lo /\ hi <= 2147446784) \/ hi <= 0x10000) /\ wfok W'     (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Definition far (a n : Z) : Prop :=
  (0x10000 <= a /\ a + n <= FILE_LO) \/ (FILE_HI <= a /\ a + n <= SBUF_LO) \/ (2147446784 <= a /\ a + n <= kHighMemBeg_z).

Lemma wfok_disjoint : forall W a n, wfok W -> far a n -> 0 <= n -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW Hf Hn; [exact I|]. destruct HW as [H1 H2]. cbn [disjoint_from].
  split; [| apply IH; assumption].
  unfold far, FILE_LO, FILE_HI, SBUF_LO, SBUF_HI, kHighMemBeg_z in *. lia.
Qed.

Lemma wfok_outside : forall W x, wfok W -> far x 1 -> outside W x.
Proof.
  intros W x HW Hf. apply (disjoint_outside W x 1 x); [apply wfok_disjoint; [exact HW| exact Hf| lia]| lia].
Qed.

(* [comment removed for export] *)

Definition fokP (P : (word -> option byte) -> Prop) : Prop :=
  forall W m m', munch W m m' -> wfok W -> P m -> P m'.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma fok_ro_cells : forall a cs, far a (Z.of_nat (cells_size cs)) -> fokP (fun m => ro_cells rsegs m a cs).
Proof.
  intros a cs Ha W m m' MU HW B. eapply ro_cells_transport; [exact B| exact MU| apply wfok_disjoint; [exact HW| exact Ha| lia]].
Qed.

Lemma fok_mapped8 : forall a, 0 <= a -> far a 8 -> fokP (fun m => mapped8 m a).
Proof.
  intros a H0 Ha W m m' MU HW M i Hi.
  rewrite (MU (Z_to_bv 64 (a + i))). { exact (M i Hi). }
  rewrite unsigned_lit by (unfold far, FILE_LO, FILE_HI, SBUF_LO, SBUF_HI, kHighMemBeg_z in Ha; lia).
  apply wfok_outside; [exact HW|]. unfold far, FILE_LO, FILE_HI, SBUF_LO, SBUF_HI, kHighMemBeg_z in *. lia.
Qed.

Lemma fokP_and : forall P Q, fokP P -> fokP Q -> fokP (fun m => P m /\ Q m).
Proof. intros P Q HP HQ W m m' MU HW [H1 H2]. split; [eapply HP| eapply HQ]; eassumption. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fok_shadow_ok : forall a n, 0 <= a -> a + n + 8 <= 2^47 -> fokP (fun m => shadow_ok m a n).
Proof.
  (intros a n H0 Hn W m m' MU HW; (first [ intro dR_1; dex2 dR_1 as ng lastb; dand3 dR_1 as NG SH LB | intro dR_1; dand5 dR_1 as ng lastb NG SH LB | intros (ng & lastb & NG & SH & LB) ])). exists ng, lastb. split; [exact NG|]. split; [|exact LB].
  pose proof (bytes_at_bound _ _ _ _ SH) as BB.
  eapply bytes_at_transport; [exact SH| exact MU| apply wfok_disjoint; [exact HW| | lia]].
  rewrite length_app, zeros_length in *. cbn [length] in *. unfold far, shadow_off, SBUF_HI, kHighMemBeg_z in *. right; right. mlia.
Qed.

Lemma fok_range_ok : forall a n, 0 <= n -> fokP (fun m => range_ok m a n).
Proof.
  (intros a n N0 W m m' MU HW; (first [ intro dR_2; dand4 dR_2 as IR SOK Q1 Q2 | intros (IR & SOK & Q1 & Q2) ])).
  assert (AF : 0 <= a /\ a + n + 8 <= 0x800000000000) by (unfold inmem_range in IR; lia).
  split; [exact IR|]. split; [exact (fok_shadow_ok a n ltac:(lia) ltac:(lia) W m m' MU HW SOK)|].
  split.
  - refine (fok_mapped8 _ _ _ W m m' MU HW Q1); unfold far, sha, shadow_off, SBUF_HI, kHighMemBeg_z; mlia.
  - refine (fok_mapped8 _ _ _ W m m' MU HW Q2); unfold far, sha, shadow_off, SBUF_HI, kHighMemBeg_z; mlia.
Qed.

Ltac far_cells := cbn [cells_size csize Nat.add length]; unfold far, FILE_LO, FILE_HI, SBUF_LO, SBUF_HI, kHighMemBeg_z; lia.

Lemma fok_map_cells : fokP map_cells.
Proof.
  unfold map_cells. repeat (apply fokP_and; [apply fok_ro_cells; far_cells|]). apply fok_ro_cells; far_cells.
Qed.
Lemma fok_asan_memcpy_cells : fokP asan_memcpy_cells.
Proof.
  unfold asan_memcpy_cells. do 3 (apply fokP_and; [apply fok_ro_cells; far_cells|]). apply fok_map_cells.
Qed.
Lemma fok_asan_memset_cells : fokP asan_memset_cells.
Proof.
  unfold asan_memset_cells. do 3 (apply fokP_and; [apply fok_ro_cells; far_cells|]). apply fok_map_cells.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac solve_wfok := try (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv);
  cbn [wfok]; unfold dst_zone, kHighMemBeg_z, FILE_LO, FILE_HI, SBUF_LO, SBUF_HI in *; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; lia.

(* [comment removed for export] *)
Ltac fok_lemma_base P :=
  lazymatch P with
  | map_cells => constr:(fok_map_cells)
  | asan_memcpy_cells => constr:(fok_asan_memcpy_cells)
  | asan_memset_cells => constr:(fok_asan_memset_cells)
  end.
Ltac fok_lemma P := fok_lemma_base P.

Ltac refok_all W m m' MU :=
  let HW := fresh "HW" in
  tryif assert (HW : wfok W) by solve_wfok then
    ((repeat match goal with
      | H : ?P m |- _ =>
          let lem := fok_lemma P in
          let H2 := fresh "SF" in
          pose proof (lem W m m' MU HW H) as H2; clear H; rename H2 into H
      end); clear HW)
  else idtac "note: refok_all: footprint not provably cell-free (wfok); bundles not re-derived".

Ltac refok_store_hook m a bs n Hn Ha Hl :=
  let MUs := fresh "MUs" in
  tryif assert (MUs : munch [(a, (a + n)%Z)] m (write_to_mem m (wa a) bs)) by (exact (munch_store1 m a bs n Hn Ha Hl))
  then (refok_all constr:([(a, (a + n)%Z)]) m constr:(write_to_mem m (wa a) bs) MUs; clear MUs)
  else idtac "note: refok_store_hook: could not state the store's munch".
