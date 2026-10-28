(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG CtSizes CtWire CtModel ApBase ApState ApErr ApParse ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface W_get_objectA W_check_tlenA Fr_asn1_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColP Require ColDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASN1_COLLECT_A : Z := 0x243768.
Definition ASN1_COLLECT_REC_RA : Z := 0x2438a8.     (* [comment removed for export] *)
Definition ASN1_COLLECT_TLEN_RA : Z := 0x243880.    (* [comment removed for export] *)
Definition BUF_GROW_CLEAN_A : Z := 0x24b32c.
Definition CLEAR_REALLOC_A : Z := 0x1fd378.
Definition ASAN_MEMCPY_A : Z := 0x1c29d0.
Definition ASAN_MEMSET_A : Z := 0x1c2e6c.
(* [comment removed for export] *)
Definition A_TASN_DEC_C_A : Z := 0x72b80.
Definition A_ASN1_COLLECT_A : Z := 0x72d80.
Definition A_BUFFER_C_A : Z := 0x73700.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition GROW_STACK_A : Z := 144 + CRYPTO_CLEAR_FREE_STACK.
(* [comment removed for export] *)
Definition COLLECT_FRAME_A : Z := 176.          (* [comment removed for export] *)
Definition COLLECT_STACK_A : Z := COLLECT_FRAME_A + CHECK_TLEN_STACK_A.

Lemma grow_le_tlenA : GROW_STACK_A <= CHECK_TLEN_STACK_A.
Proof.
  unfold GROW_STACK_A, CHECK_TLEN_STACK_A, CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, ACTL_FRAME, GETOBJ_STACK_A, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK, RT_STACK.
  cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma mcost_nonneg_a : forall n, 0 <= n -> 0 <= mcost n.
Proof. intros n Hn. unfold mcost. destruct (n <=? 64512); lia. Qed.
Lemma mcost_mono_a : forall a b, 0 <= a <= b -> 0 <= mcost a <= mcost b.
Proof. intros a b H. unfold mcost. destruct (Z.leb_spec a 64512); destruct (Z.leb_spec b 64512); lia. Qed.

(* [comment removed for export] *)
Lemma grow_cost_bound : forall L cap, 0 <= cap -> cap < L -> L <= 2 ^ 30 -> mcost ((L + 3) / 3 * 4) <= 10 * ((L + 3) / 3 * 4 - cap).
Proof.
  intros L cap H0 HL HM. unfold mcost.
  pose proof (Z.div_mod (L + 3) 3 ltac:(lia)) as E. pose proof (Z.mod_pos_bound (L + 3) 3 ltac:(lia)) as R.
  set (k := (L + 3) / 3) in *. destruct (Z.leb_spec (k * 4) 64512); lia.
Qed.
(* [comment removed for export] *)
Lemma cap_le_bound : forall L N, 0 <= L -> L <= N + 1 -> (L + 3) / 3 * 4 <= (N + 4) / 3 * 4.
Proof. intros L N H0 HL. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation buf_cells := CtColP.ColDefs.buf_cells.
Notation buf_blk := CtColP.ColDefs.buf_blk.
Notation bm_max_some := CtColP.ColDefs.bm_max_some.
Notation bm_max_none := CtColP.ColDefs.bm_max_none.
Notation magic_div3_word := CtColP.ColDefs.magic_div3_word.
Notation grow_size_bounds := CtColP.ColDefs.grow_size_bounds.
Notation le1_lit := CtColP.ColDefs.le1_lit.
Notation mod8_frame := CtColP.ColDefs.mod8_frame.
Notation ret_bits := CtColP.ColDefs.ret_bits.
Notation lb_remove_mid := CtColP.ColDefs.lb_remove_mid.
Notation slice_range := CtColP.ColDefs.slice_range.
Notation zlength_slice := CtColP.ColDefs.zlength_slice.
Notation to_bytes_app := CtColP.ColDefs.to_bytes_app.
Notation zlength_app_c := CtColP.ColDefs.zlength_app_c.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma slice_bytes_a : forall m D0 d p len,
  bytes_at ctasegs m D0 (to_bytes d) -> Forall (fun c => 0 <= c < 256) d -> 0 <= p -> 0 <= len -> p + len <= zlength d ->
  bytes_at ctasegs m (D0 + p) (to_bytes (slice d p len)) /\ Z.of_nat (length (to_bytes (slice d p len))) = len.
Proof.
  intros m D0 d p len HB HF Hp Hl Hpl. unfold slice, to_bytes in *. unfold zlength in Hpl. split.
  - rewrite <- firstn_map, <- skipn_map. replace (D0 + p) with (D0 + Z.of_nat (Z.to_nat p)) by lia.
    apply bytes_at_firstn. apply bytes_at_skipn; [exact HB| rewrite length_map; lia].
  - rewrite length_map, length_firstn, length_skipn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cb_split_a : forall m a (n1 n2 : nat) j,
  rw_cells ctasegs m a [CB (n1 + n2) j] -> rw_cells ctasegs m a [CB n1 (firstn n1 j); CB n2 (skipn n1 j)].
Proof.
  intros m a n1 n2 j H. pose proof H as [[W _] _]. cbn in W. destruct W as [L _].
  eapply rw_cells_recast; [exact H| cbn; rewrite length_firstn, length_skipn; repeat split; lia| | cbn; lia].
  cbn [cells_bytes cbytes app]. rewrite !app_nil_r. apply firstn_skipn.
Qed.

Lemma cb_join_a : forall m a (n1 n2 : nat) j1 j2,
  rw_cells ctasegs m a [CB n1 j1; CB n2 j2] -> rw_cells ctasegs m a [CB (n1 + n2) (j1 ++ j2)].
Proof.
  intros m a n1 n2 j1 j2 H. pose proof H as [[W _] _]. cbn in W. destruct W as (L1 & L2 & _).
  eapply rw_cells_recast; [exact H| cbn; rewrite length_app; repeat split; lia| | cbn; lia].
  cbn [cells_bytes cbytes app]. rewrite !app_nil_r. reflexivity.
Qed.

Lemma cb_byte_a : forall m a j, rw_cells ctasegs m a [CB 1 j] -> exists b, rw_cells ctasegs m a [C1 b].
Proof.
  intros m a j H. pose proof H as [[W _] _]. cbn in W. destruct W as [L _].
  destruct j as [|b [|]]; cbn in L; try lia. exists b.
  eapply rw_cells_recast; [exact H| cbn; auto| reflexivity| reflexivity].
Qed.

Lemma cb_len_a : forall m a n j, rw_cells ctasegs m a [CB n j] -> length j = n.
Proof. intros m a n j [[W _] _]. cbn in W. destruct W as [L _]. exact L. Qed.

(* [comment removed for export] *)
Lemma c8_zero_bytes_a : forall m a, rw_cells ctasegs m a [C8 (wz 0)] -> rw_cells ctasegs m a [C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)].
Proof. intros m a H. eapply rw_cells_recast; [exact H| cbn; auto| reflexivity| reflexivity]. Qed.
Lemma c8_zero_of_bytes_a : forall m a, rw_cells ctasegs m a [C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)] -> rw_cells ctasegs m a [C8 (wz 0)].
Proof. intros m a H. eapply rw_cells_recast; [exact H| cbn; auto| reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma rw_cells_of_bytes_a : forall m A bs, bytes_at ctasegs m A bs -> wr_at ctasegs m A (Z.of_nat (length bs)) -> rw_cells ctasegs m A [CB (length bs) bs].
Proof.
  intros m A bs HB HW. split; [split; [cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]|].
  cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact HW.
Qed.

(* [comment removed for export] *)
Ltac cut_hd H H1 a' :=
  lazymatch type of H with rw_cells _ ?m ?A (?c0 :: ?rest) =>
    change (rw_cells ctasegs m A ([c0] ++ rest)) in H; apply rw_cells_app in H; destruct H as [H1 H];
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H;
    lazymatch type of H with rw_cells _ _ ?A2 _ => replace A2 with a' in H by lia end
  end.
(* [comment removed for export] *)
Ltac join2 H1 H2 :=
  lazymatch type of H1 with rw_cells _ ?m ?A ?cs1 =>
  lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
    replace A2 with (A + Z.of_nat (cells_size cs1))%Z in H2 by (cbn [cells_size csize Nat.add]; lia);
    let J := fresh in
    pose proof (proj2 (rw_cells_app m A cs1 cs2) (conj H1 H2)) as J; clear H1 H2; cbn [app] in J; rename J into H1
  end end.

(* [comment removed for export] *)
Ltac xport H MU WM :=
  first [ eapply rw_cells_transport in H; [| exact MU| exact WM| cbn [cells_size csize Nat.add disjoint_from fst snd]; cbn; lia]
        | eapply ro_cells_transport in H; [| exact MU| cbn [cells_size csize Nat.add disjoint_from fst snd]; cbn; lia] ].

(* [comment removed for export] *)
Ltac stk_join ST FR STF a' :=
  pose proof (Frame.stk_release _ _ _ _ _ ST FR ltac:(lia)) as STF;
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in STF;
  lazymatch type of STF with Frame.stk _ _ _ ?h => replace h with a' in STF by lia end.
