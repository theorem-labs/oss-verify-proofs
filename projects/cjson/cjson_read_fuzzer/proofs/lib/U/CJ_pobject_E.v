(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Permutation.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_facts3.
Module CJ_pvalue_lemmas.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_split_app : forall m A cs1 cs2,
  rw_cells usegs m A (cs1 ++ cs2) <-> rw_cells usegs m A cs1 /\ rw_cells usegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)). rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)). rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_recell : forall m A cs cs',
  rw_cells usegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells usegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf HB] HW] Hwf' HE. split; [split; [exact Hwf'| rewrite HE; exact HB]|].
  rewrite <- (cells_bytes_length cs' Hwf'), HE, (cells_bytes_length cs Hwf). exact HW.
Qed.

(* [comment removed for export] *)
Lemma zero_node_cells : forall m A,
  rw_cells usegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells usegs m A (node_cells 0 (wz 0) 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0).
Proof. intros m A H. eapply rw_cells_recell; [exact H| cbn; repeat split; exact I| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma zero_node_cells_prev : forall m A pv,
  rw_cells usegs m A [C8 (Z_to_bv 64 0); C8 pv; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells usegs m A (node_cells 0 pv 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0).
Proof. intros m A pv H. eapply rw_cells_recell; [exact H| cbn; repeat split; exact I| reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition NUM_MASK : Z := 288230376218820613.

Lemma num_mask_numch : forall s, 0 <= s <= 58 -> Z.land (Z.shiftr NUM_MASK s) 1 <> 0 -> is_numch (s + 43) = true.
Proof.
  intros s Hs H. rewrite <- (Z2Nat.id s) in H |- * by lia. remember (Z.to_nat s) as k eqn:Ek.
  assert (Hk : (k <= 58)%nat) by lia. clear Ek Hs s.
  do 59 (destruct k as [|k]; [first [vm_compute; reflexivity | exfalso; apply H; vm_compute; reflexivity] |]). lia.
Qed.

Lemma digit_numch : forall c, 48 <= c <= 57 -> is_numch c = true.
Proof. intros c Hc. unfold is_numch. replace (48 <=? c) with true by (symmetry; apply Z.leb_le; lia). replace (c <=? 57) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

Lemma dot_numch : is_numch 46 = true.
Proof. reflexivity. Qed.

Lemma numch_not_x : forall c, is_numch c = true -> c <> 120 /\ c <> 88.
Proof. intros c H. unfold is_numch in H. split; intros ->; discriminate. Qed.

Lemma numch_range : forall c, is_numch c = true -> 0 <= c < 256.
Proof.
  intros c H. unfold is_numch in H.
  repeat match type of H with
  | (?a || ?b) = true => apply Bool.orb_true_iff in H; destruct H as [H|H]
  end.
  - apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
  - apply Z.eqb_eq in H. lia.
  - apply Z.eqb_eq in H. lia.
  - apply Z.eqb_eq in H. lia.
  - apply Z.eqb_eq in H. lia.
  - apply Z.eqb_eq in H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Chains.
  Variable HI : cj_heap_iface.

  (* [comment removed for export] *)
  Lemma cj_chain_set_prev : forall SPB LBX m0 mo R T m m' d p B pv',
    LHEAP HI SPB LBX m0 mo -> Permutation (B ++ R) LBX ->
    cj_chain T m d p B -> p <> 0 ->
    munch [(p + 8, p + 16)] m m' -> wmono usegs m m' ->
    (forall nx pv ch ty p1 vs vi p2 vd ky, rw_cells usegs m p (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
                                          rw_cells usegs m' p (node_cells nx pv' ch ty p1 vs vi p2 vd ky)) ->
    cj_chain T m' d p B.
  Proof.
    intros SPB LBX m0 mo R T m m' d p B pv' HL HP CH NZ MU WM HND.
    destruct (cj_chain_cons_inv _ _ _ _ _ CH NZ)
      as (d0 & nx & pv & ch & ty & p1 & vs & vi & p2 & vd & ky & Bv & Bk & Bc & Bn & -> & ND & TY & HT & SV & SK & CHC & CHN & ->).
    assert (DJ : forall A n, In (A, n) (Bv ++ Bk ++ Bc ++ Bn) -> disjoint_from [(p + 8, p + 16)] A n).
    { intros A n Hin. cbn. split; [|exact I].
      assert (HP' : Permutation ((p, 64) :: (Bv ++ Bk ++ Bc ++ Bn) ++ R) LBX) by exact HP.
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP' A n ltac:(apply in_or_app; left; exact Hin)) as [_ D]. lia. }
    eapply cj_chain_cons; [exact NZ| exact (HND _ _ _ _ _ _ _ _ _ _ ND)| exact TY| exact HT| | | |].
    - eapply cj_str_frame; [exact SV| exact MU| exact WM|]. intros A n Hin. apply DJ. apply in_or_app; left; exact Hin.
    - eapply cj_str_frame; [exact SK| exact MU| exact WM|]. intros A n Hin. apply DJ. apply in_or_app; right; apply in_or_app; left; exact Hin.
    - eapply cj_chain_frame; [exact CHC| exact MU| exact WM|]. intros A n Hin. apply DJ. do 2 (apply in_or_app; right). apply in_or_app; left; exact Hin.
    - eapply cj_chain_frame; [exact CHN| exact MU| exact WM|]. intros A n Hin. apply DJ. do 3 (apply in_or_app; right). exact Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma cj_chain_relink : forall SPB LBX m0 mo R T m m' d p nx pv' ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn,
    LHEAP HI SPB LBX m0 mo -> Permutation (((p, 64) :: Bv ++ Bk ++ Bc ++ Bn) ++ R) LBX ->
    p <> 0 -> 0 <= ty < 256 -> T ty ->
    cj_str m vs Bv -> cj_str m ky Bk -> cj_chain T m d ch Bc -> cj_chain T m (S d) nx Bn ->
    munch [(p + 8, p + 16)] m m' -> wmono usegs m m' ->
    rw_cells usegs m' p (node_cells nx pv' ch ty p1 vs vi p2 vd ky) ->
    cj_chain T m' (S d) p ((p, 64) :: Bv ++ Bk ++ Bc ++ Bn).
  Proof.
    intros until Bn. intros HL HP NZ TY HT SV SK CHC CHN MU WM ND.
    assert (DJ : forall A n, In (A, n) (Bv ++ Bk ++ Bc ++ Bn) -> disjoint_from [(p + 8, p + 16)] A n).
    { intros A n Hin. cbn. split; [|exact I].
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A n ltac:(apply in_or_app; left; exact Hin)) as [_ D]. lia. }
    eapply cj_chain_cons; [exact NZ| exact ND| exact TY| exact HT| | | |].
    - eapply cj_str_frame; [exact SV| exact MU| exact WM|]. intros A n Hin. apply DJ. apply in_or_app; left; exact Hin.
    - eapply cj_str_frame; [exact SK| exact MU| exact WM|]. intros A n Hin. apply DJ. apply in_or_app; right; apply in_or_app; left; exact Hin.
    - eapply cj_chain_frame; [exact CHC| exact MU| exact WM|]. intros A n Hin. apply DJ. do 2 (apply in_or_app; right). apply in_or_app; left; exact Hin.
    - eapply cj_chain_frame; [exact CHN| exact MU| exact WM|]. intros A n Hin. apply DJ. do 3 (apply in_or_app; right). exact Hin.
  Qed.
End Chains.

(* [comment removed for export] *)
Lemma cj_lseg_snoc0 : forall T m d p q B nx pv ch ty p1 vs vi p2 vd Bv Bc,
  cj_lseg T m d p q B -> q <> 0 ->
  rw_cells usegs m q (node_cells nx pv ch ty p1 vs vi p2 vd 0) ->
  0 <= ty < 256 -> T ty -> cj_str m vs Bv -> cj_chain T m d ch Bc ->
  cj_lseg T m d p nx (B ++ (q, 64) :: Bv ++ Bc).
Proof.
  intros. replace (Bv ++ Bc) with (Bv ++ [] ++ Bc) by reflexivity.
  eapply cj_lseg_snoc; eauto. apply cj_str_null.
Qed.

Lemma CJ_PRINTABLE_range : forall ty, CJ_PRINTABLE ty -> 0 <= ty < 256.
Proof. intros ty H. unfold CJ_PRINTABLE in H. cbn in H. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Fagree_set : forall F F' (k : bv 5) v,
  Fagree F F' -> (bv_unsigned k = 10 \/ bv_unsigned k = 14 \/ bv_unsigned k = 15) -> Fagree F (bvmap_set k v F').
Proof.
  intros F F' k v HA Hk r H10 H14 H15. rewrite freg_get_other; [apply HA; assumption|].
  unfold bv_eqb. apply Z.eqb_neq. lia.
Qed.

Lemma Fagree_of_strtod : forall F F',
  (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k) ->
  Fagree F F'.
Proof. intros F F' H k A B C. apply H; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition LIT_NULL : Z := 0x102e0.
Definition LIT_FALSE : Z := 0x10298.
Definition LIT_TRUE : Z := 0x10321.
Definition lit_null : list byte := map wb [110; 117; 108; 108].
Definition lit_false : list byte := map wb [102; 97; 108; 115; 101].
Definition lit_true : list byte := map wb [116; 114; 117; 101].

Lemma lit_null_at : forall m, mem_inv usegs m -> bytes_at usegs m LIT_NULL lit_null.
Proof. intros m MI. apply (ro_bytes_at usegs m LIT_NULL lit_null MI); [unfold LIT_NULL; lia| cbn; unfold LIT_NULL; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma lit_false_at : forall m, mem_inv usegs m -> bytes_at usegs m LIT_FALSE lit_false.
Proof. intros m MI. apply (ro_bytes_at usegs m LIT_FALSE lit_false MI); [unfold LIT_FALSE; lia| cbn; unfold LIT_FALSE; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma lit_true_at : forall m, mem_inv usegs m -> bytes_at usegs m LIT_TRUE lit_true.
Proof. intros m MI. apply (ro_bytes_at usegs m LIT_TRUE lit_true MI); [unfold LIT_TRUE; lia| cbn; unfold LIT_TRUE; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

Lemma strncmp_walk_total : forall k l r, (k < length l)%nat -> (k < length r)%nat -> exists v, strncmp_walk l r k = Some v.
Proof.
  induction k as [|k IH]; intros [|a l] [|b r] Hl Hr; cbn in *; try lia.
  - destruct (_ : bool); eexists; reflexivity.
  - destruct (_ : bool); [eexists; reflexivity|]. apply IH; lia.
Qed.

Lemma strncmp_model_total : forall l r n, 0 < n -> (Z.to_nat n <= length l)%nat -> (Z.to_nat n <= length r)%nat ->
  exists v, strncmp_model l r n = Some v.
Proof.
  intros l r n Hn Hl Hr. unfold strncmp_model. destruct (Z.eqb_spec n 0); [eexists; reflexivity|]. apply strncmp_walk_total; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma perm_pick_head : forall (u h : cblock) (R LR : list cblock),
  Permutation (h :: R ++ u :: LR) (u :: (h :: R) ++ LR).
Proof.
  intros. change (Permutation ((h :: R) ++ u :: LR) (u :: (h :: R) ++ LR)). apply Permutation_sym. apply (Permutation_middle (h :: R) LR u).
Qed.

Lemma perm_pick_mid : forall (u c : cblock) (B1 T LR : list cblock),
  Permutation (c :: (B1 ++ T) ++ u :: LR) (u :: (B1 ++ c :: T) ++ LR).
Proof.
  intros. transitivity (u :: c :: (B1 ++ T) ++ LR).
  - change (Permutation ((c :: B1 ++ T) ++ u :: LR) (u :: (c :: B1 ++ T) ++ LR)). apply Permutation_sym. apply (Permutation_middle (c :: B1 ++ T) LR u).
  - apply perm_skip. rewrite <- !app_assoc. change (Permutation (c :: B1 ++ (T ++ LR)) (B1 ++ c :: (T ++ LR))). apply (Permutation_middle B1 (T ++ LR) c).
Qed.

(* [comment removed for export] *)
Lemma perm_new_done : forall (u a : cblock) (T X LR : list cblock),
  Permutation (a :: T ++ u :: X ++ LR) (u :: (X ++ a :: T) ++ LR).
Proof.
  intros. transitivity (u :: a :: T ++ X ++ LR).
  - change (Permutation ((a :: T) ++ u :: X ++ LR) (u :: (a :: T) ++ X ++ LR)). apply Permutation_sym. apply (Permutation_middle (a :: T) (X ++ LR) u).
  - apply perm_skip. rewrite <- app_assoc. cbn [app].
    transitivity (a :: (X ++ T ++ LR)).
    + apply perm_skip. rewrite (app_assoc T X LR), (app_assoc X T LR). apply Permutation_app_tail. apply Permutation_app_comm.
    + apply (Permutation_middle X (T ++ LR) a).
Qed.

(* [comment removed for export] *)
Lemma perm_new_done_k : forall (u a sk : cblock) (Bv Bc X LR : list cblock),
  Permutation (a :: (Bv ++ Bc) ++ sk :: u :: X ++ LR) (u :: (X ++ a :: Bv ++ [sk] ++ Bc) ++ LR).
Proof.
  intros. transitivity (a :: (Bv ++ [sk] ++ Bc) ++ u :: X ++ LR); [| apply perm_new_done].
  apply perm_skip. rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
  apply Permutation_sym. apply (Permutation_middle Bc (u :: X ++ LR) sk).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma munch_nil_eq : forall m m', munch [] m m' -> m' = m.
Proof. intros m m' H. apply functional_extensionality. intros x. apply H. exact I. Qed.


End CeilWrap.
End CJ_pvalue_lemmas.

(* [comment removed for export] *)
Module CJ_pvalue_ctx.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_lemmas CJ_pvalue_lemmas.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section PV.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (SPB : Z) (LB LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).

  (* [comment removed for export] *)
  Definition pv_pure : Prop :=
    Permutation ((U, 64) :: LR) LB
    /\ (In (D, n) LR /\ D <= CA /\ CA + blen <= D + n)
    /\ Z.of_nat (length bs) = blen /\ blen < 2^31
    /\ alloc_ceiling <= lo /\ lo <= bv_unsigned sp - PARSE_STACK depth
    /\ (bv_unsigned sp <= P /\ P + 56 <= SPB /\ SPB < 2^62 /\ P mod 8 = 0)   (* [comment removed for export] *)
    /\ 0 <= off <= blen /\ 0 <= depth <= 1000
    /\ tp = wz PTP
    /\ cblock_range U 64 /\ cblock_range D n /\ (U + 64 <= D \/ D + n <= U).
  Hypothesis PVC : pv_pure.

  Definition POSTV := parse_value_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR U P CA blen off depth bs D n lo m
                       nx pv ty p1 vi p2 vd ky.

  (* [comment removed for export] *)
  Definition SAVEDV : list cell := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition CSTV (pc : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word)
      (Fx : bvmap 5 word) (fcx : bv 32) (mm : word -> option byte) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
       Fx (Z_to_bv 64 pc) fcx None mm (seg_rom usegs).

  Definition MIDV (m1 : word -> option byte) (mo1 : Model) (LB1 : list cblock) (errv1 : word) : Prop :=
    LHEAP HI SPB LB1 m1 mo1 /\ bytes_at usegs m1 CA bs /\ CJST m1 /\ rw_cells usegs m1 PERRNO [C4 errv1]
    /\ mem_inv usegs m1 /\ stk usegs m1 lo (bv_unsigned sp + -144) /\ ppres LR (bv_unsigned sp) P m m1.

  Lemma pvc_lits :
    Permutation ((U, 64) :: LR) LB /\ (In (D, n) LR /\ D <= CA /\ CA + blen <= D + n)
    /\ Z.of_nat (length bs) = blen /\ blen < 2^31
    /\ alloc_ceiling <= lo /\ lo <= bv_unsigned sp - (144 * (1001 - depth) + 16384)
    /\ (bv_unsigned sp <= P /\ P + 56 <= SPB /\ SPB < 2^62 /\ P mod 8 = 0)
    /\ 0 <= off <= blen /\ 0 <= depth <= 1000 /\ tp = wz PTP
    /\ (0 < U /\ U mod 16 = 0 /\ 0 <= 64 /\ U + 64 <= alloc_ceiling /\ (U + 64 <= 0x10000 \/ 0x56000 <= U))
    /\ (0 < D /\ D mod 16 = 0 /\ 0 <= n /\ D + n <= alloc_ceiling /\ (D + n <= 0x10000 \/ 0x56000 <= D))
    /\ (U + 64 <= D \/ D + n <= U)
    /\ 0 <= bv_unsigned sp < 2^64.
  Proof.
    pose proof PVC as H. unfold pv_pure, cblock_range, PARSE_STACK, PIMG_LO, PIMG_HI in H. try rewrite alloc_ceiling_eq in H.
    pose proof (bv_unsigned_in_range 64 sp) as R. change (bv_modulus 64) with (2^64) in R.
    destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
    repeat (split; [assumption|]). exact R.
  Qed.

  Ltac lits := pose proof pvc_lits as (HPU & HDn & LEN & BLEN & CEIL & LO & PP & OFF & DEP & TP & URNG & DRNG & UD & SPR).

  (* [comment removed for export] *)
  Lemma epilogue_run : forall (junk : list byte) x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 Fx fcx mm,
    rw_cells usegs mm (bv_unsigned sp + -144) (CB 80 junk :: SAVEDV) ->
    evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                                 Fx (ret_pc ra) fcx None mm (seg_rom usegs))
        (CSTV 0x140d0 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 Fx fcx mm).
  Proof.
    intros. lits. unfold CSTV, SAVEDV in *.
    do 10 zstep. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ret0_tail : forall (junk : list byte) (off1 depth1 : Z) m1 mo1 LB1 errv1 Fx fcx
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    MIDV m1 mo1 LB1 errv1 -> Permutation ((U, 64) :: LR) LB1 ->
    rw_cells usegs m1 (bv_unsigned sp + -144) (CB 80 junk :: SAVEDV) ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    SCPS usegs POSTV (CSTV 0x140cc x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HP1 FR PB ND FA FRM. lits. unfold CSTV.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. eapply evt_cut; [apply (epilogue_run junk); exact FR|]. intros ms' ->.
    unfold SAVEDV in FR. release_frame FR ST (bv_unsigned sp).
    apply evt_done. apply scps_done. unfold POSTV, parse_value_post.
    do 17 eexists. exists m1, 0, off1, depth1, LB1, [], errv1.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FA|]. split; [exact FRM|].
    split.
    { split; [exact HL|]. split; [exact HP1|].
      split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [exact CJ|]. split; [exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [try rewrite alloc_ceiling_eq; exact CEIL|]. exact PP. }
    split; [exact PR|]. split; [exact PB|]. left. split; [reflexivity|]. split; [reflexivity| exact ND].
  Qed.
End PV.


End CeilWrap.
End CJ_pvalue_ctx.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_utraps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaSplit.
Module CJ_delete.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_utraps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition DELETE_ENTRY : Z := 0x137c0.
Definition DELETE_STACK (d : nat) : Z := 32 * Z.of_nat d + RMALLOC_STACK.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PermFacts.
  Context {X : Type}.
  Implicit Types (x : X) (Bv Bk Bc Bn LR : list X).

  Lemma perm_node_nokids : forall x Bv Bk Bn LR,
    Permutation (x :: Bv ++ Bk ++ Bn ++ LR) ((x :: Bv ++ Bk ++ [] ++ Bn) ++ LR).
  Proof. intros. cbn [app]. rewrite <- !app_assoc. apply Permutation_refl. Qed.

  (* [comment removed for export] *)
  Lemma perm_node_kids : forall x Bv Bk Bc Bn LR,
    Permutation (Bc ++ x :: Bv ++ Bk ++ Bn ++ LR) ((x :: Bv ++ Bk ++ Bc ++ Bn) ++ LR).
  Proof.
    intros. cbn [app]. rewrite <- !app_assoc. apply Permutation_sym.
    apply (@Permutation_cons_app X (Bv ++ Bk ++ Bc ++ Bn ++ LR) Bc (Bv ++ Bk ++ Bn ++ LR) x).
    rewrite (app_assoc Bv Bk (Bc ++ Bn ++ LR)), (app_assoc Bv Bk (Bn ++ LR)).
    apply Permutation_sym, Permutation_app_swap_app.
  Qed.
End PermFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition delete_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LHEAP : Z -> list cblock -> (word -> option byte) -> Model -> Prop)
    (SPB : Z) (LR : list cblock) (lo : Z) (errv : word) (m : word -> option byte)
    : machine_state -> Model -> Prop :=
  fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (LR' : list cblock),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ CJST m'
    /\ rw_cells usegs m' PERRNO [C4 errv]
    /\ LHEAP SPB LR' m' mo' /\ Permutation LR' LR
    /\ cj_pres LR (bv_unsigned sp) m m'.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac slv := rewrite ?alloc_ceiling_eq in *; unfold RMALLOC_STACK, DELETE_STACK in *; lia.

Section S.
  Variable HI : cj_heap_iface.

  Definition delete_spec_at (d : nat) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
           (T : Z -> Prop) (SPB : Z) (LB LR B : list cblock) (p lo : Z) (errv : word),
    LHEAP HI SPB LB m mo ->
    cj_chain T m d p B ->
    Permutation (B ++ LR) LB ->
    CJST m ->
    bv_unsigned sp <= SPB ->
    stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - DELETE_STACK d ->
    rw_cells usegs m PERRNO [C4 errv] ->
    mem_inv usegs m ->
    tp = wz PTP ->
    a0 = wz p ->
    SCPS usegs (delete_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (LHEAP HI) SPB LR lo errv m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz DELETE_ENTRY) fc None m (seg_rom usegs)) mo.

  (* [comment removed for export] *)
  Lemma cj_pres_store_block : forall SPB LB m mo A n R (L : list cblock) SP lo' hi' m1 m2,
    LHEAP HI SPB LB m mo -> Permutation ((A, n) :: R) LB ->
    (forall b, In b L -> In b R) -> alloc_ceiling <= SP ->
    munch [(lo', hi')] m1 m2 -> wmono usegs m1 m2 -> A <= lo' -> hi' <= A + n ->
    cj_pres L SP m1 m2.
  Proof.
    intros SPB LB m mo A n R L SP lo' hi' m1 m2 HL HP HLR HSP MU WM Hlo Hhi a Ha Hc.
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 R2 R3 R4 R5).
    try rewrite alloc_ceiling_eq in *. unfold PIMG_LO, PIMG_HI in R5.
    split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn. split; [|exact I].
    destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]].
    - lia.
    - unfold PDATA_LO, PIMG_HI in Hd. lia.
    - destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' (HLR _ Hin)) as [_ D]. lia.
  Qed.

  Section Loop.
    Variable dk : nat.
    Hypothesis REC : forall d, (d < dk)%nat -> delete_spec_at d.

    (* [comment removed for export] *)
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
              (m0 : word -> option byte) (SPB : Z) (LR : list cblock) (lo : Z) (errv : word) (T : Z -> Prop).
    Hypothesis TP : tp = wz PTP.
    Hypothesis SPBle : bv_unsigned sp <= SPB.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis LO1 : lo <= bv_unsigned sp - 32 - RMALLOC_STACK.
    Hypothesis SPhi : bv_unsigned sp <= 2^64.

    Notation SP1 := (bv_unsigned sp + -32).
    Notation S2V := (Z_to_bv 64 0x247dc).
    Notation POST := (delete_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (LHEAP HI) SPB LR lo errv m0).
    Notation FRAME mm := (rw_cells usegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).

    (* [comment removed for export] *)
    Definition linv (LBX : list cblock) (m : word -> option byte) (mo : Model) : Prop :=
      LHEAP HI SPB LBX m mo /\ stk usegs m lo SP1 /\ FRAME m /\ CJST m
      /\ rw_cells usegs m PERRNO [C4 errv] /\ mem_inv usegs m /\ cj_pres LR (bv_unsigned sp) m0 m.

    (* [comment removed for export] *)
    Notation LST pc rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mm :=
      (MS (mkR rav (Z_to_bv 64 SP1) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 S2V s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

    (* [comment removed for export] *)
    Definition TestSpec (n : nat) : Prop :=
      forall (d : nat) (p : Z) (B LBX : list cblock) (m : word -> option byte) (mo : Model)
             (rav t0 t1 t2 s1v a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      (length B <= n)%nat -> (d <= dk)%nat ->
      lo <= bv_unsigned sp - DELETE_STACK d ->
      cj_chain T m d p B -> Permutation (B ++ LR) LBX -> linv LBX m mo ->
      SCPS usegs POST (LST 0x137f0 rav t0 t1 t2 (Z_to_bv 64 p) s1v a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m) mo.

    Lemma SP1eq : bv_unsigned (Z_to_bv 64 SP1) = SP1.
    Proof. apply unsigned_lit. try rewrite alloc_ceiling_eq in CEIL. unfold RMALLOC_STACK in LO1. lia. Qed.

    (* [comment removed for export] *)
    Lemma loop_exit : forall LBX m mo rav t0 t1 t2 s1v a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      Permutation LR LBX -> linv LBX m mo ->
      SCPS usegs POST (LST 0x137f0 rav t0 t1 t2 (Z_to_bv 64 0) s1v a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m) mo.
    Proof.
      intros until t6. intros HP nelH_; (nelim nelH_ 7%nat; intros HL ST FR CJ ERR MI PR).
      try rewrite alloc_ceiling_eq in CEIL. unfold RMALLOC_STACK in LO1.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
      step. step. step. step. step. step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. apply scps_done. unfold delete_post.
      nexists 17%nat. split; [reflexivity|].
      split; [exact MI|]. split; [exact ST|]. split; [exact CJ|]. split; [exact ERR|].
      split; [exact HL|]. split; [apply Permutation_sym; exact HP| exact PR].
    Qed.

    Section Body.
      Variable n : nat.
      Hypothesis IHn : forall n', (n' < n)%nat -> TestSpec n'.
      (* [comment removed for export] *)
      Variables (d0 : nat) (p nx : Z) (pv : word) (ch ty : Z) (p1 : word) (vs : Z) (vi p2 vd : word) (ky : Z)
                (Bv Bk Bc Bn : list cblock).
      Hypothesis Dle : (S d0 <= dk)%nat.
      Hypothesis LOd : lo <= bv_unsigned sp - DELETE_STACK (S d0).
      Hypothesis LEN : (length ((p, 64%Z) :: Bv ++ Bk ++ Bc ++ Bn) <= n)%nat.
      Hypothesis PNZ : p <> 0.
      Hypothesis TY : 0 <= ty < 256.

      (* [comment removed for export] *)
      Lemma tail3 : forall LBX m mo (vs' ky' : Z) rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
        Permutation ((p, 64) :: Bn ++ LR) LBX -> linv LBX m mo ->
        rw_cells usegs m p (node_cells nx pv ch ty p1 vs' vi p2 vd ky') ->
        cj_chain T m (S d0) nx Bn ->
        SCPS usegs POST (LST 0x137e4 rav t0 t1 t2 (Z_to_bv 64 nx) (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m) mo.
      Proof.
        intros until t6. intros HP (HL & ST & FR & CJ & ERR & MI & PR) ND CHN.
        try rewrite alloc_ceiling_eq in CEIL. unfold RMALLOC_STACK in LO1. pose proof SP1eq as E1.
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 R2 R3 R4 R5).
        try rewrite alloc_ceiling_eq in R4.
        (nelimp CJ 3%nat; intros HK _ _). unfold PHOOKS in HK. unfold node_cells in ND.
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
        step. step. step.
        replace (ret_pc (wz PFREE)) with (wz PFREE) by (unfold wz, PFREE; symmetry; apply ret_pc_even; [lia| reflexivity]).
        apply evt_done. cbv beta.
        eapply scps_bind.
        { eapply (lh_free HI) with (lo := lo) (A := p) (n := 64); rewrite ?E1;
            first [ exact HL | eapply perm_in_head; exact HP | exact ST | exact ERR | exact MI | exact TP | reflexivity | slv ]. }
        cbv beta. intros ms2 mo2 PO.
        (nelim PO 22%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> MI2 ST2 ERR2 PR2 HL2)
.
        rewrite E1 in ST2, PR2.
        replace (ret_pc (Z_to_bv 64 0x137f0)) with (Z_to_bv 64 0x137f0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (perm_cb_remove _ _ _ _ HP (lh_nodup HI _ _ _ _ HL)) as HP2.
        eapply (IHn (length Bn) ltac:(cbn in LEN; rewrite !length_app in LEN; lia) (S d0) nx Bn (cb_remove p LBX) m2 mo2);
          [lia| exact Dle| exact LOd| | |].
        - eapply cj_chain_pres; [exact CHN| exact PR2|]. intros b Hb. eapply Permutation_in; [exact HP2|]. apply in_or_app; left; exact Hb.
        - eapply Permutation_trans; [| exact HP2]. apply Permutation_refl.
        - split; [exact HL2|]. split; [exact ST2|]. split.
          { eapply cj_pres_rw_cells; [exact PR2| exact FR|]. left. lia. }
          split; [eapply CJST_pres; [exact PR2| exact CJ]|]. split; [exact ERR2|]. split; [exact MI2|].
          eapply cj_pres_trans; [exact PR|]. eapply cj_pres_weaken; [exact PR2| lia|].
          intros b Hb. eapply Permutation_in; [exact HP2|]. apply in_or_app; right; exact Hb.
      Qed.

      (* [comment removed for export] *)
      Lemma tail2 : forall LBX m mo (vs' : Z) rav t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
        Permutation ((p, 64) :: Bk ++ Bn ++ LR) LBX -> linv LBX m mo ->
        rw_cells usegs m p (node_cells nx pv ch ty p1 vs' vi p2 vd ky) ->
        cj_str m ky Bk -> cj_chain T m (S d0) nx Bn ->
        SCPS usegs POST (LST 0x13840 rav t0 t1 t2 (Z_to_bv 64 nx) (Z_to_bv 64 p) a0 (Z_to_bv 64 ty) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m) mo.
      Proof.
        intros until t6. intros HP LI ND SK CHN. (nelimp LI 7%nat; intros HL ST FR CJ ERR MI PR).
        pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL. unfold RMALLOC_STACK in LO1. pose proof SP1eq as E1.
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 R2 R3 R4 R5).
        try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
        pose proof (cj_str_range _ _ _ SK) as KR.
        (nelimp CJ 3%nat; intros HK _ _). unfold PHOOKS in HK. pose proof ND as ND'. unfold node_cells in ND.
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
        step. rewrite (unsigned_lit ty), land_ty_512 by lia. step. if_false.
        step. unfold wz. step. if_cases Kz; zify_cond Kz.
        - (* [comment removed for export] *)
          rewrite Kz in SK. pose proof (cj_str_zero_inv _ _ SK) as EBk. rewrite EBk in HP. cbn [app] in HP.
          apply evt_done. cbv beta. eapply tail3; [exact HP| exact LI| exact ND'| exact CHN].
        - (nelim (cj_str_nonzero_inv _ _ _ SK Kz) 7%nat; intros nk kstr ktail EBk _ _ _). rewrite EBk in HP. cbn [app] in HP.
          step. step.
          replace (ret_pc (wz PFREE)) with (wz PFREE) by (unfold wz, PFREE; symmetry; apply ret_pc_even; [lia| reflexivity]).
          apply evt_done. cbv beta.
          eapply scps_bind.
          { eapply (lh_free HI) with (lo := lo) (A := ky) (n := nk); rewrite ?E1;
              first [ exact HL | eapply Permutation_in; [exact HP| right; left; reflexivity]
                    | exact ST | exact ERR | exact MI | exact TP | reflexivity | slv ]. }
          cbv beta. intros ms2 mo2 PO.
          (nelim PO 22%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> MI2 ST2 ERR2 PR2 HL2)
.
          rewrite E1 in ST2, PR2.
          replace (ret_pc (Z_to_bv 64 0x13858)) with (Z_to_bv 64 0x13858) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          assert (HP2 : Permutation ((p, 64) :: Bn ++ LR) (cb_remove ky LBX)).
          { eapply perm_cb_remove; [| exact (lh_nodup HI _ _ _ _ HL)]. eapply Permutation_trans; [apply perm_swap| exact HP]. }
          apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
          apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in ND; [| right; right; exists p, 64; split; [eapply perm_in_head; exact HP2| cbn; lia]].
          apply (CJST_pres _ _ _ _ PR2) in CJ.
          apply (cj_chain_pres _ _ _ _ _ _ _ _ CHN) in PR2 as CHN2.
          2:{ intros b Hb. eapply Permutation_in; [exact HP2|]. right. apply in_or_app. left. exact Hb. }
          assert (PR3 : cj_pres LR (bv_unsigned sp) m0 m2).
          { eapply cj_pres_trans; [exact PR|]. eapply cj_pres_weaken; [exact PR2| lia|].
            intros b Hb. eapply Permutation_in; [exact HP2|]. right. apply in_or_app. right. exact Hb. }
          clear PR PR2 MI ST ERR HL CHN HK.
          (nelimp CJ 3%nat; intros HK _ _). unfold PHOOKS in HK. unfold PERRNO in ERR2.
          (* [comment removed for export] *)
          pose proof (munch_refl [(p + 56, p + 64)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
          eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
          step. fix_lit_store. step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
          assert (HL3 : LHEAP HI SPB (cb_remove ky LBX) m3 mo2).
          { eapply (lh_frame HI); [exact HL2| exact MU| exact WM|]. constructor; [|constructor].
            do 4 right. exists p, 64. split; [eapply perm_in_head; exact HP2| cbn; lia]. }
          assert (PR4 : cj_pres LR (bv_unsigned sp) m0 m3).
          { eapply cj_pres_trans; [exact PR3|]. eapply (cj_pres_store_block _ _ _ _ _ _ _ _ _ _ _ _ _ HL2 HP2); [| slv| exact MU| exact WM| lia| lia].
            intros b Hb. apply in_or_app. right. exact Hb. }
          assert (CHN3 : cj_chain T m3 (S d0) nx Bn).
          { eapply cj_chain_frame; [exact CHN2| exact MU| exact WM|].
            intros A' n' Hin. eapply (lheap_block_disjoint_from HI); [exact HL2| exact HP2| | | apply in_or_app; left; exact Hin]; lia. }
          assert (CJ3 : CJST m3).
          { eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' Hin. cbn in Hin. destruct Hin as [E|[]]. inversion E; subst. unfold PDATA_LO, PIMG_HI. lia. }
          apply evt_done. cbv beta.
          eapply tail3; [exact HP2| | exact ND| exact CHN3].
          split; [exact HL3|]. split; [exact ST2|]. split; [exact FR|]. split; [exact CJ3|]. split; [exact ERR2|]. split; [assumption| exact PR4].
      Qed.

      (* [comment removed for export] *)
      Lemma tail1 : forall LBX m mo rav t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
        Permutation ((p, 64) :: Bv ++ Bk ++ Bn ++ LR) LBX -> linv LBX m mo ->
        rw_cells usegs m p (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
        cj_str m vs Bv -> cj_str m ky Bk -> cj_chain T m (S d0) nx Bn ->
        SCPS usegs POST (LST 0x13820 rav t0 t1 t2 (Z_to_bv 64 nx) (Z_to_bv 64 p) a0 (Z_to_bv 64 ty) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m) mo.
      Proof.
        intros until t6. intros HP LI ND SV SK CHN. (nelimp LI 7%nat; intros HL ST FR CJ ERR MI PR).
        pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL. unfold RMALLOC_STACK in LO1. pose proof SP1eq as E1.
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 R2 R3 R4 R5).
        try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
        pose proof (cj_str_range _ _ _ SV) as VR.
        (nelimp CJ 3%nat; intros HK _ _). unfold PHOOKS in HK. pose proof ND as ND'. unfold node_cells in ND.
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
        step. rewrite (unsigned_lit ty), land_ty_256 by lia. step. if_false.
        step. unfold wz. step. if_cases Kz; zify_cond Kz.
        - (* [comment removed for export] *)
          rewrite Kz in SV. pose proof (cj_str_zero_inv _ _ SV) as EBv. rewrite EBv in HP. cbn [app] in HP.
          apply evt_done. cbv beta. eapply tail2; [exact HP| exact LI| exact ND'| exact SK| exact CHN].
        - (nelim (cj_str_nonzero_inv _ _ _ SV Kz) 7%nat; intros nv vstr vtail EBv _ _ _). rewrite EBv in HP. cbn [app] in HP.
          step. step.
          replace (ret_pc (wz PFREE)) with (wz PFREE) by (unfold wz, PFREE; symmetry; apply ret_pc_even; [lia| reflexivity]).
          apply evt_done. cbv beta.
          eapply scps_bind.
          { eapply (lh_free HI) with (lo := lo) (A := vs) (n := nv); rewrite ?E1;
              first [ exact HL | eapply Permutation_in; [exact HP| right; left; reflexivity]
                    | exact ST | exact ERR | exact MI | exact TP | reflexivity | slv ]. }
          cbv beta. intros ms2 mo2 PO.
          (nelim PO 22%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> MI2 ST2 ERR2 PR2 HL2)
.
          rewrite E1 in ST2, PR2.
          replace (ret_pc (Z_to_bv 64 0x13838)) with (Z_to_bv 64 0x13838) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          assert (HP2 : Permutation ((p, 64) :: Bk ++ Bn ++ LR) (cb_remove vs LBX)).
          { eapply perm_cb_remove; [| exact (lh_nodup HI _ _ _ _ HL)]. eapply Permutation_trans; [apply perm_swap| exact HP]. }
          apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
          apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in ND; [| right; right; exists p, 64; split; [eapply perm_in_head; exact HP2| cbn; lia]].
          apply (CJST_pres _ _ _ _ PR2) in CJ.
          apply (cj_chain_pres _ _ _ _ _ _ _ _ CHN) in PR2 as CHN2.
          2:{ intros b Hb. eapply Permutation_in; [exact HP2|]. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
          apply (cj_str_pres _ _ _ _ _ _ SK) in PR2 as SK2.
          2:{ intros b Hb. eapply Permutation_in; [exact HP2|]. right. apply in_or_app. left. exact Hb. }
          assert (PR3 : cj_pres LR (bv_unsigned sp) m0 m2).
          { eapply cj_pres_trans; [exact PR|]. eapply cj_pres_weaken; [exact PR2| lia|].
            intros b Hb. eapply Permutation_in; [exact HP2|]. right. apply in_or_app. right. apply in_or_app. right. exact Hb. }
          clear PR PR2 MI ST ERR HL CHN HK SK.
          (nelimp CJ 3%nat; intros HK _ _). unfold PHOOKS in HK. unfold PERRNO in ERR2.
          (* [comment removed for export] *)
          pose proof (munch_refl [(p + 32, p + 40)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
          eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
          step. unfold wz. rewrite (sx32_lit ty) by lia. step. fix_lit_store.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
          assert (HL3 : LHEAP HI SPB (cb_remove vs LBX) m3 mo2).
          { eapply (lh_frame HI); [exact HL2| exact MU| exact WM|]. constructor; [|constructor].
            do 4 right. exists p, 64. split; [eapply perm_in_head; exact HP2| cbn; lia]. }
          assert (PR4 : cj_pres LR (bv_unsigned sp) m0 m3).
          { eapply cj_pres_trans; [exact PR3|]. eapply (cj_pres_store_block _ _ _ _ _ _ _ _ _ _ _ _ _ HL2 HP2); [| slv| exact MU| exact WM| lia| lia].
            intros b Hb. apply in_or_app. right. apply in_or_app. right. exact Hb. }
          assert (CHN3 : cj_chain T m3 (S d0) nx Bn).
          { eapply cj_chain_frame; [exact CHN2| exact MU| exact WM|].
            intros A' n' Hin. eapply (lheap_block_disjoint_from HI); [exact HL2| exact HP2| | | apply in_or_app; right; apply in_or_app; left; exact Hin]; lia. }
          assert (SK3 : cj_str m3 ky Bk).
          { eapply cj_str_frame; [exact SK2| exact MU| exact WM|].
            intros A' n' Hin. eapply (lheap_block_disjoint_from HI); [exact HL2| exact HP2| | | apply in_or_app; left; exact Hin]; lia. }
          assert (CJ3 : CJST m3).
          { eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' Hin. cbn in Hin. destruct Hin as [E|[]]. inversion E; subst. unfold PDATA_LO, PIMG_HI. lia. }
          apply evt_done. cbv beta.
          eapply tail2; [exact HP2| | exact ND| exact SK3| exact CHN3].
          split; [exact HL3|]. split; [exact ST2|]. split; [exact FR|]. split; [exact CJ3|]. split; [exact ERR2|]. split; [assumption| exact PR4].
      Qed.

      (* [comment removed for export] *)
      Lemma node_body : forall LBX m mo rav t0 t1 t2 s1v a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
        Permutation (((p, 64) :: Bv ++ Bk ++ Bc ++ Bn) ++ LR) LBX -> linv LBX m mo ->
        rw_cells usegs m p (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
        cj_str m vs Bv -> cj_str m ky Bk -> cj_chain T m d0 ch Bc -> cj_chain T m (S d0) nx Bn ->
        SCPS usegs POST (LST 0x137f4 rav t0 t1 t2 (Z_to_bv 64 p) s1v a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m) mo.
      Proof.
        intros until t6. intros HP LI ND SV SK CHC CHN. (nelimp LI 7%nat; intros HL ST FR CJ ERR MI PR).
        pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL. unfold RMALLOC_STACK in LO1. pose proof SP1eq as E1.
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 R2 R3 R4 R5).
        try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
        (nelimp (cj_chain_ptr_range _ _ _ _ _ CHC) 3%nat; intros CR1 CR2 CR3).
        pose proof ND as ND'. unfold node_cells in ND.
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
        (* [comment removed for export] *)
        step. rewrite (unsigned_lit p), (align16_land7 p R2) by lia. step. if_false.
        step. step. unfold wz. rewrite (zx32_lit ty) by lia. step. step. rewrite (unsigned_lit ty), land_ty_256 by lia.
        step. if_false. step. unfold wz. step. if_cases Kc; zify_cond Kc.
        - (* [comment removed for export] *)
          rewrite Kc in CHC. pose proof (cj_chain_null_inv _ _ _ _ CHC) as EBc. rewrite EBc in HP.
          apply evt_done. cbv beta. eapply tail1; [| exact LI| exact ND'| exact SV| exact SK| exact CHN].
          eapply Permutation_trans; [apply perm_node_nokids| exact HP].
        - (* [comment removed for export] *)
          step. apply evt_done. cbv beta.
          eapply scps_bind.
          { eapply (REC d0 ltac:(lia)) with (lo := lo) (LR := (p, 64) :: Bv ++ Bk ++ Bn ++ LR) (B := Bc); rewrite ?E1;
              first [ exact HL | exact CHC | exact CJ | exact ST | exact ERR | exact MI | exact TP | reflexivity | slv
                    | eapply Permutation_trans; [apply perm_node_kids| exact HP] ]. }
          cbv beta. intros ms2 mo2 PO.
          (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 LR2 -> MI2 ST2 CJ2 ERR2 HL2 HP2 PR2)
.
          rewrite E1 in ST2, PR2.
          replace (ret_pc (Z_to_bv 64 0x1381c)) with (Z_to_bv 64 0x1381c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          apply Permutation_sym in HP2.
          apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
          apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in ND; [| right; right; exists p, 64; split; [left; reflexivity| cbn; lia]].
          apply (cj_chain_pres _ _ _ _ _ _ _ _ CHN) in PR2 as CHN2.
          2:{ intros b Hb. right. apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. exact Hb. }
          apply (cj_str_pres _ _ _ _ _ _ SV) in PR2 as SV2. 2:{ intros b Hb. right. apply in_or_app; left. exact Hb. }
          apply (cj_str_pres _ _ _ _ _ _ SK) in PR2 as SK2. 2:{ intros b Hb. right. apply in_or_app; right. apply in_or_app; left. exact Hb. }
          assert (PR3 : cj_pres LR (bv_unsigned sp) m0 m2).
          { eapply cj_pres_trans; [exact PR|]. eapply cj_pres_weaken; [exact PR2| lia|].
            intros b Hb. right. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hb. }
          clear PR PR2 MI ST ERR HL CHN SK SV CJ.
          (* [comment removed for export] *)
          eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
          step. unfold wz. rewrite (sx32_lit ty) by lia.
          apply evt_done. cbv beta.
          eapply tail1; [exact HP2| | exact ND| exact SV2| exact SK2| exact CHN2].
          split; [exact HL2|]. split; [exact ST2|]. split; [exact FR|]. split; [exact CJ2|]. split; [exact ERR2|]. split; [exact MI2| exact PR3].
      Qed.
    End Body.

    (* [comment removed for export] *)
    Lemma test_spec : forall n, TestSpec n.
    Proof.
      induction n as [n IHn] using lt_wf_ind. unfold TestSpec.
      intros d p B LBX m mo rav t0 t1 t2 s1v a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 LEN Dle LOd CH HP LI.
      destruct (Z.eq_dec p 0) as [->|PNZ].
      - pose proof (cj_chain_null_inv _ _ _ _ CH) as ->. cbn [app] in HP. eapply loop_exit; [exact HP| exact LI].
      - (nelim (cj_chain_cons_inv _ _ _ _ _ CH PNZ) 24%nat; intros d0 nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn -> ND TY _ SV SK CHC CHN ->)
.
        (nelimp LI 7%nat; intros HL _ _ _ _ MI _).
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 _ _ R4 _).
        try rewrite alloc_ceiling_eq in R4.
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
        step. if_cases K; zify_cond K; [exfalso; exact (PNZ K)|]. clear K.
        apply evt_done. cbv beta.
        eapply (node_body n IHn d0 p nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn Dle LOd LEN PNZ TY);
          [exact HP| exact LI| exact ND| exact SV| exact SK| exact CHC| exact CHN].
    Qed.
  End Loop.

  (* [comment removed for export] *)
  Lemma cj_pres_stack_frame : forall SPB LB m mo (L : list cblock) SP lo' hi' m1 m2,
    LHEAP HI SPB LB m mo -> (forall b, In b L -> In b LB) ->
    munch [(lo', hi')] m1 m2 -> wmono usegs m1 m2 -> alloc_ceiling <= lo' -> hi' <= SP ->
    cj_pres L SP m1 m2.
  Proof.
    intros SPB LB m mo L SP lo' hi' m1 m2 HL HLB MU WM Hlo Hhi a Ha Hc.
    try rewrite alloc_ceiling_eq in Hlo.
    split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn. split; [|exact I].
    destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]].
    - lia.
    - unfold PDATA_LO, PIMG_HI in Hd. lia.
    - (nelimp (lh_block_range HI _ _ _ _ _ _ HL (HLB _ Hin)) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma delete_spec_upto : forall dk, (forall d, (d < dk)%nat -> delete_spec_at d) ->
    forall d, (d <= dk)%nat -> delete_spec_at d.
  Proof.
    intros dk REC d Hd. unfold delete_spec_at. intros until errv. intros HL CH HP CJ SPBle ST CEIL LO ERR MI TP A0.
    unfold DELETE_ENTRY, wz in *. subst a0.
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL.
    pose proof ST as STc; (nelim STc 3%nat; intros _ SPhi _).
    assert (LO0 : lo <= bv_unsigned sp - 32). { unfold DELETE_STACK, RMALLOC_STACK in *. lia. }
    pose proof CJ as (HK & (e1 & e2 & GE) & LC). unfold PHOOKS in HK. unfold PGERROR in GE. unfold PLCONV in LC. unfold PERRNO in ERR.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    destruct (Z.eq_dec p 0) as [->|PNZ].
    - (* [comment removed for export] *)
      pose proof (cj_chain_null_inv _ _ _ _ CH) as ->. cbn [app] in HP.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      carve_frame 32%nat ST.
      step. step. step. step. step.
      step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      assert (HL1 : LHEAP HI SPB LB m1 mo).
      { eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. lia. }
      assert (PR1 : cj_pres LB (bv_unsigned sp) m m1).
      { eapply cj_pres_stack_frame; [exact HL| intros b Hb; exact Hb| exact MU| exact WM| slv| lia]. }
      assert (CJ1 : CJST m1).
      { eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' Hin. cbn in Hin. destruct Hin as [E|[]]. inversion E; subst. unfold PDATA_LO, PIMG_HI. lia. }
      step. step. step. step. step. step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. apply scps_done. unfold delete_post.
      nexists 17%nat. split; [reflexivity|].
      split; [exact MI|]. split; [exact ST|]. split; [exact CJ1|]. split; [exact ERR|].
      split; [exact HL1|]. split; [apply Permutation_sym; exact HP|].
      eapply cj_pres_weaken; [exact PR1| lia|]. intros b Hb. eapply Permutation_in; [exact HP| exact Hb].
    - (nelim (cj_chain_cons_inv _ _ _ _ _ CH PNZ) 24%nat; intros d0 nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn -> ND TY _ SV SK CHC CHN ->)
.
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 R2 R3 R4 R5).
      try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
      assert (LO1 : lo <= bv_unsigned sp - 32 - RMALLOC_STACK).
      { unfold DELETE_STACK, RMALLOC_STACK in *. lia. }
      unfold RMALLOC_STACK in LO1.
      unfold node_cells in ND.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      carve_frame 32%nat ST.
      step. step. step. step. step.
      step. if_cases K; zify_cond K; [exfalso; exact (PNZ K)|]. clear K.
      step. step. step.
      apply evt_done. cbv beta.
      lazymatch goal with |- SCPS _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m1 end.
      assert (HL1 : LHEAP HI SPB LB m1 mo).
      { eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. lia. }
      assert (PR1 : cj_pres LB (bv_unsigned sp) m m1).
      { eapply cj_pres_stack_frame; [exact HL| intros b Hb; exact Hb| exact MU| exact WM| slv| lia]. }
      assert (CJ1 : CJST m1).
      { eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' Hin. cbn in Hin. destruct Hin as [E|[]]. inversion E; subst. unfold PDATA_LO, PIMG_HI. lia. }
      assert (INB : forall b, In b ((p, 64) :: Bv ++ Bk ++ Bc ++ Bn) -> In b LB).
      { intros b Hb. eapply Permutation_in; [exact HP|]. apply in_or_app. left. exact Hb. }
      eapply (node_body dk REC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPB LR lo errv T TP SPBle CEIL'
                ltac:(unfold RMALLOC_STACK; lia) SPhi (length ((p, 64) :: Bv ++ Bk ++ Bc ++ Bn))
                (fun n' _ => test_spec dk REC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPB LR lo errv T TP SPBle CEIL' ltac:(unfold RMALLOC_STACK; lia) SPhi n')
                d0 p nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn Hd LO (Nat.le_refl _) PNZ TY LB m1 mo);
        [exact HP| | | | | |].
      + split; [exact HL1|]. split; [exact ST|]. split; [exact FR|]. split; [exact CJ1|]. split; [exact ERR|]. split; [exact MI|].
        eapply cj_pres_weaken; [exact PR1| lia|]. intros b Hb. eapply Permutation_in; [exact HP|]. apply in_or_app. right. exact Hb.
      + exact ND.
      + eapply cj_str_pres; [exact SV| exact PR1|]. intros b Hb. apply INB. right. apply in_or_app. left. exact Hb.
      + eapply cj_str_pres; [exact SK| exact PR1|]. intros b Hb. apply INB. right. apply in_or_app; right. apply in_or_app; left. exact Hb.
      + eapply cj_chain_pres; [exact CHC| exact PR1|]. intros b Hb. apply INB. right. do 2 (apply in_or_app; right). apply in_or_app; left. exact Hb.
      + eapply cj_chain_pres; [exact CHN| exact PR1|]. intros b Hb. apply INB. right. do 3 (apply in_or_app; right). exact Hb.
  Qed.

  Theorem cjson_delete_spec : forall d, delete_spec_at d.
  Proof.
    intros d. induction d as [d IH] using lt_wf_ind.
    apply (delete_spec_upto d); [| apply Nat.le_refl]. intros d' Hd'. apply IH. exact Hd'.
  Qed.
End S.


End CeilWrap.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.
Ltac slv := rewrite ?alloc_ceiling_eq in *; unfold RMALLOC_STACK, DELETE_STACK in *; lia.
End CJ_delete.

(* [comment removed for export] *)
Module CJ_pvalue_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_skipws CJ_delete OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_lemmas CJ_pvalue_lemmas CJ_pvalue_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.

Section PVA.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (SPB : Z) (LB LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure sp tp SPB LB LR U P CA blen off depth bs D n lo.
  (* [comment removed for export] *)
  Variable nfuel : nat.
  Hypothesis FUEL : blen - off <= Z.of_nat nfuel.
  Hypothesis PVREC : forall nf, (nf < nfuel)%nat -> parse_value_at HI nf.

  Notation SP := (bv_unsigned sp).
  Notation L z := (Z_to_bv 64 z) (only parsing).
  Notation CST := (CSTV sp gp tp s7 s8 s9 s10 s11).
  Notation POST := (POSTV HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).
  Notation MID := (MIDV HI sp m SPB LR P CA bs lo).
  Notation SAVED := (SAVEDV ra s0 s1 s2 s3 s4 s5 s6).
  (* [comment removed for export] *)
  Definition dch : nat := Z.to_nat (999 - depth).

  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac dj := cbn [disjoint_from cells_size csize Nat.add length];
             repeat match goal with H : length ?l = _ |- context [length ?l] => rewrite H end;
             first [lia | split; [lia| exact I]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply u8arr_transport in H; [| exact MU| exact WM| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].
  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC) as (HPU & HDn & LEN & BLEN & CEIL & LO & PP & OFF & DEP & TP & URNG & DRNG & UD & SPR).
  Ltac alia := rewrite ?alloc_ceiling_eq; unfold DELETE_STACK, PARSE_STACK, PARSE_STRING_STACK; unfold RMALLOC_STACK; lia.

  (* [comment removed for export] *)
  Lemma arr_fail_delete : forall (junk : list byte) (off1 depth1 head : Z) (X : list cblock) (dd : nat) m1 mo1 LBX errv1 Fx fcx
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31,
    MID m1 mo1 LBX errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_ANY m1 dd head X -> Z.of_nat dd <= 1000 - depth ->
    rw_cells usegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    SCPS usegs POST (CST 0x140c4 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 x11 x12 x13 x14 x15 x16 x17
                         x18 (Z_to_bv 64 head) x20 x21 x22 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HPX CH Hdd FR PB ND FA FRM. lits. unfold CSTV.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (HPX' : Permutation (X ++ (U, 64) :: LR) LBX).
    { eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply Permutation_middle. }
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. zstep.
    replace (ret_pc (Z_to_bv 64 0x137c0)) with (wz DELETE_ENTRY) by (unfold wz, DELETE_ENTRY; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply scps_bind.
    { pose proof (cjson_delete_spec HI dd) as DS. unfold delete_spec_at in DS.
      eapply DS with (lo := lo); clear DS; rewrite ?unsigned_lit by lia;
        first [ exact HL | exact CH | exact HPX' | exact CJ | exact ST | exact ERR | exact MI | exact TP | reflexivity | alia ]. }
    cbv beta. intros ms2 mo2 PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & LR2
                    & -> & MI2 & ST2 & CJ2 & ERR2 & HL2 & HP2 & PR2).
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x140cc)) with (Z_to_bv 64 0x140cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
    pose proof PB as PB'. unfold pbuf_at in PB'. apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PB'; [| left; cbn; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in ND; [| right; right; exists U, 64; split; [left; reflexivity| rewrite node_cells_size; lia]].
    apply (cj_pres_bytes_at _ _ _ _ _ _ PR2) in BY; [| right; right; exists D, n; split; [right; apply (proj1 HDn)| lia]].
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
    zstep.
    eapply evt_cut; [eapply epilogue_run; [exact PVC| exact FR]|]. intros ms' ->.
    unfold SAVEDV in FR. release_frame FR ST2 (bv_unsigned sp).
    apply evt_done. apply scps_done. unfold POSTV, parse_value_post.
    do 17 eexists. exists m2, 0, off1, depth1, LR2, [], errv1.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FA|]. split; [exact FRM|].
    split.
    { split; [exact HL2|]. split; [apply Permutation_sym; exact HP2|].
      split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [exact CJ2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact ST2|]. split; [try rewrite alloc_ceiling_eq; exact CEIL|]. exact PP. }
    split. { eapply ppres_trans; [exact PR|]. eapply ppres_of_cj_pres; [exact PR2| lia| intros b Hb; right; exact Hb]. }
    split; [exact PB'|]. left. split; [reflexivity|]. split; [reflexivity| exact ND].
  Qed.

  (* [comment removed for export] *)
  Lemma arr_success : forall (junk : list byte) (o2 head : Z) (X : list cblock) m1 mo1 LBX errv1 Fx fcx
      x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31,
    MID m1 mo1 LBX errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_PRINTABLE m1 (S dch) head X -> depth <= 999 ->
    rw_cells usegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
    pbuf_at m1 P CA blen o2 depth ->
    rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off <= o2 < blen ->
    Fagree F Fx -> frm0 fcx ->
    SCPS usegs POST (CST 0x13dcc x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 (Z_to_bv 64 o2) x12 x13 x14 x15 x16 x17
                         x18 x19 x20 (Z_to_bv 64 head) x22 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HPX CH Hd FR PB ND Ho FA FRM. lits. unfold CSTV.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold PERRNO in ERR. unfold SAVEDV in FR.
    assert (INU : In (U, 64) LBX) by (eapply perm_in_head; exact HPX).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    pose proof (munch_refl [(U + 16, U + 28)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep. zstep. zstep. zstep. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : LHEAP HI SPB LBX m2 mo1) by (eapply (lheap_block_store HI); [exact HL| exact INU| exact MU| exact WM| lia| lia]).
    assert (CJ2 : CJST m2) by (eapply (CJST_block_store HI); [exact HL| exact INU| exact CJ| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres LR SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_block_store HI); [exact HL| exact HPX| intros b Hb; apply in_or_app; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
    assert (CH2 : cj_chain CJ_PRINTABLE m2 (S dch) head X).
    { eapply cj_chain_frame; [exact CH| exact MU| exact WM|].
      intros A k Hin. cbn. split; [|exact I].
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HPX A k ltac:(apply in_or_app; left; exact Hin)) as [_ DJ]. lia. }
    clear MU WM HL CJ PR CH.
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : LHEAP HI SPB LBX m3 mo1) by (eapply (lheap_frame_store HI); [exact HL2| exact MU| exact WM| alia| alia]).
    assert (CJ3 : CJST m3) by (eapply CJST_high_store; [exact CJ2| exact MU| exact WM| alia]).
    assert (PR3 : ppres LR SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply (ppres_pbuf_store HI); [exact HL2| intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]| exact MU| exact WM| alia| alia| alia]. }
    assert (CH3 : cj_chain CJ_PRINTABLE m3 (S dch) head X).
    { eapply cj_chain_frame; [exact CH2| exact MU| exact WM|].
      intros A k Hin. cbn. split; [|exact I].
      pose proof (lh_block_range HI _ _ _ _ _ _ HL2 ltac:(eapply Permutation_in; [exact HPX| right; apply in_or_app; left; exact Hin])) as (_ & _ & _ & R4 & _).
      try rewrite alloc_ceiling_eq in R4. lia. }
    clear MU WM HL2 CJ2 PR2 CH2.
    zstep. zstep.
    eapply evt_cut; [eapply epilogue_run; [exact PVC| exact FR]|]. intros ms' ->.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. apply scps_done. unfold POSTV, parse_value_post.
    do 17 eexists. exists m3, 1, (o2 + 1), depth, LBX, ([] ++ X), errv1.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FA|]. split; [exact FRM|].
    split.
    { split; [exact HL3|]. split; [exact HPX|].
      split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [exact CJ3|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [try rewrite alloc_ceiling_eq; exact CEIL|]. exact PP. }
    split; [exact PR3|].
    split. { unfold pbuf_at. eqcells PB. }
    right. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    exists head, 32, 0. do 2 eexists. exists (S dch), [], X. split; [reflexivity|].
    split; [eqcells ND|]. split; [cbn; auto 10|]. split; [apply cj_str_null|]. split; [exact CH3|]. unfold dch. lia.
  Qed.

  (* [comment removed for export] *)
  Definition arr_inv (m1 : word -> option byte) (head cur : Z) (X : list cblock) : Prop :=
    (head = 0 /\ X = [])
    \/ (head <> 0 /\ cur <> 0 /\ exists B1 Bv Bc (chc tyc vsc : Z) (pvc p1c vic p2c vdc : word),
          X = B1 ++ (cur, 64) :: Bv ++ Bc
          /\ cj_lseg CJ_PRINTABLE m1 dch head cur B1
          /\ rw_cells usegs m1 cur (node_cells 0 pvc chc tyc p1c vsc vic p2c vdc 0)
          /\ CJ_PRINTABLE tyc /\ cj_str m1 vsc Bv /\ cj_chain CJ_PRINTABLE m1 dch chc Bc).

  Lemma arr_inv_chain : forall m1 head cur X, arr_inv m1 head cur X -> cj_chain CJ_PRINTABLE m1 (S dch) head X.
  Proof.
    intros m1 head cur X [[-> ->]|(NZ & NZc & B1 & Bv & Bc & chc & tyc & vsc & pvc & p1c & vic & p2c & vdc & -> & SEG & ND & TY & SV & CH)].
    - apply cj_chain_nil.
    - apply cj_lseg_chain0. replace (Bv ++ Bc) with (Bv ++ [] ++ Bc) by reflexivity.
      eapply cj_lseg_snoc; eauto using cj_str_null. apply CJ_PRINTABLE_range. exact TY.
  Qed.

  Lemma arr_inv_magree : forall m1 m2 head cur X, arr_inv m1 head cur X -> magree (in_cblock X) m1 m2 -> arr_inv m2 head cur X.
  Proof.
    intros m1 m2 head cur X [[-> ->]|(NZ & NZc & B1 & Bv & Bc & chc & tyc & vsc & pvc & p1c & vic & p2c & vdc & -> & SEG & ND & TY & SV & CH)] MA.
    - left. auto.
    - right. split; [exact NZ|]. split; [exact NZc|]. exists B1, Bv, Bc, chc, tyc, vsc, pvc, p1c, vic, p2c, vdc. split; [reflexivity|].
      split. { eapply cj_lseg_magree; [exact SEG| exact MA|]. intros a Ha. rewrite in_cblock_app. left. exact Ha. }
      split. { eapply rw_cells_magree; [exact MA| exact ND|]. rewrite node_cells_size. intros a Ha. rewrite in_cblock_app, in_cblock_cons. right. left. lia. }
      split; [exact TY|].
      split. { eapply cj_str_magree; [exact MA| exact SV|]. intros a Ha. rewrite in_cblock_app, in_cblock_cons, in_cblock_app. right. right. left. exact Ha. }
      eapply cj_chain_magree; [exact CH| exact MA|]. intros a Ha. rewrite in_cblock_app, in_cblock_cons, in_cblock_app. right. right. right. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Definition ALOOP (c : nat) : Prop :=
    forall (o head cur : Z) (X : list cblock) m1 mo1 LBX errv1 Fx fcx (junk : list byte)
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o < blen -> depth <= 999 ->
      MID m1 mo1 LBX errv1 -> Permutation ((U, 64) :: X ++ LR) LBX -> arr_inv m1 head cur X ->
      rw_cells usegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
      pbuf_at m1 P CA blen o (depth + 1) ->
      rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      SCPS usegs POST (CST 0x13fc4 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 x11 x12 x13 x14 x15 x16 x17
                           x18 (Z_to_bv 64 head) (Z_to_bv 64 44) x21 (Z_to_bv 64 cur) x28 x29 x30 x31 Fx fcx m1) mo1.
End PVA.


End CeilWrap.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.
End CJ_pvalue_A.

(* [comment removed for export] *)
Module CJ_pobject_ctx.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_pbuf CJ_delete OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_utraps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_lemmas CJ_pvalue_lemmas CJ_pvalue_ctx CJ_pvalue_A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.
Ltac killK K := first [exfalso; apply K; reflexivity | exfalso; revert K; lia_cj_nf].

Section PO.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (SPB : Z) (LB LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure sp tp SPB LB LR U P CA blen off depth bs D n lo.
  (* [comment removed for export] *)
  Variable junk : list byte.

  Notation SP := (bv_unsigned sp).
  Notation POST := (POSTV HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).

  Definition SAVEDO : list cell := [CB 8 junk; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition CSTO (pc : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 : word)
      (Fx : bvmap 5 word) (fcx : bv 32) (mm : word -> option byte) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
       Fx (Z_to_bv 64 pc) fcx None mm (seg_rom usegs).

  Definition MIDO (m1 : word -> option byte) (mo1 : Model) (LB1 : list cblock) (errv1 : word) : Prop :=
    LHEAP HI SPB LB1 m1 mo1 /\ bytes_at usegs m1 CA bs /\ CJST m1 /\ rw_cells usegs m1 PERRNO [C4 errv1]
    /\ mem_inv usegs m1 /\ stk usegs m1 lo (bv_unsigned sp + -96) /\ ppres LR (bv_unsigned sp) P m m1.

  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC) as (HPU & HDn & LEN & BLEN & CEIL & LO & PP & OFF & DEP & TP & URNG & DRNG & UD & SPR).
  Ltac alia := rewrite ?alloc_ceiling_eq; unfold DELETE_STACK, PARSE_STACK, PARSE_STRING_STACK; unfold RMALLOC_STACK; lia.
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.

  (* [comment removed for export] *)
  Lemma epilogue_run_o : forall x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx mm,
    rw_cells usegs mm (SP + -96) SAVEDO ->
    evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                                 Fx (ret_pc ra) fcx None mm (seg_rom usegs))
        (CSTO 0x153c4 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx mm).
  Proof.
    intros. lits. unfold CSTO, SAVEDO in *.
    do 13 zstep. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ret0_epi_o : forall (off1 depth1 : Z) m1 mo1 LB1 errv1 Fx fcx
      x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31,
    MIDO m1 mo1 LB1 errv1 -> Permutation ((U, 64) :: LR) LB1 ->
    rw_cells usegs m1 (SP + -96) SAVEDO ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    SCPS usegs POST (CSTO 0x153c4 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HP1 FR PB ND FA FRM. lits. unfold CSTO.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    eapply evt_cut; [apply epilogue_run_o; exact FR|]. intros ms' ->.
    unfold SAVEDO in FR. release_frame FR ST (bv_unsigned sp).
    apply evt_done. apply scps_done. unfold POSTV, parse_value_post.
    do 17 eexists. exists m1, 0, off1, depth1, LB1, [], errv1.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FA|]. split; [exact FRM|].
    split.
    { split; [exact HL|]. split; [exact HP1|].
      split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [exact CJ|]. split; [exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [try rewrite alloc_ceiling_eq; exact CEIL|]. exact PP. }
    split; [exact PR|]. split; [exact PB|]. left. split; [reflexivity|]. split; [reflexivity| exact ND].
  Qed.

  Lemma ret0_o : forall (off1 depth1 : Z) m1 mo1 LB1 errv1 Fx fcx
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31,
    MIDO m1 mo1 LB1 errv1 -> Permutation ((U, 64) :: LR) LB1 ->
    rw_cells usegs m1 (SP + -96) SAVEDO ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    SCPS usegs POST (CSTO 0x153c0 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros MIDm HP1 FR PB ND FA FRM. pose proof MIDm as (HL & _). lits. unfold CSTO.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. apply evt_done. eapply ret0_epi_o; [exact MIDm| exact HP1| exact FR| exact PB| exact ND| exact FA| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Notation dch := (dch depth).

  (* [comment removed for export] *)
  Lemma fail_o : forall (off1 depth1 head : Z) (X : list cblock) (dd : nat) m1 mo1 LBX errv1 Fx fcx
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31,
    MIDO m1 mo1 LBX errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_ANY m1 dd head X -> Z.of_nat dd <= 1000 - depth ->
    rw_cells usegs m1 (SP + -96) SAVEDO ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    SCPS usegs POST (CSTO 0x153b8 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 head) x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HPX CH Hdd FR PB ND FA FRM. lits. unfold CSTO.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (HPX' : Permutation (X ++ (U, 64) :: LR) LBX).
    { eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply Permutation_middle. }
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. zstep.
    replace (ret_pc (Z_to_bv 64 0x137c0)) with (wz DELETE_ENTRY) by (unfold wz, DELETE_ENTRY; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply scps_bind.
    { pose proof (cjson_delete_spec HI dd) as DS. unfold delete_spec_at in DS.
      eapply DS with (lo := lo); clear DS; rewrite ?unsigned_lit by lia;
        first [ exact HL | exact CH | exact HPX' | exact CJ | exact ST | exact ERR | exact MI | exact TP | reflexivity | alia ]. }
    cbv beta. intros ms2 mo2 PO'.
    destruct PO' as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & LR2
                    & -> & MI2 & ST2 & CJ2 & ERR2 & HL2 & HP2 & PR2).
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x153c0)) with (Z_to_bv 64 0x153c0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; cbn; lia].
    pose proof PB as PB'. unfold pbuf_at in PB'. apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PB'; [| left; cbn; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in ND; [| right; right; exists U, 64; split; [left; reflexivity| rewrite node_cells_size; lia]].
    apply (cj_pres_bytes_at _ _ _ _ _ _ PR2) in BY; [| right; right; exists D, n; split; [right; apply (proj1 HDn)| lia]].
    eapply ret0_o; [| apply Permutation_sym; exact HP2| exact FR| exact PB'| exact ND| exact FA| exact FRM].
    split; [exact HL2|]. split; [exact BY|]. split; [exact CJ2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
    eapply ppres_trans; [exact PR|]. eapply ppres_of_cj_pres; [exact PR2| lia| intros b Hb; right; exact Hb].
  Qed.

  (* [comment removed for export] *)
  Lemma fail_o' : forall (off1 depth1 head : Z) (X : list cblock) (dd : nat) m1 mo1 LBX errv1 Fx fcx
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x28 x29 x30 x31,
    MIDO m1 mo1 LBX errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_ANY m1 dd head X -> Z.of_nat dd <= 1000 - depth -> head <> 0 ->
    rw_cells usegs m1 (SP + -96) SAVEDO ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    SCPS usegs POST (CSTO 0x153b0 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                         x18 x19 x20 x21 x22 x23 (Z_to_bv 64 head) x25 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros MIDm HPX CH Hdd HNZ FR PB ND FA FRM. pose proof MIDm as (HL & _). lits. unfold CSTO.
    pose proof (cj_chain_ptr_range _ _ _ _ _ CH) as (HR1 & _ & HR2).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. zstep. if_cases Kh; zify_cond Kh; [exfalso; lia|].
    apply evt_done. eapply fail_o; [exact MIDm| exact HPX| exact CH| exact Hdd| exact FR| exact PB| exact ND| exact FA| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Lemma fail_o'' : forall (off1 depth1 head : Z) (X : list cblock) (dd : nat) m1 mo1 LBX errv1 Fx fcx
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31,
    MIDO m1 mo1 LBX errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_ANY m1 dd head X -> Z.of_nat dd <= 1000 - depth -> head <> 0 ->
    rw_cells usegs m1 (SP + -96) SAVEDO ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    SCPS usegs POST (CSTO 0x153ac x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 head) x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros MIDm HPX CH Hdd HNZ FR PB ND FA FRM. pose proof MIDm as (HL & _). lits. unfold CSTO.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. apply evt_done. eapply fail_o'; [exact MIDm| exact HPX| exact CH| exact Hdd| exact HNZ| exact FR| exact PB| exact ND| exact FA| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Lemma obj_success : forall (o2 head : Z) (X : list cblock) m1 mo1 LBX errv1 Fx fcx
      x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31,
    MIDO m1 mo1 LBX errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_PRINTABLE m1 (S dch) head X -> depth <= 999 ->
    rw_cells usegs m1 (SP + -96) SAVEDO ->
    pbuf_at m1 P CA blen o2 depth ->
    rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off <= o2 < blen ->
    Fagree F Fx -> frm0 fcx ->
    SCPS usegs POST (CSTO 0x15138 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 (Z_to_bv 64 o2) x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 head) x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HPX CH Hd FR PB ND Ho FA FRM. lits. unfold CSTO.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold PERRNO in ERR. unfold SAVEDO in FR.
    assert (INU : In (U, 64) LBX) by (eapply perm_in_head; exact HPX).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. zstep.
    (* [comment removed for export] *)
    pose proof (munch_refl [(U + 16, U + 24)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : LHEAP HI SPB LBX m2 mo1) by (eapply (lheap_block_store HI); [exact HL| exact INU| exact MU| exact WM| lia| lia]).
    assert (CJ2 : CJST m2) by (eapply (CJST_block_store HI); [exact HL| exact INU| exact CJ| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres LR SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_block_store HI); [exact HL| exact HPX| intros b Hb; apply in_or_app; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
    assert (CH2 : cj_chain CJ_PRINTABLE m2 (S dch) head X).
    { eapply cj_chain_frame; [exact CH| exact MU| exact WM|].
      intros A k Hin. cbn. split; [|exact I].
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HPX A k ltac:(apply in_or_app; left; exact Hin)) as [_ DJ]. lia. }
    clear MU WM HL CJ PR CH.
    (* [comment removed for export] *)
    pose proof (munch_refl [(U + 24, U + 28)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : LHEAP HI SPB LBX m3 mo1) by (eapply (lheap_block_store HI); [exact HL2| exact INU| exact MU| exact WM| lia| lia]).
    assert (CJ3 : CJST m3) by (eapply (CJST_block_store HI); [exact HL2| exact INU| exact CJ2| exact MU| exact WM| lia| lia]).
    assert (PR3 : ppres LR SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply (ppres_block_store HI); [exact HL2| exact HPX| intros b Hb; apply in_or_app; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
    assert (CH3 : cj_chain CJ_PRINTABLE m3 (S dch) head X).
    { eapply cj_chain_frame; [exact CH2| exact MU| exact WM|].
      intros A k Hin. cbn. split; [|exact I].
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL2 HPX A k ltac:(apply in_or_app; left; exact Hin)) as [_ DJ]. lia. }
    clear MU WM HL2 CJ2 PR2 CH2.
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 16, P + 24)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (HL4 : LHEAP HI SPB LBX m4 mo1) by (eapply (lheap_frame_store HI); [exact HL3| exact MU| exact WM| alia| alia]).
    assert (CJ4 : CJST m4) by (eapply CJST_high_store; [exact CJ3| exact MU| exact WM| alia]).
    assert (PR4 : ppres LR SP P m m4).
    { eapply ppres_trans; [exact PR3|]. eapply (ppres_pbuf_store HI); [exact HL3| intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]| exact MU| exact WM| alia| alia| alia]. }
    assert (CH4 : cj_chain CJ_PRINTABLE m4 (S dch) head X).
    { eapply cj_chain_frame; [exact CH3| exact MU| exact WM|].
      intros A k Hin. cbn. split; [|exact I].
      pose proof (lh_block_range HI _ _ _ _ _ _ HL3 ltac:(eapply Permutation_in; [exact HPX| right; apply in_or_app; left; exact Hin])) as (_ & _ & _ & R4 & _).
      try rewrite alloc_ceiling_eq in R4. lia. }
    clear MU WM HL3 CJ3 PR3 CH3.
    zstep. zstep.
    eapply evt_cut; [apply epilogue_run_o; exact FR|]. intros ms' ->.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. apply scps_done. unfold POSTV, parse_value_post.
    do 17 eexists. exists m4, 1, (o2 + 1), depth, LBX, ([] ++ X), errv1.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FA|]. split; [exact FRM|].
    split.
    { split; [exact HL4|]. split; [exact HPX|].
      split; [apply (proj1 HDn)|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [exact LEN|]. split; [exact BLEN|].
      split; [exact CJ4|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [try rewrite alloc_ceiling_eq; exact CEIL|]. exact PP. }
    split; [exact PR4|].
    split. { unfold pbuf_at. eqcells PB. }
    right. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    exists head, 64, 0. do 2 eexists. exists (S dch), [], X. split; [reflexivity|].
    split; [eqcells ND|]. split; [cbn; auto 10|]. split; [apply cj_str_null|]. split; [exact CH4|]. unfold CJ_pvalue_A.dch. lia.
  Qed.

  (* [comment removed for export] *)
  Definition obj_inv (m1 : word -> option byte) (head cur : Z) (X : list cblock) : Prop :=
    (head = 0 /\ X = [])
    \/ (head <> 0 /\ cur <> 0 /\ exists B1 Bv Bk Bc (chc tyc vsc kyc : Z) (pvc p1c vic p2c vdc : word),
          X = B1 ++ (cur, 64) :: Bv ++ Bk ++ Bc
          /\ cj_lseg CJ_PRINTABLE m1 dch head cur B1
          /\ rw_cells usegs m1 cur (node_cells 0 pvc chc tyc p1c vsc vic p2c vdc kyc)
          /\ CJ_PRINTABLE tyc /\ cj_str m1 vsc Bv /\ cj_str m1 kyc Bk /\ cj_chain CJ_PRINTABLE m1 dch chc Bc).

  Lemma obj_inv_chain : forall m1 head cur X, obj_inv m1 head cur X -> cj_chain CJ_PRINTABLE m1 (S dch) head X.
  Proof.
    intros m1 head cur X [[-> ->]|(NZ & NZc & B1 & Bv & Bk & Bc & chc & tyc & vsc & kyc & pvc & p1c & vic & p2c & vdc & -> & SEG & ND & TY & SV & SK & CH)].
    - apply cj_chain_nil.
    - apply cj_lseg_chain0. eapply cj_lseg_snoc; eauto. apply CJ_PRINTABLE_range. exact TY.
  Qed.

  Lemma obj_inv_magree : forall m1 m2 head cur X, obj_inv m1 head cur X -> magree (in_cblock X) m1 m2 -> obj_inv m2 head cur X.
  Proof.
    intros m1 m2 head cur X [[-> ->]|(NZ & NZc & B1 & Bv & Bk & Bc & chc & tyc & vsc & kyc & pvc & p1c & vic & p2c & vdc & -> & SEG & ND & TY & SV & SK & CH)] MA.
    - left. auto.
    - right. split; [exact NZ|]. split; [exact NZc|]. exists B1, Bv, Bk, Bc, chc, tyc, vsc, kyc, pvc, p1c, vic, p2c, vdc. split; [reflexivity|].
      split. { eapply cj_lseg_magree; [exact SEG| exact MA|]. intros a Ha. rewrite in_cblock_app. left. exact Ha. }
      split. { eapply rw_cells_magree; [exact MA| exact ND|]. rewrite node_cells_size. intros a Ha. rewrite in_cblock_app, in_cblock_cons. right. left. lia. }
      split; [exact TY|].
      split. { eapply cj_str_magree; [exact MA| exact SV|]. intros a Ha. rewrite in_cblock_app, in_cblock_cons, in_cblock_app. right. right. left. exact Ha. }
      split. { eapply cj_str_magree; [exact MA| exact SK|]. intros a Ha. rewrite in_cblock_app, in_cblock_cons, !in_cblock_app. right. right. right. left. exact Ha. }
      eapply cj_chain_magree; [exact CH| exact MA|]. intros a Ha. rewrite in_cblock_app, in_cblock_cons, !in_cblock_app. right. right. right. right. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Variable nfuel : nat.
  Definition OLOOP (c : nat) : Prop :=
    forall (o head cur : Z) (X : list cblock) m1 mo1 LBX errv1 Fx fcx
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o < blen -> depth <= 999 ->
      MIDO m1 mo1 LBX errv1 -> Permutation ((U, 64) :: X ++ LR) LBX -> obj_inv m1 head cur X ->
      rw_cells usegs m1 (SP + -96) SAVEDO ->
      pbuf_at m1 P CA blen o (depth + 1) ->
      rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      SCPS usegs POST (CSTO 0x15180 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 x11 x12 x13 x14 x15 x16 x17
                           x18 x19 (Z_to_bv 64 58) (Z_to_bv 64 32) (Z_to_bv 64 44) x23 (Z_to_bv 64 head) (Z_to_bv 64 cur) x28 x29 x30 x31 Fx fcx m1) mo1.
End PO.


End CeilWrap.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.
Ltac killK K := first [exfalso; apply K; reflexivity | exfalso; revert K; lia_cj_nf].
End CJ_pobject_ctx.

(* [comment removed for export] *)
Module CJ_pobject_ws.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_skipws OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_lemmas CJ_pvalue_lemmas CJ_pvalue_ctx CJ_pobject_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WS.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (SPB : Z) (LB LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Hypothesis PVC : pv_pure sp tp SPB LB LR U P CA blen off depth bs D n lo.

  Notation SP := (bv_unsigned sp).
  Notation CST := (CSTO sp gp tp s10 s11).
  Notation NC := (18446744073709551615 - CA).
  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC) as (HPU & HDn & LEN & BLEN & CEIL & LO & PP & OFF & DEP & TP & URNG & DRNG & UD & SPR).

  (* [comment removed for export] *)
  Definition ws_mem (m0 m2 : word -> option byte) (r d : Z) : Prop :=
    rw_cells usegs m2 P (pbuf_cells CA blen r d) /\ bytes_at usegs m2 CA bs /\ mem_inv usegs m2
    /\ munch [(P + 16, P + 24)] m0 m2 /\ wmono usegs m0 m2.

  Lemma fin_stop' : forall i b, 0 <= i < blen -> nth_error bs (Z.to_nat i) = Some b -> 32 < bv_unsigned b -> fin blen bs i = i.
  Proof. intros. lits. eapply (fin_stop P CA); eauto. lia. Qed.
  Lemma fin_ws' : forall i b, 0 <= i < blen -> nth_error bs (Z.to_nat i) = Some b -> bv_unsigned b <= 32 ->
    fin blen bs i = (if i + 1 =? blen then blen - 1 else fin blen bs (i + 1)).
  Proof. intros. lits. eapply (fin_ws P CA); eauto; lia. Qed.

  (* [comment removed for export] *)
  Ltac ws_body IH cnt i PB BY MI MU WM nex :=
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB;
    pose proof (rw_cells_bound usegs _ _ _ PB) as PBB; rewrite pbuf_cells_size in PBB;
    unfold pbuf_cells, wz in PB; unfold CSTO;
    let b := fresh "b" in let Hn := fresh "Hn" in
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hn; [| apply nth_error_None in Hn; lia];
    pose proof (u8ro_read usegs _ CA bs i b _ BY Hn ltac:(lia) eq_refl) as RD;
    pose proof (byte_range b) as Rb;
    let KG := fresh "KG" in
    zstep; if_cases KG; zify_cond KG; [exfalso; lia|]; clear KG;
    zstep; zstep; zstep;
    let K := fresh "K" in let K2 := fresh "K2" in
    if_cases K; zify_cond K;
    [ (* [comment removed for export] *)
      zstep; if_cases K2; zify_cond K2; [| exfalso; lia];
      apply evt_done; nex;
      split; [rewrite ?(fin_stop' i b) by first [lia | exact Hn]; reflexivity|];
      split; [unfold pbuf_cells, wz; rewrite (fin_stop' i b) by first [lia | exact Hn]; exact PB|];
      split; [exact BY|]; split; [exact MI|]; split; [exact MU| exact WM]
    | (* [comment removed for export] *)
      zstep; zstep; zstep; if_cases K2; zify_cond K2;
      [ replace (CA + i + 1) with (CA + (i + 1)) by lia;
        rewrite (fin_ws' i b) by first [lia | exact Hn]; destruct (Z.eqb_spec (i + 1) blen); [exfalso; lia|];
        eapply (IH (cnt - 1)%nat ltac:(lia) (i + 1)); [lia| lia| unfold pbuf_cells, wz; exact PB| exact BY| exact MI| exact MU| exact WM]
      | zstep; zstep; zstep;
        rewrite (fin_ws' i b) by first [lia | exact Hn]; destruct (Z.eqb_spec (i + 1) blen); [| exfalso; lia];
        apply evt_done; nex;
        split; [try replace (blen - 1) with (blen + -1) by lia; reflexivity|];
        split; [unfold pbuf_cells, wz; replace (blen - 1) with (blen + -1) by lia; exact PB|];
        split; [exact BY|]; split; [exact MI|]; split; [exact MU| exact WM] ] ].

  (* [comment removed for export] *)
  Lemma ws1 : forall (cnt : nat) (i d : Z) (m0 m1 : word -> option byte) Fx fcx
      x1 x5 x6 x7 x9 x10 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells usegs m1 P (pbuf_cells CA blen i d) -> bytes_at usegs m1 CA bs -> mem_inv usegs m1 ->
    munch [(P + 16, P + 24)] m0 m1 -> wmono usegs m0 m1 ->
    evt usegs (fun ms' => exists x16' m2,
                 ms' = CST 0x1510c x1 x5 x6 x7 (Z_to_bv 64 P) x9 x10 (Z_to_bv 64 (fin blen bs i)) (Z_to_bv 64 CA) (Z_to_bv 64 blen) (Z_to_bv 64 NC) (Z_to_bv 64 32) x16' x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx m2
                 /\ ws_mem m0 m2 (fin blen bs i) d)
        (CST 0x150e0 x1 x5 x6 x7 (Z_to_bv 64 P) x9 x10 (Z_to_bv 64 i) (Z_to_bv 64 CA) (Z_to_bv 64 blen) (Z_to_bv 64 NC) (Z_to_bv 64 32) x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. unfold ws_mem. lits. ws_body IH cnt i PB BY MI MU WM ltac:(do 2 eexists).
  Qed.

  (* [comment removed for export] *)
  Lemma ws2 : forall (cnt : nat) (i d : Z) (m0 m1 : word -> option byte) Fx fcx
      x1 x5 x6 x7 x9 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells usegs m1 P (pbuf_cells CA blen i d) -> bytes_at usegs m1 CA bs -> mem_inv usegs m1 ->
    munch [(P + 16, P + 24)] m0 m1 -> wmono usegs m0 m1 ->
    evt usegs (fun ms' => exists x10' x11' x14' m2,
                 ms' = CST 0x15228 x1 x5 x6 x7 (Z_to_bv 64 P) x9 x10' x11' (Z_to_bv 64 CA) (Z_to_bv 64 NC) x14' x15 x16 x17
                          x18 x19 x20 (Z_to_bv 64 32) x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx m2
                 /\ ws_mem m0 m2 (fin blen bs i) d)
        (CST 0x151fc x1 x5 x6 x7 (Z_to_bv 64 P) x9 (Z_to_bv 64 blen) (Z_to_bv 64 i) (Z_to_bv 64 CA) (Z_to_bv 64 NC) x14 x15 x16 x17
             x18 x19 x20 (Z_to_bv 64 32) x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. unfold ws_mem. lits. ws_body IH cnt i PB BY MI MU WM ltac:(do 4 eexists).
  Qed.

  (* [comment removed for export] *)
  Lemma ws3 : forall (cnt : nat) (i d : Z) (m0 m1 : word -> option byte) Fx fcx
      x1 x5 x6 x7 x9 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells usegs m1 P (pbuf_cells CA blen i d) -> bytes_at usegs m1 CA bs -> mem_inv usegs m1 ->
    munch [(P + 16, P + 24)] m0 m1 -> wmono usegs m0 m1 ->
    evt usegs (fun ms' => exists x11' x12' x14' m2,
                 ms' = CST 0x1527c x1 x5 x6 x7 (Z_to_bv 64 P) x9 (Z_to_bv 64 CA) x11' x12' (Z_to_bv 64 NC) x14' x15 x16 x17
                          x18 x19 x20 (Z_to_bv 64 32) x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx m2
                 /\ ws_mem m0 m2 (fin blen bs i) d)
        (CST 0x15250 x1 x5 x6 x7 (Z_to_bv 64 P) x9 (Z_to_bv 64 CA) (Z_to_bv 64 blen) (Z_to_bv 64 i) (Z_to_bv 64 NC) x14 x15 x16 x17
             x18 x19 x20 (Z_to_bv 64 32) x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. unfold ws_mem. lits. ws_body IH cnt i PB BY MI MU WM ltac:(do 4 eexists).
  Qed.

  (* [comment removed for export] *)
  Lemma ws4 : forall (cnt : nat) (i d : Z) (m0 m1 : word -> option byte) Fx fcx
      x1 x5 x6 x7 x9 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells usegs m1 P (pbuf_cells CA blen i d) -> bytes_at usegs m1 CA bs -> mem_inv usegs m1 ->
    munch [(P + 16, P + 24)] m0 m1 -> wmono usegs m0 m1 ->
    evt usegs (fun ms' => exists x11' x12' x14' m2,
                 ms' = CST 0x152f8 x1 x5 x6 x7 (Z_to_bv 64 P) x9 (Z_to_bv 64 CA) x11' x12' (Z_to_bv 64 NC) x14' x15 x16 x17
                          x18 x19 x20 (Z_to_bv 64 32) x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx m2
                 /\ ws_mem m0 m2 (fin blen bs i) d)
        (CST 0x152cc x1 x5 x6 x7 (Z_to_bv 64 P) x9 (Z_to_bv 64 CA) (Z_to_bv 64 blen) (Z_to_bv 64 i) (Z_to_bv 64 NC) x14 x15 x16 x17
             x18 x19 x20 (Z_to_bv 64 32) x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. unfold ws_mem. lits. ws_body IH cnt i PB BY MI MU WM ltac:(do 4 eexists).
  Qed.

  (* [comment removed for export] *)
  Lemma ws5 : forall (cnt : nat) (i d : Z) (m0 m1 : word -> option byte) Fx fcx
      x1 x5 x6 x7 x9 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells usegs m1 P (pbuf_cells CA blen i d) -> bytes_at usegs m1 CA bs -> mem_inv usegs m1 ->
    munch [(P + 16, P + 24)] m0 m1 -> wmono usegs m0 m1 ->
    evt usegs (fun ms' => exists x13' x14' m2,
                 ms' = CST 0x1534c x1 x5 x6 x7 (Z_to_bv 64 P) x9 (Z_to_bv 64 CA) (Z_to_bv 64 (fin blen bs i)) (Z_to_bv 64 blen) x13' x14' x15 x16 x17
                          x18 x19 x20 (Z_to_bv 64 32) x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx m2
                 /\ ws_mem m0 m2 (fin blen bs i) d)
        (CST 0x15320 x1 x5 x6 x7 (Z_to_bv 64 P) x9 (Z_to_bv 64 CA) (Z_to_bv 64 i) (Z_to_bv 64 blen) (Z_to_bv 64 NC) x14 x15 x16 x17
             x18 x19 x20 (Z_to_bv 64 32) x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. unfold ws_mem. lits. ws_body IH cnt i PB BY MI MU WM ltac:(do 3 eexists).
  Qed.
End WS.


End CeilWrap.
End CJ_pobject_ws.

(* [comment removed for export] *)
Module CJ_pobject_L.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_skipws CJ_delete OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_utraps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_lemmas CJ_pvalue_lemmas CJ_pvalue_ctx CJ_pvalue_A CJ_pobject_ctx CJ_pobject_ws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section POL.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (SPB : Z) (LB LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure sp tp SPB LB LR U P CA blen off depth bs D n lo.
  Variable junk : list byte.
  Variable nfuel : nat.
  Hypothesis FUEL : blen - off <= Z.of_nat nfuel.
  Hypothesis PVREC : forall nf, (nf < nfuel)%nat -> parse_value_at HI nf.
  Hypothesis PS : parse_string_stmt HI.

  Notation SP := (bv_unsigned sp).
  Notation CST := (CSTO sp gp tp s10 s11).
  Notation POST := (POSTV HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).
  Notation MID := (MIDO HI sp m SPB LR P CA bs lo).
  Notation SAVED := (SAVEDO ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk).
  Notation dch := (dch depth).
  Notation OLOOPc := (OLOOP HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky junk).
  Notation WSM := (ws_mem P CA blen bs).
  Notation NC := (18446744073709551615 - CA).

  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac dj := cbn [disjoint_from cells_size csize Nat.add length];
             repeat match goal with H : length ?l = _ |- context [length ?l] => rewrite H end;
             first [lia | split; [lia| exact I]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply u8arr_transport in H; [| exact MU| exact WM| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].
  Ltac lits := (nelimp (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC) 14%nat; intros HPU HDn LEN BLEN CEIL LO PP OFF DEP TP URNG DRNG UD SPR).
  Ltac alia := rewrite ?alloc_ceiling_eq; unfold DELETE_STACK, PARSE_STACK, PARSE_STRING_STACK; unfold RMALLOC_STACK; lia.
  Ltac killK K := first [exfalso; apply K; reflexivity | exfalso; revert K; lia_cj_nf].

  (* [comment removed for export] *)
  Lemma zero_node_run_o : forall x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx mm (A : Z) (jk : list byte),
    rw_cells usegs mm A [CB 64 jk] -> mem_inv usegs mm -> A mod 16 = 0 ->
    evt usegs (fun ms' => exists mm',
                 ms' = CST 0x151bc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 A) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 A) (Z_to_bv 64 A) x20 x21 x22 (Z_to_bv 64 0) x24 x25 x28 x29 x30 x31 Fx fcx mm'
                 /\ munch [(A, A + 64)] mm mm' /\ wmono usegs mm mm' /\ mem_inv usegs mm'
                 /\ rw_cells usegs mm' A (node_cells 0 (wz 0) 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0))
        (CST 0x15190 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 A) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 Fx fcx mm).
  Proof using PVC nfuel.
    intros until jk. intros BLK MI AL. lits. unfold CSTO.
    pose proof (rw_cells_bound usegs _ _ _ BLK) as AB. cbn [cells_size csize Nat.add] in AB.
    pose proof (munch_refl [(A, A + 64)] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
    zstep. do 8 (zstep; fix_lit_store). zstep. rewrite (align16_land7 A AL). zstep.
    apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    apply zero_node_cells. exact BLK.
  Qed.

  (* [comment removed for export] *)
  Lemma close_o : forall (o3 hd A : Z) (Xall : list cblock) m1 mo1 LBX errv1 Fx fcx
      x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x23 x24 x25 x28 x29 x30 x31,
    MID m1 mo1 LBX errv1 -> Permutation ((U, 64) :: Xall ++ LR) LBX ->
    hd <> 0 -> cj_chain CJ_PRINTABLE m1 (S dch) hd Xall -> depth <= 999 ->
    rw_cells usegs m1 (SP + -96) SAVED ->
    pbuf_at m1 P CA blen o3 (depth + 1) ->
    rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off <= o3 < blen -> Fagree F Fx -> frm0 fcx ->
    SCPS usegs POST (CST 0x15388 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 (Z_to_bv 64 o3) x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 hd) (Z_to_bv 64 A) (Z_to_bv 64 58) (Z_to_bv 64 32) (Z_to_bv 64 44) x23 x24 x25 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros MIDm HPX HNZ CH Hd FR PB ND Ho FA FRM. lits. unfold CSTO.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b Xall -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; left; exact Hb]).
    unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold PERRNO in ERR. unfold SAVEDO in FR.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    pose proof (cj_chain_head_block _ _ _ _ _ CH HNZ) as INH0.
    pose proof (lh_block_range HI _ _ _ _ _ _ HL (INX _ INH0)) as (HD1 & HD16 & _ & HD4 & _). try rewrite alloc_ceiling_eq in HD4.
    pose proof (munch_refl [(P + 24, P + 32)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep. zstep. zstep. rewrite (align16_land7 hd HD16). zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    zstep. if_cases KA1; zify_cond KA1; [killK KA1|]. clear KA1.
    assert (HL2 : LHEAP HI SPB LBX m2 mo1) by (eapply (lheap_frame_store HI); [exact HL| exact MU| exact WM| alia| alia]).
    assert (CJ2 : CJST m2) by (eapply CJST_high_store; [exact CJ| exact MU| exact WM| alia]).
    assert (PR2 : ppres LR SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU| exact WM| alia| alia| alia]. }
    assert (CH2 : cj_chain CJ_PRINTABLE m2 (S dch) hd Xall).
    { eapply cj_chain_frame; [exact CH| exact MU| exact WM|].
      intros A' k Hin. cbn. split; [|exact I].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL (INX _ Hin)) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
    clear MU WM HL CJ PR CH.
    (* [comment removed for export] *)
    (nelim (cj_chain_cons_inv _ _ _ _ _ CH2 HNZ) 24%nat; intros d0 nxh pvh chh tyh p1h vsh vih p2h vdh kyh Bvh Bkh Bch Bnh Ed NDH TYH HTh SVh SKh CHCh CHNh EX)
.
    rewrite EX in HPX, INX.
    assert (HPh : Permutation ((hd, 64) :: (Bvh ++ Bkh ++ Bch ++ Bnh) ++ (U, 64) :: LR) LBX).
    { eapply Permutation_trans; [apply perm_pick_head| exact HPX]. }
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HPh)) 5%nat; intros H1 H2 H3 H4 H5).
    try rewrite alloc_ceiling_eq in H4. unfold PIMG_LO, PIMG_HI in H5.
    destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL2 HPh U 64 ltac:(apply in_or_app; right; left; reflexivity)) as [_ HU].
    destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL2 HPh D n ltac:(apply in_or_app; right; right; exact (proj1 HDn))) as [_ HD].
    unfold node_cells, wz in NDH.
    pose proof (munch_refl [(hd + 8, hd + 16)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (INH : In (hd, 64) LBX) by (eapply perm_in_head; exact HPh).
    assert (HL3 : LHEAP HI SPB LBX m3 mo1) by (eapply (lheap_block_store HI); [exact HL2| exact INH| exact MU| exact WM| lia| lia]).
    assert (CJ3 : CJST m3) by (eapply (CJST_block_store HI); [exact HL2| exact INH| exact CJ2| exact MU| exact WM| lia| lia]).
    assert (PR3 : ppres LR SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply (ppres_block_store HI); [exact HL2| exact HPh| intros b Hb; apply in_or_app; right; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
    assert (CH3 : cj_chain CJ_PRINTABLE m3 (S dch) hd Xall).
    { rewrite EX, Ed. eapply (cj_chain_relink HI); [exact HL2| exact HPh| exact HNZ| exact TYH| exact HTh| exact SVh| exact SKh| exact CHCh| exact CHNh| exact MU| exact WM| eqcells NDH]. }
    clear MU WM HL2 CJ2 PR2 CH2 SVh SKh CHCh CHNh. rewrite <- EX in HPX.
    zstep. rewrite (align16_land7 U) by lia. zstep. if_cases KA2; zify_cond KA2; [| killK KA2].
    apply evt_done.
    eapply obj_success; [exact PVC| | exact HPX| exact CH3| exact Hd| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact Ho| exact FA| exact FRM].
    split; [exact HL3|]. split; [exact BY|]. split; [exact CJ3|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST| exact PR3].
  Qed.

  Notation FAILO := (fail_o'' HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC junk).

  (* [comment removed for export] *)
  Lemma after_ws5 : forall (c : nat), (forall c', (c' < c)%nat -> OLOOPc c') ->
    forall (o o3 hd A : Z) (pvA : word) (chA tyA vsA kyA : Z) (viA vdA : word) (X Bv Bk Bc : list cblock) m1 mo1 LBX errv1 Fx fcx
           x1 x5 x6 x7 x13 x14 x15 x16 x17 x18' x24 x25 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o -> o < o3 <= blen -> depth <= 999 ->
      MID m1 mo1 LBX errv1 -> Permutation ((U, 64) :: (X ++ (A, 64) :: Bv ++ Bk ++ Bc) ++ LR) LBX ->
      hd <> 0 -> A <> 0 -> cj_lseg CJ_PRINTABLE m1 dch hd A X ->
      rw_cells usegs m1 A (node_cells 0 pvA chA tyA (wz 0) vsA viA (wz 0) vdA kyA) ->
      CJ_PRINTABLE tyA -> cj_str m1 vsA Bv -> cj_str m1 kyA Bk -> cj_chain CJ_PRINTABLE m1 dch chA Bc ->
      rw_cells usegs m1 (SP + -96) SAVED ->
      pbuf_at m1 P CA blen o3 (depth + 1) ->
      rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx -> x18' = Z_to_bv 64 hd ->
      SCPS usegs POST (CST 0x1534c x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) (Z_to_bv 64 CA) (Z_to_bv 64 o3) (Z_to_bv 64 blen) x13 x14 x15 x16 x17
                           x18' (Z_to_bv 64 A) (Z_to_bv 64 58) (Z_to_bv 64 32) (Z_to_bv 64 44) (Z_to_bv 64 0) x24 x25 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Ho3 Hd MIDm HPX HNZ ANZ SEG NDA HTA SVA SKA CHA FR PB ND FA FRM ->. lits. unfold CSTO.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (CH : cj_chain CJ_PRINTABLE m1 (S dch) hd (X ++ (A, 64) :: Bv ++ Bk ++ Bc)).
    { eapply cj_lseg_chain; [exact SEG|]. eapply cj_chain_one; [exact ANZ| exact NDA| apply CJ_PRINTABLE_range; exact HTA| exact HTA| exact SVA| exact SKA| exact CHA]. }
    assert (FAIL : forall x10' x12' x13' x14' x24' x25',
      SCPS usegs POST (CST 0x153ac x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10' (Z_to_bv 64 o3) x12' x13' x14' x15 x16 x17
                           (Z_to_bv 64 hd) (Z_to_bv 64 A) (Z_to_bv 64 58) (Z_to_bv 64 32) (Z_to_bv 64 44) (Z_to_bv 64 0) x24' x25' x28 x29 x30 x31 Fx fcx m1) mo1).
    { intros. eapply FAILO; [exact MIDm| exact HPX| eapply cj_chain_any; exact CH| unfold dch; lia| exact HNZ| exact FR| exact PB| exact ND| exact FA| exact FRM]. }
    unfold CSTO in FAIL.
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. if_cases Kend; zify_cond Kend.
    { (* [comment removed for export] *) apply evt_done. apply FAIL. }
    (* [comment removed for export] *)
    zstep. zstep. if_cases KW; zify_cond KW; [exfalso; lia|].
    zstep. zstep. zstep. zstep. if_cases KN; zify_cond KN.
    { exfalso. revert KN. replace (0 <? CA) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (CA + o3 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). vm_compute. discriminate. }
    zstep. if_cases KZ; zify_cond KZ; [exfalso; lia|].
    (nelim (text_read m1 CA bs o3 (Z_to_bv 64 (CA + o3)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b Hb RD Hat).
    pose proof (byte_range b) as Rb.
    zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc.
    { (* [comment removed for export] *)
      apply evt_done. pose proof (IHc (Z.to_nat (blen - o3)) ltac:(lia)) as IH. unfold OLOOP, CSTO in IH.
      eapply (IH o3 hd A (X ++ (A, 64) :: Bv ++ Bk ++ Bc) m1 mo1 LBX errv1); [lia| lia| exact Hd| exact MIDm| exact HPX| | exact FR| exact PB'| exact ND| exact FA| exact FRM].
      right. split; [exact HNZ|]. split; [exact ANZ|]. exists X, Bv, Bk, Bc, chA, tyA, vsA, kyA, pvA, (wz 0), viA, (wz 0), vdA.
      split; [reflexivity|]. split; [exact SEG|]. split; [exact NDA|]. split; [exact HTA|]. split; [exact SVA|]. split; [exact SKA| exact CHA]. }
    zstep. if_cases KZ2; zify_cond KZ2; [exfalso; lia|].
    zstep. zstep. if_cases K125; zify_cond K125.
    { (* [comment removed for export] *) apply evt_done. apply FAIL. }
    (* [comment removed for export] *)
    apply evt_done. eapply close_o; [exact MIDm| exact HPX| exact HNZ| exact CH| exact Hd| exact FR| exact PB'| exact ND| lia| exact FA| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Lemma after_val : forall (c : nat), (forall c', (c' < c)%nat -> OLOOPc c') ->
    forall (o o4 hd A KS k : Z) (pvA : word) (X : list cblock) (r off5 depth5 : Z) (X5 : list cblock) m1 mo1 LBX errv1 Fx fcx
           x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18' x24 x25 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o -> o < o4 -> depth <= 999 ->
      MID m1 mo1 LBX errv1 -> Permutation ((A, 64) :: X5 ++ (KS, k) :: (U, 64) :: X ++ LR) LBX ->
      hd <> 0 -> A <> 0 -> cj_lseg CJ_PRINTABLE m1 dch hd A X -> cj_str m1 KS [(KS, k)] ->
      rw_cells usegs m1 (SP + -96) SAVED ->
      pbuf_at m1 P CA blen off5 depth5 ->
      rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx -> x18' = Z_to_bv 64 hd ->
      ( (r = 0 /\ X5 = [] /\ rw_cells usegs m1 A (node_cells 0 pvA 0 16 (wz 0) 0 (wz 0) (wz 0) (wz 0) KS))
        \/ (r = 1 /\ depth5 = depth + 1 /\ o4 <= off5 <= blen
             /\ exists (ch ty' vs : Z) (vi' vd' : word) (dc : nat) (Bv Bc : list cblock),
                  X5 = Bv ++ Bc
                  /\ rw_cells usegs m1 A (node_cells 0 pvA ch ty' (wz 0) vs vi' (wz 0) vd' KS)
                  /\ CJ_PRINTABLE ty' /\ cj_str m1 vs Bv /\ cj_chain CJ_PRINTABLE m1 dc ch Bc
                  /\ Z.of_nat dc + (depth + 1) <= 1000) ) ->
      SCPS usegs POST (CST 0x15304 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                           x18' (Z_to_bv 64 A) (Z_to_bv 64 58) (Z_to_bv 64 32) (Z_to_bv 64 44) (Z_to_bv 64 0) x24 x25 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Ho4 Hd MIDm HPX HNZ ANZ SEG SK FR PB ND FA FRM -> RES. lits. unfold CSTO.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; right; right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; right; right; apply in_or_app; left; exact Hb]).
    assert (INS : In (KS, k) LBX) by (eapply Permutation_in; [exact HPX| right; apply in_or_app; right; left; reflexivity]).
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HPX)) 5%nat; intros A1 A2 A3 A4 A5).
    try rewrite alloc_ceiling_eq in A4. unfold PIMG_LO, PIMG_HI in A5.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    destruct RES as [(-> & -> & NDA) | (-> & -> & Ho5 & chA & tyA & vsA & viA & vdA & dc & Bv & Bc & -> & NDA & HTA & SVA & CHA & Hdc)].
    - (* [comment removed for export] *)
      zstep. if_true. apply evt_done.
      assert (CH : cj_chain CJ_ANY m1 (S dch) hd (X ++ (A, 64) :: [] ++ [(KS, k)] ++ [])).
      { eapply cj_lseg_chain; [eapply cj_lseg_mono; [exact SEG| intros; exact I| lia]|].
        eapply cj_chain_one; [exact ANZ| exact NDA| lia| exact I| apply cj_str_null| exact SK| apply cj_chain_nil]. }
      cbn [app] in CH.
      eapply FAILO; [exact MIDm| | exact CH| unfold dch; lia| exact HNZ| exact FR| exact PB| exact ND| exact FA| exact FRM].
      eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply (perm_new_done (U, 64) (A, 64) [(KS, k)] X LR).
    - (* [comment removed for export] *)
      pose proof (rw_cells_bound usegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
      assert (HPX' : Permutation ((U, 64) :: (X ++ (A, 64) :: Bv ++ [(KS, k)] ++ Bc) ++ LR) LBX).
      { eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply perm_new_done_k. }
      pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold node_cells, wz in NDA. unfold PERRNO in ERR. unfold SAVEDO in FR.
      assert (CHA' : cj_chain CJ_PRINTABLE m1 dch chA Bc) by (eapply cj_chain_mono_d; [exact CHA| unfold dch; lia]).
      clear CHA.
      zstep. if_false. zstep. zstep. zstep. zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
      zstep. if_cases Kend; zify_cond Kend.
      + (* [comment removed for export] *)
        apply evt_done.
        eapply (after_ws5 c IHc o off5 hd A pvA chA tyA vsA KS viA vdA X Bv [(KS, k)] Bc m1 mo1 LBX errv1);
          [exact Hc| exact Ho| lia| exact Hd| exact MIDm| exact HPX'| exact HNZ| exact ANZ| exact SEG| eqcells NDA| exact HTA| exact SVA| exact SK| exact CHA'| exact FR| exact PB'| eqcells ND| exact FA| exact FRM| reflexivity].
      + pose proof (fin_off0 blen off5 bs LEN ltac:(lia)) as FO.
        zstep. rewrite zb_lxor_ones by lia.
        eapply evt_cut.
        { eapply (ws5 sp gp tp s10 s11 SPB LB LR U P CA blen off depth bs D n lo PVC (Z.to_nat (blen - off5)) off5 (depth + 1) m1 m1);
            [lia| lia| exact PB| exact BY| exact MI| apply munch_refl| apply wmono_refl]. }
        intros ms' nelH_; (nelim nelH_ 9%nat; intros x13' x14' m2 -> PB2 BY2 MI2 MU2 WM2). unfold CSTO. rewrite <- FO in PB2 |- *.
        trc FR MU2 WM2. trc ND MU2 WM2. trc NDA MU2 WM2. trc ERR MU2 WM2. trc ST MU2 WM2.
        assert (HL2 : LHEAP HI SPB LBX m2 mo1) by (eapply (lheap_frame_store HI); [exact HL| exact MU2| exact WM2| alia| alia]).
        assert (CJ2 : CJST m2) by (eapply CJST_high_store; [exact CJ| exact MU2| exact WM2| alia]).
        assert (PR2 : ppres LR SP P m m2).
        { eapply ppres_trans; [exact PR|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU2| exact WM2| alia| alia| alia]. }
        assert (BLK : forall A' k', In (A', k') LBX -> disjoint_from [(P + 16, P + 24)] A' k').
        { intros A' k' Hin. cbn. split; [|exact I].
          (nelimp (lh_block_range HI _ _ _ _ _ _ HL Hin) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
        assert (SEG2 : cj_lseg CJ_PRINTABLE m2 dch hd A X).
        { eapply cj_lseg_frame; [exact SEG| exact MU2| exact WM2|]. intros A' k' Hin. apply BLK. apply INX. exact Hin. }
        assert (SK2 : cj_str m2 KS [(KS, k)]).
        { eapply cj_str_frame; [exact SK| exact MU2| exact WM2|]. intros A' k' [E|[]]. inversion E; subst. apply BLK. exact INS. }
        assert (SVA2 : cj_str m2 vsA Bv).
        { eapply cj_str_frame; [exact SVA| exact MU2| exact WM2|]. intros A' k' Hin. apply BLK.
          eapply Permutation_in; [exact HPX|]. right. apply in_or_app. left. apply in_or_app. left. exact Hin. }
        assert (CHA2 : cj_chain CJ_PRINTABLE m2 dch chA Bc).
        { eapply cj_chain_frame; [exact CHA'| exact MU2| exact WM2|]. intros A' k' Hin. apply BLK.
          eapply Permutation_in; [exact HPX|]. right. apply in_or_app. left. apply in_or_app. right. exact Hin. }
        pose proof (skipws_off_range bs off5 ltac:(rewrite LEN; lia)) as OR. rewrite LEN in OR.
        apply evt_done.
        eapply (after_ws5 c IHc o (skipws_off bs off5) hd A pvA chA tyA vsA KS viA vdA X Bv [(KS, k)] Bc m2 mo1 LBX errv1);
          [exact Hc| exact Ho| lia| exact Hd| | exact HPX'| exact HNZ| exact ANZ| exact SEG2| eqcells NDA| exact HTA| exact SVA2| exact SK2| exact CHA2| exact FR| unfold pbuf_at; exact PB2| eqcells ND| exact FA| exact FRM| reflexivity].
        split; [exact HL2|]. split; [exact BY2|]. split; [exact CJ2|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI2|]. split; [exact ST| exact PR2].
  Qed.

  (* [comment removed for export] *)
  Lemma key_done : forall (c : nat), (forall c', (c' < c)%nat -> OLOOPc c') ->
    forall (o o3 hd A KS k : Z) (pvA : word) (X : list cblock) m1 mo1 LBX errv1 Fx fcx
           x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18' x24 x25 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o -> o < o3 <= blen -> depth <= 999 ->
      MID m1 mo1 LBX errv1 -> Permutation ((A, 64) :: (KS, k) :: (U, 64) :: X ++ LR) LBX ->
      hd <> 0 -> A <> 0 -> cj_lseg CJ_PRINTABLE m1 dch hd A X -> cj_str m1 KS [(KS, k)] ->
      rw_cells usegs m1 A (node_cells 0 pvA 0 16 (wz 0) KS (wz 0) (wz 0) (wz 0) 0) ->
      rw_cells usegs m1 (SP + -96) SAVED ->
      pbuf_at m1 P CA blen o3 (depth + 1) ->
      rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx -> x18' = Z_to_bv 64 hd ->
      SCPS usegs POST (CST 0x1527c x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) (Z_to_bv 64 CA) x11 x12 x13 x14 x15 x16 x17
                           x18' (Z_to_bv 64 A) (Z_to_bv 64 58) (Z_to_bv 64 32) (Z_to_bv 64 44) (Z_to_bv 64 0) x24 x25 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Ho3 Hd MIDm HPX HNZ ANZ SEG SK NDA FR PB ND FA FRM ->. lits. unfold CSTO.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (rw_cells_bound usegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; right; right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; right; right; apply in_or_app; left; exact Hb]).
    assert (INS : In (KS, k) LBX) by (eapply Permutation_in; [exact HPX| right; left; reflexivity]).
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HPX)) 5%nat; intros A1 A2 A3 A4 A5).
    try rewrite alloc_ceiling_eq in A4. unfold PIMG_LO, PIMG_HI in A5.
    assert (APART : forall A' n', In (A', n') ((KS, k) :: (U, 64) :: X ++ LR) -> A' <> A /\ (A' + n' <= A \/ A + 64 <= A')).
    { intros A' n' Hin. eapply (lheap_perm_apart HI); [exact HL| exact HPX| exact Hin]. }
    destruct (APART U 64 ltac:(right; left; reflexivity)) as [_ AU]. destruct (APART D n ltac:(right; right; apply in_or_app; right; exact (proj1 HDn))) as [_ AD].
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold node_cells, wz in NDA. unfold PERRNO in ERR. unfold SAVEDO in FR.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    zstep. if_cases KG; zify_cond KG; [killK KG|]. clear KG.
    (* [comment removed for export] *)
    pose proof (munch_refl [(A + 32, A + 64)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep. zstep. zstep. zstep. fix_lit_store. zstep. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : LHEAP HI SPB LBX m2 mo1) by (eapply (lheap_block_store HI); [exact HL| eapply perm_in_head; exact HPX| exact MU| exact WM| lia| lia]).
    assert (CJ2 : CJST m2) by (eapply (CJST_block_store HI); [exact HL| eapply perm_in_head; exact HPX| exact CJ| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres LR SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_block_store HI); [exact HL| exact HPX| intros b Hb; right; right; apply in_or_app; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
    assert (DJ : forall A' n', In (A', n') ((KS, k) :: (U, 64) :: X ++ LR) -> disjoint_from [(A + 32, A + 64)] A' n').
    { intros A' n' Hin. cbn. split; [|exact I]. destruct (APART A' n' Hin). lia. }
    assert (SEG2 : cj_lseg CJ_PRINTABLE m2 dch hd A X).
    { eapply cj_lseg_frame; [exact SEG| exact MU| exact WM|]. intros A' n' Hin. apply DJ. right; right. apply in_or_app. left. exact Hin. }
    assert (SK2 : cj_str m2 KS [(KS, k)]).
    { eapply cj_str_frame; [exact SK| exact MU| exact WM|]. intros A' n' [E|[]]. inversion E; subst. apply DJ. left. reflexivity. }
    assert (MID2 : MID m2 mo1 LBX errv1).
    { split; [exact HL2|]. split; [exact BY|]. split; [exact CJ2|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST| exact PR2]. }
    clear MU WM HL CJ PR SEG SK DJ MIDm.
    (* [comment removed for export] *)
    assert (CH : cj_chain CJ_ANY m2 (S dch) hd (X ++ (A, 64) :: [] ++ [(KS, k)] ++ [])).
    { eapply cj_lseg_chain; [eapply cj_lseg_mono; [exact SEG2| intros; exact I| lia]|].
      eapply cj_chain_one; [exact ANZ| eqcells NDA| lia| exact I| apply cj_str_null| exact SK2| apply cj_chain_nil]. }
    cbn [app] in CH.
    assert (HPXf : Permutation ((U, 64) :: (X ++ (A, 64) :: [(KS, k)]) ++ LR) LBX).
    { eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply (perm_new_done (U, 64) (A, 64) [(KS, k)] X LR). }
    assert (FAIL : forall x10' x12' x13' x14' x15' m', m' = m2 ->
      SCPS usegs POST (CST 0x153ac x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10' (Z_to_bv 64 blen) x12' x13' x14' x15' x16 x17
                           (Z_to_bv 64 hd) (Z_to_bv 64 A) (Z_to_bv 64 58) (Z_to_bv 64 32) (Z_to_bv 64 44) (Z_to_bv 64 0) x24 x25 x28 x29 x30 x31 Fx fcx m') mo1).
    { intros x10' x12' x13' x14' x15' m' ->. eapply FAILO; [exact MID2| exact HPXf| exact CH| unfold dch; lia| exact HNZ| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact FA| exact FRM]. }
    unfold CSTO in FAIL.
    (* [comment removed for export] *)
    zstep. if_cases Kend; zify_cond Kend.
    { apply evt_done. apply FAIL. reflexivity. }
    zstep. zstep. if_cases KW; zify_cond KW; [exfalso; lia|].
    zstep. zstep. zstep. zstep. if_cases KN; zify_cond KN.
    { exfalso. revert KN. replace (0 <? CA) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (CA + o3 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). vm_compute. discriminate. }
    zstep. if_cases KZ; zify_cond KZ; [exfalso; lia|].
    (nelim (text_read m2 CA bs o3 (Z_to_bv 64 (CA + o3)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b Hb RD _).
    pose proof (byte_range b) as Rb.
    zstep. zstep. if_cases K58; zify_cond K58.
    { apply evt_done. apply FAIL. reflexivity. }
    clear FAIL CH HPXf.
    (* [comment removed for export] *)
    (nelimp MID2 7%nat; intros HL _ CJ _ _ _ PR).
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (BLK : forall A' k', In (A', k') LBX -> disjoint_from [(P + 16, P + 24)] A' k').
    { intros A' k' Hin. cbn. split; [|exact I].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL Hin) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
    (* [comment removed for export] *)
    assert (JOIN : forall x11' x12' x13' x14' x15' m4,
      rw_cells usegs m4 P (pbuf_cells CA blen (skipws_off bs (o3 + 1)) (depth + 1)) -> bytes_at usegs m4 CA bs -> mem_inv usegs m4 ->
      munch [(P + 16, P + 24)] m3 m4 -> wmono usegs m3 m4 ->
      evt usegs (fun ms' => SCPS usegs POST ms' mo1)
        (CST 0x152f8 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) (Z_to_bv 64 CA) x11' x12' x13' x14' x15' x16 x17
             (Z_to_bv 64 hd) (Z_to_bv 64 A) (Z_to_bv 64 58) (Z_to_bv 64 32) (Z_to_bv 64 44) (Z_to_bv 64 0) x24 x25 x28 x29 x30 x31 Fx fcx m4)).
    { intros x11' x12' x13' x14' x15' m4 PB4 BY4 MI4 MU4 WM4. unfold CSTO.
      pose proof (munch_trans _ _ _ _ MU MU4) as MU24. pose proof (wmono_trans _ _ _ _ WM WM4) as WM24.
      pose proof FR as FR4. trc FR4 MU4 WM4. pose proof ND as ND4. trc ND4 MU4 WM4. pose proof NDA as NDA4. trc NDA4 MU4 WM4.
      pose proof ERR as ERR4. trc ERR4 MU4 WM4. pose proof ST as ST4. trc ST4 MU4 WM4.
      assert (HL4 : LHEAP HI SPB LBX m4 mo1) by (eapply (lheap_frame_store HI); [exact HL| exact MU24| exact WM24| alia| alia]).
      assert (CJ4 : CJST m4) by (eapply CJST_high_store; [exact CJ| exact MU24| exact WM24| alia]).
      assert (PR4 : ppres LR SP P m m4).
      { eapply ppres_trans; [exact PR|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU24| exact WM24| alia| alia| alia]. }
      assert (SEG4 : cj_lseg CJ_PRINTABLE m4 dch hd A X).
      { eapply cj_lseg_frame; [exact SEG2| exact MU24| exact WM24|]. intros A' k' Hin. apply BLK. apply INX. exact Hin. }
      assert (SK4 : cj_str m4 KS [(KS, k)]).
      { eapply cj_str_frame; [exact SK2| exact MU24| exact WM24|]. intros A' k' [E|[]]. inversion E; subst. apply BLK. exact INS. }
      assert (O4 : o3 + 1 <= skipws_off bs (o3 + 1) <= blen).
      { destruct (Z.eq_dec (o3 + 1) blen) as [E|NE].
        - rewrite skipws_off_noop by lia. lia.
        - pose proof (skipws_off_range bs (o3 + 1)) as OR. rewrite LEN in OR. lia. }
      set (o4 := skipws_off bs (o3 + 1)) in *.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      assert (PI : parse_inv HI m4 mo1 SPB LBX [] ((KS, k) :: (U, 64) :: X ++ LR) A P CA blen bs D n lo (SP + -96) errv1).
      { split; [exact HL4|]. split; [exact HPX|]. split; [right; right; apply in_or_app; right; exact (proj1 HDn)|].
        split; [lia|]. split; [lia|]. split; [exact BY4|]. split; [exact LEN|]. split; [exact BLEN|]. split; [exact CJ4|].
        split; [unfold PERRNO; exact ERR4|]. split; [exact MI4|]. split; [exact ST4|]. split; [alia|]. lia. }
      apply evt_done. cbv beta.
      eapply scps_bind.
      { pose proof (PVREC (Z.to_nat (blen - o4)) ltac:(lia)) as PVS. unfold parse_value_at in PVS.
        eapply PVS with (U := A) (P := P) (off := o4) (depth := depth + 1) (nx := 0) (ty := 16) (ky := KS); clear PVS; rewrite ?unsigned_lit by lia;
          first [exact PI | unfold pbuf_at; exact PB4 | eqcells NDA4 | exact FRM | exact TP | reflexivity | alia ]. }
      cbv beta. intros ms5 mo5 PO'.
      (nelim PO' 32%nat; intros t0' t1' t2' a0' a1_ a2_ a3_ a4_ a5_ a6_ a7' t3' t4' t5' t6' F5 fc5 m5 r off5 depth5 LB5 X5 errv5 -> -> FA5 FRM5 PI5 PR5 PB5 RES)
.
      rewrite ?unsigned_lit in PI5, PR5 by lia.
      replace (ret_pc (Z_to_bv 64 0x15304)) with (Z_to_bv 64 0x15304) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      (nelim PI5 13%nat; intros HL5 HP5 _ _ _ BY5 _ _ CJ5 ERR5 MI5 ST5 _).
      apply (ppres_rw_cells_stack _ _ _ _ _ _ _ PR5) in FR4; [| lia| cbn; lia].
      apply (ppres_rw_cells_block _ _ _ _ _ _ _ U 64 PR5) in ND4; [| right; left; reflexivity| lia| cbn; lia].
      apply (ppres_cj_lseg _ _ _ _ _ _ _ _ _ _ PR5) in SEG4; [| intros b' Hb'; right; right; apply in_or_app; left; exact Hb'].
      apply (ppres_cj_str _ _ _ _ _ _ _ PR5) in SK4; [| intros b' [E|[]]; inversion E; subst; left; reflexivity].
      assert (PR6 : ppres LR SP P m m5).
      { eapply ppres_trans; [exact PR4|]. eapply ppres_weaken; [exact PR5| lia| intros b' Hb'; right; right; apply in_or_app; right; exact Hb']. }
      unfold wz. eapply (after_val c IHc o o4 hd A KS k pvA X r off5 depth5 X5 m5 mo5 LB5 errv5);
        [exact Hc| lia| lia| exact Hd| | exact HP5| exact HNZ| exact ANZ| exact SEG4| exact SK4| exact FR4| exact PB5| eqcells ND4| eapply Fagree_trans; [exact FA| exact FA5]| exact FRM5| reflexivity| exact RES].
      split; [exact HL5|]. split; [exact BY5|]. split; [exact CJ5|]. split; [exact ERR5|]. split; [exact MI5|]. split; [exact ST5| exact PR6]. }
    zstep. if_cases Kskip; zify_cond Kskip.
    - (* [comment removed for export] *)
      eapply JOIN; [| exact BY| exact MI| apply munch_refl| apply wmono_refl]. rewrite skipws_off_noop by lia. unfold pbuf_cells, wz. exact PB.
    - pose proof (fin_off0 blen (o3 + 1) bs LEN ltac:(lia)) as FO.
      zstep. rewrite zb_lxor_ones by lia.
      eapply evt_cut.
      { eapply (ws4 sp gp tp s10 s11 SPB LB LR U P CA blen off depth bs D n lo PVC (Z.to_nat (blen - (o3 + 1))) (o3 + 1) (depth + 1) m3 m3);
          [lia| lia| unfold pbuf_cells, wz; exact PB| exact BY| exact MI| apply munch_refl| apply wmono_refl]. }
      intros ms' nelH_; (nelim nelH_ 10%nat; intros x11' x12' x14' m4 -> PB4 BY4 MI4 MU4 WM4). rewrite <- FO in PB4.
      eapply JOIN; [exact PB4| exact BY4| exact MI4| exact MU4| exact WM4].
  Qed.

  (* [comment removed for export] *)
  Lemma after_key : forall (c : nat), (forall c', (c' < c)%nat -> OLOOPc c') ->
    forall (o o1 hd A : Z) (pvA : word) (X : list cblock) (r off2 : Z) (X2 : list cblock) m1 mo1 LBX errv1 Fx fcx
           x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18' x24 x25 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o -> o < o1 -> depth <= 999 ->
      MID m1 mo1 LBX errv1 -> Permutation ((A, 64) :: X2 ++ (U, 64) :: X ++ LR) LBX ->
      hd <> 0 -> A <> 0 -> cj_lseg CJ_PRINTABLE m1 dch hd A X ->
      rw_cells usegs m1 (SP + -96) SAVED ->
      pbuf_at m1 P CA blen off2 (depth + 1) -> o1 <= off2 <= blen ->
      rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx -> x18' = Z_to_bv 64 hd ->
      ( (r = 0 /\ X2 = [] /\ rw_cells usegs m1 A (node_cells 0 pvA 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0))
        \/ (r = 1 /\ exists (KS k : Z), X2 = [(KS, k)] /\ KS <> 0
              /\ rw_cells usegs m1 A (node_cells 0 pvA 0 16 (wz 0) KS (wz 0) (wz 0) (wz 0) 0)
              /\ cj_str m1 KS [(KS, k)]) ) ->
      SCPS usegs POST (CST 0x15234 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                           x18' (Z_to_bv 64 A) (Z_to_bv 64 58) (Z_to_bv 64 32) (Z_to_bv 64 44) (Z_to_bv 64 0) x24 x25 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Ho1 Hd MIDm HPX HNZ ANZ SEG FR PB Ho2 ND FA FRM -> RES. lits. unfold CSTO.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; right; apply in_or_app; left; exact Hb]).
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HPX)) 5%nat; intros A1 A2 A3 A4 A5).
    try rewrite alloc_ceiling_eq in A4. unfold PIMG_LO, PIMG_HI in A5.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    destruct RES as [(-> & -> & NDA) | (-> & KS & k & -> & KNZ & NDA & SK)].
    - (* [comment removed for export] *)
      zstep. if_true. apply evt_done.
      assert (CH : cj_chain CJ_ANY m1 (S dch) hd (X ++ (A, 64) :: [] ++ [] ++ [])).
      { eapply cj_lseg_chain; [eapply cj_lseg_mono; [exact SEG| intros; exact I| lia]|].
        eapply cj_chain_one; [exact ANZ| exact NDA| lia| exact I| apply cj_str_null| apply cj_str_null| apply cj_chain_nil]. }
      cbn [app] in CH.
      eapply FAILO; [exact MIDm| | exact CH| unfold dch; lia| exact HNZ| exact FR| exact PB| exact ND| exact FA| exact FRM].
      eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply (perm_new_done (U, 64) (A, 64) [] X LR).
    - (* [comment removed for export] *)
      pose proof (rw_cells_bound usegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
      assert (INS : In (KS, k) LBX) by (eapply Permutation_in; [exact HPX| right; left; reflexivity]).
      pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold node_cells, wz in NDA. unfold PERRNO in ERR. unfold SAVEDO in FR.
      zstep. if_false. zstep. zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
      zstep. zstep. zstep. if_cases Kend; zify_cond Kend.
      + (* [comment removed for export] *)
        apply evt_done.
        eapply (key_done c IHc o off2 hd A KS k pvA X m1 mo1 LBX errv1);
          [exact Hc| exact Ho| lia| exact Hd| exact MIDm| exact HPX| exact HNZ| exact ANZ| exact SEG| exact SK| eqcells NDA| exact FR| exact PB'| eqcells ND| exact FA| exact FRM| reflexivity].
      + pose proof (fin_off0 blen off2 bs LEN ltac:(lia)) as FO.
        zstep. rewrite zb_lxor_ones by lia.
        eapply evt_cut.
        { eapply (ws3 sp gp tp s10 s11 SPB LB LR U P CA blen off depth bs D n lo PVC (Z.to_nat (blen - off2)) off2 (depth + 1) m1 m1);
            [lia| lia| exact PB| exact BY| exact MI| apply munch_refl| apply wmono_refl]. }
        intros ms' nelH_; (nelim nelH_ 10%nat; intros x11' x12' x14' m2 -> PB2 BY2 MI2 MU2 WM2). unfold CSTO. rewrite <- FO in PB2.
        trc FR MU2 WM2. trc ND MU2 WM2. trc NDA MU2 WM2. trc ERR MU2 WM2. trc ST MU2 WM2.
        assert (HL2 : LHEAP HI SPB LBX m2 mo1) by (eapply (lheap_frame_store HI); [exact HL| exact MU2| exact WM2| alia| alia]).
        assert (CJ2 : CJST m2) by (eapply CJST_high_store; [exact CJ| exact MU2| exact WM2| alia]).
        assert (PR2 : ppres LR SP P m m2).
        { eapply ppres_trans; [exact PR|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU2| exact WM2| alia| alia| alia]. }
        assert (BLK : forall A' k', In (A', k') LBX -> disjoint_from [(P + 16, P + 24)] A' k').
        { intros A' k' Hin. cbn. split; [|exact I].
          (nelimp (lh_block_range HI _ _ _ _ _ _ HL Hin) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
        assert (SEG2 : cj_lseg CJ_PRINTABLE m2 dch hd A X).
        { eapply cj_lseg_frame; [exact SEG| exact MU2| exact WM2|]. intros A' k' Hin. apply BLK. apply INX. exact Hin. }
        assert (SK2 : cj_str m2 KS [(KS, k)]).
        { eapply cj_str_frame; [exact SK| exact MU2| exact WM2|]. intros A' k' [E|[]]. inversion E; subst. apply BLK. exact INS. }
        pose proof (skipws_off_range bs off2 ltac:(rewrite LEN; lia)) as OR. rewrite LEN in OR.
        apply evt_done.
        eapply (key_done c IHc o (skipws_off bs off2) hd A KS k pvA X m2 mo1 LBX errv1);
          [exact Hc| exact Ho| lia| exact Hd| | exact HPX| exact HNZ| exact ANZ| exact SEG2| exact SK2| eqcells NDA| exact FR| unfold pbuf_at; exact PB2| eqcells ND| exact FA| exact FRM| reflexivity].
        split; [exact HL2|]. split; [exact BY2|]. split; [exact CJ2|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI2|]. split; [exact ST| exact PR2].
  Qed.

  (* [comment removed for export] *)
  Lemma do_key : forall (c : nat), (forall c', (c' < c)%nat -> OLOOPc c') ->
    forall (o hd A : Z) (pvA : word) (X : list cblock) m2 mo2 LBX2 errv2 Fx fcx
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18' x24 x25 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o < blen -> depth <= 999 ->
      MID m2 mo2 LBX2 errv2 -> Permutation ((A, 64) :: (U, 64) :: X ++ LR) LBX2 ->
      hd <> 0 ->
      cj_lseg CJ_PRINTABLE m2 dch hd A X ->
      rw_cells usegs m2 A (node_cells 0 pvA 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0) ->
      rw_cells usegs m2 (SP + -96) SAVED ->
      pbuf_at m2 P CA blen o (depth + 1) ->
      rw_cells usegs m2 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx -> x18' = Z_to_bv 64 hd ->
      SCPS usegs POST (CST 0x151dc x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 x11 x12 x13 x14 x15 x16 x17
                           x18' (Z_to_bv 64 A) (Z_to_bv 64 58) (Z_to_bv 64 32) (Z_to_bv 64 44) (Z_to_bv 64 0) x24 x25 x28 x29 x30 x31 Fx fcx m2) mo2.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Hd MIDm HPX HNZ SEG NDA FR PB ND FA FRM ->. lits. unfold CSTO.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (rw_cells_bound usegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HPX)) 5%nat; intros A1 A2 A3 A4 A5).
    try rewrite alloc_ceiling_eq in A4. unfold PIMG_LO, PIMG_HI in A5.
    assert (INLR : forall b, In b LR -> In b LBX2) by (intros b Hb; eapply Permutation_in; [exact HPX| right; right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX2) by (intros b Hb; eapply Permutation_in; [exact HPX| right; right; apply in_or_app; left; exact Hb]).
    assert (BLK : forall A' k, In (A', k) LBX2 -> disjoint_from [(P + 16, P + 24)] A' k).
    { intros A' k Hin. cbn. split; [|exact I].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL Hin) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold node_cells, wz in NDA. unfold PERRNO in ERR. unfold SAVEDO in FR.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases Kend; zify_cond Kend.
    { apply evt_done.
      assert (CH : cj_chain CJ_ANY m2 (S dch) hd (X ++ (A, 64) :: [] ++ [] ++ [])).
      { eapply cj_lseg_chain; [eapply cj_lseg_mono; [exact SEG| intros; exact I| lia]|].
        eapply cj_chain_one; [lia| eqcells NDA| lia| exact I| apply cj_str_null| apply cj_str_null| apply cj_chain_nil]. }
      cbn [app] in CH.
      eapply fail_o; [exact PVC| exact MIDm| | exact CH| unfold dch; lia| exact FR| exact PB'| eqcells ND| exact FA| exact FRM].
      eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply (perm_new_done (U, 64) (A, 64) [] X LR). }
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
    (* [comment removed for export] *)
    pose proof (fin_off0 blen (o + 1) bs LEN ltac:(lia)) as FO.
    zstep. rewrite zb_lxor_ones by lia.
    eapply evt_cut.
    { eapply (ws2 sp gp tp s10 s11 SPB LB LR U P CA blen off depth bs D n lo PVC (Z.to_nat (blen - (o + 1))) (o + 1) (depth + 1) m3 m3);
        [lia| lia| unfold pbuf_cells, wz; exact PB| exact BY| exact MI| apply munch_refl| apply wmono_refl]. }
    intros ms' nelH_; (nelim nelH_ 10%nat; intros x10' x11' x14' m4 -> PB4 BY4 MI4 MU4 WM4). unfold CSTO. rewrite <- FO in PB4.
    clear PB BY MI.
    pose proof (munch_trans _ _ _ _ MU MU4) as MU24. pose proof (wmono_trans _ _ _ _ WM WM4) as WM24.
    trc FR MU4 WM4. trc ND MU4 WM4. trc NDA MU4 WM4. trc ERR MU4 WM4. trc ST MU4 WM4.
    assert (HL4 : LHEAP HI SPB LBX2 m4 mo2) by (eapply (lheap_frame_store HI); [exact HL| exact MU24| exact WM24| alia| alia]).
    assert (CJ4 : CJST m4) by (eapply CJST_high_store; [exact CJ| exact MU24| exact WM24| alia]).
    assert (PR4 : ppres LR SP P m m4).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU24| exact WM24| alia| alia| alia]. }
    assert (SEG4 : cj_lseg CJ_PRINTABLE m4 dch hd A X).
    { eapply cj_lseg_frame; [exact SEG| exact MU24| exact WM24|]. intros A' k Hin. apply BLK. apply INX. exact Hin. }
    clear MU WM MU4 WM4 MU24 WM24 HL CJ PR SEG m3.
    pose proof (skipws_off_range bs (o + 1) ltac:(rewrite LEN; lia)) as OR. rewrite LEN in OR.
    set (o1 := skipws_off bs (o + 1)) in *.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    assert (PI : parse_inv HI m4 mo2 SPB LBX2 [] ((U, 64) :: X ++ LR) A P CA blen bs D n lo (SP + -96) errv2).
    { split; [exact HL4|]. split; [exact HPX|]. split; [right; apply in_or_app; right; exact (proj1 HDn)|].
      split; [lia|]. split; [lia|]. split; [exact BY4|]. split; [exact LEN|]. split; [exact BLEN|]. split; [exact CJ4|].
      split; [unfold PERRNO; exact ERR|]. split; [exact MI4|]. split; [exact ST|]. split; [alia|]. lia. }
    apply evt_done. cbv beta.
    eapply scps_bind.
    { pose proof PS as PSS. unfold parse_string_stmt in PSS.
      eapply PSS with (U := A) (P := P) (off := o1) (depth := depth + 1) (nx := 0) (ch := 0) (ty := 0) (vs := 0) (ky := 0); clear PSS; rewrite ?unsigned_lit by lia;
        first [exact PI | unfold pbuf_at; exact PB4 | eqcells NDA | exact TP | reflexivity | alia ]. }
    cbv beta. intros ms5 mo5 PO'.
    (nelim PO' 28%nat; intros t0' t1' t2' a0' a1_ a2_ a3_ a4_ a5_ a6_ a7' t3' t4' t5' t6' m5 r off2 LB5 X2 errv5 -> -> PI5 PR5 PB5 Ho2 RES)
.
    rewrite ?unsigned_lit in PI5, PR5 by lia.
    replace (ret_pc (Z_to_bv 64 0x15234)) with (Z_to_bv 64 0x15234) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (nelim PI5 13%nat; intros HL5 HP5 _ _ _ BY5 _ _ CJ5 ERR5 MI5 ST5 _).
    apply (ppres_rw_cells_stack _ _ _ _ _ _ _ PR5) in FR; [| lia| cbn; lia].
    apply (ppres_rw_cells_block _ _ _ _ _ _ _ U 64 PR5) in ND; [| left; reflexivity| lia| cbn; lia].
    apply (ppres_cj_lseg _ _ _ _ _ _ _ _ _ _ PR5) in SEG4; [| intros b Hb; right; apply in_or_app; left; exact Hb].
    assert (PR6 : ppres LR SP P m m5).
    { eapply ppres_trans; [exact PR4|]. eapply ppres_weaken; [exact PR5| lia| intros b Hb; right; apply in_or_app; right; exact Hb]. }
    unfold wz. eapply (after_key c IHc o o1 hd A pvA X r off2 X2 m5 mo5 LB5 errv5);
      [exact Hc| lia| lia| exact Hd| | exact HP5| exact HNZ| lia| exact SEG4| exact FR| exact PB5| exact Ho2| eqcells ND| exact FA| exact FRM| reflexivity| ].
    - split; [exact HL5|]. split; [exact BY5|]. split; [exact CJ5|]. split; [exact ERR5|]. split; [exact MI5|]. split; [exact ST5| exact PR6].
    - destruct RES as [(-> & -> & NDR)|(-> & KS & k & -> & KNZ & NDR & SK)].
      + left. split; [reflexivity|]. split; [reflexivity| exact NDR].
      + right. split; [reflexivity|]. exists KS, k. split; [reflexivity|]. split; [exact KNZ|]. split; [exact NDR| exact SK].
  Qed.

  (* [comment removed for export] *)
  Lemma loop_body_o : forall (c : nat), (forall c', (c' < c)%nat -> OLOOPc c') -> OLOOPc c.
  Proof.
    intros c IHc. unfold OLOOP. intros until x31. intros Hc Ho Hd MIDm HPX OI FR PB ND FA FRM. lits. unfold CSTO.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; left; exact Hb]).
    assert (INU : In (U, 64) LBX) by (eapply perm_in_head; exact HPX).
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold PERRNO in ERR. unfold SAVEDO in FR.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (ret_pc (Z_to_bv 64 PMALLOC)) with (wz PMALLOC) by (unfold wz, PMALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply scps_bind.
    { pose proof (lh_malloc HI) as LM. unfold malloc_scps_stmt in LM.
      eapply LM with (lo := lo) (n := 64); rewrite ?unsigned_lit by lia;
        first [ exact HL | exact ST | exact ERR | exact MI | exact TP | reflexivity | alia ]. }
    cbv beta. intros ms2 mo2 PO'.
    (nelim PO' 23%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 -> MI2 ST2 ERR2 PR2 RES)
.
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x1518c)) with (Z_to_bv 64 0x1518c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; cbn; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PB; [| left; cbn; lia].
    pose proof PB' as PB2. unfold pbuf_at in PB2. apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PB2; [| left; cbn; lia]. clear PB'.
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in ND; [| right; right; exists U, 64; split; [exact INU| cbn; lia]].
    apply (cj_pres_bytes_at _ _ _ _ _ _ PR2) in BY; [| right; right; exists D, n; split; [apply INLR; apply (proj1 HDn)| lia]].
    apply (CJST_pres _ _ _ _ PR2) in CJ.
    apply (obj_inv_magree _ m1 m2) in OI; [| eapply magree_blocks_of_cj_pres; [exact PR2| exact INX]].
    assert (PR3 : ppres LR SP P m m2) by (eapply ppres_trans; [exact PR| eapply ppres_of_cj_pres; [exact PR2| lia| exact INLR]]).
    clear PR PR2 MI ST HL ERR. unfold PERRNO in ERR2.
    destruct RES as [[-> HL2] | (A & jk & -> & ARNG & ANEW & HL2 & BLK)].
    - (* [comment removed for export] *)
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
      (nelimp (cj_chain_ptr_range _ _ _ _ _ (obj_inv_chain _ _ _ _ _ OI)) 3%nat; intros HR1 _ HR2).
      unfold wz. zstep. if_true. zstep. zstep. if_cases Kh; zify_cond Kh.
      + (* [comment removed for export] *)
        destruct OI as [[_ ->]|(NZ & _)]; [| exfalso; exact (NZ Kh)]. cbn [app] in HPX.
        apply evt_done. eapply ret0_o; [exact PVC| | exact HPX| exact FR| unfold pbuf_at; exact PB2| eqcells ND| exact FA| exact FRM].
        split; [exact HL2|]. split; [exact BY|]. split; [exact CJ|]. split; [unfold PERRNO; exact ERR2|]. split; [exact MI2|]. split; [exact ST2| exact PR3].
      + (* [comment removed for export] *)
        apply evt_done. eapply fail_o; [exact PVC| | exact HPX| eapply cj_chain_any; eapply obj_inv_chain; exact OI| unfold dch; lia| exact FR| unfold pbuf_at; exact PB2| eqcells ND| exact FA| exact FRM].
        split; [exact HL2|]. split; [exact BY|]. split; [exact CJ|]. split; [unfold PERRNO; exact ERR2|]. split; [exact MI2|]. split; [exact ST2| exact PR3].
    - (* [comment removed for export] *)
      (nelimp ARNG 5%nat; intros A1 A2 A3 A4 A5). try rewrite alloc_ceiling_eq in A4. unfold PIMG_LO, PIMG_HI in A5.
      assert (APART : forall A' n', In (A', n') LBX -> A' <> A /\ (A' + n' <= A \/ A + 64 <= A')).
      { intros A' n' Hin. eapply (lheap_perm_apart HI); [exact HL2| apply Permutation_refl| exact Hin]. }
      destruct (APART U 64 INU) as [_ AU]. destruct (APART D n (INLR _ (proj1 HDn))) as [_ AD].
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
      unfold wz. zstep. if_cases Kz; zify_cond Kz; [exfalso; lia|].
      eapply evt_cut; [eapply zero_node_run_o; [exact BLK| exact MI2| exact A2]|].
      intros ms' nelH_; (nelim nelH_ 6%nat; intros m3 -> MU3 WM3 MI3 NDA). unfold CSTO.
      trc FR MU3 WM3. trc PB MU3 WM3. trc ND MU3 WM3. trc ERR2 MU3 WM3. trc BY MU3 WM3. trc ST2 MU3 WM3.
      apply (obj_inv_magree _ m2 m3) in OI.
      2:{ eapply magree_blocks_of_munch; [exact MU3| exact WM3|]. intros A' n' Hin. cbn. split; [|exact I]. destruct (APART A' n' (INX _ Hin)). lia. }
      assert (HL3 : LHEAP HI SPB ((A, 64) :: LBX) m3 mo2) by (eapply (lheap_block_store HI); [exact HL2| left; reflexivity| exact MU3| exact WM3| lia| lia]).
      assert (CJ3 : CJST m3) by (eapply (CJST_block_store HI); [exact HL2| left; reflexivity| exact CJ| exact MU3| exact WM3| lia| lia]).
      assert (PR4 : ppres LR SP P m m3).
      { eapply ppres_trans; [exact PR3|]. eapply (ppres_block_store HI); [exact HL2| apply Permutation_refl| exact INLR| alia| exact MU3| exact WM3| lia| lia]. }
      clear MU3 WM3 MI2 CJ PR3 BLK.
      (nelimp (cj_chain_ptr_range _ _ _ _ _ (obj_inv_chain _ _ _ _ _ OI)) 3%nat; intros HR1 _ HR2).
      zstep. if_cases Kh; zify_cond Kh.
      + (* [comment removed for export] *)
        destruct OI as [[_ ->]|(NZ & _)]; [| exfalso; exact (NZ Kh)]. cbn [app] in HPX.
        apply evt_done. eapply (do_key c IHc o A A (wz 0) [] m3 mo2 ((A, 64) :: LBX) errv2);
          [exact Hc| exact Ho| exact Hd| | apply perm_skip; exact HPX| lia| apply cj_lseg_nil| exact NDA| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact FA| exact FRM| reflexivity].
        split; [exact HL3|]. split; [exact BY|]. split; [exact CJ3|]. split; [unfold PERRNO; exact ERR2|]. split; [exact MI3|]. split; [exact ST2| exact PR4].
      + (* [comment removed for export] *)
        destruct OI as [[E _]|(NZ & NZc & B1 & Bv & Bk & Bc & chc & tyc & vsc & kyc & pvc & p1c & vic & p2c & vdc & -> & SEG & NDC & TYC & SVC & SKC & CHC)]; [exfalso; exact (Kh E)|].
        assert (HPcur : Permutation ((cur, 64) :: (A, 64) :: (B1 ++ Bv ++ Bk ++ Bc) ++ (U, 64) :: LR) ((A, 64) :: LBX)).
        { eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. eapply Permutation_trans; [apply perm_pick_mid| exact HPX]. }
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL3 (perm_in_head _ _ _ HPcur)) 5%nat; intros C1 C2 C3 C4 C5).
        try rewrite alloc_ceiling_eq in C4. unfold PIMG_LO, PIMG_HI in C5.
        assert (CPART : forall A' n', In (A', n') ((A, 64) :: (B1 ++ Bv ++ Bk ++ Bc) ++ (U, 64) :: LR) -> A' <> cur /\ (A' + n' <= cur \/ cur + 64 <= A')).
        { intros A' n' Hin. eapply (lheap_perm_apart HI); [exact HL3| exact HPcur| exact Hin]. }
        destruct (CPART A 64 ltac:(left; reflexivity)) as [_ CA'].
        destruct (CPART U 64 ltac:(right; apply in_or_app; right; left; reflexivity)) as [_ CU].
        destruct (CPART D n ltac:(right; apply in_or_app; right; right; exact (proj1 HDn))) as [_ CD].
        pose proof (rw_cells_bound usegs _ _ _ NDC) as NCB. rewrite node_cells_size in NCB.
        unfold node_cells, wz in NDC. unfold node_cells, wz in NDA.
        zstep. if_cases KC0; zify_cond KC0; [exfalso; lia|].
        zstep. rewrite (align16_land7 cur C2). zstep. if_cases KC1; zify_cond KC1; [killK KC1|]. clear KC1.
        (* [comment removed for export] *)
        pose proof (munch_refl [(cur, cur + 8)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
        zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
        assert (INC : In (cur, 64) ((A, 64) :: LBX)) by (eapply perm_in_head; exact HPcur).
        assert (HL4 : LHEAP HI SPB ((A, 64) :: LBX) m4 mo2) by (eapply (lheap_block_store HI); [exact HL3| exact INC| exact MU| exact WM| lia| lia]).
        assert (CJ4 : CJST m4) by (eapply (CJST_block_store HI); [exact HL3| exact INC| exact CJ3| exact MU| exact WM| lia| lia]).
        assert (PR5 : ppres LR SP P m m4).
        { eapply ppres_trans; [exact PR4|]. eapply (ppres_block_store HI); [exact HL3| exact HPcur| intros b Hb; right; apply in_or_app; right; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
        assert (DJ : forall A' n', In (A', n') (B1 ++ Bv ++ Bk ++ Bc) -> disjoint_from [(cur, cur + 8)] A' n').
        { intros A' n' Hin. cbn. split; [|exact I]. destruct (CPART A' n' ltac:(right; apply in_or_app; left; exact Hin)). lia. }
        assert (SEG4 : cj_lseg CJ_PRINTABLE m4 dch head cur B1).
        { eapply cj_lseg_frame; [exact SEG| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. left. exact Hin. }
        assert (SVC4 : cj_str m4 vsc Bv).
        { eapply cj_str_frame; [exact SVC| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (SKC4 : cj_str m4 kyc Bk).
        { eapply cj_str_frame; [exact SKC| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (CHC4 : cj_chain CJ_PRINTABLE m4 dch chc Bc).
        { eapply cj_chain_frame; [exact CHC| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
        clear MU WM HL3 CJ3 PR4 SEG SVC SKC CHC DJ.
        (* [comment removed for export] *)
        zstep. if_cases KC2; zify_cond KC2; [killK KC2|]. clear KC2.
        pose proof (munch_refl [(A + 8, A + 16)] m4) as MU. pose proof (wmono_refl usegs m4) as WM.
        zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        assert (HL5 : LHEAP HI SPB ((A, 64) :: LBX) m5 mo2) by (eapply (lheap_block_store HI); [exact HL4| left; reflexivity| exact MU| exact WM| lia| lia]).
        assert (CJ5 : CJST m5) by (eapply (CJST_block_store HI); [exact HL4| left; reflexivity| exact CJ4| exact MU| exact WM| lia| lia]).
        assert (PR6 : ppres LR SP P m m5).
        { eapply ppres_trans; [exact PR5|]. eapply (ppres_block_store HI); [exact HL4| apply Permutation_refl| exact INLR| alia| exact MU| exact WM| lia| lia]. }
        assert (DJ : forall A' n', In (A', n') (B1 ++ Bv ++ Bk ++ Bc) -> disjoint_from [(A + 8, A + 16)] A' n').
        { intros A' n' Hin. cbn. split; [|exact I].
          destruct (APART A' n') as [_ ?]; [| lia]. apply INX. apply in_app_or in Hin. apply in_or_app. destruct Hin as [Hin|Hin]; [left; exact Hin| right; right; exact Hin]. }
        assert (SEG5 : cj_lseg CJ_PRINTABLE m5 dch head cur B1).
        { eapply cj_lseg_frame; [exact SEG4| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. left. exact Hin. }
        assert (SVC5 : cj_str m5 vsc Bv).
        { eapply cj_str_frame; [exact SVC4| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (SKC5 : cj_str m5 kyc Bk).
        { eapply cj_str_frame; [exact SKC4| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (CHC5 : cj_chain CJ_PRINTABLE m5 dch chc Bc).
        { eapply cj_chain_frame; [exact CHC4| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
        clear MU WM HL4 CJ4 PR5 SEG4 SVC4 SKC4 CHC4 DJ.
        zstep. apply evt_done.
        eapply (do_key c IHc o head A (Z_to_bv 64 cur) (B1 ++ (cur, 64) :: Bv ++ Bk ++ Bc) m5 mo2 ((A, 64) :: LBX) errv2);
          [exact Hc| exact Ho| exact Hd| | apply perm_skip; exact HPX| exact NZ| | eqcells NDA| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact FA| exact FRM| reflexivity].
        * split; [exact HL5|]. split; [exact BY|]. split; [exact CJ5|]. split; [unfold PERRNO; exact ERR2|]. split; [exact MI3|]. split; [exact ST2| exact PR6].
        * eapply cj_lseg_snoc; [exact SEG5| exact NZc| eqcells NDC| apply CJ_PRINTABLE_range; exact TYC| exact TYC| exact SVC5| exact SKC5| exact CHC5].
  Qed.

  Theorem oloop : forall c, OLOOPc c.
  Proof. induction c as [c IH] using lt_wf_ind. apply loop_body_o. exact IH. Qed.
End POL.


End CeilWrap.
End CJ_pobject_L.

(* [comment removed for export] *)
Module CJ_pvalue_L.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_skipws CJ_delete OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_utraps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_lemmas CJ_pvalue_lemmas CJ_pvalue_ctx CJ_pvalue_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.

Section PVL.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (SPB : Z) (LB LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure sp tp SPB LB LR U P CA blen off depth bs D n lo.
  Variable nfuel : nat.
  Hypothesis FUEL : blen - off <= Z.of_nat nfuel.
  Hypothesis PVREC : forall nf, (nf < nfuel)%nat -> parse_value_at HI nf.

  Notation SP := (bv_unsigned sp).
  Notation CST := (CSTV sp gp tp s7 s8 s9 s10 s11).
  Notation POST := (POSTV HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).
  Notation MID := (MIDV HI sp m SPB LR P CA bs lo).
  Notation SAVED := (SAVEDV ra s0 s1 s2 s3 s4 s5 s6).
  Notation dch := (dch depth).

  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac dj := cbn [disjoint_from cells_size csize Nat.add length];
             repeat match goal with H : length ?l = _ |- context [length ?l] => rewrite H end;
             first [lia | split; [lia| exact I]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply u8arr_transport in H; [| exact MU| exact WM| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].
  Ltac lits := (nelimp (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC) 14%nat; intros HPU HDn LEN BLEN CEIL LO PP OFF DEP TP URNG DRNG UD SPR).
  Ltac alia := rewrite ?alloc_ceiling_eq; unfold DELETE_STACK, PARSE_STACK, PARSE_STRING_STACK; unfold RMALLOC_STACK; lia.

  (* [comment removed for export] *)
  Lemma zero_node_run : forall x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 Fx fcx mm (A : Z) (junk : list byte),
    rw_cells usegs mm A [CB 64 junk] -> mem_inv usegs mm ->
    evt usegs (fun ms' => exists mm',
                 ms' = CST 0x13ffc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 A) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 A) x19 x20 (Z_to_bv 64 A) x22 x28 x29 x30 x31 Fx fcx mm'
                 /\ munch [(A, A + 64)] mm mm' /\ wmono usegs mm mm' /\ mem_inv usegs mm'
                 /\ rw_cells usegs mm' A (node_cells 0 (wz 0) 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0))
        (CST 0x13fd4 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 A) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 Fx fcx mm).
  Proof using PVC nfuel.
    intros until junk. intros BLK MI. lits. unfold CSTV.
    pose proof (rw_cells_bound usegs _ _ _ BLK) as AB. cbn [cells_size csize Nat.add] in AB.
    pose proof (munch_refl [(A, A + 64)] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
    zstep. do 8 (zstep; fix_lit_store). zstep.
    apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    apply zero_node_cells. exact BLK.
  Qed.

  Notation ALOOPc := (ALOOP HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).

  (* [comment removed for export] *)
  Lemma fail_13d24 : forall (junk : list byte) (off1 depth1 head : Z) (X : list cblock) (dd : nat) m1 mo1 LBX errv1 Fx fcx
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31,
    MID m1 mo1 LBX errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_ANY m1 dd head X -> Z.of_nat dd <= 1000 - depth ->
    rw_cells usegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    SCPS usegs POST (CST 0x140b8 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 x11 x12 x13 x14 x15 x16 x17
                         x18 x19 x20 (Z_to_bv 64 head) x22 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros MIDm HPX CH Hdd FR PB ND FA FRM. pose proof MIDm as (HL & _). unfold CSTV.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. zstep. apply evt_done. eapply arr_fail_delete; [exact PVC| exact nfuel| exact MIDm| exact HPX| exact CH| exact Hdd| exact FR| exact PB| exact ND| exact FA| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Lemma close_ok : forall (junk : list byte) (o3 hd A : Z) (Xall : list cblock) m1 mo1 LBX errv1 Fx fcx
      x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x20 x22 x28 x29 x30 x31,
    MID m1 mo1 LBX errv1 -> Permutation ((U, 64) :: Xall ++ LR) LBX ->
    hd <> 0 -> cj_chain CJ_PRINTABLE m1 (S dch) hd Xall -> depth <= 999 ->
    rw_cells usegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
    pbuf_at m1 P CA blen o3 (depth + 1) ->
    rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off <= o3 < blen -> Fagree F Fx -> frm0 fcx ->
    SCPS usegs POST (CST 0x14094 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 (Z_to_bv 64 o3) x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 A) x19 x20 (Z_to_bv 64 hd) x22 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros MIDm HPX HNZ CH Hd FR PB ND Ho FA FRM. lits. unfold CSTV.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b Xall -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; left; exact Hb]).
    unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold PERRNO in ERR. unfold SAVEDV in FR.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    pose proof (cj_chain_head_block _ _ _ _ _ CH HNZ) as INH0.
    pose proof (lh_block_range HI _ _ _ _ _ _ HL (INX _ INH0)) as (HD1 & HD16 & _ & HD4 & _). try rewrite alloc_ceiling_eq in HD4.
    pose proof (munch_refl [(P + 24, P + 32)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep. zstep. zstep. rewrite (align16_land7 hd HD16). zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    zstep. if_cases KA1; zify_cond KA1; [exfalso; exact (KA1 eq_refl)|].
    assert (HL2 : LHEAP HI SPB LBX m2 mo1) by (eapply (lheap_frame_store HI); [exact HL| exact MU| exact WM| alia| alia]).
    assert (CJ2 : CJST m2) by (eapply CJST_high_store; [exact CJ| exact MU| exact WM| alia]).
    assert (PR2 : ppres LR SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU| exact WM| alia| alia| alia]. }
    assert (CH2 : cj_chain CJ_PRINTABLE m2 (S dch) hd Xall).
    { eapply cj_chain_frame; [exact CH| exact MU| exact WM|].
      intros A' k Hin. cbn. split; [|exact I].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL (INX _ Hin)) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
    clear MU WM HL CJ PR CH.
    (* [comment removed for export] *)
    (nelim (cj_chain_cons_inv _ _ _ _ _ CH2 HNZ) 24%nat; intros d0 nxh pvh chh tyh p1h vsh vih p2h vdh kyh Bvh Bkh Bch Bnh Ed NDH TYH HTh SVh SKh CHCh CHNh EX)
.
    rewrite EX in HPX, INX.
    assert (HPh : Permutation ((hd, 64) :: (Bvh ++ Bkh ++ Bch ++ Bnh) ++ (U, 64) :: LR) LBX).
    { eapply Permutation_trans; [apply perm_pick_head| exact HPX]. }
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HPh)) 5%nat; intros H1 H2 H3 H4 H5).
    try rewrite alloc_ceiling_eq in H4. unfold PIMG_LO, PIMG_HI in H5.
    destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL2 HPh U 64 ltac:(apply in_or_app; right; left; reflexivity)) as [_ HU].
    destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL2 HPh D n ltac:(apply in_or_app; right; right; exact (proj1 HDn))) as [_ HD].
    unfold node_cells, wz in NDH.
    pose proof (munch_refl [(hd + 8, hd + 16)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (INH : In (hd, 64) LBX) by (eapply perm_in_head; exact HPh).
    assert (HL3 : LHEAP HI SPB LBX m3 mo1) by (eapply (lheap_block_store HI); [exact HL2| exact INH| exact MU| exact WM| lia| lia]).
    assert (CJ3 : CJST m3) by (eapply (CJST_block_store HI); [exact HL2| exact INH| exact CJ2| exact MU| exact WM| lia| lia]).
    assert (PR3 : ppres LR SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply (ppres_block_store HI); [exact HL2| exact HPh| intros b Hb; apply in_or_app; right; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
    assert (CH3 : cj_chain CJ_PRINTABLE m3 (S dch) hd Xall).
    { rewrite EX, Ed. eapply (cj_chain_relink HI); [exact HL2| exact HPh| exact HNZ| exact TYH| exact HTh| exact SVh| exact SKh| exact CHCh| exact CHNh| exact MU| exact WM| eqcells NDH]. }
    clear MU WM HL2 CJ2 PR2 CH2 SVh SKh CHCh CHNh. rewrite <- EX in HPX.
    zstep. rewrite (align16_land7 U) by lia. zstep. if_cases KA2; zify_cond KA2; [| exfalso; apply KA2; reflexivity].
    apply evt_done.
    eapply arr_success; [exact PVC| exact nfuel| | exact HPX| exact CH3| exact Hd| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact Ho| exact FA| exact FRM].
    split; [exact HL3|]. split; [exact BY|]. split; [exact CJ3|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST| exact PR3].
  Qed.

  (* [comment removed for export] *)
  Lemma after_ws2 : forall (c : nat), (forall c', (c' < c)%nat -> ALOOPc c') ->
    forall (junk : list byte) (o o3 hd A : Z) (pvA : word) (chA tyA vsA : Z) (viA vdA : word) (X Bv Bc : list cblock) m1 mo1 LBX errv1 Fx fcx
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o -> o < o3 <= blen -> depth <= 999 ->
      MID m1 mo1 LBX errv1 -> Permutation ((U, 64) :: (X ++ (A, 64) :: Bv ++ Bc) ++ LR) LBX ->
      hd <> 0 -> A <> 0 -> cj_lseg CJ_PRINTABLE m1 dch hd A X ->
      rw_cells usegs m1 A (node_cells 0 pvA chA tyA (wz 0) vsA viA (wz 0) vdA 0) ->
      CJ_PRINTABLE tyA -> cj_str m1 vsA Bv -> cj_chain CJ_PRINTABLE m1 dch chA Bc ->
      rw_cells usegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
      pbuf_at m1 P CA blen o3 (depth + 1) ->
      rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      SCPS usegs POST (CST 0x1404c x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 x11 x12 x13 x14 x15 x16 x17
                           (Z_to_bv 64 A) x19 (Z_to_bv 64 44) (Z_to_bv 64 hd) x22 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Ho3 Hd MIDm HPX HNZ ANZ SEG NDA HTA SVA CHA FR PB ND FA FRM. lits. unfold CSTV.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    (* [comment removed for export] *)
    assert (CH : cj_chain CJ_PRINTABLE m1 (S dch) hd (X ++ (A, 64) :: Bv ++ [] ++ Bc)).
    { eapply cj_lseg_chain; [exact SEG|]. eapply cj_chain_one; [exact ANZ| exact NDA| apply CJ_PRINTABLE_range; exact HTA| exact HTA| exact SVA| apply cj_str_null| exact CHA]. }
    cbn [app] in CH.
    assert (FAIL : forall x10' x12' x13' x14' x19' x22',
      SCPS usegs POST (CST 0x140b8 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10' (Z_to_bv 64 o3) x12' x13' x14' x15 x16 x17
                           (Z_to_bv 64 A) x19' (Z_to_bv 64 44) (Z_to_bv 64 hd) x22' x28 x29 x30 x31 Fx fcx m1) mo1).
    { intros. eapply fail_13d24; [exact MIDm| exact HPX| eapply cj_chain_any; exact CH| unfold dch; lia| exact FR| exact PB| exact ND| exact FA| exact FRM]. }
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. zstep. zstep. if_cases Kend; zify_cond Kend.
    { (* [comment removed for export] *) unfold CSTV in FAIL. apply evt_done. apply FAIL. }
    zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases KW; zify_cond KW; [exfalso; lia|].
    zstep. zstep. zstep. zstep. if_cases KN; zify_cond KN.
    { exfalso. revert KN. replace (0 <? CA) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (CA + o3 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). vm_compute. discriminate. }
    zstep. if_cases KZ; zify_cond KZ; [exfalso; lia|].
    (nelim (text_read m1 CA bs o3 (Z_to_bv 64 (CA + o3)) BY ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b Hb RD Hat).
    pose proof (byte_range b) as Rb.
    zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc.
    { (* [comment removed for export] *)
      apply evt_done. pose proof (IHc (Z.to_nat (blen - o3)) ltac:(lia)) as IH. unfold ALOOP, CSTV in IH.
      eapply (IH o3 hd A (X ++ (A, 64) :: Bv ++ Bc) m1 mo1 LBX errv1); [lia| lia| exact Hd| exact MIDm| exact HPX| | exact FR| exact PB'| exact ND| exact FA| exact FRM].
      right. split; [exact HNZ|]. split; [exact ANZ|]. exists X, Bv, Bc, chA, tyA, vsA, pvA, (wz 0), viA, (wz 0), vdA.
      split; [reflexivity|]. split; [exact SEG|]. split; [exact NDA|]. split; [exact HTA|]. split; [exact SVA| exact CHA]. }
    zstep. if_cases KZ2; zify_cond KZ2; [exfalso; lia|].
    zstep. zstep. if_cases K93; zify_cond K93.
    { (* [comment removed for export] *) unfold CSTV in FAIL. apply evt_done. apply FAIL. }
    (* [comment removed for export] *)
    apply evt_done. eapply close_ok; [exact MIDm| exact HPX| exact HNZ| exact CH| exact Hd| exact FR| exact PB'| exact ND| lia| exact FA| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Lemma after_call : forall (c : nat), (forall c', (c' < c)%nat -> ALOOPc c') ->
    forall (junk : list byte) (o o1 hd A : Z) (pvA : word) (X : list cblock) (r off5 depth5 : Z) (X5 : list cblock) m1 mo1 LBX errv1 Fx fcx
           x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o -> o < o1 -> depth <= 999 ->
      MID m1 mo1 LBX errv1 -> Permutation ((A, 64) :: X5 ++ (U, 64) :: X ++ LR) LBX ->
      hd <> 0 -> A <> 0 -> cj_lseg CJ_PRINTABLE m1 dch hd A X ->
      rw_cells usegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
      pbuf_at m1 P CA blen off5 depth5 ->
      rw_cells usegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      ( (r = 0 /\ X5 = [] /\ rw_cells usegs m1 A (node_cells 0 pvA 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0))
        \/ (r = 1 /\ depth5 = depth + 1 /\ o1 <= off5 <= blen
             /\ exists (ch ty' vs : Z) (vi' vd' : word) (dc : nat) (Bv Bc : list cblock),
                  X5 = Bv ++ Bc
                  /\ rw_cells usegs m1 A (node_cells 0 pvA ch ty' (wz 0) vs vi' (wz 0) vd' 0)
                  /\ CJ_PRINTABLE ty' /\ cj_str m1 vs Bv /\ cj_chain CJ_PRINTABLE m1 dc ch Bc
                  /\ Z.of_nat dc + (depth + 1) <= 1000) ) ->
      SCPS usegs POST (CST 0x14040 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                           (Z_to_bv 64 A) x19 (Z_to_bv 64 44) (Z_to_bv 64 hd) x22 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Ho1 Hd MIDm HPX HNZ ANZ SEG FR PB ND FA FRM RES. lits. unfold CSTV.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; right; apply in_or_app; left; exact Hb]).
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HPX)) 5%nat; intros A1 A2 A3 A4 A5).
    try rewrite alloc_ceiling_eq in A4. unfold PIMG_LO, PIMG_HI in A5.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    destruct RES as [(-> & -> & NDA) | (-> & -> & Ho5 & chA & tyA & vsA & viA & vdA & dc & Bv & Bc & -> & NDA & HTA & SVA & CHA & Hdc)].
    - (* [comment removed for export] *)
      zstep. if_true. apply evt_done.
      assert (CH : cj_chain CJ_ANY m1 (S dch) hd (X ++ (A, 64) :: [] ++ [] ++ [])).
      { eapply cj_lseg_chain; [eapply cj_lseg_mono; [exact SEG| intros; exact I| lia]|].
        eapply cj_chain_one; [exact ANZ| exact NDA| lia| exact I| apply cj_str_null| apply cj_str_null| apply cj_chain_nil]. }
      cbn [app] in CH.
      eapply fail_13d24; [exact MIDm| | exact CH| unfold dch; lia| exact FR| exact PB| exact ND| exact FA| exact FRM].
      eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply (perm_new_done (U, 64) (A, 64) [] X LR).
    - (* [comment removed for export] *)
      pose proof (rw_cells_bound usegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
      assert (HPX' : Permutation ((U, 64) :: (X ++ (A, 64) :: Bv ++ Bc) ++ LR) LBX).
      { eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply perm_new_done. }
      unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold node_cells, wz in NDA. unfold PERRNO in ERR. unfold SAVEDV in FR.
      zstep. if_false. zstep. zstep.
      eapply evt_cut.
      { eapply skipws_spec with (P := P) (content := CA) (len := blen) (offset := off5) (depth := depth + 1) (bs := bs);
          [unfold pbuf_at, pbuf_cells; exact PB| reflexivity| lia| lia| lia| exact BY| exact LEN| lia| lia| exact MI]. }
      intros ms' PO. (nelim PO 13%nat; intros a1' a2' a3' a4' a5' a6' m4 -> MU4 WM4 MI4 PB4 BY4).
      replace (ret_pc (Z_to_bv 64 0x1404c)) with (Z_to_bv 64 0x1404c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      trc FR MU4 WM4. trc ND MU4 WM4. trc NDA MU4 WM4. trc ERR MU4 WM4. trc ST MU4 WM4. clear PB BY MI.
      assert (HL4 : LHEAP HI SPB LBX m4 mo1) by (eapply (lheap_frame_store HI); [exact HL| exact MU4| exact WM4| alia| alia]).
      assert (CJ4 : CJST m4) by (eapply CJST_high_store; [exact CJ| exact MU4| exact WM4| alia]).
      assert (PR4 : ppres LR SP P m m4).
      { eapply ppres_trans; [exact PR|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU4| exact WM4| alia| alia| alia]. }
      assert (BLK : forall A' k, In (A', k) LBX -> disjoint_from [(P + 16, P + 24)] A' k).
      { intros A' k Hin. cbn. split; [|exact I].
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL Hin) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
      assert (SEG4 : cj_lseg CJ_PRINTABLE m4 dch hd A X).
      { eapply cj_lseg_frame; [exact SEG| exact MU4| exact WM4|]. intros A' k Hin. apply BLK. apply INX. exact Hin. }
      assert (SVA4 : cj_str m4 vsA Bv).
      { eapply cj_str_frame; [exact SVA| exact MU4| exact WM4|]. intros A' k Hin. apply BLK.
        eapply Permutation_in; [exact HPX|]. right. apply in_or_app. left. apply in_or_app. left. exact Hin. }
      assert (CHA4 : cj_chain CJ_PRINTABLE m4 dch chA Bc).
      { eapply cj_chain_frame; [eapply cj_chain_mono_d; [exact CHA| unfold dch; lia]| exact MU4| exact WM4|]. intros A' k Hin. apply BLK.
        eapply Permutation_in; [exact HPX|]. right. apply in_or_app. left. apply in_or_app. right. exact Hin. }
      clear MU4 WM4 HL CJ PR SEG SVA CHA.
      assert (O3 : off5 <= skipws_off bs off5 <= blen).
      { destruct (Z.eq_dec off5 blen) as [E|NE].
        - rewrite skipws_off_noop by lia. lia.
        - pose proof (skipws_off_range bs off5) as OR. rewrite LEN in OR. lia. }
      apply evt_done.
      eapply (after_ws2 c IHc _ o (skipws_off bs off5) hd A pvA chA tyA vsA viA vdA X Bv Bc m4 mo1 LBX errv1);
        [exact Hc| exact Ho| lia| exact Hd| | exact HPX'| exact HNZ| exact ANZ| exact SEG4| eqcells NDA| exact HTA| exact SVA4| exact CHA4| exact FR| exact PB4| eqcells ND| exact FA| exact FRM].
      split; [exact HL4|]. split; [exact BY4|]. split; [exact CJ4|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI4|]. split; [exact ST| exact PR4].
  Qed.

  (* [comment removed for export] *)
  Lemma do_call : forall (c : nat), (forall c', (c' < c)%nat -> ALOOPc c') ->
    forall (junk : list byte) (o hd A : Z) (pvA : word) (X : list cblock) m2 mo2 LBX2 errv2 Fx fcx
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o < blen -> depth <= 999 ->
      MID m2 mo2 LBX2 errv2 -> Permutation ((A, 64) :: (U, 64) :: X ++ LR) LBX2 ->
      hd <> 0 ->
      cj_lseg CJ_PRINTABLE m2 dch hd A X ->
      rw_cells usegs m2 A (node_cells 0 pvA 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0) ->
      rw_cells usegs m2 (SP + -144) (CB 80 junk :: SAVED) ->
      pbuf_at m2 P CA blen o (depth + 1) ->
      rw_cells usegs m2 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      SCPS usegs POST (CST 0x14020 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 x11 x12 x13 x14 x15 x16 x17
                           (Z_to_bv 64 A) x19 (Z_to_bv 64 44) (Z_to_bv 64 hd) x22 x28 x29 x30 x31 Fx fcx m2) mo2.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Hd MIDm HPX HNZ SEG NDA FR PB ND FA FRM. lits. unfold CSTV.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (rw_cells_bound usegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HPX)) 5%nat; intros A1 A2 A3 A4 A5).
    try rewrite alloc_ceiling_eq in A4. unfold PIMG_LO, PIMG_HI in A5.
    unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold node_cells, wz in NDA. unfold PERRNO in ERR. unfold SAVEDV in FR.
    assert (INLR : forall b, In b LR -> In b LBX2) by (intros b Hb; eapply Permutation_in; [exact HPX| right; right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX2) by (intros b Hb; eapply Permutation_in; [exact HPX| right; right; apply in_or_app; left; exact Hb]).
    assert (BLK : forall A' k, In (A', k) LBX2 -> disjoint_from [(P + 16, P + 24)] A' k).
    { intros A' k Hin. cbn. split; [|exact I].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL Hin) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    (* [comment removed for export] *)
    zstep. zstep.
    eapply evt_cut.
    { eapply skipws_spec with (P := P) (content := CA) (len := blen) (offset := o + 1) (depth := depth + 1) (bs := bs);
        [unfold pbuf_at, pbuf_cells; exact PB| reflexivity| lia| lia| lia| exact BY| exact LEN| lia| lia| exact MI]. }
    intros ms' PO. (nelim PO 13%nat; intros a1' a2' a3' a4' a5' a6' m4 -> MU4 WM4 MI4 PB4 BY4).
    replace (ret_pc (Z_to_bv 64 0x14034)) with (Z_to_bv 64 0x14034) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    trc FR MU4 WM4. trc ND MU4 WM4. trc NDA MU4 WM4. trc ERR MU4 WM4. trc ST MU4 WM4. clear PB BY MI.
    apply (munch_trans _ _ _ _ MU) in MU4. apply (wmono_trans _ _ _ _ WM) in WM4. clear MU WM m3.
    assert (HL4 : LHEAP HI SPB LBX2 m4 mo2) by (eapply (lheap_frame_store HI); [exact HL| exact MU4| exact WM4| alia| alia]).
    assert (CJ4 : CJST m4) by (eapply CJST_high_store; [exact CJ| exact MU4| exact WM4| alia]).
    assert (PR4 : ppres LR SP P m m4).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_pbuf_store HI); [exact HL| exact INLR| exact MU4| exact WM4| alia| alia| alia]. }
    assert (SEG4 : cj_lseg CJ_PRINTABLE m4 dch hd A X).
    { eapply cj_lseg_frame; [exact SEG| exact MU4| exact WM4|]. intros A' k Hin. apply BLK. apply INX. exact Hin. }
    clear MU4 WM4 HL CJ PR SEG.
    assert (O1 : o + 1 <= skipws_off bs (o + 1) <= blen).
    { destruct (Z.eq_dec (o + 1) blen) as [E|NE].
      - rewrite skipws_off_noop by lia. lia.
      - pose proof (skipws_off_range bs (o + 1)) as OR. rewrite LEN in OR. lia. }
    set (o1 := skipws_off bs (o + 1)) in *.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    assert (PI : parse_inv HI m4 mo2 SPB LBX2 [] ((U, 64) :: X ++ LR) A P CA blen bs D n lo (SP + -144) errv2).
    { split; [exact HL4|]. split; [exact HPX|]. split; [right; apply in_or_app; right; exact (proj1 HDn)|].
      split; [lia|]. split; [lia|]. split; [exact BY4|]. split; [exact LEN|]. split; [exact BLEN|]. split; [exact CJ4|].
      split; [unfold PERRNO; exact ERR|]. split; [exact MI4|]. split; [exact ST|]. split; [alia|]. lia. }
    apply evt_done. cbv beta.
    eapply scps_bind.
    { pose proof (PVREC (Z.to_nat (blen - o1)) ltac:(lia)) as PVS. unfold parse_value_at in PVS.
      eapply PVS with (U := A) (P := P) (off := o1) (depth := depth + 1) (nx := 0) (ty := 0) (ky := 0); clear PVS; rewrite ?unsigned_lit by lia;
        first [exact PI | exact PB4 | eqcells NDA | exact FRM | exact TP | reflexivity | alia ]. }
    cbv beta. intros ms5 mo5 PO.
    (nelim PO 32%nat; intros t0' t1' t2' a0' a1_ a2_ a3_ a4_ a5_ a6_ a7' t3' t4' t5' t6' F5 fc5 m5 r off5 depth5 LB5 X5 errv5 -> -> FA5 FRM5 PI5 PR5 PB5 RES)
.
    rewrite ?unsigned_lit in PI5, PR5 by lia.
    replace (ret_pc (Z_to_bv 64 0x14040)) with (Z_to_bv 64 0x14040) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (nelim PI5 13%nat; intros HL5 HP5 _ _ _ BY5 _ _ CJ5 ERR5 MI5 ST5 _).
    (* [comment removed for export] *)
    apply (ppres_rw_cells_stack _ _ _ _ _ _ _ PR5) in FR; [| lia| cbn; lia].
    apply (ppres_rw_cells_block _ _ _ _ _ _ _ U 64 PR5) in ND; [| left; reflexivity| lia| cbn; lia].
    apply (ppres_cj_lseg _ _ _ _ _ _ _ _ _ _ PR5) in SEG4; [| intros b Hb; right; apply in_or_app; left; exact Hb].
    assert (PR6 : ppres LR SP P m m5).
    { eapply ppres_trans; [exact PR4|]. eapply ppres_weaken; [exact PR5| lia| intros b Hb; right; apply in_or_app; right; exact Hb]. }
    unfold wz. eapply (after_call c IHc _ o o1 hd A pvA X r off5 depth5 X5 m5 mo5 LB5 errv5);
      [exact Hc| lia| lia| exact Hd| | exact HP5| exact HNZ| lia| exact SEG4| exact FR| exact PB5| eqcells ND| eapply Fagree_trans; [exact FA| exact FA5]| exact FRM5| exact RES].
    split; [exact HL5|]. split; [exact BY5|]. split; [exact CJ5|]. split; [exact ERR5|]. split; [exact MI5|]. split; [exact ST5| exact PR6].
  Qed.

  (* [comment removed for export] *)
  Lemma loop_body : forall (c : nat), (forall c', (c' < c)%nat -> ALOOPc c') -> ALOOPc c.
  Proof.
    intros c IHc. unfold ALOOP. intros until x31. intros Hc Ho Hd MIDm HPX AI FR PB ND FA FRM. lits. unfold CSTV.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; left; exact Hb]).
    assert (INU : In (U, 64) LBX) by (eapply perm_in_head; exact HPX).
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold PERRNO in ERR. unfold SAVEDV in FR.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (ret_pc (Z_to_bv 64 PMALLOC)) with (wz PMALLOC) by (unfold wz, PMALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply scps_bind.
    { pose proof (lh_malloc HI) as LM. unfold malloc_scps_stmt in LM.
      eapply LM with (lo := lo) (n := 64); rewrite ?unsigned_lit by lia;
        first [ exact HL | exact ST | exact ERR | exact MI | exact TP | reflexivity | alia ]. }
    cbv beta. intros ms2 mo2 PO.
    (nelim PO 23%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 -> MI2 ST2 ERR2 PR2 RES)
.
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x13fd0)) with (Z_to_bv 64 0x13fd0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PB; [| left; cbn; lia].
    pose proof PB' as PB2. unfold pbuf_at in PB2. apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PB2; [| left; cbn; lia]. clear PB'.
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in ND; [| right; right; exists U, 64; split; [exact INU| cbn; lia]].
    apply (cj_pres_bytes_at _ _ _ _ _ _ PR2) in BY; [| right; right; exists D, n; split; [apply INLR; apply (proj1 HDn)| lia]].
    apply (CJST_pres _ _ _ _ PR2) in CJ.
    apply (arr_inv_magree _ nfuel m1 m2) in AI; [| eapply magree_blocks_of_cj_pres; [exact PR2| exact INX]].
    assert (PR3 : ppres LR SP P m m2) by (eapply ppres_trans; [exact PR| eapply ppres_of_cj_pres; [exact PR2| lia| exact INLR]]).
    clear PR PR2 MI ST HL ERR. unfold PERRNO in ERR2.
    destruct RES as [[-> HL2] | (A & jk & -> & ARNG & ANEW & HL2 & BLK)].
    - (* [comment removed for export] *)
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
      (nelimp (cj_chain_ptr_range _ _ _ _ _ (arr_inv_chain _ _ _ _ _ AI)) 3%nat; intros HR1 _ HR2).
      unfold wz. zstep. if_true. zstep. if_cases Kh; zify_cond Kh.
      + (* [comment removed for export] *)
        destruct AI as [[_ ->]|(NZ & _)]; [| exfalso; exact (NZ Kh)]. cbn [app] in HPX.
        apply evt_done. eapply ret0_tail; [exact PVC| | exact HPX| exact FR| unfold pbuf_at; exact PB2| eqcells ND| exact FA| exact FRM].
        split; [exact HL2|]. split; [exact BY|]. split; [exact CJ|]. split; [unfold PERRNO; exact ERR2|]. split; [exact MI2|]. split; [exact ST2| exact PR3].
      + (* [comment removed for export] *)
        apply evt_done. eapply arr_fail_delete; [exact PVC| exact nfuel| | exact HPX| eapply cj_chain_any; eapply arr_inv_chain; exact AI| unfold dch; lia| exact FR| unfold pbuf_at; exact PB2| eqcells ND| exact FA| exact FRM].
        split; [exact HL2|]. split; [exact BY|]. split; [exact CJ|]. split; [unfold PERRNO; exact ERR2|]. split; [exact MI2|]. split; [exact ST2| exact PR3].
    - (* [comment removed for export] *)
      (nelimp ARNG 5%nat; intros A1 A2 A3 A4 A5). try rewrite alloc_ceiling_eq in A4. unfold PIMG_LO, PIMG_HI in A5.
      assert (APART : forall A' n', In (A', n') LBX -> A' <> A /\ (A' + n' <= A \/ A + 64 <= A')).
      { intros A' n' Hin. eapply (lheap_perm_apart HI); [exact HL2| apply Permutation_refl| exact Hin]. }
      destruct (APART U 64 INU) as [_ AU]. destruct (APART D n (INLR _ (proj1 HDn))) as [_ AD].
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
      unfold wz. zstep. if_cases Kz; zify_cond Kz; [exfalso; lia|].
      eapply evt_cut; [eapply zero_node_run; [exact BLK| exact MI2]|].
      intros ms' nelH_; (nelim nelH_ 6%nat; intros m3 -> MU3 WM3 MI3 NDA). unfold CSTV.
      trc FR MU3 WM3. trc PB MU3 WM3. trc ND MU3 WM3. trc ERR2 MU3 WM3. trc BY MU3 WM3. trc ST2 MU3 WM3.
      apply (arr_inv_magree _ nfuel m2 m3) in AI.
      2:{ eapply magree_blocks_of_munch; [exact MU3| exact WM3|]. intros A' n' Hin. cbn. split; [|exact I]. destruct (APART A' n' (INX _ Hin)). lia. }
      assert (HL3 : LHEAP HI SPB ((A, 64) :: LBX) m3 mo2) by (eapply (lheap_block_store HI); [exact HL2| left; reflexivity| exact MU3| exact WM3| lia| lia]).
      assert (CJ3 : CJST m3) by (eapply (CJST_block_store HI); [exact HL2| left; reflexivity| exact CJ| exact MU3| exact WM3| lia| lia]).
      assert (PR4 : ppres LR SP P m m3).
      { eapply ppres_trans; [exact PR3|]. eapply (ppres_block_store HI); [exact HL2| apply Permutation_refl| exact INLR| alia| exact MU3| exact WM3| lia| lia]. }
      clear MU3 WM3 MI2 CJ PR3 BLK.
      (nelimp (cj_chain_ptr_range _ _ _ _ _ (arr_inv_chain _ _ _ _ _ AI)) 3%nat; intros HR1 _ HR2).
      zstep. if_cases Kh; zify_cond Kh.
      + (* [comment removed for export] *)
        destruct AI as [[_ ->]|(NZ & _)]; [| exfalso; exact (NZ Kh)]. cbn [app] in HPX.
        apply evt_done. eapply (do_call c IHc _ o A A (wz 0) [] m3 mo2 ((A, 64) :: LBX) errv2);
          [exact Hc| exact Ho| exact Hd| | apply perm_skip; exact HPX| lia| apply cj_lseg_nil| exact NDA| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact FA| exact FRM].
        split; [exact HL3|]. split; [exact BY|]. split; [exact CJ3|]. split; [unfold PERRNO; exact ERR2|]. split; [exact MI3|]. split; [exact ST2| exact PR4].
      + (* [comment removed for export] *)
        destruct AI as [[E _]|(NZ & NZc & B1 & Bv & Bc & chc & tyc & vsc & pvc & p1c & vic & p2c & vdc & -> & SEG & NDC & TYC & SVC & CHC)]; [exfalso; exact (Kh E)|].
        assert (HPcur : Permutation ((cur, 64) :: (A, 64) :: (B1 ++ Bv ++ Bc) ++ (U, 64) :: LR) ((A, 64) :: LBX)).
        { eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. eapply Permutation_trans; [apply perm_pick_mid| exact HPX]. }
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL3 (perm_in_head _ _ _ HPcur)) 5%nat; intros C1 C2 C3 C4 C5).
        try rewrite alloc_ceiling_eq in C4. unfold PIMG_LO, PIMG_HI in C5.
        assert (CPART : forall A' n', In (A', n') ((A, 64) :: (B1 ++ Bv ++ Bc) ++ (U, 64) :: LR) -> A' <> cur /\ (A' + n' <= cur \/ cur + 64 <= A')).
        { intros A' n' Hin. eapply (lheap_perm_apart HI); [exact HL3| exact HPcur| exact Hin]. }
        destruct (CPART A 64 ltac:(left; reflexivity)) as [_ CA'].
        destruct (CPART U 64 ltac:(right; apply in_or_app; right; left; reflexivity)) as [_ CU].
        destruct (CPART D n ltac:(right; apply in_or_app; right; right; exact (proj1 HDn))) as [_ CD].
        pose proof (rw_cells_bound usegs _ _ _ NDC) as NCB. rewrite node_cells_size in NCB.
        unfold node_cells, wz in NDC. unfold node_cells, wz in NDA.
        (* [comment removed for export] *)
        zstep. if_cases KC0; zify_cond KC0; [exfalso; lia|].
        zstep. rewrite (align16_land7 cur C2). zstep. if_cases KC1; zify_cond KC1; [exfalso; exact (KC1 eq_refl)|].
        zstep. rewrite (align16_land7 A A2).
        pose proof (munch_refl [(cur, cur + 8)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
        zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
        zstep. if_cases KC2; zify_cond KC2; [exfalso; exact (KC2 eq_refl)|].
        assert (INC : In (cur, 64) ((A, 64) :: LBX)) by (eapply perm_in_head; exact HPcur).
        assert (HL4 : LHEAP HI SPB ((A, 64) :: LBX) m4 mo2) by (eapply (lheap_block_store HI); [exact HL3| exact INC| exact MU| exact WM| lia| lia]).
        assert (CJ4 : CJST m4) by (eapply (CJST_block_store HI); [exact HL3| exact INC| exact CJ3| exact MU| exact WM| lia| lia]).
        assert (PR5 : ppres LR SP P m m4).
        { eapply ppres_trans; [exact PR4|]. eapply (ppres_block_store HI); [exact HL3| exact HPcur| intros b Hb; right; apply in_or_app; right; right; exact Hb| alia| exact MU| exact WM| lia| lia]. }
        assert (DJ : forall A' n', In (A', n') (B1 ++ Bv ++ Bc) -> disjoint_from [(cur, cur + 8)] A' n').
        { intros A' n' Hin. cbn. split; [|exact I]. destruct (CPART A' n' ltac:(right; apply in_or_app; left; exact Hin)). lia. }
        assert (SEG4 : cj_lseg CJ_PRINTABLE m4 dch head cur B1).
        { eapply cj_lseg_frame; [exact SEG| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. left. exact Hin. }
        assert (SVC4 : cj_str m4 vsc Bv).
        { eapply cj_str_frame; [exact SVC| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (CHC4 : cj_chain CJ_PRINTABLE m4 dch chc Bc).
        { eapply cj_chain_frame; [exact CHC| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. right. exact Hin. }
        clear MU WM HL3 CJ3 PR4 SEG SVC CHC DJ.
        (* [comment removed for export] *)
        pose proof (munch_refl [(A + 8, A + 16)] m4) as MU. pose proof (wmono_refl usegs m4) as WM.
        zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        assert (HL5 : LHEAP HI SPB ((A, 64) :: LBX) m5 mo2) by (eapply (lheap_block_store HI); [exact HL4| left; reflexivity| exact MU| exact WM| lia| lia]).
        assert (CJ5 : CJST m5) by (eapply (CJST_block_store HI); [exact HL4| left; reflexivity| exact CJ4| exact MU| exact WM| lia| lia]).
        assert (PR6 : ppres LR SP P m m5).
        { eapply ppres_trans; [exact PR5|]. eapply (ppres_block_store HI); [exact HL4| apply Permutation_refl| exact INLR| alia| exact MU| exact WM| lia| lia]. }
        assert (DJ : forall A' n', In (A', n') (B1 ++ Bv ++ Bc) -> disjoint_from [(A + 8, A + 16)] A' n').
        { intros A' n' Hin. cbn. split; [|exact I].
          destruct (APART A' n') as [_ ?]; [| lia]. apply INX. apply in_app_or in Hin. apply in_or_app. destruct Hin as [Hin|Hin]; [left; exact Hin| right; right; exact Hin]. }
        assert (SEG5 : cj_lseg CJ_PRINTABLE m5 dch head cur B1).
        { eapply cj_lseg_frame; [exact SEG4| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. left. exact Hin. }
        assert (SVC5 : cj_str m5 vsc Bv).
        { eapply cj_str_frame; [exact SVC4| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (CHC5 : cj_chain CJ_PRINTABLE m5 dch chc Bc).
        { eapply cj_chain_frame; [exact CHC4| exact MU| exact WM|]. intros A' n' Hin. apply DJ. apply in_or_app. right. apply in_or_app. right. exact Hin. }
        clear MU WM HL4 CJ4 PR5 SEG4 SVC4 CHC4 DJ.
        zstep. apply evt_done.
        eapply (do_call c IHc _ o head A (Z_to_bv 64 cur) (B1 ++ (cur, 64) :: Bv ++ Bc) m5 mo2 ((A, 64) :: LBX) errv2);
          [exact Hc| exact Ho| exact Hd| | apply perm_skip; exact HPX| exact NZ| | eqcells NDA| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| exact FA| exact FRM].
        * split; [exact HL5|]. split; [exact BY|]. split; [exact CJ5|]. split; [unfold PERRNO; exact ERR2|]. split; [exact MI3|]. split; [exact ST2| exact PR6].
        * eapply cj_lseg_snoc0; [exact SEG5| exact NZc| eqcells NDC| apply CJ_PRINTABLE_range; exact TYC| exact TYC| exact SVC5| exact CHC5].
  Qed.

  Theorem aloop : forall c, ALOOPc c.
  Proof. induction c as [c IH] using lt_wf_ind. apply loop_body. exact IH. Qed.

End PVL.


End CeilWrap.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.
End CJ_pvalue_L.

(* [comment removed for export] *)
Module CJ_pwlopts_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_skipws CJ_delete OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_lemmas CJ_pvalue_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dpres_of_cj_pres : forall LB LB1 SP SP' m1 m2,
  cj_pres LB1 SP' m1 m2 -> SP' <= SP -> (forall b, In b LB -> In b LB1) -> dpres LB SP m1 m2.
Proof.
  intros LB LB1 SP SP' m1 m2 H HS HL a Ha [Hc _]. apply H; [exact Ha|].
  destruct Hc as [H1|[H2|(A & n & Hin & Hr)]]; [left; lia| right; left; exact H2| right; right].
  exists A, n. split; [apply HL; exact Hin| exact Hr].
Qed.

Lemma dpres_of_ppres : forall LB SP SP' P m1 m2,
  ppres LB SP' P m1 m2 -> SP' <= SP -> P + 56 <= SP -> dpres LB SP m1 m2.
Proof.
  intros LB SP SP' P m1 m2 H HS HP a Ha [Hc _]. apply H; [exact Ha|].
  destruct Hc as [H1|[H2|H3]]; [left; lia| right; left; exact H2| right; right; exact H3].
Qed.

Lemma dpres_of_munch : forall LB SP W m1 m2,
  munch W m1 m2 -> wmono usegs m1 m2 -> (forall a, 0 <= a < 2^64 -> doc_addr LB SP a -> outside W a) -> dpres LB SP m1 m2.
Proof. intros. eapply magree_of_munch; eauto. Qed.

Section WL.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (SPB : Z) (LB : list cblock) (CA blen : Z) (bs : list byte) (D n lo : Z).

  Definition wl_pure : Prop :=
    (In (D, n) LB /\ D <= CA /\ CA + blen <= D + n) /\ 0 < CA
    /\ Z.of_nat (length bs) = blen /\ blen < 2^31
    /\ alloc_ceiling <= lo /\ lo <= bv_unsigned sp - PARSE_DOC_STACK
    /\ bv_unsigned sp <= SPB /\ SPB < 2^62
    /\ tp = wz PTP /\ cblock_range D n
    /\ bv_unsigned sp mod 16 = 0.    (* [comment removed for export] *)
  Hypothesis WLC : wl_pure.

  Notation SP := (bv_unsigned sp).
  Definition DPOST := parse_doc_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LB CA bs lo m.

  (* [comment removed for export] *)
  Definition CSTW (pc : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word)
      (Fx : bvmap 5 word) (fcx : bv 32) (mm : word -> option byte) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
       Fx (Z_to_bv 64 pc) fcx None mm (seg_rom usegs).

  Definition FRS (mm : word -> option byte) : Prop :=
    rw_cells usegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition MIDW (m1 : word -> option byte) (mo1 : Model) (LB1 : list cblock) (errv1 : word) : Prop :=
    LHEAP HI SPB LB1 m1 mo1 /\ bytes_at usegs m1 CA bs /\ CJST m1 /\ rw_cells usegs m1 PERRNO [C4 errv1]
    /\ mem_inv usegs m1 /\ stk usegs m1 lo (bv_unsigned sp + -112) /\ dpres LB (bv_unsigned sp) m m1.

  Lemma wlc_lits :
    (In (D, n) LB /\ D <= CA /\ CA + blen <= D + n) /\ 0 < CA
    /\ Z.of_nat (length bs) = blen /\ blen < 2^31
    /\ alloc_ceiling <= lo /\ lo <= SP - (112 + (144 * (1001 - 0) + 16384))
    /\ SP <= SPB /\ SPB < 2^62 /\ tp = wz PTP
    /\ (0 < D /\ D mod 16 = 0 /\ 0 <= n /\ D + n <= alloc_ceiling /\ (D + n <= 0x10000 \/ 0x56000 <= D))
    /\ SP mod 16 = 0 /\ 0 <= SP < 2^64.
  Proof.
    pose proof WLC as H. unfold wl_pure, cblock_range, PARSE_DOC_STACK, PARSE_STACK, PIMG_LO, PIMG_HI in H. try rewrite alloc_ceiling_eq in H.
    pose proof (bv_unsigned_in_range 64 sp) as R. change (bv_modulus 64) with (2^64) in R.
    (nelim H 11%nat; intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11).
    repeat (split; [assumption|]). exact R.
  Qed.

  Ltac lits := (nelimp wlc_lits 12%nat; intros HDn CA0 LEN BLEN CEIL LO SPSPB SPB62 TP DRNG SPAL SPR).
  Ltac alia := rewrite ?alloc_ceiling_eq; unfold DELETE_STACK, PARSE_STACK, PARSE_STRING_STACK, PARSE_DOC_STACK; unfold RMALLOC_STACK; lia.
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac dj := cbn [disjoint_from cells_size csize Nat.add length];
             repeat match goal with H : length ?l = _ |- context [length ?l] => rewrite H end;
             first [lia | split; [lia| exact I]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].

  (* [comment removed for export] *)
  Lemma frame_merge : forall mm (j : list byte) (c1 c2 c3 c4 c5 c6 c7 : word),
    rw_cells usegs mm (SP + -112) [CB 8 j] ->
    rw_cells usegs mm (SP + -104) [C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7] ->
    FRS mm ->
    rw_cells usegs mm (SP + -112) [CB 8 j; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Proof.
    intros mm j c1 c2 c3 c4 c5 c6 c7 FJ PB FS. unfold FRS in FS.
    apply (proj2 (rw_cells_split_app mm (SP + -112) [CB 8 j] _)). split; [exact FJ|].
    cbn [cells_size csize Nat.add]. replace (SP + -112 + Z.of_nat 8) with (SP + -104) by lia.
    apply (proj2 (rw_cells_split_app mm (SP + -104) [C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7] _)). split; [exact PB|].
    cbn [cells_size csize Nat.add]. replace (SP + -104 + Z.of_nat 56) with (SP + -48) by lia. exact FS.
  Qed.

  (* [comment removed for export] *)
  Lemma epilogue_w : forall x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 Fx fcx mm,
    FRS mm ->
    evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                                 Fx (ret_pc ra) fcx None mm (seg_rom usegs))
        (CSTW 0x13b28 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 Fx fcx mm).
  Proof.
    intros. lits. unfold CSTW, FRS in *.
    do 8 zstep. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma doc_fail_tail : forall (j : list byte) (c1 c2 c3 c4 c5 c6 c7 pos : word) m1 mo1 LB1 errv1 Fx fcx
      x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31,
    MIDW m1 mo1 LB1 errv1 -> Permutation LB1 LB ->
    rw_cells usegs m1 (SP + -112) [CB 8 j] ->
    rw_cells usegs m1 (SP + -104) [C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7] ->
    FRS m1 ->
    Fagree F Fx -> frm0 fcx ->
    SCPS usegs DPOST (CSTW 0x13ac0 x1 x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 CA) x10 pos x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 PGERROR) x20 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HP1 FJ PB FS FA FRM. lits. unfold CSTW.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. unfold PERRNO in ERR. unfold FRS in FS.
    pose proof CJ as (HK & (e1 & e2 & GE) & LC). unfold PHOOKS in HK. unfold PGERROR in GE. unfold PLCONV in LC. unfold PGERROR.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. if_true.
    pose proof (munch_refl [(0x348f0, 0x348f0 + 16)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    zstep. eapply evt_cut; [apply epilogue_w; exact FS|]. intros ms' ->.
    pose proof (frame_merge _ _ _ _ _ _ _ _ _ FJ PB FS) as FR. clear FJ PB FS. release_frame FR ST (bv_unsigned sp).
    apply evt_done. apply scps_done. unfold DPOST, parse_doc_post.
    nexists 17%nat. exists m2, 0, LB1, errv1.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FA|]. split; [exact FRM|]. split; [exact MI|]. split; [exact ST|].
    split. { split; [unfold PHOOKS; exact HK|]. split; [do 2 eexists; unfold PGERROR; exact GE| unfold PLCONV; exact LC]. }
    split; [unfold PERRNO; exact ERR|].
    split. { eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor]. do 3 right; left. unfold PGERROR. cbn. lia. }
    split; [exact BY|].
    split. { eapply dpres_trans; [exact PR|]. eapply dpres_of_munch; [exact MU| exact WM|]. intros a Ha [_ Hg]. unfold PGERROR in Hg. cbn. lia. }
    left. split; [reflexivity| exact HP1].
  Qed.

  (* [comment removed for export] *)
  Lemma doc_fail : forall (j : list byte) (c lw ow d h1 h2 h3 : word) m1 mo1 LB1 errv1 Fx fcx
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31,
    MIDW m1 mo1 LB1 errv1 -> Permutation LB1 LB ->
    rw_cells usegs m1 (SP + -112) [CB 8 j] ->
    rw_cells usegs m1 (SP + -104) [C8 c; C8 lw; C8 ow; C8 d; C8 h1; C8 h2; C8 h3] ->
    FRS m1 ->
    Fagree F Fx -> frm0 fcx ->
    SCPS usegs DPOST (CSTW 0x13aa4 x1 x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 CA) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 PGERROR) x20 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros MIDm HP1 FJ PB FS FA FRM. pose proof MIDm as (HL & _). lits. unfold CSTW.
    pose proof FS as FS'. unfold FRS in FS'.
    pose proof (bv_unsigned_in_range 64 lw) as Rl. pose proof (bv_unsigned_in_range 64 ow) as Ro. change (bv_modulus 64) with (2^64) in Rl, Ro.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. zstep. zstep. if_cases Kol; zify_cond Kol.
    - apply evt_done. eapply doc_fail_tail; [exact MIDm| exact HP1| exact FJ| exact PB| exact FS| exact FA| exact FRM].
    - zstep. zstep. zstep. zstep. apply evt_done. eapply doc_fail_tail; [exact MIDm| exact HP1| exact FJ| exact PB| exact FS| exact FA| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Lemma doc_fail_delete : forall (j : list byte) (c lw ow d h1 h2 h3 : word) (item : Z) (B : list cblock) (dd : nat) m1 mo1 LB1 errv1 Fx fcx
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31,
    MIDW m1 mo1 LB1 errv1 -> Permutation (B ++ LB) LB1 ->
    cj_chain CJ_ANY m1 dd item B -> (dd <= 1001)%nat ->
    rw_cells usegs m1 (SP + -112) [CB 8 j] ->
    rw_cells usegs m1 (SP + -104) [C8 c; C8 lw; C8 ow; C8 d; C8 h1; C8 h2; C8 h3] ->
    FRS m1 ->
    Fagree F Fx -> frm0 fcx ->
    SCPS usegs DPOST (CSTW 0x13a98 x1 x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 CA) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 item) (Z_to_bv 64 PGERROR) x20 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HPB CH Hdd FJ PB FS FA FRM. lits. unfold CSTW.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. unfold FRS in FS.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. zstep.
    replace (ret_pc (Z_to_bv 64 0x137c0)) with (wz DELETE_ENTRY) by (unfold wz, DELETE_ENTRY; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply scps_bind.
    { pose proof (cjson_delete_spec HI dd) as DS. unfold delete_spec_at in DS.
      eapply DS with (lo := lo); clear DS; rewrite ?unsigned_lit by lia;
        first [ exact HL | exact CH | exact HPB | exact CJ | exact ST | exact ERR | exact MI | exact TP | reflexivity | alia ]. }
    cbv beta. intros ms2 mo2 PO'.
    (nelim PO' 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 LR2 -> MI2 ST2 CJ2 ERR2 HL2 HP2 PR2)
.
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x13aa0)) with (Z_to_bv 64 0x13aa0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FJ; [| left; cbn; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PB; [| left; cbn; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FS; [| left; cbn; lia].
    apply (cj_pres_bytes_at _ _ _ _ _ _ PR2) in BY; [| right; right; exists D, n; split; [apply (proj1 HDn)| lia]].
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
    apply evt_done. eapply doc_fail; [| exact HP2| exact FJ| exact PB| exact FS| exact FA| exact FRM].
    split; [exact HL2|]. split; [exact BY|]. split; [exact CJ2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
    eapply dpres_trans; [exact PR|]. eapply dpres_of_cj_pres; [exact PR2| lia| intros b Hb; exact Hb].
  Qed.

  (* [comment removed for export] *)
  Lemma doc_success : forall (j : list byte) (c1 c2 c3 c4 c5 c6 c7 : word) (item : Z) (B : list cblock) (d : nat)
      (ch ty vs : Z) (p1 vi p2 vd : word) m1 mo1 LB1 errv1 Fx fcx
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31,
    MIDW m1 mo1 LB1 errv1 -> Permutation LB1 (B ++ LB) ->
    cj_chain CJ_PRINTABLE m1 d item B -> (d <= 1001)%nat -> item <> 0 ->
    rw_cells usegs m1 item (node_cells 0 (wz 0) ch ty p1 vs vi p2 vd 0) ->
    rw_cells usegs m1 (SP + -112) [CB 8 j] ->
    rw_cells usegs m1 (SP + -104) [C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7] ->
    FRS m1 ->
    Fagree F Fx -> frm0 fcx ->
    SCPS usegs DPOST (CSTW 0x13af4 x1 x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 CA) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 item) x19 x20 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HPB CH Hd NZ ND FJ PB FS FA FRM. lits. unfold CSTW.
    pose proof FS as FS'. unfold FRS in FS.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. if_true. zstep.
    eapply evt_cut; [apply epilogue_w; exact FS'|]. intros ms' ->.
    pose proof (frame_merge _ _ _ _ _ _ _ _ _ FJ PB FS) as FR. clear FJ PB FS. release_frame FR ST (bv_unsigned sp).
    apply evt_done. apply scps_done. unfold DPOST, parse_doc_post.
    nexists 17%nat. exists m1, item, LB1, errv1.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FA|]. split; [exact FRM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact CJ|]. split; [exact ERR|]. split; [exact HL|]. split; [exact BY|]. split; [exact PR|].
    right. split; [exact NZ|]. exists B, d, ch, ty, p1, vs, vi, p2, vd.
    split; [exact CH|]. split; [exact Hd|]. split; [exact HPB| exact ND].
  Qed.

  (* [comment removed for export] *)
  Lemma wsB : forall (cnt : nat) (i dp : Z) (m0 m1 : word -> option byte) Fx fcx
      x1 x5 x6 x7 x8 x9 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells usegs m1 (SP + -104) (pbuf_cells CA blen i dp) -> bytes_at usegs m1 CA bs -> mem_inv usegs m1 ->
    munch [(SP + -88, SP + -80)] m0 m1 -> wmono usegs m0 m1 ->
    evt usegs (fun ms' => exists x15' m2,
                 ms' = CSTW 0x13a70 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 CA) (Z_to_bv 64 (fin blen bs i)) (Z_to_bv 64 blen) (Z_to_bv 64 (18446744073709551615 - CA)) (Z_to_bv 64 32) x15' x16 x17
                          x18 x19 x20 x28 x29 x30 x31 Fx fcx m2
                 /\ rw_cells usegs m2 (SP + -104) (pbuf_cells CA blen (fin blen bs i) dp) /\ bytes_at usegs m2 CA bs /\ mem_inv usegs m2
                 /\ munch [(SP + -88, SP + -80)] m0 m2 /\ wmono usegs m0 m2)
        (CSTW 0x13a44 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 CA) (Z_to_bv 64 i) (Z_to_bv 64 blen) (Z_to_bv 64 (18446744073709551615 - CA)) (Z_to_bv 64 32) x15 x16 x17
             x18 x19 x20 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. lits.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (rw_cells_bound usegs _ _ _ PB) as PBB. rewrite pbuf_cells_size in PBB.
    unfold pbuf_cells, wz in PB. unfold CSTW.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hn; [| apply nth_error_None in Hn; lia].
    pose proof (u8ro_read usegs _ CA bs i b _ BY Hn ltac:(lia) eq_refl) as RD.
    pose proof (byte_range b) as Rb.
    assert (SEP : CA + blen <= SP + -104 \/ SP + -104 + 56 <= CA) by lia.
    zstep. if_cases KG; zify_cond KG; [exfalso; lia|].
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
      apply evt_done. do 2 eexists.
      split; [rewrite (fin_stop (SP + -104) CA blen bs LEN SEP i b) by first [lia | exact Hn]; reflexivity|].
      split; [unfold pbuf_cells, wz; rewrite (fin_stop (SP + -104) CA blen bs LEN SEP i b) by first [lia | exact Hn]; exact PB|].
      split; [exact BY|]. split; [exact MI|]. split; [exact MU| exact WM].
    - zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + replace (CA + i + 1) with (CA + (i + 1)) by lia.
        rewrite (fin_ws (SP + -104) CA blen bs LEN ltac:(lia) ltac:(lia) i b) by first [lia | exact Hn].
        destruct (Z.eqb_spec (i + 1) blen); [exfalso; lia|].
        eapply (IH (cnt - 1)%nat ltac:(lia) (i + 1)); [lia| lia| unfold pbuf_cells, wz; exact PB| exact BY| exact MI| exact MU| exact WM].
      + zstep. zstep. zstep.
        rewrite (fin_ws (SP + -104) CA blen bs LEN ltac:(lia) ltac:(lia) i b) by first [lia | exact Hn].
        destruct (Z.eqb_spec (i + 1) blen); [| exfalso; lia].
        apply evt_done. do 2 eexists.
        split; [replace (blen - 1) with (blen + -1) by lia; reflexivity|].
        split; [unfold pbuf_cells, wz; replace (blen - 1) with (blen + -1) by lia; exact PB|].
        split; [exact BY|]. split; [exact MI|]. split; [exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma null_check : forall (j : list byte) (off1 item : Z) (rnt : word) (Bv Bc : list cblock) (dc : nat)
      (ch ty vs : Z) (vi vd : word) m1 mo1 LB1 errv1 Fx fcx
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    MIDW m1 mo1 LB1 errv1 -> Permutation ((item, 64) :: (Bv ++ Bc) ++ LB) LB1 ->
    item <> 0 -> rw_cells usegs m1 item (node_cells 0 (wz 0) ch ty (wz 0) vs vi (wz 0) vd 0) ->
    CJ_PRINTABLE ty -> cj_str m1 vs Bv -> cj_chain CJ_PRINTABLE m1 dc ch Bc -> (dc <= 1000)%nat ->
    rw_cells usegs m1 (SP + -112) [CB 8 j] ->
    rw_cells usegs m1 (SP + -104) (pbuf_cells CA blen off1 0) -> 0 <= off1 <= blen ->
    FRS m1 ->
    Fagree F Fx -> frm0 fcx ->
    SCPS usegs DPOST (CSTW 0x13a24 x1 x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 CA) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 item) (Z_to_bv 64 PGERROR) rnt x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros MIDm HPB NZ ND HT SV CH Hdc FJ PB Ho FS FA FRM. lits. unfold CSTW.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (CHR : cj_chain CJ_PRINTABLE m1 (S dc) item ((item, 64) :: Bv ++ [] ++ Bc)).
    { eapply cj_chain_one; [exact NZ| exact ND| apply CJ_PRINTABLE_range; exact HT| exact HT| exact SV| apply cj_str_null| exact CH]. }
    cbn [app] in CHR.
    assert (HPB' : Permutation LB1 (((item, 64) :: Bv ++ Bc) ++ LB)) by (apply Permutation_sym; exact HPB).
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HPB)) 5%nat; intros I1 I2 I3 I4 I5).
    try rewrite alloc_ceiling_eq in I4. unfold PIMG_LO, PIMG_HI in I5.
    pose proof PB as PB'. unfold pbuf_cells, wz in PB.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. if_cases Krnt; zify_cond Krnt.
    { (* [comment removed for export] *)
      apply evt_done. eapply doc_success; [exact MIDm| exact HPB'| exact CHR| lia| exact NZ| exact ND| exact FJ| exact PB| exact FS| exact FA| exact FRM]. }
    zstep. zstep. zstep. zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
    (* [comment removed for export] *)
    assert (JOIN : forall x13' x14' x15' m2,
      rw_cells usegs m2 (SP + -104) (pbuf_cells CA blen (skipws_off bs off1) 0) -> bytes_at usegs m2 CA bs -> mem_inv usegs m2 ->
      munch [(SP + -88, SP + -80)] m1 m2 -> wmono usegs m1 m2 ->
      evt usegs (fun ms' => SCPS usegs DPOST ms' mo1)
        (CSTW 0x13a70 x1 x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 CA) (Z_to_bv 64 CA) (Z_to_bv 64 (skipws_off bs off1)) (Z_to_bv 64 blen) x13' x14' x15' x16 x17
             (Z_to_bv 64 item) (Z_to_bv 64 PGERROR) rnt x28 x29 x30 x31 Fx fcx m2)).
    { intros x13' x14' x15' m2 PB2 BY2 MI2 MU2 WM2. unfold CSTW.
      pose proof FJ as FJ2. trc FJ2 MU2 WM2. pose proof FS as FS2. unfold FRS in FS2. trc FS2 MU2 WM2.
      pose proof ND as ND2. unfold node_cells, wz in ND2. trc ND2 MU2 WM2.
      pose proof ERR as ERR2. unfold PERRNO in ERR2. trc ERR2 MU2 WM2. pose proof ST as ST2. trc ST2 MU2 WM2.
      assert (HL2 : LHEAP HI SPB LB1 m2 mo1) by (eapply (lheap_frame_store HI); [exact HL| exact MU2| exact WM2| alia| alia]).
      assert (CJ2 : CJST m2) by (eapply CJST_high_store; [exact CJ| exact MU2| exact WM2| alia]).
      assert (PR2 : dpres LB SP m m2).
      { eapply dpres_trans; [exact PR|]. eapply dpres_of_munch; [exact MU2| exact WM2|].
        intros a Ha [[Hs|[[Hd _]|(A' & n' & Hin & Hr)]] _]; cbn; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HPB| right; apply in_or_app; right; exact Hin])) 5%nat; intros _ _ _ R4 _).
        try rewrite alloc_ceiling_eq in R4. lia. }
      assert (BLK : forall A' k', In (A', k') LB1 -> disjoint_from [(SP + -88, SP + -80)] A' k').
      { intros A' k' Hin. cbn. split; [|exact I].
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL Hin) 5%nat; intros _ _ _ R4 _). try rewrite alloc_ceiling_eq in R4. lia. }
      assert (CHR2 : cj_chain CJ_PRINTABLE m2 (S dc) item ((item, 64) :: Bv ++ Bc)).
      { eapply cj_chain_frame; [exact CHR| exact MU2| exact WM2|]. intros A' k' Hin. apply BLK.
        eapply Permutation_in; [exact HPB|]. change (In (A', k') (((item, 64) :: Bv ++ Bc) ++ LB)). apply in_or_app. left. exact Hin. }
      assert (MID2 : MIDW m2 mo1 LB1 errv1).
      { split; [exact HL2|]. split; [exact BY2|]. split; [exact CJ2|]. split; [unfold PERRNO; exact ERR2|]. split; [exact MI2|]. split; [exact ST2| exact PR2]. }
      pose proof (rw_cells_bound usegs _ _ _ PB2) as PBB2. rewrite pbuf_cells_size in PBB2. unfold pbuf_cells, wz in PB2.
      assert (O2 : off1 <= skipws_off bs off1 <= blen).
      { destruct (Z.eq_dec off1 blen) as [E|NE].
        - rewrite skipws_off_noop by lia. lia.
        - pose proof (skipws_off_range bs off1) as OR. rewrite LEN in OR. lia. }
      set (o2 := skipws_off bs off1) in *.
      zstep. if_cases Kend; zify_cond Kend.
      { apply evt_done. eapply doc_fail_delete; [exact MID2| | eapply cj_chain_any; exact CHR2| lia| exact FJ2| exact PB2| exact FS2| exact FA| exact FRM]. exact HPB. }
      (* [comment removed for export] *)
      zstep. zstep. if_cases KW; zify_cond KW; [exfalso; lia|].
      zstep. zstep. zstep. zstep. if_cases KN; zify_cond KN.
      { exfalso. revert KN. replace (0 <? CA) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (CA + o2 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). vm_compute. discriminate. }
      zstep. if_cases KZ; zify_cond KZ; [exfalso; lia|].
      (nelim (text_read m2 CA bs o2 (Z_to_bv 64 (CA + o2)) BY2 ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b Hb RD _).
      pose proof (byte_range b) as Rb.
      zstep. zstep. if_cases K0; zify_cond K0.
      { apply evt_done. eapply doc_success; [exact MID2| exact HPB'| exact CHR2| lia| exact NZ| eqcells ND2| exact FJ2| exact PB2| exact FS2| exact FA| exact FRM]. }
      apply evt_done. eapply doc_fail_delete; [exact MID2| | eapply cj_chain_any; exact CHR2| lia| exact FJ2| exact PB2| exact FS2| exact FA| exact FRM]. exact HPB. }
    zstep. if_cases Kskip; zify_cond Kskip.
    - replace (Z_to_bv 64 off1) with (Z_to_bv 64 (skipws_off bs off1)) by (rewrite skipws_off_noop by lia; reflexivity).
      eapply JOIN; [| exact BY| exact MI| apply munch_refl| apply wmono_refl]. rewrite skipws_off_noop by lia. exact PB'.
    - zstep. rewrite zb_lxor_ones by lia. zstep.
      pose proof (fin_off0 blen off1 bs LEN ltac:(lia)) as FO.
      eapply evt_cut.
      { eapply (wsB (Z.to_nat (blen - off1)) off1 0 m1 m1); [lia| lia| exact PB'| exact BY| exact MI| apply munch_refl| apply wmono_refl]. }
      intros ms' nelH_; (nelim nelH_ 8%nat; intros x15' m2 -> PB2 BY2 MI2 MU2 WM2). rewrite <- FO in PB2 |- *.
      eapply JOIN; [exact PB2| exact BY2| exact MI2| exact MU2| exact WM2].
  Qed.
End WL.


End CeilWrap.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.
End CJ_pwlopts_A.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_skipws.
Import CJ_delete.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import CJ_utraps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_lemmas.
Import CJ_pvalue_lemmas.
Import CJ_pvalue_ctx.
Import CJ_pvalue_A.
Import CJ_pobject_ctx.
Import CJ_pobject_ws.
Import CJ_pobject_L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.




(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section POE.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (SPB : Z) (LB LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure sp tp SPB LB LR U P CA blen off depth bs D n lo.
  Variable nfuel : nat.
  Hypothesis FUEL : blen - off <= Z.of_nat nfuel.
  Hypothesis PVREC : forall nf, (nf < nfuel)%nat -> parse_value_at HI nf.
  Hypothesis PS : parse_string_stmt HI.

  Notation SP := (bv_unsigned sp).
  Notation CST := (CSTO sp gp tp s10 s11).
  Notation POST := (POSTV HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).
  Notation MID := (MIDO HI sp m SPB LR P CA bs lo).
  Notation dch := (dch depth).

  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac dj := cbn [disjoint_from cells_size csize Nat.add length];
             repeat match goal with H : length ?l = _ |- context [length ?l] => rewrite H end;
             first [lia | split; [lia| exact I]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply u8arr_transport in H; [| exact MU| exact WM| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].
  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC) as (HPU & HDn & LEN & BLEN & CEIL & LO & PP & OFF & DEP & TP & URNG & DRNG & UD & SPR).
  Ltac alia := rewrite ?alloc_ceiling_eq; unfold DELETE_STACK, PARSE_STACK, PARSE_STRING_STACK; unfold RMALLOC_STACK; lia.
  Ltac killK K := first [exfalso; apply K; reflexivity | exfalso; revert K; lia_cj_nf].

  Lemma po_body : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (mo : Model) (errv : word),
    LHEAP HI SPB LB m mo -> bytes_at usegs m CA bs -> CJST m -> rw_cells usegs m PERRNO [C4 errv] -> mem_inv usegs m ->
    stk usegs m lo SP ->
    rw_cells usegs m U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) -> pbuf_at m P CA blen off depth ->
    frm0 fc -> a0 = wz U -> a1 = wz P ->
    SCPS usegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (wz PARSE_OBJECT) fc None m (seg_rom usegs)) mo.
  Proof.
    intros until errv. intros HL BY CJ ERR MI ST ND PB FRM A0 A1. lits. pose proof (ppres_refl LR SP P m) as PR0.
    unfold wz in A0, A1. subst a0 a1. unfold PARSE_OBJECT, wz.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. unfold pbuf_at, pbuf_cells, wz in PB.
    pose proof (rw_cells_bound usegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB. unfold node_cells, wz in ND.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. unfold PERRNO in ERR.
    assert (INLR : forall b, In b LR -> In b LB) by (intros b Hb; eapply Permutation_in; [exact HPU| right; exact Hb]).
    assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    pose proof (munch_refl [(SP + -96, SP)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. carve_frame 96%nat ST. do 11 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => set (junk0 := j) in FR; clearbody junk0 end.
    assert (HL1 : LHEAP HI SPB LB m1 mo) by (eapply (lheap_frame_store HI); [exact HL| exact MU| exact WM| alia| alia]).
    assert (CJ1 : CJST m1) by (eapply CJST_high_store; [exact CJ| exact MU| exact WM| alia]).
    assert (PR1 : ppres LR SP P m m1).
    { eapply ppres_trans; [exact PR0|]. eapply (ppres_frame_store HI); [exact HL| exact INLR| exact MU| exact WM| alia| lia]. }
    clear MU WM HL CJ PR0.
    assert (MID1 : MID m1 mo LB errv).
    { split; [exact HL1|]. split; [exact BY|]. split; [exact CJ1|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST| exact PR1]. }
    (* [comment removed for export] *)
    zstep. zstep. rewrite (align8_land7 P) by lia. zstep. if_cases KA; zify_cond KA; [killK KA|]. clear KA. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases Kd; zify_cond Kd.
    { apply evt_done. eapply ret0_o; [exact PVC| exact MID1| exact HPU| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| apply Fagree_refl| exact FRM]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 24, P + 32)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : LHEAP HI SPB LB m2 mo) by (eapply (lheap_frame_store HI); [exact HL1| exact MU| exact WM| alia| alia]).
    assert (CJ2 : CJST m2) by (eapply CJST_high_store; [exact CJ1| exact MU| exact WM| alia]).
    assert (PR2 : ppres LR SP P m m2).
    { eapply ppres_trans; [exact PR1|]. eapply (ppres_pbuf_store HI); [exact HL1| exact INLR| exact MU| exact WM| alia| alia| alia]. }
    clear MU WM HL1 CJ1 PR1 MID1.
    assert (MID2 : MID m2 mo LB errv).
    { split; [exact HL2|]. split; [exact BY|]. split; [exact CJ2|]. split; [unfold PERRNO; exact ERR|]. split; [exact MI|]. split; [exact ST| exact PR2]. }
    zstep. if_cases Kend; zify_cond Kend.
    { apply evt_done. eapply ret0_o; [exact PVC| exact MID2| exact HPU| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| apply Fagree_refl| exact FRM]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KW; zify_cond KW; [exfalso; lia|].
    zstep. zstep. zstep. zstep. if_cases KN; zify_cond KN.
    { exfalso. revert KN. replace (0 <? CA) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (CA + off <? 1) with false by (symmetry; apply Z.ltb_ge; lia). vm_compute. discriminate. }
    zstep. if_cases KZ; zify_cond KZ; [exfalso; lia|].
    destruct (text_read m2 CA bs off (Z_to_bv 64 (CA + off)) BY ltac:(lia) ltac:(lia) eq_refl) as (b & Hb & RD & _).
    pose proof (byte_range b) as Rb.
    zstep. zstep. zstep. if_cases K123; zify_cond K123.
    { apply evt_done. eapply ret0_o; [exact PVC| exact MID2| exact HPU| exact FR| unfold pbuf_at; eqcells PB| eqcells ND| apply Fagree_refl| exact FRM]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (BLK : forall A' k, In (A', k) LB -> disjoint_from [(P + 16, P + 24)] A' k).
    { intros A' k Hin. cbn. split; [|exact I].
      pose proof (lh_block_range HI _ _ _ _ _ _ HL2 Hin) as (_ & _ & _ & R4 & _). try rewrite alloc_ceiling_eq in R4. lia. }
    (* [comment removed for export] *)
    assert (JOIN : forall x14' x15' x16' m4,
      rw_cells usegs m4 P (pbuf_cells CA blen (skipws_off bs (off + 1)) (depth + 1)) -> bytes_at usegs m4 CA bs -> mem_inv usegs m4 ->
      munch [(P + 16, P + 24)] m3 m4 -> wmono usegs m3 m4 ->
      evt usegs (fun ms' => SCPS usegs POST ms' mo)
        (CST 0x1510c ra t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 U) (Z_to_bv 64 depth) (Z_to_bv 64 (skipws_off bs (off + 1))) (Z_to_bv 64 CA) (Z_to_bv 64 blen) x14' x15' x16' a7
             s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 F fc m4)).
    { intros x14' x15' x16' m4 PB4 BY4 MI4 MU4 WM4. unfold CSTO.
      pose proof (munch_trans _ _ _ _ MU MU4) as MU24. pose proof (wmono_trans _ _ _ _ WM WM4) as WM24.
      pose proof FR as FR4. trc FR4 MU4 WM4. pose proof ND as ND4. trc ND4 MU4 WM4.
      pose proof ERR as ERR4. trc ERR4 MU4 WM4. pose proof ST as ST4. trc ST4 MU4 WM4.
      assert (HL4 : LHEAP HI SPB LB m4 mo) by (eapply (lheap_frame_store HI); [exact HL2| exact MU24| exact WM24| alia| alia]).
      assert (CJ4 : CJST m4) by (eapply CJST_high_store; [exact CJ2| exact MU24| exact WM24| alia]).
      assert (PR4 : ppres LR SP P m m4).
      { eapply ppres_trans; [exact PR2|]. eapply (ppres_pbuf_store HI); [exact HL2| exact INLR| exact MU24| exact WM24| alia| alia| alia]. }
      clear MU4 WM4 MU24 WM24.
      assert (O2 : off + 1 <= skipws_off bs (off + 1) <= blen).
      { destruct (Z.eq_dec (off + 1) blen) as [E|NE].
        - rewrite skipws_off_noop by lia. lia.
        - pose proof (skipws_off_range bs (off + 1)) as OR. rewrite LEN in OR. lia. }
      set (o2 := skipws_off bs (off + 1)) in *.
      pose proof (rw_cells_bound usegs _ _ _ PB4) as PBB4. rewrite pbuf_cells_size in PBB4. unfold pbuf_cells, wz in PB4.
      (* [comment removed for export] *)
      zstep. if_cases Kend2; zify_cond Kend2.
      { (* [comment removed for export] *)
        pose proof (munch_refl [(P + 16, P + 24)] m4) as MU5. pose proof (wmono_refl usegs m4) as WM5.
        zstep. zstep. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        zstep. apply evt_done. eapply (ret0_epi_o HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC junk0 (o2 - 1) (depth + 1) m5 mo LB errv);
          [| exact HPU| exact FR4| unfold pbuf_at; eqcells PB4| eqcells ND4| apply Fagree_refl| exact FRM].
        split. { eapply (lheap_frame_store HI); [exact HL4| exact MU5| exact WM5| alia| alia]. }
        split; [exact BY4|]. split. { eapply CJST_high_store; [exact CJ4| exact MU5| exact WM5| alia]. }
        split; [unfold PERRNO; exact ERR4|]. split; [exact MI4|]. split; [exact ST4|].
        eapply ppres_trans; [exact PR4|]. eapply (ppres_pbuf_store HI); [exact HL4| exact INLR| exact MU5| exact WM5| alia| alia| alia]. }
      (* [comment removed for export] *)
      zstep. rewrite zb_lxor_ones by lia. zstep. if_cases KW2; zify_cond KW2; [killK KW2|]. clear KW2.
      zstep.
      destruct (text_read m4 CA bs o2 (Z_to_bv 64 (CA + o2)) BY4 ltac:(lia) ltac:(lia) eq_refl) as (c2 & Hc2 & RD2 & _).
      pose proof (byte_range c2) as Rc2.
      zstep. zstep. zstep. if_cases K125; zify_cond K125.
      - (* [comment removed for export] *)
        pose proof (munch_refl [(P + 16, P + 24)] m4) as MU5. pose proof (wmono_refl usegs m4) as WM5.
        zstep. zstep. zstep. zstep. zstep. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        zstep. apply evt_done.
        pose proof (oloop HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC junk0 nfuel FUEL PVREC PS (Z.to_nat (blen - (o2 - 1)))) as OL.
        unfold OLOOP, CSTO in OL.
        eapply (OL (o2 - 1) 0 0 [] m5 mo LB errv); [lia| lia| lia| | exact HPU| left; split; reflexivity| exact FR4| unfold pbuf_at; eqcells PB4| eqcells ND4| apply Fagree_refl| exact FRM].
        split. { eapply (lheap_frame_store HI); [exact HL4| exact MU5| exact WM5| alia| alia]. }
        split; [exact BY4|]. split. { eapply CJST_high_store; [exact CJ4| exact MU5| exact WM5| alia]. }
        split; [unfold PERRNO; exact ERR4|]. split; [exact MI4|]. split; [exact ST4|].
        eapply ppres_trans; [exact PR4|]. eapply (ppres_pbuf_store HI); [exact HL4| exact INLR| exact MU5| exact WM5| alia| alia| alia].
      - (* [comment removed for export] *)
        pose proof (munch_refl [(P + 24, P + 32)] m4) as MU5. pose proof (wmono_refl usegs m4) as WM5.
        zstep. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        zstep. rewrite (align16_land7 U) by lia. zstep. if_cases KA2; zify_cond KA2; [killK KA2|]. clear KA2.
        apply evt_done.
        eapply (obj_success HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC junk0 o2 0 [] m5 mo LB errv);
          [| exact HPU| apply cj_chain_nil| lia| exact FR4| unfold pbuf_at; eqcells PB4| eqcells ND4| lia| apply Fagree_refl| exact FRM].
        split. { eapply (lheap_frame_store HI); [exact HL4| exact MU5| exact WM5| alia| alia]. }
        split; [exact BY4|]. split. { eapply CJST_high_store; [exact CJ4| exact MU5| exact WM5| alia]. }
        split; [unfold PERRNO; exact ERR4|]. split; [exact MI4|]. split; [exact ST4|].
        eapply ppres_trans; [exact PR4|]. eapply (ppres_pbuf_store HI); [exact HL4| exact INLR| exact MU5| exact WM5| alia| alia| alia]. }
    zstep. if_cases Kskip; zify_cond Kskip.
    - replace (Z_to_bv 64 (off + 1)) with (Z_to_bv 64 (skipws_off bs (off + 1))) by (rewrite skipws_off_noop by lia; reflexivity).
      eapply JOIN; [| exact BY| exact MI| apply munch_refl| apply wmono_refl]. rewrite skipws_off_noop by lia. unfold pbuf_cells, wz. exact PB.
    - zstep. rewrite zb_lxor_ones by lia. zstep.
      pose proof (fin_off0 blen (off + 1) bs LEN ltac:(lia)) as FO.
      eapply evt_cut.
      { eapply (ws1 sp gp tp s10 s11 SPB LB LR U P CA blen off depth bs D n lo PVC (Z.to_nat (blen - (off + 1))) (off + 1) (depth + 1) m3 m3);
          [lia| lia| unfold pbuf_cells, wz; exact PB| exact BY| exact MI| apply munch_refl| apply wmono_refl]. }
      intros ms' (x16' & m4 & -> & PB4 & BY4 & MI4 & MU4 & WM4). rewrite <- FO in PB4 |- *.
      eapply JOIN; [exact PB4| exact BY4| exact MI4| exact MU4| exact WM4].
  Qed.
End POE.

(* [comment removed for export] *)
Theorem po_step : forall HI nfuel,
  parse_string_stmt HI -> (forall nf, (nf < nfuel)%nat -> parse_value_at HI nf) -> parse_object_at HI nfuel.
Proof.
  intros HI nfuel PS PVREC. unfold parse_object_at. intros until ky.
  intros (HL & HPU & HD & DCA & CAD & BY & LEN & BLEN & CJ & ERR & MI & ST & CEIL & SPP & PSPB & SPB62 & PAL) ND PB OFF DEP FUEL LO FRM TP A0 A1.
  assert (INU : In (U, 64) LB) by (eapply perm_in_head; exact HPU).
  assert (IND : In (D, n) LB) by (eapply Permutation_in; [exact HPU| right; exact HD]).
  assert (UD : U <> D).
  { intros ->. pose proof (lh_nodup HI _ _ _ _ HL) as NDP.
    apply (NoDup_map_fst_perm _ _ (Permutation_sym HPU)) in NDP. rewrite NoDup_ListNoDup in NDP. cbn in NDP.
    inversion NDP; subst. apply H1. apply (in_map fst) in HD. exact HD. }
  eapply (po_body HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LB LR U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky);
    [| exact FUEL| exact PVREC| exact PS| exact HL| exact BY| exact CJ| exact ERR| exact MI| exact ST| exact ND| exact PB| exact FRM| exact A0| exact A1].
  split; [exact HPU|]. split; [split; [exact HD| split; [exact DCA| exact CAD]]|]. split; [exact LEN|]. split; [exact BLEN|].
  split; [exact CEIL|]. split; [exact LO|]. split; [split; [exact SPP| split; [exact PSPB| split; [exact SPB62| exact PAL]]]|]. split; [exact OFF|]. split; [exact DEP|].
  split; [exact TP|]. split; [eapply (lh_block_range HI); [exact HL| exact INU]|]. split; [eapply (lh_block_range HI); [exact HL| exact IND]|].
  destruct (lh_blocks_disjoint HI _ _ _ _ _ _ _ _ HL INU IND UD); lia.
Qed.


End CeilWrap.
