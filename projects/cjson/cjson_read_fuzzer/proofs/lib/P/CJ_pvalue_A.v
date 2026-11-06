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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_facts3.
Module CJ_pvalue_lemmas.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
  rw_cells psegs m A (cs1 ++ cs2) <-> rw_cells psegs m A cs1 /\ rw_cells psegs m (A + Z.of_nat (cells_size cs1)) cs2.
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
  rw_cells psegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells psegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf HB] HW] Hwf' HE. split; [split; [exact Hwf'| rewrite HE; exact HB]|].
  rewrite <- (cells_bytes_length cs' Hwf'), HE, (cells_bytes_length cs Hwf). exact HW.
Qed.

(* [comment removed for export] *)
Lemma zero_node_cells : forall m A,
  rw_cells psegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells psegs m A (node_cells 0 (wz 0) 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0).
Proof. intros m A H. eapply rw_cells_recell; [exact H| cbn; repeat split; exact I| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma zero_node_cells_prev : forall m A pv,
  rw_cells psegs m A [C8 (Z_to_bv 64 0); C8 pv; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells psegs m A (node_cells 0 pv 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0).
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
    munch [(p + 8, p + 16)] m m' -> wmono psegs m m' ->
    (forall nx pv ch ty p1 vs vi p2 vd ky, rw_cells psegs m p (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
                                          rw_cells psegs m' p (node_cells nx pv' ch ty p1 vs vi p2 vd ky)) ->
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
    munch [(p + 8, p + 16)] m m' -> wmono psegs m m' ->
    rw_cells psegs m' p (node_cells nx pv' ch ty p1 vs vi p2 vd ky) ->
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
  rw_cells psegs m q (node_cells nx pv ch ty p1 vs vi p2 vd 0) ->
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

Lemma lit_null_at : forall m, mem_inv psegs m -> bytes_at psegs m LIT_NULL lit_null.
Proof. intros m MI. apply (ro_bytes_at psegs m LIT_NULL lit_null MI); [unfold LIT_NULL; lia| cbn; unfold LIT_NULL; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma lit_false_at : forall m, mem_inv psegs m -> bytes_at psegs m LIT_FALSE lit_false.
Proof. intros m MI. apply (ro_bytes_at psegs m LIT_FALSE lit_false MI); [unfold LIT_FALSE; lia| cbn; unfold LIT_FALSE; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma lit_true_at : forall m, mem_inv psegs m -> bytes_at psegs m LIT_TRUE lit_true.
Proof. intros m MI. apply (ro_bytes_at psegs m LIT_TRUE lit_true MI); [unfold LIT_TRUE; lia| cbn; unfold LIT_TRUE; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

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

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_lemmas CJ_pvalue_lemmas.
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
    /\ (bv_unsigned sp <= P /\ P + 56 <= SPB /\ SPB < 2^62)
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
       Fx (Z_to_bv 64 pc) fcx None mm (seg_rom psegs).

  Definition MIDV (m1 : word -> option byte) (mo1 : Model) (LB1 : list cblock) (errv1 : word) : Prop :=
    LHEAP HI SPB LB1 m1 mo1 /\ bytes_at psegs m1 CA bs /\ CJST m1 /\ rw_cells psegs m1 PERRNO [C4 errv1]
    /\ mem_inv psegs m1 /\ stk psegs m1 lo (bv_unsigned sp + -144) /\ ppres LR (bv_unsigned sp) P m m1.

  Lemma pvc_lits :
    Permutation ((U, 64) :: LR) LB /\ (In (D, n) LR /\ D <= CA /\ CA + blen <= D + n)
    /\ Z.of_nat (length bs) = blen /\ blen < 2^31
    /\ alloc_ceiling <= lo /\ lo <= bv_unsigned sp - (144 * (1001 - depth) + 16384)
    /\ (bv_unsigned sp <= P /\ P + 56 <= SPB /\ SPB < 2^62)
    /\ 0 <= off <= blen /\ 0 <= depth <= 1000 /\ tp = wz PTP
    /\ (0 < U /\ U mod 16 = 0 /\ 0 <= 64 /\ U + 64 <= alloc_ceiling /\ (U + 64 <= 0x10000 \/ 0x55000 <= U))
    /\ (0 < D /\ D mod 16 = 0 /\ 0 <= n /\ D + n <= alloc_ceiling /\ (D + n <= 0x10000 \/ 0x55000 <= D))
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
    rw_cells psegs mm (bv_unsigned sp + -144) (CB 80 junk :: SAVEDV) ->
    evt psegs (fun ms' => ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                                 Fx (ret_pc ra) fcx None mm (seg_rom psegs))
        (CSTV 0x12e70 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 Fx fcx mm).
  Proof.
    intros. lits. unfold CSTV, SAVEDV in *.
    do 10 zstep. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ret0_tail : forall (junk : list byte) (off1 depth1 : Z) m1 mo1 LB1 errv1 Fx fcx
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    MIDV m1 mo1 LB1 errv1 -> Permutation ((U, 64) :: LR) LB1 ->
    rw_cells psegs m1 (bv_unsigned sp + -144) (CB 80 junk :: SAVEDV) ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    SCPS psegs POSTV (CSTV 0x12e6c x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 Fx fcx m1) mo1.
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
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree.
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

Definition DELETE_ENTRY : Z := 0x12720.
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
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ CJST m'
    /\ rw_cells psegs m' PERRNO [C4 errv]
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
    stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - DELETE_STACK d ->
    rw_cells psegs m PERRNO [C4 errv] ->
    mem_inv psegs m ->
    tp = wz PTP ->
    a0 = wz p ->
    SCPS psegs (delete_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (LHEAP HI) SPB LR lo errv m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz DELETE_ENTRY) fc None m (seg_rom psegs)) mo.

  (* [comment removed for export] *)
  Lemma cj_pres_store_block : forall SPB LB m mo A n R (L : list cblock) SP lo' hi' m1 m2,
    LHEAP HI SPB LB m mo -> Permutation ((A, n) :: R) LB ->
    (forall b, In b L -> In b R) -> alloc_ceiling <= SP ->
    munch [(lo', hi')] m1 m2 -> wmono psegs m1 m2 -> A <= lo' -> hi' <= A + n ->
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
    Notation S2V := (Z_to_bv 64 0x2373c).
    Notation POST := (delete_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (LHEAP HI) SPB LR lo errv m0).
    Notation FRAME mm := (rw_cells psegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).

    (* [comment removed for export] *)
    Definition linv (LBX : list cblock) (m : word -> option byte) (mo : Model) : Prop :=
      LHEAP HI SPB LBX m mo /\ stk psegs m lo SP1 /\ FRAME m /\ CJST m
      /\ rw_cells psegs m PERRNO [C4 errv] /\ mem_inv psegs m /\ cj_pres LR (bv_unsigned sp) m0 m.

    (* [comment removed for export] *)
    Notation LST pc rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mm :=
      (MS (mkR rav (Z_to_bv 64 SP1) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 S2V s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

    (* [comment removed for export] *)
    Definition TestSpec (n : nat) : Prop :=
      forall (d : nat) (p : Z) (B LBX : list cblock) (m : word -> option byte) (mo : Model)
             (rav t0 t1 t2 s1v a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      (length B <= n)%nat -> (d <= dk)%nat ->
      lo <= bv_unsigned sp - DELETE_STACK d ->
      cj_chain T m d p B -> Permutation (B ++ LR) LBX -> linv LBX m mo ->
      SCPS psegs POST (LST 0x12750 rav t0 t1 t2 (Z_to_bv 64 p) s1v a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m) mo.

    Lemma SP1eq : bv_unsigned (Z_to_bv 64 SP1) = SP1.
    Proof. apply unsigned_lit. try rewrite alloc_ceiling_eq in CEIL. unfold RMALLOC_STACK in LO1. lia. Qed.

    (* [comment removed for export] *)
    Lemma loop_exit : forall LBX m mo rav t0 t1 t2 s1v a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      Permutation LR LBX -> linv LBX m mo ->
      SCPS psegs POST (LST 0x12750 rav t0 t1 t2 (Z_to_bv 64 0) s1v a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m) mo.
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
        rw_cells psegs m p (node_cells nx pv ch ty p1 vs' vi p2 vd ky') ->
        cj_chain T m (S d0) nx Bn ->
        SCPS psegs POST (LST 0x12744 rav t0 t1 t2 (Z_to_bv 64 nx) (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m) mo.
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
        replace (ret_pc (Z_to_bv 64 0x12750)) with (Z_to_bv 64 0x12750) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
        rw_cells psegs m p (node_cells nx pv ch ty p1 vs' vi p2 vd ky) ->
        cj_str m ky Bk -> cj_chain T m (S d0) nx Bn ->
        SCPS psegs POST (LST 0x12798 rav t0 t1 t2 (Z_to_bv 64 nx) (Z_to_bv 64 p) a0 (Z_to_bv 64 ty) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m) mo.
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
          replace (ret_pc (Z_to_bv 64 0x127b0)) with (Z_to_bv 64 0x127b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
          pose proof (munch_refl [(p + 56, p + 64)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
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
        rw_cells psegs m p (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
        cj_str m vs Bv -> cj_str m ky Bk -> cj_chain T m (S d0) nx Bn ->
        SCPS psegs POST (LST 0x12778 rav t0 t1 t2 (Z_to_bv 64 nx) (Z_to_bv 64 p) a0 (Z_to_bv 64 ty) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m) mo.
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
          replace (ret_pc (Z_to_bv 64 0x12790)) with (Z_to_bv 64 0x12790) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
          pose proof (munch_refl [(p + 32, p + 40)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
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
        rw_cells psegs m p (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
        cj_str m vs Bv -> cj_str m ky Bk -> cj_chain T m d0 ch Bc -> cj_chain T m (S d0) nx Bn ->
        SCPS psegs POST (LST 0x12754 rav t0 t1 t2 (Z_to_bv 64 p) s1v a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m) mo.
      Proof.
        intros until t6. intros HP LI ND SV SK CHC CHN. (nelimp LI 7%nat; intros HL ST FR CJ ERR MI PR).
        pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL. unfold RMALLOC_STACK in LO1. pose proof SP1eq as E1.
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 R2 R3 R4 R5).
        try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
        (nelimp (cj_chain_ptr_range _ _ _ _ _ CHC) 3%nat; intros CR1 CR2 CR3).
        pose proof ND as ND'. unfold node_cells in ND.
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
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
          replace (ret_pc (Z_to_bv 64 0x12774)) with (Z_to_bv 64 0x12774) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
    munch [(lo', hi')] m1 m2 -> wmono psegs m1 m2 -> alloc_ceiling <= lo' -> hi' <= SP ->
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
    destruct (Z.eq_dec p 0) as [->|PNZ].
    - (* [comment removed for export] *)
      pose proof (cj_chain_null_inv _ _ _ _ CH) as ->. cbn [app] in HP.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
      step. apply evt_done. apply scps_done. unfold delete_post.
      nexists 17%nat. split; [reflexivity|].
      split; [exact MI|]. split; [exact ST|]. split; [exact CJ|]. split; [exact ERR|].
      split; [exact HL|]. split; [apply Permutation_sym; exact HP| apply cj_pres_refl].
    - (nelim (cj_chain_cons_inv _ _ _ _ _ CH PNZ) 24%nat; intros d0 nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn -> ND TY _ SV SK CHC CHN ->)
.
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 R2 R3 R4 R5).
      try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
      assert (LO1 : lo <= bv_unsigned sp - 32 - RMALLOC_STACK).
      { unfold DELETE_STACK, RMALLOC_STACK in *. lia. }
      unfold RMALLOC_STACK in LO1.
      pose proof CJ as (HK & (e1 & e2 & GE) & LC). unfold PHOOKS in HK. unfold PGERROR in GE. unfold PLCONV in LC. unfold PERRNO in ERR.
      unfold node_cells in ND.
      pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      step. if_cases K; zify_cond K; [exfalso; exact (PNZ K)|]. clear K.
      carve_frame 32%nat ST.
      step. step. step. step. step. step. step. step.
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
Module CJ_pwlopts_A.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_skipws CJ_delete OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_lemmas CJ_pvalue_lemmas.
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
  munch W m1 m2 -> wmono psegs m1 m2 -> (forall a, 0 <= a < 2^64 -> doc_addr LB SP a -> outside W a) -> dpres LB SP m1 m2.
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
    /\ tp = wz PTP /\ cblock_range D n.
  Hypothesis WLC : wl_pure.

  Notation SP := (bv_unsigned sp).
  Definition DPOST := parse_doc_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LB CA bs lo m.

  (* [comment removed for export] *)
  Definition CSTW (pc : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word)
      (Fx : bvmap 5 word) (fcx : bv 32) (mm : word -> option byte) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
       Fx (Z_to_bv 64 pc) fcx None mm (seg_rom psegs).

  Definition FRS (mm : word -> option byte) : Prop :=
    rw_cells psegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition MIDW (m1 : word -> option byte) (mo1 : Model) (LB1 : list cblock) (errv1 : word) : Prop :=
    LHEAP HI SPB LB1 m1 mo1 /\ bytes_at psegs m1 CA bs /\ CJST m1 /\ rw_cells psegs m1 PERRNO [C4 errv1]
    /\ mem_inv psegs m1 /\ stk psegs m1 lo (bv_unsigned sp + -112) /\ dpres LB (bv_unsigned sp) m m1.

  Lemma wlc_lits :
    (In (D, n) LB /\ D <= CA /\ CA + blen <= D + n) /\ 0 < CA
    /\ Z.of_nat (length bs) = blen /\ blen < 2^31
    /\ alloc_ceiling <= lo /\ lo <= SP - (112 + (144 * (1001 - 0) + 16384))
    /\ SP <= SPB /\ SPB < 2^62 /\ tp = wz PTP
    /\ (0 < D /\ D mod 16 = 0 /\ 0 <= n /\ D + n <= alloc_ceiling /\ (D + n <= 0x10000 \/ 0x55000 <= D))
    /\ 0 <= SP < 2^64.
  Proof.
    pose proof WLC as H. unfold wl_pure, cblock_range, PARSE_DOC_STACK, PARSE_STACK, PIMG_LO, PIMG_HI in H. try rewrite alloc_ceiling_eq in H.
    pose proof (bv_unsigned_in_range 64 sp) as R. change (bv_modulus 64) with (2^64) in R.
    (nelim H 10%nat; intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10).
    repeat (split; [assumption|]). exact R.
  Qed.

  Ltac lits := (nelimp wlc_lits 11%nat; intros HDn CA0 LEN BLEN CEIL LO SPSPB SPB62 TP DRNG SPR).
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
    rw_cells psegs mm (SP + -112) [CB 8 j] ->
    rw_cells psegs mm (SP + -104) [C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7] ->
    FRS mm ->
    rw_cells psegs mm (SP + -112) [CB 8 j; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
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
    evt psegs (fun ms' => ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                                 Fx (ret_pc ra) fcx None mm (seg_rom psegs))
        (CSTW 0x12a44 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 Fx fcx mm).
  Proof.
    intros. lits. unfold CSTW, FRS in *.
    do 8 zstep. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma doc_fail_tail : forall (j : list byte) (c1 c2 c3 c4 c5 c6 c7 pos : word) m1 mo1 LB1 errv1 Fx fcx
      x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31,
    MIDW m1 mo1 LB1 errv1 -> Permutation LB1 LB ->
    rw_cells psegs m1 (SP + -112) [CB 8 j] ->
    rw_cells psegs m1 (SP + -104) [C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7] ->
    FRS m1 ->
    Fagree F Fx -> frm0 fcx ->
    SCPS psegs DPOST (CSTW 0x12a08 x1 x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 CA) x10 pos x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 PGERROR) x20 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HP1 FJ PB FS FA FRM. lits. unfold CSTW.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. unfold PERRNO in ERR. unfold FRS in FS.
    pose proof CJ as (HK & (e1 & e2 & GE) & LC). unfold PHOOKS in HK. unfold PGERROR in GE. unfold PLCONV in LC. unfold PGERROR.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. if_true.
    pose proof (munch_refl [(0x337b0, 0x337b0 + 16)] m1) as MU. pose proof (wmono_refl psegs m1) as WM.
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
    rw_cells psegs m1 (SP + -112) [CB 8 j] ->
    rw_cells psegs m1 (SP + -104) [C8 c; C8 lw; C8 ow; C8 d; C8 h1; C8 h2; C8 h3] ->
    FRS m1 ->
    Fagree F Fx -> frm0 fcx ->
    SCPS psegs DPOST (CSTW 0x129ec x1 x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 CA) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 PGERROR) x20 x28 x29 x30 x31 Fx fcx m1) mo1.
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
    rw_cells psegs m1 (SP + -112) [CB 8 j] ->
    rw_cells psegs m1 (SP + -104) [C8 c; C8 lw; C8 ow; C8 d; C8 h1; C8 h2; C8 h3] ->
    FRS m1 ->
    Fagree F Fx -> frm0 fcx ->
    SCPS psegs DPOST (CSTW 0x129e0 x1 x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 CA) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 item) (Z_to_bv 64 PGERROR) x20 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HPB CH Hdd FJ PB FS FA FRM. lits. unfold CSTW.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. unfold FRS in FS.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. zstep.
    replace (ret_pc (Z_to_bv 64 0x12720)) with (wz DELETE_ENTRY) by (unfold wz, DELETE_ENTRY; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply scps_bind.
    { pose proof (cjson_delete_spec HI dd) as DS. unfold delete_spec_at in DS.
      eapply DS with (lo := lo); clear DS; rewrite ?unsigned_lit by lia;
        first [ exact HL | exact CH | exact HPB | exact CJ | exact ST | exact ERR | exact MI | exact TP | reflexivity | alia ]. }
    cbv beta. intros ms2 mo2 PO'.
    (nelim PO' 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 LR2 -> MI2 ST2 CJ2 ERR2 HL2 HP2 PR2)
.
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x129e8)) with (Z_to_bv 64 0x129e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
    rw_cells psegs m1 item (node_cells 0 (wz 0) ch ty p1 vs vi p2 vd 0) ->
    rw_cells psegs m1 (SP + -112) [CB 8 j] ->
    rw_cells psegs m1 (SP + -104) [C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7] ->
    FRS m1 ->
    Fagree F Fx -> frm0 fcx ->
    SCPS psegs DPOST (CSTW 0x12a2c x1 x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 CA) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 item) x19 x20 x28 x29 x30 x31 Fx fcx m1) mo1.
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
      x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells psegs m1 (SP + -104) (pbuf_cells CA blen i dp) -> bytes_at psegs m1 CA bs -> mem_inv psegs m1 ->
    munch [(SP + -88, SP + -80)] m0 m1 -> wmono psegs m0 m1 ->
    evt psegs (fun ms' => exists x14' m2,
                 ms' = CSTW 0x129d0 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 CA) (Z_to_bv 64 (fin blen bs i)) (Z_to_bv 64 blen) (Z_to_bv 64 32) x14' x15 x16 x17
                          x18 x19 x20 x28 x29 x30 x31 Fx fcx m2
                 /\ rw_cells psegs m2 (SP + -104) (pbuf_cells CA blen (fin blen bs i) dp) /\ bytes_at psegs m2 CA bs /\ mem_inv psegs m2
                 /\ munch [(SP + -88, SP + -80)] m0 m2 /\ wmono psegs m0 m2)
        (CSTW 0x1298c x1 x5 x6 x7 x8 x9 (Z_to_bv 64 CA) (Z_to_bv 64 i) (Z_to_bv 64 blen) (Z_to_bv 64 32) x14 x15 x16 x17
             x18 x19 x20 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. lits.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (rw_cells_bound psegs _ _ _ PB) as PBB. rewrite pbuf_cells_size in PBB.
    unfold pbuf_cells, wz in PB. unfold CSTW.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hn; [| apply nth_error_None in Hn; lia].
    pose proof (u8ro_read psegs _ CA bs i b _ BY Hn ltac:(lia) eq_refl) as RD.
    pose proof (byte_range b) as Rb.
    assert (SEP : CA + blen <= SP + -104 \/ SP + -104 + 56 <= CA) by lia.
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
    item <> 0 -> rw_cells psegs m1 item (node_cells 0 (wz 0) ch ty (wz 0) vs vi (wz 0) vd 0) ->
    CJ_PRINTABLE ty -> cj_str m1 vs Bv -> cj_chain CJ_PRINTABLE m1 dc ch Bc -> (dc <= 1000)%nat ->
    rw_cells psegs m1 (SP + -112) [CB 8 j] ->
    rw_cells psegs m1 (SP + -104) (pbuf_cells CA blen off1 0) -> 0 <= off1 <= blen ->
    FRS m1 ->
    Fagree F Fx -> frm0 fcx ->
    SCPS psegs DPOST (CSTW 0x12970 x1 x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 CA) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 item) (Z_to_bv 64 PGERROR) rnt x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros MIDm HPB NZ ND HT SV CH Hdc FJ PB Ho FS FA FRM. lits. unfold CSTW.
    (nelimp MIDm 7%nat; intros HL BY CJ ERR MI ST PR).
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
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
    assert (JOIN : forall x13' x14' m2,
      rw_cells psegs m2 (SP + -104) (pbuf_cells CA blen (skipws_off bs off1) 0) -> bytes_at psegs m2 CA bs -> mem_inv psegs m2 ->
      munch [(SP + -88, SP + -80)] m1 m2 -> wmono psegs m1 m2 ->
      evt psegs (fun ms' => SCPS psegs DPOST ms' mo1)
        (CSTW 0x129d0 x1 x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 CA) (Z_to_bv 64 CA) (Z_to_bv 64 (skipws_off bs off1)) (Z_to_bv 64 blen) x13' x14' x15 x16 x17
             (Z_to_bv 64 item) (Z_to_bv 64 PGERROR) rnt x28 x29 x30 x31 Fx fcx m2)).
    { intros x13' x14' m2 PB2 BY2 MI2 MU2 WM2. unfold CSTW.
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
      pose proof (rw_cells_bound psegs _ _ _ PB2) as PBB2. rewrite pbuf_cells_size in PBB2. unfold pbuf_cells, wz in PB2.
      assert (O2 : off1 <= skipws_off bs off1 <= blen).
      { destruct (Z.eq_dec off1 blen) as [E|NE].
        - rewrite skipws_off_noop by lia. lia.
        - pose proof (skipws_off_range bs off1) as OR. rewrite LEN in OR. lia. }
      set (o2 := skipws_off bs off1) in *.
      zstep. if_cases Kend; zify_cond Kend.
      { apply evt_done. eapply doc_fail_delete; [exact MID2| | eapply cj_chain_any; exact CHR2| lia| exact FJ2| exact PB2| exact FS2| exact FA| exact FRM]. exact HPB. }
      zstep.
      (nelim (text_read m2 CA bs o2 (Z_to_bv 64 (CA + o2)) BY2 ltac:(lia) ltac:(lia) eq_refl) 4%nat; intros b Hb RD _).
      pose proof (byte_range b) as Rb.
      zstep. zstep. if_cases K0; zify_cond K0.
      { apply evt_done. eapply doc_success; [exact MID2| exact HPB'| exact CHR2| lia| exact NZ| eqcells ND2| exact FJ2| exact PB2| exact FS2| exact FA| exact FRM]. }
      apply evt_done. eapply doc_fail_delete; [exact MID2| | eapply cj_chain_any; exact CHR2| lia| exact FJ2| exact PB2| exact FS2| exact FA| exact FRM]. exact HPB. }
    zstep. if_cases Kskip; zify_cond Kskip.
    - replace (Z_to_bv 64 off1) with (Z_to_bv 64 (skipws_off bs off1)) by (rewrite skipws_off_noop by lia; reflexivity).
      eapply JOIN; [| exact BY| exact MI| apply munch_refl| apply wmono_refl]. rewrite skipws_off_noop by lia. exact PB'.
    - zstep.
      pose proof (fin_off0 blen off1 bs LEN ltac:(lia)) as FO.
      eapply evt_cut.
      { eapply (wsB (Z.to_nat (blen - off1)) off1 0 m1 m1); [lia| lia| exact PB'| exact BY| exact MI| apply munch_refl| apply wmono_refl]. }
      intros ms' nelH_; (nelim nelH_ 8%nat; intros x14' m2 -> PB2 BY2 MI2 MU2 WM2). rewrite <- FO in PB2 |- *.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg CJ_iface CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_skipws.
Import CJ_delete.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_lemmas.
Import CJ_pvalue_lemmas.
Import CJ_pvalue_ctx.
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
    rw_cells psegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    SCPS psegs POST (CST 0x12e58 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 x11 x12 x13 x14 x15 x16 x17
                         x18 (Z_to_bv 64 head) x20 x21 x22 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HPX CH Hdd FR PB ND FA FRM. lits. unfold CSTV.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (HPX' : Permutation (X ++ (U, 64) :: LR) LBX).
    { eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply Permutation_middle. }
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. zstep.
    replace (ret_pc (Z_to_bv 64 0x12720)) with (wz DELETE_ENTRY) by (unfold wz, DELETE_ENTRY; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply scps_bind.
    { pose proof (cjson_delete_spec HI dd) as DS. unfold delete_spec_at in DS.
      eapply DS with (lo := lo); clear DS; rewrite ?unsigned_lit by lia;
        first [ exact HL | exact CH | exact HPX' | exact CJ | exact ST | exact ERR | exact MI | exact TP | reflexivity | alia ]. }
    cbv beta. intros ms2 mo2 PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & LR2
                    & -> & MI2 & ST2 & CJ2 & ERR2 & HL2 & HP2 & PR2).
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x12e60)) with (Z_to_bv 64 0x12e60) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
    pose proof PB as PB'. unfold pbuf_at in PB'. apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PB'; [| left; cbn; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in ND; [| right; right; exists U, 64; split; [left; reflexivity| rewrite node_cells_size; lia]].
    apply (cj_pres_bytes_at _ _ _ _ _ _ PR2) in BY; [| right; right; exists D, n; split; [right; apply (proj1 HDn)| lia]].
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
    zstep. zstep.
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
    rw_cells psegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
    pbuf_at m1 P CA blen o2 depth ->
    rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off <= o2 < blen ->
    Fagree F Fx -> frm0 fcx ->
    SCPS psegs POST (CST 0x12bec x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 (Z_to_bv 64 o2) x12 x13 x14 x15 x16 x17
                         x18 x19 x20 (Z_to_bv 64 head) x22 x28 x29 x30 x31 Fx fcx m1) mo1.
  Proof.
    intros until x31. intros (HL & BY & CJ & ERR & MI & ST & PR) HPX CH Hd FR PB ND Ho FA FRM. lits. unfold CSTV.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound psegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold PERRNO in ERR. unfold SAVEDV in FR.
    assert (INU : In (U, 64) LBX) by (eapply perm_in_head; exact HPX).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    (* [comment removed for export] *)
    pose proof (munch_refl [(U + 16, U + 28)] m1) as MU. pose proof (wmono_refl psegs m1) as WM.
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
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
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
          /\ rw_cells psegs m1 cur (node_cells 0 pvc chc tyc p1c vsc vic p2c vdc 0)
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
      rw_cells psegs m1 (SP + -144) (CB 80 junk :: SAVED) ->
      pbuf_at m1 P CA blen o (depth + 1) ->
      rw_cells psegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      SCPS psegs POST (CST 0x12da0 x1 x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 U) x10 x11 x12 x13 x14 x15 x16 x17
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
