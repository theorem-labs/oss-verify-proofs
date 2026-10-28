(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire CtModel ApBase ApState ApErr ApParse ApBridge.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Monad ProgG Stdio.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac ApErrKit3 ApIface W_get_object W_check_tlen W_item_d2i_stmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASN1_COLLECT : Z := 0x11300c.
Definition BUF_GROW_CLEAN : Z := 0x1178ec.
Definition CLEAR_REALLOC : Z := 0xe9e88.
Definition MEMCPY : Z := 0x2bd77c.
Definition MEMSET_F : Z := 0x2781a0.
(* [comment removed for export] *)
Definition A_TASN_DEC_C : Z := 0x1ae18.
Definition A_ASN1_ITEM_EMBED_D2I : Z := 0x26a87.
Definition A_ASN1_D2I_EX_PRIMITIVE : Z := 0x27ce5.
Definition A_ASN1_COLLECT : Z := 0x3147d.
Definition A_BUFFER_C : Z := 0x11d70.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition GROW_STACK : Z := 112 + CRYPTO_MALLOC_STACK.
(* [comment removed for export] *)
Definition COLLECT_FRAME : Z := 144.
Definition COLLECT_STACK : Z := COLLECT_FRAME + CHECK_TLEN_STACK.

Lemma grow_le_tlen : GROW_STACK <= CHECK_TLEN_STACK.
Proof. unfold GROW_STACK, CHECK_TLEN_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition buf_cells (b : bufm bptr) (A : Z) : list cell :=
  [C8 (wz (bm_len b)); C8 (wz A); C8 (wz (bm_max b)); C8 (wz 0)].
(* [comment removed for export] *)
Definition buf_blk (b : bufm bptr) (A : Z) : list block :=
  match bm_data b with Some (q, n) => [(q, A, n)] | None => [] end.

Lemma bm_max_some : forall (b : bufm bptr) q n, bm_data b = Some (q, n) -> bm_max b = n.
Proof. intros b q n H. unfold bm_max. rewrite H. reflexivity. Qed.
Lemma bm_max_none : forall (b : bufm bptr), bm_data b = None -> bm_max b = 0.
Proof. intros b H. unfold bm_max. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma magic_div3 : forall x, 0 <= x < 2 ^ 32 -> (x * 2863311531) / 2 ^ 33 = x / 3.
Proof.
  intros x Hx. pose proof (Z.div_mod x 3 ltac:(lia)) as E. pose proof (Z.mod_pos_bound x 3 ltac:(lia)) as R.
  set (q := x / 3) in *. set (r := x mod 3) in *.
  symmetry. apply Z.div_unique with (r := q + r * 2863311531); [left; nia| nia].
Qed.

(* [comment removed for export] *)
Lemma magic_div3_word : forall N, 3 <= N <= 2 ^ 30 + 3 ->
  Z.shiftl (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64
     (Z.shiftr ((bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 N)) 32))) * 12297829383904690176) 64))) 31)))) 2)))) 2
  = N / 3 * 4.
Proof.
  intros N HN.
  rewrite (unsigned_lit N) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (N * 2 ^ 32)) by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  replace (N * 2 ^ 32 * 12297829383904690176 / 2 ^ 64) with (N * 2863311531) by
    (apply Z.div_unique with (r := 0); [lia| lia]).
  rewrite (unsigned_lit (N * 2863311531)) by lia.
  assert (E33 : N * 2863311531 / 2 ^ 31 / 2 ^ 2 = N / 3).
  { rewrite Z.div_div by lia. change (2 ^ 31 * 2 ^ 2) with (2 ^ 33). apply magic_div3. lia. }
  pose proof (Z.div_mod (N * 2863311531 / 2 ^ 31) (2 ^ 2) ltac:(lia)) as DM.
  pose proof (Z.mod_pos_bound (N * 2863311531 / 2 ^ 31) (2 ^ 2) ltac:(lia)) as MB.
  assert (Q3 : 1 <= N / 3 <= 2 ^ 29) by (split; [apply Z.div_le_lower_bound; lia| apply Z.div_le_upper_bound; lia]).
  set (X := N * 2863311531 / 2 ^ 31) in *.
  assert (XB : 0 <= X < 2 ^ 32) by lia.
  rewrite (unsigned_lit X) by lia.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite Z.mod_small by lia.
  rewrite E33. rewrite swrap32_small by lia. rewrite unsigned_lit by lia. change (2 ^ 2) with 4. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma le1_lit : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64%N) with (2 ^ 64). apply mod_mod8_of_modw. lia.
Qed.

(* [comment removed for export] *)
Lemma mod8_frame : forall a b k, a mod 16 = 0 -> b mod 16 = 0 -> k mod 8 = 0 -> (a + b + k) mod 8 = 0.
Proof.
  intros a b k Ha Hb Hk.
  apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia]. apply Z.mod_divide in Hk; [|lia].
  destruct Ha as [qa Ea]. destruct Hb as [qb Eb]. destruct Hk as [qk Ek].
  apply Z.mod_divide; [lia|]. exists (2 * qa + 2 * qb + qk). lia.
Qed.

(* [comment removed for export] *)
Lemma ret_bits : forall r, r = 0 \/ r = 1 \/ r = 32 \/ r = 33 ->
  (Z.land r 1 = 0 \/ Z.land r 1 = 1) /\ (Z.land r 32 = 0 \/ Z.land r 32 = 32) /\ Z.land r 129 = Z.land r 1 /\ Z.land r 128 = 0
  /\ Z.land (Z.land r 1) 1 = Z.land r 1 /\ (Z.testbit r 0 = true <-> Z.land r 1 = 1).
Proof.
  intros r [->|[->|[->| ->]]]; (split; [first [left; reflexivity| right; reflexivity]|]); (split; [first [left; reflexivity| right; reflexivity]|]);
    (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; intros H; first [reflexivity| discriminate H]).
Qed.

(* [comment removed for export] *)
Lemma grow_size_bounds : forall len, 0 <= len <= 2 ^ 30 -> let n := (len + 3) / 3 * 4 in len < n /\ 4 <= n /\ n < 2 ^ 31.
Proof.
  intros len Hl. cbv zeta.
  pose proof (Z.div_mod (len + 3) 3 ltac:(lia)) as E. pose proof (Z.mod_pos_bound (len + 3) 3 ltac:(lia)) as R. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lb_remove_mid : forall (OW : list block) (b : block) (NEW LB : list block),
  List.NoDup (map blk_id (OW ++ (b :: NEW) ++ LB)) -> lb_remove (blk_id b) (OW ++ (b :: NEW) ++ LB) = OW ++ NEW ++ LB.
Proof.
  intros OW b NEW LB ND. rewrite map_app in ND. cbn [map app] in ND.
  assert (N1 : ~ In (blk_id b) (map blk_id OW)).
  { intros H. exact (nodup_app_disj _ _ (blk_id b) ND H ltac:(left; reflexivity)). }
  pose proof (nodup_app_r _ _ ND) as ND2. apply NoDup_cons_iff in ND2. destruct ND2 as [N2 _]. rewrite map_app in N2.
  rewrite lb_remove_app. rewrite (lb_remove_notin _ _ N1). f_equal.
  cbn [app]. rewrite lb_remove_cons, bptr_eqb_refl. rewrite lb_remove_app.
  rewrite (lb_remove_notin _ NEW) by (intros H; apply N2; apply in_app_iff; left; exact H).
  rewrite (lb_remove_notin _ LB) by (intros H; apply N2; apply in_app_iff; right; exact H). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma slice_bytes : forall m D0 d p len,
  bytes_at ctusegs m D0 (to_bytes d) -> Forall (fun c => 0 <= c < 256) d -> 0 <= p -> 0 <= len -> p + len <= zlength d ->
  bytes_at ctusegs m (D0 + p) (to_bytes (slice d p len)) /\ Z.of_nat (length (to_bytes (slice d p len))) = len.
Proof.
  intros m D0 d p len HB HF Hp Hl Hpl. unfold slice, to_bytes in *. unfold zlength in Hpl. split.
  - rewrite <- firstn_map, <- skipn_map. replace (D0 + p) with (D0 + Z.of_nat (Z.to_nat p)) by lia.
    apply bytes_at_firstn. apply bytes_at_skipn; [exact HB| rewrite length_map; lia].
  - rewrite length_map, length_firstn, length_skipn. lia.
Qed.

Lemma slice_range : forall d p len, Forall (fun c => 0 <= c < 256) d -> Forall (fun c => 0 <= c < 256) (slice d p len).
Proof.
  intros d p len HF. unfold slice. rewrite <- (firstn_skipn (Z.to_nat p) d) in HF. apply Forall_app in HF. destruct HF as [_ HF].
  rewrite <- (firstn_skipn (Z.to_nat len) (skipn (Z.to_nat p) d)) in HF. apply Forall_app in HF. destruct HF as [HF _]. exact HF.
Qed.

Lemma zlength_slice : forall d p len, 0 <= p -> 0 <= len -> p + len <= zlength d -> zlength (slice d p len) = len.
Proof. intros d p len Hp Hl H. unfold zlength. rewrite slice_length by assumption. lia. Qed.

Lemma to_bytes_app : forall a b, to_bytes (a ++ b) = to_bytes a ++ to_bytes b.
Proof. intros. unfold to_bytes. apply map_app. Qed.

Lemma zlength_app_c : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cb_split : forall m a (n1 n2 : nat) j,
  rw_cells ctusegs m a [CB (n1 + n2) j] -> rw_cells ctusegs m a [CB n1 (firstn n1 j); CB n2 (skipn n1 j)].
Proof.
  intros m a n1 n2 j H. pose proof H as [[W _] _]. cbn in W. destruct W as [L _].
  eapply rw_cells_recast; [exact H| cbn; rewrite length_firstn, length_skipn; repeat split; lia| | cbn; lia].
  cbn [cells_bytes cbytes app]. rewrite !app_nil_r. apply firstn_skipn.
Qed.

Lemma cb_join : forall m a (n1 n2 : nat) j1 j2,
  rw_cells ctusegs m a [CB n1 j1; CB n2 j2] -> rw_cells ctusegs m a [CB (n1 + n2) (j1 ++ j2)].
Proof.
  intros m a n1 n2 j1 j2 H. pose proof H as [[W _] _]. cbn in W. destruct W as (L1 & L2 & _).
  eapply rw_cells_recast; [exact H| cbn; rewrite length_app; repeat split; lia| | cbn; lia].
  cbn [cells_bytes cbytes app]. rewrite !app_nil_r. reflexivity.
Qed.

Lemma cb_byte : forall m a j, rw_cells ctusegs m a [CB 1 j] -> exists b, rw_cells ctusegs m a [C1 b].
Proof.
  intros m a j H. pose proof H as [[W _] _]. cbn in W. destruct W as [L _].
  destruct j as [|b [|]]; cbn in L; try lia. exists b.
  eapply rw_cells_recast; [exact H| cbn; auto| reflexivity| reflexivity].
Qed.

Lemma cb_len : forall m a n j, rw_cells ctusegs m a [CB n j] -> length j = n.
Proof. intros m a n j [[W _] _]. cbn in W. destruct W as [L _]. exact L. Qed.

(* [comment removed for export] *)
Lemma c8_zero_bytes : forall m a, rw_cells ctusegs m a [C8 (wz 0)] -> rw_cells ctusegs m a [C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)].
Proof. intros m a H. eapply rw_cells_recast; [exact H| cbn; auto| reflexivity| reflexivity]. Qed.
Lemma c8_zero_of_bytes : forall m a, rw_cells ctusegs m a [C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)] -> rw_cells ctusegs m a [C8 (wz 0)].
Proof. intros m a H. eapply rw_cells_recast; [exact H| cbn; auto| reflexivity| reflexivity]. Qed.

End WithCeiling0.

(* [comment removed for export] *)
Ltac cut_hd H H1 a' :=
  lazymatch type of H with rw_cells _ ?m ?A (?c0 :: ?rest) =>
    change (rw_cells ctusegs m A ([c0] ++ rest)) in H; apply rw_cells_app in H; destruct H as [H1 H];
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
