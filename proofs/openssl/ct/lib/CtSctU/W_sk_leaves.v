(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac ApCells ApWalkTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_list_free SctRep W_sct_leaves.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition OPENSSL_SK_NUM : Z := 0xe7798.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SK_SCT_CMP_THUNK : Z := 0x19d074.
Definition SK_SCT_COPY_THUNK : Z := 0x19d0a0.

(* [comment removed for export] *)
Definition ptrw (adr : bptr -> Z) (x : sctr bptr) : word := wz (adr (sc_blk x)).
(* [comment removed for export] *)
Definition data_block (adr : bptr -> Z) (items : list (sctr bptr)) (jb : list byte) : list cell := map C8 (map (ptrw adr) items) ++ [CB (length jb) jb].
(* [comment removed for export] *)
Definition dblk (adr : bptr -> Z) (o : option (bptr * Z)) : list block := match o with Some (q, na) => [(q, adr q, 8 * na)] | None => [] end.

Definition sk_cells (adr : bptr -> Z) (k : skr bptr) (sorted : Z) : list cell :=
  [C4 (wz (sk_num k)); C4 (wz 0); C8 (wz (optr adr (sk_data k))); C4 (wz sorted); C4 (wz (olen (sk_data k)));
   C8 (wz 0); C8 (wz SK_SCT_CMP_THUNK); C8 (wz SK_SCT_FREEFUNC_THUNK); C8 (wz SK_SCT_COPY_THUNK)].

Lemma sk_cells_size : forall adr k sorted, Z.of_nat (cells_size (sk_cells adr k sorted)) = STACK_SIZE.
Proof. intros. reflexivity. Qed.

Lemma data_block_size : forall adr items jb, Z.of_nat (cells_size (data_block adr items jb)) = 8 * zlength items + Z.of_nat (length jb).
Proof.
  intros adr items jb. unfold data_block, zlength. rewrite cells_size_app. cbn [cells_size csize]. rewrite <- (length_map (ptrw adr) items).
  generalize (map (ptrw adr) items) as l. intros l.
  replace (cells_size (map C8 l)) with (8 * length l)%nat; [lia|].
  induction l as [|w t IH]; [reflexivity|]. cbn [map cells_size csize length]. cbn [map cells_size] in IH. lia.
Qed.

Local Notation mem := (word -> option byte).

Section WithCeiling. Context {CE__ : Ceiling}.

Definition sk_rep (m : mem) (L : list block) (adr : bptr -> Z) (k : skr bptr) : Prop :=
  In (sk_blk k, adr (sk_blk k), STACK_SIZE) L
  /\ (exists sorted, 0 <= sorted <= 1 /\ rw_cells ctusegs m (adr (sk_blk k)) (sk_cells adr k sorted))
  /\ match sk_data k with
     | Some (q, na) => In (q, adr q, 8 * na) L /\ sk_num k <= na /\ SK_MIN_NODES <= na < 2^23
                       /\ exists jb, Z.of_nat (length jb) = 8 * (na - sk_num k) /\ rw_cells ctusegs m (adr q) (data_block adr (sk_items k) jb)
     | None => sk_items k = []
     end
  /\ Forall (sct_rep m L adr) (sk_items k)
  /\ List.NoDup (map blk_id (scts_blocks adr (sk_items k) ++ dblk adr (sk_data k) ++ [(sk_blk k, adr (sk_blk k), STACK_SIZE)])).

(* [comment removed for export] *)
Lemma sk_rep_scts : forall m L adr k, sk_rep m L adr k -> scts_rep m L adr (sk_items k).
Proof.
  intros m L adr k (_ & _ & _ & HF & ND). split; [exact HF|]. rewrite map_app in ND. exact (proj2 (proj2 (NoDup_app_split _ _ ND))).
Qed.

Lemma data_cells_of_block : forall m adr D i items junk,
  rw_cells ctusegs m (D + 8 * i) (data_block adr items junk) -> data_cells m adr D i items.
Proof.
  intros m adr D i items junk. revert i. induction items as [|x t IH]; intros i H; cbn; [exact I|].
  unfold data_block in H. cbn [map app] in H. change (C8 (ptrw adr x) :: map C8 (map (ptrw adr) t) ++ [CB (length junk) junk]) with ([C8 (ptrw adr x)] ++ data_block adr t junk) in H.
  apply rw_cells_app in H. destruct H as [H1 H2]. split; [exact (proj1 H1)|]. apply IH. cbn [cells_size csize Nat.add] in H2.
  replace (D + 8 * (i + 1)) with (D + 8 * i + Z.of_nat 8) by lia. exact H2.
Qed.

(* [comment removed for export] *)
Lemma data_block_nth : forall m adr D items junk (i : nat) x,
  rw_cells ctusegs m D (data_block adr items junk) -> nth_error items i = Some x ->
  ro_cells ctusegs m (D + 8 * Z.of_nat i) [C8 (ptrw adr x)].
Proof.
  intros m adr D items junk i x H Hn.
  pose proof (data_cells_of_block m adr D 0 items junk ltac:(rewrite Z.mul_0_r, Z.add_0_r; exact H)) as DC.
  revert DC Hn. generalize 0 as i0. revert i. induction items as [|y t IH]; intros [|i] i0 DC Hn; cbn in Hn; [discriminate| discriminate| |].
  - injection Hn; intros ->. cbn in DC. rewrite Z.add_0_r. Abort.

Lemma data_cells_nth : forall m adr D items (i0 : Z) (i : nat) x,
  data_cells m adr D i0 items -> nth_error items i = Some x -> ro_cells ctusegs m (D + 8 * (i0 + Z.of_nat i)) [C8 (ptrw adr x)].
Proof.
  intros m adr D items. induction items as [|y t IH]; intros i0 [|i] x DC Hn; cbn in Hn; [discriminate| discriminate| |]; cbn in DC; destruct DC as [D1 D2].
  - injection Hn; intros ->. rewrite Z.add_0_r. exact D1.
  - replace (i0 + Z.of_nat (S i)) with ((i0 + 1) + Z.of_nat i) by lia. apply IH; [exact D2| exact Hn].
Qed.

Lemma data_block_nth : forall m adr D items junk (i : nat) x,
  rw_cells ctusegs m D (data_block adr items junk) -> nth_error items i = Some x ->
  ro_cells ctusegs m (D + 8 * Z.of_nat i) [C8 (ptrw adr x)].
Proof.
  intros m adr D items junk i x H Hn.
  pose proof (data_cells_of_block m adr D 0 items junk ltac:(rewrite Z.mul_0_r, Z.add_0_r; exact H)) as DC.
  replace (Z.of_nat i) with (0 + Z.of_nat i) by lia. eapply data_cells_nth; [exact DC| exact Hn].
Qed.

(* [comment removed for export] *)
Lemma sk_rep_free_view : forall m L adr k, sk_rep m L adr k ->
  st_cells m (adr (sk_blk k)) (sk_num k) (optr adr (sk_data k))
  /\ In (sk_blk k, adr (sk_blk k), STACK_SIZE) L
  /\ match sk_data k with Some (q, na) => In (q, adr q, 8 * na) L /\ sk_num k <= na | None => sk_items k = [] end
  /\ data_cells m adr (optr adr (sk_data k)) 0 (sk_items k) /\ Forall (sct_ptr_cells m adr) (sk_items k)
  /\ Forall (fun b => In b L) (scts_blocks adr (sk_items k))
  /\ List.NoDup (map blk_id (scts_blocks adr (sk_items k) ++ oblk adr (sk_data k) ++ [(sk_blk k, adr (sk_blk k), STACK_SIZE)])).
Proof.
  intros m L adr k (HIN & (sorted & SR & HC) & HD & HF & ND).
  split.
  { unfold st_cells, SKO_DATA, SKO_FREE_THUNK. unfold sk_cells in HC.
    lazymatch type of HC with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) with ([c0] ++ [c1] ++ [c2] ++ [c3; c4; c5; c6] ++ [c7] ++ rest) in HC end.
    apply rw_cells_app in HC. destruct HC as [H0 HC]. apply rw_cells_app in HC. destruct HC as [_ HC]. apply rw_cells_app in HC. destruct HC as [H2 HC].
    apply rw_cells_app in HC. destruct HC as [_ HC]. apply rw_cells_app in HC. destruct HC as [H7 _]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in *.
    rewrite <- ?Z.add_assoc in *. cbn [Z.add Pos.add Pos.succ] in *.
    split; [exact (proj1 H0)|]. split; [exact (proj1 H2)| exact (proj1 H7)]. }
  split; [exact HIN|].
  split. { destruct (sk_data k) as [[q na]|]; [| exact HD]. destruct HD as (H1 & H2 & _ & _). split; [exact H1| exact H2]. }
  split. { destruct (sk_data k) as [[q na]|]; cbn [optr].
           - destruct HD as (_ & _ & _ & junk & _ & HB). eapply data_cells_of_block. rewrite Z.mul_0_r, Z.add_0_r. exact HB.
           - rewrite HD. exact I. }
  split. { eapply Forall_impl; [| exact HF]. intros x Hx. eapply sct_rep_ptr_cells. exact Hx. }
  split. { clear - HF. induction (sk_items k) as [|x t IH]; cbn; [constructor|]. inversion HF; subst. apply Forall_app. split; [| apply IH; assumption].
           apply Forall_forall. intros b Hb. eapply sct_rep_blocks_in; [eassumption| exact Hb]. }
  destruct (sk_data k) as [[q na]|]; cbn [dblk oblk] in ND; [| exact ND]. revert ND. rewrite !map_app. cbn [map blk_id fst snd app]. intros ND. exact ND.
Qed.

(* [comment removed for export] *)
Lemma OPENSSL_sk_num_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo SA num : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  (0 < SA /\ SA + STACK_SIZE <= lo)%Z -> SA mod 8 = 0 ->
  ro_cells ctusegs m SA [C4 (wz num)] -> (0 <= num < 2^31)%Z ->
  a0 = wz SA ->
  evt ctusegs (nid_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m num)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz OPENSSL_SK_NUM) fc None m (seg_rom ctusegs)).
Proof.
  intros until num. intros ST MI GLO LO HA AL8 HN Hn ->. unfold GLOBALS_TOP in GLO.
  unfold OPENSSL_SK_NUM, STACK_SIZE, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (SEPA : SA + 56 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= SA) by lia.
  carve_frame 16%nat ST. do 4 step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  step. uchk.
  step. step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
  setreg 10%Z (Z_to_bv 64 num) ltac:(symmetry; apply bv_eq; rewrite ?sx32_small, ?unsigned_lit by lia; reflexivity).
  finish.
Qed.

(* [comment removed for export] *)
Lemma OPENSSL_sk_value_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo SA num D i V : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  (0 < SA /\ SA + STACK_SIZE <= lo)%Z -> (0 < D /\ D + 8 * num <= lo)%Z -> SA mod 8 = 0 -> D mod 8 = 0 ->
  ro_cells ctusegs m SA [C4 (wz num)] -> ro_cells ctusegs m (SA + SKO_DATA) [C8 (wz D)] -> (0 <= i < num)%Z -> (num < 2^31)%Z ->
  ro_cells ctusegs m (D + 8 * i) [C8 (wz V)] ->
  a0 = wz SA -> a1 = wz i ->
  evt ctusegs (nid_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m V)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz OPENSSL_SK_VALUE) fc None m (seg_rom ctusegs)).
Proof.
  intros until V. intros ST MI GLO LO HA HDR AL8 AL8D HN HD Hi Hn HV -> ->. unfold GLOBALS_TOP in GLO.
  unfold OPENSSL_SK_VALUE, STACK_SIZE, SKO_DATA, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (SEPA : SA + 56 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= SA) by lia.
  assert (SEPD : D + 8 * num <= bv_unsigned sp - 16 \/ bv_unsigned sp <= D) by lia.
  remember (D + 8 * i) as Di eqn:EDi.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 step.
  step.
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
  step. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?signed_small, ?unsigned_lit by lia; lia|]. clear K1.
  step. uchk.
  step.
  step. if_cases K2; zify_cond K2; [exfalso; revert K2; rewrite ?sx32_small, ?signed_small, ?unsigned_lit by lia; lia|]. clear K2.
  step. step. step.
  setreg 10%Z (Z_to_bv 64 Di) ltac:(symmetry; apply bv_eq; subst Di; rewrite ?unsigned_lit by lia; bv_solve).
  ub.
  step. step. step.
  do 3 step. release_frame FR ST (bv_unsigned sp). step.
  finish.
Qed.
End WithCeiling.
