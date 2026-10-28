(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec AgentLib SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymXfer HUStartupDefs HUMainEntryDefs HUMainEntry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations. Import SX2. Import SX2S.
Import ConeCfg.

Definition is_kblob (K : kentry) : bool := match K with KBlob _ _ _ => true | _ => false end.
Definition kn_main_noblob : list kentry := List.filter (fun K => negb (is_kblob K)) kn_main.
Definition kn_rndcan : list kentry :=
  [KWord (SA (EVar 4) 0) 8 (EVar 38); KWord (SA (EVar 4) 8) 8 (EVar 39);
   KWord (SA (ELit 0) 0x331ad8) 8 (EVar 40); KWord (SA (ELit 0) 0x351b28) 8 (EVar 40)].
Definition kn_exec : list kentry := Eval vm_compute in (kn_main_noblob ++ kn_rndcan).

Definition ENVX (a0s path : list byte) (rdraw : EntryDraw) (vals : list word) : env :=
  Env (vals_ev vals) (blobs_ev (blobs0 a0s path rdraw)).
Definition valsX (sp0 : word) (a0s path : list byte) (envv : list (list byte)) (rdraw : EntryDraw) (tid : word)
    (regs0 : bvmap 5 word) : list word :=
  vals0 sp0 a0s path envv tid regs0 ++ [rndw0 rdraw; rndw1 rdraw; can rdraw].

Lemma valsX_length : forall sp0 a0s path envv rdraw tid regs0, length (valsX sp0 a0s path envv rdraw tid regs0) = 41%nat.
Proof. intros. unfold valsX, vals0. rewrite !length_app, junk_vals_length. reflexivity. Qed.

Lemma regs_exec_of_main : forall sp0 a0s path envv rdraw tid regs0,
  regs_ok (E0 sp0 a0s path envv rdraw tid regs0) sr_main regs0 ->
  regs_ok (ENVX a0s path rdraw (valsX sp0 a0s path envv rdraw tid regs0)) sr_main regs0.
Proof.
  intros sp0 a0s path envv rdraw tid regs0 HR. unfold ENVX, valsX, E0 in *.
  apply env_app_regs; [|exact HR]. unfold vals0. rewrite length_app, junk_vals_length. vm_compute. reflexivity.
Qed.

Lemma word_to_le_bytes_le_word : forall bs, length bs = 8%nat -> word_to_le_bytes 8 (le_bytes_to_word bs) = bs.
Proof. intros bs H. unfold le_bytes_to_word. apply word_to_le_bytes_of_lez; [exact H | lia]. Qed.

(* [comment removed for export] *)
Lemma kword_of_bytes : forall E M a (bs : list byte) v,
  flat E a 8 -> length bs = 8%nat ->
  (forall i, (0 <= i < 8)%Z -> M (Z_to_bv 64 (estart E a + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
  edenot E v = le_bytes_to_word bs ->
  kentry_ok RSEGS E M (KWord a 8 v).
Proof.
  intros E M a bs v Hf Hl Hb Hv. cbn [kentry_ok]. split; [lia|]. split; [exact Hf|].
  rewrite Hv, (word_to_le_bytes_le_word bs Hl).
  apply rdn_pointwise; [exact Hl | unfold flat in Hf; unfold adenot, estart in *; cbn [a_base a_off] in *;
                                    destruct a as [b k]; cbn [a_base a_off] in *; pose proof (u64_range (v_addi (edenot E b) k)); unfold v_addi; rewrite u_small by lia; lia |].
  intros j Hj. unfold adenot, estart in *. destruct a as [b k]; cbn [a_base a_off] in *.
  unfold flat in Hf. cbn [a_base a_off] in Hf. unfold estart in Hf. cbn [a_base a_off] in Hf.
  unfold v_addi. rewrite u_small by lia.
  rewrite <- (Nat2Z.id j) at 2. apply Hb. lia.
Qed.

Lemma know_exec_of_main : forall sp0 a0s path envv rdraw tid regs0 mem,
  know_ok RSEGS (E0 sp0 a0s path envv rdraw tid regs0) mem kn_main ->
  know_ok RSEGS (ENVX a0s path rdraw (valsX sp0 a0s path envv rdraw tid regs0)) mem kn_exec.
Proof.
  intros sp0 a0s path envv rdraw tid regs0 mem HK.
  set (E := E0 sp0 a0s path envv rdraw tid regs0) in HK.
  set (E' := ENVX a0s path rdraw (valsX sp0 a0s path envv rdraw tid regs0)).
  assert (HLv : length (vals0 sp0 a0s path envv tid regs0) = 38%nat)
    by (unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
  (* [comment removed for export] *)
  assert (HK1 : know_ok RSEGS E' mem kn_main_noblob).
  { unfold E', ENVX, valsX. apply env_app_know; [rewrite HLv; vm_compute; reflexivity|].
    unfold know_ok in *. unfold kn_main_noblob. apply incl_Forall with (l1 := kn_main); [|exact HK].
    intros K HKin. apply filter_In in HKin. tauto. }
  (* [comment removed for export] *)
  pose proof (know_nth RSEGS E mem kn_main ltac:(let i := eval vm_compute in (kindex (kentry_eqb (KBlob (SA (EVar 4) 0) (ELit 16) 2)) kn_main 0) in
                                              lazymatch i with Some ?j => exact j end) _ HK eq_refl) as Brnd.
  pose proof (know_nth RSEGS E mem kn_main ltac:(let i := eval vm_compute in (kindex (kentry_eqb (KBlob (SA (ELit 0) 0x331ad8) (ELit 8) 3)) kn_main 0) in
                                              lazymatch i with Some ?j => exact j end) _ HK eq_refl) as Bcan1.
  pose proof (know_nth RSEGS E mem kn_main ltac:(let i := eval vm_compute in (kindex (kentry_eqb (KBlob (SA (ELit 0) 0x351b28) (ELit 8) 3)) kn_main 0) in
                                              lazymatch i with Some ?j => exact j end) _ HK eq_refl) as Bcan2.
  cbn [kentry_ok] in Brnd, Bcan1, Bcan2. unfold elenZ in Brnd, Bcan1, Bcan2. cbn [edenot] in Brnd, Bcan1, Bcan2.
  change (eb E 2) with (rnd16 rdraw) in Brnd. change (eb E 3) with (guard8 rdraw) in Bcan1, Bcan2.
  rewrite (u64_lit 16) in Brnd by lia. rewrite (u64_lit 8) in Bcan1, Bcan2 by lia.
  destruct Brnd as (Fr & Lr & Br). destruct Bcan1 as (F1 & L1 & B1). destruct Bcan2 as (F2 & L2 & B2).
  assert (Ev4 : ev E' 4 = ev E 4) by reflexivity.
  assert (E38 : ev E' 38 = rndw0 rdraw).
  { unfold E', ENVX, valsX. cbn [ev]. replace 38%nat with (length (vals0 sp0 a0s path envv tid regs0) + 0)%nat by (rewrite HLv; reflexivity).
    rewrite vals_ev_app_r. reflexivity. }
  assert (E39 : ev E' 39 = rndw1 rdraw).
  { unfold E', ENVX, valsX. cbn [ev]. replace 39%nat with (length (vals0 sp0 a0s path envv tid regs0) + 1)%nat by (rewrite HLv; reflexivity).
    rewrite vals_ev_app_r. reflexivity. }
  assert (E40 : ev E' 40 = can rdraw).
  { unfold E', ENVX, valsX. cbn [ev]. replace 40%nat with (length (vals0 sp0 a0s path envv tid regs0) + 2)%nat by (rewrite HLv; reflexivity).
    rewrite vals_ev_app_r. reflexivity. }
  assert (Lf : length (firstn 8 (rnd16 rdraw)) = 8%nat) by (rewrite length_firstn; lia).
  assert (Ls : length (skipn 8 (rnd16 rdraw)) = 8%nat) by (rewrite length_skipn; lia).
  unfold kn_exec. change (know_ok RSEGS E' mem (kn_main_noblob ++ kn_rndcan)).
  unfold know_ok. apply Forall_app. split; [exact HK1|]. unfold kn_rndcan.
  repeat apply Forall_cons; [| | | | apply Forall_nil].
  - apply (kword_of_bytes E' mem _ (firstn 8 (rnd16 rdraw))).
    + unfold flat in *. unfold estart in *. cbn [a_base a_off edenot] in *. rewrite Ev4. lia.
    + exact Lf.
    + intros i Hi. unfold estart. cbn [a_base a_off edenot]. rewrite Ev4.
      unfold estart in Br. cbn [a_base a_off edenot] in Br. rewrite (Br i) by lia.
      rewrite nth_firstn. replace (Z.to_nat i <? 8)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
    + cbn [edenot]. exact E38.
  - apply (kword_of_bytes E' mem _ (skipn 8 (rnd16 rdraw))).
    + unfold flat in *. unfold estart in *. cbn [a_base a_off edenot] in *. rewrite Ev4. lia.
    + exact Ls.
    + intros i Hi. unfold estart. cbn [a_base a_off edenot]. rewrite Ev4.
      unfold estart in Br. cbn [a_base a_off edenot] in Br.
      replace (bv_unsigned (ev E 4) + 8 + i)%Z with (bv_unsigned (ev E 4) + 0 + (8 + i))%Z by lia.
      rewrite (Br (8 + i)%Z) by lia. rewrite nth_skipn. f_equal. f_equal. lia.
    + cbn [edenot]. exact E39.
  - apply (kword_of_bytes E' mem _ (guard8 rdraw)).
    + unfold flat in *. unfold estart in *. cbn [a_base a_off edenot] in *. lia.
    + lia.
    + intros i Hi. exact (B1 i Hi).
    + cbn [edenot]. exact E40.
  - apply (kword_of_bytes E' mem _ (guard8 rdraw)).
    + unfold flat in *. unfold estart in *. cbn [a_base a_off edenot] in *. lia.
    + lia.
    + intros i Hi. exact (B2 i Hi).
    + cbn [edenot]. exact E40.
Qed.
