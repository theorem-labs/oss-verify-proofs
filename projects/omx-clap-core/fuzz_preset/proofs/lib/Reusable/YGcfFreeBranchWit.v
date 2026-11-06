(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfFreeBranchWit.v, with its module paths changed; 10 of its 168 lines of code are new or changed and 4 lines of the source are left out. *)
(* Taken by path from commit f381ad4bcd7, proofs/cgif/cgif_file_fuzzer/lib/YGcfFreeBranchWit.v (the P'' successor); module paths changed to fuzz_preset lib.Reusable, the text is otherwise unchanged. *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane, DeallocNmaxA): the two branches of free_cf's size test (YG00cf.free_cf, Quarantine::Put's
   `size <= max_size`) are both taken at a reachable state of the cf model.
   From init_state (ARcf_nil_init's state), a granted malloc_cf of n, then a granted free_cf of the result:
   - n = 2 ^ 28 = kQuarantineMax: the enqueue side (the boundary block, the largest size Put enqueues);
   - n = 2 ^ 28 + 1: the recycle side (the chunk is recycled at once).
   Each witness gives the two paths, the branch condition at the freed chunk, and free_cf's law (free_post_ycf) on the
   free path. The traces are those of the all-granted run [irun_tr] (sound for apath, irun_tr_apath). The witnesses
   are generic over the instance (CfImg, CfParams) with the premise n < cf_malloc_max, and are instantiated at
   preset's cf_malloc_max = 2 ^ 28 + 2 ^ 27 (CfParamsPreset's instance code) and reply's 2 ^ 30 - 2 ^ 20 (atop's
   A/CfParamsReply.v); both values are below 2 ^ 30 (YG08cf.cf_malloc_max_bound).
   The second observable [map24]: the free path asks a class-24 (batch) map exactly on the enqueue side, where a new
   batch is needed; the recycle side asks none.
   Nothing here is a function's proof (rule 24). No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG03cf YG03dcf YGcfTok.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfApath YGcfNilInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG08cf.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The all-granted run, with its trace, sound for apath.                       *)
Definition aok1b (s : astate) (q : kreq) : bool :=
  match q with KDepot tr => negb (mem_trace tr (st_depot s)) | _ => true end.

Lemma aok1b_aok : forall s q, aok1b s q = true -> aok s q 1.
Proof.
  intros s q H. destruct q; cbn in *; auto.
  right. split; [reflexivity|]. apply negb_true_iff in H. exact H.
Qed.

Fixpoint irun_tr {A} (fuel : nat) (t : itree astate A) : option (A * list (kreq * Z)) :=
  match fuel with
  | O => None
  | S f =>
      match t with
      | IRet a => Some (a, [])
      | IAsk q s k =>
          if aok1b s q then
            match irun_tr f (k 1) with Some (a, tr) => Some (a, (q, 1) :: tr) | None => None end
          else None
      | _ => None
      end
  end.

Lemma irun_tr_apath : forall A fuel (t : itree astate A) a tr, irun_tr fuel t = Some (a, tr) -> apath t tr a.
Proof.
  intros A fuel. induction fuel as [|f IH]; intros t a tr H; [discriminate|].
  destruct t as [a'|q s k|pc|fl]; cbn in H.
  - injection H as <- <-. reflexivity.
  - destruct (aok1b s q) eqn:E; [|discriminate].
    destruct (irun_tr f (k 1)) as [[a0 tr0]|] eqn:R; [|discriminate].
    injection H as <- <-. cbn. split; [reflexivity|]. split; [exact (aok1b_aok s q E)|]. exact (IH _ _ _ R).
  - discriminate.
  - discriminate.
Qed.

Definition nnb (p : sptr) : bool := match p with PNull => false | _ => true end.
Lemma nnb_ok : forall p, nnb p = true -> p <> PNull.
Proof. intros p H E. subst p. discriminate H. Qed.

(* the free path asks a class-24 (batch) map: a new batch, which only the enqueue side takes *)
Definition map24 (tr : list (kreq * Z)) : bool :=
  existsb (fun e => match fst e with KMapUser c _ _ => c =? kBatchClass | _ => false end) tr.

(* ---------------------------------------------------------------------------- *)
(* 2. The witnesses, generic over the instance.                                   *)
Section W.
Context {ci : CfImg} {cp : CfParams}.

(* the two traces of the run, the malloc's and the free's, as the universe's fixed traces (no wild ones) *)
Definition U_w : Univ := MkUniv [[1; 2]; [3; 4]] [] 0.

Lemma U_w_ok : universe_ok U_w.
Proof.
  unfold universe_ok, U_w. cbn [u_fix u_wmax]. split; [cbn; unfold DEPOT_MAX; lia|]. split.
  - apply Forall_cons; [cbn; unfold kUnwindMax; lia | apply Forall_cons; [cbn; unfold kUnwindMax; lia | constructor]].
  - apply NoDup_cons; [|apply NoDup_cons; [intros [] | constructor]].
    intros [H|[]]. inversion H.
Qed.

(* a fixed trace of U_w is admitted at any state *)
Lemma U_w_admits : forall tr s, In tr (u_fix U_w) -> admits U_w tr s.
Proof.
  intros tr s Hin. split.
  - split; [|left; exact Hin]. cbn in Hin. destruct Hin as [<-|[<-|[]]]; cbn; unfold kUnwindMax; lia.
  - right; left. cbn in Hin. destruct Hin as [<-|[<-|[]]]; reflexivity.
Qed.

(* free_cf's law on the free path, from malloc_cf's on the malloc path, at init_state *)
Lemma wit_post : forall n p S1 trc1 S2 trc2,
  0 <= n < cf_malloc_max ->
  apath (malloc_cf n [1; 2] init_state) trc1 (p, S1) -> p <> PNull -> batch_room_cf S1 ->
  apath (free_cf p [3; 4] S1) trc2 (tt, S2) ->
  In (p, n) (blocks S1) /\ Wf_cf U_w S1 /\ exists ns, free_post_ycf U_w S1 p n ns (tt, S2).
Proof.
  intros n p S1 trc1 S2 trc2 Hn H1 Hp HB H2.
  pose proof YG08cf.cf_malloc_max_bound as MB.
  assert (HL : blocks_bytes init_state + n <= LIVE_MAX)
    by (replace (blocks_bytes init_state) with 0 by reflexivity; unfold LIVE_MAX; lia).
  assert (HS : Z.of_nat (length (st_sec_arr init_state)) < cf_sec_live_max)
    by (replace (st_sec_arr init_state) with (@nil nat) by reflexivity; cbn; pose proof cf_sec_live_pos; lia).
  destruct (malloc_cf_apath_success U_w init_state n [1; 2] trc1 p S1 U_w_ok (wf_init_cf U_w) Hn HL
    (U_w_admits [1; 2] init_state ltac:(cbn; left; reflexivity)) HS ERRB_ROOM_init batch_room_cf_init H1 Hp)
    as (W1 & _ & _ & _ & B1 & _ & _).
  assert (HIn : In (p, n) (blocks S1)) by (rewrite B1; apply in_or_app; right; left; reflexivity).
  split; [exact HIn|]. split; [exact W1|].
  exact (atok_cf_apath _ _ _ _ _ (ml_free_cf U_w U_w_ok S1 p n [3; 4] W1 HB (or_intror HIn)
    (U_w_admits [3; 4] S1 ltac:(cbn; right; left; reflexivity))) H2).
Qed.

(* the computed check: the malloc and the free run granted, the freed chunk's size test is [enq], and the free
   path's class-24 map ask is [enq] *)
Definition wit_check (n : Z) (enq : bool) : bool :=
  match irun_tr 5000 (malloc_cf n [1; 2] init_state) with
  | Some ((p, S1), _) =>
      nnb p && (rg_mapped_user (reg S1 kBatchClass) + kUserMapSize <=? kFreeArrayOffset) &&
      match find_user (st_chunks S1) p with
      | Some k =>
          Bool.eqb (ck_n k <=? kQuarantineMax) enq &&
          match irun_tr 100000 (free_cf p [3; 4] S1) with
          | Some ((_, S2), trc2) => Bool.eqb (map24 trc2) enq
          | None => false
          end
      | None => false
      end
  | None => false
  end.

Theorem free_cf_branch_wit_gen : forall n enq, 0 <= n < cf_malloc_max -> wit_check n enq = true ->
  exists p S1 trc1 k S2 trc2,
    apath (malloc_cf n [1; 2] init_state) trc1 (p, S1) /\ p <> PNull /\ In (p, n) (blocks S1) /\
    find_user (st_chunks S1) p = Some k /\ (ck_n k <=? kQuarantineMax) = enq /\
    apath (free_cf p [3; 4] S1) trc2 (tt, S2) /\ map24 trc2 = enq /\
    exists ns, free_post_ycf U_w S1 p n ns (tt, S2).
Proof.
  intros n enq Hn H. unfold wit_check in H.
  destruct (irun_tr 5000 (malloc_cf n [1; 2] init_state)) as [[[p S1] trc1]|] eqn:R1; [|discriminate].
  apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [Hnn Hbr].
  destruct (find_user (st_chunks S1) p) as [k|] eqn:Hf; [|discriminate].
  apply andb_true_iff in H4 as [Hq H5].
  destruct (irun_tr 100000 (free_cf p [3; 4] S1)) as [[[u S2] trc2]|] eqn:R2; [|discriminate]. destruct u.
  apply Bool.eqb_prop in Hq. apply Bool.eqb_prop in H5.
  pose proof (irun_tr_apath _ _ _ _ _ R1) as A1. pose proof (irun_tr_apath _ _ _ _ _ R2) as A2.
  pose proof (nnb_ok p Hnn) as Hp.
  assert (HB : batch_room_cf S1) by (unfold batch_room_cf; apply Z.leb_le; exact Hbr).
  destruct (wit_post n p S1 trc1 S2 trc2 Hn A1 Hp HB A2) as (HIn & _ & Hpost).
  exists p, S1, trc1, k, S2, trc2.
  exact (conj A1 (conj Hp (conj HIn (conj Hf (conj Hq (conj A2 (conj H5 Hpost))))))).
Qed.

(* the enqueue side at the boundary n = kQuarantineMax, the recycle side one byte above it *)
Lemma wit_check_enqueue : wit_check (2 ^ 28) true = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wit_check_recycle : wit_check (2 ^ 28 + 1) false = true.
Proof. vm_compute. reflexivity. Qed.

Theorem free_cf_enqueue_witness : 2 ^ 28 < cf_malloc_max ->
  exists p S1 trc1 k S2 trc2,
    apath (malloc_cf (2 ^ 28) [1; 2] init_state) trc1 (p, S1) /\ p <> PNull /\ In (p, 2 ^ 28) (blocks S1) /\
    find_user (st_chunks S1) p = Some k /\ (ck_n k <=? kQuarantineMax) = true /\
    apath (free_cf p [3; 4] S1) trc2 (tt, S2) /\ map24 trc2 = true /\
    exists ns, free_post_ycf U_w S1 p (2 ^ 28) ns (tt, S2).
Proof.
  intros H. apply free_cf_branch_wit_gen; [split; [apply Z.leb_le; vm_compute; reflexivity | exact H] | exact wit_check_enqueue].
Qed.

Theorem free_cf_recycle_witness : 2 ^ 28 + 1 < cf_malloc_max ->
  exists p S1 trc1 k S2 trc2,
    apath (malloc_cf (2 ^ 28 + 1) [1; 2] init_state) trc1 (p, S1) /\ p <> PNull /\ In (p, 2 ^ 28 + 1) (blocks S1) /\
    find_user (st_chunks S1) p = Some k /\ (ck_n k <=? kQuarantineMax) = false /\
    apath (free_cf p [3; 4] S1) trc2 (tt, S2) /\ map24 trc2 = false /\
    exists ns, free_post_ycf U_w S1 p (2 ^ 28 + 1) ns (tt, S2).
Proof.
  intros H. apply free_cf_branch_wit_gen; [split; [apply Z.leb_le; vm_compute; reflexivity | exact H] | exact wit_check_recycle].
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. At the two units' values (each unit's instance gives the equation by reflexivity).                         *)
Corollary preset_free_cf_enqueue_witness : cf_malloc_max = 2 ^ 28 + 2 ^ 27 ->
  exists p S1 trc1 k S2 trc2,
    apath (malloc_cf (2 ^ 28) [1; 2] init_state) trc1 (p, S1) /\ p <> PNull /\ In (p, 2 ^ 28) (blocks S1) /\
    find_user (st_chunks S1) p = Some k /\ (ck_n k <=? kQuarantineMax) = true /\
    apath (free_cf p [3; 4] S1) trc2 (tt, S2) /\ map24 trc2 = true /\
    exists ns, free_post_ycf U_w S1 p (2 ^ 28) ns (tt, S2).
Proof. intros E. apply free_cf_enqueue_witness. rewrite E. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

Corollary preset_free_cf_recycle_witness : cf_malloc_max = 2 ^ 28 + 2 ^ 27 ->
  exists p S1 trc1 k S2 trc2,
    apath (malloc_cf (2 ^ 28 + 1) [1; 2] init_state) trc1 (p, S1) /\ p <> PNull /\ In (p, 2 ^ 28 + 1) (blocks S1) /\
    find_user (st_chunks S1) p = Some k /\ (ck_n k <=? kQuarantineMax) = false /\
    apath (free_cf p [3; 4] S1) trc2 (tt, S2) /\ map24 trc2 = false /\
    exists ns, free_post_ycf U_w S1 p (2 ^ 28 + 1) ns (tt, S2).
Proof. intros E. apply free_cf_recycle_witness. rewrite E. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

Corollary reply_free_cf_enqueue_witness : cf_malloc_max = 2 ^ 30 - 2 ^ 20 ->
  exists p S1 trc1 k S2 trc2,
    apath (malloc_cf (2 ^ 28) [1; 2] init_state) trc1 (p, S1) /\ p <> PNull /\ In (p, 2 ^ 28) (blocks S1) /\
    find_user (st_chunks S1) p = Some k /\ (ck_n k <=? kQuarantineMax) = true /\
    apath (free_cf p [3; 4] S1) trc2 (tt, S2) /\ map24 trc2 = true /\
    exists ns, free_post_ycf U_w S1 p (2 ^ 28) ns (tt, S2).
Proof. intros E. apply free_cf_enqueue_witness. rewrite E. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

Corollary reply_free_cf_recycle_witness : cf_malloc_max = 2 ^ 30 - 2 ^ 20 ->
  exists p S1 trc1 k S2 trc2,
    apath (malloc_cf (2 ^ 28 + 1) [1; 2] init_state) trc1 (p, S1) /\ p <> PNull /\ In (p, 2 ^ 28 + 1) (blocks S1) /\
    find_user (st_chunks S1) p = Some k /\ (ck_n k <=? kQuarantineMax) = false /\
    apath (free_cf p [3; 4] S1) trc2 (tt, S2) /\ map24 trc2 = false /\
    exists ns, free_post_ycf U_w S1 p (2 ^ 28 + 1) ns (tt, S2).
Proof. intros E. apply free_cf_recycle_witness. rewrite E. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

End W.
