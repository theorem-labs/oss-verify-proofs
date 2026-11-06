(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Frame Step Tac Image ZBridge SysStep SFModel ITree Nodes NodesM Decode DecodeM Arr.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog MSafe KLink KStep KOwn KStepC A_MallocBlocks A_MallocHINV A_Malloc_iface A_MallocTree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import F_syscalls RMallocRep RMallocTree RMallocKit_B RMalloc_iface RMalloc_ifaceP RF_aligned16.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Instr Plan ValProofs MemProofs StepSoundBase StepSoundMem StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem State Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue RegsEqv TreeBridgeN KRel MPath Room HeapCore MF AW RMallocG RAllocG CtrFX.

Set Keyed Unification.
Import ListNotations.
Import W64 Val FI St Step Plan ValP MemP StepB StepM StepS PlanS CtrLib CtrA HeapOp CtrFX.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition ERRNO : int := 0x673ec%uint63.
Definition LIBC  : int := 0x87720%uint63.
Definition GOT   : int := 0x55660%uint63.
Definition GUARD : int := 0x87700%uint63.
Definition TP    : int := 0x67490%uint63.

Lemma ERRNO_eq : to_Z ERRNO = RERRNO. Proof. reflexivity. Qed.
Lemma LIBC_eq : to_Z LIBC = RLIBC. Proof. reflexivity. Qed.
Lemma GOT_eq : to_Z GOT = RGOT_SSP. Proof. reflexivity. Qed.
Lemma GUARD_eq : to_Z GUARD = RSSP_GUARD. Proof. reflexivity. Qed.
Lemma TP_eq : to_Z TP = RATP. Proof. reflexivity. Qed.
Lemma NEED_LOCKS_eq : to_Z (PrimInt63.add LIBC 3%uint63) = RNEED_LOCKS. Proof. reflexivity. Qed.
Lemma PAGE_SIZE_eq : to_Z (PrimInt63.add LIBC 48%uint63) = RPAGE_SIZE. Proof. reflexivity. Qed.
Lemma AUXV_CELL_eq : to_Z (PrimInt63.add LIBC 8%uint63) = RAUXV_CELL. Proof. reflexivity. Qed.

Lemma wr_NEED_LOCKS : Mem.abs_writable rsegs RNEED_LOCKS 1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wr_PAGE_SIZE : Mem.abs_writable rsegs RPAGE_SIZE 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wr_AUXV_CELL : Mem.abs_writable rsegs RAUXV_CELL 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wr_GOT : Mem.abs_writable rsegs RGOT_SSP 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wr_GUARD : Mem.abs_writable rsegs RSSP_GUARD 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wr_ERRNO : Mem.abs_writable rsegs RERRNO 4 = true. Proof. vm_compute. reflexivity. Qed.

Lemma rom_of_seg_rom : St.rom_of rsegs = seg_rom rsegs.
Proof. reflexivity. Qed.

Lemma rb_mrd : forall m a, rb rsegs m a = mrd rsegs m (wa a).
Proof. reflexivity. Qed.

Lemma wb_wview : forall m a, wb rsegs m a = true <-> wview rsegs m (wa a) <> None.
Proof. intros m a. unfold wb, wa. destruct (wview rsegs m (Z_to_bv 64 a)); split; congruence. Qed.

Lemma bytes_at_of_ov_read : forall m a n bs,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  ov_read_bytes rsegs m (wa a) n = Some bs -> bytes_at rsegs m a bs.
Proof.
  intros m a n. revert a. induction n as [|n IH]; intros a bs Ha Hn H.
  - cbn in H. injection H as <-. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [ov_read_bytes] in H. fold (mrd rsegs m (wa a)) in H.
    change (match m (wa a) with Some b => Some b | None => match memory_read rsegs (wa a) 1 with Some (b :: _) => Some b | _ => None end end)
      with (mrd rsegs m (wa a)) in H.
    destruct (mrd rsegs m (wa a)) as [b|] eqn:Hb; [|discriminate].
    destruct (ov_read_bytes rsegs m (wa a + 1)%bv n) as [bs'|] eqn:Hr; [|discriminate]. injection H as <-.
    rewrite wa_succ in Hr. pose proof (IH (a + 1) bs' ltac:(lia) ltac:(lia) Hr) as (_ & L & B).
    split; [lia|]. split; [cbn [length]; lia|].
    intros [|i] Hi; cbn [nth_error].
    + rewrite Z.add_0_r. exact Hb.
    + replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply B. cbn in Hi. lia.
Qed.

Lemma ov_read_bytes_length : forall m a n bs, ov_read_bytes rsegs m a n = Some bs -> length bs = n.
Proof.
  intros m a n. revert a. induction n as [|n IH]; intros a bs H; cbn [ov_read_bytes] in H.
  - injection H as <-. reflexivity.
  - destruct (match m a with Some b => Some b | None => _ end); [|discriminate].
    destruct (ov_read_bytes rsegs m (a + 1)%bv n) eqn:R; [|discriminate]. injection H as <-. cbn. f_equal. eapply IH. exact R.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
    pose proof (bytes_le_to_Z_nonneg bs) as NN.
    unfold bv_wrap. replace (bv_modulus 8) with 256 by reflexivity.
    rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. pose proof (bytes_le_to_Z_nonneg bs) as NN.
    rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. rewrite Z.add_0_r. exact IH.
Qed.

Lemma bytes_val_false_eq : forall n bs, length bs = n -> (1 <= n <= 8)%nat ->
  bv_unsigned (bytes_val false (Z.of_nat n) bs) = bytes_le_to_Z bs.
Proof.
  intros n bs Hl Hn. unfold bytes_val. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_bound bs) as B. rewrite Hl in B.
  assert (P : 2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite (ext_Z_small_id false (Z.of_nat n) (bytes_le_to_Z bs)).
  1:{ apply bv_wrap_small. rewrite bv_modulus_64, two64_eq. lia. }
  1:{ lia. }
  1:{ rewrite two64_eq. lia. }
  rewrite Z.sub_0_r. exact B.
Qed.

Lemma lit_load_bytes : forall E n bs (x : int),
  length bs = n -> (n <= 8)%nat ->
  den E (VL (wlit x)) = bytes_val false (Z.of_nat n) bs ->
  bs = Z_to_le_bytes n (to_Z x).
Proof.
  intros E n bs x Hl Hn H.
  destruct n as [|n']. { destruct bs; [reflexivity| discriminate]. }
  assert (E1 : to_Z x = bytes_le_to_Z bs).
  { apply (f_equal bv_unsigned) in H. rewrite unsigned_VL, wlit_ok in H. rewrite (bytes_val_false_eq (S n') bs Hl ltac:(lia)) in H. exact H. }
  rewrite E1, <- Hl. symmetry. apply Z_to_le_bytes_to_Z.
Qed.

Lemma load8_bytes : forall E bs v, length bs = 8%nat -> den E v = bytes_val false 8 bs -> bs = le8 (den E v).
Proof.
  intros E bs v Hl H. unfold le8, word_to_le_bytes. rewrite H, (bytes_val_false_eq 8 bs Hl ltac:(lia)), <- Hl.
  symmetry. apply Z_to_le_bytes_to_Z.
Qed.
Lemma load4_bytes : forall E bs v, length bs = 4%nat -> den E v = bytes_val false 4 bs -> bs = le4 (den E v).
Proof.
  intros E bs v Hl H. unfold le4. rewrite H, (bytes_val_false_eq 4 bs Hl ltac:(lia)), <- Hl.
  symmetry. apply Z_to_le_bytes_to_Z.
Qed.

Variable Cw : client_world.
Variable OPS : St.optable.

Hypothesis OPS_plain : St.plain_table OPS.

Hypothesis OPS_holds1 : forall args m mo, St.op_holds OPS HEAP_ID args m mo = heap_holds rsegs IMGX AWI Cw args m mo.
Hypothesis OPS_fp1 : forall args, St.op_fp OPS HEAP_ID args = heap_fp IMGX args.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Variable CANARY : sv.
Hypothesis PB_canary : forall E, PB (eb E) -> den E CANARY = Z_to_bv 64 ssp_canary.
Hypothesis PB_secret : forall E, PB (eb E) -> forall i, (i < 8)%nat ->
  nth_error (eb E 6%uint63) (8 + i) = nth_error (le8 (wz ctx_secret)) i.

Lemma st_ok_set_A : forall E st ms mo hargs a a' md nw rest,
  St.st_ok rsegs OPS E st ms mo ->
  find_op HEAP_ID (s_ops st) = Some hargs -> hargs = VL md :: a :: VL nw :: rest ->
  (forall s LBf mo', pclaim (bv_unsigned (den E a)) s LBf mo' -> pclaim (bv_unsigned (den E a')) s LBf mo') ->
  St.st_ok rsegs OPS E (set_ops st (set_op HEAP_ID (VL md :: a' :: VL nw :: rest) (s_ops st))) ms mo.
Proof.
  intros E st ms mo hargs a a' md nw rest HS Hf -> HR.
  pose proof (ops_hold_find OPS E (s_ops st) (ms_mem ms) mo HEAP_ID _ (St.so_ops _ _ _ _ _ _ HS) Hf) as HH.
  rewrite OPS_holds1 in HH. destruct HH as (md' & aw & ws & ca & LB & D & HA & WF & HC).
  destruct (decode_set_A E (VL md) a a' (VL nw) rest md' aw ws ca D) as [D' ->].
  destruct HS as [Hpc Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hops Hapart Hmf Hcov Hminv].
  split; cbn [set_ops s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - eapply ops_hold_set_op1; [exact Hf| exact Hops|]. rewrite OPS_holds1.
    exists md', (den E a'), ws, ca, LB. split; [exact D'|]. split; [| split; [exact WF| exact HC]].
    destruct HA as ((s & LBf & P & RC & K & MT & RM & RP) & NGW). apply aw_holdsW_intro; [| exact NGW]. exists s, LBf. repeat (split; [assumption|]). split; [| exact RP].
    apply HR. exact RM.
  - eapply ops_apart_set_op1; [exact Hf| exact Hapart|]. rewrite !OPS_fp1. unfold heap_fp. rewrite D, D'. reflexivity.
  -
    intros x _. apply St.plain_cover. exact OPS_plain.
Qed.

Theorem roomdrop_sound : forall pc, contract_sound rsegs OPS MP PB (CtrM.roomdrop_c pc).
Proof.
  intros pc st sts Hpc Happ K E ms mo HS HMP HPB HK. cbn [c_apply CtrM.roomdrop_c] in Happ. unfold CtrM.roomdrop_apply in Happ.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|] eqn:Hf; [|discriminate].
  destruct (heap_A hargs) as [[j| | | | | | | | | |]|] eqn:HA; try discriminate.
  destruct (heap_set_A hargs (VL wones)) as [hargs'|] eqn:HS'; [|discriminate]. injection Happ as <-.
  destruct (heap_set_A_shape hargs (VL wones) hargs' HS') as (md & A & nw & rest & -> & ->).
  apply (HK _ (or_introl eq_refl) E ms mo (env_ext_refl _ E) HMP).
  eapply st_ok_set_A; [exact HS| exact Hf| reflexivity|].
  intros s LBf mo' _. apply pclaim_none. rewrite unsigned_VL. change (w2Z wones) with (2^64 - 1). lia.
Qed.

Lemma pw_ok_inv : forall a, pw_ok a = true -> wt a = false /\ 0 <= w2Z a < 768 /\ w2Z a = to_Z (wl a).
Proof.
  intros a H. unfold pw_ok in H. apply andb_prop in H as [T L]. destruct (wt a) eqn:T'; [discriminate|].
  apply Uint63.ltb_spec in L. change (to_Z 768%uint63) with 768 in L. pose proof (w2Z_nowt a T') as E. pose proof (int_range (wl a)). lia.
Qed.
Lemma pw_j_eq : forall a, to_Z (pw_j a) = to_Z (wl a) mod 256.
Proof.
  intros a. unfold pw_j. pose proof (land_mk (wl a) 8%uint63 ltac:(change (to_Z 8%uint63) with 8; lia)) as LM.
  change (PrimInt63.sub (PrimInt63.lsl 1 8) 1)%uint63 with 255%uint63 in LM. change (2 ^ to_Z 8%uint63) with 256 in LM. exact LM.
Qed.
Lemma pw_nb_eq : forall a, to_Z (pw_nb a) = to_Z (wl a) / 256.
Proof. intros a. unfold pw_nb. rewrite Uint63.lsr_spec. change (2 ^ to_Z 8%uint63) with 256. reflexivity. Qed.

Theorem roomcap_sound : forall pc, contract_sound rsegs OPS MP PB (CtrA.roomcap_c pc).
Proof.
  intros pc st sts Hpc Happ K E ms mo HS HMP HPB HK. cbn [c_apply CtrA.roomcap_c] in Happ. unfold CtrA.roomcap_apply in Happ.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|] eqn:Hf; [|discriminate].
  destruct (heap_A hargs) as [[a| | | | | | | | | |]|] eqn:HA; try discriminate.
  destruct (pw_ok a && PrimInt63.leb (pw_j a) J_CAP) eqn:C; [|discriminate]. apply andb_prop in C as [P L].
  match type of Happ with context [heap_set_A hargs (VL ?x)] => set (a' := x) in Happ end.
  destruct (heap_set_A hargs (VL a')) as [hargs'|] eqn:HS'; [|discriminate]. injection Happ as <-.
  destruct (heap_set_A_shape hargs (VL a') hargs' HS') as (md & A & nw & rest & -> & ->).
  cbn [heap_A] in HA. injection HA as ->.
  apply (HK _ (or_introl eq_refl) E ms mo (env_ext_refl _ E) HMP).
  eapply st_ok_set_A; [exact HS| exact Hf| reflexivity|].
  destruct (pw_ok_inv a P) as (T & R & Ea). apply Uint63.leb_spec in L. change (to_Z J_CAP) with 21 in L. rewrite pw_j_eq in L.
  assert (Ea' : w2Z a' = to_Z (wl a) - to_Z (wl a) mod 256 + 21).
  { subst a'. unfold w2Z. cbn [wt wl]. rewrite Uint63.add_spec, Uint63.sub_spec, pw_j_eq. change (to_Z J_CAP) with 21.
    pose proof (Z.mod_pos_bound (to_Z (wl a)) 256 ltac:(lia)). pose proof (int_range (wl a)).
    rewrite (Z.mod_small (to_Z (wl a) - to_Z (wl a) mod 256)) by (rewrite wB_two63; lia). rewrite Z.mod_small by (rewrite wB_two63; unfold two63; lia). lia. }
  intros s LBf mo' H. rewrite !unsigned_VL in *. rewrite Ea', Ea in *.
  pose proof (Z.mod_pos_bound (to_Z (wl a)) 256 ltac:(lia)) as MB. pose proof (Z.div_mod (to_Z (wl a)) 256 ltac:(lia)) as DM.
  apply (pclaim_mono (to_Z (wl a))); [exact H| lia| lia| | | lia].
  - replace (to_Z (wl a) - to_Z (wl a) mod 256 + 21) with (21 + (to_Z (wl a) / 256) * 256) by lia.
    rewrite Z.mod_add by lia. change (21 mod 256) with 21. lia.
  - replace (to_Z (wl a) - to_Z (wl a) mod 256 + 21) with (21 + (to_Z (wl a) / 256) * 256) by lia.
    rewrite Z.div_add by lia. change (21 / 256) with 0. lia.
Qed.

Lemma alloc_call_inv : forall need st r ksp hargs wnl,
  alloc_call rsegs ERRNO LIBC GOT GUARD TP CANARY need st = Some (r, ksp, hargs, wnl) ->
  s_resv st = RNone /\ call_pre st = Some r /\ PrimInt63.ltb r bit62i = true
  /\ (exists ra, getr st X1 = VL ra /\ PrimInt63.land (wl ra) 1%uint63 = 0%uint63)
  /\ getr st X4 = VL (wlit TP)
  /\ statics_ok rsegs ERRNO LIBC GOT GUARD CANARY st = true /\ auxv_ok rsegs st = true /\ above_stack_ok st = true
  /\ exists klo1, stack_ok st need = Some (ksp, klo1) /\ heap_windows st klo1 = Some (hargs, wnl).
Proof.
  intros need st r ksp hargs wnl H. unfold alloc_call in H.
  destruct (s_resv st); try discriminate. destruct (call_pre st) as [r0|]; [|discriminate].
  destruct (getr st X1) as [ra| | | | | | | | | |]; try discriminate.
  destruct (getr st X4) as [tp| | | | | | | | | |]; try discriminate.
  destruct (stack_ok st need) as [[ksp0 klo1]|]; [|discriminate].
  destruct (weqb tp (wlit TP)) eqn:Htp; [|discriminate].
  destruct (PrimInt63.eqb (PrimInt63.land (wl ra) 1) 0) eqn:Hra; [|discriminate].
  destruct (statics_ok _ _ _ _ _ _ st) eqn:Hst; [|discriminate]. destruct (auxv_ok rsegs st) eqn:Hav; [|discriminate].
  destruct (above_stack_ok st) eqn:Hab; [|discriminate]. destruct (PrimInt63.ltb r0 bit62i) eqn:Hr; [|discriminate].
  cbn [andb] in H. destruct (heap_windows st klo1) as [[h w]|] eqn:Hw; [|discriminate]. injection H as <- <- <- <-.
  apply weqb_eq in Htp. subst tp. apply Uint63.eqb_correct in Hra.
  repeat split; try assumption; try reflexivity. { exists ra. auto. } exists klo1. auto.
Qed.

Lemma call_pre_inv : forall st r, call_pre st = Some r ->
  fresh_ok st = true /\ exists ra, getr st X1 = VL ra /\ wt ra = false /\ PrimInt63.ltb (wl ra) bit62i = true /\ r = wl ra.
Proof.
  intros st r H. unfold call_pre in H. destruct (s_resv st); try discriminate H. destruct (fresh_ok st); [|discriminate]. split; [reflexivity|].
  unfold ret_pc, small_lit in H. destruct (getr st X1) as [ra| | | | | | | | | |]; try discriminate.
  exists ra. destruct (wt ra); [discriminate|]. cbn [negb andb] in H. destruct (PrimInt63.ltb (wl ra) bit62i); [|discriminate].
  destruct (PrimInt63.eqb (PrimInt63.land (wl ra) 1) 0); [|discriminate]. injection H as <-. auto.
Qed.

Lemma call_pre_resv : forall st r, call_pre st = Some r -> s_resv st = RNone.
Proof. intros st r H. unfold call_pre in H. destruct (s_resv st); [reflexivity| discriminate H| discriminate H]. Qed.

Lemma call_pre_even : forall st r, call_pre st = Some r -> PrimInt63.land r 1%uint63 = 0%uint63.
Proof.
  intros st r H. unfold call_pre in H. destruct (s_resv st); try discriminate H. destruct (fresh_ok st); [|discriminate].
  destruct (ret_pc st) as [r0|]; [|discriminate]. destruct (PrimInt63.eqb (PrimInt63.land r0 1) 0) eqn:Q; [|discriminate].
  injection H as <-. apply Uint63.eqb_correct in Q. exact Q.
Qed.

Lemma fresh_ok_inv : forall st, fresh_ok st = true ->
  st_vars_below (s_next st) st = true /\ 0 < to_Z (s_next st) /\ to_Z (s_next st) + 256 <= 2 ^ 62.
Proof.
  intros st H. unfold fresh_ok in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  split; [exact H1|]. apply Uint63.ltb_spec in H2. apply Uint63.ltb_spec in H3. change (to_Z 0%uint63) with 0 in H2.
  change (to_Z 4611686018427387648%uint63) with (2 ^ 62 - 256) in H3. lia.
Qed.

Lemma den_wlit : forall E (a : int), den E (VL (wlit a)) = wa (to_Z a).
Proof. intros E a. rewrite den_VL. unfold wbv, wa. rewrite wlit_ok. reflexivity. Qed.

Lemma den_VPz : forall E k, den E (VP k wzero) = ev E k.
Proof. intros E k. apply bv_eq. apply (den_VP0 E k wzero eq_refl). Qed.

Lemma to_Z_lt64 : forall a : int, 0 <= to_Z a /\ to_Z a + 8 < 2 ^ 64.
Proof. intros a. pose proof (int_range a) as B. unfold two63 in B. lia. Qed.

Lemma aload_inv : forall E st ms mo a w v,
  St.st_ok rsegs OPS E st ms mo -> wok w -> aload rsegs st a w = Some v ->
  exists bs, length bs = Z.to_nat (to_Z w) /\ bytes_at rsegs (ms_mem ms) (to_Z a) bs
    /\ den E v = bytes_val false (to_Z w) bs.
Proof.
  intros E st ms mo a w v HS Hw H. unfold aload in H.
  destruct (do_load rsegs st (VL (wlit a)) w false) as [[v'|]|] eqn:D; try discriminate. injection H as ->.
  destruct (do_load_sound rsegs OPS E st ms mo (VL (wlit a)) w false v HS Hw D) as (bs & L & R & Dv).
  pose proof (to_Z_lt64 a) as B. assert (Hw8 : 1 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  exists bs. split; [exact L|]. split.
  - apply (bytes_at_of_ov_read (ms_mem ms) (to_Z a) (Z.to_nat (to_Z w)) bs); [lia| lia|].
    rewrite <- den_wlit with (E := E). exact R.
  - rewrite Dv. symmetry. apply bytes_val_ext_word; [exact L| exact Hw8].
Qed.

Lemma is_litv_inv : forall ov x, is_litv ov x = true -> ov = Some (VL (wlit x)).
Proof.
  intros [[w| | | | | | | | | |]|] x H; cbn in H; try discriminate. apply weqb_eq in H. subst. reflexivity.
Qed.
Lemma is_sv_inv : forall ov x, is_sv ov x = true -> ov = Some x.
Proof. intros [u|] x H; cbn in H; [|discriminate]. apply sv_eqb_eq in H. subst. reflexivity. Qed.

Lemma rw_cell_of_bytes : forall M A (c : Cells.cell), Cells.cell_wf c -> bytes_at rsegs M A (cbytes c) ->
  Mem.abs_writable rsegs A (Z.of_nat (csize c)) = true -> rw_cells rsegs M A [c].
Proof.
  intros M A c Hwf HB HW. pose proof HB as (H0 & H1 & _). rewrite (cbytes_length c Hwf) in H1.
  split.
  - split; [cbn; auto|]. cbn [cells_bytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size]. rewrite Nat.add_0_r. split; [exact H0|]. split; [exact H1|].
    intros i Hi. apply (proj1 (wb_wview M (A + i))).
    destruct (abs_writable_sound rsegs A (Z.of_nat (csize c)) ltac:(lia) ltac:(lia) HW) as [_ W]. apply (proj1 (W i Hi)).
Qed.

Lemma wok1 : wok 1%uint63. Proof. left. reflexivity. Qed.
Lemma wok4 : wok 4%uint63. Proof. right; right; left. reflexivity. Qed.
Lemma wok8 : wok 8%uint63. Proof. right; right; right. reflexivity. Qed.

Lemma statics_sound : forall E st ms mo,
  St.st_ok rsegs OPS E st ms mo -> PB (eb E) ->
  statics_ok rsegs ERRNO LIBC GOT GUARD CANARY st = true ->
  PUBS (ms_mem ms) /\ rw_cells rsegs (ms_mem ms) RAUXV_CELL [C8 (ev E AUXV_ID)]
  /\ exists errv, rw_cells rsegs (ms_mem ms) RERRNO [C4 errv].
Proof.
  intros E st ms mo HS HPB H. unfold statics_ok in H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply is_litv_inv in H1. apply is_litv_inv in H2. apply is_sv_inv in H3. apply is_litv_inv in H4. apply is_sv_inv in H5.
  destruct (aload rsegs st ERRNO 4%uint63) as [ve|] eqn:H6'; [|discriminate]. clear H6.
  destruct (aload_inv E st ms mo _ _ _ HS wok1 H1) as (bs1 & L1 & B1 & D1).
  destruct (aload_inv E st ms mo _ _ _ HS wok8 H2) as (bs2 & L2 & B2 & D2).
  destruct (aload_inv E st ms mo _ _ _ HS wok8 H3) as (bs3 & L3 & B3 & D3).
  destruct (aload_inv E st ms mo _ _ _ HS wok8 H4) as (bs4 & L4 & B4 & D4).
  destruct (aload_inv E st ms mo _ _ _ HS wok8 H5) as (bs5 & L5 & B5 & D5).
  destruct (aload_inv E st ms mo _ _ _ HS wok4 H6') as (bs6 & L6 & B6 & D6).
  cbn in L1, L2, L3, L4, L5, L6.
  pose proof (lit_load_bytes E 1 bs1 0%uint63 L1 ltac:(lia) D1) as E1.
  pose proof (lit_load_bytes E 8 bs2 4096%uint63 L2 ltac:(lia) D2) as E2.
  pose proof (load8_bytes E bs3 _ L3 D3) as E3.
  pose proof (lit_load_bytes E 8 bs4 GUARD L4 ltac:(lia) D4) as E4.
  pose proof (load8_bytes E bs5 _ L5 D5) as E5.
  pose proof (load4_bytes E bs6 _ L6 D6) as E6.
  subst bs1 bs2 bs3 bs4 bs5 bs6.
  split; [| split].
  - split; [| split; [| split]].
    + apply rw_cell_of_bytes; [exact I| | exact wr_NEED_LOCKS]. rewrite <- NEED_LOCKS_eq. exact B1.
    + apply rw_cell_of_bytes; [exact I| | exact wr_PAGE_SIZE]. rewrite <- PAGE_SIZE_eq. exact B2.
    + apply rw_cell_of_bytes; [exact I| | exact wr_GOT]. rewrite <- GOT_eq. exact B4.
    + apply rw_cell_of_bytes; [exact I| | exact wr_GUARD]. rewrite <- GUARD_eq.
      cbn [cbytes]. unfold wz. rewrite <- (PB_canary E HPB). exact B5.
  - apply rw_cell_of_bytes; [exact I| | exact wr_AUXV_CELL]. rewrite <- AUXV_CELL_eq. cbn [cbytes]. rewrite <- (den_VPz E AUXV_ID). exact B3.
  - exists (den E ve). apply rw_cell_of_bytes; [exact I| | exact wr_ERRNO]. rewrite <- ERRNO_eq. exact B6.
Qed.

Lemma okey_wlit : forall off key, Mem.okey (wlit off) = Some key -> keyZ key = to_Z off.
Proof.
  intros off key H. destruct (okey_sound (wlit off) key H) as [E _]. rewrite E, w2Zs_eq, wlit_ok. cbn [wt wlit]. lia.
Qed.

Lemma rload_inv : forall E st ms mo k off w v,
  St.st_ok rsegs OPS E st ms mo -> wok w -> PrimInt63.eqb k 0%uint63 = false -> rload rsegs st k off w = Some v ->
  exists r bs, IMap.find k (s_regs st) = Some r /\ length bs = Z.to_nat (to_Z w)
    /\ loZ r <= to_Z off /\ to_Z off + to_Z w <= hiZ E r /\ bv_unsigned (ev E k) + hiZ E r < 2 ^ 64
    /\ bytes_at rsegs (ms_mem ms) (bv_unsigned (ev E k) + to_Z off) bs /\ den E v = bytes_val false (to_Z w) bs.
Proof.
  intros E st ms mo k off w v HS Hw K H. unfold rload, do_load in H. cbn [addr_of] in H.
  pose proof (so_zero _ _ _ _ _ _ HS) as Hz. pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  assert (Hw8 : 1 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate].
  destruct (Mem.okey (wlit off)) as [key|] eqn:Hk; [|discriminate].
  destruct (can_read rsegs (s_facts st) (s_priv st) k r key w) eqn:CR; [|discriminate].
  destruct (Mem.region_load rsegs k r key w false) as [v'|] eqn:RL; [|discriminate]. injection H as <-.
  pose proof (so_reg _ _ _ _ _ _ HS k r Hr) as RO.
  destruct (region_load_sound rsegs (s_priv st) E (ms_mem ms) (s_facts st) k r key w false v' Hfs Hz RO Hw CR RL) as (bs & Len & OV & Dv).
  pose proof (can_read_sound rsegs (s_priv st) E (ms_mem ms) (s_facts st) k r key w Hfs Hz RO Hw CR) as (RA & RAw & _ & IN & _).
  cbv zeta in IN. specialize (IN K). pose proof (okey_wlit off key Hk) as EK. unfold addrZ in RA, RAw, OV. rewrite EK in RA, RAw, OV, IN.
  pose proof (ro_range _ _ _ _ _ _ RO K) as [_ RH].
  exists r, bs. split; [reflexivity|]. split; [exact Len|]. split; [specialize (IN 0 ltac:(lia)); lia|].
  split; [specialize (IN (to_Z w - 1) ltac:(lia)); lia|]. split; [unfold two64 in RH; lia|]. split.
  - apply (bytes_at_of_ov_read (ms_mem ms) _ (Z.to_nat (to_Z w)) bs); [lia| unfold two64 in RAw; lia| exact OV].
  - rewrite (den_narrow_f E (s_facts st) Hfs). exact Dv.
Qed.

Lemma blob_region_bytes : forall priv E m k r j (o : Z) (n : nat),
  St.region_ok rsegs priv E m k r -> PrimInt63.eqb k 0%uint63 = false -> Mem.rg_cells r = IMap.Leaf -> Mem.rg_bg r = Mem.BGBlob j 0%uint63 ->
  0 <= o -> loZ r <= o -> o + Z.of_nat n <= hiZ E r ->
  bytes_at rsegs m (bv_unsigned (ev E k) + o) (map (fun i => nth (Z.to_nat o + i)%nat (eb E j) (Z_to_bv 8 0)) (seq 0 n)).
Proof.
  intros priv E m k r j o n RO K HC HB Ho Hlo Hhi.
  pose proof (ro_range _ _ _ _ _ _ RO K) as [RL RH]. unfold two64 in RH.
  split; [lia|]. rewrite length_map, length_seq. split; [lia|].
  intros i Hi. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec i n); [|lia]. cbn [option_map Nat.add].
  rewrite <- rb_mrd. replace (bv_unsigned (ev E k) + o + Z.of_nat i) with (bv_unsigned (ev E k) + (o + Z.of_nat i)) by lia.
  pose proof (ro_bg _ _ _ _ _ _ RO (o + Z.of_nat i) ltac:(intros _; lia) ltac:(intros X; rewrite K in X; discriminate X)) as G.
  unfold bg_byte in G. rewrite HB in G. change (to_Z 0%uint63) with 0 in G. rewrite Z.sub_0_r in G.
  replace (Z.to_nat (o + Z.of_nat i)) with (Z.to_nat o + i)%nat in G by lia. apply G.
  intros g gr _ Hf. rewrite HC in Hf. cbn in Hf. discriminate Hf.
Qed.

Lemma le8_wz : forall x, 0 <= x < 2 ^ 64 -> Z_to_le_bytes 8 x = le8 (wz x).
Proof. intros x Hx. unfold le8, word_to_le_bytes, wz. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64; lia). reflexivity. Qed.
Lemma wz_unsigned : forall w : word, wz (bv_unsigned w) = w.
Proof. intros w. unfold wz. apply Z_to_bv_bv_unsigned. Qed.

Lemma list_eq_nth_error : forall {T} (l1 l2 : list T), length l1 = length l2 ->
  (forall i, (i < length l1)%nat -> nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  intros T l1. induction l1 as [|x l1 IH]; intros [|y l2] L H; cbn in L; try discriminate; [reflexivity|].
  pose proof (H O ltac:(cbn; lia)) as H0. cbn in H0. injection H0 as ->. f_equal. apply IH; [lia|].
  intros i Hi. exact (H (S i) ltac:(cbn; lia)).
Qed.

Lemma secret_bytes : forall E, PB (eb E) ->
  map (fun i => nth (8 + i)%nat (eb E 6%uint63) (Z_to_bv 8 0)) (seq 0 8) = le8 (wz ctx_secret).
Proof.
  intros E HPB. apply list_eq_nth_error.
  - rewrite length_map, length_seq, length_le8. reflexivity.
  - intros i Hi. rewrite length_map, length_seq in Hi. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec i 8); [|lia]. cbn [option_map Nat.add].
    pose proof (PB_secret E HPB i Hi) as P.
    destruct (nth_error (le8 (wz ctx_secret)) i) as [b|] eqn:Hb.
    + f_equal. apply nth_error_nth. exact P.
    + exfalso. apply nth_error_None in Hb. rewrite length_le8 in Hb. lia.
Qed.

Lemma bytes_at_cons8 : forall m a c (w : word) rest,
  bytes_at rsegs m (a + c) (le8 w) -> bytes_at rsegs m (a + (c + 8)) rest -> bytes_at rsegs m (a + c) (le8 w ++ rest).
Proof.
  intros m a c w rest H1 H2. apply (proj2 (bytes_at_app rsegs m (a + c) (le8 w) rest)). split; [exact H1|].
  rewrite length_le8. replace (a + c + Z.of_nat 8) with (a + (c + 8)) by lia. exact H2.
Qed.

Ltac lit_ints := repeat match goal with |- context [to_Z ?x] => let v := eval vm_compute in (to_Z x) in change (to_Z x) with v end.
Ltac lit_ints_in H := repeat match type of H with context [to_Z ?x] => let v := eval vm_compute in (to_Z x) in change (to_Z x) with v in H end.

Lemma auxv_sound : forall E st ms mo B,
  St.st_ok rsegs OPS E st ms mo -> PB (eb E) -> auxv_ok rsegs st = true ->
  rw_cells rsegs (ms_mem ms) RAUXV_CELL [C8 (ev E AUXV_ID)] ->
  alloc_ceiling <= B -> B <= bv_unsigned (ev E AUXV_ID) -> B <= bv_unsigned (ev E RND_ID) ->
  rauxv_ok (ms_mem ms) B.
Proof.
  intros E st ms mo B HS HPB H HC HB1 HB2 HB3. unfold auxv_ok in H.
  apply andb_prop in H as [H HR]. apply andb_prop in H as [H H152]. apply andb_prop in H as [H H136].
  cbn [auxv_keys_ok AUXV_KEYS PrimInt63.add] in H. rewrite !andb_true_r in H.
  repeat match goal with X : _ && _ = true |- _ => apply andb_prop in X as [? ?] end.

  repeat match goal with
  | X : is_litv (rload _ _ _ ?o _) _ = true |- _ => apply is_litv_inv in X
  | X : match rload ?sg ?st ?k ?o ?w with Some _ => true | None => false end = true |- _ =>
      destruct (rload sg st k o w) eqn:?L in X; [clear X| discriminate X]
  end.
  apply is_sv_inv in H136.
  repeat match goal with
  | X : rload rsegs st AUXV_ID ?o 8%uint63 = Some _ |- _ =>
      apply (rload_inv E st ms mo AUXV_ID o 8%uint63 _ HS wok8 eq_refl) in X;
      destruct X as (?rg & ?bys & ?Hreg & ?Ln & ?LO & ?HI & ?RH & ?BA & ?DV); cbn in Ln
  end.

  unfold rnd_region_ok in HR. destruct (IMap.find RND_ID (s_regs st)) as [qr|] eqn:Hqr; [|discriminate].
  destruct (Mem.rg_cells qr) eqn:HCq; try discriminate. destruct (Mem.rg_bg qr) as [| | | |j sh] eqn:HBq; try discriminate.
  apply andb_prop in HR as [HR HLq]. apply andb_prop in HR as [HR HLOq]. apply andb_prop in HR as [HJ HSH].
  apply Uint63.eqb_correct in HJ. apply Uint63.eqb_correct in HSH. apply Uint63.eqb_correct in HLOq. subst j sh.
  destruct (rload rsegs st RND_ID 8%uint63 8%uint63) as [vq|] eqn:Lq; [|discriminate].
  destruct (rload_inv E st ms mo RND_ID 8%uint63 8%uint63 vq HS wok8 eq_refl Lq) as (qr' & bsq & Hqr' & _ & _ & HIq & RHq & _ & _).
  rewrite Hqr in Hqr'. injection Hqr' as <-. lit_ints_in HIq.
  pose proof (blob_region_bytes (s_priv st) E (ms_mem ms) RND_ID qr RND_ID 8 8 (so_reg _ _ _ _ _ _ HS _ _ Hqr) eq_refl HCq HBq
                ltac:(lia) ltac:(unfold loZ; rewrite HLOq; change (keyZ 0%uint63) with 0; lia) ltac:(cbn; lia)) as SEC.
  rewrite (secret_bytes E HPB) in SEC.

  repeat match goal with
  | Ln : length ?bs = Z.to_nat (to_Z 8%uint63), DV : den E ?v = bytes_val false (to_Z 8%uint63) ?bs, BA : bytes_at _ _ _ ?bs |- _ =>
      change (Z.to_nat (to_Z 8%uint63)) with 8%nat in Ln; change (to_Z 8%uint63) with 8 in DV;
      first [ rewrite (lit_load_bytes E 8 bs _ Ln ltac:(lia) DV) in BA; rewrite le8_wz in BA by (lit_ints; lia)
            | rewrite (load8_bytes E bs v Ln DV) in BA; try rewrite (den_VPz E) in BA; rewrite <- (wz_unsigned (den E v)) in BA || rewrite <- (wz_unsigned (ev E RND_ID)) in BA ];
      clear Ln DV; lit_ints_in BA
  end.
  rewrite <- (wz_unsigned (ev E AUXV_ID)) in HC.
  set (av := bv_unsigned (ev E AUXV_ID)) in *. set (rnd := bv_unsigned (ev E RND_ID)) in *.
  match goal with H : to_Z 152%uint63 + to_Z 8%uint63 <= hiZ E ?r, H' : av + hiZ E ?r < 2 ^ 64 |- _ =>
    lit_ints_in H; assert (AVH : av + 160 <= 2 ^ 64) by lia end.
  unfold rauxv_ok. eexists av, _, _, _, _, _, _, _, _, rnd.
  split; [exact HC|]. split; [| split; [exact SEC|]].
  - unfold auxv_list. cbn [map u64s app]. rewrite <- (Z.add_0_r av) at 1.
    repeat (apply bytes_at_cons8; [eassumption|];
            match goal with |- bytes_at _ _ (_ + ?c) _ => let v := eval vm_compute in c in change c with v end).
    apply bytes_at_nil. pose proof (bv_unsigned_in_range 64 (ev E AUXV_ID)). lia.
  - pose proof (bv_unsigned_in_range 64 (ev E RND_ID)) as RR. unfold bv_modulus in RR.
    repeat match goal with |- context [bv_unsigned (den E ?v)] =>
      lazymatch goal with _ : 0 <= bv_unsigned (den E v) < _ |- _ => fail | _ => pose proof (bv_unsigned_in_range 64 (den E v)) end end.
    unfold bv_modulus in *. cbn -[Z.pow av rnd alloc_ceiling Z.le Z.lt Z.add] in *. lia.
Qed.

Lemma auxv_region : forall E st ms mo, St.st_ok rsegs OPS E st ms mo -> auxv_ok rsegs st = true ->
  exists r3, IMap.find AUXV_ID (s_regs st) = Some r3.
Proof.
  intros E st ms mo HS H. unfold auxv_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H].
  apply is_sv_inv in H. destruct (rload_inv E st ms mo AUXV_ID 136%uint63 8%uint63 _ HS wok8 eq_refl H) as (r3 & bs & Hr3 & _).
  exists r3. exact Hr3.
Qed.

Lemma w2Zs_wsub_small : forall a b, - two63 <= w2Zs a - w2Zs b < two63 -> w2Zs (wsub a b) = w2Zs a - w2Zs b.
Proof.
  intros a b H. rewrite (w2Zs_eq (wsub a b)), w2Z_wt, wsub_ok.
  rewrite (w2Zs_eq a), (w2Zs_eq b), (w2Z_wt a), (w2Z_wt b) in H |- *.
  pose proof (w2Z_range a) as Ra. pose proof (w2Z_range b) as Rb. unfold two63, two64 in *.
  destruct (Z.leb_spec 9223372036854775808 (w2Z a)), (Z.leb_spec 9223372036854775808 (w2Z b));
  destruct (Z_lt_le_dec (w2Z a - w2Z b) 0);
  try (replace (w2Z a - w2Z b) with ((w2Z a - w2Z b + 18446744073709551616) + (-1) * 18446744073709551616) by lia;
       rewrite Z.mod_add, Z.mod_small by lia;
       destruct (Z.leb_spec 9223372036854775808 (w2Z a - w2Z b + 18446744073709551616)); lia);
  try (rewrite (Z.mod_small (w2Z a - w2Z b)) by lia; destruct (Z.leb_spec 9223372036854775808 (w2Z a - w2Z b)); lia).
Qed.

Lemma stack_sound : forall E st ms mo need ksp klo1,
  St.st_ok rsegs OPS E st ms mo -> to_Z need < 2 ^ 32 -> stack_ok st need = Some (ksp, klo1) ->
  exists off r1, getr st X2 = VP STACK_ID off /\ IMap.find STACK_ID (s_regs st) = Some r1
    /\ Mem.rg_w r1 = true /\ Mem.rg_bg r1 = Mem.BGNone /\ Mem.okey off = Some ksp /\ klo1 = Mem.rg_lo r1 /\ keyZ ksp mod 16 = 0
    /\ keyZ ksp < 0
    /\ bv_unsigned (den E (getr st X2)) = bv_unsigned (ev E STACK_ID) + keyZ ksp
    /\ 0 <= bv_unsigned (ev E STACK_ID) + loZ r1
    /\ bv_unsigned (ev E STACK_ID) + loZ r1 <= bv_unsigned (ev E STACK_ID) + keyZ ksp - to_Z need
    /\ bv_unsigned (ev E STACK_ID) + keyZ ksp <= bv_unsigned (ev E STACK_ID) + hiZ E r1 < 2 ^ 64
    /\ stk rsegs (ms_mem ms) (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + hiZ E r1).
Proof.
  intros E st ms mo need ksp klo1 HS Hneed H. unfold stack_ok in H.
  destruct (getr st X2) as [|k off| | | | | | | | |] eqn:HX2; try discriminate.
  destruct (IMap.find STACK_ID (s_regs st)) as [r1|] eqn:Hr1; [|discriminate].
  destruct (PrimInt63.eqb k STACK_ID) eqn:HK; [|discriminate]. apply Uint63.eqb_correct in HK. subst k.
  destruct (Mem.rg_w r1) eqn:HW; [|discriminate]. destruct (Mem.rg_bg r1) eqn:HBG; try discriminate. cbn [negb orb] in H.
  destruct (Mem.okey off) as [ksp'|] eqn:Hksp; [|discriminate].
  destruct (Mem.okey (wsub off (wlit need))) as [klo|] eqn:Hklo; [|discriminate].
  destruct (Mem.rg_hi r1) as [h| | | | | | | | | |] eqn:Hhi; try discriminate.
  destruct (Mem.okey h) as [kh|] eqn:Hkh; [|discriminate].
  destruct (Mem.kleb (Mem.rg_lo r1) klo) eqn:L1; [|discriminate]. destruct (Mem.kleb ksp' kh) eqn:L2; [|discriminate].
  destruct (PrimInt63.eqb (PrimInt63.land ksp' 15) 0) eqn:AL; [|discriminate].
  destruct (PrimInt63.leb bit62i ksp') eqn:NEG; [|discriminate]. cbn [andb] in H. injection H as -> <-.
  rewrite kleb_keyZ in L1, L2. apply Z.leb_le in L1. apply Z.leb_le in L2.
  destruct (okey_sound _ _ Hksp) as [Eksp Rksp]. destruct (okey_sound _ _ Hklo) as [Eklo Rklo]. destruct (okey_sound _ _ Hkh) as [Ekh Rkh].
  rewrite !half63 in Rksp, Rklo, Rkh.
  assert (Eneed : w2Zs (wlit need) = to_Z need) by (rewrite w2Zs_eq, wlit_ok; cbn [wt wlit]; lia).
  pose proof (int_range need) as Rn. rewrite two63_eq in Rn.
  assert (Eklo' : keyZ klo = keyZ ksp - to_Z need).
  { rewrite Eklo, w2Zs_wsub_small; [rewrite Eneed, Eksp; reflexivity|].
    rewrite Eneed, <- Eksp. unfold two63 in *. lia. }
  pose proof (so_reg _ _ _ _ _ _ HS _ _ Hr1) as RO.
  pose proof (ro_range _ _ _ _ _ _ RO eq_refl) as [RLO RHI]. unfold two64 in RHI.
  assert (Ehi : keyZ kh <= hiZ E r1).
  { unfold hiZ. rewrite Hhi, unsigned_VL, Ekh, w2Zs_eq. unfold two64. destruct (wt h); lia. }
  exists off, r1. split; [reflexivity|]. split; [reflexivity|]. split; [exact HW|]. split; [exact HBG|]. split; [exact Hksp|]. split; [reflexivity|]. split.
  { apply Uint63.eqb_correct in AL. pose proof (land_mk ksp 4%uint63 ltac:(change (to_Z 4%uint63) with 4; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 4) 1)%uint63 with 15%uint63 in LM. rewrite AL in LM.
    change (to_Z 0%uint63) with 0 in LM. change (2 ^ to_Z 4%uint63) with 16 in LM.
    destruct (keyZ_cases ksp) as [[_ ->]|[_ ->]]; [lia|].
    replace (to_Z ksp - 2 ^ 63) with (to_Z ksp + (- 2 ^ 59) * 16) by lia. rewrite Z.mod_add by lia. lia. }
  split. { apply Uint63.leb_spec in NEG. rewrite to_Z_bit62i in NEG. destruct (keyZ_cases ksp) as [[R EK]|[R EK]]; [lia| rewrite EK; lia]. }
  assert (Esp : bv_unsigned (den E (VP STACK_ID off)) = bv_unsigned (ev E STACK_ID) + keyZ ksp).
  { rewrite den_VP, <- Eksp. unfold loZ in *. apply Z.mod_small. unfold two64. lia. }
  split; [exact Esp|]. unfold loZ in *. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (ro_valid _ _ _ _ _ _ RO eq_refl a Ha) as (V1 & V2 & _).
  split; [apply wb_wview; apply V2; exact HW|]. rewrite rb_mrd in V1. destruct (mrd rsegs (ms_mem ms) (wa a)); [eexists; reflexivity| congruence].
Qed.

Lemma weqb_wzero_unsigned' : forall c, weqb c wzero = true -> w2Z c = 0.
Proof. intros c H. apply weqb_eq in H. subst. reflexivity. Qed.

Lemma heap_windows_inv : forall st klo1 hargs wnl,
  heap_windows st klo1 = Some (hargs, wnl) ->
  find_op HEAP_ID (s_ops st) = Some hargs /\ count_op HEAP_ID (s_ops st) = 1%nat
  /\ exists n md A nw rest, heap_nwin hargs = Some n /\ hargs = VL md :: A :: VL nw :: rest
     /\ wt nw = false /\ n = Z.to_nat (to_Z (wl nw)) /\ (3 * n <= length rest)%nat /\ (n <= 255)%nat
     /\ stack_window_ok n rest klo1 = true /\ nonstack_windows n rest = Some wnl
     /\ windows_anchored (s_regs st) wnl = true /\ regions_justified st wnl = true.
Proof.
  intros st klo1 hargs wnl H. unfold heap_windows in H.
  destruct (find_op HEAP_ID (s_ops st)) as [h|] eqn:Hf; [|discriminate].
  destruct (count_op HEAP_ID (s_ops st)) as [|[|c]] eqn:Hc; try discriminate.
  destruct (heap_nwin h) as [n|] eqn:Hn; [|discriminate].
  destruct (heap_nwin_shape h n Hn) as (md & A & nw & rest & Eh & T & N & L). rewrite Eh in H.
  destruct (Nat.leb n 255) eqn:N255; [|discriminate]. apply Nat.leb_le in N255. cbn [andb] in H.
  destruct (stack_window_ok n rest klo1) eqn:SW; [|discriminate].
  destruct (nonstack_windows n rest) as [wl'|] eqn:NW; [|discriminate].
  destruct (windows_anchored (s_regs st) wl' && regions_justified st wl') eqn:AJ; [|discriminate]. injection H as <- <-.
  apply andb_prop in AJ as [A1 A2]. subst h. split; [reflexivity|]. split; [reflexivity|].
  exists n, md, A, nw, rest. repeat (split; [assumption || reflexivity|]). exact A2.
Qed.

Lemma stack_window_In : forall E n rest klo,
  stack_window_ok n rest klo = true ->
  exists wlo len, Mem.okey wlo = Some klo /\ In (Win (bv_unsigned (den E (VP STACK_ID wlo))) len K_STACK) (wins_of E n rest).
Proof.
  intros E n. induction n as [|n IH]; intros rest klo H; [cbn in H; destruct rest; discriminate|].
  destruct rest as [|lo rest1]; [cbn in H; discriminate|].
  destruct rest1 as [|len rest2]; [destruct lo; cbn in H; discriminate|].
  destruct rest2 as [|kd rest']; [destruct lo; cbn in H; discriminate|].
  cbn [stack_window_ok] in H.
  assert (STEP : stack_window_ok n rest' klo = true ->
            exists wlo len0, Mem.okey wlo = Some klo /\ In (Win (bv_unsigned (den E (VP STACK_ID wlo))) len0 K_STACK) (wins_of E (S n) (lo :: len :: kd :: rest'))).
  { intros H'. destruct (IH rest' klo H') as (wlo & len0 & K1 & K2). exists wlo, len0. split; [exact K1|]. rewrite wins_of_cons. right. exact K2. }
  destruct lo as [|k wlo| | | | | | | | |]; cbn in H; try (apply STEP; exact H).
  destruct kd as [kdw| | | | | | | | | |]; cbn in H; try (apply STEP; exact H).
  apply orb_prop in H as [H|H]; [| apply STEP; exact H].
  apply andb_prop in H as [H HK]. apply andb_prop in H as [H1 H2].
  apply Uint63.eqb_correct in H1. subst k. destruct (Mem.okey wlo) as [kw|] eqn:Hkw; [|discriminate].
  apply Uint63.eqb_correct in HK. subst kw.
  exists wlo, (bv_unsigned (den E len)). split; [exact Hkw|]. rewrite wins_of_cons. left.
  unfold K_STACK. rewrite (unsigned_VL E kdw), (weqb_wzero_unsigned' kdw H2). reflexivity.
Qed.

Lemma known_ltu_sound : forall E fs a b, facts_hold E fs -> known_ltu fs a b = true -> bv_unsigned (den E a) < bv_unsigned (den E b).
Proof.
  intros E fs a b Hfs H. unfold known_ltu, dec_true in H. destruct (decide_ltu fs a b) as [[|]|] eqn:D; try discriminate H.
  exact (proj1 (ltu_iff _ _ true) (ValP.decide_ltu_sound E fs Hfs a b true D)).
Qed.
Lemma known_leu_sound : forall E fs a b, facts_hold E fs -> known_leu fs a b = true -> bv_unsigned (den E a) <= bv_unsigned (den E b).
Proof.
  intros E fs a b Hfs H. unfold known_leu, dec_false in H. destruct (decide_ltu fs b a) as [[|]|] eqn:D; try discriminate H.
  exact (proj1 (ltu_iff _ _ false) (ValP.decide_ltu_sound E fs Hfs b a false D)).
Qed.

Lemma known_leu_q_sound : forall E fs a b, facts_hold E fs -> known_leu_q fs a b = true -> bv_unsigned (den E a) <= bv_unsigned (den E b).
Proof.
  intros E fs a b Hfs H. unfold known_leu_q in H.
  destruct (sv_eqb a b) eqn:Q; [apply ValP.sv_eqb_eq in Q; subst; lia|].
  destruct (fact_lookup fs (is_FULe a b)) eqn:L1.
  { destruct (ValP.fact_lookup_holds E fs _ Hfs L1) as (f & HF & PF). destruct f; try discriminate PF. cbn [is_FULe] in PF.
    apply andb_prop in PF as [P1 P2]. apply ValP.sv_eqb_eq in P1, P2. subst. cbn [fact_holds] in HF. exact HF. }
  destruct (fact_lookup fs (is_FULt a b)) eqn:L2.
  { destruct (ValP.fact_lookup_holds E fs _ Hfs L2) as (f & HF & PF). destruct f; try discriminate PF. cbn [is_FULt] in PF.
    apply andb_prop in PF as [P1 P2]. apply ValP.sv_eqb_eq in P1, P2. subst. cbn [fact_holds] in HF. lia. }
  exact (known_leu_sound E fs a b Hfs H).
Qed.
Lemma anchored_above_sound : forall E fs k, facts_hold E fs ->
  anchored_above fs k = true -> bv_unsigned (ev E STACK_ID) <= bv_unsigned (ev E k).
Proof.
  intros E fs k Hfs H. unfold anchored_above in H. apply existsb_exists in H as (f & Hin & Hf).
  pose proof (proj1 (Forall_forall _ _) Hfs f Hin) as HF.
  destruct f as [| | | |a b| | |]; try discriminate Hf. destruct a as [|k' z| | | | | | | | |]; try discriminate Hf. destruct b as [|s o| | | | | | | | |]; try discriminate Hf.
  destruct (PrimInt63.eqb k' k) eqn:K; [|discriminate Hf]. apply Uint63.eqb_correct in K. subst k'.
  apply andb_prop in Hf as [Hf NW]. apply andb_prop in Hf as [Hf WT]. apply andb_prop in Hf as [Z0 S1].
  apply weqb_eq in Z0. subst z. apply Uint63.eqb_correct in S1. subst s.
  cbn [fact_holds] in HF. destruct (ValP.nowrap_k_sound E fs Hfs _ _ NW) as (R & D).
  rewrite <- (den_VPz E k), HF, D. rewrite ValP.w2Zs_eq. destruct (wt o); [discriminate WT|]. pose proof (w2Z_range o). lia.
Qed.
Lemma stack_side_sound : forall E fs sp k, facts_hold E fs ->
  stack_side fs sp (sp_below_anchor fs sp) k = true -> bv_unsigned (den E sp) <= bv_unsigned (ev E k).
Proof.
  intros E fs sp k Hfs H. unfold stack_side, sp_below_anchor in H.
  destruct (known_leu fs sp (VP STACK_ID wzero)) eqn:A.
  - destruct (anchored_above fs k) eqn:AA.
    { apply (known_leu_sound E _ _ _ Hfs) in A. rewrite (den_VPz E STACK_ID) in A. pose proof (anchored_above_sound E fs k Hfs AA). lia. }
    destruct (known_leu fs (VP STACK_ID wzero) (VP k wzero)) eqn:B.
    + apply (known_leu_sound E _ _ _ Hfs) in A. apply (known_leu_sound E _ _ _ Hfs) in B. rewrite (den_VPz E STACK_ID) in A, B. rewrite (den_VPz E k) in B. lia.
    + apply (known_leu_sound E _ _ _ Hfs) in H. rewrite den_VPz in H. exact H.
  - apply (known_leu_sound E _ _ _ Hfs) in H. rewrite den_VPz in H. exact H.
Qed.
Lemma region_justified_inv : forall E fs sp wl k r, facts_hold E fs ->
  region_justified fs sp (sp_below_anchor fs sp) wl k r = true -> k <> 0%uint63 -> k <> STACK_ID ->
  Mem.rg_lo r = 0%uint63 /\
  (bv_unsigned (den E sp) <= bv_unsigned (ev E k)
   \/ exists len kd, win_lookup wl k = Some (len, kd) /\ known_leu_q fs (Mem.rg_hi r) len = true).
Proof.
  intros E fs sp wl k r Hfs J K0 K1. unfold region_justified in J.
  destruct (Uint63.eqb k 0%uint63) eqn:Q0; [apply Uint63.eqb_correct in Q0; congruence|].
  destruct (Uint63.eqb k STACK_ID) eqn:Q1; [apply Uint63.eqb_correct in Q1; congruence|].
  destruct (Uint63.eqb (Mem.rg_lo r) 0%uint63) eqn:L0; [|discriminate]. apply Uint63.eqb_correct in L0.
  split; [exact L0|].
  destruct (win_lookup wl k) as [[len kd]|] eqn:WL.
  - destruct (known_leu_q fs (Mem.rg_hi r) len) eqn:W.
    + right. exists len, kd. split; [reflexivity| exact W].
    + left. exact (stack_side_sound E fs sp k Hfs J).
  - left. exact (stack_side_sound E fs sp k Hfs J).
Qed.
Lemma known_eq_sound : forall E fs a b, facts_hold E fs -> known_eq fs a b = true -> den E a = den E b.
Proof.
  intros E fs a b Hfs H. unfold known_eq, dec_true in H. destruct (decide_eq fs a b) as [[|]|] eqn:D; try discriminate H.
  exact (proj1 (eqb_iff _ _ true) (ValP.decide_eq_sound E fs Hfs a b true D)).
Qed.

Lemma getr_R : forall E st ms mo, St.st_ok rsegs OPS E st ms mo ->
  forall x, PropExec.getr (ms_regs ms) (reg_of_r5 x) = den E (getr st x).
Proof.
  intros E st ms mo HS x. pose proof (so_regs _ _ _ _ _ _ HS x) as R. unfold rget in R. cbn [c_regs] in R.
  unfold PropExec.getr, getr. unfold is_x0 in R.
  destruct x; cbn [reg_of_r5 r5_to_Z] in R |- *; first [exact R | rewrite <- R; reflexivity].
Qed.

Lemma reg_of_X1 : reg_of_r5 X1 = 1%bv. Proof. apply bv_eq. reflexivity. Qed.
Lemma reg_of_X2 : reg_of_r5 X2 = 2%bv. Proof. apply bv_eq. reflexivity. Qed.
Lemma reg_of_X4 : reg_of_r5 X4 = 4%bv. Proof. apply bv_eq. reflexivity. Qed.
Lemma reg_of_X10 : reg_of_r5 X10 = 10%bv. Proof. apply bv_eq. reflexivity. Qed.
Lemma reg_of_X11 : reg_of_r5 X11 = 11%bv. Proof. apply bv_eq. reflexivity. Qed.
Lemma reg_of_X12 : reg_of_r5 X12 = 12%bv. Proof. apply bv_eq. reflexivity. Qed.

Set Implicit Arguments.
Record callG (E : env) (st : sstate) (ms : machine_state) (mo : Model) (need r ksp : int) (hargs : list sv)
       (wnl : list (int * sv * w64)) (off : w64) (r1 : Mem.region) (n : nat) (md : w64) (A : sv) (nw : w64) (rest : list sv)
       (s : PState) (LBf : list block) (LB : blocks) : Prop := CG {
  cg_ms : ms = MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 (to_Z (s_pc st))) (ms_fcsr ms) None (ms_mem ms) (seg_rom rsegs);
  cg_regs : forall x, PropExec.getr (ms_regs ms) (reg_of_r5 x) = den E (getr st x);
  cg_tp : PropExec.getr (ms_regs ms) 4%bv = Z_to_bv 64 RATP;
  cg_ra : MState.ret_pc (PropExec.getr (ms_regs ms) 1%bv) = PropExec.getr (ms_regs ms) 1%bv;
  cg_ra_r : PropExec.getr (ms_regs ms) 1%bv = Z_to_bv 64 (to_Z r);
  cg_r62 : to_Z r < 2 ^ 62;
  cg_fresh : fresh_ok st = true;

  cg_x2 : getr st X2 = VP STACK_ID off;
  cg_r1 : IMap.find STACK_ID (s_regs st) = Some r1;
  cg_r1w : Mem.rg_w r1 = true;
  cg_r1bg : Mem.rg_bg r1 = Mem.BGNone;
  cg_ksp : Mem.okey off = Some ksp;
  cg_ksp16 : keyZ ksp mod 16 = 0;
  cg_kspneg : keyZ ksp < 0;
  cg_sp : bv_unsigned (PropExec.getr (ms_regs ms) 2%bv) = bv_unsigned (ev E STACK_ID) + keyZ ksp;
  cg_lo0 : 0 <= bv_unsigned (ev E STACK_ID) + loZ r1;
  cg_room : bv_unsigned (ev E STACK_ID) + loZ r1 <= bv_unsigned (ev E STACK_ID) + keyZ ksp - to_Z need;
  cg_hi : bv_unsigned (ev E STACK_ID) + keyZ ksp <= bv_unsigned (ev E STACK_ID) + hiZ E r1 < 2 ^ 64;
  cg_stk : stk rsegs (ms_mem ms) (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + hiZ E r1);
  cg_ceil : alloc_ceiling <= bv_unsigned (ev E STACK_ID) + loZ r1;

  cg_statics : statics_ok rsegs ERRNO LIBC GOT GUARD CANARY st = true;
  cg_pubs : PUBS (ms_mem ms);
  cg_auxcell : rw_cells rsegs (ms_mem ms) RAUXV_CELL [C8 (ev E AUXV_ID)];
  cg_r3 : exists r3, IMap.find AUXV_ID (s_regs st) = Some r3;
  cg_auxv : rauxv_ok (ms_mem ms) (bv_unsigned (ev E STACK_ID) + keyZ ksp);
  cg_errno : exists errv, rw_cells rsegs (ms_mem ms) RERRNO [C4 errv];
  cg_minv : mem_inv rsegs (ms_mem ms);
  cg_mo : mo_ok mo;

  cg_find : find_op HEAP_ID (s_ops st) = Some hargs;
  cg_count : count_op HEAP_ID (s_ops st) = 1%nat;
  cg_nwin : heap_nwin hargs = Some n;
  cg_hargs : hargs = VL md :: A :: VL nw :: rest;
  cg_nw : wt nw = false /\ n = Z.to_nat (to_Z (wl nw)) /\ (3 * n <= length rest)%nat;
  cg_n255 : (n <= 255)%nat;
  cg_decode : decode (map (den E) hargs) = Some (w2Z md, den E A, wins_of E n rest, map (den E) (skipn (3 * n) rest));
  cg_perm : Permutation (blocks_of LBf) LB;
  cg_rheap : RHEAP s LBf (ms_mem ms);
  cg_krel : KREL s LBf mo;
  cg_claim : pclaim (bv_unsigned (den E A)) s LBf mo;
  cg_repl : rw_cells rsegs (ms_mem ms) RMREPL [C4 (wz 0)];
  cg_wf : windows_wf (wins_of E n rest) LB alloc_ceiling;
  cg_ng : NG (wins_of E n rest);
  cg_cw : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * n) rest)) LB (wins_of E n rest) (ms_mem ms);
  cg_swin : stack_window_ok n rest (Mem.rg_lo r1) = true;
  cg_wnl : nonstack_windows n rest = Some wnl;
  cg_anch : windows_anchored (s_regs st) wnl = true;
  cg_just : regions_justified st wnl = true }.
Unset Implicit Arguments.

Theorem alloc_call_sound : forall E st ms mo need r ksp hargs wnl,
  St.st_ok rsegs OPS E st ms mo -> PB (eb E) -> to_Z need < 2 ^ 32 ->
  alloc_call rsegs ERRNO LIBC GOT GUARD TP CANARY need st = Some (r, ksp, hargs, wnl) ->
  exists off r1 n md A nw rest s LBf LB, callG E st ms mo need r ksp hargs wnl off r1 n md A nw rest s LBf LB.
Proof.
  intros E st ms mo need r ksp hargs wnl HS HPB Hneed H. pose proof (int_range need) as Rneed.
  destruct (alloc_call_inv need st r ksp hargs wnl H) as (Hrv & Hcp & Hr62 & (ra & Hra & Hev) & Htp & Hst & Hav & Hab & klo1 & Hstk & Hhw).
  destruct (call_pre_inv st r Hcp) as (Hfr & ra' & Hra' & Twt & Tlt & ->). rewrite Hra in Hra'. injection Hra' as <-.
  destruct (statics_sound E st ms mo HS HPB Hst) as (PU & AC & ER).
  destruct (stack_sound E st ms mo need ksp klo1 HS Hneed Hstk) as (off & r1 & HX2 & Hr1 & HW & HBG & Hksp & -> & A16 & NEG & Esp & LO0 & ROOM & HI & STK).
  destruct (heap_windows_inv st (Mem.rg_lo r1) hargs wnl Hhw) as (Hf & Hc & n & md & A & nw & rest & Hn & Eh & T & N & L & N255 & SW & NW & AN & JU).
  pose proof (ops_hold_find OPS E (s_ops st) (ms_mem ms) mo HEAP_ID _ (so_ops _ _ _ _ _ _ HS) Hf) as HH.
  rewrite OPS_holds1 in HH. destruct HH as (md' & aw & ws & ca & LB & D & HA & WF & HC).
  rewrite Eh, (decode_hargs E md A nw rest n T N L) in D. injection D as <- <- <- <-.
  destruct HA as ((s & LBf & P & RC & K & MT & CL & RP) & NGW).

  destruct (stack_window_In E n rest (Mem.rg_lo r1) SW) as (wlo & wlen & Hwlo & INw).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & [[_ CE]|[[KB _]|[KS _]]]); cbn [w_kind w_lo] in *;
    [| unfold K_BLOCK, K_STACK in KB; lia | unfold K_SUB, K_STACK in KS; lia].
  assert (Elo : bv_unsigned (den E (VP STACK_ID wlo)) = bv_unsigned (ev E STACK_ID) + loZ r1).
  { rewrite den_VP. destruct (okey_sound _ _ Hwlo) as [EK _]. unfold loZ in *. rewrite <- EK. apply Z.mod_small. unfold two64.
    pose proof (int_range need). lia. }
  rewrite Elo in CE. cbn [aw_ceiling AWI] in CE.
  pose proof (getr_R E st ms mo HS) as GR.
  assert (MSE : ms = MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 (to_Z (s_pc st))) (ms_fcsr ms) None (ms_mem ms) (seg_rom rsegs)).
  { rewrite (MS_eta ms) at 1 by exact (so_svc _ _ _ _ _ _ HS). f_equal.
    + exact (so_pc _ _ _ _ _ _ HS).
    + pose proof (so_resv _ _ _ _ _ _ HS) as RV. rewrite Hrv in RV. exact RV.
    + exact (so_rom _ _ _ _ _ _ HS). }
  assert (TP4 : PropExec.getr (ms_regs ms) 4%bv = Z_to_bv 64 RATP).
  { rewrite <- reg_of_X4, GR, Htp. rewrite den_wlit. reflexivity. }
  pose proof (int_range (wl ra)) as Rr. rewrite two63_eq in Rr.
  assert (RA1 : MState.ret_pc (PropExec.getr (ms_regs ms) 1%bv) = PropExec.getr (ms_regs ms) 1%bv).
  { rewrite <- reg_of_X1, GR, Hra, den_VL. unfold wbv. rewrite (w2Z_nowt ra Twt).
    apply ret_pc_even; [lia|].
    pose proof (land_mk (wl ra) 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite Hev in LM. change (to_Z 0%uint63) with 0 in LM.
    change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  assert (RA2 : PropExec.getr (ms_regs ms) 1%bv = Z_to_bv 64 (to_Z (wl ra))).
  { rewrite <- reg_of_X1, GR, Hra, den_VL. unfold wbv. rewrite (w2Z_nowt ra Twt). reflexivity. }
  assert (R62 : to_Z (wl ra) < 2 ^ 62).
  { apply Uint63.ltb_spec in Tlt. rewrite to_Z_bit62i in Tlt. exact Tlt. }
  assert (SP2 : bv_unsigned (PropExec.getr (ms_regs ms) 2%bv) = bv_unsigned (ev E STACK_ID) + keyZ ksp).
  { rewrite <- reg_of_X2, GR. exact Esp. }
  assert (AUX : rauxv_ok (ms_mem ms) (bv_unsigned (ev E STACK_ID) + keyZ ksp)).
  { unfold above_stack_ok in Hab. cbv zeta in Hab.
    destruct (stack_side (s_facts st) (getr st X2) (sp_below_anchor (s_facts st) (getr st X2)) AUXV_ID) eqn:B1; [|discriminate Hab].
    rename Hab into B2.
    apply (auxv_sound E st ms mo _ HS HPB Hav AC); [lia| |].
    + apply (stack_side_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in B1. rewrite Esp in B1. exact B1.
    + apply (stack_side_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in B2. rewrite Esp in B2. exact B2. }
  pose proof (auxv_region E st ms mo HS Hav) as R3.
  assert (MINV : mem_inv rsegs (ms_mem ms)).
  { intros a b Hm. unfold ro_addr. destruct (find_segment rsegs (bv_unsigned a) 1) as [seg|] eqn:Fs; [|reflexivity].
    rewrite (so_minv _ _ _ _ _ _ HS a b Hm seg Fs). reflexivity. }
  assert (MOK : mo_ok mo).
  { destruct (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS)) as [MH ML]. split; [exact MH|]. split; [exact ML| exact MT]. }
  assert (DEC : decode (map (den E) hargs) = Some (w2Z md, den E A, wins_of E n rest, map (den E) (skipn (3 * n) rest))).
  { rewrite Eh. exact (decode_hargs E md A nw rest n T N L). }
  assert (RH : RHEAP s LBf (ms_mem ms)). { apply RHEAP_split. split; [exact RC| exact PU]. }
  exists off, r1, n, md, A, nw, rest, s, LBf, LB.
  constructor; try assumption; auto.
Qed.

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.base stdpp.decidable stdpp.list stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.NodesM OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.DecodeM OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Prelim OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.KInv.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.MSafe OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KLink OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KOwn OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KStepC OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocBlocks OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocHINV OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Malloc_iface OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocTree.
Import F_syscalls.TwinB RMallocRep.TwinB RMallocTree.TwinB RMallocKit_B.TwinB RMalloc_iface.TwinB RMalloc_ifaceP.TwinB RF_aligned16.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsM.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.StateGlue OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.RegsEqv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.TreeBridgeN OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.KRel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MPath OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.Room OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.
Import HeapCore.TwinB MF.TwinB AW.TwinB RMallocG.TwinB RAllocG.TwinB.

Set Keyed Unification.
Import ListNotations.
Import W64 Val FI St Step Plan ValP MemP StepB StepM StepS PlanS CtrLib CtrA HeapOp CtrFX.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition ERRNO : int := 0x68bec%uint63.
Definition LIBC  : int := 0x88f20%uint63.
Definition GOT   : int := 0x56e68%uint63.
Definition GUARD : int := 0x88f00%uint63.
Definition TP    : int := 0x68c90%uint63.

Lemma ERRNO_eq : to_Z ERRNO = RERRNO. Proof. reflexivity. Qed.
Lemma LIBC_eq : to_Z LIBC = RLIBC. Proof. reflexivity. Qed.
Lemma GOT_eq : to_Z GOT = RGOT_SSP. Proof. reflexivity. Qed.
Lemma GUARD_eq : to_Z GUARD = RSSP_GUARD. Proof. reflexivity. Qed.
Lemma TP_eq : to_Z TP = RATP. Proof. reflexivity. Qed.
Lemma NEED_LOCKS_eq : to_Z (PrimInt63.add LIBC 3%uint63) = RNEED_LOCKS. Proof. reflexivity. Qed.
Lemma PAGE_SIZE_eq : to_Z (PrimInt63.add LIBC 48%uint63) = RPAGE_SIZE. Proof. reflexivity. Qed.
Lemma AUXV_CELL_eq : to_Z (PrimInt63.add LIBC 8%uint63) = RAUXV_CELL. Proof. reflexivity. Qed.

Lemma wr_NEED_LOCKS : Mem.abs_writable rsegs RNEED_LOCKS 1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wr_PAGE_SIZE : Mem.abs_writable rsegs RPAGE_SIZE 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wr_AUXV_CELL : Mem.abs_writable rsegs RAUXV_CELL 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wr_GOT : Mem.abs_writable rsegs RGOT_SSP 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wr_GUARD : Mem.abs_writable rsegs RSSP_GUARD 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wr_ERRNO : Mem.abs_writable rsegs RERRNO 4 = true. Proof. vm_compute. reflexivity. Qed.

Lemma rom_of_seg_rom : St.rom_of rsegs = seg_rom rsegs.
Proof. reflexivity. Qed.

Lemma rb_mrd : forall m a, rb rsegs m a = mrd rsegs m (wa a).
Proof. reflexivity. Qed.

Lemma wb_wview : forall m a, wb rsegs m a = true <-> wview rsegs m (wa a) <> None.
Proof. intros m a. unfold wb, wa. destruct (wview rsegs m (Z_to_bv 64 a)); split; congruence. Qed.

Lemma bytes_at_of_ov_read : forall m a n bs,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  ov_read_bytes rsegs m (wa a) n = Some bs -> bytes_at rsegs m a bs.
Proof.
  intros m a n. revert a. induction n as [|n IH]; intros a bs Ha Hn H.
  - cbn in H. injection H as <-. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [ov_read_bytes] in H. fold (mrd rsegs m (wa a)) in H.
    change (match m (wa a) with Some b => Some b | None => match memory_read rsegs (wa a) 1 with Some (b :: _) => Some b | _ => None end end)
      with (mrd rsegs m (wa a)) in H.
    destruct (mrd rsegs m (wa a)) as [b|] eqn:Hb; [|discriminate].
    destruct (ov_read_bytes rsegs m (wa a + 1)%bv n) as [bs'|] eqn:Hr; [|discriminate]. injection H as <-.
    rewrite wa_succ in Hr. pose proof (IH (a + 1) bs' ltac:(lia) ltac:(lia) Hr) as (_ & L & B).
    split; [lia|]. split; [cbn [length]; lia|].
    intros [|i] Hi; cbn [nth_error].
    + rewrite Z.add_0_r. exact Hb.
    + replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply B. cbn in Hi. lia.
Qed.

Lemma ov_read_bytes_length : forall m a n bs, ov_read_bytes rsegs m a n = Some bs -> length bs = n.
Proof.
  intros m a n. revert a. induction n as [|n IH]; intros a bs H; cbn [ov_read_bytes] in H.
  - injection H as <-. reflexivity.
  - destruct (match m a with Some b => Some b | None => _ end); [|discriminate].
    destruct (ov_read_bytes rsegs m (a + 1)%bv n) eqn:R; [|discriminate]. injection H as <-. cbn. f_equal. eapply IH. exact R.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
    pose proof (bytes_le_to_Z_nonneg bs) as NN.
    unfold bv_wrap. replace (bv_modulus 8) with 256 by reflexivity.
    rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. pose proof (bytes_le_to_Z_nonneg bs) as NN.
    rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. rewrite Z.add_0_r. exact IH.
Qed.

Lemma bytes_val_false_eq : forall n bs, length bs = n -> (1 <= n <= 8)%nat ->
  bv_unsigned (bytes_val false (Z.of_nat n) bs) = bytes_le_to_Z bs.
Proof.
  intros n bs Hl Hn. unfold bytes_val. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_bound bs) as B. rewrite Hl in B.
  assert (P : 2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite (ext_Z_small_id false (Z.of_nat n) (bytes_le_to_Z bs)).
  1:{ apply bv_wrap_small. rewrite bv_modulus_64, two64_eq. lia. }
  1:{ lia. }
  1:{ rewrite two64_eq. lia. }
  rewrite Z.sub_0_r. exact B.
Qed.

Lemma lit_load_bytes : forall E n bs (x : int),
  length bs = n -> (n <= 8)%nat ->
  den E (VL (wlit x)) = bytes_val false (Z.of_nat n) bs ->
  bs = Z_to_le_bytes n (to_Z x).
Proof.
  intros E n bs x Hl Hn H.
  destruct n as [|n']. { destruct bs; [reflexivity| discriminate]. }
  assert (E1 : to_Z x = bytes_le_to_Z bs).
  { apply (f_equal bv_unsigned) in H. rewrite unsigned_VL, wlit_ok in H. rewrite (bytes_val_false_eq (S n') bs Hl ltac:(lia)) in H. exact H. }
  rewrite E1, <- Hl. symmetry. apply Z_to_le_bytes_to_Z.
Qed.

Lemma load8_bytes : forall E bs v, length bs = 8%nat -> den E v = bytes_val false 8 bs -> bs = le8 (den E v).
Proof.
  intros E bs v Hl H. unfold le8, word_to_le_bytes. rewrite H, (bytes_val_false_eq 8 bs Hl ltac:(lia)), <- Hl.
  symmetry. apply Z_to_le_bytes_to_Z.
Qed.
Lemma load4_bytes : forall E bs v, length bs = 4%nat -> den E v = bytes_val false 4 bs -> bs = le4 (den E v).
Proof.
  intros E bs v Hl H. unfold le4. rewrite H, (bytes_val_false_eq 4 bs Hl ltac:(lia)), <- Hl.
  symmetry. apply Z_to_le_bytes_to_Z.
Qed.

Variable Cw : client_world.
Variable OPS : St.optable.

Hypothesis OPS_plain : St.plain_table OPS.

Hypothesis OPS_holds1 : forall args m mo, St.op_holds OPS HEAP_ID args m mo = heap_holds rsegs IMGX AWI Cw args m mo.
Hypothesis OPS_fp1 : forall args, St.op_fp OPS HEAP_ID args = heap_fp IMGX args.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Variable CANARY : sv.
Hypothesis PB_canary : forall E, PB (eb E) -> den E CANARY = Z_to_bv 64 ssp_canary.
Hypothesis PB_secret : forall E, PB (eb E) -> forall i, (i < 8)%nat ->
  nth_error (eb E 6%uint63) (8 + i) = nth_error (le8 (wz ctx_secret)) i.

Lemma st_ok_set_A : forall E st ms mo hargs a a' md nw rest,
  St.st_ok rsegs OPS E st ms mo ->
  find_op HEAP_ID (s_ops st) = Some hargs -> hargs = VL md :: a :: VL nw :: rest ->
  (forall s LBf mo', pclaim (bv_unsigned (den E a)) s LBf mo' -> pclaim (bv_unsigned (den E a')) s LBf mo') ->
  St.st_ok rsegs OPS E (set_ops st (set_op HEAP_ID (VL md :: a' :: VL nw :: rest) (s_ops st))) ms mo.
Proof.
  intros E st ms mo hargs a a' md nw rest HS Hf -> HR.
  pose proof (ops_hold_find OPS E (s_ops st) (ms_mem ms) mo HEAP_ID _ (St.so_ops _ _ _ _ _ _ HS) Hf) as HH.
  rewrite OPS_holds1 in HH. destruct HH as (md' & aw & ws & ca & LB & D & HA & WF & HC).
  destruct (decode_set_A E (VL md) a a' (VL nw) rest md' aw ws ca D) as [D' ->].
  destruct HS as [Hpc Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hops Hapart Hmf Hcov Hminv].
  split; cbn [set_ops s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - eapply ops_hold_set_op1; [exact Hf| exact Hops|]. rewrite OPS_holds1.
    exists md', (den E a'), ws, ca, LB. split; [exact D'|]. split; [| split; [exact WF| exact HC]].
    destruct HA as ((s & LBf & P & RC & K & MT & RM & RP) & NGW). apply aw_holdsW_intro; [| exact NGW]. exists s, LBf. repeat (split; [assumption|]). split; [| exact RP].
    apply HR. exact RM.
  - eapply ops_apart_set_op1; [exact Hf| exact Hapart|]. rewrite !OPS_fp1. unfold heap_fp. rewrite D, D'. reflexivity.
  -
    intros x _. apply St.plain_cover. exact OPS_plain.
Qed.

Theorem roomdrop_sound : forall pc, contract_sound rsegs OPS MP PB (CtrM.roomdrop_c pc).
Proof.
  intros pc st sts Hpc Happ K E ms mo HS HMP HPB HK. cbn [c_apply CtrM.roomdrop_c] in Happ. unfold CtrM.roomdrop_apply in Happ.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|] eqn:Hf; [|discriminate].
  destruct (heap_A hargs) as [[j| | | | | | | | | |]|] eqn:HA; try discriminate.
  destruct (heap_set_A hargs (VL wones)) as [hargs'|] eqn:HS'; [|discriminate]. injection Happ as <-.
  destruct (heap_set_A_shape hargs (VL wones) hargs' HS') as (md & A & nw & rest & -> & ->).
  apply (HK _ (or_introl eq_refl) E ms mo (env_ext_refl _ E) HMP).
  eapply st_ok_set_A; [exact HS| exact Hf| reflexivity|].
  intros s LBf mo' _. apply pclaim_none. rewrite unsigned_VL. change (w2Z wones) with (2^64 - 1). lia.
Qed.

Lemma pw_ok_inv : forall a, pw_ok a = true -> wt a = false /\ 0 <= w2Z a < 768 /\ w2Z a = to_Z (wl a).
Proof.
  intros a H. unfold pw_ok in H. apply andb_prop in H as [T L]. destruct (wt a) eqn:T'; [discriminate|].
  apply Uint63.ltb_spec in L. change (to_Z 768%uint63) with 768 in L. pose proof (w2Z_nowt a T') as E. pose proof (int_range (wl a)). lia.
Qed.
Lemma pw_j_eq : forall a, to_Z (pw_j a) = to_Z (wl a) mod 256.
Proof.
  intros a. unfold pw_j. pose proof (land_mk (wl a) 8%uint63 ltac:(change (to_Z 8%uint63) with 8; lia)) as LM.
  change (PrimInt63.sub (PrimInt63.lsl 1 8) 1)%uint63 with 255%uint63 in LM. change (2 ^ to_Z 8%uint63) with 256 in LM. exact LM.
Qed.
Lemma pw_nb_eq : forall a, to_Z (pw_nb a) = to_Z (wl a) / 256.
Proof. intros a. unfold pw_nb. rewrite Uint63.lsr_spec. change (2 ^ to_Z 8%uint63) with 256. reflexivity. Qed.

Theorem roomcap_sound : forall pc, contract_sound rsegs OPS MP PB (CtrA.roomcap_c pc).
Proof.
  intros pc st sts Hpc Happ K E ms mo HS HMP HPB HK. cbn [c_apply CtrA.roomcap_c] in Happ. unfold CtrA.roomcap_apply in Happ.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|] eqn:Hf; [|discriminate].
  destruct (heap_A hargs) as [[a| | | | | | | | | |]|] eqn:HA; try discriminate.
  destruct (pw_ok a && PrimInt63.leb (pw_j a) J_CAP) eqn:C; [|discriminate]. apply andb_prop in C as [P L].
  match type of Happ with context [heap_set_A hargs (VL ?x)] => set (a' := x) in Happ end.
  destruct (heap_set_A hargs (VL a')) as [hargs'|] eqn:HS'; [|discriminate]. injection Happ as <-.
  destruct (heap_set_A_shape hargs (VL a') hargs' HS') as (md & A & nw & rest & -> & ->).
  cbn [heap_A] in HA. injection HA as ->.
  apply (HK _ (or_introl eq_refl) E ms mo (env_ext_refl _ E) HMP).
  eapply st_ok_set_A; [exact HS| exact Hf| reflexivity|].
  destruct (pw_ok_inv a P) as (T & R & Ea). apply Uint63.leb_spec in L. change (to_Z J_CAP) with 21 in L. rewrite pw_j_eq in L.
  assert (Ea' : w2Z a' = to_Z (wl a) - to_Z (wl a) mod 256 + 21).
  { subst a'. unfold w2Z. cbn [wt wl]. rewrite Uint63.add_spec, Uint63.sub_spec, pw_j_eq. change (to_Z J_CAP) with 21.
    pose proof (Z.mod_pos_bound (to_Z (wl a)) 256 ltac:(lia)). pose proof (int_range (wl a)).
    rewrite (Z.mod_small (to_Z (wl a) - to_Z (wl a) mod 256)) by (rewrite wB_two63; lia). rewrite Z.mod_small by (rewrite wB_two63; unfold two63; lia). lia. }
  intros s LBf mo' H. rewrite !unsigned_VL in *. rewrite Ea', Ea in *.
  pose proof (Z.mod_pos_bound (to_Z (wl a)) 256 ltac:(lia)) as MB. pose proof (Z.div_mod (to_Z (wl a)) 256 ltac:(lia)) as DM.
  apply (pclaim_mono (to_Z (wl a))); [exact H| lia| lia| | | lia].
  - replace (to_Z (wl a) - to_Z (wl a) mod 256 + 21) with (21 + (to_Z (wl a) / 256) * 256) by lia.
    rewrite Z.mod_add by lia. change (21 mod 256) with 21. lia.
  - replace (to_Z (wl a) - to_Z (wl a) mod 256 + 21) with (21 + (to_Z (wl a) / 256) * 256) by lia.
    rewrite Z.div_add by lia. change (21 / 256) with 0. lia.
Qed.

Lemma alloc_call_inv : forall need st r ksp hargs wnl,
  alloc_call rsegs ERRNO LIBC GOT GUARD TP CANARY need st = Some (r, ksp, hargs, wnl) ->
  s_resv st = RNone /\ call_pre st = Some r /\ PrimInt63.ltb r bit62i = true
  /\ (exists ra, getr st X1 = VL ra /\ PrimInt63.land (wl ra) 1%uint63 = 0%uint63)
  /\ getr st X4 = VL (wlit TP)
  /\ statics_ok rsegs ERRNO LIBC GOT GUARD CANARY st = true /\ auxv_ok rsegs st = true /\ above_stack_ok st = true
  /\ exists klo1, stack_ok st need = Some (ksp, klo1) /\ heap_windows st klo1 = Some (hargs, wnl).
Proof.
  intros need st r ksp hargs wnl H. unfold alloc_call in H.
  destruct (s_resv st); try discriminate. destruct (call_pre st) as [r0|]; [|discriminate].
  destruct (getr st X1) as [ra| | | | | | | | | |]; try discriminate.
  destruct (getr st X4) as [tp| | | | | | | | | |]; try discriminate.
  destruct (stack_ok st need) as [[ksp0 klo1]|]; [|discriminate].
  destruct (weqb tp (wlit TP)) eqn:Htp; [|discriminate].
  destruct (PrimInt63.eqb (PrimInt63.land (wl ra) 1) 0) eqn:Hra; [|discriminate].
  destruct (statics_ok _ _ _ _ _ _ st) eqn:Hst; [|discriminate]. destruct (auxv_ok rsegs st) eqn:Hav; [|discriminate].
  destruct (above_stack_ok st) eqn:Hab; [|discriminate]. destruct (PrimInt63.ltb r0 bit62i) eqn:Hr; [|discriminate].
  cbn [andb] in H. destruct (heap_windows st klo1) as [[h w]|] eqn:Hw; [|discriminate]. injection H as <- <- <- <-.
  apply weqb_eq in Htp. subst tp. apply Uint63.eqb_correct in Hra.
  repeat split; try assumption; try reflexivity. { exists ra. auto. } exists klo1. auto.
Qed.

Lemma call_pre_inv : forall st r, call_pre st = Some r ->
  fresh_ok st = true /\ exists ra, getr st X1 = VL ra /\ wt ra = false /\ PrimInt63.ltb (wl ra) bit62i = true /\ r = wl ra.
Proof.
  intros st r H. unfold call_pre in H. destruct (s_resv st); try discriminate H. destruct (fresh_ok st); [|discriminate]. split; [reflexivity|].
  unfold ret_pc, small_lit in H. destruct (getr st X1) as [ra| | | | | | | | | |]; try discriminate.
  exists ra. destruct (wt ra); [discriminate|]. cbn [negb andb] in H. destruct (PrimInt63.ltb (wl ra) bit62i); [|discriminate].
  destruct (PrimInt63.eqb (PrimInt63.land (wl ra) 1) 0); [|discriminate]. injection H as <-. auto.
Qed.

Lemma call_pre_resv : forall st r, call_pre st = Some r -> s_resv st = RNone.
Proof. intros st r H. unfold call_pre in H. destruct (s_resv st); [reflexivity| discriminate H| discriminate H]. Qed.

Lemma call_pre_even : forall st r, call_pre st = Some r -> PrimInt63.land r 1%uint63 = 0%uint63.
Proof.
  intros st r H. unfold call_pre in H. destruct (s_resv st); try discriminate H. destruct (fresh_ok st); [|discriminate].
  destruct (ret_pc st) as [r0|]; [|discriminate]. destruct (PrimInt63.eqb (PrimInt63.land r0 1) 0) eqn:Q; [|discriminate].
  injection H as <-. apply Uint63.eqb_correct in Q. exact Q.
Qed.

Lemma fresh_ok_inv : forall st, fresh_ok st = true ->
  st_vars_below (s_next st) st = true /\ 0 < to_Z (s_next st) /\ to_Z (s_next st) + 256 <= 2 ^ 62.
Proof.
  intros st H. unfold fresh_ok in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  split; [exact H1|]. apply Uint63.ltb_spec in H2. apply Uint63.ltb_spec in H3. change (to_Z 0%uint63) with 0 in H2.
  change (to_Z 4611686018427387648%uint63) with (2 ^ 62 - 256) in H3. lia.
Qed.

Lemma den_wlit : forall E (a : int), den E (VL (wlit a)) = wa (to_Z a).
Proof. intros E a. rewrite den_VL. unfold wbv, wa. rewrite wlit_ok. reflexivity. Qed.

Lemma den_VPz : forall E k, den E (VP k wzero) = ev E k.
Proof. intros E k. apply bv_eq. apply (den_VP0 E k wzero eq_refl). Qed.

Lemma to_Z_lt64 : forall a : int, 0 <= to_Z a /\ to_Z a + 8 < 2 ^ 64.
Proof. intros a. pose proof (int_range a) as B. unfold two63 in B. lia. Qed.

Lemma aload_inv : forall E st ms mo a w v,
  St.st_ok rsegs OPS E st ms mo -> wok w -> aload rsegs st a w = Some v ->
  exists bs, length bs = Z.to_nat (to_Z w) /\ bytes_at rsegs (ms_mem ms) (to_Z a) bs
    /\ den E v = bytes_val false (to_Z w) bs.
Proof.
  intros E st ms mo a w v HS Hw H. unfold aload in H.
  destruct (do_load rsegs st (VL (wlit a)) w false) as [[v'|]|] eqn:D; try discriminate. injection H as ->.
  destruct (do_load_sound rsegs OPS E st ms mo (VL (wlit a)) w false v HS Hw D) as (bs & L & R & Dv).
  pose proof (to_Z_lt64 a) as B. assert (Hw8 : 1 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  exists bs. split; [exact L|]. split.
  - apply (bytes_at_of_ov_read (ms_mem ms) (to_Z a) (Z.to_nat (to_Z w)) bs); [lia| lia|].
    rewrite <- den_wlit with (E := E). exact R.
  - rewrite Dv. symmetry. apply bytes_val_ext_word; [exact L| exact Hw8].
Qed.

Lemma is_litv_inv : forall ov x, is_litv ov x = true -> ov = Some (VL (wlit x)).
Proof.
  intros [[w| | | | | | | | | |]|] x H; cbn in H; try discriminate. apply weqb_eq in H. subst. reflexivity.
Qed.
Lemma is_sv_inv : forall ov x, is_sv ov x = true -> ov = Some x.
Proof. intros [u|] x H; cbn in H; [|discriminate]. apply sv_eqb_eq in H. subst. reflexivity. Qed.

Lemma rw_cell_of_bytes : forall M A (c : Cells.cell), Cells.cell_wf c -> bytes_at rsegs M A (cbytes c) ->
  Mem.abs_writable rsegs A (Z.of_nat (csize c)) = true -> rw_cells rsegs M A [c].
Proof.
  intros M A c Hwf HB HW. pose proof HB as (H0 & H1 & _). rewrite (cbytes_length c Hwf) in H1.
  split.
  - split; [cbn; auto|]. cbn [cells_bytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size]. rewrite Nat.add_0_r. split; [exact H0|]. split; [exact H1|].
    intros i Hi. apply (proj1 (wb_wview M (A + i))).
    destruct (abs_writable_sound rsegs A (Z.of_nat (csize c)) ltac:(lia) ltac:(lia) HW) as [_ W]. apply (proj1 (W i Hi)).
Qed.

Lemma wok1 : wok 1%uint63. Proof. left. reflexivity. Qed.
Lemma wok4 : wok 4%uint63. Proof. right; right; left. reflexivity. Qed.
Lemma wok8 : wok 8%uint63. Proof. right; right; right. reflexivity. Qed.

Lemma statics_sound : forall E st ms mo,
  St.st_ok rsegs OPS E st ms mo -> PB (eb E) ->
  statics_ok rsegs ERRNO LIBC GOT GUARD CANARY st = true ->
  PUBS (ms_mem ms) /\ rw_cells rsegs (ms_mem ms) RAUXV_CELL [C8 (ev E AUXV_ID)]
  /\ exists errv, rw_cells rsegs (ms_mem ms) RERRNO [C4 errv].
Proof.
  intros E st ms mo HS HPB H. unfold statics_ok in H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply is_litv_inv in H1. apply is_litv_inv in H2. apply is_sv_inv in H3. apply is_litv_inv in H4. apply is_sv_inv in H5.
  destruct (aload rsegs st ERRNO 4%uint63) as [ve|] eqn:H6'; [|discriminate]. clear H6.
  destruct (aload_inv E st ms mo _ _ _ HS wok1 H1) as (bs1 & L1 & B1 & D1).
  destruct (aload_inv E st ms mo _ _ _ HS wok8 H2) as (bs2 & L2 & B2 & D2).
  destruct (aload_inv E st ms mo _ _ _ HS wok8 H3) as (bs3 & L3 & B3 & D3).
  destruct (aload_inv E st ms mo _ _ _ HS wok8 H4) as (bs4 & L4 & B4 & D4).
  destruct (aload_inv E st ms mo _ _ _ HS wok8 H5) as (bs5 & L5 & B5 & D5).
  destruct (aload_inv E st ms mo _ _ _ HS wok4 H6') as (bs6 & L6 & B6 & D6).
  cbn in L1, L2, L3, L4, L5, L6.
  pose proof (lit_load_bytes E 1 bs1 0%uint63 L1 ltac:(lia) D1) as E1.
  pose proof (lit_load_bytes E 8 bs2 4096%uint63 L2 ltac:(lia) D2) as E2.
  pose proof (load8_bytes E bs3 _ L3 D3) as E3.
  pose proof (lit_load_bytes E 8 bs4 GUARD L4 ltac:(lia) D4) as E4.
  pose proof (load8_bytes E bs5 _ L5 D5) as E5.
  pose proof (load4_bytes E bs6 _ L6 D6) as E6.
  subst bs1 bs2 bs3 bs4 bs5 bs6.
  split; [| split].
  - split; [| split; [| split]].
    + apply rw_cell_of_bytes; [exact I| | exact wr_NEED_LOCKS]. rewrite <- NEED_LOCKS_eq. exact B1.
    + apply rw_cell_of_bytes; [exact I| | exact wr_PAGE_SIZE]. rewrite <- PAGE_SIZE_eq. exact B2.
    + apply rw_cell_of_bytes; [exact I| | exact wr_GOT]. rewrite <- GOT_eq. exact B4.
    + apply rw_cell_of_bytes; [exact I| | exact wr_GUARD]. rewrite <- GUARD_eq.
      cbn [cbytes]. unfold wz. rewrite <- (PB_canary E HPB). exact B5.
  - apply rw_cell_of_bytes; [exact I| | exact wr_AUXV_CELL]. rewrite <- AUXV_CELL_eq. cbn [cbytes]. rewrite <- (den_VPz E AUXV_ID). exact B3.
  - exists (den E ve). apply rw_cell_of_bytes; [exact I| | exact wr_ERRNO]. rewrite <- ERRNO_eq. exact B6.
Qed.

Lemma okey_wlit : forall off key, Mem.okey (wlit off) = Some key -> keyZ key = to_Z off.
Proof.
  intros off key H. destruct (okey_sound (wlit off) key H) as [E _]. rewrite E, w2Zs_eq, wlit_ok. cbn [wt wlit]. lia.
Qed.

Lemma rload_inv : forall E st ms mo k off w v,
  St.st_ok rsegs OPS E st ms mo -> wok w -> PrimInt63.eqb k 0%uint63 = false -> rload rsegs st k off w = Some v ->
  exists r bs, IMap.find k (s_regs st) = Some r /\ length bs = Z.to_nat (to_Z w)
    /\ loZ r <= to_Z off /\ to_Z off + to_Z w <= hiZ E r /\ bv_unsigned (ev E k) + hiZ E r < 2 ^ 64
    /\ bytes_at rsegs (ms_mem ms) (bv_unsigned (ev E k) + to_Z off) bs /\ den E v = bytes_val false (to_Z w) bs.
Proof.
  intros E st ms mo k off w v HS Hw K H. unfold rload, do_load in H. cbn [addr_of] in H.
  pose proof (so_zero _ _ _ _ _ _ HS) as Hz. pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  assert (Hw8 : 1 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate].
  destruct (Mem.okey (wlit off)) as [key|] eqn:Hk; [|discriminate].
  destruct (can_read rsegs (s_facts st) (s_priv st) k r key w) eqn:CR; [|discriminate].
  destruct (Mem.region_load rsegs k r key w false) as [v'|] eqn:RL; [|discriminate]. injection H as <-.
  pose proof (so_reg _ _ _ _ _ _ HS k r Hr) as RO.
  destruct (region_load_sound rsegs (s_priv st) E (ms_mem ms) (s_facts st) k r key w false v' Hfs Hz RO Hw CR RL) as (bs & Len & OV & Dv).
  pose proof (can_read_sound rsegs (s_priv st) E (ms_mem ms) (s_facts st) k r key w Hfs Hz RO Hw CR) as (RA & RAw & _ & IN & _).
  cbv zeta in IN. specialize (IN K). pose proof (okey_wlit off key Hk) as EK. unfold addrZ in RA, RAw, OV. rewrite EK in RA, RAw, OV, IN.
  pose proof (ro_range _ _ _ _ _ _ RO K) as [_ RH].
  exists r, bs. split; [reflexivity|]. split; [exact Len|]. split; [specialize (IN 0 ltac:(lia)); lia|].
  split; [specialize (IN (to_Z w - 1) ltac:(lia)); lia|]. split; [unfold two64 in RH; lia|]. split.
  - apply (bytes_at_of_ov_read (ms_mem ms) _ (Z.to_nat (to_Z w)) bs); [lia| unfold two64 in RAw; lia| exact OV].
  - rewrite (den_narrow_f E (s_facts st) Hfs). exact Dv.
Qed.

Lemma blob_region_bytes : forall priv E m k r j (o : Z) (n : nat),
  St.region_ok rsegs priv E m k r -> PrimInt63.eqb k 0%uint63 = false -> Mem.rg_cells r = IMap.Leaf -> Mem.rg_bg r = Mem.BGBlob j 0%uint63 ->
  0 <= o -> loZ r <= o -> o + Z.of_nat n <= hiZ E r ->
  bytes_at rsegs m (bv_unsigned (ev E k) + o) (map (fun i => nth (Z.to_nat o + i)%nat (eb E j) (Z_to_bv 8 0)) (seq 0 n)).
Proof.
  intros priv E m k r j o n RO K HC HB Ho Hlo Hhi.
  pose proof (ro_range _ _ _ _ _ _ RO K) as [RL RH]. unfold two64 in RH.
  split; [lia|]. rewrite length_map, length_seq. split; [lia|].
  intros i Hi. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec i n); [|lia]. cbn [option_map Nat.add].
  rewrite <- rb_mrd. replace (bv_unsigned (ev E k) + o + Z.of_nat i) with (bv_unsigned (ev E k) + (o + Z.of_nat i)) by lia.
  pose proof (ro_bg _ _ _ _ _ _ RO (o + Z.of_nat i) ltac:(intros _; lia) ltac:(intros X; rewrite K in X; discriminate X)) as G.
  unfold bg_byte in G. rewrite HB in G. change (to_Z 0%uint63) with 0 in G. rewrite Z.sub_0_r in G.
  replace (Z.to_nat (o + Z.of_nat i)) with (Z.to_nat o + i)%nat in G by lia. apply G.
  intros g gr _ Hf. rewrite HC in Hf. cbn in Hf. discriminate Hf.
Qed.

Lemma le8_wz : forall x, 0 <= x < 2 ^ 64 -> Z_to_le_bytes 8 x = le8 (wz x).
Proof. intros x Hx. unfold le8, word_to_le_bytes, wz. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64; lia). reflexivity. Qed.
Lemma wz_unsigned : forall w : word, wz (bv_unsigned w) = w.
Proof. intros w. unfold wz. apply Z_to_bv_bv_unsigned. Qed.

Lemma list_eq_nth_error : forall {T} (l1 l2 : list T), length l1 = length l2 ->
  (forall i, (i < length l1)%nat -> nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  intros T l1. induction l1 as [|x l1 IH]; intros [|y l2] L H; cbn in L; try discriminate; [reflexivity|].
  pose proof (H O ltac:(cbn; lia)) as H0. cbn in H0. injection H0 as ->. f_equal. apply IH; [lia|].
  intros i Hi. exact (H (S i) ltac:(cbn; lia)).
Qed.

Lemma secret_bytes : forall E, PB (eb E) ->
  map (fun i => nth (8 + i)%nat (eb E 6%uint63) (Z_to_bv 8 0)) (seq 0 8) = le8 (wz ctx_secret).
Proof.
  intros E HPB. apply list_eq_nth_error.
  - rewrite length_map, length_seq, length_le8. reflexivity.
  - intros i Hi. rewrite length_map, length_seq in Hi. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec i 8); [|lia]. cbn [option_map Nat.add].
    pose proof (PB_secret E HPB i Hi) as P.
    destruct (nth_error (le8 (wz ctx_secret)) i) as [b|] eqn:Hb.
    + f_equal. apply nth_error_nth. exact P.
    + exfalso. apply nth_error_None in Hb. rewrite length_le8 in Hb. lia.
Qed.

Lemma bytes_at_cons8 : forall m a c (w : word) rest,
  bytes_at rsegs m (a + c) (le8 w) -> bytes_at rsegs m (a + (c + 8)) rest -> bytes_at rsegs m (a + c) (le8 w ++ rest).
Proof.
  intros m a c w rest H1 H2. apply (proj2 (bytes_at_app rsegs m (a + c) (le8 w) rest)). split; [exact H1|].
  rewrite length_le8. replace (a + c + Z.of_nat 8) with (a + (c + 8)) by lia. exact H2.
Qed.

Ltac lit_ints := repeat match goal with |- context [to_Z ?x] => let v := eval vm_compute in (to_Z x) in change (to_Z x) with v end.
Ltac lit_ints_in H := repeat match type of H with context [to_Z ?x] => let v := eval vm_compute in (to_Z x) in change (to_Z x) with v in H end.

Lemma auxv_sound : forall E st ms mo B,
  St.st_ok rsegs OPS E st ms mo -> PB (eb E) -> auxv_ok rsegs st = true ->
  rw_cells rsegs (ms_mem ms) RAUXV_CELL [C8 (ev E AUXV_ID)] ->
  alloc_ceiling <= B -> B <= bv_unsigned (ev E AUXV_ID) -> B <= bv_unsigned (ev E RND_ID) ->
  rauxv_ok (ms_mem ms) B.
Proof.
  intros E st ms mo B HS HPB H HC HB1 HB2 HB3. unfold auxv_ok in H.
  apply andb_prop in H as [H HR]. apply andb_prop in H as [H H152]. apply andb_prop in H as [H H136].
  cbn [auxv_keys_ok AUXV_KEYS PrimInt63.add] in H. rewrite !andb_true_r in H.
  repeat match goal with X : _ && _ = true |- _ => apply andb_prop in X as [? ?] end.

  repeat match goal with
  | X : is_litv (rload _ _ _ ?o _) _ = true |- _ => apply is_litv_inv in X
  | X : match rload ?sg ?st ?k ?o ?w with Some _ => true | None => false end = true |- _ =>
      destruct (rload sg st k o w) eqn:?L in X; [clear X| discriminate X]
  end.
  apply is_sv_inv in H136.
  repeat match goal with
  | X : rload rsegs st AUXV_ID ?o 8%uint63 = Some _ |- _ =>
      apply (rload_inv E st ms mo AUXV_ID o 8%uint63 _ HS wok8 eq_refl) in X;
      destruct X as (?rg & ?bys & ?Hreg & ?Ln & ?LO & ?HI & ?RH & ?BA & ?DV); cbn in Ln
  end.

  unfold rnd_region_ok in HR. destruct (IMap.find RND_ID (s_regs st)) as [qr|] eqn:Hqr; [|discriminate].
  destruct (Mem.rg_cells qr) eqn:HCq; try discriminate. destruct (Mem.rg_bg qr) as [| | | |j sh] eqn:HBq; try discriminate.
  apply andb_prop in HR as [HR HLq]. apply andb_prop in HR as [HR HLOq]. apply andb_prop in HR as [HJ HSH].
  apply Uint63.eqb_correct in HJ. apply Uint63.eqb_correct in HSH. apply Uint63.eqb_correct in HLOq. subst j sh.
  destruct (rload rsegs st RND_ID 8%uint63 8%uint63) as [vq|] eqn:Lq; [|discriminate].
  destruct (rload_inv E st ms mo RND_ID 8%uint63 8%uint63 vq HS wok8 eq_refl Lq) as (qr' & bsq & Hqr' & _ & _ & HIq & RHq & _ & _).
  rewrite Hqr in Hqr'. injection Hqr' as <-. lit_ints_in HIq.
  pose proof (blob_region_bytes (s_priv st) E (ms_mem ms) RND_ID qr RND_ID 8 8 (so_reg _ _ _ _ _ _ HS _ _ Hqr) eq_refl HCq HBq
                ltac:(lia) ltac:(unfold loZ; rewrite HLOq; change (keyZ 0%uint63) with 0; lia) ltac:(cbn; lia)) as SEC.
  rewrite (secret_bytes E HPB) in SEC.

  repeat match goal with
  | Ln : length ?bs = Z.to_nat (to_Z 8%uint63), DV : den E ?v = bytes_val false (to_Z 8%uint63) ?bs, BA : bytes_at _ _ _ ?bs |- _ =>
      change (Z.to_nat (to_Z 8%uint63)) with 8%nat in Ln; change (to_Z 8%uint63) with 8 in DV;
      first [ rewrite (lit_load_bytes E 8 bs _ Ln ltac:(lia) DV) in BA; rewrite le8_wz in BA by (lit_ints; lia)
            | rewrite (load8_bytes E bs v Ln DV) in BA; try rewrite (den_VPz E) in BA; rewrite <- (wz_unsigned (den E v)) in BA || rewrite <- (wz_unsigned (ev E RND_ID)) in BA ];
      clear Ln DV; lit_ints_in BA
  end.
  rewrite <- (wz_unsigned (ev E AUXV_ID)) in HC.
  set (av := bv_unsigned (ev E AUXV_ID)) in *. set (rnd := bv_unsigned (ev E RND_ID)) in *.
  match goal with H : to_Z 152%uint63 + to_Z 8%uint63 <= hiZ E ?r, H' : av + hiZ E ?r < 2 ^ 64 |- _ =>
    lit_ints_in H; assert (AVH : av + 160 <= 2 ^ 64) by lia end.
  unfold rauxv_ok. eexists av, _, _, _, _, _, _, _, _, rnd.
  split; [exact HC|]. split; [| split; [exact SEC|]].
  - unfold auxv_list. cbn [map u64s app]. rewrite <- (Z.add_0_r av) at 1.
    repeat (apply bytes_at_cons8; [eassumption|];
            match goal with |- bytes_at _ _ (_ + ?c) _ => let v := eval vm_compute in c in change c with v end).
    apply bytes_at_nil. pose proof (bv_unsigned_in_range 64 (ev E AUXV_ID)). lia.
  - pose proof (bv_unsigned_in_range 64 (ev E RND_ID)) as RR. unfold bv_modulus in RR.
    repeat match goal with |- context [bv_unsigned (den E ?v)] =>
      lazymatch goal with _ : 0 <= bv_unsigned (den E v) < _ |- _ => fail | _ => pose proof (bv_unsigned_in_range 64 (den E v)) end end.
    unfold bv_modulus in *. cbn -[Z.pow av rnd alloc_ceiling Z.le Z.lt Z.add] in *. lia.
Qed.

Lemma auxv_region : forall E st ms mo, St.st_ok rsegs OPS E st ms mo -> auxv_ok rsegs st = true ->
  exists r3, IMap.find AUXV_ID (s_regs st) = Some r3.
Proof.
  intros E st ms mo HS H. unfold auxv_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H].
  apply is_sv_inv in H. destruct (rload_inv E st ms mo AUXV_ID 136%uint63 8%uint63 _ HS wok8 eq_refl H) as (r3 & bs & Hr3 & _).
  exists r3. exact Hr3.
Qed.

Lemma w2Zs_wsub_small : forall a b, - two63 <= w2Zs a - w2Zs b < two63 -> w2Zs (wsub a b) = w2Zs a - w2Zs b.
Proof.
  intros a b H. rewrite (w2Zs_eq (wsub a b)), w2Z_wt, wsub_ok.
  rewrite (w2Zs_eq a), (w2Zs_eq b), (w2Z_wt a), (w2Z_wt b) in H |- *.
  pose proof (w2Z_range a) as Ra. pose proof (w2Z_range b) as Rb. unfold two63, two64 in *.
  destruct (Z.leb_spec 9223372036854775808 (w2Z a)), (Z.leb_spec 9223372036854775808 (w2Z b));
  destruct (Z_lt_le_dec (w2Z a - w2Z b) 0);
  try (replace (w2Z a - w2Z b) with ((w2Z a - w2Z b + 18446744073709551616) + (-1) * 18446744073709551616) by lia;
       rewrite Z.mod_add, Z.mod_small by lia;
       destruct (Z.leb_spec 9223372036854775808 (w2Z a - w2Z b + 18446744073709551616)); lia);
  try (rewrite (Z.mod_small (w2Z a - w2Z b)) by lia; destruct (Z.leb_spec 9223372036854775808 (w2Z a - w2Z b)); lia).
Qed.

Lemma stack_sound : forall E st ms mo need ksp klo1,
  St.st_ok rsegs OPS E st ms mo -> to_Z need < 2 ^ 32 -> stack_ok st need = Some (ksp, klo1) ->
  exists off r1, getr st X2 = VP STACK_ID off /\ IMap.find STACK_ID (s_regs st) = Some r1
    /\ Mem.rg_w r1 = true /\ Mem.rg_bg r1 = Mem.BGNone /\ Mem.okey off = Some ksp /\ klo1 = Mem.rg_lo r1 /\ keyZ ksp mod 16 = 0
    /\ keyZ ksp < 0
    /\ bv_unsigned (den E (getr st X2)) = bv_unsigned (ev E STACK_ID) + keyZ ksp
    /\ 0 <= bv_unsigned (ev E STACK_ID) + loZ r1
    /\ bv_unsigned (ev E STACK_ID) + loZ r1 <= bv_unsigned (ev E STACK_ID) + keyZ ksp - to_Z need
    /\ bv_unsigned (ev E STACK_ID) + keyZ ksp <= bv_unsigned (ev E STACK_ID) + hiZ E r1 < 2 ^ 64
    /\ stk rsegs (ms_mem ms) (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + hiZ E r1).
Proof.
  intros E st ms mo need ksp klo1 HS Hneed H. unfold stack_ok in H.
  destruct (getr st X2) as [|k off| | | | | | | | |] eqn:HX2; try discriminate.
  destruct (IMap.find STACK_ID (s_regs st)) as [r1|] eqn:Hr1; [|discriminate].
  destruct (PrimInt63.eqb k STACK_ID) eqn:HK; [|discriminate]. apply Uint63.eqb_correct in HK. subst k.
  destruct (Mem.rg_w r1) eqn:HW; [|discriminate]. destruct (Mem.rg_bg r1) eqn:HBG; try discriminate. cbn [negb orb] in H.
  destruct (Mem.okey off) as [ksp'|] eqn:Hksp; [|discriminate].
  destruct (Mem.okey (wsub off (wlit need))) as [klo|] eqn:Hklo; [|discriminate].
  destruct (Mem.rg_hi r1) as [h| | | | | | | | | |] eqn:Hhi; try discriminate.
  destruct (Mem.okey h) as [kh|] eqn:Hkh; [|discriminate].
  destruct (Mem.kleb (Mem.rg_lo r1) klo) eqn:L1; [|discriminate]. destruct (Mem.kleb ksp' kh) eqn:L2; [|discriminate].
  destruct (PrimInt63.eqb (PrimInt63.land ksp' 15) 0) eqn:AL; [|discriminate].
  destruct (PrimInt63.leb bit62i ksp') eqn:NEG; [|discriminate]. cbn [andb] in H. injection H as -> <-.
  rewrite kleb_keyZ in L1, L2. apply Z.leb_le in L1. apply Z.leb_le in L2.
  destruct (okey_sound _ _ Hksp) as [Eksp Rksp]. destruct (okey_sound _ _ Hklo) as [Eklo Rklo]. destruct (okey_sound _ _ Hkh) as [Ekh Rkh].
  rewrite !half63 in Rksp, Rklo, Rkh.
  assert (Eneed : w2Zs (wlit need) = to_Z need) by (rewrite w2Zs_eq, wlit_ok; cbn [wt wlit]; lia).
  pose proof (int_range need) as Rn. rewrite two63_eq in Rn.
  assert (Eklo' : keyZ klo = keyZ ksp - to_Z need).
  { rewrite Eklo, w2Zs_wsub_small; [rewrite Eneed, Eksp; reflexivity|].
    rewrite Eneed, <- Eksp. unfold two63 in *. lia. }
  pose proof (so_reg _ _ _ _ _ _ HS _ _ Hr1) as RO.
  pose proof (ro_range _ _ _ _ _ _ RO eq_refl) as [RLO RHI]. unfold two64 in RHI.
  assert (Ehi : keyZ kh <= hiZ E r1).
  { unfold hiZ. rewrite Hhi, unsigned_VL, Ekh, w2Zs_eq. unfold two64. destruct (wt h); lia. }
  exists off, r1. split; [reflexivity|]. split; [reflexivity|]. split; [exact HW|]. split; [exact HBG|]. split; [exact Hksp|]. split; [reflexivity|]. split.
  { apply Uint63.eqb_correct in AL. pose proof (land_mk ksp 4%uint63 ltac:(change (to_Z 4%uint63) with 4; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 4) 1)%uint63 with 15%uint63 in LM. rewrite AL in LM.
    change (to_Z 0%uint63) with 0 in LM. change (2 ^ to_Z 4%uint63) with 16 in LM.
    destruct (keyZ_cases ksp) as [[_ ->]|[_ ->]]; [lia|].
    replace (to_Z ksp - 2 ^ 63) with (to_Z ksp + (- 2 ^ 59) * 16) by lia. rewrite Z.mod_add by lia. lia. }
  split. { apply Uint63.leb_spec in NEG. rewrite to_Z_bit62i in NEG. destruct (keyZ_cases ksp) as [[R EK]|[R EK]]; [lia| rewrite EK; lia]. }
  assert (Esp : bv_unsigned (den E (VP STACK_ID off)) = bv_unsigned (ev E STACK_ID) + keyZ ksp).
  { rewrite den_VP, <- Eksp. unfold loZ in *. apply Z.mod_small. unfold two64. lia. }
  split; [exact Esp|]. unfold loZ in *. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (ro_valid _ _ _ _ _ _ RO eq_refl a Ha) as (V1 & V2 & _).
  split; [apply wb_wview; apply V2; exact HW|]. rewrite rb_mrd in V1. destruct (mrd rsegs (ms_mem ms) (wa a)); [eexists; reflexivity| congruence].
Qed.

Lemma weqb_wzero_unsigned' : forall c, weqb c wzero = true -> w2Z c = 0.
Proof. intros c H. apply weqb_eq in H. subst. reflexivity. Qed.

Lemma heap_windows_inv : forall st klo1 hargs wnl,
  heap_windows st klo1 = Some (hargs, wnl) ->
  find_op HEAP_ID (s_ops st) = Some hargs /\ count_op HEAP_ID (s_ops st) = 1%nat
  /\ exists n md A nw rest, heap_nwin hargs = Some n /\ hargs = VL md :: A :: VL nw :: rest
     /\ wt nw = false /\ n = Z.to_nat (to_Z (wl nw)) /\ (3 * n <= length rest)%nat /\ (n <= 255)%nat
     /\ stack_window_ok n rest klo1 = true /\ nonstack_windows n rest = Some wnl
     /\ windows_anchored (s_regs st) wnl = true /\ regions_justified st wnl = true.
Proof.
  intros st klo1 hargs wnl H. unfold heap_windows in H.
  destruct (find_op HEAP_ID (s_ops st)) as [h|] eqn:Hf; [|discriminate].
  destruct (count_op HEAP_ID (s_ops st)) as [|[|c]] eqn:Hc; try discriminate.
  destruct (heap_nwin h) as [n|] eqn:Hn; [|discriminate].
  destruct (heap_nwin_shape h n Hn) as (md & A & nw & rest & Eh & T & N & L). rewrite Eh in H.
  destruct (Nat.leb n 255) eqn:N255; [|discriminate]. apply Nat.leb_le in N255. cbn [andb] in H.
  destruct (stack_window_ok n rest klo1) eqn:SW; [|discriminate].
  destruct (nonstack_windows n rest) as [wl'|] eqn:NW; [|discriminate].
  destruct (windows_anchored (s_regs st) wl' && regions_justified st wl') eqn:AJ; [|discriminate]. injection H as <- <-.
  apply andb_prop in AJ as [A1 A2]. subst h. split; [reflexivity|]. split; [reflexivity|].
  exists n, md, A, nw, rest. repeat (split; [assumption || reflexivity|]). exact A2.
Qed.

Lemma stack_window_In : forall E n rest klo,
  stack_window_ok n rest klo = true ->
  exists wlo len, Mem.okey wlo = Some klo /\ In (Win (bv_unsigned (den E (VP STACK_ID wlo))) len K_STACK) (wins_of E n rest).
Proof.
  intros E n. induction n as [|n IH]; intros rest klo H; [cbn in H; destruct rest; discriminate|].
  destruct rest as [|lo rest1]; [cbn in H; discriminate|].
  destruct rest1 as [|len rest2]; [destruct lo; cbn in H; discriminate|].
  destruct rest2 as [|kd rest']; [destruct lo; cbn in H; discriminate|].
  cbn [stack_window_ok] in H.
  assert (STEP : stack_window_ok n rest' klo = true ->
            exists wlo len0, Mem.okey wlo = Some klo /\ In (Win (bv_unsigned (den E (VP STACK_ID wlo))) len0 K_STACK) (wins_of E (S n) (lo :: len :: kd :: rest'))).
  { intros H'. destruct (IH rest' klo H') as (wlo & len0 & K1 & K2). exists wlo, len0. split; [exact K1|]. rewrite wins_of_cons. right. exact K2. }
  destruct lo as [|k wlo| | | | | | | | |]; cbn in H; try (apply STEP; exact H).
  destruct kd as [kdw| | | | | | | | | |]; cbn in H; try (apply STEP; exact H).
  apply orb_prop in H as [H|H]; [| apply STEP; exact H].
  apply andb_prop in H as [H HK]. apply andb_prop in H as [H1 H2].
  apply Uint63.eqb_correct in H1. subst k. destruct (Mem.okey wlo) as [kw|] eqn:Hkw; [|discriminate].
  apply Uint63.eqb_correct in HK. subst kw.
  exists wlo, (bv_unsigned (den E len)). split; [exact Hkw|]. rewrite wins_of_cons. left.
  unfold K_STACK. rewrite (unsigned_VL E kdw), (weqb_wzero_unsigned' kdw H2). reflexivity.
Qed.

Lemma known_ltu_sound : forall E fs a b, facts_hold E fs -> known_ltu fs a b = true -> bv_unsigned (den E a) < bv_unsigned (den E b).
Proof.
  intros E fs a b Hfs H. unfold known_ltu, dec_true in H. destruct (decide_ltu fs a b) as [[|]|] eqn:D; try discriminate H.
  exact (proj1 (ltu_iff _ _ true) (ValP.decide_ltu_sound E fs Hfs a b true D)).
Qed.
Lemma known_leu_sound : forall E fs a b, facts_hold E fs -> known_leu fs a b = true -> bv_unsigned (den E a) <= bv_unsigned (den E b).
Proof.
  intros E fs a b Hfs H. unfold known_leu, dec_false in H. destruct (decide_ltu fs b a) as [[|]|] eqn:D; try discriminate H.
  exact (proj1 (ltu_iff _ _ false) (ValP.decide_ltu_sound E fs Hfs b a false D)).
Qed.

Lemma known_leu_q_sound : forall E fs a b, facts_hold E fs -> known_leu_q fs a b = true -> bv_unsigned (den E a) <= bv_unsigned (den E b).
Proof.
  intros E fs a b Hfs H. unfold known_leu_q in H.
  destruct (sv_eqb a b) eqn:Q; [apply ValP.sv_eqb_eq in Q; subst; lia|].
  destruct (fact_lookup fs (is_FULe a b)) eqn:L1.
  { destruct (ValP.fact_lookup_holds E fs _ Hfs L1) as (f & HF & PF). destruct f; try discriminate PF. cbn [is_FULe] in PF.
    apply andb_prop in PF as [P1 P2]. apply ValP.sv_eqb_eq in P1, P2. subst. cbn [fact_holds] in HF. exact HF. }
  destruct (fact_lookup fs (is_FULt a b)) eqn:L2.
  { destruct (ValP.fact_lookup_holds E fs _ Hfs L2) as (f & HF & PF). destruct f; try discriminate PF. cbn [is_FULt] in PF.
    apply andb_prop in PF as [P1 P2]. apply ValP.sv_eqb_eq in P1, P2. subst. cbn [fact_holds] in HF. lia. }
  exact (known_leu_sound E fs a b Hfs H).
Qed.
Lemma anchored_above_sound : forall E fs k, facts_hold E fs ->
  anchored_above fs k = true -> bv_unsigned (ev E STACK_ID) <= bv_unsigned (ev E k).
Proof.
  intros E fs k Hfs H. unfold anchored_above in H. apply existsb_exists in H as (f & Hin & Hf).
  pose proof (proj1 (Forall_forall _ _) Hfs f Hin) as HF.
  destruct f as [| | | |a b| | |]; try discriminate Hf. destruct a as [|k' z| | | | | | | | |]; try discriminate Hf. destruct b as [|s o| | | | | | | | |]; try discriminate Hf.
  destruct (PrimInt63.eqb k' k) eqn:K; [|discriminate Hf]. apply Uint63.eqb_correct in K. subst k'.
  apply andb_prop in Hf as [Hf NW]. apply andb_prop in Hf as [Hf WT]. apply andb_prop in Hf as [Z0 S1].
  apply weqb_eq in Z0. subst z. apply Uint63.eqb_correct in S1. subst s.
  cbn [fact_holds] in HF. destruct (ValP.nowrap_k_sound E fs Hfs _ _ NW) as (R & D).
  rewrite <- (den_VPz E k), HF, D. rewrite ValP.w2Zs_eq. destruct (wt o); [discriminate WT|]. pose proof (w2Z_range o). lia.
Qed.
Lemma stack_side_sound : forall E fs sp k, facts_hold E fs ->
  stack_side fs sp (sp_below_anchor fs sp) k = true -> bv_unsigned (den E sp) <= bv_unsigned (ev E k).
Proof.
  intros E fs sp k Hfs H. unfold stack_side, sp_below_anchor in H.
  destruct (known_leu fs sp (VP STACK_ID wzero)) eqn:A.
  - destruct (anchored_above fs k) eqn:AA.
    { apply (known_leu_sound E _ _ _ Hfs) in A. rewrite (den_VPz E STACK_ID) in A. pose proof (anchored_above_sound E fs k Hfs AA). lia. }
    destruct (known_leu fs (VP STACK_ID wzero) (VP k wzero)) eqn:B.
    + apply (known_leu_sound E _ _ _ Hfs) in A. apply (known_leu_sound E _ _ _ Hfs) in B. rewrite (den_VPz E STACK_ID) in A, B. rewrite (den_VPz E k) in B. lia.
    + apply (known_leu_sound E _ _ _ Hfs) in H. rewrite den_VPz in H. exact H.
  - apply (known_leu_sound E _ _ _ Hfs) in H. rewrite den_VPz in H. exact H.
Qed.
Lemma region_justified_inv : forall E fs sp wl k r, facts_hold E fs ->
  region_justified fs sp (sp_below_anchor fs sp) wl k r = true -> k <> 0%uint63 -> k <> STACK_ID ->
  Mem.rg_lo r = 0%uint63 /\
  (bv_unsigned (den E sp) <= bv_unsigned (ev E k)
   \/ exists len kd, win_lookup wl k = Some (len, kd) /\ known_leu_q fs (Mem.rg_hi r) len = true).
Proof.
  intros E fs sp wl k r Hfs J K0 K1. unfold region_justified in J.
  destruct (Uint63.eqb k 0%uint63) eqn:Q0; [apply Uint63.eqb_correct in Q0; congruence|].
  destruct (Uint63.eqb k STACK_ID) eqn:Q1; [apply Uint63.eqb_correct in Q1; congruence|].
  destruct (Uint63.eqb (Mem.rg_lo r) 0%uint63) eqn:L0; [|discriminate]. apply Uint63.eqb_correct in L0.
  split; [exact L0|].
  destruct (win_lookup wl k) as [[len kd]|] eqn:WL.
  - destruct (known_leu_q fs (Mem.rg_hi r) len) eqn:W.
    + right. exists len, kd. split; [reflexivity| exact W].
    + left. exact (stack_side_sound E fs sp k Hfs J).
  - left. exact (stack_side_sound E fs sp k Hfs J).
Qed.
Lemma known_eq_sound : forall E fs a b, facts_hold E fs -> known_eq fs a b = true -> den E a = den E b.
Proof.
  intros E fs a b Hfs H. unfold known_eq, dec_true in H. destruct (decide_eq fs a b) as [[|]|] eqn:D; try discriminate H.
  exact (proj1 (eqb_iff _ _ true) (ValP.decide_eq_sound E fs Hfs a b true D)).
Qed.

Lemma getr_R : forall E st ms mo, St.st_ok rsegs OPS E st ms mo ->
  forall x, PropExec.getr (ms_regs ms) (reg_of_r5 x) = den E (getr st x).
Proof.
  intros E st ms mo HS x. pose proof (so_regs _ _ _ _ _ _ HS x) as R. unfold rget in R. cbn [c_regs] in R.
  unfold PropExec.getr, getr. unfold is_x0 in R.
  destruct x; cbn [reg_of_r5 r5_to_Z] in R |- *; first [exact R | rewrite <- R; reflexivity].
Qed.

Lemma reg_of_X1 : reg_of_r5 X1 = 1%bv. Proof. apply bv_eq. reflexivity. Qed.
Lemma reg_of_X2 : reg_of_r5 X2 = 2%bv. Proof. apply bv_eq. reflexivity. Qed.
Lemma reg_of_X4 : reg_of_r5 X4 = 4%bv. Proof. apply bv_eq. reflexivity. Qed.
Lemma reg_of_X10 : reg_of_r5 X10 = 10%bv. Proof. apply bv_eq. reflexivity. Qed.
Lemma reg_of_X11 : reg_of_r5 X11 = 11%bv. Proof. apply bv_eq. reflexivity. Qed.
Lemma reg_of_X12 : reg_of_r5 X12 = 12%bv. Proof. apply bv_eq. reflexivity. Qed.

Set Implicit Arguments.
Record callG (E : env) (st : sstate) (ms : machine_state) (mo : Model) (need r ksp : int) (hargs : list sv)
       (wnl : list (int * sv * w64)) (off : w64) (r1 : Mem.region) (n : nat) (md : w64) (A : sv) (nw : w64) (rest : list sv)
       (s : PState) (LBf : list block) (LB : blocks) : Prop := CG {
  cg_ms : ms = MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 (to_Z (s_pc st))) (ms_fcsr ms) None (ms_mem ms) (seg_rom rsegs);
  cg_regs : forall x, PropExec.getr (ms_regs ms) (reg_of_r5 x) = den E (getr st x);
  cg_tp : PropExec.getr (ms_regs ms) 4%bv = Z_to_bv 64 RATP;
  cg_ra : MState.ret_pc (PropExec.getr (ms_regs ms) 1%bv) = PropExec.getr (ms_regs ms) 1%bv;
  cg_ra_r : PropExec.getr (ms_regs ms) 1%bv = Z_to_bv 64 (to_Z r);
  cg_r62 : to_Z r < 2 ^ 62;
  cg_fresh : fresh_ok st = true;

  cg_x2 : getr st X2 = VP STACK_ID off;
  cg_r1 : IMap.find STACK_ID (s_regs st) = Some r1;
  cg_r1w : Mem.rg_w r1 = true;
  cg_r1bg : Mem.rg_bg r1 = Mem.BGNone;
  cg_ksp : Mem.okey off = Some ksp;
  cg_ksp16 : keyZ ksp mod 16 = 0;
  cg_kspneg : keyZ ksp < 0;
  cg_sp : bv_unsigned (PropExec.getr (ms_regs ms) 2%bv) = bv_unsigned (ev E STACK_ID) + keyZ ksp;
  cg_lo0 : 0 <= bv_unsigned (ev E STACK_ID) + loZ r1;
  cg_room : bv_unsigned (ev E STACK_ID) + loZ r1 <= bv_unsigned (ev E STACK_ID) + keyZ ksp - to_Z need;
  cg_hi : bv_unsigned (ev E STACK_ID) + keyZ ksp <= bv_unsigned (ev E STACK_ID) + hiZ E r1 < 2 ^ 64;
  cg_stk : stk rsegs (ms_mem ms) (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + hiZ E r1);
  cg_ceil : alloc_ceiling <= bv_unsigned (ev E STACK_ID) + loZ r1;

  cg_statics : statics_ok rsegs ERRNO LIBC GOT GUARD CANARY st = true;
  cg_pubs : PUBS (ms_mem ms);
  cg_auxcell : rw_cells rsegs (ms_mem ms) RAUXV_CELL [C8 (ev E AUXV_ID)];
  cg_r3 : exists r3, IMap.find AUXV_ID (s_regs st) = Some r3;
  cg_auxv : rauxv_ok (ms_mem ms) (bv_unsigned (ev E STACK_ID) + keyZ ksp);
  cg_errno : exists errv, rw_cells rsegs (ms_mem ms) RERRNO [C4 errv];
  cg_minv : mem_inv rsegs (ms_mem ms);
  cg_mo : mo_ok mo;

  cg_find : find_op HEAP_ID (s_ops st) = Some hargs;
  cg_count : count_op HEAP_ID (s_ops st) = 1%nat;
  cg_nwin : heap_nwin hargs = Some n;
  cg_hargs : hargs = VL md :: A :: VL nw :: rest;
  cg_nw : wt nw = false /\ n = Z.to_nat (to_Z (wl nw)) /\ (3 * n <= length rest)%nat;
  cg_n255 : (n <= 255)%nat;
  cg_decode : decode (map (den E) hargs) = Some (w2Z md, den E A, wins_of E n rest, map (den E) (skipn (3 * n) rest));
  cg_perm : Permutation (blocks_of LBf) LB;
  cg_rheap : RHEAP s LBf (ms_mem ms);
  cg_krel : KREL s LBf mo;
  cg_claim : pclaim (bv_unsigned (den E A)) s LBf mo;
  cg_repl : rw_cells rsegs (ms_mem ms) RMREPL [C4 (wz 0)];
  cg_wf : windows_wf (wins_of E n rest) LB alloc_ceiling;
  cg_ng : NG (wins_of E n rest);
  cg_cw : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * n) rest)) LB (wins_of E n rest) (ms_mem ms);
  cg_swin : stack_window_ok n rest (Mem.rg_lo r1) = true;
  cg_wnl : nonstack_windows n rest = Some wnl;
  cg_anch : windows_anchored (s_regs st) wnl = true;
  cg_just : regions_justified st wnl = true }.
Unset Implicit Arguments.

Theorem alloc_call_sound : forall E st ms mo need r ksp hargs wnl,
  St.st_ok rsegs OPS E st ms mo -> PB (eb E) -> to_Z need < 2 ^ 32 ->
  alloc_call rsegs ERRNO LIBC GOT GUARD TP CANARY need st = Some (r, ksp, hargs, wnl) ->
  exists off r1 n md A nw rest s LBf LB, callG E st ms mo need r ksp hargs wnl off r1 n md A nw rest s LBf LB.
Proof.
  intros E st ms mo need r ksp hargs wnl HS HPB Hneed H. pose proof (int_range need) as Rneed.
  destruct (alloc_call_inv need st r ksp hargs wnl H) as (Hrv & Hcp & Hr62 & (ra & Hra & Hev) & Htp & Hst & Hav & Hab & klo1 & Hstk & Hhw).
  destruct (call_pre_inv st r Hcp) as (Hfr & ra' & Hra' & Twt & Tlt & ->). rewrite Hra in Hra'. injection Hra' as <-.
  destruct (statics_sound E st ms mo HS HPB Hst) as (PU & AC & ER).
  destruct (stack_sound E st ms mo need ksp klo1 HS Hneed Hstk) as (off & r1 & HX2 & Hr1 & HW & HBG & Hksp & -> & A16 & NEG & Esp & LO0 & ROOM & HI & STK).
  destruct (heap_windows_inv st (Mem.rg_lo r1) hargs wnl Hhw) as (Hf & Hc & n & md & A & nw & rest & Hn & Eh & T & N & L & N255 & SW & NW & AN & JU).
  pose proof (ops_hold_find OPS E (s_ops st) (ms_mem ms) mo HEAP_ID _ (so_ops _ _ _ _ _ _ HS) Hf) as HH.
  rewrite OPS_holds1 in HH. destruct HH as (md' & aw & ws & ca & LB & D & HA & WF & HC).
  rewrite Eh, (decode_hargs E md A nw rest n T N L) in D. injection D as <- <- <- <-.
  destruct HA as ((s & LBf & P & RC & K & MT & CL & RP) & NGW).

  destruct (stack_window_In E n rest (Mem.rg_lo r1) SW) as (wlo & wlen & Hwlo & INw).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & [[_ CE]|[[KB _]|[KS _]]]); cbn [w_kind w_lo] in *;
    [| unfold K_BLOCK, K_STACK in KB; lia | unfold K_SUB, K_STACK in KS; lia].
  assert (Elo : bv_unsigned (den E (VP STACK_ID wlo)) = bv_unsigned (ev E STACK_ID) + loZ r1).
  { rewrite den_VP. destruct (okey_sound _ _ Hwlo) as [EK _]. unfold loZ in *. rewrite <- EK. apply Z.mod_small. unfold two64.
    pose proof (int_range need). lia. }
  rewrite Elo in CE. cbn [aw_ceiling AWI] in CE.
  pose proof (getr_R E st ms mo HS) as GR.
  assert (MSE : ms = MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 (to_Z (s_pc st))) (ms_fcsr ms) None (ms_mem ms) (seg_rom rsegs)).
  { rewrite (MS_eta ms) at 1 by exact (so_svc _ _ _ _ _ _ HS). f_equal.
    + exact (so_pc _ _ _ _ _ _ HS).
    + pose proof (so_resv _ _ _ _ _ _ HS) as RV. rewrite Hrv in RV. exact RV.
    + exact (so_rom _ _ _ _ _ _ HS). }
  assert (TP4 : PropExec.getr (ms_regs ms) 4%bv = Z_to_bv 64 RATP).
  { rewrite <- reg_of_X4, GR, Htp. rewrite den_wlit. reflexivity. }
  pose proof (int_range (wl ra)) as Rr. rewrite two63_eq in Rr.
  assert (RA1 : MState.ret_pc (PropExec.getr (ms_regs ms) 1%bv) = PropExec.getr (ms_regs ms) 1%bv).
  { rewrite <- reg_of_X1, GR, Hra, den_VL. unfold wbv. rewrite (w2Z_nowt ra Twt).
    apply ret_pc_even; [lia|].
    pose proof (land_mk (wl ra) 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite Hev in LM. change (to_Z 0%uint63) with 0 in LM.
    change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  assert (RA2 : PropExec.getr (ms_regs ms) 1%bv = Z_to_bv 64 (to_Z (wl ra))).
  { rewrite <- reg_of_X1, GR, Hra, den_VL. unfold wbv. rewrite (w2Z_nowt ra Twt). reflexivity. }
  assert (R62 : to_Z (wl ra) < 2 ^ 62).
  { apply Uint63.ltb_spec in Tlt. rewrite to_Z_bit62i in Tlt. exact Tlt. }
  assert (SP2 : bv_unsigned (PropExec.getr (ms_regs ms) 2%bv) = bv_unsigned (ev E STACK_ID) + keyZ ksp).
  { rewrite <- reg_of_X2, GR. exact Esp. }
  assert (AUX : rauxv_ok (ms_mem ms) (bv_unsigned (ev E STACK_ID) + keyZ ksp)).
  { unfold above_stack_ok in Hab. cbv zeta in Hab.
    destruct (stack_side (s_facts st) (getr st X2) (sp_below_anchor (s_facts st) (getr st X2)) AUXV_ID) eqn:B1; [|discriminate Hab].
    rename Hab into B2.
    apply (auxv_sound E st ms mo _ HS HPB Hav AC); [lia| |].
    + apply (stack_side_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in B1. rewrite Esp in B1. exact B1.
    + apply (stack_side_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in B2. rewrite Esp in B2. exact B2. }
  pose proof (auxv_region E st ms mo HS Hav) as R3.
  assert (MINV : mem_inv rsegs (ms_mem ms)).
  { intros a b Hm. unfold ro_addr. destruct (find_segment rsegs (bv_unsigned a) 1) as [seg|] eqn:Fs; [|reflexivity].
    rewrite (so_minv _ _ _ _ _ _ HS a b Hm seg Fs). reflexivity. }
  assert (MOK : mo_ok mo).
  { destruct (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS)) as [MH ML]. split; [exact MH|]. split; [exact ML| exact MT]. }
  assert (DEC : decode (map (den E) hargs) = Some (w2Z md, den E A, wins_of E n rest, map (den E) (skipn (3 * n) rest))).
  { rewrite Eh. exact (decode_hargs E md A nw rest n T N L). }
  assert (RH : RHEAP s LBf (ms_mem ms)). { apply RHEAP_split. split; [exact RC| exact PU]. }
  exists off, r1, n, md, A, nw, rest, s, LBf, LB.
  constructor; try assumption; auto.
Qed.

End CEIL.
End TwinB.
