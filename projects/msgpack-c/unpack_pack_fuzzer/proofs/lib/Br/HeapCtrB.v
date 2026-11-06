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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import F_syscalls RMallocRep RMallocTree RMallocKit_B RMalloc_iface RMalloc_ifaceP RF_aligned16 RRealloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Instr Plan ValProofs MemProofs StepSoundBase StepSoundMem StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem State Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM DefsE DefsN.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue RegsEqv TreeBridgeN KRel MPath Room HeapCore MF MFInst AW RMallocG RAllocG CtrFX HeapCtr.
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
Variable Cw : client_world.
Variable OPS : St.optable.

Hypothesis OPS_plain : St.plain_table OPS.
Hypothesis OPS_holds1 : forall args m mo, St.op_holds OPS HEAP_ID args m mo = heap_holds rsegs IMGX AWI Cw args m mo.
Hypothesis OPS_fp1 : forall args, St.op_fp OPS HEAP_ID args = heap_fp IMGX args.

Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> St.op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  St.op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS id args) ->
  0x52000 <= a < 0x88000 /\ ~ ralloc_static a.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> vm_agree mo mo' -> St.op_holds OPS id args m mo ->
  St.op_holds OPS id args m mo'.
Variable MP : Model -> Prop.
Hypothesis MP_vm : forall mo mo', vm_agree mo mo' -> MP mo -> MP mo'.
Variable PB : (int -> list byte) -> Prop.
Variable CANARY : sv.
Hypothesis PB_canary : forall E, PB (eb E) -> den E CANARY = Z_to_bv 64 ssp_canary.
Hypothesis PB_secret : forall E, PB (eb E) -> forall i, (i < 8)%nat ->
  nth_error (eb E 6%uint63) (8 + i) = nth_error (le8 (wz ctx_secret)) i.

Lemma alloc_post_inv : forall st r ksp st4 r1,
  IMap.find STACK_ID (s_regs st) = Some r1 ->
  alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp = Some st4 ->
  exists r0, IMap.find 0%uint63 (s_regs st) = Some r0 /\ st4 = alloc_post_mk ERRNO LIBC GOT GUARD CANARY st r ksp r0 r1.
Proof.
  intros st r ksp st4 r1 Hr1 H. unfold alloc_post in H. rewrite Hr1 in H.
  destruct (IMap.find 0%uint63 (s_regs st)) as [r0|]; [|discriminate]. apply Some_inj in H. exists r0. auto.
Qed.

Lemma rget_core_getr : forall R F pc fc rv x, rget (Core R F pc fc rv) (reg_of_r5 x) = PropExec.getr R (reg_of_r5 x).
Proof. intros. apply rget_getr. Qed.

Lemma reg_of_X0 : reg_of_r5 X0 = 0%bv. Proof. apply bv_eq. reflexivity. Qed.
Lemma key_range_half : forall i, - two63 / 2 <= keyZ i < two63 / 2.
Proof. intros i. pose proof (keyZ_range i). change (- two63 / 2) with (- (2 ^ 62)). rewrite half63. lia. Qed.
Lemma getr_x0 : forall R, PropExec.getr R (reg_of_r5 X0) = Z_to_bv 64 0.
Proof. intros R. rewrite reg_of_X0. unfold PropExec.getr. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma kept_or_clobbered : forall x, x <> X0 -> x <> X10 -> clob_pos x = None -> In (reg_of_r5 x) kept_regs.
Proof.
  intros x N0 N10 H. destruct x; try discriminate H; try congruence;
  unfold kept_regs; cbn [In];
  repeat match goal with |- ?a = ?b \/ _ => first [left; apply bv_eq; reflexivity | right] | |- False => fail end.
Qed.

Lemma aload_priv : forall st a w v, aload rsegs st a w = Some v -> in_priv_b (s_priv st) a w = false.
Proof.
  intros st a w v H. unfold aload, do_load in H. cbn [addr_of] in H.
  destruct (IMap.find 0%uint63 (s_regs st)) as [r0|]; [|discriminate].
  destruct (Mem.okey (wlit a)) as [key|] eqn:Hk; [|discriminate].
  assert (Ek : key = a).
  { unfold Mem.okey in Hk. cbn [wt wl wlit] in Hk. destruct (PrimInt63.ltb a bit62i); [injection Hk as <-; reflexivity| discriminate]. }
  subst key. destruct (can_read rsegs (s_facts st) (s_priv st) 0%uint63 r0 a w) eqn:CR; [|discriminate].
  unfold can_read in CR. rewrite Uint63.eqb_refl in CR. apply andb_prop in CR as [_ P]. destruct (in_priv_b (s_priv st) a w); [discriminate| reflexivity].
Qed.

Lemma nth_error_Z_to_le_bytes : forall k z i, (i < k)%nat ->
  nth_error (Z_to_le_bytes k z) i = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat i))).
Proof.
  induction k as [|k IH]; intros z i Hi; [lia|]. cbn [Z_to_le_bytes]. destruct i as [|i].
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma byte_of_le8 : forall (w : word) i, (i < 8)%nat -> nth_error (le8 w) i = Some (byte_of w (Z.of_nat i)).
Proof. intros w i Hi. unfold le8, word_to_le_bytes, byte_of. apply nth_error_Z_to_le_bytes. exact Hi. Qed.
Lemma byte_of_le4 : forall (w : word) i, (i < 4)%nat -> nth_error (le4 w) i = Some (byte_of w (Z.of_nat i)).
Proof. intros w i Hi. unfold le4, byte_of. apply nth_error_Z_to_le_bytes. exact Hi. Qed.

Lemma rw_cell_rb : forall m A (c : Cells.cell) i, rw_cells rsegs m A [c] -> (i < length (cbytes c))%nat ->
  rb rsegs m (A + Z.of_nat i) = nth_error (cbytes c) i.
Proof.
  intros m A c i [[_ HB] _] Hi. cbn [cells_bytes] in HB. rewrite app_nil_r in HB. destruct HB as (_ & _ & HB).
  rewrite rb_mrd. apply HB. exact Hi.
Qed.

Lemma region_store_known : forall priv E m fs k r key w v,
  facts_hold E fs -> ev E 0%uint63 = Z_to_bv 64 0 ->
  St.region_ok rsegs priv E m k r -> wok w -> can_write rsegs fs priv k r key w = true ->
  (forall i, 0 <= i < to_Z w -> rb rsegs m (addrZ E k key + i) = Some (byte_of (den E v) i)) ->
  St.region_ok rsegs priv E m k (Mem.region_store r key w v).
Proof.
  intros priv E m fs k r key w v Hfs Hz RO Hw CW BY.
  destruct (region_store_sound rsegs priv E m fs k r key w v Hfs Hz RO Hw CW) as (_ & RO' & Elo & Ehi & Ew & Ebg & FR).
  cbv zeta in RO'. set (A := addrZ E k key) in *.
  set (m' := write_to_mem m (Z_to_bv 64 A) (store_bytes w (den E v))) in *.
  pose proof (can_write_sound rsegs priv E m fs k r key w Hfs Hz RO Hw CW) as (CR & _ & _).
  pose proof (can_read_sound rsegs priv E m fs k r key w Hfs Hz RO Hw CR) as (RA & RAw & _ & RNG & _). cbv zeta in RA, RAw. fold A in RA, RAw.
  assert (Hw8 : 1 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  assert (RB : forall x, 0 <= x < two64 -> rb rsegs m x = rb rsegs m' x).
  { intros x Hx. destruct (Z_lt_le_dec x A) as [L|G]; [| destruct (Z_lt_le_dec x (A + to_Z w)) as [L2|G2]].
    - unfold rb. rewrite (FR x Hx) by lia. reflexivity.
    - replace x with (A + (x - A)) by lia. rewrite (BY (x - A)) by lia.
      unfold rb. subst m'. rewrite (write_to_mem_in m A (store_bytes w (den E v)) (x - A));
        [| lia | rewrite store_bytes_length, Z2Nat.id; unfold two64 in *; lia| rewrite store_bytes_length, Z2Nat.id; lia].
      rewrite store_bytes_nth_error by lia. reflexivity.
    - unfold rb. rewrite (FR x Hx) by lia. reflexivity. }
  apply (region_ok_fine_frame rsegs priv E m' m k (Mem.region_store r key w v) Hz RO').
  - intros o H1 H2 _. apply RB.
    destruct (PrimInt63.eqb k 0%uint63) eqn:K.
    + destruct (H2 eq_refl) as (Q & _). apply Uint63.eqb_correct in K. subst k. rewrite (ev0_zero E Hz). rewrite half63 in Q. unfold two64. lia.
    + specialize (H1 eq_refl). unfold loZ, hiZ in H1. rewrite Elo, Ehi in H1. pose proof (ro_range _ _ _ _ _ _ RO K) as [R1 R2].
      unfold loZ, hiZ in R1, R2. lia.
  - intros K a Ha. unfold loZ, hiZ in Ha. rewrite Elo, Ehi in Ha. destruct (ro_valid _ _ _ _ _ _ RO K a Ha) as (V1 & V2 & _).
    split; [exact V1|]. rewrite Ew. exact V2.
Qed.

Ltac zofN_lits_in H := repeat match type of H with context [Z.of_N ?x] => let v := eval vm_compute in (Z.of_N x) in change (Z.of_N x) with v in H end.
Ltac seg_cases H :=
  unfold rsegs, Plain.M.loaded_segments,
    Plain.Plain_loaded_segments in H; cbn [find_segment] in H;
  repeat match type of H with (if ?c then _ else _) = _ => destruct c eqn:?Q end;
  repeat match goal with X : _ && _ = true |- _ => zofN_lits_in X; apply andb_prop in X;
                             let X1 := fresh "SB" in let X2 := fresh "SB" in destruct X as [X1 X2]; apply Z.leb_le in X1; apply Z.leb_le in X2
                        | X : _ && _ = false |- _ => zofN_lits_in X; apply andb_false_iff in X; rewrite !Z.leb_gt in X end.

Lemma rw_seg_range : forall a seg, find_segment rsegs a 1 = Some seg -> seg_writable seg = true -> 0x52000 <= a < 0x88000.
Proof.
  intros a seg H W. seg_cases H; try discriminate H; injection H as <-; cbn in W; try discriminate W; lia.
Qed.

Lemma hi_seg : forall a, 0x56000 <= a < 0x88000 -> exists seg, find_segment rsegs a 1 = Some seg.
Proof.
  intros a Ha. destruct (find_segment rsegs a 1) as [seg|] eqn:H; [exists seg; reflexivity| exfalso].
  seg_cases H; try discriminate H; lia.
Qed.

Lemma del_window_wins : forall E0 m ws lo ws', del_window m ws lo = Some ws' -> (3 * m <= length ws)%nat ->
  exists l1 len l2, wins_of E0 m ws = l1 ++ Win (bv_unsigned (den E0 lo)) (bv_unsigned (den E0 len)) K_BLOCK :: l2
    /\ wins_of E0 (pred m) ws' = l1 ++ l2 /\ skipn (3 * pred m) ws' = skipn (3 * m) ws /\ (3 * pred m <= length ws')%nat /\ (1 <= m)%nat.
Proof.
  intros E0 m. induction m as [|m IH]; intros ws lo ws' H L; [cbn in H; destruct ws; discriminate|].
  destruct ws as [|l [|sz [|kd ws0]]]; try (cbn in H; discriminate). cbn [del_window] in H. cbn [length] in L.
  destruct (sv_eqb l lo && sv_eqb kd (VL CtrLib.K_BLOCK)) eqn:C.
  - apply Some_inj in H. subst ws'. apply andb_prop in C as [C1 C2]. apply sv_eqb_eq in C1. apply sv_eqb_eq in C2. subst l kd.
    exists [], sz, (wins_of E0 m ws0). rewrite wins_of_cons, unsigned_VL. cbn [app pred]. repeat split; try reflexivity; try lia.
    replace (3 * S m)%nat with (S (S (S (3 * m)))) by lia. reflexivity.
  - destruct (del_window m ws0 lo) as [ws''|] eqn:D; [|discriminate]. apply Some_inj in H. subst ws'.
    destruct (IH ws0 lo ws'' D ltac:(lia)) as (l1 & len & l2 & W1 & W2 & SK & L2 & M1).
    exists (Win (bv_unsigned (den E0 l)) (bv_unsigned (den E0 sz)) (bv_unsigned (den E0 kd)) :: l1), len, l2.
    rewrite wins_of_cons, W1. cbn [app]. split; [reflexivity|].
    destruct m as [|m']; [lia|]. cbn [pred] in *. rewrite wins_of_cons, W2. split; [reflexivity|].
    replace (3 * S m')%nat with (S (S (S (3 * m')))) by lia. replace (3 * S (S m'))%nat with (S (S (S (3 * S m')))) by lia.
    cbn [skipn length]. rewrite SK. replace (3 * S m')%nat with (S (S (S (3 * m')))) by lia. cbn [skipn]. repeat split; try reflexivity; lia.
Qed.

Lemma free_ok_inv : forall st wl kf lenf, free_ok st wl kf = Some lenf ->
  exists rf, IMap.find kf (s_regs st) = Some rf /\ win_lookup wl kf = Some (lenf, CtrLib.K_BLOCK)
    /\ Mem.rg_lo rf = 0%uint63 /\ known_ltu (s_facts st) (VL wzero) (Mem.rg_hi rf) = true /\ known_leu_q (s_facts st) (Mem.rg_hi rf) lenf = true
    /\ forall k len kd, In (k, len, kd) wl -> k <> kf ->
         exists rg, IMap.find k (s_regs st) = Some rg /\ Mem.rg_lo rg = 0%uint63
           /\ (known_ltu (s_facts st) (VL wzero) (Mem.rg_hi rg) = true
               \/ (kd <> CtrLib.K_BLOCK /\ known_eq (s_facts st) (Mem.rg_hi rg) len = true
                   /\ exists k3 len3, In (k3, len3, CtrLib.K_BLOCK) wl /\ k3 <> kf))
           /\ known_leu_q (s_facts st) (Mem.rg_hi rg) len = true /\ (Mem.rg_w rf = true \/ Mem.rg_w rg = true)
           /\ (kd = CtrLib.K_BLOCK \/ known_eq (s_facts st) (Mem.rg_hi rf) lenf = true).
Proof.
  intros st wl kf lenf H. unfold free_ok in H.
  destruct (IMap.find kf (s_regs st)) as [rf|] eqn:Hrf; [|discriminate].
  destruct (win_lookup wl kf) as [[lenf' kdf]|] eqn:WL; [|discriminate].
  destruct (negb (weqb kdf CtrLib.K_BLOCK) || negb (PrimInt63.eqb (Mem.rg_lo rf) 0) || negb (known_ltu (s_facts st) (VL wzero) (Mem.rg_hi rf))
            || negb (known_leu_q (s_facts st) (Mem.rg_hi rf) lenf')) eqn:C; [discriminate|].
  apply orb_false_iff in C as [C C4]. apply orb_false_iff in C as [C C3]. apply orb_false_iff in C as [C1 C2].
  apply negb_false_iff in C1. apply negb_false_iff in C2. apply negb_false_iff in C3. apply negb_false_iff in C4.
  apply weqb_eq in C1. apply Uint63.eqb_correct in C2. subst kdf.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:FA end; [|discriminate]. apply Some_inj in H. subst lenf'.
  exists rf. repeat (split; [assumption || reflexivity|]).
  intros k len kd Hin NK. pose proof (proj1 (forallb_forall _ _) FA _ Hin) as X. cbv beta iota in X.
  destruct (Uint63.eqb k kf) eqn:Q; [apply Uint63.eqb_correct in Q; congruence|]. cbn [orb] in X.
  destruct (IMap.find k (s_regs st)) as [rg|]; [|discriminate]. exists rg.
  apply andb_prop in X as [X X6]. apply andb_prop in X as [X X5]. apply andb_prop in X as [X X4]. apply andb_prop in X as [X1 X3].
  apply Uint63.eqb_correct in X1. split; [reflexivity|]. split; [exact X1|]. split; [| split; [exact X3|]; split].
  - apply orb_prop in X6 as [X6|X6]; [left; exact X6| right].
    apply andb_prop in X6 as [X6 OB]. apply andb_prop in X6 as [NKB HEQ]. apply negb_true_iff in NKB.
    split; [intros ->; rewrite weqb_refl in NKB; discriminate NKB|]. split; [exact HEQ|].
    apply existsb_exists in OB as ([[k3 len3] kd3] & I3 & CK3). apply andb_prop in CK3 as [N3 K3].
    apply negb_true_iff in N3. apply Uint63.eqb_false_spec in N3. apply weqb_eq in K3. subst kd3. exists k3, len3. auto.
  - apply orb_prop in X4 as [X4|X4]; [left| right]; exact X4.
  - apply orb_prop in X5 as [X5|X5]; [left; apply weqb_eq in X5; exact X5| right; exact X5].
Qed.

Lemma windows_anchored_nodup : forall R wl k len kd len' kd',
  windows_anchored R wl = true -> In (k, len, kd) wl -> In (k, len', kd') wl -> len = len' /\ kd = kd'.
Proof.
  intros R wl. induction wl as [|[[k0 len0] kd0] wl IH]; intros k len kd len' kd' H I1 I2; [destruct I1|].
  cbn [windows_anchored] in H. destruct (IMap.find k0 R); [|discriminate]. destruct (win_lookup wl k0) eqn:WL; [discriminate|].
  assert (NOTIN : forall ln kn, ~ In (k0, ln, kn) wl).
  { intros ln kn X. clear IH I1 I2. induction wl as [|[[k1 l1] d1] wl IH2]; [destruct X|]. cbn [win_lookup] in WL.
    destruct (Uint63.eqb k1 k0) eqn:Q; [discriminate|]. destruct X as [X|X]; [injection X as -> -> ->; rewrite Uint63.eqb_refl in Q; discriminate|].
    cbn [windows_anchored] in H. destruct (IMap.find k1 R); [|discriminate]. destruct (win_lookup wl k1); [discriminate|]. exact (IH2 WL H X). }
  destruct I1 as [I1|I1]; destruct I2 as [I2|I2].
  - rewrite I1 in I2. injection I2 as <- <-. auto.
  - injection I1 as -> -> ->. exfalso. exact (NOTIN _ _ I2).
  - injection I2 as -> -> ->. exfalso. exact (NOTIN _ _ I1).
  - exact (IH k len kd len' kd' H I1 I2).
Qed.

Lemma wins_cover : forall E0 m ws wl w, nonstack_windows m ws = Some wl -> In w (wins_of E0 m ws) ->
  w_kind w = K_STACK \/ exists k len kd, In (k, len, kd) wl /\ w = Win (bv_unsigned (ev E0 k)) (bv_unsigned (den E0 len)) (w2Z kd).
Proof.
  intros E0 m. induction m as [|m IH]; intros ws wl w H Hin; [destruct ws; cbn in Hin; destruct Hin|].
  destruct ws as [|wlo [|ln [|kdv ws']]]; try (cbn in Hin; destruct Hin; fail); try (cbn in H; discriminate).
  cbn [nonstack_windows] in H. destruct kdv as [kw| | | | | | | | | |]; try discriminate.
  destruct (nonstack_windows m ws') as [l|] eqn:NW; [|discriminate].
  rewrite wins_of_cons in Hin.
  destruct (weqb kw wzero) eqn:Z0.
  - apply Some_inj in H. subst wl. destruct Hin as [<-|Hin].
    + left. cbn [w_kind]. rewrite unsigned_VL. apply weqb_eq in Z0. subst kw. reflexivity.
    + exact (IH ws' l w NW Hin).
  - destruct wlo as [|k0 o0| | | | | | | | |]; try discriminate.
    destruct (weqb o0 wzero && negb (PrimInt63.eqb k0 0) && negb (PrimInt63.eqb k0 STACK_ID)) eqn:C; [|discriminate].
    apply Some_inj in H. subst wl. apply andb_prop in C as [C _]. apply andb_prop in C as [C1 _]. apply weqb_eq in C1. subst o0.
    destruct Hin as [<-|Hin].
    + right. exists k0, ln, kw. split; [left; reflexivity|]. rewrite den_VPz, unsigned_VL. reflexivity.
    + destruct (IH ws' l w NW Hin) as [S|(k & len & kd & I & ->)]; [left; exact S| right]. exists k, len, kd. split; [right; exact I| reflexivity].
Qed.

Lemma del_window_has : forall m ws kf ws' wl, del_window m ws (VP kf wzero) = Some ws' -> nonstack_windows m ws = Some wl ->
  exists len, In (kf, len, CtrLib.K_BLOCK) wl.
Proof.
  induction m as [|m IH]; intros ws kf ws' wl H N; [cbn in H; destruct ws; discriminate|].
  destruct ws as [|wlo [|ln [|kdv ws0]]]; try (cbn in H; discriminate). cbn [del_window] in H. cbn [nonstack_windows] in N.
  destruct kdv as [kw| | | | | | | | | |]; try discriminate.
  destruct (nonstack_windows m ws0) as [l|] eqn:NW; [|discriminate].
  destruct (sv_eqb wlo (VP kf wzero) && sv_eqb (VL kw) (VL CtrLib.K_BLOCK)) eqn:C.
  - apply andb_prop in C as [C1 C2]. apply sv_eqb_eq in C1. apply sv_eqb_eq in C2. injection C2 as ->. subst wlo.
    cbn [weqb wone wzero CtrLib.K_BLOCK] in N. rewrite weqb_refl in N || idtac.
    destruct (weqb CtrLib.K_BLOCK wzero) eqn:KZ; [apply weqb_eq in KZ; discriminate KZ|].
    cbn [andb negb] in N. destruct (PrimInt63.eqb kf 0); [discriminate|]. destruct (PrimInt63.eqb kf STACK_ID); [discriminate|].
    apply Some_inj in N. subst wl. exists ln. left. reflexivity.
  - destruct (del_window m ws0 (VP kf wzero)) as [ws''|] eqn:D; [|discriminate].
    assert (TL : forall l', (exists len, In (kf, len, CtrLib.K_BLOCK) l) -> (forall x, In x l -> In x l') -> exists len, In (kf, len, CtrLib.K_BLOCK) l').
    { intros l' [len I] SUB. exists len. apply SUB. exact I. }
    destruct (weqb kw wzero).
    + apply Some_inj in N. subst wl. exact (IH ws0 kf ws'' l D NW).
    + destruct wlo as [|k0 o0| | | | | | | | |]; try discriminate.
      destruct (weqb o0 wzero && negb (PrimInt63.eqb k0 0) && negb (PrimInt63.eqb k0 STACK_ID)); [|discriminate].
      apply Some_inj in N. subst wl. apply (TL _ (IH ws0 kf ws'' l D NW)). intros x Hx. right. exact Hx.
Qed.

Definition anchors (wl : list (int * sv * w64)) : list int := map (fun t => fst (fst t)) wl.

Lemma windows_anchored_nodup_anchors : forall R wl, windows_anchored R wl = true -> List.NoDup (anchors wl).
Proof.
  intros R wl. induction wl as [|[[k0 len0] kd0] wl IH]; intros H; [constructor|].
  cbn [windows_anchored] in H. destruct (IMap.find k0 R); [|discriminate]. destruct (win_lookup wl k0) eqn:WL; [discriminate|].
  cbn [anchors map fst]. constructor; [| apply IH; exact H].
  intros X. unfold anchors in X. apply in_map_iff in X as ([[k1 l1] d1] & E1 & I1). cbn [fst] in E1. subst k1.
  clear IH H. induction wl as [|[[k2 l2] d2] wl IH2]; [destruct I1|]. cbn [win_lookup] in WL.
  destruct (Uint63.eqb k2 k0) eqn:Q; [discriminate|]. destruct I1 as [I1|I1]; [injection I1 as -> -> ->; rewrite Uint63.eqb_refl in Q; discriminate|].
  exact (IH2 WL I1).
Qed.

Lemma del_window_prov : forall E0 m ws kf ws' wl, nonstack_windows m ws = Some wl -> del_window m ws (VP kf wzero) = Some ws' ->
  List.NoDup (anchors wl) ->
  forall w, In w (wins_of E0 (pred m) ws') ->
    w_kind w = K_STACK \/ exists k len kd, In (k, len, kd) wl /\ k <> kf /\ w = Win (bv_unsigned (ev E0 k)) (bv_unsigned (den E0 len)) (w2Z kd).
Proof.
  intros E0 m. induction m as [|m IH]; intros ws kf ws' wl N H ND w Hin; [cbn in H; destruct ws; discriminate|].
  destruct ws as [|wlo [|ln [|kdv ws0]]]; try (cbn in H; discriminate). cbn [del_window] in H. cbn [nonstack_windows] in N.
  destruct kdv as [kw| | | | | | | | | |]; try discriminate.
  destruct (nonstack_windows m ws0) as [l|] eqn:NW; [|discriminate].
  cbn [pred] in Hin.
  destruct (sv_eqb wlo (VP kf wzero) && sv_eqb (VL kw) (VL CtrLib.K_BLOCK)) eqn:C.
  -
    apply Some_inj in H. subst ws'. apply andb_prop in C as [C1 C2]. apply sv_eqb_eq in C1. apply sv_eqb_eq in C2. injection C2 as ->. subst wlo.
    destruct (weqb CtrLib.K_BLOCK wzero) eqn:KZ; [apply weqb_eq in KZ; discriminate KZ|].
    cbn [andb negb] in N. rewrite weqb_refl in N. cbn [andb negb] in N.
    destruct (PrimInt63.eqb kf 0); [discriminate|]. destruct (PrimInt63.eqb kf STACK_ID); [discriminate|].
    apply Some_inj in N. subst wl. cbn [anchors map fst] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
    destruct (wins_cover E0 m ws0 l w NW Hin) as [S|(k & len & kd & I & ->)]; [left; exact S| right].
    exists k, len, kd. split; [right; exact I|]. split; [| reflexivity].
    intros ->. apply NI. unfold anchors. apply in_map_iff. exists (kf, len, kd). auto.
  - destruct (del_window m ws0 (VP kf wzero)) as [ws''|] eqn:D; [|discriminate]. apply Some_inj in H. subst ws'.
    destruct m as [|m']; [cbn in D; destruct ws0; discriminate|].
    rewrite wins_of_cons in Hin.
    destruct (weqb kw wzero) eqn:Z0.
    + apply Some_inj in N. subst wl. destruct Hin as [<-|Hin].
      * left. cbn [w_kind]. rewrite unsigned_VL. apply weqb_eq in Z0. subst kw. reflexivity.
      * exact (IH ws0 kf ws'' l NW D ND w Hin).
    + destruct wlo as [|k0 o0| | | | | | | | |]; try discriminate.
      destruct (weqb o0 wzero && negb (PrimInt63.eqb k0 0) && negb (PrimInt63.eqb k0 STACK_ID)) eqn:CC; [|discriminate].
      apply Some_inj in N. subst wl. apply andb_prop in CC as [CC _]. apply andb_prop in CC as [C1 _]. apply weqb_eq in C1. subst o0.
      cbn [anchors map fst] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
      assert (NK : k0 <> kf).
      { intros ->. destruct (del_window_has _ ws0 kf ws'' l D NW) as [len I]. apply NI. unfold anchors. apply in_map_iff. exists (kf, len, CtrLib.K_BLOCK). auto. }
      destruct Hin as [<-|Hin].
      * right. exists k0, ln, kw. split; [left; reflexivity|]. split; [exact NK|]. rewrite den_VPz, unsigned_VL. reflexivity.
      * destruct (IH ws0 kf ws'' l NW D ND w Hin) as [S|(k & len & kd & I & NK' & ->)]; [left; exact S| right].
        exists k, len, kd. split; [right; exact I|]. auto.
Qed.

Lemma set_op_same : forall id os args, find_op id os = Some args -> set_op id args os = os.
Proof.
  intros id os args. induction os as [|o os IH]; intros H; [discriminate|]. cbn [find_op set_op] in H |- *.
  destruct (Uint63.eqb (op_id o) id) eqn:Q.
  - injection H as <-. apply Uint63.eqb_correct in Q. destruct o as [i a]. cbn [op_id op_args] in *. subst i. reflexivity.
  - rewrite (IH H). reflexivity.
Qed.

Lemma st_ok_fields : forall segs OPS0 E0 st1 st2 ms0 mo0,
  s_pc st2 = s_pc st1 -> s_rf st2 = s_rf st1 -> s_ff st2 = s_ff st1 -> s_resv st2 = s_resv st1 -> s_regs st2 = s_regs st1 ->
  s_facts st2 = s_facts st1 -> s_ops st2 = s_ops st1 -> s_priv st2 = s_priv st1 ->
  St.st_ok segs OPS0 E0 st1 ms0 mo0 -> St.st_ok segs OPS0 E0 st2 ms0 mo0.
Proof.
  intros segs OPS0 E0 st1 st2 ms0 mo0 E1 E2 E3 E4 E5 E6 E7 E8 HS. destruct HS. split; rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8; assumption.
Qed.

Lemma wsub_one_small : forall nw, wt nw = false -> 1 <= to_Z (wl nw) ->
  wt (wsub nw wone) = false /\ to_Z (wl (wsub nw wone)) = to_Z (wl nw) - 1.
Proof.
  intros nw T B.
  assert (E2 : w2Z (wsub nw wone) = w2Z nw - 1).
  { rewrite wsub_ok, (w2Z_nowt nw T). change (w2Z wone) with 1. pose proof (int_range (wl nw)). unfold two64, two63 in *. rewrite Z.mod_small; lia. }
  pose proof (w2Z_wt (wsub nw wone)) as WT. rewrite E2, (w2Z_nowt nw T) in WT. pose proof (int_range (wl nw)) as R.
  assert (T' : wt (wsub nw wone) = false) by (rewrite WT; apply Z.leb_gt; unfold two63 in *; lia).
  split; [exact T'|]. pose proof (w2Z_nowt _ T') as E3. rewrite E2, (w2Z_nowt nw T) in E3. lia.
Qed.

Lemma nonstack_windows_firstn : forall m ws, nonstack_windows m (firstn (3 * m) ws) = nonstack_windows m ws.
Proof.
  induction m as [|m IH]; intros ws; [reflexivity|].
  replace (3 * S m)%nat with (S (S (S (3 * m)))) by lia.
  destruct ws as [|a [|b [|c ws']]]; cbn [firstn nonstack_windows]; try reflexivity; try (destruct c; reflexivity).
  rewrite IH. reflexivity.
Qed.

Lemma wins_of_prefix : forall E0 m ws t, (3 * m <= length ws)%nat -> wins_of E0 m (ws ++ t) = wins_of E0 m ws.
Proof.
  intros E0 m. induction m as [|m IH]; intros ws t L; [reflexivity|].
  destruct ws as [|a [|b [|c ws']]]; cbn [length] in L; try lia. cbn [app]. rewrite !wins_of_cons, IH by lia. reflexivity.
Qed.

Lemma del_window_sub : forall m ws lo ws' x, del_window m ws lo = Some ws' -> In x ws' -> In x ws.
Proof.
  induction m as [|m IH]; intros ws lo ws' x H Hin; [cbn in H; destruct ws; discriminate|].
  destruct ws as [|a [|b [|c ws0]]]; try (cbn in H; discriminate). cbn [del_window] in H.
  destruct (sv_eqb a lo && sv_eqb c (VL CtrLib.K_BLOCK)).
  - apply Some_inj in H. subst ws'. do 3 right. exact Hin.
  - destruct (del_window m ws0 lo) as [ws''|] eqn:D; [|discriminate]. apply Some_inj in H. subst ws'.
    destruct Hin as [Hin|[Hin|[Hin|Hin]]]; [left| right; left| right; right; left| do 3 right; eapply IH; eauto]; assumption.
Qed.

Lemma del_window_split : forall E0 m ws kf ws' wl, del_window m ws (VP kf wzero) = Some ws' -> nonstack_windows m ws = Some wl ->
  (3 * m <= length ws)%nat ->
  exists l1 len l2, In (kf, len, CtrLib.K_BLOCK) wl
    /\ wins_of E0 m ws = l1 ++ Win (bv_unsigned (ev E0 kf)) (bv_unsigned (den E0 len)) K_BLOCK :: l2
    /\ wins_of E0 (pred m) ws' = l1 ++ l2 /\ length ws' = (length ws - 3)%nat /\ (1 <= m)%nat.
Proof.
  intros E0 m. induction m as [|m IH]; intros ws kf ws' wl H N L; [cbn in H; destruct ws; discriminate|].
  destruct ws as [|wlo [|ln [|kdv ws0]]]; try (cbn in H; discriminate). cbn [del_window] in H. cbn [nonstack_windows] in N. cbn [length] in L |- *.
  destruct kdv as [kw| | | | | | | | | |]; try discriminate.
  destruct (nonstack_windows m ws0) as [l|] eqn:NW; [|discriminate].
  destruct (sv_eqb wlo (VP kf wzero) && sv_eqb (VL kw) (VL CtrLib.K_BLOCK)) eqn:C.
  - apply Some_inj in H. subst ws'. apply andb_prop in C as [C1 C2]. apply sv_eqb_eq in C1. apply sv_eqb_eq in C2. injection C2 as ->. subst wlo.
    destruct (weqb CtrLib.K_BLOCK wzero) eqn:KZ; [apply weqb_eq in KZ; discriminate KZ|].
    rewrite weqb_refl in N. cbn [andb negb] in N.
    destruct (PrimInt63.eqb kf 0); [discriminate|]. destruct (PrimInt63.eqb kf STACK_ID); [discriminate|]. apply Some_inj in N. subst wl.
    exists [], ln, (wins_of E0 m ws0). split; [left; reflexivity|]. rewrite wins_of_cons, den_VPz, unsigned_VL. cbn [app pred].
    repeat split; try reflexivity; lia.
  - destruct (del_window m ws0 (VP kf wzero)) as [ws''|] eqn:D; [|discriminate]. apply Some_inj in H. subst ws'.
    assert (REC : forall l0, (forall x, In x l -> In x l0) -> nonstack_windows m ws0 = Some l ->
              exists l1 len l2, In (kf, len, CtrLib.K_BLOCK) l0
                /\ wins_of E0 (S m) (wlo :: ln :: VL kw :: ws0) = l1 ++ Win (bv_unsigned (ev E0 kf)) (bv_unsigned (den E0 len)) K_BLOCK :: l2
                /\ wins_of E0 m (wlo :: ln :: VL kw :: ws'') = l1 ++ l2 /\ length (wlo :: ln :: VL kw :: ws'') = (length ws0 + 3 - 3)%nat /\ (1 <= S m)%nat).
    { intros l0 SUB NW'. destruct (IH ws0 kf ws'' l D NW' ltac:(lia)) as (l1 & len & l2 & I & W1 & W2 & LEN & M1).
      exists (Win (bv_unsigned (den E0 wlo)) (bv_unsigned (den E0 ln)) (bv_unsigned (den E0 (VL kw))) :: l1), len, l2.
      split; [apply SUB; exact I|]. rewrite wins_of_cons, W1. cbn [app]. split; [reflexivity|].
      destruct m as [|m']; [lia|]. cbn [pred] in W2. rewrite wins_of_cons, W2. cbn [length]. repeat split; try reflexivity; lia. }
    cbn [pred]. replace (S (S (S (length ws0))) - 3)%nat with (length ws0 + 3 - 3)%nat by lia.
    destruct (weqb kw wzero).
    + apply Some_inj in N. subst wl. apply (REC l); [auto| exact NW].
    + destruct wlo as [|k0 o0| | | | | | | | |]; try discriminate.
      destruct (weqb o0 wzero && negb (PrimInt63.eqb k0 0) && negb (PrimInt63.eqb k0 STACK_ID)); [|discriminate].
      apply Some_inj in N. subst wl. apply (REC _); [intros x Hx; right; exact Hx| exact NW].
Qed.

Lemma perm_remove : forall (x : iv) l l', Permutation l l' -> Permutation (remove iv_eq_dec x l) (remove iv_eq_dec x l').
Proof.
  intros x l l' P. induction P as [| y l l' P IH | y z l | l l' l'' P1 IH1 P2 IH2].
  - constructor.
  - cbn [remove]. destruct (iv_eq_dec x y); [exact IH| apply perm_skip; exact IH].
  - cbn [remove]. destruct (iv_eq_dec x z), (iv_eq_dec x y); try apply Permutation_refl; try apply perm_swap; apply perm_skip; apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

Lemma block_windows_In : forall l k len, In (k, len) (block_windows l) -> In (k, len, CtrLib.K_BLOCK) l.
Proof.
  intros l. induction l as [|[[k0 len0] kd0] l IH]; intros k len H; [destruct H|]. cbn [block_windows] in H.
  destruct (weqb kd0 CtrLib.K_BLOCK) eqn:Q.
  - apply weqb_eq in Q. subst kd0. destruct H as [H|H]; [injection H as -> ->; left; reflexivity| right; apply IH; exact H].
  - right. apply IH. exact H.
Qed.

Lemma bufsz_pos : forall k, 0 < bufsz k.
Proof. intros k. unfold bufsz, BUF0. apply Z.mul_pos_pos; [lia|]. apply Z.pow_pos_nonneg; lia. Qed.
Lemma bufsz_S : forall k, bufsz (S k) = 2 * bufsz k.
Proof. intros k. unfold bufsz. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. Qed.
Lemma bufsz_le_10 : forall k, bufsz k <= 2 ^ 26 -> (k <= 10)%nat.
Proof.
  intros k H. destruct (Nat.le_gt_cases k 10) as [L|G]; [exact L|]. exfalso. unfold bufsz, BUF0 in H.
  assert (2 ^ 11 <= 2 ^ Z.of_nat k) by (apply Z.pow_le_mono_r; lia). change (2 ^ 26) with (65536 * 2 ^ 10) in H.
  assert (2 ^ 10 < 2 ^ 11) by (apply Z.pow_lt_mono_r; lia). nia.
Qed.

Lemma In_lb_remove : forall p0 L b, In b (lb_remove p0 L) <-> In b L /\ blk_id b <> p0.
Proof.
  intros p0 L b. induction L as [|x L IH].
  - cbn. tauto.
  - rewrite lb_remove_cons. destruct (bptr_eqb (blk_id x) p0) eqn:Q.
    + apply bptr_eqb_true in Q. rewrite IH. cbn [In]. split; [tauto|]. intros [[<-|H] N]; [congruence| auto].
    + assert (NQ : blk_id x <> p0) by (intros X; apply (proj2 (bptr_eqb_true _ _)) in X; congruence).
      cbn [In]. rewrite IH. split; [intros [<-|[H N]]; auto| intros [[<-|H] N]; auto].
Qed.

Lemma ev_above_lit : forall E0 nx Fv Gv (i : int), to_Z nx + to_Z i < wB -> ev (env_above E0 nx Fv Gv) (PrimInt63.add nx i) = Fv (to_Z i).
Proof.
  intros E0 nx Fv Gv i B. pose proof (int_range i) as R. cbn [env_above ev]. rewrite add_Z by exact B.
  destruct (Z.ltb_spec (to_Z nx + to_Z i) (to_Z nx)); [lia|]. f_equal. lia.
Qed.

Section POST.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model) (need r ksp : int) (hargs : list sv) (wnl : list (int * sv * w64)).
Variables (off : w64) (r1 : Mem.region) (n : nat) (md : w64) (A : sv) (nw : w64) (rest : list sv) (s : PState) (LBf : list block) (LB : blocks).
Hypothesis HS : St.st_ok rsegs OPS E st ms mo.
Hypothesis HPB : PB (eb E).
Hypothesis HMP : MP mo.
Hypothesis CG : callG Cw CANARY E st ms mo need r ksp hargs wnl off r1 n md A nw rest s LBf LB.

Variables (R' : bvmap 5 word) (M' : mem) (mo' : Model) (LBg : list block) (errv' : word).
Let base : Z := bv_unsigned (ev E STACK_ID).
Let sp : Z := base + keyZ ksp.
Let lo : Z := base + loZ r1.
Hypothesis GP : gpost (ms_regs ms) (ms_mem ms) mo LBg lo sp R' M' mo'.
Hypothesis HLBg : forall b, In b LBg -> In b LBf.
Hypothesis ERR' : rw_cells rsegs M' RERRNO [C4 errv'].
Hypothesis PUBS' : PUBS M'.

Variables (Fv : Z -> word) (Gv : Z -> Z -> byte).
Definition E' : env := env_above E (s_next st) Fv Gv.
Hypothesis HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x).
Hypothesis HF15 : Fv 15 = errv'.
Definition ms' : machine_state := MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None M' (seg_rom rsegs).
Variable st4 : sstate.
Hypothesis H4 : alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp = Some st4.

Lemma EXT : env_ext (s_next st) E E'.
Proof. apply env_above_ext. Qed.

Lemma NX : st_vars_below (s_next st) st = true /\ 0 < to_Z (s_next st) /\ to_Z (s_next st) + 256 <= 2 ^ 62.
Proof. apply fresh_ok_inv. exact (cg_fresh CG). Qed.

Lemma SVB_parts :
  rf_allb (sv_vars_below (s_next st)) (s_rf st) = true /\ rf_allb (sv_vars_below (s_next st)) (s_ff st) = true
  /\ resv_vars_below (s_next st) (s_resv st) = true
  /\ IMap.forallb (fun k r => PrimInt63.ltb k (s_next st) && region_vars_below (s_next st) r) (s_regs st) = true
  /\ forallb (fact_vars_below (s_next st)) (s_facts st) = true
  /\ forallb (fun o => forallb (sv_vars_below (s_next st)) (op_args o)) (s_ops st) = true.
Proof.
  destruct NX as (SVB & _). unfold st_vars_below in SVB.
  apply andb_prop in SVB as [SVB H6]. apply andb_prop in SVB as [SVB H5]. apply andb_prop in SVB as [SVB H4'].
  apply andb_prop in SVB as [SVB H3]. apply andb_prop in SVB as [H1 H2]. repeat split; assumption.
Qed.

Lemma HS' : St.st_ok rsegs OPS E' st ms mo.
Proof. destruct NX as (SVB & POS & _). exact (st_ok_reval rsegs OPS (s_next st) E E' EXT st ms mo POS SVB HS). Qed.

Lemma den_E' : forall v, sv_vars_below (s_next st) v = true -> den E' v = den E v.
Proof. intros v Hv. exact (den_reval (s_next st) E E' EXT v Hv). Qed.

Lemma ev_E'_below : forall k, to_Z k < to_Z (s_next st) -> ev E' k = ev E k.
Proof. intros k Hk. unfold E'. apply ev_below. exact Hk. Qed.

Lemma ev_E'_fresh : forall i, (i <= 200)%nat -> ev E' (addn (s_next st) i) = Fv (Z.of_nat i).
Proof.
  intros i Hi. destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  assert (EA : to_Z (addn (s_next st) i) = to_Z (s_next st) + Z.of_nat i) by (apply addn_Z; rewrite wB_two63, two63_eq; lia).
  unfold E'. rewrite ev_above by (rewrite EA; lia). rewrite EA. f_equal. lia.
Qed.

Lemma ST4 : exists r0, IMap.find 0%uint63 (s_regs st) = Some r0 /\ st4 = alloc_post_mk ERRNO LIBC GOT GUARD CANARY st r ksp r0 r1.
Proof. apply alloc_post_inv; [exact (cg_r1 CG) | exact H4]. Qed.

Lemma post_regs : forall v, den E' v = PropExec.getr R' 10%bv ->
  forall x, rget (Core R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None) (reg_of_r5 x)
            = den E' (rf_get (rf_set (s_rf (clobber st)) X10 v) x).
Proof.
  intros v Hv x. rewrite rget_core_getr.
  destruct (r5_eqb x X10) eqn:Q10.
  { apply r5_eqb_spec in Q10. subst x. rewrite rf_get_set_same. symmetry. exact Hv. }
  assert (N10 : x <> X10) by (intros ->; rewrite r5_eqb_refl in Q10; discriminate).
  rewrite rf_get_set_other by (intros Q; apply N10; symmetry; exact Q).
  change (rf_get (s_rf (clobber st)) x) with (getr (clobber st) x). rewrite getr_clobber.
  destruct (clob_pos x) as [i|] eqn:CP.
  - rewrite <- (HF x i CP). cbn [den]. rewrite ev_E'_fresh; [| destruct x; cbn in CP; try discriminate; injection CP as <-; lia].
    apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned, w2Z_wzero, Z.add_0_r. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
  - destruct (r5_eqb x X0) eqn:Q0.
    + apply r5_eqb_spec in Q0. subst x. rewrite getr_x0. change (getr st X0) with (rf_get (s_rf st) X0).
      rewrite (so_x0 _ _ _ _ _ _ HS'). rewrite den_VL. reflexivity.
    + assert (N0 : x <> X0) by (intros ->; rewrite r5_eqb_refl in Q0; discriminate).
      pose proof (gp_regs _ _ _ _ _ _ _ _ _ GP (reg_of_r5 x) (kept_or_clobbered x N0 N10 CP)) as K. rewrite K.
        rewrite (cg_regs CG x).
        symmetry. apply den_E'. destruct SVB_parts as (SVB & _). exact (rf_allb_get _ _ _ SVB x).
Qed.

Lemma reg_E' : forall k rg, IMap.find k (s_regs st) = Some rg ->
  ev E' k = ev E k /\ hiZ E' rg = hiZ E rg /\ PrimInt63.ltb k (s_next st) = true /\ region_vars_below (s_next st) rg = true.
Proof.
  intros k rg Hk. destruct SVB_parts as (_ & _ & _ & HR & _). exact (regs_reval_find (s_next st) E E' EXT _ k rg (so_bst _ _ _ _ _ _ HS) HR Hk).
Qed.

Lemma ev1_E' : ev E' STACK_ID = ev E STACK_ID.
Proof. destruct (reg_E' _ _ (cg_r1 CG)) as (X & _). exact X. Qed.

Lemma SP_R : bv_unsigned (PropExec.getr (ms_regs ms) 2%bv) = sp.
Proof. exact (cg_sp CG). Qed.

Lemma PRES : rheap_pres LBg sp (ms_mem ms) M'.
Proof. rewrite <- SP_R. exact (gp_pres _ _ _ _ _ _ _ _ _ GP). Qed.

Lemma STK' : stk rsegs M' lo sp.
Proof. rewrite <- SP_R. exact (gp_stk _ _ _ _ _ _ _ _ _ GP). Qed.

Lemma client_byte : forall a, 0 <= a < 2 ^ 64 -> rclient_addr LBg sp a ->
  M' (wa a) = ms_mem ms (wa a) /\ rb rsegs M' a = rb rsegs (ms_mem ms) a /\ (wb rsegs (ms_mem ms) a = true -> wb rsegs M' a = true).
Proof.
  intros a Ha HC. destruct (PRES a Ha HC) as [E1 W1]. split; [exact E1|]. split.
  - unfold rb. unfold wa in E1. rewrite E1. reflexivity.
  - intros W. apply wb_wview. apply W1. apply wb_wview. exact W.
Qed.

Lemma old_region_ok : forall k rg, IMap.find k (s_regs st) = Some rg -> PrimInt63.eqb k 0%uint63 = false ->
  (forall a, bv_unsigned (ev E k) + loZ rg <= a < bv_unsigned (ev E k) + hiZ E rg -> rclient_addr LBg sp a) ->
  St.region_ok rsegs (s_priv st) E' M' k rg.
Proof.
  intros k rg Hk K CL. pose proof (so_reg _ _ _ _ _ _ HS' k rg Hk) as RO. destruct (reg_E' k rg Hk) as (Ek & Eh & _).
  apply (region_ok_frame rsegs (s_priv st) E' (ms_mem ms) M' k rg (so_zero _ _ _ _ _ _ HS') RO).
  intros a Ha R _. rewrite Ek, Eh in R. destruct (client_byte a ltac:(unfold two64 in Ha; lia) (CL a (R K))) as (E1 & _). unfold wa in E1. exact E1.
Qed.

Lemma r1_ok : St.region_ok rsegs (s_priv st) E' M' STACK_ID (forget_r1 r1 ksp).
Proof.
  pose proof (cg_r1 CG) as Hr1. pose proof (cg_r1w CG) as HW. pose proof (cg_r1bg CG) as HBG. pose proof (cg_ksp CG) as Hksp.
  pose proof (cg_ksp16 CG) as K16. pose proof (cg_kspneg CG) as KNEG. pose proof (cg_lo0 CG) as LO0. pose proof (cg_room CG) as ROOM. pose proof (cg_hi CG) as HI.
  pose proof (so_reg _ _ _ _ _ _ HS' STACK_ID r1 Hr1) as RO.
  destruct (region_forget_sound rsegs (s_priv st) E' (ms_mem ms) STACK_ID r1 (Mem.granule (Mem.rg_lo r1)) (Mem.granule ksp) RO) as (RO' & Elo & Ehi & Ew & Ebg).
  fold (forget_r1 r1 ksp) in RO', Elo, Ehi, Ew, Ebg.
  destruct (reg_E' STACK_ID r1 Hr1) as (Ek & Eh & _).
  assert (LH : loZ (forget_r1 r1 ksp) = loZ r1 /\ hiZ E' (forget_r1 r1 ksp) = hiZ E r1).
  { unfold loZ, hiZ. rewrite Elo, Ehi. fold (hiZ E' r1). rewrite Eh. auto. }
  destruct LH as [Lq Hq].
  pose proof (okey_sound _ _ Hksp) as [_ Rksp]. rewrite half63 in Rksp.
  pose proof (int_range need) as Rn.
  apply (region_ok_fine_frame rsegs (s_priv st) E' (ms_mem ms) M' STACK_ID (forget_r1 r1 ksp) (so_zero _ _ _ _ _ _ HS') RO').
  - intros o R1 _ CL. specialize (R1 eq_refl). rewrite Lq, Hq in R1. rewrite Ek.
    destruct CL as [(g & gr & c & Hg & Hc & Eg & COV) | [U BG]].
    +
      unfold forget_r1, Mem.region_forget in Hg. rewrite HBG in Hg. cbn [Mem.is_bgnone Mem.rg_cells] in Hg.
      rewrite IMap.find_remove_range in Hg by exact (ro_bst _ _ _ _ _ _ RO).
      destruct (PrimInt63.leb (Mem.granule (Mem.rg_lo r1)) g && PrimInt63.ltb g (Mem.granule ksp))%bool eqn:RNG; [discriminate|].
      assert (LE : keyZ ksp <= o).
      { pose proof (keyZ_range (Mem.rg_lo r1)) as Rlo. pose proof (keyZ_range ksp) as Rk.
        destruct (granule_gidx (Mem.rg_lo r1) (key_range_half _)) as [Glo Ilo].
        destruct (granule_gidx ksp (key_range_half _)) as [Gk Ik].
        destruct (gidx_ok ksp) as [Gm _].
        assert (G0 : to_Z (Mem.gidx ksp) = 0).
        { rewrite Gm. destruct (keyZ_cases ksp) as [[_ EK]|[_ EK]]; rewrite EK in K16.
          - apply Z.mod_divide in K16; [|lia]. apply Z.mod_divide; [lia|]. destruct K16 as [q Qq]. exists (2 * q). lia.
          - replace (to_Z ksp - 2 ^ 63) with (to_Z ksp + (- 2 ^ 59) * 16) in K16 by lia. rewrite Z.mod_add in K16 by lia.
            apply Z.mod_divide in K16; [|lia]. apply Z.mod_divide; [lia|]. destruct K16 as [q Qq]. exists (2 * q). lia. }
        pose proof (Z.div_mod o 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound o 8 ltac:(lia)) as MB.
        unfold loZ in R1, ROOM, LO0.
        destruct (keyZ_cases g) as [[Rg Egk]|[Rg Egk]]; [lia|].
        destruct (keyZ_cases (Mem.granule (Mem.rg_lo r1))) as [[R2 E2]|[R2 E2]]; [lia|].
        destruct (keyZ_cases (Mem.granule ksp)) as [[R3 E3]|[R3 E3]]; [lia|].
        apply andb_false_iff in RNG. destruct RNG as [RNG|RNG].
        - destruct (lebP (Mem.granule (Mem.rg_lo r1)) g) as [X|X]; [rewrite RNG in *; discriminate || lia|]. lia.
        - destruct (ltbP g (Mem.granule ksp)) as [X|X]; [rewrite RNG in *; discriminate || lia|]. lia. }
      destruct (client_byte (bv_unsigned (ev E STACK_ID) + o) ltac:(unfold loZ in *; lia) ltac:(left; unfold sp, base; lia)) as (_ & E2 & _).
      exact E2.
    + exfalso. apply BG. unfold bg_byte. rewrite Ebg, HBG. reflexivity.
  - intros _ a Ha. rewrite Ek, Lq, Hq in Ha.
    destruct (Z_lt_le_dec a sp) as [LT|GE].
    + destruct STK' as (_ & _ & ST). destruct (ST a ltac:(unfold lo, sp in *; lia)) as [W [b Hb]].
      split; [rewrite rb_mrd, Hb; discriminate|]. intros _. apply wb_wview. exact W.
    + destruct (ro_valid _ _ _ _ _ _ RO eq_refl a ltac:(rewrite Ek, Eh; exact Ha)) as (V1 & V2 & _).
      destruct (client_byte a ltac:(lia) ltac:(left; lia)) as (_ & E2 & W2).
      split; [rewrite E2; exact V1|]. intros Wr. apply W2. apply V2. rewrite <- Ew. exact Wr.
Qed.

Lemma windows_off_image : forall a, RIMG_LO <= a < RIMG_HI -> ~ in_ws (wins_of E n rest) a.
Proof.
  intros a Ha IN. pose proof (cg_perm CG) as PERM. pose proof (cg_rheap CG) as RH. pose proof (cg_wf CG) as WF.
  apply RHEAP_split in RH as [RC _].
  unfold in_ws in IN. apply in_ivs_In in IN as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
  pose proof (proj1 (Forall_forall _ _) WF w Hw) as (W1 & W2 & W3 & [[K CE]|[[K B]|[K (b & Hb & SUB)]]]).
  - unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. pose_ceil. unfold CEIL_MIN, RIMG_HI in *. lia.
  - assert (Hb' : In (w_iv w) (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact B]).
    apply in_map_iff in Hb' as (blk & Eb & Hblk).
    destruct (RHEAP_core_block_range s LBf (ms_mem ms) blk RC Hblk) as (_ & _ & _ & B4 & _).
    unfold in_iv in Hin. rewrite <- Eb in Hin. cbn [fst snd] in Hin. unfold RIMG_LO, RIMG_HI in *. lia.
  - assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]).
    apply in_map_iff in Hb' as (blk & Eb & Hblk).
    destruct (RHEAP_core_block_range s LBf (ms_mem ms) blk RC Hblk) as (_ & _ & _ & B4 & _).
    specialize (SUB a Hin). unfold in_iv in SUB. rewrite <- Eb in SUB. cbn [fst snd] in SUB. unfold RIMG_LO, RIMG_HI in *. lia.
Qed.

Lemma heap_priv : forall a, RMLOCK <= a < RCTX + 936 -> in_priv (s_priv st) a.
Proof.
  intros a Ha. pose proof (cg_find CG) as Hf. pose proof (cg_decode CG) as D.
  assert (IMG : RIMG_LO <= a < RIMG_HI) by (unfold RMLOCK, RCTX, RIMG_LO, RIMG_HI in *; lia).
  apply (ops_apart_find rsegs OPS E (s_ops st) (s_regs st) (s_priv st) HEAP_ID hargs a (so_apart _ _ _ _ _ _ HS) Hf).
  - rewrite OPS_fp1. apply (proj2 (fp_spec IMGX _ _ _ _ _ a D)). split; [unfold RIMG_LO, RIMG_HI, two64 in *; lia|]. split.
    + intros I. apply in_IMGX in I. destruct I as [_ I2]. exact (I2 Ha).
    + apply windows_off_image. exact IMG.
  - apply hi_seg. unfold RMLOCK, RCTX in Ha. lia.
Qed.

Definition e15 : int := PrimInt63.add (s_next st) 15%uint63.
Lemma e15_addn : e15 = addn (s_next st) 15.
Proof.
  destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  unfold e15. symmetry. apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma ev_e15 : ev E' e15 = errv'.
Proof. rewrite e15_addn, ev_E'_fresh by lia. exact HF15. Qed.

Definition Me : mem := write_to_mem (ms_mem ms) (Z_to_bv 64 RERRNO) (store_bytes 4%uint63 errv').

Lemma can_write_abs : forall q a w, Mem.abs_writable rsegs (to_Z a) (to_Z w) = true -> PrimInt63.ltb a bit62i = true ->
  in_priv_b (s_priv st) a w = false -> can_write rsegs (s_facts st) (s_priv st) 0%uint63 q a w = true.
Proof. intros q a w H1 H2 H3. unfold can_write. rewrite Uint63.eqb_refl, H2, H1, H3. reflexivity. Qed.

Lemma statics_priv :
  in_priv_b (s_priv st) (PrimInt63.add LIBC 3%uint63) 1%uint63 = false /\ in_priv_b (s_priv st) (PrimInt63.add LIBC 48%uint63) 8%uint63 = false
  /\ in_priv_b (s_priv st) (PrimInt63.add LIBC 8%uint63) 8%uint63 = false /\ in_priv_b (s_priv st) GOT 8%uint63 = false
  /\ in_priv_b (s_priv st) GUARD 8%uint63 = false /\ in_priv_b (s_priv st) ERRNO 4%uint63 = false.
Proof.
  pose proof (cg_statics CG) as H. unfold statics_ok in H.
  apply andb_prop in H as [H Q6]. apply andb_prop in H as [H Q5]. apply andb_prop in H as [H Q4].
  apply andb_prop in H as [H Q3]. apply andb_prop in H as [Q1 Q2].
  apply is_litv_inv in Q1. apply is_litv_inv in Q2. apply is_sv_inv in Q3. apply is_litv_inv in Q4. apply is_sv_inv in Q5.
  destruct (aload rsegs st ERRNO 4%uint63) as [ve|] eqn:Q6'; [|discriminate].
  repeat split; eapply aload_priv; eassumption.
Qed.

Lemma claimed_dirty_r0 : forall r0 o, IMap.bst (Mem.rg_cells r0) -> 0 <= o < 2 ^ 62 ->
  claimed rsegs E' 0%uint63 (dirty_r0 LIBC r0) o -> ~ (RLIBC <= o < RLIBC + 112).
Proof.
  intros r0 o B Ho CL IN.
  destruct (dirty_range_spec (Mem.granule LIBC) LIBC_GRANS (Mem.rg_cells r0) B ltac:(rewrite wB_two63; vm_compute; reflexivity)) as [B' F].
  assert (Q : RLIBC = 8 * to_Z (Mem.granule LIBC)) by (vm_compute; reflexivity).
  set (gL := to_Z (Mem.granule LIBC)) in *.
  pose proof (Z.div_mod o 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound o 8 ltac:(lia)) as MB.
  destruct CL as [(g & gr & c & Hg & Hc & Eg & COV) | [U BG]].
  - cbn [dirty_r0 Mem.rg_cells] in Hg. rewrite F in Hg.
    destruct (keyZ_cases g) as [[Rg Ek]|[Rg Ek]]; [| lia].
    destruct (Z.leb_spec gL (to_Z g)), (Z.ltb_spec (to_Z g) (gL + Z.of_nat LIBC_GRANS)); cbn [andb] in Hg;
      try (injection Hg as <-; destruct Hc); unfold LIBC_GRANS in *; lia.
  -
    set (g := of_Z (o / 8)).
    assert (Tg : to_Z g = o / 8). { subst g. rewrite of_Z_spec. apply Z.mod_small. rewrite wB_two63, two63_eq. lia. }
    assert (Kg : keyZ g = o / 8). { destruct (keyZ_cases g) as [[_ ->]|[R _]]; lia. }
    specialize (U g (Mem.Gran true []) Kg). cbn [dirty_r0 Mem.rg_cells] in U. rewrite F, Tg in U.
    destruct (Z.leb_spec gL (o / 8)), (Z.ltb_spec (o / 8) (gL + Z.of_nat LIBC_GRANS)); cbn [andb] in U; unfold LIBC_GRANS in *; try lia.
    destruct (U eq_refl) as [D _]. discriminate D.
Qed.

Lemma r0_agree : forall o seg, 0 <= o < 2 ^ 62 -> find_segment rsegs o 1 = Some seg -> ~ in_priv (s_priv st) o ->
  ~ (RLIBC <= o < RLIBC + 112) -> ~ (RERRNO <= o < RERRNO + 4) -> rb rsegs M' o = rb rsegs (ms_mem ms) o.
Proof.
  intros o seg Ho Hseg NP NL NE.
  pose proof (cg_minv CG) as MINV. pose proof (gp_minv _ _ _ _ _ _ _ _ _ GP) as MINV'.
  pose proof (cg_pubs CG) as (PU1 & PU2 & PU3 & PU4). pose proof PUBS' as (PV1 & PV2 & PV3 & PV4).
  destruct (seg_writable seg) eqn:W.
  - pose proof (rw_seg_range o seg Hseg W) as RW.
    assert (STATIC : forall lo, lo <= o < lo + 8 ->
              rw_cells rsegs (ms_mem ms) lo [C8 (wz match lo with _ => 0 end)] -> True) by (intros; exact I). clear STATIC.
    destruct (Z_lt_le_dec o RSSP_GUARD) as [G1|G1]; [| destruct (Z_lt_le_dec o (RSSP_GUARD + 8)) as [G2|G2]].
    all: destruct (Z_lt_le_dec o RGOT_SSP) as [T1|T1]; [| destruct (Z_lt_le_dec o (RGOT_SSP + 8)) as [T2|T2]].
    all: destruct (Z_lt_le_dec o RMLOCK) as [L1|L1]; [| destruct (Z_lt_le_dec o (RCTX + 936)) as [L2|L2]].
    all: first
      [
        replace o with (RSSP_GUARD + Z.of_nat (Z.to_nat (o - RSSP_GUARD))) by lia;
        rewrite (rw_cell_rb (ms_mem ms) RSSP_GUARD (C8 (wz ssp_canary)) _ PU4) by (cbn [cbytes]; rewrite length_le8; lia);
        rewrite (rw_cell_rb M' RSSP_GUARD (C8 (wz ssp_canary)) _ PV4) by (cbn [cbytes]; rewrite length_le8; lia); reflexivity
      |
        replace o with (RGOT_SSP + Z.of_nat (Z.to_nat (o - RGOT_SSP))) by lia;
        rewrite (rw_cell_rb (ms_mem ms) RGOT_SSP (C8 (wz RSSP_GUARD)) _ PU3) by (cbn [cbytes]; rewrite length_le8; lia);
        rewrite (rw_cell_rb M' RGOT_SSP (C8 (wz RSSP_GUARD)) _ PV3) by (cbn [cbytes]; rewrite length_le8; lia); reflexivity
      |
        exfalso; apply NP; apply heap_priv; lia
      |
        destruct (client_byte o ltac:(lia) ltac:(right; left; unfold ralloc_static; unfold RLIBC, RCTX, RMLOCK, RERRNO, RSSP_GUARD, RGOT_SSP in *; lia)) as (_ & E2 & _); exact E2 ].
  - assert (N1 : ms_mem ms (wa o) = None).
    { destruct (ms_mem ms (wa o)) as [b|] eqn:Hb; [|reflexivity]. exfalso. pose proof (MINV _ _ Hb) as X. unfold ro_addr in X.
      unfold wa in X. rewrite Z_to_bv_unsigned, bv_wrap_small in X by (rewrite bv_modulus_64; unfold W64.two64; lia). rewrite Hseg, W in X. discriminate X. }
    assert (N2 : M' (wa o) = None).
    { destruct (M' (wa o)) as [b|] eqn:Hb; [|reflexivity]. exfalso. pose proof (MINV' _ _ Hb) as X. unfold ro_addr in X.
      unfold wa in X. rewrite Z_to_bv_unsigned, bv_wrap_small in X by (rewrite bv_modulus_64; unfold W64.two64; lia). rewrite Hseg, W in X. discriminate X. }
    unfold rb. unfold wa in N1, N2. rewrite N1, N2. reflexivity.
Qed.

Lemma r0_ok : forall r0, IMap.find 0%uint63 (s_regs st) = Some r0 ->
  St.region_ok rsegs (s_priv st) E' M' 0%uint63 (havoc_r0 ERRNO LIBC GOT GUARD CANARY r0 e15).
Proof.
  intros r0 Hr0.
  pose proof (cg_pubs CG) as PU. pose proof (cg_auxcell CG) as AC. destruct (cg_r3 CG) as [r3 Hr3]. destruct (cg_errno CG) as [errv ERR].
  destruct statics_priv as (P1 & P2 & P3 & P4 & P5 & P6).
  pose proof (so_zero _ _ _ _ _ _ HS') as Hz. pose proof (so_facts _ _ _ _ _ _ HS') as Hfs.
  pose proof (so_reg _ _ _ _ _ _ HS' 0%uint63 r0 Hr0) as RO0.

  pose proof (region_dirty_sound rsegs (s_priv st) E' (ms_mem ms) 0%uint63 r0 (Mem.granule LIBC) LIBC_GRANS
                ltac:(rewrite wB_two63; vm_compute; reflexivity) RO0) as RO1.
  change (St.region_ok rsegs (s_priv st) E' (ms_mem ms) 0%uint63 (dirty_r0 LIBC r0)) in RO1.

  set (Mh := write_to_mem M' (Z_to_bv 64 RERRNO) (le4 errv)).
  assert (FRh : forall a, 0 <= a < two64 -> ~ (RERRNO <= a < RERRNO + 4) -> Mh (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
  { intros a Ha Na. subst Mh. apply write_to_mem_frame; rewrite ?length_le4; unfold RERRNO, two64 in *; lia. }
  assert (INh : forall i, 0 <= i < 4 -> Mh (Z_to_bv 64 (RERRNO + i)) = nth_error (le4 errv) (Z.to_nat i)).
  { intros i Hi. subst Mh. apply write_to_mem_in; rewrite ?length_le4; unfold RERRNO, two64; lia. }
  assert (RO1h : St.region_ok rsegs (s_priv st) E' Mh 0%uint63 (dirty_r0 LIBC r0)).
  { apply (region_ok_fine_frame rsegs (s_priv st) E' (ms_mem ms) Mh 0%uint63 (dirty_r0 LIBC r0) Hz RO1); [| intros K; discriminate K].
    intros o _ H2 CL. destruct (H2 eq_refl) as (Ro & [seg Hseg] & NP). rewrite (ev0_zero E' Hz), Z.add_0_l. rewrite half63 in Ro.
    pose proof (claimed_dirty_r0 r0 o (ro_bst _ _ _ _ _ _ RO0) Ro CL) as NL.
    destruct (Z_lt_le_dec o RERRNO) as [E1|E1]; [| destruct (Z_lt_le_dec o (RERRNO + 4)) as [E2|E2]].
    2:{ unfold rb at 1. replace (Mh (Z_to_bv 64 o)) with (Mh (Z_to_bv 64 (RERRNO + (o - RERRNO)))) by (f_equal; f_equal; lia). rewrite INh by lia.
        replace o with (RERRNO + Z.of_nat (Z.to_nat (o - RERRNO))) at 2 by lia.
        rewrite (rw_cell_rb (ms_mem ms) RERRNO (C4 errv) _ ERR) by (cbn [cbytes]; rewrite length_le4; lia).
        cbn [cbytes]. destruct (nth_error (le4 errv) (Z.to_nat (o - RERRNO))) eqn:X; [reflexivity|].
        apply nth_error_None in X. rewrite length_le4 in X. lia. }
    all: unfold rb at 1; rewrite FRh by (unfold two64; lia); fold (rb rsegs M' o); apply (r0_agree o seg); try assumption; lia. }

  destruct (region_store_sound rsegs (s_priv st) E' Mh (s_facts st) 0%uint63 (dirty_r0 LIBC r0) ERRNO 4%uint63 (VP e15 wzero)
              Hfs Hz RO1h wok4 (can_write_abs (dirty_r0 LIBC r0) ERRNO 4%uint63 wr_ERRNO eq_refl P6)) as (_ & RO2 & Elo2 & Ehi2 & Ew2 & Ebg2 & FR2).
  cbv zeta in RO2, FR2. unfold addrZ in RO2, FR2. rewrite (ev0_zero E' Hz), Z.add_0_l in RO2, FR2.
  change (keyZ ERRNO) with RERRNO in RO2, FR2. change (to_Z 4%uint63) with 4 in FR2.
  replace (den E' (VP e15 wzero)) with errv' in RO2, FR2 by (rewrite den_VPz, ev_e15; reflexivity).
  set (Mhh := write_to_mem Mh (Z_to_bv 64 RERRNO) (store_bytes 4%uint63 errv')) in *.
  assert (RO2' : St.region_ok rsegs (s_priv st) E' M' 0%uint63 (Mem.region_store (dirty_r0 LIBC r0) ERRNO 4%uint63 (VP e15 wzero))).
  { apply (region_ok_fine_frame rsegs (s_priv st) E' Mhh M' 0%uint63 _ Hz RO2); [| intros K; discriminate K].
    intros o _ H2 _. destruct (H2 eq_refl) as (Ro & _ & _). rewrite (ev0_zero E' Hz), Z.add_0_l. rewrite half63 in Ro.
    destruct (Z_lt_le_dec o RERRNO) as [E1|E1]; [| destruct (Z_lt_le_dec o (RERRNO + 4)) as [E2|E2]].
    2:{ unfold rb at 2. subst Mhh.
        replace (write_to_mem Mh (Z_to_bv 64 RERRNO) (store_bytes 4 errv') (Z_to_bv 64 o))
           with (write_to_mem Mh (Z_to_bv 64 RERRNO) (store_bytes 4 errv') (Z_to_bv 64 (RERRNO + (o - RERRNO)))) by (f_equal; f_equal; lia).
        rewrite write_to_mem_in; [| unfold RERRNO; lia| rewrite store_bytes_length; change (to_Z 4%uint63) with 4; unfold RERRNO, two64; lia
                                 | rewrite store_bytes_length; change (to_Z 4%uint63) with 4; lia].
        rewrite store_bytes_nth_error by (change (to_Z 4%uint63) with 4; lia).
        replace o with (RERRNO + Z.of_nat (Z.to_nat (o - RERRNO))) at 1 by lia.
        rewrite (rw_cell_rb M' RERRNO (C4 errv') _ ERR') by (cbn [cbytes]; rewrite length_le4; lia). cbn [cbytes].
        rewrite byte_of_le4 by lia. f_equal. f_equal. lia. }
    all: unfold rb; subst Mhh; rewrite (FR2 o) by (unfold two64; lia); rewrite FRh by (unfold two64; lia); reflexivity. }

  unfold havoc_r0, store_pubs. fold e15.
  assert (E3 : ev E' AUXV_ID = ev E AUXV_ID) by (destruct (reg_E' _ _ Hr3) as (X & _); exact X).
  pose proof PUBS' as (PV1 & PV2 & PV3 & PV4).
  pose proof (gp_auxcell _ _ _ _ _ _ _ _ _ GP) as AP.
  apply (region_store_known (s_priv st) E' M' (s_facts st) 0%uint63 _ GUARD 8%uint63 CANARY Hfs Hz);
    [| exact wok8 | apply (can_write_abs _ GUARD 8%uint63 wr_GUARD eq_refl P5) |].
  apply (region_store_known (s_priv st) E' M' (s_facts st) 0%uint63 _ GOT 8%uint63 _ Hfs Hz);
    [| exact wok8 | apply (can_write_abs _ GOT 8%uint63 wr_GOT eq_refl P4) |].
  apply (region_store_known (s_priv st) E' M' (s_facts st) 0%uint63 _ (PrimInt63.add LIBC 48%uint63) 8%uint63 _ Hfs Hz);
    [| exact wok8 | apply (can_write_abs _ (PrimInt63.add LIBC 48%uint63) 8%uint63 wr_PAGE_SIZE eq_refl P2) |].
  apply (region_store_known (s_priv st) E' M' (s_facts st) 0%uint63 _ (PrimInt63.add LIBC 8%uint63) 8%uint63 _ Hfs Hz);
    [| exact wok8 | apply (can_write_abs _ (PrimInt63.add LIBC 8%uint63) 8%uint63 wr_AUXV_CELL eq_refl P3) |].
  apply (region_store_known (s_priv st) E' M' (s_facts st) 0%uint63 _ (PrimInt63.add LIBC 3%uint63) 1%uint63 _ Hfs Hz);
    [exact RO2' | exact wok1 | apply (can_write_abs _ (PrimInt63.add LIBC 3%uint63) 1%uint63 wr_NEED_LOCKS eq_refl P1) |].
  all: intros i Hi; unfold addrZ; rewrite (ev0_zero E' Hz), Z.add_0_l.
  - change (keyZ (PrimInt63.add LIBC 3%uint63)) with RNEED_LOCKS. change (to_Z 1%uint63) with 1 in Hi.
    replace (RNEED_LOCKS + i) with (RNEED_LOCKS + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (rw_cell_rb M' RNEED_LOCKS (C1 (b8 0)) _ PV1) by (cbn; lia). replace (Z.to_nat i) with 0%nat by lia. cbn [cbytes nth_error].
    f_equal. unfold byte_of, b8. rewrite den_VL. f_equal. replace i with 0 by lia. reflexivity.
  - change (keyZ (PrimInt63.add LIBC 8%uint63)) with RAUXV_CELL. change (to_Z 8%uint63) with 8 in Hi.
    replace (RAUXV_CELL + i) with (RAUXV_CELL + Z.of_nat (Z.to_nat i)) by lia.
    assert (RBq : rb rsegs M' (RAUXV_CELL + Z.of_nat (Z.to_nat i)) = rb rsegs (ms_mem ms) (RAUXV_CELL + Z.of_nat (Z.to_nat i))).
    { unfold rb. unfold wa in AP. rewrite (AP (RAUXV_CELL + Z.of_nat (Z.to_nat i))) by lia. reflexivity. }
    rewrite RBq, (rw_cell_rb (ms_mem ms) RAUXV_CELL (C8 (ev E AUXV_ID)) _ AC) by (cbn [cbytes]; rewrite length_le8; lia). cbn [cbytes].
    rewrite byte_of_le8 by lia. rewrite den_VPz, E3. f_equal. f_equal. lia.
  - change (keyZ (PrimInt63.add LIBC 48%uint63)) with RPAGE_SIZE. change (to_Z 8%uint63) with 8 in Hi.
    replace (RPAGE_SIZE + i) with (RPAGE_SIZE + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (rw_cell_rb M' RPAGE_SIZE (C8 (wz 4096)) _ PV2) by (cbn [cbytes]; rewrite length_le8; lia). cbn [cbytes].
    rewrite byte_of_le8 by lia. rewrite den_VL. f_equal. replace (Z.of_nat (Z.to_nat i)) with i by lia. reflexivity.
  - change (keyZ GOT) with RGOT_SSP. change (to_Z 8%uint63) with 8 in Hi.
    replace (RGOT_SSP + i) with (RGOT_SSP + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (rw_cell_rb M' RGOT_SSP (C8 (wz RSSP_GUARD)) _ PV3) by (cbn [cbytes]; rewrite length_le8; lia). cbn [cbytes].
    rewrite byte_of_le8 by lia. rewrite den_VL. f_equal. replace (Z.of_nat (Z.to_nat i)) with i by lia. reflexivity.
  - change (keyZ GUARD) with RSSP_GUARD. change (to_Z 8%uint63) with 8 in Hi.
    replace (RSSP_GUARD + i) with (RSSP_GUARD + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (rw_cell_rb M' RSSP_GUARD (C8 (wz ssp_canary)) _ PV4) by (cbn [cbytes]; rewrite length_le8; lia). cbn [cbytes].
    rewrite byte_of_le8 by lia. rewrite (PB_canary E') by (unfold E'; rewrite eb_above; exact HPB).
    f_equal. replace (Z.of_nat (Z.to_nat i)) with i by lia. reflexivity.
Qed.

Definition Rg4 (r0 : Mem.region) : IMap.t Mem.region :=
  IMap.add 0%uint63 (havoc_r0 ERRNO LIBC GOT GUARD CANARY r0 e15) (IMap.add STACK_ID (forget_r1 r1 ksp) (s_regs st)).

Lemma Rg4_bst : forall r0, IMap.bst (Rg4 r0).
Proof. intros r0. unfold Rg4. apply IMap.bst_add, IMap.bst_add. exact (so_bst _ _ _ _ _ _ HS). Qed.

Lemma region_store_fields : forall q o w v,
  Mem.rg_lo (Mem.region_store q o w v) = Mem.rg_lo q /\ Mem.rg_hi (Mem.region_store q o w v) = Mem.rg_hi q
  /\ Mem.rg_w (Mem.region_store q o w v) = Mem.rg_w q /\ Mem.rg_bg (Mem.region_store q o w v) = Mem.rg_bg q.
Proof.
  intros q o w v. unfold Mem.region_store. destruct (Mem.in_granule o w).
  - apply region_store1_fields.
  - cbv zeta.
    match goal with |- context [Mem.rg_lo (Mem.region_store1 ?q2 ?o2 ?w2 ?v2)] =>
      destruct (region_store1_fields q2 o2 w2 v2) as (-> & -> & -> & ->) end.
    apply region_store1_fields.
Qed.

Lemma havoc_fields : forall r0, Mem.rg_lo (havoc_r0 ERRNO LIBC GOT GUARD CANARY r0 e15) = Mem.rg_lo r0
  /\ Mem.rg_hi (havoc_r0 ERRNO LIBC GOT GUARD CANARY r0 e15) = Mem.rg_hi r0
  /\ Mem.rg_w (havoc_r0 ERRNO LIBC GOT GUARD CANARY r0 e15) = Mem.rg_w r0.
Proof.
  intros r0. unfold havoc_r0, store_pubs.
  repeat match goal with |- context [Mem.rg_lo (Mem.region_store ?q ?o ?w ?v)] =>
    let F := fresh in pose proof (region_store_fields q o w v) as F; destruct F as (-> & -> & -> & _) end.
  cbn [dirty_r0 Mem.rg_lo Mem.rg_hi Mem.rg_w]. repeat split; reflexivity.
Qed.

Lemma Rg4_find : forall r0 k rg, IMap.find 0%uint63 (s_regs st) = Some r0 -> IMap.find k (Rg4 r0) = Some rg ->
  (k = 0%uint63 /\ rg = havoc_r0 ERRNO LIBC GOT GUARD CANARY r0 e15)
  \/ (k = STACK_ID /\ rg = forget_r1 r1 ksp)
  \/ (k <> 0%uint63 /\ k <> STACK_ID /\ IMap.find k (s_regs st) = Some rg).
Proof.
  intros r0 k rg Hr0 H. unfold Rg4 in H. pose proof (so_bst _ _ _ _ _ _ HS) as B.
  destruct (Uint63.eqb 0%uint63 k) eqn:K0.
  - apply Uint63.eqb_correct in K0. subst k. rewrite IMap.find_add_same in H by (apply IMap.bst_add; exact B). injection H as <-. left; auto.
  - apply Uint63.eqb_false_spec in K0. rewrite IMap.find_add_other in H by (try apply IMap.bst_add; assumption || exact B || auto).
    destruct (Uint63.eqb STACK_ID k) eqn:K1.
    + apply Uint63.eqb_correct in K1. subst k. rewrite IMap.find_add_same in H by exact B. injection H as <-. right; left; auto.
    + apply Uint63.eqb_false_spec in K1. rewrite IMap.find_add_other in H by (exact B || auto). right; right. repeat split; auto.
Qed.

Lemma win_lookup_In : forall l k len kd, win_lookup l k = Some (len, kd) -> In (k, len, kd) l.
Proof.
  intros l. induction l as [|[[k' len'] kd'] l IH]; intros k len kd H; cbn in H; [discriminate|].
  destruct (Uint63.eqb k' k) eqn:Q.
  - apply Uint63.eqb_correct in Q. subst k'. injection H as <- <-. left. reflexivity.
  - right. apply IH. exact H.
Qed.

Lemma nonstack_windows_In : forall E0 m ws l k len kd, nonstack_windows m ws = Some l -> In (k, len, kd) l ->
  k <> 0%uint63 /\ k <> STACK_ID /\ w2Z kd <> 0 /\
  In (Win (bv_unsigned (ev E0 k)) (bv_unsigned (den E0 len)) (w2Z kd)) (wins_of E0 m ws).
Proof.
  intros E0 m. induction m as [|m IH]; intros ws wl0 k len kd H Hin.
  - cbn in H. injection H as <-. destruct Hin.
  - destruct ws as [|wlo [|ln [|kdv ws']]]; try (cbn in H; discriminate).
    cbn [nonstack_windows] in H. destruct kdv as [kw| | | | | | | | | |]; try discriminate.
    destruct (nonstack_windows m ws') as [l|] eqn:NW; [|discriminate].
    rewrite wins_of_cons.
    destruct (weqb kw wzero) eqn:Z0.
    + injection H as <-. destruct (IH ws' l k len kd NW Hin) as (A1 & A2 & A3 & A4). repeat split; try assumption. right. exact A4.
    + destruct wlo as [|k0 o0| | | | | | | | |]; try discriminate.
      destruct (weqb o0 wzero && negb (PrimInt63.eqb k0 0) && negb (PrimInt63.eqb k0 STACK_ID)) eqn:C; [|discriminate].
      injection H as <-. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
      destruct Hin as [Hin|Hin].
      * injection Hin as -> -> ->. apply weqb_eq in C1. subst o0.
        split; [intros ->; discriminate C2|]. split; [intros ->; discriminate C3|].
        split. { intros X. assert (Q : weqb kd wzero = true) by (apply weqb_w2Z; rewrite X; reflexivity). rewrite Q in Z0. discriminate Z0. }
        left. rewrite den_VPz, unsigned_VL. reflexivity.
      * destruct (IH ws' l k len kd NW Hin) as (A1 & A2 & A3 & A4). repeat split; try assumption. right. exact A4.
Qed.

Lemma justified_client : forall k rg, IMap.find k (s_regs st) = Some rg -> k <> 0%uint63 -> k <> STACK_ID ->
  (forall len kd b, win_lookup wnl k = Some (len, kd) -> In b LB -> 0 < bv_unsigned (den E len) ->
      (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) ->
      exists blk, In blk LBg /\ (blk_addr blk, blk_size blk) = b) ->
  forall a, bv_unsigned (ev E k) + loZ rg <= a < bv_unsigned (ev E k) + hiZ E rg -> rclient_addr LBg sp a.
Proof.
  intros k rg Hk K0 K1 WB a Ha.
  pose proof (cg_just CG) as J. unfold regions_justified in J. cbv zeta in J.
  pose proof (proj1 (IMap.forallb_spec _ _ (so_bst _ _ _ _ _ _ HS)) J k rg Hk) as Jk.
  destruct (region_justified_inv E _ _ _ _ _ (so_facts _ _ _ _ _ _ HS) Jk K0 K1) as (L0 & JJ).
  assert (LZ : loZ rg = 0) by (unfold loZ; rewrite L0; reflexivity). rewrite LZ in Ha.
  destruct JJ as [SJ|(len & kd & WL & WJ)].
  - left. rewrite <- (cg_regs CG X2), reg_of_X2, SP_R in SJ. lia.
  - apply (known_leu_q_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in WJ. fold (hiZ E rg) in WJ.
    destruct (nonstack_windows_In E n rest wnl k len kd (cg_wnl CG) (win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
    pose proof (proj1 (Forall_forall _ _) (cg_wf CG) _ INW) as (W1 & W2 & W3 & [[KS _]|[[KB B]|[KS (b & Hb & SUB)]]]); cbn [w_kind w_lo w_len w_iv] in *.
    + exfalso. exact (KD KS).
    + destruct (WB len kd _ WL B ltac:(lia) ltac:(intros x Hx; exact Hx)) as (blk & Hblk & Eblk).
      right; right. exists blk. split; [exact Hblk|]. unfold blk_addr, blk_size in *.
      pose proof (f_equal fst Eblk) as E1. pose proof (f_equal snd Eblk) as E2. cbn [fst snd w_iv w_lo w_len] in E1, E2.
      rewrite E1, E2. lia.
    + destruct (WB len kd b WL Hb ltac:(lia) SUB) as (blk & Hblk & Eblk).
      right; right. exists blk. split; [exact Hblk|].
      assert (INK : in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a) by (unfold in_iv; cbn [fst snd]; lia).
      specialize (SUB a INK). unfold in_iv in SUB. rewrite <- Eblk in SUB.
      unfold blk_addr, blk_size in *. cbn [fst snd] in SUB. lia.
Qed.

Lemma Rg4_ranges : forall r0 k rg, IMap.find 0%uint63 (s_regs st) = Some r0 -> IMap.find k (Rg4 r0) = Some rg ->
  exists rg', IMap.find k (s_regs st) = Some rg' /\ loZ rg = loZ rg' /\ (forall E0, hiZ E0 rg = hiZ E0 rg') /\ Mem.rg_w rg = Mem.rg_w rg'.
Proof.
  intros r0 k rg Hr0 H. destruct (Rg4_find r0 k rg Hr0 H) as [[-> ->]|[[-> ->]|(_ & _ & F)]].
  - exists r0. destruct (havoc_fields r0) as (L & Hh & W). unfold loZ, hiZ. rewrite L, Hh, W. auto.
  - exists r1. pose proof (cg_r1 CG) as Hr1.
    destruct (region_forget_sound rsegs (s_priv st) E (ms_mem ms) STACK_ID r1 (Mem.granule (Mem.rg_lo r1)) (Mem.granule ksp)
                (so_reg _ _ _ _ _ _ HS _ _ Hr1)) as (_ & L & Hh & W & _).
    fold (forget_r1 r1 ksp) in L, Hh, W. unfold loZ, hiZ. rewrite L, Hh, W. auto.
  - exists rg. auto.
Qed.

Lemma Rg4_disjoint : forall r0, IMap.find 0%uint63 (s_regs st) = Some r0 -> regions_disjoint E' (Rg4 r0).
Proof.
  intros r0 Hr0 k1 q1 k2 q2 H1 H2 N K1 K2 W a.
  destruct (Rg4_ranges r0 k1 q1 Hr0 H1) as (q1' & F1 & L1 & M1 & W1).
  destruct (Rg4_ranges r0 k2 q2 Hr0 H2) as (q2' & F2 & L2 & M2 & W2).
  rewrite L1, (M1 E'), L2, (M2 E'). rewrite W1, W2 in W.
  exact (so_disj _ _ _ _ _ _ HS' k1 q1' k2 q2' F1 F2 N K1 K2 W a).
Qed.

Lemma Rg4_in_based : forall r0 a, IMap.find 0%uint63 (s_regs st) = Some r0 -> in_based E' (Rg4 r0) a -> in_based E' (s_regs st) a.
Proof.
  intros r0 a Hr0 (k & rg & H & K & R). destruct (Rg4_ranges r0 k rg Hr0 H) as (rg' & F & L & M & _).
  exists k, rg'. rewrite <- L, <- (M E'). auto.
Qed.

Lemma other_ops_hold : forall o, In o (s_ops st) -> not_id HEAP_ID o ->
  St.op_holds OPS (op_id o) (map (den E') (op_args o)) (ms_mem ms) mo -> St.op_holds OPS (op_id o) (map (den E') (op_args o)) M' mo'.
Proof.
  intros o Ho NI H. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
  apply (OPS_mo_other _ _ _ mo mo' NI (gp_va _ _ _ _ _ _ _ _ _ GP)).
  apply (OPS_frame_other _ _ (ms_mem ms) M' mo NI H).
  intros a Ha FP. destruct (OPS_fp_other _ _ a NI FP) as [R NS].
  destruct (client_byte a ltac:(unfold two64 in Ha; lia) ltac:(right; left; auto)) as (E1 & _). unfold wa in E1. symmetry. exact E1.
Qed.

Lemma MP' : MP mo'.
Proof. exact (MP_vm mo mo' (gp_va _ _ _ _ _ _ _ _ _ GP) HMP). Qed.

Lemma mfacts' : mfacts mo'.
Proof. destruct (gp_mo _ _ _ _ _ _ _ _ _ GP) as (H1 & H2 & _). split; assumption. Qed.

Lemma minv' : forall a b, M' a = Some b -> forall seg, find_segment rsegs (bv_unsigned a) 1 = Some seg -> seg_writable seg = true.
Proof.
  intros a b H seg Hs. pose proof (gp_minv _ _ _ _ _ _ _ _ _ GP a b H) as X. unfold ro_addr in X. rewrite Hs in X.
  destruct (seg_writable seg); [reflexivity| discriminate X].
Qed.

Theorem post_N : forall v hargs',
  (forall b, In b LBf -> In b LBg) ->
  den E' v = PropExec.getr R' 10%bv ->
  St.op_holds OPS HEAP_ID (map (den E') hargs') M' mo' ->
  (forall a, Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E') hargs')) ->
             Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E) hargs))) ->
  St.st_ok rsegs OPS E' (setr (set_ops st4 (set_op HEAP_ID hargs' (s_ops st4))) X10 v) ms' mo' /\ MP mo'.
Proof.
  intros v hargs' ALL Hv HH FP. split; [| exact MP'].
  destruct ST4 as (r0 & Hr0 & ->).
  pose proof HS' as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (REGS : forall k rg, IMap.find k (Rg4 r0) = Some rg -> St.region_ok rsegs (s_priv st) E' M' k rg).
  { intros k rg H. destruct (Rg4_find r0 k rg Hr0 H) as [[-> ->]|[[-> ->]|(K0 & K1 & F)]].
    - apply r0_ok. exact Hr0.
    - apply r1_ok.
    - apply (old_region_ok k rg F); [apply Uint63.eqb_false_spec; exact K0|].
      apply (justified_client k rg F K0 K1). intros len kd b WL Hb SUB.
      assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
      apply in_map_iff in Hb' as (blk & Eb & Hblk). exists blk. split; [apply ALL; exact Hblk| exact Eb]. }
  unfold setr, set_ops, alloc_post_mk. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]. fold e15. fold (Rg4 r0).
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
  - reflexivity.
  - rewrite rf_get_set_other by discriminate. change (rf_get (s_rf (clobber st)) X0) with (getr (clobber st) X0). rewrite getr_clobber. cbn [clob_pos]. exact Px0.
  - apply post_regs. exact Hv.
  - exact Pfregs.
  - reflexivity.
  - pose proof (cg_ms CG) as MSE. pose proof Presv as X. unfold resv_ok in X |- *. destruct (s_resv st); [reflexivity| |exact I].
    exfalso. rewrite MSE in X. cbn in X. discriminate X.
  - exact Pfcsr.
  - reflexivity.
  - rewrite ev_E'_below; [exact (so_zero _ _ _ _ _ _ HS)|]. destruct NX as (_ & P & _). change (to_Z 0%uint63) with 0. lia.
  - apply Rg4_bst.
  - exact REGS.
  - apply Rg4_disjoint. exact Hr0.
  - eapply pub_of_regions. exact REGS.
  - exact Pfacts.
  - eapply (ops_hold_set_op OPS E' E' (s_ops st) HEAP_ID hargs hargs' (ms_mem ms) M' mo mo' (cg_find CG) (cg_count CG) Pops).
    + exact other_ops_hold.
    + exact HH.
  - eapply (ops_apart_set_op rsegs OPS E' E' (s_ops st) HEAP_ID hargs hargs' (s_regs st) (Rg4 r0) (s_priv st) (cg_find CG) (cg_count CG) Papart).
    + intros o a Ho NI IMP X. destruct (IMP X) as [NB PR]. split; [| exact PR]. intros IB. apply NB. eapply Rg4_in_based; eauto.
    + intros a X. assert (X' : Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E') hargs))).
      { rewrite (map_ext_in (den E') (den E) hargs) ; [apply FP; exact X|]. intros u Hu. apply den_E'.
        destruct SVB_parts as (_ & _ & _ & _ & _ & OV). exact (forallb_In _ _ _ u (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) Hu). }
      destruct (ops_apart_find rsegs OPS E' (s_ops st) (s_regs st) (s_priv st) HEAP_ID hargs a Papart (cg_find CG) X') as [NB PR].
      split; [| exact PR]. intros IB. apply NB. eapply Rg4_in_based; eauto.
  - apply (St.plain_minv _ _ OPS_plain). apply mfacts'.
  - intros xa _. apply St.plain_cover. exact OPS_plain.
  - exact minv'.
Qed.

Definition k16 : int := PrimInt63.add (s_next st) 16%uint63.
Lemma k16_addn : k16 = addn (s_next st) 16.
Proof.
  destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  unfold k16. symmetry. apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma ev_k16 : ev E' k16 = Fv 16.
Proof. rewrite k16_addn, ev_E'_fresh by lia. reflexivity. Qed.
Lemma k16_Z : to_Z k16 = to_Z (s_next st) + 16.
Proof.
  destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  rewrite k16_addn, addn_Z; [lia| rewrite wB_two63, two63_eq; lia].
Qed.

Definition blk_region (nsv : sv) : Mem.region := Mem.Region 0%uint63 nsv true Mem.BGUnk IMap.empty.

Lemma block_post_shape : forall (S : sstate) (k nx : int) (RG : Mem.region) (hargs' : list sv) (f1 f2 f3 : fact) (v : sv),
  setr (addfact (addfact (addfact
         (set_ops (setregs (set_next S nx) (IMap.add k RG (s_regs (set_next S nx))))
                  (set_op HEAP_ID hargs' (s_ops (setregs (set_next S nx) (IMap.add k RG (s_regs (set_next S nx)))))))
         f1) f2) f3) X10 v
  = SS (s_pc S) (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (IMap.add k RG (s_regs S))
       (f3 :: f2 :: f1 :: s_facts S) (set_op HEAP_ID hargs' (s_ops S)) (s_priv S) nx.
Proof. intros. destruct S. reflexivity. Qed.

Lemma block_post_inv : forall r0 hargsB nsv rg stB,
  IMap.find 0%uint63 (s_regs st) = Some r0 -> st4 = alloc_post_mk ERRNO LIBC GOT GUARD CANARY st r ksp r0 r1 ->
  block_post st4 hargsB nsv rg = Some stB ->
  exists hargs', heap_add_window hargsB (VP k16 wzero) nsv (VL CtrLib.K_BLOCK) = Some hargs' /\
    stB = SS r (rf_set (s_rf (clobber st)) X10 (VP k16 wzero)) (s_ff st) (s_resv st)
             (IMap.add k16 (blk_region nsv) (Rg4 r0))
             (FULt nsv (VL two47) :: FAlign k16 4%uint63 :: FRange k16 (fst rg) (snd rg) :: s_facts st)
             (set_op HEAP_ID hargs' (s_ops st)) (s_priv st) (PrimInt63.add k16 1%uint63).
Proof.
  intros r0 hargsB nsv rg stB Hr0 E4 H. unfold block_post, fresh in H. rewrite E4 in H.
  cbn [fst snd s_next alloc_post_mk] in H. fold k16 in H.
  destruct (heap_add_window hargsB (VP k16 wzero) nsv (VL CtrLib.K_BLOCK)) as [hargs'|] eqn:AW; [|discriminate].
  apply Some_inj in H. exists hargs'. split; [reflexivity|]. subst stB.
  rewrite block_post_shape. unfold alloc_post_mk. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]. fold e15. reflexivity.
Qed.

Lemma blk_region_ok : forall nsv Ablk nZ junk,
  sv_vars_below (s_next st) nsv = true -> nZ = bv_unsigned (den E nsv) ->
  Fv 16 = Z_to_bv 64 Ablk -> (forall o, 0 <= o < nZ -> nth_error junk (Z.to_nat o) = Some (Gv 16 o)) ->
  rw_cells rsegs M' Ablk [CB (Z.to_nat nZ) junk] ->
  0 <= Ablk -> Ablk + nZ <= alloc_ceiling -> (Ablk + nZ <= RIMG_LO \/ RIMG_HI <= Ablk) ->
  St.region_ok rsegs (s_priv st) E' M' k16 (blk_region nsv).
Proof.
  intros nsv Ablk nZ junk SV EN F16 GJ RW A0 AC AI.
  pose proof alloc_ceiling_lt64 as C64. pose proof (bv_unsigned_in_range 64 (den E nsv)) as RN. unfold bv_modulus in RN.
  assert (EK : bv_unsigned (ev E' k16) = Ablk).
  { rewrite ev_k16, F16, Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. unfold W64.two64. lia. }
  assert (EH : hiZ E' (blk_region nsv) = nZ). { unfold hiZ, blk_region. cbn [Mem.rg_hi]. rewrite (den_E' nsv SV). symmetry. exact EN. }
  assert (EL : loZ (blk_region nsv) = 0) by reflexivity.
  assert (K0 : PrimInt63.eqb k16 0%uint63 = false).
  { apply Uint63.eqb_false_spec. intros X. pose proof k16_Z as KZ. rewrite X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NX as (_ & P & _). lia. }
  destruct RW as [[CW BA] WR]. cbn [cells_bytes cells_size] in BA, WR. rewrite app_nil_r in BA. rewrite Nat.add_0_r in WR.
  destruct BA as (_ & BL & BY). cbn [Cells.cells_wf Cells.cell_wf] in CW. destruct CW as [LJ _]. cbn [cbytes] in BL, BY. rewrite LJ in BL, BY.
  constructor; rewrite ?EK, ?EH, ?EL.
  - apply IMap.bst_empty || constructor.
  - intros _. unfold two64. lia.
  - intros _ a Ha. split; [| split].
    + rewrite rb_mrd. replace a with (Ablk + Z.of_nat (Z.to_nat (a - Ablk))) by lia. rewrite BY by lia. cbn [cbytes].
      destruct (nth_error junk (Z.to_nat (a - Ablk))) eqn:X; [congruence|]. apply nth_error_None in X. lia.
    + intros _. apply (proj2 (wb_wview _ _)). destruct WR as (_ & _ & W). replace a with (Ablk + (a - Ablk)) by lia. apply W.
      cbn [csize] in *. lia.
    + apply ref_find_segment_none; [lia|]. unfold RIMG_LO, RIMG_HI in AI. lia.
  - intros g gr Hg. cbn [blk_region Mem.rg_cells] in Hg. rewrite IMap.find_empty in Hg || cbn in Hg. discriminate Hg.
  - intros g gr c i Hg. cbn [blk_region Mem.rg_cells] in Hg. cbn in Hg. discriminate Hg.
  - intros o H1 _ _. specialize (H1 K0). unfold bg_byte. cbn [blk_region Mem.rg_bg]. unfold E'. rewrite eg_above by (rewrite k16_Z; lia).
    rewrite k16_Z. replace (to_Z (s_next st) + 16 - to_Z (s_next st)) with 16 by lia.
    rewrite rb_mrd. replace (Ablk + o) with (Ablk + Z.of_nat (Z.to_nat o)) by lia. rewrite BY by lia. rewrite GJ by lia. reflexivity.
Qed.

Lemma windows_wf_mono : forall ws L1 L2 c, windows_wf ws L1 c -> (forall b, In b L1 -> In b L2) -> windows_wf ws L2 c.
Proof.
  intros ws L1 L2 c WF SUB. apply Forall_forall. intros w Hw.
  pose proof (proj1 (Forall_forall _ _) WF w Hw) as (W1 & W2 & W3 & [[K S]|[[K B]|[K (b & Hb & SB)]]]).
  - split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. left; auto.
  - split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. right; left; auto.
  - split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. right; right. split; [exact K|]. exists b. auto.
Qed.

Lemma wins_of_E' : forall m l, forallb (sv_vars_below (s_next st)) l = true -> wins_of E' m l = wins_of E m l.
Proof.
  induction m as [|m IH]; intros l AV; [reflexivity|]. destruct l as [|x [|y [|z l']]]; try reflexivity. cbn [forallb] in AV.
  apply andb_prop in AV as [A1 AV]. apply andb_prop in AV as [A2 AV]. apply andb_prop in AV as [A3 AV].
  rewrite !wins_of_cons, (IH l' AV), !den_E' by assumption. reflexivity.
Qed.

Theorem post_B : forall hargsB a' nsv rlo rhi stB Ablk nZ junk,
  hargsB = VL md :: a' :: VL nw :: rest ->
  block_post st4 hargsB nsv (rlo, rhi) = Some stB ->
  sv_vars_below (s_next st) nsv = true -> sv_vars_below (s_next st) a' = true -> nZ = bv_unsigned (den E nsv) ->
  Fv 16 = Z_to_bv 64 Ablk -> (forall o, 0 <= o < nZ -> nth_error junk (Z.to_nat o) = Some (Gv 16 o)) ->
  rw_cells rsegs M' Ablk [CB (Z.to_nat nZ) junk] ->
  4096 <= Ablk -> Ablk + nZ <= alloc_ceiling -> Ablk mod 16 = 0 -> (Ablk + nZ <= RIMG_LO \/ RIMG_HI <= Ablk) ->
  w2Z rlo <= Ablk <= w2Z rhi ->
  (forall b a, In b LB -> in_iv b a -> ~ (Ablk <= a < Ablk + nZ)) ->
  (forall b, In b LBf -> In b LBg) ->
  aw_holdsI (den E a') ((Ablk, nZ) :: LB) M' mo' ->
  PropExec.getr R' 10%bv = Z_to_bv 64 Ablk ->
  St.st_ok rsegs OPS E' stB ms' mo' /\ MP mo'.
Proof.
  intros hargsB a' nsv rlo rhi stB Ablk nZ junk EhB HB SVn SVa EN F16 GJ RW A4096 AC A16 AI FR NEW ALL AWH Ha0.
  split; [| exact MP'].
  destruct ST4 as (r0 & Hr0 & E4).
  destruct (block_post_inv r0 hargsB nsv (rlo, rhi) stB Hr0 E4 HB) as (hargs' & AW & ->). cbn [fst snd].
  pose proof HS' as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  pose proof (cg_nwin CG) as NW. pose proof (cg_nw CG) as (T & N & L). pose proof (cg_hargs CG) as EH.
  pose proof alloc_ceiling_lt64 as C64. pose proof (bv_unsigned_in_range 64 (den E nsv)) as RN. unfold bv_modulus in RN.
  subst hargsB. assert (NW' : heap_nwin (VL md :: a' :: VL nw :: rest) = Some n) by (rewrite EH in NW; exact NW).
  rewrite (heap_add_window_eq md a' nw rest n _ nsv _ NW') in AW. apply Some_inj in AW. subst hargs'.
  assert (EK : bv_unsigned (ev E' k16) = Ablk).
  { rewrite ev_k16, F16, Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. unfold W64.two64. lia. }
  assert (DK : den E' (VP k16 wzero) = Z_to_bv 64 Ablk) by (rewrite den_VPz, ev_k16; exact F16).
  assert (EH' : hiZ E' (blk_region nsv) = nZ). { unfold hiZ, blk_region. cbn [Mem.rg_hi]. rewrite (den_E' nsv SVn). symmetry. exact EN. }
  assert (EL0 : loZ (blk_region nsv) = 0) by reflexivity.
  assert (K0 : PrimInt63.eqb k16 0%uint63 = false).
  { apply Uint63.eqb_false_spec. intros X. pose proof k16_Z as KZ. rewrite X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NX as (_ & P & _). lia. }
  assert (KF : forall k rg, IMap.find k (s_regs st) = Some rg -> k <> k16).
  { intros k rg Hk ->. destruct (reg_E' _ _ Hk) as (_ & _ & LT & _). apply Uint63.ltb_spec in LT. rewrite k16_Z in LT. lia. }
  assert (KF4 : IMap.find k16 (Rg4 r0) = None).
  { destruct (IMap.find k16 (Rg4 r0)) as [rg|] eqn:X; [|reflexivity]. exfalso.
    destruct (Rg4_ranges r0 k16 rg Hr0 X) as (rg' & F & _). exact (KF _ _ F eq_refl). }

  assert (NB : to_Z (wl nw) + 1 < two63).
  { pose proof (cg_n255 CG) as N255. pose proof (int_range (wl nw)) as R. unfold two63. rewrite N in N255. lia. }
  assert (DEC' : decode (map (den E') (VL md :: a' :: VL (wadd nw wone) :: firstn (3 * n) rest ++ [VP k16 wzero; nsv; VL CtrLib.K_BLOCK] ++ skipn (3 * n) rest))
                 = Some (w2Z md, den E' a', wins_of E n rest ++ [Win Ablk nZ K_BLOCK], map (den E) (skipn (3 * n) rest))).
  { rewrite (decode_add_window E' md a' nw rest n _ nsv _ T N L NB).
    rewrite DK, Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64; lia).
    rewrite (den_E' nsv SVn), <- EN, unsigned_VL. change (w2Z CtrLib.K_BLOCK) with K_BLOCK.
    destruct SVB_parts as (_ & _ & _ & _ & _ & OV).
    pose proof (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) as AV. rewrite EH in AV. cbn [op_args forallb] in AV.
    apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV].
    assert (CE : map (den E') (skipn (3 * n) rest) = map (den E) (skipn (3 * n) rest)).
    { apply map_ext_in. intros u Hu. apply den_E'. apply (forallb_In _ _ _ u AV). rewrite <- (firstn_skipn (3 * n) rest). apply in_app_iff. right. exact Hu. }
    rewrite (wins_of_E' n rest AV), CE. reflexivity. }
  assert (MAPH : map (den E') hargs = map (den E) hargs).
  { apply map_ext_in. intros u Hu. apply den_E'. destruct SVB_parts as (_ & _ & _ & _ & _ & OV).
    exact (forallb_In _ _ _ u (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) Hu). }

  assert (NEWR : forall a k rg, Ablk <= a < Ablk + nZ -> IMap.find k (Rg4 r0) = Some rg -> PrimInt63.eqb k 0%uint63 = false ->
            ~ (bv_unsigned (ev E' k) + loZ rg <= a < bv_unsigned (ev E' k) + hiZ E' rg)).
  { intros a k rg Ha Hk K R. destruct (Rg4_ranges r0 k rg Hr0 Hk) as (rg' & F & L' & Mq & _). rewrite L', (Mq E') in R.
    destruct (reg_E' _ _ F) as (Ek & Eh & _). rewrite Ek, Eh in R.
    destruct (Uint63.eqb k STACK_ID) eqn:K1.
    - apply Uint63.eqb_correct in K1. subst k. rewrite (cg_r1 CG) in F. injection F as <-.
      pose proof (cg_ceil CG) as CE. unfold lo, base in *. lia.
    - apply Uint63.eqb_false_spec in K1. apply Uint63.eqb_false_spec in K.
      assert (CL : rclient_addr LBg sp a).
      { apply (justified_client k rg' F K K1); [| exact R]. intros len kd b WL Hb SUB.
        assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
        apply in_map_iff in Hb' as (blk & Eb & Hblk). exists blk. split; [apply ALL; exact Hblk| exact Eb]. }
      destruct CL as [S1|[[I1 I2]|(blk & Hblk & Rb)]].
      + pose proof (cg_ceil CG) as CE. pose proof (cg_room CG) as RM. pose proof (int_range need). unfold sp, lo, base in *. lia.
      + unfold RIMG_LO, RIMG_HI in AI. lia.
      + apply HLBg in Hblk. apply (NEW (blk_addr blk, blk_size blk) a); [| unfold in_iv; cbn [fst snd]; lia| lia].
        eapply Permutation_in; [exact (cg_perm CG)|]. apply in_map_iff. exists blk. auto. }
  set (R5 := IMap.add k16 (blk_region nsv) (Rg4 r0)).
  pose proof (Rg4_bst r0) as B4.
  assert (F5 : forall k rg, IMap.find k R5 = Some rg -> (k = k16 /\ rg = blk_region nsv) \/ (k <> k16 /\ IMap.find k (Rg4 r0) = Some rg)).
  { intros k rg H. subst R5. destruct (Uint63.eqb k16 k) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_add_same in H by exact B4. injection H as <-. left; auto.
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other in H by (exact B4 || exact Q). right. split; [congruence| exact H]. }
  assert (REGS : forall k rg, IMap.find k R5 = Some rg -> St.region_ok rsegs (s_priv st) E' M' k rg).
  { intros k rg H. destruct (F5 k rg H) as [[-> ->]|[NK H4']].
    - apply (blk_region_ok nsv Ablk nZ junk); try assumption. lia.
    - destruct (Rg4_find r0 k rg Hr0 H4') as [[-> ->]|[[-> ->]|(K0' & K1 & F)]].
      + apply r0_ok. exact Hr0.
      + apply r1_ok.
      + apply (old_region_ok k rg F); [apply Uint63.eqb_false_spec; exact K0'|].
        apply (justified_client k rg F K0' K1). intros len kd b WL Hb SUB.
        assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
        apply in_map_iff in Hb' as (blk & Eb & Hblk). exists blk. split; [apply ALL; exact Hblk| exact Eb]. }
  assert (NEWB : forall a, in_based E' R5 a -> (Ablk <= a < Ablk + nZ) \/ in_based E' (s_regs st) a).
  { intros a (k & rg & H & K & R). destruct (F5 k rg H) as [[-> ->]|[NK H4']].
    - left. rewrite EK, EH', EL0 in R. lia.
    - right. apply (Rg4_in_based r0 a Hr0). exists k, rg. auto. }

  assert (HH : St.op_holds OPS HEAP_ID (map (den E') (VL md :: a' :: VL (wadd nw wone) :: firstn (3 * n) rest ++ [VP k16 wzero; nsv; VL CtrLib.K_BLOCK] ++ skipn (3 * n) rest)) M' mo').
  { rewrite OPS_holds1. exists (w2Z md), (den E' a'), (wins_of E n rest ++ [Win Ablk nZ K_BLOCK]), (map (den E) (skipn (3 * n) rest)), ((Ablk, nZ) :: LB).
    split; [exact DEC'|]. split; [apply aw_holdsW_intro; [rewrite (den_E' a' SVa); exact AWH| apply NG_app_block; exact (cg_ng CG)]|]. split.
    - apply Forall_app. split.
      + apply (windows_wf_mono _ LB). { exact (cg_wf CG). } intros b Hb. right. exact Hb.
      + constructor; [| constructor]. split; [cbn [w_lo]; lia|]. split; [cbn [w_len]; lia|]. split; [cbn [w_lo w_len]; unfold two64; lia|].
        right; left. split; [reflexivity|]. left. reflexivity.
    - apply (cw_grow Cw). 2:{ intros a Ha U. unfold in_user in U. apply in_ivs_In in U as (b & Hb & Hin). exact (NEW b a Hb Hin Ha). }
      apply (cw_frame Cw _ _ _ _ (ms_mem ms) M' (cg_cw CG)). intros a Ha U _.
      unfold in_user in U. apply in_ivs_In in U as (b & Hb & Hin).
      assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
      apply in_map_iff in Hb' as (blk & Eb & Hblk).
      destruct (client_byte a ltac:(unfold two64 in Ha; lia)) as (E1 & _); [| unfold wa in E1; symmetry; exact E1].
      right; right. exists blk. split; [apply ALL; exact Hblk|]. unfold in_iv in Hin. rewrite <- Eb in Hin. cbn [fst snd] in Hin. exact Hin. }
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
  - reflexivity.
  - rewrite rf_get_set_other by discriminate. change (rf_get (s_rf (clobber st)) X0) with (getr (clobber st) X0). rewrite getr_clobber. cbn [clob_pos]. exact Px0.
  - apply post_regs. rewrite DK. symmetry. exact Ha0.
  - exact Pfregs.
  - reflexivity.
  - pose proof (cg_ms CG) as MSE. pose proof Presv as X. unfold resv_ok in X |- *. destruct (s_resv st); [reflexivity| |exact I].
    exfalso. rewrite MSE in X. cbn in X. discriminate X.
  - exact Pfcsr.
  - reflexivity.
  - rewrite ev_E'_below; [exact (so_zero _ _ _ _ _ _ HS)|]. destruct NX as (_ & P & _). change (to_Z 0%uint63) with 0. lia.
  - subst R5. apply IMap.bst_add. exact B4.
  - exact REGS.
  - intros k1 q1 k2 q2 H1 H2 NE K1 K2 W a [X1 X2].
    destruct (F5 k1 q1 H1) as [[-> ->]|[N1 G1]]; destruct (F5 k2 q2 H2) as [[-> ->]|[N2 G2]].
    + exact (NE eq_refl).
    + rewrite EK, EH', EL0 in X1. exact (NEWR a k2 q2 ltac:(lia) G2 K2 X2).
    + rewrite EK, EH', EL0 in X2. exact (NEWR a k1 q1 ltac:(lia) G1 K1 X1).
    + exact (Rg4_disjoint r0 Hr0 k1 q1 k2 q2 G1 G2 NE K1 K2 W a (conj X1 X2)).
  - eapply pub_of_regions. exact REGS.
  - constructor; [| constructor; [| constructor; [| exact Pfacts]]].
    + cbn [fact_holds]. rewrite (den_E' nsv SVn), <- EN, unsigned_VL. change (w2Z two47) with (2 ^ 47).
      pose_ceil. unfold CEIL_MIN, CEIL_MAX in *. lia.
    + cbn [fact_holds]. rewrite EK. change (2 ^ to_Z 4%uint63) with 16. exact A16.
    + cbn [fact_holds]. rewrite EK. exact FR.
  - eapply (ops_hold_set_op OPS E' E' (s_ops st) HEAP_ID hargs _ (ms_mem ms) M' mo mo' (cg_find CG) (cg_count CG) Pops).
    + exact other_ops_hold.
    + exact HH.
  - eapply (ops_apart_set_op rsegs OPS E' E' (s_ops st) HEAP_ID hargs _ (s_regs st) R5 (s_priv st) (cg_find CG) (cg_count CG) Papart).
    + intros o a Ho NI IMP X. destruct (IMP X) as [NB' PR]. split; [| exact PR]. intros IB.
      destruct (NEWB a IB) as [BL|OLD]; [| exact (NB' OLD)].
      unfold not_id in NI. apply Uint63.eqb_false_spec in NI. destruct (OPS_fp_other _ _ a NI X) as [RNG _]. unfold RIMG_LO, RIMG_HI in AI. lia.
    + intros a X. rewrite OPS_fp1 in X. apply (proj1 (fp_spec IMGX _ _ _ _ _ a DEC')) in X as (Ra & NI & NWS).
      assert (X' : Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E') hargs))).
      { rewrite OPS_fp1, MAPH. apply (proj2 (fp_spec IMGX _ _ _ _ _ a (cg_decode CG))). split; [exact Ra|]. split; [exact NI|].
        intros W. apply NWS. unfold in_ws in *. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). left. exact W. }
      destruct (ops_apart_find rsegs OPS E' (s_ops st) (s_regs st) (s_priv st) HEAP_ID hargs a Papart (cg_find CG) X') as [NB' PR].
      split; [| exact PR]. intros IB. destruct (NEWB a IB) as [BL|OLD]; [| exact (NB' OLD)].
      apply NWS. unfold in_ws. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). right. cbn [map].
      apply (proj2 (in_ivs_cons _ _ _)). left. unfold in_iv, w_iv. cbn [fst snd w_lo w_len]. exact BL.
  - apply (St.plain_minv _ _ OPS_plain). apply mfacts'.
  - intros xa _. apply St.plain_cover. exact OPS_plain.
  - exact minv'.
Qed.

Lemma blk_by_id : forall (l : list block) b1 b2, List.NoDup (map blk_id l) -> In b1 l -> In b2 l -> blk_id b1 = blk_id b2 -> b1 = b2.
Proof.
  intros l. induction l as [|x l IH]; intros b1 b2 ND I1 I2 E12; [destruct I1|].
  cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
  destruct I1 as [<-|I1]; destruct I2 as [<-|I2].
  - reflexivity.
  - exfalso. apply NI. rewrite E12. apply in_map. exact I2.
  - exfalso. apply NI. rewrite <- E12. apply in_map. exact I1.
  - exact (IH b1 b2 ND I1 I2 E12).
Qed.

Theorem post_F : forall r0 kf rf lenf p Af nf a' hargs' l1 l2 stF,
  IMap.find 0%uint63 (s_regs st) = Some r0 -> st4 = alloc_post_mk ERRNO LIBC GOT GUARD CANARY st r ksp r0 r1 ->
  IMap.find kf (s_regs st) = Some rf -> kf <> 0%uint63 -> kf <> STACK_ID ->
  free_ok st wnl kf = Some lenf ->
  In (p, Af, nf) LBf -> Af = bv_unsigned (ev E kf) -> nf = bv_unsigned (den E lenf) ->
  (forall b, In b LBf -> blk_id b <> p -> In b LBg) -> (forall b, In b LBg -> blk_id b <> p) ->
  wins_of E n rest = l1 ++ Win Af nf K_BLOCK :: l2 ->
  (forall w, In w (l1 ++ l2) -> w_kind w = K_STACK \/ exists k len kd, In (k, len, kd) wnl /\ k <> kf /\
                                  w = Win (bv_unsigned (ev E k)) (bv_unsigned (den E len)) (w2Z kd)) ->
  decode (map (den E') hargs') = Some (w2Z md, den E' a', l1 ++ l2, map (den E) (skipn (3 * n) rest)) ->
  sv_vars_below (s_next st) a' = true ->
  aw_holdsI (den E a') (remove iv_eq_dec (Af, nf) LB) M' mo' ->
  Fv 16 = PropExec.getr R' 10%bv ->
  stF = SS r (rf_set (s_rf (clobber st)) X10 (VP k16 wzero)) (s_ff st) (s_resv st) (IMap.remove kf (Rg4 r0)) (s_facts st)
           (set_op HEAP_ID hargs' (s_ops st)) (s_priv st) (PrimInt63.add k16 1%uint63) ->
  St.st_ok rsegs OPS E' stF ms' mo' /\ MP mo'.
Proof.
  intros r0 kf rf lenf p Af nf a' hargs' l1 l2 stF Hr0 E4 Hkf K0 K1 FOK INf EAf Enf LBG LBGid WS PROV DEC' SVa AWH F16 ->.
  split; [| exact MP'].
  pose proof HS' as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  pose proof (Rg4_bst r0) as B4. pose proof alloc_ceiling_lt64 as C64.
  pose proof (cg_rheap CG) as RH. apply RHEAP_split in RH as [RC _].
  pose proof (RHEAP_core_nodup s LBf (ms_mem ms) RC) as NDid.
  destruct (free_ok_inv st wnl kf lenf FOK) as (rf' & Hrf' & WLf & LOf & NEf & LEf & OTH). rewrite Hkf in Hrf'. injection Hrf' as <-.
  apply (known_ltu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in NEf. rewrite unsigned_VL in NEf. change (w2Z wzero) with 0 in NEf. fold (hiZ E rf) in NEf.
  apply (known_leu_q_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in LEf. fold (hiZ E rf) in LEf. rewrite <- Enf in LEf.
  assert (LZf : loZ rf = 0) by (unfold loZ; rewrite LOf; reflexivity).

  destruct (RHEAP_core_block_range s LBf (ms_mem ms) _ RC INf) as (Bf1 & Bf2 & Bf3 & Bf4 & _). cbn [blk_addr blk_size fst snd] in Bf1, Bf2, Bf3, Bf4.

  assert (FREED : forall k2 len2 kd2, In (k2, len2, kd2) wnl -> k2 <> kf ->
            (0 < bv_unsigned (den E len2)
             \/ (bv_unsigned (den E len2) = 0 /\ exists k3 len3, In (k3, len3, CtrLib.K_BLOCK) wnl /\ k3 <> kf)) /\
            forall a, bv_unsigned (ev E k2) <= a < bv_unsigned (ev E k2) + bv_unsigned (den E len2) -> ~ (Af <= a < Af + nf)).
  { intros k2 len2 kd2 I2 NK.
    destruct (OTH k2 len2 kd2 I2 NK) as (rg2 & Hk2 & LO2 & NE2' & LE2 & WW & FULL).
    apply (known_leu_q_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in LE2. fold (hiZ E rg2) in LE2.
    pose proof (bv_unsigned_in_range 64 (den E (Mem.rg_hi rg2))) as HR2. rewrite bv_modulus_64 in HR2. fold (hiZ E rg2) in HR2.
    assert (NE2 : 0 < hiZ E rg2 \/ (bv_unsigned (den E len2) = 0 /\ exists k3 len3, In (k3, len3, CtrLib.K_BLOCK) wnl /\ k3 <> kf)).
    { destruct NE2' as [NE2|(KNB & HEQ & OB)].
      - left. apply (known_ltu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in NE2. rewrite unsigned_VL in NE2. change (w2Z wzero) with 0 in NE2. fold (hiZ E rg2) in NE2. exact NE2.
      - destruct (Z_lt_le_dec 0 (hiZ E rg2)) as [POS2|Z2]; [left; exact POS2| right]. split; [| exact OB].
        apply (known_eq_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in HEQ. apply (f_equal bv_unsigned) in HEQ. fold (hiZ E rg2) in HEQ. lia. }
    assert (LZ2 : loZ rg2 = 0) by (unfold loZ; rewrite LO2; reflexivity).
    destruct (nonstack_windows_In E n rest wnl k2 len2 kd2 (cg_wnl CG) I2) as (K20 & K21 & KD2 & INW2).
    split; [destruct NE2 as [NE2|NE2]; [left; lia| right; exact NE2]|]. intros a Ha INA.
    destruct NE2 as [NE2|[Z2 _]]; [| lia].

    assert (DISJ := so_disj _ _ _ _ _ _ HS kf rf k2 rg2 Hkf Hk2 ltac:(congruence) ltac:(apply Uint63.eqb_false_spec; exact K0) ltac:(apply Uint63.eqb_false_spec; exact K20)
                     ltac:(destruct WW; [left|right]; assumption)).
    rewrite LZf, LZ2, <- EAf in DISJ.
    pose proof (proj1 (Forall_forall _ _) (cg_wf CG) _ INW2) as (_ & _ & _ & [[KS _]|[[KB B2]|[KS (b & Hb & SUB)]]]); cbn [w_kind w_lo w_len w_iv] in *.
    - exact (KD2 KS).
    -
      assert (B2' : In (bv_unsigned (ev E k2), bv_unsigned (den E len2)) (blocks_of LBf))
        by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact B2]).
      apply in_map_iff in B2' as (blk2 & Eb2 & Hblk2).
      destruct (bptr_eqb (blk_id blk2) p) eqn:BP.
      + apply bptr_eqb_true in BP. pose proof (blk_by_id LBf blk2 (p, Af, nf) NDid Hblk2 INf BP) as ->.
        cbn [blk_addr blk_size fst snd] in Eb2. injection Eb2 as EA2 EN2.
        apply (DISJ Af). rewrite <- EA2. lia.
      + assert (NEb : blk_id (p, Af, nf) <> blk_id blk2).
        { cbn [blk_id fst]. intros X. rewrite <- X in BP. rewrite (proj2 (bptr_eqb_true p p) eq_refl) in BP. discriminate BP. }
        pose proof (f_equal fst Eb2) as E1. pose proof (f_equal snd Eb2) as E2. unfold blk_addr, blk_size in E1, E2. cbn [fst snd] in E1, E2.
        destruct (RHEAP_core_blocks_disjoint s LBf (ms_mem ms) (p, Af, nf) blk2 RC INf Hblk2 NEb) as [D|D];
          unfold blk_addr, blk_size in D; cbn [fst snd] in D; lia.
    -
      assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
      apply in_map_iff in Hb' as (blk2 & Eb2 & Hblk2).
      destruct (bptr_eqb (blk_id blk2) p) eqn:BP.
      + apply bptr_eqb_true in BP. pose proof (blk_by_id LBf blk2 (p, Af, nf) NDid Hblk2 INf BP) as ->.
        cbn [blk_addr blk_size fst snd] in Eb2. subst b.
        destruct FULL as [KDB|FU]; [rewrite KDB in KS; unfold K_SUB in KS; change (w2Z CtrLib.K_BLOCK) with 1 in KS; lia|].
        apply (known_eq_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in FU. apply (f_equal bv_unsigned) in FU. fold (hiZ E rf) in FU. rewrite <- Enf in FU.
        assert (INK : in_iv (bv_unsigned (ev E k2), bv_unsigned (den E len2)) (bv_unsigned (ev E k2))) by (unfold in_iv; cbn [fst snd]; lia).
        specialize (SUB (bv_unsigned (ev E k2)) INK). unfold in_iv in SUB. cbn [fst snd] in SUB.
        apply (DISJ (bv_unsigned (ev E k2))). lia.
      + assert (NEb : blk_id (p, Af, nf) <> blk_id blk2).
        { cbn [blk_id fst]. intros X. rewrite <- X in BP. rewrite (proj2 (bptr_eqb_true p p) eq_refl) in BP. discriminate BP. }
        assert (INK : in_iv (bv_unsigned (ev E k2), bv_unsigned (den E len2)) a) by (unfold in_iv; cbn [fst snd]; lia).
        specialize (SUB a INK). unfold in_iv in SUB. rewrite <- Eb2 in SUB. unfold blk_addr, blk_size in SUB. cbn [fst snd] in SUB.
        destruct (RHEAP_core_blocks_disjoint s LBf (ms_mem ms) (p, Af, nf) blk2 RC INf Hblk2 NEb) as [D|D];
          unfold blk_addr, blk_size in D; cbn [fst snd] in D; lia. }
  set (R6 := IMap.remove kf (Rg4 r0)).
  assert (F6 : forall k rg, IMap.find k R6 = Some rg -> k <> kf /\ IMap.find k (Rg4 r0) = Some rg).
  { intros k rg H. subst R6. destruct (Uint63.eqb kf k) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_remove_same in H by exact B4. discriminate H.
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_remove_other in H by (exact B4 || exact Q). split; [congruence| exact H]. }

  assert (LIVE : forall len kd b k, win_lookup wnl k = Some (len, kd) -> k <> kf -> In b LB -> 0 < bv_unsigned (den E len) ->
            (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) ->
            exists blk, In blk LBg /\ (blk_addr blk, blk_size blk) = b).
  { intros len kd b k WL NK Hb POS SUB.
    assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
    apply in_map_iff in Hb' as (blk & Eb & Hblk). exists blk. split; [| exact Eb]. apply LBG; [exact Hblk|]. intros EQ.
    pose proof (blk_by_id LBf blk (p, Af, nf) NDid Hblk INf EQ) as ->. unfold blk_addr, blk_size in Eb. cbn [fst snd] in Eb. subst b.
    destruct (FREED k len kd (win_lookup_In _ _ _ _ WL) NK) as [_ FR'].
    assert (INK : in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) (bv_unsigned (ev E k))) by (unfold in_iv; cbn [fst snd]; lia).
    pose proof (SUB _ INK) as IB. unfold in_iv in IB. cbn [fst snd] in IB.
    exact (FR' (bv_unsigned (ev E k)) ltac:(lia) IB). }
  assert (REGS : forall k rg, IMap.find k R6 = Some rg -> St.region_ok rsegs (s_priv st) E' M' k rg).
  { intros k rg H. destruct (F6 k rg H) as [NK H4']. destruct (Rg4_find r0 k rg Hr0 H4') as [[-> ->]|[[-> ->]|(K0' & K1' & F)]].
    - apply r0_ok. exact Hr0.
    - apply r1_ok.
    - apply (old_region_ok k rg F); [apply Uint63.eqb_false_spec; exact K0'|].
      apply (justified_client k rg F K0' K1'). intros len kd b WL Hb POS SUB. exact (LIVE len kd b k WL NK Hb POS SUB). }
  assert (NEWB : forall a, in_based E' R6 a -> in_based E' (s_regs st) a).
  { intros a (k & rg & H & K & R). destruct (F6 k rg H) as [_ H4']. apply (Rg4_in_based r0 a Hr0). exists k, rg. auto. }

  pose proof (cg_wf CG) as WF. rewrite WS in WF.
  assert (WIN : forall w, In w (l1 ++ l2) -> In w (l1 ++ Win Af nf K_BLOCK :: l2)) by (intros w Hw; apply in_app_iff in Hw as [Hw|Hw]; apply in_app_iff; [left| right; right]; exact Hw).
  assert (NOTF : forall w, In w (l1 ++ l2) -> w <> Win Af nf K_BLOCK).
  { intros w Hw ->. destruct (PROV _ Hw) as [S|(k2 & len2 & kd2 & I2 & NK2 & EW)]; [cbn in S; unfold K_STACK, K_BLOCK in S; lia|].
    injection EW as EA2 EN2 _. destruct (FREED k2 len2 kd2 I2 NK2) as [_ FR']. apply (FR' Af); lia. }
  assert (HH : St.op_holds OPS HEAP_ID (map (den E') hargs') M' mo').
  { rewrite OPS_holds1. exists (w2Z md), (den E' a'), (l1 ++ l2), (map (den E) (skipn (3 * n) rest)), (remove iv_eq_dec (Af, nf) LB).
    split; [exact DEC'|]. split; [apply aw_holdsW_intro; [rewrite (den_E' a' SVa); exact AWH| apply (NG_incl _ _ (cg_ng CG)); intros w Hw; rewrite WS; exact (WIN w Hw)]|]. split.
    - apply Forall_forall. intros w Hw.
      pose proof (proj1 (Forall_forall _ _) WF w (WIN w Hw)) as (W1 & W2 & W3 & ALT).
      split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
      destruct ALT as [[K S]|[[K B]|[K (b & Hb & SUB)]]]; [left; auto| right; left| right; right].
      + split; [exact K|]. apply in_in_remove; [| exact B]. intros EQ.
        destruct (PROV _ Hw) as [S|(k2 & len2 & kd2 & I2 & NK2 & ->)]; [rewrite K in S; unfold K_STACK, K_BLOCK in S; lia|].
        cbn [w_iv w_lo w_len] in EQ. injection EQ as EA2 EN2. destruct (FREED k2 len2 kd2 I2 NK2) as [_ FR']. apply (FR' Af); lia.
      + split; [exact K|].
        destruct (PROV _ Hw) as [S|(k2 & len2 & kd2 & I2 & NK2 & ->)]; [rewrite S in K; unfold K_STACK, K_SUB in K; lia|].
        cbn [w_iv w_lo w_len] in SUB. destruct (FREED k2 len2 kd2 I2 NK2) as [[POS|(Z0 & k3 & len3 & I3 & NK3)] FR'].
        * exists b. split; [| exact SUB]. apply in_in_remove; [| exact Hb]. intros ->.
          assert (INK : in_iv (bv_unsigned (ev E k2), bv_unsigned (den E len2)) (bv_unsigned (ev E k2))) by (unfold in_iv; cbn [fst snd]; lia).
          pose proof (SUB _ INK) as IB. unfold in_iv in IB. cbn [fst snd] in IB. apply (FR' (bv_unsigned (ev E k2))); lia.
        *
          destruct (nonstack_windows_In E n rest wnl k3 len3 CtrLib.K_BLOCK (cg_wnl CG) I3) as (K30 & K31 & _ & INW3).
          pose proof (proj1 (Forall_forall _ _) (cg_wf CG) _ INW3) as (_ & _ & _ & ALT3). cbn [w_kind w_lo w_len w_iv] in ALT3.
          change (w2Z CtrLib.K_BLOCK) with 1 in ALT3.
          destruct ALT3 as [[KS3 _]|[[_ B3]|[KS3 _]]]; [unfold K_STACK in KS3; lia| | unfold K_SUB in KS3; lia].
          exists (bv_unsigned (ev E k3), bv_unsigned (den E len3)). split.
          -- apply in_in_remove; [| exact B3]. intros EQ. injection EQ as EA3 EN3.
             destruct (FREED k3 len3 CtrLib.K_BLOCK I3 NK3) as [[POS3|[Z3 _]] FR3']; [| lia].
             apply (FR3' (bv_unsigned (ev E k3))); lia.
          -- intros a Ha. exfalso. unfold in_iv in Ha. cbn [w_iv w_lo w_len fst snd] in Ha. lia.
    - apply (cw_free Cw (w2Z md) _ LB (l1 ++ Win Af nf K_BLOCK :: l2) M' Af nf (l1 ++ l2)).
      + apply (cw_frame Cw _ _ _ _ (ms_mem ms) M'); [rewrite <- WS; exact (cg_cw CG)|]. intros a Ha U NW.
        unfold in_user in U. apply in_ivs_In in U as (b & Hb & Hin).
        assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
        apply in_map_iff in Hb' as (blk & Eb & Hblk).
        destruct (bptr_eqb (blk_id blk) p) eqn:BP.
        * exfalso. apply bptr_eqb_true in BP. pose proof (blk_by_id LBf blk (p, Af, nf) NDid Hblk INf BP) as ->.
          unfold blk_addr, blk_size in Eb. cbn [fst snd] in Eb. subst b. apply NW. unfold in_ws, heap_ws. apply in_ivs_In.
          exists (Af, nf). split; [| exact Hin]. apply in_map_iff. exists (Win Af nf K_BLOCK). split; [reflexivity|].
          apply filter_In. split; [apply in_app_iff; right; left; reflexivity| reflexivity].
        * assert (NEp : blk_id blk <> p) by (intros X; rewrite X, (proj2 (bptr_eqb_true p p) eq_refl) in BP; discriminate BP).
          destruct (client_byte a ltac:(unfold two64 in Ha; lia)) as (E1 & _); [| unfold wa in E1; symmetry; exact E1].
          right; right. exists blk. split; [apply LBG; assumption|]. unfold in_iv in Hin. rewrite <- Eb in Hin. cbn [fst snd] in Hin. exact Hin.
      + apply in_app_iff. right. left. reflexivity.
      + intros w. split.
        * intros Hw. split; [exact (WIN w Hw)| exact (NOTF w Hw)].
        * intros [Hw NE]. apply in_app_iff in Hw. apply in_app_iff. destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw| exfalso; exact (NE (eq_sym Hw))| right; exact Hw]. }
  assert (DK : den E' (VP k16 wzero) = PropExec.getr R' 10%bv) by (rewrite den_VPz, ev_k16; exact F16).
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
  - reflexivity.
  - rewrite rf_get_set_other by discriminate. change (rf_get (s_rf (clobber st)) X0) with (getr (clobber st) X0). rewrite getr_clobber. cbn [clob_pos]. exact Px0.
  - apply post_regs. exact DK.
  - exact Pfregs.
  - reflexivity.
  - pose proof (cg_ms CG) as MSE. pose proof Presv as X. unfold resv_ok in X |- *. destruct (s_resv st); [reflexivity| |exact I].
    exfalso. rewrite MSE in X. cbn in X. discriminate X.
  - exact Pfcsr.
  - reflexivity.
  - rewrite ev_E'_below; [exact (so_zero _ _ _ _ _ _ HS)|]. destruct NX as (_ & P & _). change (to_Z 0%uint63) with 0. lia.
  - subst R6. apply IMap.bst_remove. exact B4.
  - exact REGS.
  - intros k1 q1 k2 q2 H1 H2 NE K1' K2' W a X. destruct (F6 k1 q1 H1) as [_ G1]. destruct (F6 k2 q2 H2) as [_ G2].
    exact (Rg4_disjoint r0 Hr0 k1 q1 k2 q2 G1 G2 NE K1' K2' W a X).
  - eapply pub_of_regions. exact REGS.
  - exact Pfacts.
  - eapply (ops_hold_set_op OPS E' E' (s_ops st) HEAP_ID hargs _ (ms_mem ms) M' mo mo' (cg_find CG) (cg_count CG) Pops).
    + exact other_ops_hold.
    + exact HH.
  - assert (MAPH : map (den E') hargs = map (den E) hargs).
    { apply map_ext_in. intros u Hu. apply den_E'. destruct SVB_parts as (_ & _ & _ & _ & _ & OV).
      exact (forallb_In _ _ _ u (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) Hu). }
    eapply (ops_apart_set_op rsegs OPS E' E' (s_ops st) HEAP_ID hargs _ (s_regs st) R6 (s_priv st) (cg_find CG) (cg_count CG) Papart).
    + intros o a Ho NI IMP X. destruct (IMP X) as [NB' PR]. split; [| exact PR]. intros IB. exact (NB' (NEWB a IB)).
    + intros a X. rewrite OPS_fp1 in X. apply (proj1 (fp_spec IMGX _ _ _ _ _ a DEC')) in X as (Ra & NI & NWS).
      assert (OUTF : ~ (Af <= a < Af + nf) -> ~ in_ws (wins_of E n rest) a).
      { intros NA IW. apply NWS. unfold in_ws in IW |- *. rewrite WS in IW. rewrite map_app in IW |- *. cbn [map] in IW.
        apply (proj1 (in_ivs_app _ _ _)) in IW. apply (proj2 (in_ivs_app _ _ _)).
        destruct IW as [IW|IW]; [left; exact IW| right]. apply (proj1 (in_ivs_cons _ _ _)) in IW. destruct IW as [IW|IW]; [| exact IW].
        exfalso. unfold in_iv, w_iv in IW. cbn [fst snd w_lo w_len] in IW. lia. }
      assert (CASE : (Af <= a < Af + nf) \/ ~ in_ws (wins_of E n rest) a).
      { destruct (Z_lt_le_dec a Af) as [L|G]; [right; apply OUTF; lia|].
        destruct (Z_lt_le_dec a (Af + nf)) as [L2|G2]; [left; lia| right; apply OUTF; lia]. }
      destruct CASE as [INA|OLD].
      * split.
        -- intros (k & rg & H & K & R). destruct (F6 k rg H) as [NK H4']. rewrite <- (Uint63.eqb_false_spec k 0%uint63) in K || idtac.
           pose proof (Rg4_ranges r0 k rg Hr0 H4') as (rg' & F & L' & Mq & _). rewrite L', (Mq E') in R.
           destruct (reg_E' _ _ F) as (Ek & Eh & _). rewrite Ek, Eh in R.
           destruct (Uint63.eqb k STACK_ID) eqn:Q1.
           ++ apply Uint63.eqb_correct in Q1. subst k. rewrite (cg_r1 CG) in F. injection F as <-. pose proof (cg_ceil CG) as CE. unfold lo, base in *. lia.
           ++ apply Uint63.eqb_false_spec in Q1. assert (K' : k <> 0%uint63) by (apply Uint63.eqb_false_spec; exact K).
              assert (CL : rclient_addr LBg sp a).
              { apply (justified_client k rg' F K' Q1); [| exact R]. intros len kd b WL Hb POS SUB. exact (LIVE len kd b k WL NK Hb POS SUB). }
              destruct CL as [S1|[[I1 I2]|(blk & Hblk & Rb)]].
              ** pose proof (cg_ceil CG) as CE. pose proof (cg_room CG) as RM. pose proof (int_range need). unfold sp, lo, base in *. lia.
              ** unfold RIMG_LO, RIMG_HI in Bf4. lia.
              ** pose proof (HLBg _ Hblk) as Hblk'.
                 assert (NEb : blk_id (p, Af, nf) <> blk_id blk).
                 { cbn [blk_id fst]. intros X2. exact (LBGid blk Hblk (eq_sym X2)). }
                 destruct (RHEAP_core_blocks_disjoint s LBf (ms_mem ms) (p, Af, nf) blk RC INf Hblk' NEb) as [D|D];
                   unfold blk_addr, blk_size in D, Rb; cbn [fst snd] in D; lia.
        -- intros [seg Hs]. exfalso. rewrite ref_find_segment_none in Hs; [discriminate Hs| lia| unfold RIMG_LO, RIMG_HI in Bf4; lia].
      * assert (X' : Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E') hargs))).
        { rewrite OPS_fp1, MAPH. apply (proj2 (fp_spec IMGX _ _ _ _ _ a (cg_decode CG))). auto. }
        destruct (ops_apart_find rsegs OPS E' (s_ops st) (s_regs st) (s_priv st) HEAP_ID hargs a Papart (cg_find CG) X') as [NB' PR].
        split; [| exact PR]. intros IB. exact (NB' (NEWB a IB)).
  - apply (St.plain_minv _ _ OPS_plain). apply mfacts'.
  - intros xa _. apply St.plain_cover. exact OPS_plain.
  - exact minv'.
Qed.

Theorem post_FB : forall r0 kf rf lenf p Af nf a' hargs' l1 l2 nsv rlo rhi Ablk nZ junk stFB,
  IMap.find 0%uint63 (s_regs st) = Some r0 -> st4 = alloc_post_mk ERRNO LIBC GOT GUARD CANARY st r ksp r0 r1 ->
  IMap.find kf (s_regs st) = Some rf -> kf <> 0%uint63 -> kf <> STACK_ID ->
  free_ok st wnl kf = Some lenf ->
  In (p, Af, nf) LBf -> Af = bv_unsigned (ev E kf) -> nf = bv_unsigned (den E lenf) ->
  (forall b, In b LBf -> blk_id b <> p -> In b LBg) -> (forall b, In b LBg -> blk_id b <> p) ->
  wins_of E n rest = l1 ++ Win Af nf K_BLOCK :: l2 ->
  (forall w, In w (l1 ++ l2) -> w_kind w = K_STACK \/ exists k len kd, In (k, len, kd) wnl /\ k <> kf /\
                                  w = Win (bv_unsigned (ev E k)) (bv_unsigned (den E len)) (w2Z kd)) ->
  decode (map (den E') hargs') = Some (w2Z md, den E' a', (l1 ++ l2) ++ [Win Ablk nZ K_BLOCK], map (den E) (skipn (3 * n) rest)) ->
  sv_vars_below (s_next st) a' = true ->
  sv_vars_below (s_next st) nsv = true -> nZ = bv_unsigned (den E nsv) ->
  Fv 16 = Z_to_bv 64 Ablk -> (forall o, 0 <= o < nZ -> nth_error junk (Z.to_nat o) = Some (Gv 16 o)) ->
  rw_cells rsegs M' Ablk [CB (Z.to_nat nZ) junk] ->
  4096 <= Ablk -> Ablk + nZ <= alloc_ceiling -> Ablk mod 16 = 0 -> (Ablk + nZ <= RIMG_LO \/ RIMG_HI <= Ablk) ->
  w2Z rlo <= Ablk <= w2Z rhi ->
  (forall blk a, In blk LBg -> blk_addr blk <= a < blk_addr blk + blk_size blk -> ~ (Ablk <= a < Ablk + nZ)) ->
  aw_holdsI (den E a') ((Ablk, nZ) :: remove iv_eq_dec (Af, nf) LB) M' mo' ->
  PropExec.getr R' 10%bv = Z_to_bv 64 Ablk ->
  stFB = SS r (rf_set (s_rf (clobber st)) X10 (VP k16 wzero)) (s_ff st) (s_resv st)
            (IMap.add k16 (blk_region nsv) (IMap.remove kf (Rg4 r0)))
            (FULt nsv (VL two47) :: FAlign k16 4%uint63 :: FRange k16 rlo rhi :: s_facts st)
            (set_op HEAP_ID hargs' (s_ops st)) (s_priv st) (PrimInt63.add k16 1%uint63) ->
  St.st_ok rsegs OPS E' stFB ms' mo' /\ MP mo'.
Proof.
  intros r0 kf rf lenf p Af nf a' hargs' l1 l2 nsv rlo rhi Ablk nZ junk stFB Hr0 E4 Hkf K0 K1 FOK INf EAf Enf LBG LBGid WS PROV DEC' SVa
         SVn EN F16 GJ RW A4096 AC A16 AI FR NEW AWH Ha0 ->.
  split; [| exact MP'].
  pose proof HS' as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  pose proof (Rg4_bst r0) as B4. pose proof alloc_ceiling_lt64 as C64.
  pose proof (bv_unsigned_in_range 64 (den E nsv)) as RN. unfold bv_modulus in RN.
  pose proof (cg_rheap CG) as RH. apply RHEAP_split in RH as [RC _].
  pose proof (RHEAP_core_nodup s LBf (ms_mem ms) RC) as NDid.
  destruct (free_ok_inv st wnl kf lenf FOK) as (rf' & Hrf' & WLf & LOf & NEf & LEf & OTH). rewrite Hkf in Hrf'. injection Hrf' as <-.
  apply (known_ltu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in NEf. rewrite unsigned_VL in NEf. change (w2Z wzero) with 0 in NEf. fold (hiZ E rf) in NEf.
  apply (known_leu_q_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in LEf. fold (hiZ E rf) in LEf. rewrite <- Enf in LEf.
  assert (LZf : loZ rf = 0) by (unfold loZ; rewrite LOf; reflexivity).

  assert (EK : bv_unsigned (ev E' k16) = Ablk).
  { rewrite ev_k16, F16, Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. unfold W64.two64. lia. }
  assert (DK : den E' (VP k16 wzero) = Z_to_bv 64 Ablk) by (rewrite den_VPz, ev_k16; exact F16).
  assert (EH' : hiZ E' (blk_region nsv) = nZ). { unfold hiZ, blk_region. cbn [Mem.rg_hi]. rewrite (den_E' nsv SVn). symmetry. exact EN. }
  assert (EL0 : loZ (blk_region nsv) = 0) by reflexivity.
  assert (K160 : PrimInt63.eqb k16 0%uint63 = false).
  { apply Uint63.eqb_false_spec. intros X. pose proof k16_Z as KZ. rewrite X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NX as (_ & P & _). lia. }
  assert (KF : forall k rg, IMap.find k (s_regs st) = Some rg -> k <> k16).
  { intros k rg Hk ->. destruct (reg_E' _ _ Hk) as (_ & _ & LT & _). apply Uint63.ltb_spec in LT. rewrite k16_Z in LT. lia. }

  destruct (RHEAP_core_block_range s LBf (ms_mem ms) _ RC INf) as (Bf1 & Bf2 & Bf3 & Bf4 & _). cbn [blk_addr blk_size fst snd] in Bf1, Bf2, Bf3, Bf4.

  assert (FREED : forall k2 len2 kd2, In (k2, len2, kd2) wnl -> k2 <> kf ->
            (0 < bv_unsigned (den E len2)
             \/ (bv_unsigned (den E len2) = 0 /\ exists k3 len3, In (k3, len3, CtrLib.K_BLOCK) wnl /\ k3 <> kf)) /\
            forall a, bv_unsigned (ev E k2) <= a < bv_unsigned (ev E k2) + bv_unsigned (den E len2) -> ~ (Af <= a < Af + nf)).
  { intros k2 len2 kd2 I2 NK.
    destruct (OTH k2 len2 kd2 I2 NK) as (rg2 & Hk2 & LO2 & NE2' & LE2 & WW & FULL).
    apply (known_leu_q_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in LE2. fold (hiZ E rg2) in LE2.
    pose proof (bv_unsigned_in_range 64 (den E (Mem.rg_hi rg2))) as HR2. rewrite bv_modulus_64 in HR2. fold (hiZ E rg2) in HR2.
    assert (NE2 : 0 < hiZ E rg2 \/ (bv_unsigned (den E len2) = 0 /\ exists k3 len3, In (k3, len3, CtrLib.K_BLOCK) wnl /\ k3 <> kf)).
    { destruct NE2' as [NE2|(KNB & HEQ & OB)].
      - left. apply (known_ltu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in NE2. rewrite unsigned_VL in NE2. change (w2Z wzero) with 0 in NE2. fold (hiZ E rg2) in NE2. exact NE2.
      - destruct (Z_lt_le_dec 0 (hiZ E rg2)) as [POS2|Z2]; [left; exact POS2| right]. split; [| exact OB].
        apply (known_eq_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in HEQ. apply (f_equal bv_unsigned) in HEQ. fold (hiZ E rg2) in HEQ. lia. }
    assert (LZ2 : loZ rg2 = 0) by (unfold loZ; rewrite LO2; reflexivity).
    destruct (nonstack_windows_In E n rest wnl k2 len2 kd2 (cg_wnl CG) I2) as (K20 & K21 & KD2 & INW2).
    split; [destruct NE2 as [NE2|NE2]; [left; lia| right; exact NE2]|]. intros a Ha INA.
    destruct NE2 as [NE2|[Z2 _]]; [| lia].
    assert (DISJ := so_disj _ _ _ _ _ _ HS kf rf k2 rg2 Hkf Hk2 ltac:(congruence) ltac:(apply Uint63.eqb_false_spec; exact K0) ltac:(apply Uint63.eqb_false_spec; exact K20)
                     ltac:(destruct WW; [left|right]; assumption)).
    rewrite LZf, LZ2, <- EAf in DISJ.
    pose proof (proj1 (Forall_forall _ _) (cg_wf CG) _ INW2) as (_ & _ & _ & [[KS _]|[[KB B2]|[KS (b & Hb & SUB)]]]); cbn [w_kind w_lo w_len w_iv] in *.
    - exact (KD2 KS).
    - assert (B2' : In (bv_unsigned (ev E k2), bv_unsigned (den E len2)) (blocks_of LBf))
        by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact B2]).
      apply in_map_iff in B2' as (blk2 & Eb2 & Hblk2).
      destruct (bptr_eqb (blk_id blk2) p) eqn:BP.
      + apply bptr_eqb_true in BP. pose proof (blk_by_id LBf blk2 (p, Af, nf) NDid Hblk2 INf BP) as ->.
        cbn [blk_addr blk_size fst snd] in Eb2. injection Eb2 as EA2 EN2.
        apply (DISJ Af). rewrite <- EA2. lia.
      + assert (NEb : blk_id (p, Af, nf) <> blk_id blk2).
        { cbn [blk_id fst]. intros X. rewrite <- X in BP. rewrite (proj2 (bptr_eqb_true p p) eq_refl) in BP. discriminate BP. }
        pose proof (f_equal fst Eb2) as E1. pose proof (f_equal snd Eb2) as E2. unfold blk_addr, blk_size in E1, E2. cbn [fst snd] in E1, E2.
        destruct (RHEAP_core_blocks_disjoint s LBf (ms_mem ms) (p, Af, nf) blk2 RC INf Hblk2 NEb) as [D|D];
          unfold blk_addr, blk_size in D; cbn [fst snd] in D; lia.
    - assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
      apply in_map_iff in Hb' as (blk2 & Eb2 & Hblk2).
      destruct (bptr_eqb (blk_id blk2) p) eqn:BP.
      + apply bptr_eqb_true in BP. pose proof (blk_by_id LBf blk2 (p, Af, nf) NDid Hblk2 INf BP) as ->.
        cbn [blk_addr blk_size fst snd] in Eb2. subst b.
        destruct FULL as [KDB|FU]; [rewrite KDB in KS; unfold K_SUB in KS; change (w2Z CtrLib.K_BLOCK) with 1 in KS; lia|].
        apply (known_eq_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in FU. apply (f_equal bv_unsigned) in FU. fold (hiZ E rf) in FU. rewrite <- Enf in FU.
        assert (INK : in_iv (bv_unsigned (ev E k2), bv_unsigned (den E len2)) (bv_unsigned (ev E k2))) by (unfold in_iv; cbn [fst snd]; lia).
        specialize (SUB (bv_unsigned (ev E k2)) INK). unfold in_iv in SUB. cbn [fst snd] in SUB.
        apply (DISJ (bv_unsigned (ev E k2))). lia.
      + assert (NEb : blk_id (p, Af, nf) <> blk_id blk2).
        { cbn [blk_id fst]. intros X. rewrite <- X in BP. rewrite (proj2 (bptr_eqb_true p p) eq_refl) in BP. discriminate BP. }
        assert (INK : in_iv (bv_unsigned (ev E k2), bv_unsigned (den E len2)) a) by (unfold in_iv; cbn [fst snd]; lia).
        specialize (SUB a INK). unfold in_iv in SUB. rewrite <- Eb2 in SUB. unfold blk_addr, blk_size in SUB. cbn [fst snd] in SUB.
        destruct (RHEAP_core_blocks_disjoint s LBf (ms_mem ms) (p, Af, nf) blk2 RC INf Hblk2 NEb) as [D|D];
          unfold blk_addr, blk_size in D; cbn [fst snd] in D; lia. }
  set (R6 := IMap.remove kf (Rg4 r0)).
  assert (B6 : IMap.bst R6) by (subst R6; apply IMap.bst_remove; exact B4).
  assert (F6 : forall k rg, IMap.find k R6 = Some rg -> k <> kf /\ IMap.find k (Rg4 r0) = Some rg).
  { intros k rg H. subst R6. destruct (Uint63.eqb kf k) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_remove_same in H by exact B4. discriminate H.
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_remove_other in H by (exact B4 || exact Q). split; [congruence| exact H]. }
  set (R7 := IMap.add k16 (blk_region nsv) R6).
  assert (F7 : forall k rg, IMap.find k R7 = Some rg -> (k = k16 /\ rg = blk_region nsv) \/ (k <> k16 /\ IMap.find k R6 = Some rg)).
  { intros k rg H. subst R7. destruct (Uint63.eqb k16 k) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_add_same in H by exact B6. injection H as <-. left; auto.
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other in H by (exact B6 || exact Q). right. split; [congruence| exact H]. }

  assert (LIVE : forall len kd b k, win_lookup wnl k = Some (len, kd) -> k <> kf -> In b LB -> 0 < bv_unsigned (den E len) ->
            (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) ->
            exists blk, In blk LBg /\ (blk_addr blk, blk_size blk) = b).
  { intros len kd b k WL NK Hb POS SUB.
    assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
    apply in_map_iff in Hb' as (blk & Eb & Hblk). exists blk. split; [| exact Eb]. apply LBG; [exact Hblk|]. intros EQ.
    pose proof (blk_by_id LBf blk (p, Af, nf) NDid Hblk INf EQ) as ->. unfold blk_addr, blk_size in Eb. cbn [fst snd] in Eb. subst b.
    destruct (FREED k len kd (win_lookup_In _ _ _ _ WL) NK) as [_ FR'].
    assert (INK : in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) (bv_unsigned (ev E k))) by (unfold in_iv; cbn [fst snd]; lia).
    pose proof (SUB _ INK) as IB. unfold in_iv in IB. cbn [fst snd] in IB.
    exact (FR' (bv_unsigned (ev E k)) ltac:(lia) IB). }

  assert (NEWR : forall a k rg, Ablk <= a < Ablk + nZ -> IMap.find k R6 = Some rg -> PrimInt63.eqb k 0%uint63 = false ->
            ~ (bv_unsigned (ev E' k) + loZ rg <= a < bv_unsigned (ev E' k) + hiZ E' rg)).
  { intros a k rg Ha Hk6 K R. destruct (F6 k rg Hk6) as [NK Hk]. destruct (Rg4_ranges r0 k rg Hr0 Hk) as (rg' & F & L' & Mq & _). rewrite L', (Mq E') in R.
    destruct (reg_E' _ _ F) as (Ek & Eh & _). rewrite Ek, Eh in R.
    destruct (Uint63.eqb k STACK_ID) eqn:Q1.
    - apply Uint63.eqb_correct in Q1. subst k. rewrite (cg_r1 CG) in F. injection F as <-.
      pose proof (cg_ceil CG) as CE. unfold lo, base in *. lia.
    - apply Uint63.eqb_false_spec in Q1. apply Uint63.eqb_false_spec in K.
      assert (CL : rclient_addr LBg sp a).
      { apply (justified_client k rg' F K Q1); [| exact R]. intros len kd b WL Hb POS SUB. exact (LIVE len kd b k WL NK Hb POS SUB). }
      destruct CL as [S1|[[I1 I2]|(blk & Hblk & Rb)]].
      + pose proof (cg_ceil CG) as CE. pose proof (cg_room CG) as RM. pose proof (int_range need). unfold sp, lo, base in *. lia.
      + unfold RIMG_LO, RIMG_HI in AI. lia.
      + exact (NEW blk a Hblk Rb Ha). }
  assert (REGS : forall k rg, IMap.find k R7 = Some rg -> St.region_ok rsegs (s_priv st) E' M' k rg).
  { intros k rg H. destruct (F7 k rg H) as [[-> ->]|[NK16 H6]].
    - apply (blk_region_ok nsv Ablk nZ junk); try assumption. lia.
    - destruct (F6 k rg H6) as [NK H4']. destruct (Rg4_find r0 k rg Hr0 H4') as [[-> ->]|[[-> ->]|(K0' & K1' & F)]].
      + apply r0_ok. exact Hr0.
      + apply r1_ok.
      + apply (old_region_ok k rg F); [apply Uint63.eqb_false_spec; exact K0'|].
        apply (justified_client k rg F K0' K1'). intros len kd b WL Hb POS SUB. exact (LIVE len kd b k WL NK Hb POS SUB). }
  assert (NEWB7 : forall a, in_based E' R7 a -> (Ablk <= a < Ablk + nZ) \/ in_based E' R6 a).
  { intros a (k & rg & H & K & R). destruct (F7 k rg H) as [[-> ->]|[NK16 H6]].
    - left. rewrite EK, EH', EL0 in R. lia.
    - right. exists k, rg. auto. }
  assert (NEWB6 : forall a, in_based E' R6 a -> in_based E' (s_regs st) a).
  { intros a (k & rg & H & K & R). destruct (F6 k rg H) as [_ H4']. apply (Rg4_in_based r0 a Hr0). exists k, rg. auto. }
  assert (NEWB : forall a, in_based E' R7 a -> (Ablk <= a < Ablk + nZ) \/ in_based E' (s_regs st) a).
  { intros a IB. destruct (NEWB7 a IB) as [BL|IB6]; [left; exact BL| right; exact (NEWB6 a IB6)]. }

  pose proof (cg_wf CG) as WF. rewrite WS in WF.
  assert (WIN : forall w, In w (l1 ++ l2) -> In w (l1 ++ Win Af nf K_BLOCK :: l2)) by (intros w Hw; apply in_app_iff in Hw as [Hw|Hw]; apply in_app_iff; [left| right; right]; exact Hw).
  assert (NOTF : forall w, In w (l1 ++ l2) -> w <> Win Af nf K_BLOCK).
  { intros w Hw ->. destruct (PROV _ Hw) as [S|(k2 & len2 & kd2 & I2 & NK2 & EW)]; [cbn in S; unfold K_STACK, K_BLOCK in S; lia|].
    injection EW as EA2 EN2 _. destruct (FREED k2 len2 kd2 I2 NK2) as [_ FR']. apply (FR' Af); lia. }

  assert (NEWU : forall a, in_iv (Ablk, nZ) a -> ~ in_user (remove iv_eq_dec (Af, nf) LB) a).
  { intros a Ha U. unfold in_user in U. apply in_ivs_In in U as (b & Hb & Hin). apply in_remove in Hb as [Hb NEb0].
    assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
    apply in_map_iff in Hb' as (blk & Eb & Hblk).
    destruct (bptr_eqb (blk_id blk) p) eqn:BP.
    - apply bptr_eqb_true in BP. pose proof (blk_by_id LBf blk (p, Af, nf) NDid Hblk INf BP) as ->.
      unfold blk_addr, blk_size in Eb. cbn [fst snd] in Eb. exact (NEb0 (eq_sym Eb)).
    - assert (NEp : blk_id blk <> p) by (intros X; rewrite X, (proj2 (bptr_eqb_true p p) eq_refl) in BP; discriminate BP).
      unfold in_iv in Hin, Ha. rewrite <- Eb in Hin. cbn [fst snd] in Hin, Ha.
      exact (NEW blk a (LBG blk Hblk NEp) Hin Ha). }
  assert (HH : St.op_holds OPS HEAP_ID (map (den E') hargs') M' mo').
  { rewrite OPS_holds1. exists (w2Z md), (den E' a'), ((l1 ++ l2) ++ [Win Ablk nZ K_BLOCK]), (map (den E) (skipn (3 * n) rest)), ((Ablk, nZ) :: remove iv_eq_dec (Af, nf) LB).
    split; [exact DEC'|]. split; [apply aw_holdsW_intro; [rewrite (den_E' a' SVa); exact AWH| apply NG_app_block; apply (NG_incl _ _ (cg_ng CG)); intros w Hw; rewrite WS; exact (WIN w Hw)]|]. split.
    - apply Forall_app. split.
      + apply Forall_forall. intros w Hw.
        pose proof (proj1 (Forall_forall _ _) WF w (WIN w Hw)) as (W1 & W2 & W3 & ALT).
        split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
        destruct ALT as [[K S]|[[K B]|[K (b & Hb & SUB)]]]; [left; auto| right; left| right; right].
        * split; [exact K|]. right. apply in_in_remove; [| exact B]. intros EQ.
          destruct (PROV _ Hw) as [S|(k2 & len2 & kd2 & I2 & NK2 & ->)]; [rewrite K in S; unfold K_STACK, K_BLOCK in S; lia|].
          cbn [w_iv w_lo w_len] in EQ. injection EQ as EA2 EN2. destruct (FREED k2 len2 kd2 I2 NK2) as [_ FR']. apply (FR' Af); lia.
        * split; [exact K|].
          destruct (PROV _ Hw) as [S|(k2 & len2 & kd2 & I2 & NK2 & ->)]; [rewrite S in K; unfold K_STACK, K_SUB in K; lia|].
          cbn [w_iv w_lo w_len] in SUB. destruct (FREED k2 len2 kd2 I2 NK2) as [[POS|(Z0 & _)] FR'].
          -- exists b. split; [| exact SUB]. right. apply in_in_remove; [| exact Hb]. intros ->.
             assert (INK : in_iv (bv_unsigned (ev E k2), bv_unsigned (den E len2)) (bv_unsigned (ev E k2))) by (unfold in_iv; cbn [fst snd]; lia).
             pose proof (SUB _ INK) as IB. unfold in_iv in IB. cbn [fst snd] in IB. apply (FR' (bv_unsigned (ev E k2))); lia.
          --
             eexists. split; [left; reflexivity|]. intros a Ha. exfalso. unfold in_iv in Ha. cbn [w_iv w_lo w_len fst snd] in Ha. lia.
      + constructor; [| constructor]. split; [cbn [w_lo]; lia|]. split; [cbn [w_len]; lia|]. split; [cbn [w_lo w_len]; unfold two64; lia|].
        right; left. split; [reflexivity|]. left. reflexivity.
    - apply (cw_grow Cw). 2:{ exact NEWU. }
      apply (cw_free Cw (w2Z md) _ LB (l1 ++ Win Af nf K_BLOCK :: l2) M' Af nf (l1 ++ l2)).
      + apply (cw_frame Cw _ _ _ _ (ms_mem ms) M'); [rewrite <- WS; exact (cg_cw CG)|]. intros a Ha U NW.
        unfold in_user in U. apply in_ivs_In in U as (b & Hb & Hin).
        assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
        apply in_map_iff in Hb' as (blk & Eb & Hblk).
        destruct (bptr_eqb (blk_id blk) p) eqn:BP.
        * exfalso. apply bptr_eqb_true in BP. pose proof (blk_by_id LBf blk (p, Af, nf) NDid Hblk INf BP) as ->.
          unfold blk_addr, blk_size in Eb. cbn [fst snd] in Eb. subst b. apply NW. unfold in_ws, heap_ws. apply in_ivs_In.
          exists (Af, nf). split; [| exact Hin]. apply in_map_iff. exists (Win Af nf K_BLOCK). split; [reflexivity|].
          apply filter_In. split; [apply in_app_iff; right; left; reflexivity| reflexivity].
        * assert (NEp : blk_id blk <> p) by (intros X; rewrite X, (proj2 (bptr_eqb_true p p) eq_refl) in BP; discriminate BP).
          destruct (client_byte a ltac:(unfold two64 in Ha; lia)) as (E1 & _); [| unfold wa in E1; symmetry; exact E1].
          right; right. exists blk. split; [apply LBG; assumption|]. unfold in_iv in Hin. rewrite <- Eb in Hin. cbn [fst snd] in Hin. exact Hin.
      + apply in_app_iff. right. left. reflexivity.
      + intros w. split.
        * intros Hw. split; [exact (WIN w Hw)| exact (NOTF w Hw)].
        * intros [Hw NE]. apply in_app_iff in Hw. apply in_app_iff. destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw| exfalso; exact (NE (eq_sym Hw))| right; exact Hw]. }
  assert (MAPH : map (den E') hargs = map (den E) hargs).
  { apply map_ext_in. intros u Hu. apply den_E'. destruct SVB_parts as (_ & _ & _ & _ & _ & OV).
    exact (forallb_In _ _ _ u (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) Hu). }
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
  - reflexivity.
  - rewrite rf_get_set_other by discriminate. change (rf_get (s_rf (clobber st)) X0) with (getr (clobber st) X0). rewrite getr_clobber. cbn [clob_pos]. exact Px0.
  - apply post_regs. rewrite DK. symmetry. exact Ha0.
  - exact Pfregs.
  - reflexivity.
  - pose proof (cg_ms CG) as MSE. pose proof Presv as X. unfold resv_ok in X |- *. destruct (s_resv st); [reflexivity| |exact I].
    exfalso. rewrite MSE in X. cbn in X. discriminate X.
  - exact Pfcsr.
  - reflexivity.
  - rewrite ev_E'_below; [exact (so_zero _ _ _ _ _ _ HS)|]. destruct NX as (_ & P & _). change (to_Z 0%uint63) with 0. lia.
  - subst R7. apply IMap.bst_add. exact B6.
  - exact REGS.
  - intros k1 q1 k2 q2 H1 H2 NE K1' K2' W a [X1 X2].
    destruct (F7 k1 q1 H1) as [[-> ->]|[N1 G1]]; destruct (F7 k2 q2 H2) as [[-> ->]|[N2 G2]].
    + exact (NE eq_refl).
    + rewrite EK, EH', EL0 in X1. exact (NEWR a k2 q2 ltac:(lia) G2 K2' X2).
    + rewrite EK, EH', EL0 in X2. exact (NEWR a k1 q1 ltac:(lia) G1 K1' X1).
    + destruct (F6 k1 q1 G1) as [_ G1']. destruct (F6 k2 q2 G2) as [_ G2'].
      exact (Rg4_disjoint r0 Hr0 k1 q1 k2 q2 G1' G2' NE K1' K2' W a (conj X1 X2)).
  - eapply pub_of_regions. exact REGS.
  - constructor; [| constructor; [| constructor; [| exact Pfacts]]].
    + cbn [fact_holds]. rewrite (den_E' nsv SVn), <- EN, unsigned_VL. change (w2Z two47) with (2 ^ 47).
      pose_ceil. unfold CEIL_MIN, CEIL_MAX in *. lia.
    + cbn [fact_holds]. rewrite EK. change (2 ^ to_Z 4%uint63) with 16. exact A16.
    + cbn [fact_holds]. rewrite EK. exact FR.
  - eapply (ops_hold_set_op OPS E' E' (s_ops st) HEAP_ID hargs _ (ms_mem ms) M' mo mo' (cg_find CG) (cg_count CG) Pops).
    + exact other_ops_hold.
    + exact HH.
  - eapply (ops_apart_set_op rsegs OPS E' E' (s_ops st) HEAP_ID hargs _ (s_regs st) R7 (s_priv st) (cg_find CG) (cg_count CG) Papart).
    + intros o a Ho NI IMP X. destruct (IMP X) as [NB' PR]. split; [| exact PR]. intros IB.
      destruct (NEWB a IB) as [BL|OLD]; [| exact (NB' OLD)].
      unfold not_id in NI. apply Uint63.eqb_false_spec in NI. destruct (OPS_fp_other _ _ a NI X) as [RNG _]. unfold RIMG_LO, RIMG_HI in AI. lia.
    + intros a X. rewrite OPS_fp1 in X. apply (proj1 (fp_spec IMGX _ _ _ _ _ a DEC')) in X as (Ra & NI & NWS).
      assert (NOTNEW : ~ (Ablk <= a < Ablk + nZ)).
      { intros BL. apply NWS. unfold in_ws. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). right. cbn [map].
        apply (proj2 (in_ivs_cons _ _ _)). left. unfold in_iv, w_iv. cbn [fst snd w_lo w_len]. exact BL. }
      assert (OUTF : ~ (Af <= a < Af + nf) -> ~ in_ws (wins_of E n rest) a).
      { intros NA IW. apply NWS. unfold in_ws in IW |- *. rewrite WS in IW. rewrite !map_app in IW |- *. cbn [map] in IW.
        apply (proj1 (in_ivs_app _ _ _)) in IW. apply (proj2 (in_ivs_app _ _ _)). left. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)).
        destruct IW as [IW|IW]; [left; exact IW| right]. apply (proj1 (in_ivs_cons _ _ _)) in IW. destruct IW as [IW|IW]; [| exact IW].
        exfalso. unfold in_iv, w_iv in IW. cbn [fst snd w_lo w_len] in IW. lia. }
      assert (CASE : (Af <= a < Af + nf) \/ ~ in_ws (wins_of E n rest) a).
      { destruct (Z_lt_le_dec a Af) as [L|G]; [right; apply OUTF; lia|].
        destruct (Z_lt_le_dec a (Af + nf)) as [L2|G2]; [left; lia| right; apply OUTF; lia]. }
      destruct CASE as [INA|OLD].
      * split.
        -- intros IB7. destruct (NEWB7 a IB7) as [BL|(k & rg & H & K & R)]; [exact (NOTNEW BL)|].
           destruct (F6 k rg H) as [NK H4']. rewrite <- (Uint63.eqb_false_spec k 0%uint63) in K || idtac.
           pose proof (Rg4_ranges r0 k rg Hr0 H4') as (rg' & F & L' & Mq & _). rewrite L', (Mq E') in R.
           destruct (reg_E' _ _ F) as (Ek & Eh & _). rewrite Ek, Eh in R.
           destruct (Uint63.eqb k STACK_ID) eqn:Q1.
           ++ apply Uint63.eqb_correct in Q1. subst k. rewrite (cg_r1 CG) in F. injection F as <-. pose proof (cg_ceil CG) as CE. unfold lo, base in *. lia.
           ++ apply Uint63.eqb_false_spec in Q1. assert (K' : k <> 0%uint63) by (apply Uint63.eqb_false_spec; exact K).
              assert (CL : rclient_addr LBg sp a).
              { apply (justified_client k rg' F K' Q1); [| exact R]. intros len kd b WL Hb POS SUB. exact (LIVE len kd b k WL NK Hb POS SUB). }
              destruct CL as [S1|[[I1 I2]|(blk & Hblk & Rb)]].
              ** pose proof (cg_ceil CG) as CE. pose proof (cg_room CG) as RM. pose proof (int_range need). unfold sp, lo, base in *. lia.
              ** unfold RIMG_LO, RIMG_HI in Bf4. lia.
              ** pose proof (HLBg _ Hblk) as Hblk'.
                 assert (NEb : blk_id (p, Af, nf) <> blk_id blk).
                 { cbn [blk_id fst]. intros X2. exact (LBGid blk Hblk (eq_sym X2)). }
                 destruct (RHEAP_core_blocks_disjoint s LBf (ms_mem ms) (p, Af, nf) blk RC INf Hblk' NEb) as [D|D];
                   unfold blk_addr, blk_size in D, Rb; cbn [fst snd] in D; lia.
        -- intros [seg Hs]. exfalso. rewrite ref_find_segment_none in Hs; [discriminate Hs| lia| unfold RIMG_LO, RIMG_HI in Bf4; lia].
      * assert (X' : Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E') hargs))).
        { rewrite OPS_fp1, MAPH. apply (proj2 (fp_spec IMGX _ _ _ _ _ a (cg_decode CG))). auto. }
        destruct (ops_apart_find rsegs OPS E' (s_ops st) (s_regs st) (s_priv st) HEAP_ID hargs a Papart (cg_find CG) X') as [NB' PR].
        split; [| exact PR]. intros IB. destruct (NEWB a IB) as [BL|OLD']; [exact (NOTNEW BL)| exact (NB' OLD')].
  - apply (St.plain_minv _ _ OPS_plain). apply mfacts'.
  - intros xa _. apply St.plain_cover. exact OPS_plain.
  - exact minv'.
Qed.

End POST.

Definition Fv_of (R' : bvmap 5 word) (e a : word) (i : Z) : word :=
  nth (Z.to_nat i)
      [PropExec.getr R' 1%bv; PropExec.getr R' 5%bv; PropExec.getr R' 6%bv; PropExec.getr R' 7%bv;
       PropExec.getr R' 11%bv; PropExec.getr R' 12%bv; PropExec.getr R' 13%bv; PropExec.getr R' 14%bv;
       PropExec.getr R' 15%bv; PropExec.getr R' 16%bv; PropExec.getr R' 17%bv;
       PropExec.getr R' 28%bv; PropExec.getr R' 29%bv; PropExec.getr R' 30%bv; PropExec.getr R' 31%bv; e; a]
      (Z_to_bv 64 0).

Lemma Fv_of_clob : forall R' e a x i, clob_pos x = Some i -> Fv_of R' e a (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x).
Proof.
  intros R' e a x i H. destruct x; cbn in H; try discriminate; injection H as <-; cbn; f_equal; apply bv_eq; reflexivity.
Qed.
Lemma Fv_of_15 : forall R' e a, Fv_of R' e a 15 = e. Proof. reflexivity. Qed.
Lemma Fv_of_16 : forall R' e a, Fv_of R' e a 16 = a. Proof. reflexivity. Qed.

Definition Gv_of (junk : list byte) (i : Z) (o : Z) : byte := nth (Z.to_nat o) junk (Z_to_bv 8 0).

Lemma size_ok_sound : forall E fs v, facts_hold E fs -> size_ok fs v = true -> 0 < bv_unsigned (den E v) < 2 ^ 48.
Proof.
  intros E fs v Hfs H. unfold size_ok in H. apply andb_prop in H as [H1 H2].
  apply (known_ltu_sound E _ _ _ Hfs) in H1. apply (known_ltu_sound E _ _ _ Hfs) in H2.
  rewrite unsigned_VL in H1, H2. change (w2Z wzero) with 0 in H1. change (w2Z size_lim) with (2 ^ 48) in H2. lia.
Qed.
Lemma size_ok32_sound : forall E fs v, facts_hold E fs -> size_ok32 fs v = true -> 0 < bv_unsigned (den E v) < 2 ^ 32.
Proof.
  intros E fs v Hfs H. unfold size_ok32 in H. apply andb_prop in H as [H1 H2].
  apply (known_ltu_sound E fs) in H1; [| exact Hfs]. apply (known_ltu_sound E fs) in H2; [| exact Hfs].
  rewrite unsigned_VL in H1, H2. change (w2Z wzero) with 0 in H1. change (w2Z two32) with (2 ^ 32) in H2. lia.
Qed.

Lemma heap_drop_A_eq : forall md A nw rest, heap_drop_A (VL md :: A :: VL nw :: rest) = Some (VL md :: VL wones :: VL nw :: rest).
Proof. reflexivity. Qed.

Lemma cw_post : forall LBf LB SP M M' md ca ws, Permutation (blocks_of LBf) LB -> rheap_pres LBf SP M M' ->
  cw_holds Cw md ca LB ws M -> cw_holds Cw md ca LB ws M'.
Proof.
  intros LBf LB SP M M' md ca ws P PR HC. apply (cw_frame Cw md ca LB ws M M' HC). intros a Ha U _.
  unfold in_user in U. apply in_ivs_In in U as (b & Hb & Hin).
  assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact P| exact Hb]).
  apply in_map_iff in Hb' as (blk & Eb & Hblk). unfold in_iv in Hin. rewrite <- Eb in Hin. cbn [fst snd] in Hin.
  destruct (PR a ltac:(unfold two64 in Ha; lia) ltac:(right; right; exists blk; split; [exact Hblk| exact Hin])) as [E1 _].
  unfold wa in E1. symmetry. exact E1.
Qed.

Lemma repl_post : forall LBf SP M M', rheap_pres LBf SP M M' -> rw_cells rsegs M RMREPL [C4 (wz 0)] -> rw_cells rsegs M' RMREPL [C4 (wz 0)].
Proof.
  intros LBf SP M M' PR RC. eapply rheap_pres_rw_cells; [exact PR| exact RC|]. right; left. cbn [cells_size csize Nat.add].
  unfold RMREPL, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia.
Qed.

Theorem malloc_s_sound : forall pc, to_Z pc = RMALLOC_SYM ->
  contract_sound rsegs OPS MP PB (malloc_s_c rsegs ERRNO LIBC GOT GUARD TP CANARY pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply malloc_s_c] in Happ. unfold malloc_s_apply in Happ.
  destruct (alloc_call rsegs ERRNO LIBC GOT GUARD TP CANARY ALLOC_STACK st) as [[[[r ksp] hargs0] wnl]|] eqn:AC; [|discriminate].
  destruct (alloc_call_sound Cw OPS OPS_plain OPS_holds1 PB CANARY PB_canary PB_secret E st ms mo ALLOC_STACK r ksp hargs0 wnl HS HPB ltac:(vm_compute; reflexivity) AC)
    as (off & r1 & n & md & A & nw & rest & s & LBf & LB & CG).
  pose proof (cg_hargs CG) as EH. rewrite EH, heap_drop_A_eq in Happ.
  destruct (size_ok (s_facts st) (getr st X10)) eqn:SZ; [|discriminate].
  unfold malloc_posts, malloc_posts_rg in Happ.
  destruct (alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp) as [st4|] eqn:H4; [|discriminate].
  cbn [block_posts] in Happ.
  destruct (block_post st4 (VL md :: VL wones :: VL nw :: rest) (getr st X10) (BLK_LO, BLK_HI)) as [stB|] eqn:HB; [|discriminate].
  apply Some_inj in Happ. subst sts.
  pose proof (size_ok_sound E _ _ (so_facts _ _ _ _ _ _ HS) SZ) as NZ. set (nZ := bv_unsigned (den E (getr st X10))) in *.
  pose proof (cg_nw CG) as (T & N & L).
  assert (SVn : sv_vars_below (s_next st) (getr st X10) = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB.
    do 5 (apply andb_prop in SVB as [SVB ?]). exact (rf_allb_get _ _ _ SVB X10). }
  assert (AVB : forallb (sv_vars_below (s_next st)) rest = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB. apply andb_prop in SVB as [_ OV].
    pose proof (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) as AV. rewrite EH in AV. cbn [op_args forallb] in AV.
    apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. exact AV. }

  pose proof (cg_ms CG) as MSE. rewrite Hspc in MSE. cbn [c_pc malloc_s_c] in MSE. rewrite Hpc in MSE. rewrite MSE.
  pose proof (cg_stk CG) as STK. pose proof (cg_room CG) as ROOM. pose proof (cg_hi CG) as HI. pose proof (cg_ceil CG) as CE.
  pose proof (int_range ALLOC_STACK) as RAS. change (to_Z ALLOC_STACK) with 8192 in ROOM, RAS.
  destruct (stk_split rsegs (ms_mem ms) _ (bv_unsigned (ev E STACK_ID) + keyZ ksp) _ STK ltac:(lia)) as [STK1 _].
  destruct (cg_errno CG) as [errv ERR].
  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 nZ).
  { subst nZ. rewrite <- reg_of_X10, (cg_regs CG X10). symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (cg_sp CG) as SP.
  apply (malloc_silent_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo s LBf nZ
           (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + keyZ ksp) errv K
           A0 ltac:(lia) (cg_tp CG) (cg_ra CG) (cg_rheap CG) (cg_krel CG) (cg_auxv CG) ltac:(rewrite SP; lia)
           ltac:(rewrite SP; exact STK1) CE ltac:(rewrite SP; unfold RMALLOC_STACK; lia) ERR (cg_minv CG) (cg_mo CG)).
  -
    intros R' M' mo' s' errv' GP MPATH MTR Ha0 ERR' RH' KR'. apply RHEAP_split in RH' as [RC' PU'].
    set (Fv := Fv_of R' errv' (Z_to_bv 64 0)). set (Gv := Gv_of []).
    assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
    assert (DECN : decode (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest)) = Some (w2Z md, wbv wones, wins_of E n rest, map (den E) (skipn (3 * n) rest))).
    { rewrite (decode_hargs (E' E st Fv Gv) md (VL wones) nw rest n T N L), (wins_of_E' E st Fv Gv n rest AVB), den_VL. f_equal. f_equal.
      apply map_ext_in. intros u Hu. apply (den_E' E st Fv Gv). apply (forallb_In _ _ _ u AVB).
      rewrite <- (firstn_skipn (3 * n) rest). apply in_app_iff. right. exact Hu. }
    assert (HH : St.op_holds OPS HEAP_ID (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest)) M' mo').
    { rewrite OPS_holds1. exists (w2Z md), (wbv wones), (wins_of E n rest), (map (den E) (skipn (3 * n) rest)), LB.
      split; [exact DECN|]. split; [| split; [exact (cg_wf CG)| exact (cw_post LBf LB _ _ _ _ _ _ (cg_perm CG) (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_cw CG))]].
      apply aw_holdsW_intro; [| exact (cg_ng CG)]. exists s', LBf. split; [exact (cg_perm CG)|]. split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
      split; [apply pclaim_none; rewrite wbv_unsigned; change (w2Z wones) with (2 ^ 64 - 1); lia|].
      exact (repl_post LBf _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG)). }
    assert (FP : forall a, Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest))) ->
                           Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E) hargs0))).
    { intros a X. rewrite OPS_fp1 in X |- *. unfold heap_fp in X |- *. rewrite DECN in X. rewrite (cg_decode CG). exact X. }
    destruct (post_N E st ms mo ALLOC_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP ERR' PU' Fv Gv HF
                (Fv_of_15 _ _ _) st4 H4 (VL wzero) (VL md :: VL wones :: VL nw :: rest) (fun b H => H)
                ltac:(rewrite den_VL, Ha0; reflexivity) HH FP) as [ST MP'].
    rewrite (cg_ra_r CG). exact (HK _ (or_introl eq_refl) _ _ _ (EXT E st Fv Gv) MP' ST).
  -
    intros R' M' mo' s' errv' p Ab junk GP MPATH MTR Ha0 ERR' RNG CELLS EXP RH' KR'. apply RHEAP_split in RH' as [RC' PU'].
    destruct RNG as (Apos & A16 & Nn & AC' & AI).
    set (Fv := Fv_of R' errv' (Z_to_bv 64 Ab)). set (Gv := Gv_of junk).
    assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
    destruct (RHEAP_core_block_range s' ((p, Ab, nZ) :: LBf) M' (p, Ab, nZ) RC' (or_introl eq_refl)) as (B4096 & _). cbn [blk_addr fst snd] in B4096.
    pose proof (RHEAP_core_nodup s' _ M' RC') as ND. cbn [map blk_id fst] in ND. apply List.NoDup_cons_iff in ND as [NI ND'].
    assert (NEW : forall b a, In b LB -> in_iv b a -> ~ (Ab <= a < Ab + nZ)).
    { intros b a Hb Hin R5.
      assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
      apply in_map_iff in Hb' as (blk & Eb & Hblk).
      assert (NEb : blk_id (p, Ab, nZ) <> blk_id blk).
      { cbn [blk_id fst]. intros X. apply NI. rewrite X. apply in_map_iff. exists blk. auto. }
      destruct (RHEAP_core_blocks_disjoint s' _ M' (p, Ab, nZ) blk RC' (or_introl eq_refl) (or_intror Hblk) NEb) as [D|D];
        unfold in_iv in Hin; rewrite <- Eb in Hin; unfold blk_addr, blk_size in D, Hin; cbn [fst snd] in D, Hin; lia. }
    assert (LJ : length junk = Z.to_nat nZ) by (destruct CELLS as [[[LJ _] _] _]; exact LJ).
    assert (GJ : forall o, 0 <= o < nZ -> nth_error junk (Z.to_nat o) = Some (Gv 16 o)).
    { intros o Ho. unfold Gv, Gv_of. apply nth_error_nth'. rewrite LJ. lia. }
    assert (AWH : aw_holdsI (den E (VL wones)) ((Ab, nZ) :: LB) M' mo').
    { exists s', ((p, Ab, nZ) :: LBf). split; [cbn [blocks_of map blk_addr blk_size fst snd]; apply perm_skip; exact (cg_perm CG)|].
      split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
      split; [apply pclaim_none; rewrite den_VL, wbv_unsigned; change (w2Z wones) with (2 ^ 64 - 1); lia|].
      exact (repl_post LBf _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG)). }
    pose proof alloc_ceiling_lt47 as C47.
    destruct (post_B E st ms mo ALLOC_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP (fun b H => H) ERR' PU' Fv Gv HF
                (Fv_of_15 _ _ _) st4 H4 (VL md :: VL wones :: VL nw :: rest) (VL wones) (getr st X10) BLK_LO BLK_HI stB Ab nZ junk
                eq_refl HB SVn eq_refl eq_refl (Fv_of_16 _ _ _) GJ CELLS B4096 AC' A16 ltac:(unfold RIMG_LO, RIMG_HI; lia)
                ltac:(change (w2Z BLK_LO) with 4096; change (w2Z BLK_HI) with (2 ^ 47 - 1); lia) NEW (fun b H => H) AWH Ha0) as [ST MP'].
    rewrite (cg_ra_r CG). exact (HK _ (or_intror (or_introl eq_refl)) _ _ _ (EXT E st Fv Gv) MP' ST).
Qed.

Theorem aligned_alloc_sound : forall IMG_HI pc, to_Z IMG_HI = RIMG_HI -> to_Z pc = RALIGNED16_SYM ->
  contract_sound rsegs OPS MP PB (aligned_alloc_c rsegs ERRNO LIBC GOT GUARD TP CANARY IMG_HI pc).
Proof.
  intros IMG_HI pc HIMG Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply aligned_alloc_c] in Happ. unfold aligned_alloc_apply in Happ.
  destruct (alloc_call rsegs ERRNO LIBC GOT GUARD TP CANARY ALIGNED_STACK st) as [[[[r ksp] hargs0] wnl]|] eqn:AC; [|discriminate].
  destruct (getr st X10) as [al| | | | | | | | | |] eqn:HX10; try discriminate.
  destruct (alloc_call_sound Cw OPS OPS_plain OPS_holds1 PB CANARY PB_canary PB_secret E st ms mo ALIGNED_STACK r ksp hargs0 wnl HS HPB ltac:(vm_compute; reflexivity) AC)
    as (off & r1 & n & md & A & nw & rest & s & LBf & LB & CG).
  pose proof (cg_hargs CG) as EH. rewrite EH, heap_drop_A_eq in Happ.
  destruct (weqb al (wlit 16%uint63)) eqn:AL; [|discriminate]. apply weqb_eq in AL. subst al.
  destruct (size_ok (s_facts st) (getr st X11)) eqn:SZ; [|discriminate]. cbn [andb] in Happ.
  unfold malloc_posts_rg in Happ.
  destruct (alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp) as [st4|] eqn:H4; [|discriminate].
  cbn [block_posts] in Happ.
  destruct (block_post st4 (VL md :: VL wones :: VL nw :: rest) (getr st X11) (BLK_LO, wsub IMG_LO wone)) as [stB1|] eqn:HB1; [|discriminate].
  destruct (block_post st4 (VL md :: VL wones :: VL nw :: rest) (getr st X11) (wlit IMG_HI, BLK_HI)) as [stB2|] eqn:HB2; [|discriminate].
  apply Some_inj in Happ. subst sts.
  pose proof (size_ok_sound E _ _ (so_facts _ _ _ _ _ _ HS) SZ) as NZ. set (nZ := bv_unsigned (den E (getr st X11))) in *.
  pose proof (cg_nw CG) as (T & N & L).
  assert (SVn : sv_vars_below (s_next st) (getr st X11) = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB.
    do 5 (apply andb_prop in SVB as [SVB ?]). exact (rf_allb_get _ _ _ SVB X11). }
  assert (AVB : forallb (sv_vars_below (s_next st)) rest = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB. apply andb_prop in SVB as [_ OV].
    pose proof (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) as AV. rewrite EH in AV. cbn [op_args forallb] in AV.
    apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. exact AV. }
  pose proof (cg_ms CG) as MSE. rewrite Hspc in MSE. cbn [c_pc aligned_alloc_c] in MSE. rewrite Hpc in MSE. rewrite MSE.
  pose proof (cg_stk CG) as STK. pose proof (cg_room CG) as ROOM. pose proof (cg_hi CG) as HI. pose proof (cg_ceil CG) as CE.
  pose proof (int_range ALIGNED_STACK) as RAS. change (to_Z ALIGNED_STACK) with 8224 in ROOM, RAS.
  destruct (stk_split rsegs (ms_mem ms) _ (bv_unsigned (ev E STACK_ID) + keyZ ksp) _ STK ltac:(lia)) as [STK1 _].
  destruct (cg_errno CG) as [errv ERR].
  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 16).
  { rewrite <- reg_of_X10, (cg_regs CG X10), HX10, den_VL. reflexivity. }
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 nZ).
  { subst nZ. rewrite <- reg_of_X11, (cg_regs CG X11). symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (cg_sp CG) as SP.
  apply (aligned16_silent_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo s LBf nZ
           (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + keyZ ksp) errv K
           A0 A1 ltac:(lia) (cg_tp CG) (cg_ra CG) (cg_rheap CG) (cg_krel CG) (cg_auxv CG) ltac:(rewrite SP; lia)
           ltac:(rewrite SP; exact STK1) CE ltac:(rewrite SP; unfold RALIGNED16_STACK, RMALLOC_STACK; lia) ERR (cg_minv CG) (cg_repl CG) (cg_mo CG)).
  -
    intros R' M' mo' s' errv' GP MPATH MTR Ha0 ERR' RH' KR'. apply RHEAP_split in RH' as [RC' PU'].
    set (Fv := Fv_of R' errv' (Z_to_bv 64 0)). set (Gv := Gv_of []).
    assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
    assert (DECN : decode (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest)) = Some (w2Z md, wbv wones, wins_of E n rest, map (den E) (skipn (3 * n) rest))).
    { rewrite (decode_hargs (E' E st Fv Gv) md (VL wones) nw rest n T N L), (wins_of_E' E st Fv Gv n rest AVB), den_VL. f_equal. f_equal.
      apply map_ext_in. intros u Hu. apply (den_E' E st Fv Gv). apply (forallb_In _ _ _ u AVB).
      rewrite <- (firstn_skipn (3 * n) rest). apply in_app_iff. right. exact Hu. }
    assert (HH : St.op_holds OPS HEAP_ID (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest)) M' mo').
    { rewrite OPS_holds1. exists (w2Z md), (wbv wones), (wins_of E n rest), (map (den E) (skipn (3 * n) rest)), LB.
      split; [exact DECN|]. split; [| split; [exact (cg_wf CG)| exact (cw_post LBf LB _ _ _ _ _ _ (cg_perm CG) (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_cw CG))]].
      apply aw_holdsW_intro; [| exact (cg_ng CG)]. exists s', LBf. split; [exact (cg_perm CG)|]. split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
      split; [apply pclaim_none; rewrite wbv_unsigned; change (w2Z wones) with (2 ^ 64 - 1); lia|].
      exact (repl_post LBf _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG)). }
    assert (FP : forall a, Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest))) ->
                           Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E) hargs0))).
    { intros a X. rewrite OPS_fp1 in X |- *. unfold heap_fp in X |- *. rewrite DECN in X. rewrite (cg_decode CG). exact X. }
    destruct (post_N E st ms mo ALIGNED_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP ERR' PU' Fv Gv HF
                (Fv_of_15 _ _ _) st4 H4 (VL wzero) (VL md :: VL wones :: VL nw :: rest) (fun b H => H)
                ltac:(rewrite den_VL, Ha0; reflexivity) HH FP) as [ST MP'].
    rewrite (cg_ra_r CG). exact (HK _ (or_introl eq_refl) _ _ _ (EXT E st Fv Gv) MP' ST).
  -
    intros R' M' mo' s' errv' p Ab junk GP MPATH MTR Ha0 ERR' RNG CELLS EXP RH' KR'. apply RHEAP_split in RH' as [RC' PU'].
    destruct RNG as (Apos & A16 & Nn & AC' & AI).
    set (Fv := Fv_of R' errv' (Z_to_bv 64 Ab)). set (Gv := Gv_of junk).
    assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
    destruct (RHEAP_core_block_range s' ((p, Ab, nZ) :: LBf) M' (p, Ab, nZ) RC' (or_introl eq_refl)) as (B4096 & _). cbn [blk_addr fst snd] in B4096.
    pose proof (RHEAP_core_nodup s' _ M' RC') as ND. cbn [map blk_id fst] in ND. apply List.NoDup_cons_iff in ND as [NI ND'].
    assert (NEW : forall b a, In b LB -> in_iv b a -> ~ (Ab <= a < Ab + nZ)).
    { intros b a Hb Hin R5.
      assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
      apply in_map_iff in Hb' as (blk & Eb & Hblk).
      assert (NEb : blk_id (p, Ab, nZ) <> blk_id blk).
      { cbn [blk_id fst]. intros X. apply NI. rewrite X. apply in_map_iff. exists blk. auto. }
      destruct (RHEAP_core_blocks_disjoint s' _ M' (p, Ab, nZ) blk RC' (or_introl eq_refl) (or_intror Hblk) NEb) as [D|D];
        unfold in_iv in Hin; rewrite <- Eb in Hin; unfold blk_addr, blk_size in D, Hin; cbn [fst snd] in D, Hin; lia. }
    assert (LJ : length junk = Z.to_nat nZ) by (destruct CELLS as [[[LJ _] _] _]; exact LJ).
    assert (GJ : forall o, 0 <= o < nZ -> nth_error junk (Z.to_nat o) = Some (Gv 16 o)).
    { intros o Ho. unfold Gv, Gv_of. apply nth_error_nth'. rewrite LJ. lia. }
    assert (AWH : aw_holdsI (den E (VL wones)) ((Ab, nZ) :: LB) M' mo').
    { exists s', ((p, Ab, nZ) :: LBf). split; [cbn [blocks_of map blk_addr blk_size fst snd]; apply perm_skip; exact (cg_perm CG)|].
      split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
      split; [apply pclaim_none; rewrite den_VL, wbv_unsigned; change (w2Z wones) with (2 ^ 64 - 1); lia|].
      exact (repl_post LBf _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG)). }
    pose proof alloc_ceiling_lt47 as C47.
    destruct AI as [LOW|HIGH].
    + destruct (post_B E st ms mo ALIGNED_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP (fun b H => H) ERR' PU' Fv Gv HF
                  (Fv_of_15 _ _ _) st4 H4 (VL md :: VL wones :: VL nw :: rest) (VL wones) (getr st X11) BLK_LO (wsub IMG_LO wone) stB1 Ab nZ junk
                  eq_refl HB1 SVn eq_refl eq_refl (Fv_of_16 _ _ _) GJ CELLS B4096 AC' A16 ltac:(unfold RIMG_LO, RIMG_HI; lia)
                  ltac:(change (w2Z BLK_LO) with 4096; change (w2Z (wsub IMG_LO wone)) with 65535; lia) NEW (fun b H => H) AWH Ha0) as [ST MP'].
      rewrite (cg_ra_r CG). exact (HK _ (or_intror (or_introl eq_refl)) _ _ _ (EXT E st Fv Gv) MP' ST).
    + destruct (post_B E st ms mo ALIGNED_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP (fun b H => H) ERR' PU' Fv Gv HF
                  (Fv_of_15 _ _ _) st4 H4 (VL md :: VL wones :: VL nw :: rest) (VL wones) (getr st X11) (wlit IMG_HI) BLK_HI stB2 Ab nZ junk
                  eq_refl HB2 SVn eq_refl eq_refl (Fv_of_16 _ _ _) GJ CELLS B4096 AC' A16 ltac:(unfold RIMG_LO, RIMG_HI; lia)
                  ltac:(rewrite wlit_ok, HIMG; change (w2Z BLK_HI) with (2 ^ 47 - 1); unfold RIMG_HI in *; lia) NEW (fun b H => H) AWH Ha0) as [ST MP'].
      rewrite (cg_ra_r CG). exact (HK _ (or_intror (or_intror (or_introl eq_refl))) _ _ _ (EXT E st Fv Gv) MP' ST).
Qed.

Theorem free_sound : forall pc, to_Z pc = RFREE_SYM ->
  contract_sound rsegs OPS MP PB (free_c rsegs ERRNO LIBC GOT GUARD TP CANARY pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply free_c] in Happ. unfold free_apply in Happ.
  destruct (alloc_call rsegs ERRNO LIBC GOT GUARD TP CANARY ALLOC_STACK st) as [[[[r ksp] hargs0] wnl]|] eqn:AC; [|discriminate].
  destruct (alloc_call_sound Cw OPS OPS_plain OPS_holds1 PB CANARY PB_canary PB_secret E st ms mo ALLOC_STACK r ksp hargs0 wnl HS HPB ltac:(vm_compute; reflexivity) AC)
    as (off & r1 & n & md & A & nw & rest & s & LBf & LB & CG).
  pose proof (cg_hargs CG) as EH. rewrite EH, heap_A_eq in Happ.
  destruct A as [a| | | | | | | | | |]; try discriminate.
  pose proof (cg_nw CG) as (T & N & L).
  assert (AVB : forallb (sv_vars_below (s_next st)) rest = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB. apply andb_prop in SVB as [_ OV].
    pose proof (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) as AV. rewrite EH in AV. cbn [op_args forallb] in AV.
    apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. exact AV. }
  pose proof (cg_ms CG) as MSE. rewrite Hspc in MSE. cbn [c_pc free_c] in MSE. rewrite Hpc in MSE. rewrite MSE.
  pose proof (cg_stk CG) as STK. pose proof (cg_room CG) as ROOM. pose proof (cg_hi CG) as HI. pose proof (cg_ceil CG) as CE.
  pose proof (int_range ALLOC_STACK) as RAS. change (to_Z ALLOC_STACK) with 8192 in ROOM, RAS.
  destruct (stk_split rsegs (ms_mem ms) _ (bv_unsigned (ev E STACK_ID) + keyZ ksp) _ STK ltac:(lia)) as [STK1 _].
  destruct (cg_errno CG) as [errv ERR]. pose proof (cg_sp CG) as SP.
  pose proof (fresh_ok_inv st (cg_fresh CG)) as (_ & NXpos & NX256).
  assert (K16 : to_Z (s_next st) + to_Z 16%uint63 < wB) by (change (to_Z 16%uint63) with 16; rewrite wB_two63, two63_eq; lia).
  destruct (getr st X10) as [w|kf o| | | | | | | | |] eqn:HX10; try discriminate.
  -
    destruct (weqb w wzero && is_lib a) eqn:C; [|discriminate]. apply andb_prop in C as [W0 LIB]. apply weqb_eq in W0. subst w.
    destruct (alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp) as [st4|] eqn:H4; [|discriminate].
    unfold fresh in Happ. cbn [fst snd] in Happ. apply Some_inj in Happ. subst sts.
    destruct (alloc_post_inv st r ksp st4 r1 (cg_r1 CG) H4) as (r0 & Hr0 & E4).
    assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 0).
    { rewrite <- reg_of_X10, (cg_regs CG X10), HX10, den_VL. reflexivity. }
    apply realizes_to_mkR. unfold mkR_of.
    eapply (evt_realizes rsegs _ _ mo K).
    + apply (rfree_null_spec (PropExec.getr (ms_regs ms) 1%bv)). exact A0.
    + exact (mo_ok_halted _ (cg_mo CG)).
    + exact (mo_ok_lazy _ (cg_mo CG)).
    + intros ms' ->.
      set (R' := mkR (PropExec.getr (ms_regs ms) 1%bv) (PropExec.getr (ms_regs ms) 2%bv) (PropExec.getr (ms_regs ms) 3%bv) (PropExec.getr (ms_regs ms) 4%bv)
                     (PropExec.getr (ms_regs ms) 5%bv) (PropExec.getr (ms_regs ms) 6%bv) (PropExec.getr (ms_regs ms) 7%bv) (PropExec.getr (ms_regs ms) 8%bv)
                     (PropExec.getr (ms_regs ms) 9%bv) (PropExec.getr (ms_regs ms) 10%bv) (PropExec.getr (ms_regs ms) 11%bv) (PropExec.getr (ms_regs ms) 12%bv)
                     (PropExec.getr (ms_regs ms) 13%bv) (PropExec.getr (ms_regs ms) 14%bv) (PropExec.getr (ms_regs ms) 15%bv) (PropExec.getr (ms_regs ms) 16%bv)
                     (PropExec.getr (ms_regs ms) 17%bv) (PropExec.getr (ms_regs ms) 18%bv) (PropExec.getr (ms_regs ms) 19%bv) (PropExec.getr (ms_regs ms) 20%bv)
                     (PropExec.getr (ms_regs ms) 21%bv) (PropExec.getr (ms_regs ms) 22%bv) (PropExec.getr (ms_regs ms) 23%bv) (PropExec.getr (ms_regs ms) 24%bv)
                     (PropExec.getr (ms_regs ms) 25%bv) (PropExec.getr (ms_regs ms) 26%bv) (PropExec.getr (ms_regs ms) 27%bv) (PropExec.getr (ms_regs ms) 28%bv)
                     (PropExec.getr (ms_regs ms) 29%bv) (PropExec.getr (ms_regs ms) 30%bv) (PropExec.getr (ms_regs ms) 31%bv)).
      rewrite (cg_ra CG), (cg_ra_r CG).
      set (Fv := Fv_of R' errv (PropExec.getr R' 10%bv)). set (Gv := Gv_of []).
      assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
      assert (GP : gpost (ms_regs ms) (ms_mem ms) mo LBf (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + keyZ ksp) R' (ms_mem ms) mo).
      { constructor.
        - intros x Hx. subst R'. apply kept_mkR. exact Hx.
        - exact (cg_minv CG).
        - rewrite SP. exact STK1.
        - exact (cg_auxv CG).
        - apply rauxcell_pres_refl.
        - apply rheap_pres_refl.
        - exact (cg_mo CG).
        - apply vm_agree_refl. }
      assert (MAPH : map (den (E' E st Fv Gv)) hargs0 = map (den E) hargs0).
      { apply map_ext_in. intros u Hu. apply (den_E' E st Fv Gv). destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB.
        apply andb_prop in SVB as [_ OV]. exact (forallb_In _ _ _ u (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) Hu). }
      assert (HH : St.op_holds OPS HEAP_ID (map (den (E' E st Fv Gv)) hargs0) (ms_mem ms) mo).
      { rewrite MAPH. exact (ops_hold_find OPS E (s_ops st) (ms_mem ms) mo HEAP_ID _ (so_ops _ _ _ _ _ _ HS) (cg_find CG)). }
      destruct (post_N E st ms mo ALLOC_STACK r ksp hargs0 wnl off r1 n md (VL a) nw rest s LBf LB HS HPB HMP CG R' (ms_mem ms) mo LBf errv GP ERR (cg_pubs CG) Fv Gv HF
                  (Fv_of_15 _ _ _) st4 H4 (VP (PrimInt63.add (s_next st) 16%uint63) wzero) hargs0 (fun b H => H)
                  ltac:(rewrite den_VPz; unfold E'; rewrite (ev_above_lit E (s_next st) Fv Gv 16%uint63 K16); reflexivity) HH ltac:(intros a0 X; rewrite MAPH in X; exact X)) as [ST MP'].
      refine (HK _ (or_introl eq_refl) _ _ _ (EXT E st Fv Gv) MP' _).
      refine (st_ok_fields rsegs OPS _ _ _ _ _ _ _ _ _ _ _ _ _ ST); subst st4; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next setr set_ops set_next alloc_post_mk]; try reflexivity.
      rewrite (set_op_same HEAP_ID (s_ops st) hargs0 (cg_find CG)). reflexivity.
  -
    destruct (negb (weqb o wzero) || PrimInt63.eqb kf 0 || PrimInt63.eqb kf STACK_ID) eqn:C; [discriminate|].
    apply orb_false_iff in C as [C K1]. apply orb_false_iff in C as [O0 K0]. apply negb_false_iff in O0. apply weqb_eq in O0. subst o.
    apply Uint63.eqb_false_spec in K0. apply Uint63.eqb_false_spec in K1.
    match type of Happ with context [match ?na with Some _ => _ | None => None end = Some sts] =>
      match na with (if is_lib a then _ else _) => destruct na as [av|] eqn:NA; [|discriminate] end end.
    destruct (free_ok st wnl kf) as [lenf|] eqn:FOK; [|discriminate].
    unfold heap_del_window in Happ.
    assert (NW' : heap_nwin (VL md :: VL a :: VL nw :: rest) = Some n) by (pose proof (cg_nwin CG) as X; rewrite EH in X; exact X).
    rewrite NW' in Happ.
    destruct (del_window n (firstn (3 * n) rest) (VP kf wzero)) as [ws'|] eqn:DEL; [|discriminate].
    destruct (alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp) as [st4|] eqn:H4; [|discriminate].
    cbn [heap_set_A] in Happ. unfold fresh in Happ. cbn [fst snd] in Happ. apply Some_inj in Happ. subst sts.
    destruct (alloc_post_inv st r ksp st4 r1 (cg_r1 CG) H4) as (r0 & Hr0 & E4).

    destruct (free_ok_inv st wnl kf lenf FOK) as (rf & Hkf & WLf & LOf & NEf & LEf & OTH).
    apply (known_ltu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in NEf. rewrite unsigned_VL in NEf. change (w2Z wzero) with 0 in NEf.
    apply (known_leu_q_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in LEf.
    set (Af := bv_unsigned (ev E kf)). set (nf := bv_unsigned (den E lenf)).
    destruct (nonstack_windows_In E n rest wnl kf lenf CtrLib.K_BLOCK (cg_wnl CG) (win_lookup_In _ _ _ _ WLf)) as (_ & _ & _ & INW).
    pose proof (cg_rheap CG) as RH. pose proof RH as RH0. apply RHEAP_split in RH0 as [RC _]. pose proof (RHEAP_core_nodup s LBf (ms_mem ms) RC) as NDid.
    pose proof (proj1 (Forall_forall _ _) (cg_wf CG) _ INW) as (_ & _ & _ & [[KS _]|[[_ BLB]|[KS _]]]); cbn [w_kind w_lo w_len w_iv] in *;
      [exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_STACK in KS; lia| | exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_SUB in KS; lia].
    fold Af nf in BLB.
    assert (BLB' : In (Af, nf) (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact BLB]).
    apply in_map_iff in BLB' as ([[p A1] n1] & Eb & INf). cbn [blk_addr blk_size fst snd] in Eb. injection Eb as -> ->.
    assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 Af).
    { rewrite <- reg_of_X10, (cg_regs CG X10), HX10, den_VPz. subst Af. symmetry. apply Z_to_bv_bv_unsigned. }
    apply (free_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo s LBf p Af nf
             (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + keyZ ksp) errv K
             A0 INf (cg_tp CG) (cg_ra CG) RH (cg_krel CG) (cg_auxv CG) ltac:(rewrite SP; lia)
             ltac:(rewrite SP; exact STK1) CE ltac:(rewrite SP; unfold RFREE_STACK; lia) ERR (cg_minv CG) (cg_mo CG)).
    intros R' M' mo' s' GP MPATH MTR ERR' RH' KR'. pose proof RH' as RH1. apply RHEAP_split in RH1 as [RC' PU'].
    set (Fv := Fv_of R' errv (PropExec.getr R' 10%bv)). set (Gv := Gv_of []).
    assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).

    assert (L3 : length (firstn (3 * n) rest) = (3 * n)%nat) by (apply firstn_length_le; exact L).
    assert (NWf : nonstack_windows n (firstn (3 * n) rest) = Some wnl) by (rewrite nonstack_windows_firstn; exact (cg_wnl CG)).
    destruct (del_window_split E n (firstn (3 * n) rest) kf ws' wnl DEL NWf ltac:(lia)) as (l1 & len & l2 & INlen & WS & WS' & LEN & M1).
    rewrite <- (app_nil_r (firstn (3 * n) rest)), (wins_of_firstn E n rest []) in WS by exact L.
    destruct (windows_anchored_nodup _ _ _ _ _ _ _ (cg_anch CG) INlen (win_lookup_In _ _ _ _ WLf)) as [-> _]. fold Af nf in WS.
    pose proof (del_window_prov E n (firstn (3 * n) rest) kf ws' wnl NWf DEL (windows_anchored_nodup_anchors _ _ (cg_anch CG))) as PROV. rewrite WS' in PROV.
    assert (AVW : forallb (sv_vars_below (s_next st)) ws' = true).
    { apply forallb_forall. intros x Hx. apply (proj1 (forallb_forall _ _) AVB).
      pose proof (del_window_sub _ _ _ _ _ DEL Hx) as X. rewrite <- (firstn_skipn (3 * n) rest). apply in_app_iff. left. exact X. }
    destruct (wsub_one_small nw T ltac:(lia)) as [T' EN'].
    assert (DEC' : decode (map (den (E' E st Fv Gv)) (VL md :: av :: VL (wsub nw wone) :: ws' ++ skipn (3 * n) rest))
                   = Some (w2Z md, den (E' E st Fv Gv) av, l1 ++ l2, map (den E) (skipn (3 * n) rest))).
    { rewrite (decode_hargs (E' E st Fv Gv) md av (wsub nw wone) (ws' ++ skipn (3 * n) rest) (pred n) T' ltac:(rewrite EN'; lia) ltac:(rewrite app_length; lia)).
      rewrite (wins_of_prefix _ (pred n) ws' _ ltac:(lia)), (wins_of_E' E st Fv Gv (pred n) ws' AVW), WS'.
      rewrite (skipn_app_exact ws' (skipn (3 * n) rest) (3 * pred n) ltac:(lia)). f_equal. f_equal.
      apply map_ext_in. intros u Hu. apply (den_E' E st Fv Gv). apply (forallb_In _ _ _ u AVB).
      rewrite <- (firstn_skipn (3 * n) rest). apply in_app_iff. right. exact Hu. }

    pose proof (lb_remove_perm p Af nf LBf INf NDid) as PL.
    assert (NOTIN : ~ In (Af, nf) (blocks_of (lb_remove p LBf))).
    { intros X. apply in_map_iff in X as (blk & Eb & Hblk). apply In_lb_remove in Hblk as [Hblk NEp].
      assert (NEb : blk_id (p, Af, nf) <> blk_id blk) by (cbn [blk_id fst]; congruence).
      pose proof (f_equal fst Eb) as E1. pose proof (f_equal snd Eb) as E2. unfold blk_addr, blk_size in E1, E2. cbn [fst snd] in E1, E2.
      destruct (RHEAP_core_blocks_disjoint s LBf (ms_mem ms) (p, Af, nf) blk RC INf Hblk NEb) as [D|D]; unfold blk_addr, blk_size in D; cbn [fst snd] in D; lia. }
    assert (PERM' : Permutation (blocks_of (lb_remove p LBf)) (remove iv_eq_dec (Af, nf) LB)).
    { apply Permutation_sym. eapply Permutation_trans. { apply perm_remove. apply Permutation_sym. exact (cg_perm CG). }
      eapply Permutation_trans. { apply perm_remove. apply (Permutation_map (fun b => (blk_addr b, blk_size b))) in PL. exact PL. }
      cbn [map blk_addr blk_size fst snd remove]. destruct (iv_eq_dec (Af, nf) (Af, nf)); [| congruence].
      rewrite notin_remove by exact NOTIN. apply Permutation_refl. }

    assert (SVa : sv_vars_below (s_next st) av = true) by (destruct (is_lib a); [injection NA as <-; reflexivity|]; destruct (pw_ok a && free_stage_ok a wnl kf); [injection NA as <-; reflexivity| discriminate]).
    assert (AWH : aw_holdsI (den E av) (remove iv_eq_dec (Af, nf) LB) M' mo').
    { exists s', (lb_remove p LBf). split; [exact PERM'|]. split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
      split; [| exact (repl_post _ _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG))].
      destruct (is_lib a) eqn:LIB.
      - injection NA as <-. unfold is_lib in LIB. apply weqb_eq in LIB. subst a. apply pclaim_none. rewrite den_VL, wbv_unsigned. change (w2Z wones) with (2 ^ 64 - 1). lia.
      - destruct (pw_ok a && free_stage_ok a wnl kf) eqn:PW; [|discriminate]. injection NA as <-.
        apply andb_prop in PW as [PWA FSO]. destruct (pw_ok_inv a PWA) as (Ta & Ra & Ea).
        unfold free_stage_ok in FSO. apply andb_prop in FSO as [FSO BW]. apply andb_prop in FSO as [NB2 JLT].
        apply Uint63.eqb_correct in NB2. pose proof (pw_nb_eq a) as NBE. rewrite NB2 in NBE. change (to_Z 2%uint63) with 2 in NBE.
        apply Uint63.ltb_spec in JLT. rewrite pw_j_eq in JLT. change (to_Z 255%uint63) with 255 in JLT.

        pose proof (cg_claim CG) as CL. rewrite den_VL, wbv_unsigned, Ea in CL.
        destruct (CL ltac:(lia)) as [RM HP]. rewrite <- NBE in HP.
        replace (to_Z (wl a) / 256) with 2 in HP by lia.
        destruct HP as [[X _]|[[X _]|[_ (k & po & Ao & p' & A' & sp0 & K10 & HIS & MM & PLB)]]]; [lia| lia|].

        assert (TWO : exists ks cf cs, In (kf, VL cf, CtrLib.K_BLOCK) wnl /\ In (ks, VL cs, CtrLib.K_BLOCK) wnl /\ ks <> kf
                 /\ cs = wadd cf cf /\ wleu cs CAP_MAX = true).
        { destruct (block_windows wnl) as [|[k1 [c1| | | | | | | | | |]] [|[k2 [c2| | | | | | | | | |]] [|]]] eqn:BWE; try discriminate.
          pose proof (block_windows_In wnl k1 (VL c1) ltac:(rewrite BWE; left; reflexivity)) as I1.
          pose proof (block_windows_In wnl k2 (VL c2) ltac:(rewrite BWE; right; left; reflexivity)) as I2.
          destruct (Uint63.eqb k1 kf) eqn:Q1.
          - apply Uint63.eqb_correct in Q1. subst k1. apply andb_prop in BW as [BW NK2]. apply andb_prop in BW as [EC LE].
            apply weqb_eq in EC. apply negb_true_iff in NK2. apply Uint63.eqb_false_spec in NK2.
            exists k2, c1, c2. repeat split; assumption.
          - apply Uint63.eqb_false_spec in Q1. apply andb_prop in BW as [BW LE]. apply andb_prop in BW as [Q2 EC].
            apply Uint63.eqb_correct in Q2. subst k2. apply weqb_eq in EC.
            exists k1, c2, c1. repeat split; auto. }
        destruct TWO as (ks & cf & cs & Ikf & Iks & NKS & ECS & LECS).
        destruct (windows_anchored_nodup _ _ _ _ _ _ _ (cg_anch CG) Ikf (win_lookup_In _ _ _ _ WLf)) as [ELF _].
        destruct (nonstack_windows_In E n rest wnl ks (VL cs) CtrLib.K_BLOCK (cg_wnl CG) Iks) as (_ & _ & _ & INWs).
        pose proof (proj1 (Forall_forall _ _) (cg_wf CG) _ INWs) as (_ & _ & Ws3 & [[KS _]|[[_ BLs]|[KS _]]]); cbn [w_kind w_lo w_len w_iv] in *;
          [exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_STACK in KS; lia| | exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_SUB in KS; lia].
        rewrite unsigned_VL in BLs, Ws3.
        assert (NF : nf = w2Z cf) by (subst nf; rewrite <- ELF, unsigned_VL; reflexivity).
        pose proof (Permutation_map (fun b => (blk_addr b, blk_size b)) PLB) as PM. cbn [map blk_addr blk_size fst snd] in PM.
        change (map (fun b => (blk_addr b, blk_size b)) LBf) with (blocks_of LBf) in PM.
        assert (IN2 : forall x, In x LB -> x = (A', bufsz (S k)) \/ x = (Ao, bufsz k)).
        { intros x Hx. assert (Hx' : In x (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hx]).
          pose proof (Permutation_in _ PM Hx') as Hx''. cbn [In] in Hx''. destruct Hx'' as [<-|[<-|[]]]; auto. }
        pose proof (bufsz_pos k) as BP0. pose proof (bufsz_S k) as BS1. pose proof (bufsz_S (S k)) as BS2.
        destruct (RHEAP_core_block_range s LBf (ms_mem ms) _ RC INf) as (Bf1 & Bf2 & Bf3 & Bf4 & _). cbn [blk_addr blk_size fst snd] in Bf1, Bf2, Bf3, Bf4.
        assert (CS2 : w2Z cs = 2 * nf).
        { rewrite ECS, wadd_ok, <- NF. pose proof alloc_ceiling_lt47. unfold two64. rewrite Z.mod_small; lia. }
        rewrite CS2 in BLs.
        assert (FREED_OLD : Af = Ao /\ nf = bufsz k).
        { destruct (IN2 _ BLB) as [E1|E1]; injection E1 as Ea1 En1; [| auto].
          exfalso. destruct (IN2 _ BLs) as [E2|E2]; injection E2 as Ea2 En2; lia. }
        destruct FREED_OLD as [EAo ENo].
        assert (PP0 : p = po).
        { assert (INo : In (po, Ao, bufsz k) LBf) by (eapply Permutation_in; [apply Permutation_sym; exact PLB| right; left; reflexivity]).
          destruct (bptr_eqb p po) eqn:Q; [apply bptr_eqb_true in Q; exact Q| exfalso].
          assert (NEb : blk_id (p, Af, nf) <> blk_id (po, Ao, bufsz k)) by (cbn [blk_id fst]; intros X; rewrite X, (proj2 (bptr_eqb_true po po) eq_refl) in Q; discriminate Q).
          destruct (RHEAP_core_blocks_disjoint s LBf (ms_mem ms) _ _ RC INf INo NEb) as [D|D]; unfold blk_addr, blk_size in D; cbn [fst snd] in D; lia. }
        subst po.
        assert (INn : In (p', A', bufsz (S k)) LBf) by (eapply Permutation_in; [apply Permutation_sym; exact PLB| left; reflexivity]).
        rewrite EAo, ENo in INf.
        pose proof (MF3_F_i k sp0 p Ao p' A' s mo (to_Z (wl a) mod 256) s' mo' LBf HIS MM (cg_krel CG) INf INn (cg_mo CG) RM ltac:(pose proof (Z.mod_pos_bound (to_Z (wl a)) 256); lia) MPATH) as RM'.

        assert (EX : bv_unsigned (den E (VL (W64 false (PrimInt63.sub (PrimInt63.add (wl a) 1%uint63) PW_NB)))) = to_Z (wl a) + 1 - 256).
        { rewrite unsigned_VL. unfold w2Z. cbn [wt wl]. rewrite Uint63.sub_spec, Uint63.add_spec. change (to_Z 1%uint63) with 1. change (to_Z PW_NB) with 256.
          pose proof (Z.div_mod (to_Z (wl a)) 256 ltac:(lia)). pose proof (Z.mod_pos_bound (to_Z (wl a)) 256 ltac:(lia)).
          rewrite (Z.mod_small (to_Z (wl a) + 1)) by (rewrite wB_two63; unfold two63; lia). rewrite Z.mod_small by (rewrite wB_two63; unfold two63; lia). lia. }
        rewrite EX. intros _. pose proof (Z.div_mod (to_Z (wl a)) 256 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (to_Z (wl a)) 256 ltac:(lia)) as MB.
        assert (EQM : (to_Z (wl a) + 1 - 256) mod 256 = to_Z (wl a) mod 256 + 1).
        { replace (to_Z (wl a) + 1 - 256) with ((to_Z (wl a) mod 256 + 1) + 1 * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
        assert (EQD : (to_Z (wl a) + 1 - 256) / 256 = 1).
        { replace (to_Z (wl a) + 1 - 256) with ((to_Z (wl a) mod 256 + 1) + 1 * 256) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. reflexivity. }
        split.
        + rewrite EQM. exact RM'.
        + rewrite EQD.
          right; left. split; [reflexivity|]. exists (S k), p', A'. split; [lia|]. split; [eapply histR_S; eauto|].
          pose proof (RHEAP_core_nodup s LBf (ms_mem ms) RC) as ND2.
          assert (NPP : p' <> p).
          { intros ->. pose proof (Permutation_NoDup (Permutation_map blk_id PLB) ND2) as ND3. cbn [map blk_id fst] in ND3.
            apply List.NoDup_cons_iff in ND3 as [NI3 _]. apply NI3. left. reflexivity. }
          assert (QP : bptr_eqb p' p = false) by (destruct (bptr_eqb p' p) eqn:Q; [apply bptr_eqb_true in Q; congruence| reflexivity]).
          destruct (Permutation_length_2_inv (Permutation_sym PLB)) as [EL|EL]; rewrite EL;
            rewrite !lb_remove_cons; cbn [blk_id fst]; rewrite QP, (proj2 (bptr_eqb_true p p) eq_refl); reflexivity. }
    destruct (post_F E st ms mo ALLOC_STACK r ksp hargs0 wnl off r1 n md (VL a) nw rest s LBf LB HS HPB HMP CG R' M' mo' (lb_remove p LBf) errv GP
                ltac:(intros b Hb; apply In_lb_remove in Hb; exact (proj1 Hb)) ERR' PU' Fv Gv HF (Fv_of_15 _ _ _) st4
                r0 kf rf lenf p Af nf av _ l1 l2 _ Hr0 E4 Hkf K0 K1 FOK INf eq_refl eq_refl
                ltac:(intros b Hb Nb; apply In_lb_remove; auto) ltac:(intros b Hb; apply In_lb_remove in Hb; exact (proj2 Hb))
                WS PROV DEC' SVa AWH (Fv_of_16 _ _ _) eq_refl) as [ST MP'].
    rewrite (cg_ra_r CG). refine (HK _ (or_introl eq_refl) _ _ _ (EXT E st Fv Gv) MP' _).
    refine (st_ok_fields rsegs OPS _ _ _ _ _ _ _ _ _ _ _ _ _ ST); subst st4; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next setr set_ops setregs set_next alloc_post_mk]; try reflexivity.
Qed.

Lemma bufsz_lt_10 : forall k, bufsz k < 2 ^ 26 -> (k < 10)%nat.
Proof.
  intros k H. destruct (Nat.lt_ge_cases k 10) as [L|G]; [exact L|]. exfalso. unfold bufsz, BUF0 in H.
  assert (2 ^ 10 <= 2 ^ Z.of_nat k) by (apply Z.pow_le_mono_r; lia). change (2 ^ 26) with (65536 * 2 ^ 10) in H. nia.
Qed.
Lemma cap_ok_sound : forall c, cap_ok c = true -> exists k, (k <= 10)%nat /\ w2Z c = bufsz k.
Proof.
  intros c H. unfold cap_ok in H. cbn [existsb] in H.
  repeat match type of H with (?x || ?y) = true => destruct x eqn:?Q; [clear H| cbn [orb] in H] end;
  repeat match goal with Q : weqb c (wlit ?l) = true |- _ => apply weqb_eq in Q; subst c;
      match l with of_Z (65536 * 2 ^ ?z) => exists (Z.to_nat z) end; split; [lia| vm_compute; reflexivity] end.
  discriminate H.
Qed.

Theorem malloc_nofork : forall pc st stA stB (KB : TSet) E ms mo,
  to_Z pc = RMALLOC_SYM -> s_pc st = pc ->
  malloc_apply rsegs ERRNO LIBC GOT GUARD TP CANARY st = Some [stA; stB] ->
  St.st_ok rsegs OPS E st ms mo -> MP mo -> PB (eb E) ->
  (forall E2 ms2 mo2, env_ext (s_next st) E E2 -> MP mo2 -> St.st_ok rsegs OPS E2 stB ms2 mo2 -> realizes rsegs (mkCfg ms2 mo2) KB) ->
  realizes rsegs (mkCfg ms mo) KB.
Proof.
  intros pc st stA stB KB E ms mo Hpc Hspc Happ HS HMP HPB HKB.
  unfold malloc_apply in Happ.
  destruct (alloc_call rsegs ERRNO LIBC GOT GUARD TP CANARY ALLOC_STACK st) as [[[[r ksp] hargs0] wnl]|] eqn:AC; [|discriminate].
  destruct (alloc_call_sound Cw OPS OPS_plain OPS_holds1 PB CANARY PB_canary PB_secret E st ms mo ALLOC_STACK r ksp hargs0 wnl HS HPB ltac:(vm_compute; reflexivity) AC)
    as (off & r1 & n & md & A & nw & rest & s & LBf & LB & CG).
  pose proof (cg_hargs CG) as EH. rewrite EH, heap_A_eq in Happ.
  destruct A as [a| | | | | | | | | |]; try discriminate.
  destruct (pw_ok a && PrimInt63.leb (pw_j a) J_MAX && size_ok32 (s_facts st) (getr st X10)) eqn:C; [|discriminate].
  apply andb_prop in C as [C SZ]. apply andb_prop in C as [PWA JMAX].
  destruct (malloc_stage_ok (s_facts st) a wnl (getr st X10)) as [grow|] eqn:STG; [|discriminate].
  cbn [heap_set_A] in Happ. unfold malloc_posts, malloc_posts_rg in Happ.
  destruct (alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp) as [st4|] eqn:H4; [|discriminate].
  cbn [block_posts] in Happ.
  set (aB := if grow then VL (wadd a (wlit 257%uint63)) else VL wones) in Happ.
  destruct (block_post st4 (VL md :: aB :: VL nw :: rest) (getr st X10) (BLK_LO, BLK_HI)) as [stB'|] eqn:HB; [|discriminate].
  apply Some_inj in Happ. injection Happ as <- <-.
  pose proof (size_ok32_sound E _ _ (so_facts _ _ _ _ _ _ HS) SZ) as NZ. set (nZ := bv_unsigned (den E (getr st X10))) in *.
  pose proof (cg_nw CG) as (T & N & L).
  assert (SVn : sv_vars_below (s_next st) (getr st X10) = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB.
    do 5 (apply andb_prop in SVB as [SVB ?]). exact (rf_allb_get _ _ _ SVB X10). }
  assert (AVB : forallb (sv_vars_below (s_next st)) rest = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB. apply andb_prop in SVB as [_ OV].
    pose proof (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) as AV. rewrite EH in AV. cbn [op_args forallb] in AV.
    apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. exact AV. }

  destruct (pw_ok_inv a PWA) as (Ta & Ra & Ea). apply Uint63.leb_spec in JMAX. rewrite pw_j_eq in JMAX. change (to_Z J_MAX) with 27 in JMAX.
  pose proof (cg_claim CG) as CL. rewrite den_VL, wbv_unsigned, Ea in CL. destruct (CL ltac:(lia)) as [RM HP].
  pose proof (Z.div_mod (to_Z (wl a)) 256 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (to_Z (wl a)) 256 ltac:(lia)) as MB.
  pose proof (cg_rheap CG) as RH. pose proof RH as RH0. apply RHEAP_split in RH0 as [RC _].

  assert (STAGE : malloc_must_succeed s mo nZ /\
            (grow = true -> forall s' mo' p Ab rr, mpath (raw_malloc nZ) s mo rr s' mo' -> mtr_malloc s nZ (Some p) s' ->
               pclaim (to_Z (wl a) + 257) s' ((p, Ab, nZ) :: LBf) mo')).
  { unfold malloc_stage_ok in STG.
    destruct (Uint63.eqb (pw_nb a) 0%uint63) eqn:NB0.
    -
      apply Uint63.eqb_correct in NB0. pose proof (pw_nb_eq a) as NBE. rewrite NB0 in NBE. change (to_Z 0%uint63) with 0 in NBE.
      destruct (PrimInt63.eqb (pw_j a) 0 && sv_eqb (getr st X10) (VL (wlit 65536))) eqn:C0; [|discriminate]. apply Some_inj in STG. subst grow.
      apply andb_prop in C0 as [J0 N0]. apply Uint63.eqb_correct in J0. pose proof (pw_j_eq a) as JE. rewrite J0 in JE. change (to_Z 0%uint63) with 0 in JE.
      apply sv_eqb_eq in N0.
      assert (A0 : to_Z (wl a) = 0) by lia.
      assert (EN : nZ = BUF0) by (subst nZ; rewrite N0, unsigned_VL; reflexivity).
      rewrite <- NBE in HP. replace (to_Z (wl a) / 256) with 0 in HP by lia.
      destruct HP as [[_ [Es ELB]]|[[X _]|[X _]]]; [| lia| lia]. subst s LBf.
      pose proof (cg_krel CG) as KR0. rewrite A0 in RM. rewrite (Z.mod_0_l 256 ltac:(lia)) in RM.
      rewrite EN. split; [exact (MF_A_must_i mo KR0 (cg_mo CG) RM)|].
      intros _ s' mo' p Ab rr MPATH MTR. rewrite A0. unfold pclaim. intros _.
      replace ((0 + 257) mod 256) with (0 + 1) by reflexivity. replace ((0 + 257) / 256) with 1 by reflexivity.
      split.
      + exact (MF3_A_i mo 0 rr s' mo' KR0 (cg_mo CG) RM ltac:(lia) MPATH).
      + right; left. split; [reflexivity|]. exists O, p, Ab. split; [lia|]. split; [apply histR_O; exact MTR|].
        unfold bufsz; rewrite Z.pow_0_r, Z.mul_1_r; reflexivity.
    - destruct (Uint63.eqb (pw_nb a) 1%uint63) eqn:NB1; [|discriminate].
      apply Uint63.eqb_correct in NB1. pose proof (pw_nb_eq a) as NBE. rewrite NB1 in NBE. change (to_Z 1%uint63) with 1 in NBE.
      rewrite <- NBE in HP. replace (to_Z (wl a) / 256) with 1 in HP by lia.
      destruct HP as [[X _]|[[_ (k & p0 & A0 & K10 & HIS & ELB)]|[X _]]]; [lia| | lia].
      destruct (block_windows wnl) as [|[kb [c| | | | | | | | | |]] [|]] eqn:BWE; try discriminate.
      destruct (cap_ok c) eqn:CAP; [cbn [negb] in STG| discriminate].

      pose proof (block_windows_In wnl kb (VL c) ltac:(rewrite BWE; left; reflexivity)) as Ikb.
      destruct (nonstack_windows_In E n rest wnl kb (VL c) CtrLib.K_BLOCK (cg_wnl CG) Ikb) as (_ & _ & _ & INWb).
      pose proof (proj1 (Forall_forall _ _) (cg_wf CG) _ INWb) as (_ & _ & _ & [[KS _]|[[_ BLb]|[KS _]]]); cbn [w_kind w_lo w_len w_iv] in *;
        [exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_STACK in KS; lia| | exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_SUB in KS; lia].
      rewrite unsigned_VL in BLb.
      assert (BLb' : In (bv_unsigned (ev E kb), w2Z c) (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact BLb]).
      rewrite ELB in BLb'. cbn [blocks_of map blk_addr blk_size fst snd In] in BLb'. destruct BLb' as [BLb'|[]]. injection BLb' as _ EC.
      pose proof (bufsz_pos k) as BP0. pose proof (bufsz_S k) as BS1.
      pose proof (cg_krel CG) as KR1. rewrite ELB in KR1.
      destruct (sv_eqb (getr st X10) (VL (wadd c c)) && wltu c CAP_MAX) eqn:GR.
      +
        apply Some_inj in STG. subst grow. apply andb_prop in GR as [N2 CLT]. apply sv_eqb_eq in N2.
        rewrite wltu_w2Z in CLT || (unfold wltu in CLT). apply Z.ltb_lt in CLT. change (w2Z CAP_MAX) with (2 ^ 26) in CLT. rewrite <- EC in CLT.
        pose proof (bufsz_lt_10 k CLT) as K9.
        assert (EN : nZ = bufsz (S k)).
        { subst nZ. rewrite N2, unsigned_VL, wadd_ok, <- EC, BS1. unfold two64. rewrite Z.mod_small; lia. }
        rewrite EN. split; [exact (MF_B_must_i k s p0 A0 mo _ HIS KR1 (cg_mo CG) K9 RM ltac:(lia))|].
        intros _ s' mo' p Ab rr MPATH MTR LT. split.
        * replace ((to_Z (wl a) + 257) mod 256) with (to_Z (wl a) mod 256 + 1).
          { exact (MF3_B_i k s p0 A0 mo _ rr s' mo' HIS KR1 (cg_mo CG) K9 RM ltac:(lia) MPATH). }
          apply (Z.mod_unique_pos _ 256 (to_Z (wl a) / 256 + 1)); lia.
        * replace ((to_Z (wl a) + 257) / 256) with 2 by (apply (Z.div_unique_pos _ 256 2 (to_Z (wl a) mod 256 + 1)); lia).
          right; right. split; [reflexivity|]. exists k, p0, A0, p, Ab, s. split; [exact K9|]. split; [exact HIS|]. split; [exact MTR|]. rewrite ELB. apply Permutation_refl.
      +
        destruct (known_ltu (s_facts st) (VL wzero) (getr st X10) && known_ltu (s_facts st) (getr st X10) (VL CAP_MAX)) eqn:PC; [|discriminate].
        apply Some_inj in STG. subst grow. apply andb_prop in PC as [P1 P2].
        apply (known_ltu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in P1. apply (known_ltu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in P2.
        rewrite unsigned_VL in P1, P2. change (w2Z wzero) with 0 in P1. change (w2Z CAP_MAX) with (2 ^ 26) in P2. fold nZ in P1, P2.
        split; [exact (MF_C_must_i k s p0 A0 mo nZ _ HIS KR1 (cg_mo CG) K10 ltac:(lia) RM ltac:(lia))|].
        intros X; discriminate X. }
  destruct STAGE as (MUST & GCLAIM).

  pose proof (cg_ms CG) as MSE. rewrite Hspc, Hpc in MSE. rewrite MSE.
  pose proof (cg_stk CG) as STK. pose proof (cg_room CG) as ROOM. pose proof (cg_hi CG) as HI. pose proof (cg_ceil CG) as CE.
  pose proof (int_range ALLOC_STACK) as RAS. change (to_Z ALLOC_STACK) with 8192 in ROOM, RAS.
  destruct (stk_split rsegs (ms_mem ms) _ (bv_unsigned (ev E STACK_ID) + keyZ ksp) _ STK ltac:(lia)) as [STK1 _].
  destruct (cg_errno CG) as [errv ERR].
  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 nZ).
  { subst nZ. rewrite <- reg_of_X10, (cg_regs CG X10). symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (cg_sp CG) as SP.
  apply (malloc_must_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo s LBf nZ
           (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + keyZ ksp) errv KB
           A0 ltac:(lia) (cg_tp CG) (cg_ra CG) RH (cg_krel CG) (cg_auxv CG) ltac:(rewrite SP; lia)
           ltac:(rewrite SP; exact STK1) CE ltac:(rewrite SP; unfold RMALLOC_STACK; lia) ERR (cg_minv CG) (cg_mo CG) MUST).
  -
    intros R' M' mo' s' errv' p Ab junk GP MPATH MTR Ha0 ERR' RNG CELLS EXP RH' KR'. apply RHEAP_split in RH' as [RC' PU'].
    destruct RNG as (Apos & A16 & Nn & AC' & AI).
    set (Fv := Fv_of R' errv' (Z_to_bv 64 Ab)). set (Gv := Gv_of junk).
    assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
    destruct (RHEAP_core_block_range s' ((p, Ab, nZ) :: LBf) M' (p, Ab, nZ) RC' (or_introl eq_refl)) as (B4096 & _). cbn [blk_addr fst snd] in B4096.
    pose proof (RHEAP_core_nodup s' _ M' RC') as ND. cbn [map blk_id fst] in ND. apply List.NoDup_cons_iff in ND as [NI ND'].
    assert (NEW : forall b a1, In b LB -> in_iv b a1 -> ~ (Ab <= a1 < Ab + nZ)).
    { intros b a1 Hb Hin R5.
      assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
      apply in_map_iff in Hb' as (blk & Eb & Hblk).
      assert (NEb : blk_id (p, Ab, nZ) <> blk_id blk).
      { cbn [blk_id fst]. intros X. apply NI. rewrite X. apply in_map_iff. exists blk. auto. }
      destruct (RHEAP_core_blocks_disjoint s' _ M' (p, Ab, nZ) blk RC' (or_introl eq_refl) (or_intror Hblk) NEb) as [D|D];
        unfold in_iv in Hin; rewrite <- Eb in Hin; unfold blk_addr, blk_size in D, Hin; cbn [fst snd] in D, Hin; lia. }
    assert (LJ : length junk = Z.to_nat nZ) by (destruct CELLS as [[[LJ _] _] _]; exact LJ).
    assert (GJ : forall o, 0 <= o < nZ -> nth_error junk (Z.to_nat o) = Some (Gv 16 o)).
    { intros o Ho. unfold Gv, Gv_of. apply nth_error_nth'. rewrite LJ. lia. }
    assert (SVaB : sv_vars_below (s_next st) aB = true) by (subst aB; destruct grow; reflexivity).
    assert (AWH : aw_holdsI (den E aB) ((Ab, nZ) :: LB) M' mo').
    { exists s', ((p, Ab, nZ) :: LBf). split; [cbn [blocks_of map blk_addr blk_size fst snd]; apply perm_skip; exact (cg_perm CG)|].
      split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
      split; [| exact (repl_post LBf _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG))].
      subst aB. destruct grow.
      - rewrite den_VL, wbv_unsigned, wadd_ok, Ea, wlit_ok. change (to_Z 257%uint63) with 257. unfold two64. rewrite Z.mod_small by lia.
        exact (GCLAIM eq_refl s' mo' p Ab (Some p) MPATH MTR).
      - apply pclaim_none. rewrite den_VL, wbv_unsigned. change (w2Z wones) with (2 ^ 64 - 1). lia. }
    pose proof alloc_ceiling_lt47 as C47.
    destruct (post_B E st ms mo ALLOC_STACK r ksp hargs0 wnl off r1 n md (VL a) nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP (fun b H => H) ERR' PU' Fv Gv HF
                (Fv_of_15 _ _ _) st4 H4 (VL md :: aB :: VL nw :: rest) aB (getr st X10) BLK_LO BLK_HI stB' Ab nZ junk
                eq_refl HB SVn SVaB eq_refl (Fv_of_16 _ _ _) GJ CELLS B4096 AC' A16 ltac:(unfold RIMG_LO, RIMG_HI; lia)
                ltac:(change (w2Z BLK_LO) with 4096; change (w2Z BLK_HI) with (2 ^ 47 - 1); lia) NEW (fun b H => H) AWH Ha0) as [ST MP'].
    rewrite (cg_ra_r CG). exact (HKB _ _ _ (EXT E st Fv Gv) MP' ST).
Qed.

Theorem malloc1_sound : forall pc, to_Z pc = RMALLOC_SYM ->
  contract_sound rsegs OPS MP PB (CtrN.malloc1_c rsegs ERRNO LIBC GOT GUARD TP CANARY pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrN.malloc1_c] in Happ. unfold CtrN.malloc1_apply in Happ.
  destruct (malloc_apply rsegs ERRNO LIBC GOT GUARD TP CANARY st) as [[| stA [| stB [| stC l]]]|] eqn:MA; try discriminate.
  apply Some_inj in Happ. subst sts.
  apply (malloc_nofork pc st stA stB K E ms mo Hpc Hspc MA HS HMP HPB).
  intros E2 ms2 mo2 EXT2 MP2 ST2. exact (HK stB (or_introl eq_refl) E2 ms2 mo2 EXT2 MP2 ST2).
Qed.

Lemma block_bytes : forall s LB m p A old, RHEAP_core s LB m -> In (p, A, old) LB ->
  exists bs, bytes_at rsegs m A bs /\ Z.of_nat (length bs) = old.
Proof.
  intros s LB m p A old RC Hin.
  destruct (RHEAP_core_block_range s LB m _ RC Hin) as (B1 & B2 & B3 & B4 & B5). cbn [blk_addr blk_size fst snd] in B1, B2, B3, B4, B5.
  pose proof alloc_ceiling_lt64 as C64.
  exists (map (fun i => match m (wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 (Z.to_nat old))).
  unfold bytes_at. rewrite !length_map, !length_seq. split; [| lia]. split; [lia|]. split; [lia|].
  intros i Hi. rewrite nth_error_map, Stdlib.Lists.List.nth_error_seq.
  destruct (Nat.ltb i (Z.to_nat old)) eqn:LT; [| apply Nat.ltb_ge in LT; lia]. cbn [option_map Nat.add].
  unfold mrd. destruct (m (wa (A + Z.of_nat i))) as [b|] eqn:Hm; [reflexivity|]. exfalso. exact (B5 (A + Z.of_nat i) ltac:(lia) Hm).
Qed.

Theorem realloc_sound : forall pc, to_Z pc = RREALLOC_SYM ->
  contract_sound rsegs OPS MP PB (realloc_c rsegs ERRNO LIBC GOT GUARD TP CANARY pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply realloc_c] in Happ. unfold realloc_apply in Happ.
  destruct (alloc_call rsegs ERRNO LIBC GOT GUARD TP CANARY REALLOC_STACK st) as [[[[r ksp] hargs0] wnl]|] eqn:AC; [|discriminate].
  destruct (alloc_call_sound Cw OPS OPS_plain OPS_holds1 PB CANARY PB_canary PB_secret E st ms mo REALLOC_STACK r ksp hargs0 wnl HS HPB ltac:(vm_compute; reflexivity) AC)
    as (off & r1 & n & md & A & nw & rest & s & LBf & LB & CG).
  pose proof (cg_hargs CG) as EH. rewrite EH, heap_drop_A_eq in Happ.
  destruct (size_ok (s_facts st) (getr st X11)) eqn:SZ; [cbn [negb] in Happ| discriminate].
  pose proof (size_ok_sound E _ _ (so_facts _ _ _ _ _ _ HS) SZ) as NZ. set (nZ := bv_unsigned (den E (getr st X11))) in *.
  pose proof (cg_nw CG) as (T & N & L).
  assert (SVn : sv_vars_below (s_next st) (getr st X11) = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB.
    do 5 (apply andb_prop in SVB as [SVB ?]). exact (rf_allb_get _ _ _ SVB X11). }
  assert (AVB : forallb (sv_vars_below (s_next st)) rest = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB. apply andb_prop in SVB as [_ OV].
    pose proof (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) as AV. rewrite EH in AV. cbn [op_args forallb] in AV.
    apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. exact AV. }

  pose proof (cg_ms CG) as MSE. rewrite Hspc in MSE. cbn [c_pc realloc_c] in MSE. rewrite Hpc in MSE. rewrite MSE.
  pose proof (cg_stk CG) as STK. pose proof (cg_room CG) as ROOM. pose proof (cg_hi CG) as HI. pose proof (cg_ceil CG) as CE.
  pose proof (int_range REALLOC_STACK) as RAS. change (to_Z REALLOC_STACK) with 8256 in ROOM, RAS.
  destruct (stk_split rsegs (ms_mem ms) _ (bv_unsigned (ev E STACK_ID) + keyZ ksp) _ STK ltac:(lia)) as [STK1 _].
  destruct (cg_errno CG) as [errv ERR].
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 nZ).
  { subst nZ. rewrite <- reg_of_X11, (cg_regs CG X11). symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (cg_sp CG) as SP. pose proof alloc_ceiling_lt47 as C47.
  pose proof (cg_rheap CG) as RH. pose proof RH as RH0. apply RHEAP_split in RH0 as [RC _]. pose proof (RHEAP_core_nodup s LBf (ms_mem ms) RC) as NDid.
  pose proof (fresh_ok_inv st (cg_fresh CG)) as (_ & NXpos & NX256).
  assert (K16 : to_Z (s_next st) + to_Z 16%uint63 < wB) by (change (to_Z 16%uint63) with 16; rewrite wB_two63, two63_eq; lia).

  assert (DECN : forall Fv Gv, decode (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest)) = Some (w2Z md, wbv wones, wins_of E n rest, map (den E) (skipn (3 * n) rest))).
  { intros Fv Gv. rewrite (decode_hargs (E' E st Fv Gv) md (VL wones) nw rest n T N L), (wins_of_E' E st Fv Gv n rest AVB), den_VL. f_equal. f_equal.
    apply map_ext_in. intros u Hu. apply (den_E' E st Fv Gv). apply (forallb_In _ _ _ u AVB).
    rewrite <- (firstn_skipn (3 * n) rest). apply in_app_iff. right. exact Hu. }
  assert (FPN : forall Fv Gv a, Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest))) ->
                         Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E) hargs0))).
  { intros Fv Gv a X. rewrite OPS_fp1 in X |- *. unfold heap_fp in X |- *. rewrite DECN in X. rewrite (cg_decode CG). exact X. }

  assert (POSTN : forall st4 R' M' mo' s' errv',
            alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp = Some st4 ->
            In (setr (set_ops st4 (set_op HEAP_ID (VL md :: VL wones :: VL nw :: rest) (s_ops st4))) X10 (VL wzero)) sts ->
            gpost (ms_regs ms) (ms_mem ms) mo LBf (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + keyZ ksp) R' M' mo' ->
            PropExec.getr R' 10%bv = Z_to_bv 64 0 -> rw_cells rsegs M' RERRNO [C4 errv'] -> RHEAP s' LBf M' -> KREL s' LBf mo' ->
            realizes rsegs (mkCfg (MS R' (ms_fregs ms) (PropExec.getr (ms_regs ms) 1%bv) (ms_fcsr ms) None M' (seg_rom rsegs)) mo') K).
  { intros st4 R' M' mo' s' errv' H4 HIN GP Ha0 ERR' RH'. intros KR'. apply RHEAP_split in RH' as [RC' PU'].
    set (Fv := Fv_of R' errv' (Z_to_bv 64 0)). set (Gv := Gv_of []).
    assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
    assert (HH : St.op_holds OPS HEAP_ID (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest)) M' mo').
    { rewrite OPS_holds1. exists (w2Z md), (wbv wones), (wins_of E n rest), (map (den E) (skipn (3 * n) rest)), LB.
      split; [exact (DECN Fv Gv)|]. split; [| split; [exact (cg_wf CG)| exact (cw_post LBf LB _ _ _ _ _ _ (cg_perm CG) (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_cw CG))]].
      apply aw_holdsW_intro; [| exact (cg_ng CG)]. exists s', LBf. split; [exact (cg_perm CG)|]. split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
      split; [apply pclaim_none; rewrite wbv_unsigned; change (w2Z wones) with (2 ^ 64 - 1); lia|].
      exact (repl_post LBf _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG)). }
    destruct (post_N E st ms mo REALLOC_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP ERR' PU' Fv Gv HF
                (Fv_of_15 _ _ _) st4 H4 (VL wzero) (VL md :: VL wones :: VL nw :: rest) (fun b H => H)
                ltac:(rewrite den_VL, Ha0; reflexivity) HH (FPN Fv Gv)) as [ST MP'].
    rewrite (cg_ra_r CG). exact (HK _ HIN _ _ _ (EXT E st Fv Gv) MP' ST). }
  destruct (getr st X10) as [w|kf o| | | | | | | | |] eqn:HX10; try discriminate.
  -
    destruct (weqb w wzero) eqn:W0; [|discriminate]. apply weqb_eq in W0. subst w.
    unfold malloc_posts, malloc_posts_rg in Happ.
    destruct (alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp) as [st4|] eqn:H4; [|discriminate].
    cbn [block_posts] in Happ.
    destruct (block_post st4 (VL md :: VL wones :: VL nw :: rest) (getr st X11) (BLK_LO, BLK_HI)) as [stB|] eqn:HB; [|discriminate].
    apply Some_inj in Happ. subst sts.
    assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 0).
    { rewrite <- reg_of_X10, (cg_regs CG X10), HX10, den_VL. reflexivity. }
    apply (realloc_null_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo s LBf nZ
             (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + keyZ ksp) errv K
             A0 A1 ltac:(lia) (cg_tp CG) (cg_ra CG) RH (cg_krel CG) (cg_auxv CG) ltac:(rewrite SP; lia)
             ltac:(rewrite SP; exact STK1) CE ltac:(rewrite SP; unfold RREALLOC_STACK, RMALLOC_STACK; lia) ERR (cg_minv CG) (cg_mo CG)).
    +
      intros R' M' mo' s' errv' GP MPATH MTR Ha0 ERR' RH' KR'. exact (POSTN st4 R' M' mo' s' errv' eq_refl (or_introl eq_refl) GP Ha0 ERR' RH' KR').
    +
      intros R' M' mo' s' errv' p Ab junk GP MPATH MTR Ha0 ERR' RNG CELLS EXP RH' KR'. apply RHEAP_split in RH' as [RC' PU'].
      destruct RNG as (Apos & A16 & Nn & AC' & AI).
      set (Fv := Fv_of R' errv' (Z_to_bv 64 Ab)). set (Gv := Gv_of junk).
      assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
      destruct (RHEAP_core_block_range s' ((p, Ab, nZ) :: LBf) M' (p, Ab, nZ) RC' (or_introl eq_refl)) as (B4096 & _). cbn [blk_addr fst snd] in B4096.
      pose proof (RHEAP_core_nodup s' _ M' RC') as ND. cbn [map blk_id fst] in ND. apply List.NoDup_cons_iff in ND as [NI ND'].
      assert (NEW : forall b a, In b LB -> in_iv b a -> ~ (Ab <= a < Ab + nZ)).
      { intros b a Hb Hin R5.
        assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
        apply in_map_iff in Hb' as (blk & Eb & Hblk).
        assert (NEb : blk_id (p, Ab, nZ) <> blk_id blk).
        { cbn [blk_id fst]. intros X. apply NI. rewrite X. apply in_map_iff. exists blk. auto. }
        destruct (RHEAP_core_blocks_disjoint s' _ M' (p, Ab, nZ) blk RC' (or_introl eq_refl) (or_intror Hblk) NEb) as [D|D];
          unfold in_iv in Hin; rewrite <- Eb in Hin; unfold blk_addr, blk_size in D, Hin; cbn [fst snd] in D, Hin; lia. }
      assert (LJ : length junk = Z.to_nat nZ) by (destruct CELLS as [[[LJ _] _] _]; exact LJ).
      assert (GJ : forall o, 0 <= o < nZ -> nth_error junk (Z.to_nat o) = Some (Gv 16 o)).
      { intros o Ho. unfold Gv, Gv_of. apply nth_error_nth'. rewrite LJ. lia. }
      assert (AWH : aw_holdsI (den E (VL wones)) ((Ab, nZ) :: LB) M' mo').
      { exists s', ((p, Ab, nZ) :: LBf). split; [cbn [blocks_of map blk_addr blk_size fst snd]; apply perm_skip; exact (cg_perm CG)|].
        split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
        split; [apply pclaim_none; rewrite den_VL, wbv_unsigned; change (w2Z wones) with (2 ^ 64 - 1); lia|].
        exact (repl_post LBf _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG)). }
      destruct (post_B E st ms mo REALLOC_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP (fun b H => H) ERR' PU' Fv Gv HF
                  (Fv_of_15 _ _ _) st4 H4 (VL md :: VL wones :: VL nw :: rest) (VL wones) (getr st X11) BLK_LO BLK_HI stB Ab nZ junk
                  eq_refl HB SVn eq_refl eq_refl (Fv_of_16 _ _ _) GJ CELLS B4096 AC' A16 ltac:(unfold RIMG_LO, RIMG_HI; lia)
                  ltac:(change (w2Z BLK_LO) with 4096; change (w2Z BLK_HI) with (2 ^ 47 - 1); lia) NEW (fun b H => H) AWH Ha0) as [ST MP'].
      rewrite (cg_ra_r CG). exact (HK _ (or_intror (or_introl eq_refl)) _ _ _ (EXT E st Fv Gv) MP' ST).
  -
    destruct (negb (weqb o wzero) || PrimInt63.eqb kf 0 || PrimInt63.eqb kf STACK_ID) eqn:C; [discriminate|].
    apply orb_false_iff in C as [C K1]. apply orb_false_iff in C as [O0 K0]. apply negb_false_iff in O0. apply weqb_eq in O0. subst o.
    apply Uint63.eqb_false_spec in K0. apply Uint63.eqb_false_spec in K1.
    destruct (IMap.find kf (s_regs st)) as [rg|] eqn:Hkf; [|discriminate].
    destruct (free_ok st wnl kf) as [old|] eqn:FOK; [|discriminate].
    destruct (negb (sv_eqb (Mem.rg_hi rg) old) || negb (Mem.rg_w rg)) eqn:C2; [discriminate|].
    apply orb_false_iff in C2 as [HIo Wo].
    apply negb_false_iff in HIo. apply sv_eqb_eq in HIo. apply negb_false_iff in Wo.
    destruct (alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp) as [st4|] eqn:H4; [|discriminate].
    unfold heap_del_window in Happ.
    assert (NW' : heap_nwin (VL md :: VL wones :: VL nw :: rest) = Some n) by (pose proof (cg_nwin CG) as X; rewrite EH in X; exact X).
    rewrite NW' in Happ.
    destruct (del_window n (firstn (3 * n) rest) (VP kf wzero)) as [ws'|] eqn:DEL; [|discriminate].
    unfold fresh in Happ. cbn [fst snd] in Happ.

    assert (L3 : length (firstn (3 * n) rest) = (3 * n)%nat) by (apply firstn_length_le; exact L).
    assert (NWf : nonstack_windows n (firstn (3 * n) rest) = Some wnl) by (rewrite nonstack_windows_firstn; exact (cg_wnl CG)).
    destruct (free_ok_inv st wnl kf old FOK) as (rf & Hkf' & WLf & LOf & NEf & LEf & OTH). rewrite Hkf in Hkf'. injection Hkf' as <-.
    destruct (del_window_split E n (firstn (3 * n) rest) kf ws' wnl DEL NWf ltac:(lia)) as (l1 & len & l2 & INlen & WS & WS' & LEN & M1).
    rewrite <- (app_nil_r (firstn (3 * n) rest)), (wins_of_firstn E n rest []) in WS by exact L.
    destruct (windows_anchored_nodup _ _ _ _ _ _ _ (cg_anch CG) INlen (win_lookup_In _ _ _ _ WLf)) as [-> _].
    destruct (wsub_one_small nw T ltac:(lia)) as [T' EN'].
    assert (NW1 : heap_nwin (VL md :: VL wones :: VL (wsub nw wone) :: ws' ++ skipn (3 * n) rest) = Some (pred n)).
    { unfold heap_nwin. rewrite T', EN'. replace (Z.to_nat (to_Z (wl nw) - 1)) with (pred n) by lia.
      rewrite length_app. replace (Nat.leb (3 * pred n) (length ws' + length (skipn (3 * n) rest))) with true; [reflexivity|].
      symmetry. apply Nat.leb_le. lia. }
    rewrite (heap_add_window_eq md (VL wones) (wsub nw wone) (ws' ++ skipn (3 * n) rest) (pred n) _ _ _ NW1) in Happ.
    apply Some_inj in Happ. subst sts.
    destruct (alloc_post_inv st r ksp st4 r1 (cg_r1 CG) H4) as (r0 & Hr0 & E4).

    apply (known_ltu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in NEf. rewrite unsigned_VL in NEf. change (w2Z wzero) with 0 in NEf. rewrite HIo in NEf.
    set (Af := bv_unsigned (ev E kf)). set (nf := bv_unsigned (den E old)) in *.
    destruct (nonstack_windows_In E n rest wnl kf old CtrLib.K_BLOCK (cg_wnl CG) (win_lookup_In _ _ _ _ WLf)) as (_ & _ & _ & INW).
    pose proof (proj1 (Forall_forall _ _) (cg_wf CG) _ INW) as (_ & _ & _ & [[KS _]|[[_ BLB]|[KS _]]]); cbn [w_kind w_lo w_len w_iv] in *;
      [exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_STACK in KS; lia| | exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_SUB in KS; lia].
    fold Af nf in BLB.
    assert (BLB' : In (Af, nf) (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact BLB]).
    apply in_map_iff in BLB' as ([[p A1'] n1] & Eb & INf). cbn [blk_addr blk_size fst snd] in Eb. injection Eb as -> ->.
    destruct (block_bytes s LBf (ms_mem ms) p Af nf RC INf) as (oldbs & OLDBS & OLDLEN).
    assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 Af).
    { rewrite <- reg_of_X10, (cg_regs CG X10), HX10, den_VPz. subst Af. symmetry. apply Z_to_bv_bv_unsigned. }
    fold Af nf in WS.
    pose proof (del_window_prov E n (firstn (3 * n) rest) kf ws' wnl NWf DEL (windows_anchored_nodup_anchors _ _ (cg_anch CG))) as PROV. rewrite WS' in PROV.
    assert (AVW : forallb (sv_vars_below (s_next st)) ws' = true).
    { apply forallb_forall. intros x Hx. apply (proj1 (forallb_forall _ _) AVB).
      pose proof (del_window_sub _ _ _ _ _ DEL Hx) as X. rewrite <- (firstn_skipn (3 * n) rest). apply in_app_iff. left. exact X. }
    apply (realloc_silent_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo s LBf p Af nf nZ
             (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + keyZ ksp) errv oldbs K
             A0 A1 ltac:(lia) INf OLDBS OLDLEN (cg_tp CG) (cg_ra CG) RH (cg_krel CG) (cg_auxv CG) ltac:(rewrite SP; lia)
             ltac:(rewrite SP; exact STK1) CE ltac:(rewrite SP; unfold RREALLOC_STACK, RMALLOC_STACK; lia) ERR (cg_minv CG) (cg_mo CG)).
    +
      intros R' M' mo' s' errv' GP MTR Ha0 ERR' RH' KR'. exact (POSTN st4 R' M' mo' s' errv' eq_refl (or_introl eq_refl) GP Ha0 ERR' RH' KR').
    +
      intros R' M' mo' s' errv' p' Ab junk GP MTR Ha0 ERR' RNG CELLS RH' KR'. pose proof RH' as RH1. apply RHEAP_split in RH1 as [RC' PU'].
      destruct RNG as (Apos & A16 & Nn & AC' & AI).
      set (bs := firstn (Z.to_nat (Z.min nf nZ)) oldbs ++ junk) in CELLS.
      set (Fv := Fv_of R' errv' (Z_to_bv 64 Ab)). set (Gv := Gv_of bs).
      assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
      destruct (RHEAP_core_block_range s' ((p', Ab, nZ) :: lb_remove p LBf) M' (p', Ab, nZ) RC' (or_introl eq_refl)) as (B4096 & _). cbn [blk_addr fst snd] in B4096.
      pose proof (RHEAP_core_nodup s' _ M' RC') as ND. cbn [map blk_id fst] in ND. apply List.NoDup_cons_iff in ND as [NI ND'].
      assert (NEW : forall blk a, In blk (lb_remove p LBf) -> blk_addr blk <= a < blk_addr blk + blk_size blk -> ~ (Ab <= a < Ab + nZ)).
      { intros blk a Hblk Hin R5.
        assert (NEb : blk_id (p', Ab, nZ) <> blk_id blk).
        { cbn [blk_id fst]. intros X. apply NI. rewrite X. apply in_map_iff. exists blk. auto. }
        destruct (RHEAP_core_blocks_disjoint s' _ M' (p', Ab, nZ) blk RC' (or_introl eq_refl) (or_intror Hblk) NEb) as [D|D];
          unfold blk_addr, blk_size in D, Hin; cbn [fst snd] in D, Hin; lia. }
      assert (LJ : length bs = Z.to_nat nZ) by (destruct CELLS as [[[LJ _] _] _]; exact LJ).
      assert (GJ : forall o, 0 <= o < nZ -> nth_error bs (Z.to_nat o) = Some (Gv 16 o)).
      { intros o Ho. unfold Gv, Gv_of. apply nth_error_nth'. rewrite LJ. lia. }

      pose proof (lb_remove_perm p Af nf LBf INf NDid) as PL.
      assert (NOTIN : ~ In (Af, nf) (blocks_of (lb_remove p LBf))).
      { intros X. apply in_map_iff in X as (blk & Eb & Hblk). apply In_lb_remove in Hblk as [Hblk NEp].
        assert (NEb : blk_id (p, Af, nf) <> blk_id blk) by (cbn [blk_id fst]; congruence).
        pose proof (f_equal fst Eb) as E1. pose proof (f_equal snd Eb) as E2. unfold blk_addr, blk_size in E1, E2. cbn [fst snd] in E1, E2.
        destruct (RHEAP_core_blocks_disjoint s LBf (ms_mem ms) (p, Af, nf) blk RC INf Hblk NEb) as [D|D]; unfold blk_addr, blk_size in D; cbn [fst snd] in D; lia. }
      assert (PERM' : Permutation (blocks_of (lb_remove p LBf)) (remove iv_eq_dec (Af, nf) LB)).
      { apply Permutation_sym. eapply Permutation_trans. { apply perm_remove. apply Permutation_sym. exact (cg_perm CG). }
        eapply Permutation_trans. { apply perm_remove. apply (Permutation_map (fun b => (blk_addr b, blk_size b))) in PL. exact PL. }
        cbn [map blk_addr blk_size fst snd remove]. destruct (iv_eq_dec (Af, nf) (Af, nf)); [| congruence].
        rewrite notin_remove by exact NOTIN. apply Permutation_refl. }
      assert (AWH : aw_holdsI (den E (VL wones)) ((Ab, nZ) :: remove iv_eq_dec (Af, nf) LB) M' mo').
      { exists s', ((p', Ab, nZ) :: lb_remove p LBf). split; [cbn [blocks_of map blk_addr blk_size fst snd]; apply perm_skip; exact PERM'|].
        split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
        split; [apply pclaim_none; rewrite den_VL, wbv_unsigned; change (w2Z wones) with (2 ^ 64 - 1); lia|].
        apply (repl_post (lb_remove p LBf) _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG)). }

      assert (NB : to_Z (wl (wsub nw wone)) + 1 < two63) by (rewrite EN'; pose proof (cg_n255 CG) as N255; rewrite N in N255; unfold two63; lia).
      assert (DEC' : decode (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL (wadd (wsub nw wone) wone)
                                 :: firstn (3 * pred n) (ws' ++ skipn (3 * n) rest) ++ [VP (PrimInt63.add (s_next st) 16%uint63) wzero; getr st X11; VL CtrLib.K_BLOCK]
                                    ++ skipn (3 * pred n) (ws' ++ skipn (3 * n) rest)))
                     = Some (w2Z md, den (E' E st Fv Gv) (VL wones), (l1 ++ l2) ++ [Win Ab nZ K_BLOCK], map (den E) (skipn (3 * n) rest))).
      { rewrite (decode_add_window (E' E st Fv Gv) md (VL wones) (wsub nw wone) (ws' ++ skipn (3 * n) rest) (pred n) _ _ _ T' ltac:(rewrite EN'; lia) ltac:(rewrite length_app; lia) NB).
        rewrite (wins_of_prefix _ (pred n) ws' _ ltac:(lia)), (wins_of_E' E st Fv Gv (pred n) ws' AVW), WS'.
        rewrite (skipn_app_exact ws' (skipn (3 * n) rest) (3 * pred n) ltac:(lia)).
        assert (EVK : ev (E' E st Fv Gv) (PrimInt63.add (s_next st) 16%uint63) = Z_to_bv 64 Ab).
        { unfold E'. rewrite (ev_above_lit E (s_next st) Fv Gv 16%uint63 K16). reflexivity. }
        rewrite den_VPz, EVK, Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64 in *; lia).
        rewrite (den_E' E st Fv Gv _ SVn), unsigned_VL. change (w2Z CtrLib.K_BLOCK) with K_BLOCK. fold nZ. f_equal. f_equal.
        apply map_ext_in. intros u Hu. apply (den_E' E st Fv Gv). apply (forallb_In _ _ _ u AVB).
        rewrite <- (firstn_skipn (3 * n) rest). apply in_app_iff. right. exact Hu. }
      destruct (post_FB E st ms mo REALLOC_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' (lb_remove p LBf) errv' GP
                  ltac:(intros b Hb; apply In_lb_remove in Hb; exact (proj1 Hb)) ERR' PU' Fv Gv HF (Fv_of_15 _ _ _) st4
                  r0 kf rg old p Af nf (VL wones) _ l1 l2 (getr st X11) BLK_LO BLK_HI Ab nZ bs _ Hr0 E4 Hkf K0 K1 FOK INf eq_refl eq_refl
                  ltac:(intros b Hb Nb; apply In_lb_remove; auto) ltac:(intros b Hb; apply In_lb_remove in Hb; exact (proj2 Hb))
                  WS PROV DEC' eq_refl SVn eq_refl (Fv_of_16 _ _ _) GJ CELLS B4096 AC' A16 ltac:(unfold RIMG_LO, RIMG_HI; lia)
                  ltac:(change (w2Z BLK_LO) with 4096; change (w2Z BLK_HI) with (2 ^ 47 - 1); lia) NEW AWH Ha0 eq_refl) as [ST MP'].
      rewrite (cg_ra_r CG). refine (HK _ (or_intror (or_introl eq_refl)) _ _ _ (EXT E st Fv Gv) MP' _).
      refine (st_ok_fields rsegs OPS _ _ _ _ _ _ _ _ _ _ _ _ _ ST); subst st4; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next setr set_ops setregs set_next addfact alloc_post_mk fst snd]; try reflexivity.
Qed.

Theorem aligned_alloc1_sound : forall pc, to_Z pc = RALIGNED16_SYM ->
  contract_sound rsegs OPS MP PB (CtrE.aligned_alloc1_c rsegs ERRNO LIBC GOT GUARD TP CANARY pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrE.aligned_alloc1_c] in Happ. unfold CtrE.aligned_alloc1_apply in Happ.
  destruct (alloc_call rsegs ERRNO LIBC GOT GUARD TP CANARY ALIGNED_STACK st) as [[[[r ksp] hargs0] wnl]|] eqn:AC; [|discriminate].
  destruct (getr st X10) as [al| | | | | | | | | |] eqn:HX10; try discriminate.
  destruct (alloc_call_sound Cw OPS OPS_plain OPS_holds1 PB CANARY PB_canary PB_secret E st ms mo ALIGNED_STACK r ksp hargs0 wnl HS HPB ltac:(vm_compute; reflexivity) AC)
    as (off & r1 & n & md & A & nw & rest & s & LBf & LB & CG).
  pose proof (cg_hargs CG) as EH. rewrite EH, heap_drop_A_eq in Happ.
  destruct (weqb al (wlit 16%uint63)) eqn:AL; [|discriminate]. apply weqb_eq in AL. subst al.
  destruct (size_ok (s_facts st) (getr st X11)) eqn:SZ; [|discriminate]. cbn [andb] in Happ.
  unfold malloc_posts, malloc_posts_rg in Happ.
  destruct (alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp) as [st4|] eqn:H4; [|discriminate].
  cbn [block_posts] in Happ.
  destruct (block_post st4 (VL md :: VL wones :: VL nw :: rest) (getr st X11) (BLK_LO, BLK_HI)) as [stB|] eqn:HB; [|discriminate].
  apply Some_inj in Happ. subst sts.
  pose proof (size_ok_sound E _ _ (so_facts _ _ _ _ _ _ HS) SZ) as NZ. set (nZ := bv_unsigned (den E (getr st X11))) in *.
  pose proof (cg_nw CG) as (T & N & L).
  assert (SVn : sv_vars_below (s_next st) (getr st X11) = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB.
    do 5 (apply andb_prop in SVB as [SVB ?]). exact (rf_allb_get _ _ _ SVB X11). }
  assert (AVB : forallb (sv_vars_below (s_next st)) rest = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB. apply andb_prop in SVB as [_ OV].
    pose proof (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) as AV. rewrite EH in AV. cbn [op_args forallb] in AV.
    apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. exact AV. }
  pose proof (cg_ms CG) as MSE. rewrite Hspc in MSE. cbn [c_pc CtrE.aligned_alloc1_c] in MSE. rewrite Hpc in MSE. rewrite MSE.
  pose proof (cg_stk CG) as STK. pose proof (cg_room CG) as ROOM. pose proof (cg_hi CG) as HI. pose proof (cg_ceil CG) as CE.
  pose proof (int_range ALIGNED_STACK) as RAS. change (to_Z ALIGNED_STACK) with 8224 in ROOM, RAS.
  destruct (stk_split rsegs (ms_mem ms) _ (bv_unsigned (ev E STACK_ID) + keyZ ksp) _ STK ltac:(lia)) as [STK1 _].
  destruct (cg_errno CG) as [errv ERR].
  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 16).
  { rewrite <- reg_of_X10, (cg_regs CG X10), HX10, den_VL. reflexivity. }
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 nZ).
  { subst nZ. rewrite <- reg_of_X11, (cg_regs CG X11). symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (cg_sp CG) as SP.
  apply (aligned16_silent_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo s LBf nZ
           (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + keyZ ksp) errv K
           A0 A1 ltac:(lia) (cg_tp CG) (cg_ra CG) (cg_rheap CG) (cg_krel CG) (cg_auxv CG) ltac:(rewrite SP; lia)
           ltac:(rewrite SP; exact STK1) CE ltac:(rewrite SP; unfold RALIGNED16_STACK, RMALLOC_STACK; lia) ERR (cg_minv CG) (cg_repl CG) (cg_mo CG)).
  -
    intros R' M' mo' s' errv' GP MPATH MTR Ha0 ERR' RH' KR'. apply RHEAP_split in RH' as [RC' PU'].
    set (Fv := Fv_of R' errv' (Z_to_bv 64 0)). set (Gv := Gv_of []).
    assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
    assert (DECN : decode (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest)) = Some (w2Z md, wbv wones, wins_of E n rest, map (den E) (skipn (3 * n) rest))).
    { rewrite (decode_hargs (E' E st Fv Gv) md (VL wones) nw rest n T N L), (wins_of_E' E st Fv Gv n rest AVB), den_VL. f_equal. f_equal.
      apply map_ext_in. intros u Hu. apply (den_E' E st Fv Gv). apply (forallb_In _ _ _ u AVB).
      rewrite <- (firstn_skipn (3 * n) rest). apply in_app_iff. right. exact Hu. }
    assert (HH : St.op_holds OPS HEAP_ID (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest)) M' mo').
    { rewrite OPS_holds1. exists (w2Z md), (wbv wones), (wins_of E n rest), (map (den E) (skipn (3 * n) rest)), LB.
      split; [exact DECN|]. split; [| split; [exact (cg_wf CG)| exact (cw_post LBf LB _ _ _ _ _ _ (cg_perm CG) (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_cw CG))]].
      apply aw_holdsW_intro; [| exact (cg_ng CG)]. exists s', LBf. split; [exact (cg_perm CG)|]. split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
      split; [apply pclaim_none; rewrite wbv_unsigned; change (w2Z wones) with (2 ^ 64 - 1); lia|].
      exact (repl_post LBf _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG)). }
    assert (FP : forall a, Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest))) ->
                           Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E) hargs0))).
    { intros a X. rewrite OPS_fp1 in X |- *. unfold heap_fp in X |- *. rewrite DECN in X. rewrite (cg_decode CG). exact X. }
    destruct (post_N E st ms mo ALIGNED_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP ERR' PU' Fv Gv HF
                (Fv_of_15 _ _ _) st4 H4 (VL wzero) (VL md :: VL wones :: VL nw :: rest) (fun b H => H)
                ltac:(rewrite den_VL, Ha0; reflexivity) HH FP) as [ST MP'].
    rewrite (cg_ra_r CG). exact (HK _ (or_introl eq_refl) _ _ _ (EXT E st Fv Gv) MP' ST).
  -
    intros R' M' mo' s' errv' p Ab junk GP MPATH MTR Ha0 ERR' RNG CELLS EXP RH' KR'. apply RHEAP_split in RH' as [RC' PU'].
    destruct RNG as (Apos & A16 & Nn & AC' & AI).
    set (Fv := Fv_of R' errv' (Z_to_bv 64 Ab)). set (Gv := Gv_of junk).
    assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
    destruct (RHEAP_core_block_range s' ((p, Ab, nZ) :: LBf) M' (p, Ab, nZ) RC' (or_introl eq_refl)) as (B4096 & _). cbn [blk_addr fst snd] in B4096.
    pose proof (RHEAP_core_nodup s' _ M' RC') as ND. cbn [map blk_id fst] in ND. apply List.NoDup_cons_iff in ND as [NI ND'].
    assert (NEW : forall b a, In b LB -> in_iv b a -> ~ (Ab <= a < Ab + nZ)).
    { intros b a Hb Hin R5.
      assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
      apply in_map_iff in Hb' as (blk & Eb & Hblk).
      assert (NEb : blk_id (p, Ab, nZ) <> blk_id blk).
      { cbn [blk_id fst]. intros X. apply NI. rewrite X. apply in_map_iff. exists blk. auto. }
      destruct (RHEAP_core_blocks_disjoint s' _ M' (p, Ab, nZ) blk RC' (or_introl eq_refl) (or_intror Hblk) NEb) as [D|D];
        unfold in_iv in Hin; rewrite <- Eb in Hin; unfold blk_addr, blk_size in D, Hin; cbn [fst snd] in D, Hin; lia. }
    assert (LJ : length junk = Z.to_nat nZ) by (destruct CELLS as [[[LJ _] _] _]; exact LJ).
    assert (GJ : forall o, 0 <= o < nZ -> nth_error junk (Z.to_nat o) = Some (Gv 16 o)).
    { intros o Ho. unfold Gv, Gv_of. apply nth_error_nth'. rewrite LJ. lia. }
    assert (AWH : aw_holdsI (den E (VL wones)) ((Ab, nZ) :: LB) M' mo').
    { exists s', ((p, Ab, nZ) :: LBf). split; [cbn [blocks_of map blk_addr blk_size fst snd]; apply perm_skip; exact (cg_perm CG)|].
      split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
      split; [apply pclaim_none; rewrite den_VL, wbv_unsigned; change (w2Z wones) with (2 ^ 64 - 1); lia|].
      exact (repl_post LBf _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG)). }
    pose proof alloc_ceiling_lt47 as C47.
    destruct (post_B E st ms mo ALIGNED_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP (fun b H => H) ERR' PU' Fv Gv HF
                (Fv_of_15 _ _ _) st4 H4 (VL md :: VL wones :: VL nw :: rest) (VL wones) (getr st X11) BLK_LO BLK_HI stB Ab nZ junk
                eq_refl HB SVn eq_refl eq_refl (Fv_of_16 _ _ _) GJ CELLS B4096 AC' A16 ltac:(unfold RIMG_LO, RIMG_HI in *; lia)
                ltac:(change (w2Z BLK_LO) with 4096; change (w2Z BLK_HI) with (2 ^ 47 - 1); lia) NEW (fun b H => H) AWH Ha0) as [ST MP'].
    rewrite (cg_ra_r CG). exact (HK _ (or_intror (or_introl eq_refl)) _ _ _ (EXT E st Fv Gv) MP' ST).
Qed.

Lemma has_block_window_sound : forall E fs k n rest, facts_hold E fs ->
  CtrE.has_block_window fs k n rest = true ->
  exists w, In w (wins_of E n rest) /\ w_lo w = bv_unsigned (ev E k) /\ 0 < w_len w /\ w_kind w = K_BLOCK.
Proof.
  intros E fs k n. induction n as [|n IH]; intros rest FH H; [discriminate H|].
  destruct rest as [|lo [|len [|kd rest']]]; try discriminate H.
  cbn [CtrE.has_block_window] in H. apply orb_prop in H as [H|H].
  - destruct lo as [|k' o| | | | | | | | |]; try discriminate H. destruct kd as [kw| | | | | | | | | |]; try discriminate H.
    apply andb_prop in H as [H LT]. apply andb_prop in H as [H KB]. apply andb_prop in H as [KE O].
    apply Uint63.eqb_correct in KE. subst k'. apply weqb_eq in O. subst o. apply weqb_eq in KB. subst kw.
    pose proof (known_ltu_sound E fs _ _ FH LT) as LT'. rewrite den_VL in LT'.
    eexists. split; [rewrite wins_of_cons; left; reflexivity|]. cbn [w_lo w_len w_kind].
    split; [rewrite den_VPz; reflexivity|]. split; [change (bv_unsigned (wbv wzero)) with 0 in LT'; exact LT'|].
    rewrite den_VL. reflexivity.
  - destruct (IH rest' FH H) as (w & IN & P). exists w. split; [rewrite wins_of_cons; right; exact IN| exact P].
Qed.

Theorem blk_side_sound : forall IMG_HI pc, to_Z IMG_HI = RIMG_HI ->
  contract_sound rsegs OPS MP PB (CtrE.blk_side_c IMG_HI pc).
Proof.
  intros IMG_HI pc HIMG st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrE.blk_side_c] in Happ. unfold CtrE.blk_side_apply in Happ.
  destruct (getr st X10) as [|k o| | | | | | | | |] eqn:HX10; try discriminate.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|] eqn:Hf; [|discriminate].
  destruct (heap_nwin hargs) as [n|] eqn:Hn; [|discriminate].
  destruct (heap_nwin_shape hargs n Hn) as (md & A & nw & rest & Eh & T & N & L). subst hargs.
  destruct (weqb o wzero && CtrE.has_block_window (s_facts st) k n rest) eqn:C; [|discriminate].
  apply andb_prop in C as [_ W]. apply Some_inj in Happ. subst sts.
  pose proof (ops_hold_find OPS E (s_ops st) (ms_mem ms) mo HEAP_ID _ (so_ops _ _ _ _ _ _ HS) Hf) as HH.
  rewrite OPS_holds1 in HH. destruct HH as (md' & aw & ws & ca & LB & D & HA & WF & HC).
  rewrite (decode_hargs E md A nw rest n T N L) in D. injection D as <- <- <- <-.
  destruct HA as ((s & LBf & P & RC & KR & MT & CL & RP) & _).
  destruct (has_block_window_sound E (s_facts st) k n rest (so_facts _ _ _ _ _ _ HS) W) as (w & INw & WLO & WLEN & WK).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & [[KS _]|[[_ INB]|[KS _]]]);
    [rewrite WK in KS; unfold K_BLOCK, K_STACK in KS; lia| | rewrite WK in KS; unfold K_SUB, K_BLOCK in KS; lia].
  assert (INB' : In (w_iv w) (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact P| exact INB]).
  apply in_map_iff in INB' as (blk & Eb & Hblk).
  destruct (RHEAP_core_block_range s LBf (ms_mem ms) blk RC Hblk) as (B4096 & _ & BC & BI & _).
  assert (EA : blk_addr blk = bv_unsigned (ev E k)) by (rewrite <- WLO; unfold w_iv in Eb; injection Eb as E1 E2; exact E1).
  assert (EN : blk_size blk = w_len w) by (unfold w_iv in Eb; injection Eb as E1 E2; exact E2).
  rewrite EA in B4096, BC, BI. rewrite EN in BC, BI.
  pose proof alloc_ceiling_lt47 as C47.
  destruct BI as [LOW|HIGH].
  - refine (HK _ (or_introl eq_refl) E ms mo (env_ext_refl (s_next st) E) HMP _).
    apply addfact_sound; [exact HS|]. cbn [fact_holds].
    change (w2Z BLK_LO) with 4096. change (w2Z (wsub IMG_LO wone)) with 65535. unfold RIMG_LO in LOW. lia.
  - refine (HK _ (or_intror (or_introl eq_refl)) E ms mo (env_ext_refl (s_next st) E) HMP _).
    apply addfact_sound; [exact HS|]. cbn [fact_holds].
    rewrite wlit_ok, HIMG. change (w2Z BLK_HI) with (2 ^ 47 - 1). lia.
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
Import F_syscalls.TwinB RMallocRep.TwinB RMallocTree.TwinB RMallocKit_B.TwinB RMalloc_iface.TwinB RMalloc_ifaceP.TwinB RF_aligned16.TwinB RRealloc_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsM OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsE OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsN.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.StateGlue OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.RegsEqv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.TreeBridgeN OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.KRel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MPath OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.Room OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.
Import HeapCore.TwinB MF.TwinB MFInst.TwinB AW.TwinB RMallocG.TwinB RAllocG.TwinB HeapCtr.TwinB.

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
Variable Cw : client_world.
Variable OPS : St.optable.

Hypothesis OPS_plain : St.plain_table OPS.
Hypothesis OPS_holds1 : forall args m mo, St.op_holds OPS HEAP_ID args m mo = heap_holds rsegs IMGX AWI Cw args m mo.
Hypothesis OPS_fp1 : forall args, St.op_fp OPS HEAP_ID args = heap_fp IMGX args.

Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> St.op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  St.op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS id args) ->
  0x53000 <= a < 0x8a000 /\ ~ ralloc_static a.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> vm_agree mo mo' -> St.op_holds OPS id args m mo ->
  St.op_holds OPS id args m mo'.
Variable MP : Model -> Prop.
Hypothesis MP_vm : forall mo mo', vm_agree mo mo' -> MP mo -> MP mo'.
Variable PB : (int -> list byte) -> Prop.
Variable CANARY : sv.
Hypothesis PB_canary : forall E, PB (eb E) -> den E CANARY = Z_to_bv 64 ssp_canary.
Hypothesis PB_secret : forall E, PB (eb E) -> forall i, (i < 8)%nat ->
  nth_error (eb E 6%uint63) (8 + i) = nth_error (le8 (wz ctx_secret)) i.

Lemma alloc_post_inv : forall st r ksp st4 r1,
  IMap.find STACK_ID (s_regs st) = Some r1 ->
  alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp = Some st4 ->
  exists r0, IMap.find 0%uint63 (s_regs st) = Some r0 /\ st4 = alloc_post_mk ERRNO LIBC GOT GUARD CANARY st r ksp r0 r1.
Proof.
  intros st r ksp st4 r1 Hr1 H. unfold alloc_post in H. rewrite Hr1 in H.
  destruct (IMap.find 0%uint63 (s_regs st)) as [r0|]; [|discriminate]. apply Some_inj in H. exists r0. auto.
Qed.

Lemma rget_core_getr : forall R F pc fc rv x, rget (Core R F pc fc rv) (reg_of_r5 x) = PropExec.getr R (reg_of_r5 x).
Proof. intros. apply rget_getr. Qed.

Lemma reg_of_X0 : reg_of_r5 X0 = 0%bv. Proof. apply bv_eq. reflexivity. Qed.
Lemma key_range_half : forall i, - two63 / 2 <= keyZ i < two63 / 2.
Proof. intros i. pose proof (keyZ_range i). change (- two63 / 2) with (- (2 ^ 62)). rewrite half63. lia. Qed.
Lemma getr_x0 : forall R, PropExec.getr R (reg_of_r5 X0) = Z_to_bv 64 0.
Proof. intros R. rewrite reg_of_X0. unfold PropExec.getr. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma kept_or_clobbered : forall x, x <> X0 -> x <> X10 -> clob_pos x = None -> In (reg_of_r5 x) kept_regs.
Proof.
  intros x N0 N10 H. destruct x; try discriminate H; try congruence;
  unfold kept_regs; cbn [In];
  repeat match goal with |- ?a = ?b \/ _ => first [left; apply bv_eq; reflexivity | right] | |- False => fail end.
Qed.

Lemma aload_priv : forall st a w v, aload rsegs st a w = Some v -> in_priv_b (s_priv st) a w = false.
Proof.
  intros st a w v H. unfold aload, do_load in H. cbn [addr_of] in H.
  destruct (IMap.find 0%uint63 (s_regs st)) as [r0|]; [|discriminate].
  destruct (Mem.okey (wlit a)) as [key|] eqn:Hk; [|discriminate].
  assert (Ek : key = a).
  { unfold Mem.okey in Hk. cbn [wt wl wlit] in Hk. destruct (PrimInt63.ltb a bit62i); [injection Hk as <-; reflexivity| discriminate]. }
  subst key. destruct (can_read rsegs (s_facts st) (s_priv st) 0%uint63 r0 a w) eqn:CR; [|discriminate].
  unfold can_read in CR. rewrite Uint63.eqb_refl in CR. apply andb_prop in CR as [_ P]. destruct (in_priv_b (s_priv st) a w); [discriminate| reflexivity].
Qed.

Lemma nth_error_Z_to_le_bytes : forall k z i, (i < k)%nat ->
  nth_error (Z_to_le_bytes k z) i = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat i))).
Proof.
  induction k as [|k IH]; intros z i Hi; [lia|]. cbn [Z_to_le_bytes]. destruct i as [|i].
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma byte_of_le8 : forall (w : word) i, (i < 8)%nat -> nth_error (le8 w) i = Some (byte_of w (Z.of_nat i)).
Proof. intros w i Hi. unfold le8, word_to_le_bytes, byte_of. apply nth_error_Z_to_le_bytes. exact Hi. Qed.
Lemma byte_of_le4 : forall (w : word) i, (i < 4)%nat -> nth_error (le4 w) i = Some (byte_of w (Z.of_nat i)).
Proof. intros w i Hi. unfold le4, byte_of. apply nth_error_Z_to_le_bytes. exact Hi. Qed.

Lemma rw_cell_rb : forall m A (c : Cells.cell) i, rw_cells rsegs m A [c] -> (i < length (cbytes c))%nat ->
  rb rsegs m (A + Z.of_nat i) = nth_error (cbytes c) i.
Proof.
  intros m A c i [[_ HB] _] Hi. cbn [cells_bytes] in HB. rewrite app_nil_r in HB. destruct HB as (_ & _ & HB).
  rewrite rb_mrd. apply HB. exact Hi.
Qed.

Lemma region_store_known : forall priv E m fs k r key w v,
  facts_hold E fs -> ev E 0%uint63 = Z_to_bv 64 0 ->
  St.region_ok rsegs priv E m k r -> wok w -> can_write rsegs fs priv k r key w = true ->
  (forall i, 0 <= i < to_Z w -> rb rsegs m (addrZ E k key + i) = Some (byte_of (den E v) i)) ->
  St.region_ok rsegs priv E m k (Mem.region_store r key w v).
Proof.
  intros priv E m fs k r key w v Hfs Hz RO Hw CW BY.
  destruct (region_store_sound rsegs priv E m fs k r key w v Hfs Hz RO Hw CW) as (_ & RO' & Elo & Ehi & Ew & Ebg & FR).
  cbv zeta in RO'. set (A := addrZ E k key) in *.
  set (m' := write_to_mem m (Z_to_bv 64 A) (store_bytes w (den E v))) in *.
  pose proof (can_write_sound rsegs priv E m fs k r key w Hfs Hz RO Hw CW) as (CR & _ & _).
  pose proof (can_read_sound rsegs priv E m fs k r key w Hfs Hz RO Hw CR) as (RA & RAw & _ & RNG & _). cbv zeta in RA, RAw. fold A in RA, RAw.
  assert (Hw8 : 1 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  assert (RB : forall x, 0 <= x < two64 -> rb rsegs m x = rb rsegs m' x).
  { intros x Hx. destruct (Z_lt_le_dec x A) as [L|G]; [| destruct (Z_lt_le_dec x (A + to_Z w)) as [L2|G2]].
    - unfold rb. rewrite (FR x Hx) by lia. reflexivity.
    - replace x with (A + (x - A)) by lia. rewrite (BY (x - A)) by lia.
      unfold rb. subst m'. rewrite (write_to_mem_in m A (store_bytes w (den E v)) (x - A));
        [| lia | rewrite store_bytes_length, Z2Nat.id; unfold two64 in *; lia| rewrite store_bytes_length, Z2Nat.id; lia].
      rewrite store_bytes_nth_error by lia. reflexivity.
    - unfold rb. rewrite (FR x Hx) by lia. reflexivity. }
  apply (region_ok_fine_frame rsegs priv E m' m k (Mem.region_store r key w v) Hz RO').
  - intros o H1 H2 _. apply RB.
    destruct (PrimInt63.eqb k 0%uint63) eqn:K.
    + destruct (H2 eq_refl) as (Q & _). apply Uint63.eqb_correct in K. subst k. rewrite (ev0_zero E Hz). rewrite half63 in Q. unfold two64. lia.
    + specialize (H1 eq_refl). unfold loZ, hiZ in H1. rewrite Elo, Ehi in H1. pose proof (ro_range _ _ _ _ _ _ RO K) as [R1 R2].
      unfold loZ, hiZ in R1, R2. lia.
  - intros K a Ha. unfold loZ, hiZ in Ha. rewrite Elo, Ehi in Ha. destruct (ro_valid _ _ _ _ _ _ RO K a Ha) as (V1 & V2 & _).
    split; [exact V1|]. rewrite Ew. exact V2.
Qed.

Ltac zofN_lits_in H := repeat match type of H with context [Z.of_N ?x] => let v := eval vm_compute in (Z.of_N x) in change (Z.of_N x) with v in H end.
Ltac seg_cases H :=
  unfold rsegs, Ubsan.M.loaded_segments,
    Ubsan.Ubsan_loaded_segments in H; cbn [find_segment] in H;
  repeat match type of H with (if ?c then _ else _) = _ => destruct c eqn:?Q end;
  repeat match goal with X : _ && _ = true |- _ => zofN_lits_in X; apply andb_prop in X;
                             let X1 := fresh "SB" in let X2 := fresh "SB" in destruct X as [X1 X2]; apply Z.leb_le in X1; apply Z.leb_le in X2
                        | X : _ && _ = false |- _ => zofN_lits_in X; apply andb_false_iff in X; rewrite !Z.leb_gt in X end.

Lemma rw_seg_range : forall a seg, find_segment rsegs a 1 = Some seg -> seg_writable seg = true -> 0x53000 <= a < 0x8a000.
Proof.
  intros a seg H W. seg_cases H; try discriminate H; injection H as <-; cbn in W; try discriminate W; lia.
Qed.

Lemma hi_seg : forall a, 0x57000 <= a < 0x8a000 -> exists seg, find_segment rsegs a 1 = Some seg.
Proof.
  intros a Ha. destruct (find_segment rsegs a 1) as [seg|] eqn:H; [exists seg; reflexivity| exfalso].
  seg_cases H; try discriminate H; lia.
Qed.

Lemma del_window_wins : forall E0 m ws lo ws', del_window m ws lo = Some ws' -> (3 * m <= length ws)%nat ->
  exists l1 len l2, wins_of E0 m ws = l1 ++ Win (bv_unsigned (den E0 lo)) (bv_unsigned (den E0 len)) K_BLOCK :: l2
    /\ wins_of E0 (pred m) ws' = l1 ++ l2 /\ skipn (3 * pred m) ws' = skipn (3 * m) ws /\ (3 * pred m <= length ws')%nat /\ (1 <= m)%nat.
Proof.
  intros E0 m. induction m as [|m IH]; intros ws lo ws' H L; [cbn in H; destruct ws; discriminate|].
  destruct ws as [|l [|sz [|kd ws0]]]; try (cbn in H; discriminate). cbn [del_window] in H. cbn [length] in L.
  destruct (sv_eqb l lo && sv_eqb kd (VL CtrLib.K_BLOCK)) eqn:C.
  - apply Some_inj in H. subst ws'. apply andb_prop in C as [C1 C2]. apply sv_eqb_eq in C1. apply sv_eqb_eq in C2. subst l kd.
    exists [], sz, (wins_of E0 m ws0). rewrite wins_of_cons, unsigned_VL. cbn [app pred]. repeat split; try reflexivity; try lia.
    replace (3 * S m)%nat with (S (S (S (3 * m)))) by lia. reflexivity.
  - destruct (del_window m ws0 lo) as [ws''|] eqn:D; [|discriminate]. apply Some_inj in H. subst ws'.
    destruct (IH ws0 lo ws'' D ltac:(lia)) as (l1 & len & l2 & W1 & W2 & SK & L2 & M1).
    exists (Win (bv_unsigned (den E0 l)) (bv_unsigned (den E0 sz)) (bv_unsigned (den E0 kd)) :: l1), len, l2.
    rewrite wins_of_cons, W1. cbn [app]. split; [reflexivity|].
    destruct m as [|m']; [lia|]. cbn [pred] in *. rewrite wins_of_cons, W2. split; [reflexivity|].
    replace (3 * S m')%nat with (S (S (S (3 * m')))) by lia. replace (3 * S (S m'))%nat with (S (S (S (3 * S m')))) by lia.
    cbn [skipn length]. rewrite SK. replace (3 * S m')%nat with (S (S (S (3 * m')))) by lia. cbn [skipn]. repeat split; try reflexivity; lia.
Qed.

Lemma free_ok_inv : forall st wl kf lenf, free_ok st wl kf = Some lenf ->
  exists rf, IMap.find kf (s_regs st) = Some rf /\ win_lookup wl kf = Some (lenf, CtrLib.K_BLOCK)
    /\ Mem.rg_lo rf = 0%uint63 /\ known_ltu (s_facts st) (VL wzero) (Mem.rg_hi rf) = true /\ known_leu_q (s_facts st) (Mem.rg_hi rf) lenf = true
    /\ forall k len kd, In (k, len, kd) wl -> k <> kf ->
         exists rg, IMap.find k (s_regs st) = Some rg /\ Mem.rg_lo rg = 0%uint63
           /\ (known_ltu (s_facts st) (VL wzero) (Mem.rg_hi rg) = true
               \/ (kd <> CtrLib.K_BLOCK /\ known_eq (s_facts st) (Mem.rg_hi rg) len = true
                   /\ exists k3 len3, In (k3, len3, CtrLib.K_BLOCK) wl /\ k3 <> kf))
           /\ known_leu_q (s_facts st) (Mem.rg_hi rg) len = true /\ (Mem.rg_w rf = true \/ Mem.rg_w rg = true)
           /\ (kd = CtrLib.K_BLOCK \/ known_eq (s_facts st) (Mem.rg_hi rf) lenf = true).
Proof.
  intros st wl kf lenf H. unfold free_ok in H.
  destruct (IMap.find kf (s_regs st)) as [rf|] eqn:Hrf; [|discriminate].
  destruct (win_lookup wl kf) as [[lenf' kdf]|] eqn:WL; [|discriminate].
  destruct (negb (weqb kdf CtrLib.K_BLOCK) || negb (PrimInt63.eqb (Mem.rg_lo rf) 0) || negb (known_ltu (s_facts st) (VL wzero) (Mem.rg_hi rf))
            || negb (known_leu_q (s_facts st) (Mem.rg_hi rf) lenf')) eqn:C; [discriminate|].
  apply orb_false_iff in C as [C C4]. apply orb_false_iff in C as [C C3]. apply orb_false_iff in C as [C1 C2].
  apply negb_false_iff in C1. apply negb_false_iff in C2. apply negb_false_iff in C3. apply negb_false_iff in C4.
  apply weqb_eq in C1. apply Uint63.eqb_correct in C2. subst kdf.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:FA end; [|discriminate]. apply Some_inj in H. subst lenf'.
  exists rf. repeat (split; [assumption || reflexivity|]).
  intros k len kd Hin NK. pose proof (proj1 (forallb_forall _ _) FA _ Hin) as X. cbv beta iota in X.
  destruct (Uint63.eqb k kf) eqn:Q; [apply Uint63.eqb_correct in Q; congruence|]. cbn [orb] in X.
  destruct (IMap.find k (s_regs st)) as [rg|]; [|discriminate]. exists rg.
  apply andb_prop in X as [X X6]. apply andb_prop in X as [X X5]. apply andb_prop in X as [X X4]. apply andb_prop in X as [X1 X3].
  apply Uint63.eqb_correct in X1. split; [reflexivity|]. split; [exact X1|]. split; [| split; [exact X3|]; split].
  - apply orb_prop in X6 as [X6|X6]; [left; exact X6| right].
    apply andb_prop in X6 as [X6 OB]. apply andb_prop in X6 as [NKB HEQ]. apply negb_true_iff in NKB.
    split; [intros ->; rewrite weqb_refl in NKB; discriminate NKB|]. split; [exact HEQ|].
    apply existsb_exists in OB as ([[k3 len3] kd3] & I3 & CK3). apply andb_prop in CK3 as [N3 K3].
    apply negb_true_iff in N3. apply Uint63.eqb_false_spec in N3. apply weqb_eq in K3. subst kd3. exists k3, len3. auto.
  - apply orb_prop in X4 as [X4|X4]; [left| right]; exact X4.
  - apply orb_prop in X5 as [X5|X5]; [left; apply weqb_eq in X5; exact X5| right; exact X5].
Qed.

Lemma windows_anchored_nodup : forall R wl k len kd len' kd',
  windows_anchored R wl = true -> In (k, len, kd) wl -> In (k, len', kd') wl -> len = len' /\ kd = kd'.
Proof.
  intros R wl. induction wl as [|[[k0 len0] kd0] wl IH]; intros k len kd len' kd' H I1 I2; [destruct I1|].
  cbn [windows_anchored] in H. destruct (IMap.find k0 R); [|discriminate]. destruct (win_lookup wl k0) eqn:WL; [discriminate|].
  assert (NOTIN : forall ln kn, ~ In (k0, ln, kn) wl).
  { intros ln kn X. clear IH I1 I2. induction wl as [|[[k1 l1] d1] wl IH2]; [destruct X|]. cbn [win_lookup] in WL.
    destruct (Uint63.eqb k1 k0) eqn:Q; [discriminate|]. destruct X as [X|X]; [injection X as -> -> ->; rewrite Uint63.eqb_refl in Q; discriminate|].
    cbn [windows_anchored] in H. destruct (IMap.find k1 R); [|discriminate]. destruct (win_lookup wl k1); [discriminate|]. exact (IH2 WL H X). }
  destruct I1 as [I1|I1]; destruct I2 as [I2|I2].
  - rewrite I1 in I2. injection I2 as <- <-. auto.
  - injection I1 as -> -> ->. exfalso. exact (NOTIN _ _ I2).
  - injection I2 as -> -> ->. exfalso. exact (NOTIN _ _ I1).
  - exact (IH k len kd len' kd' H I1 I2).
Qed.

Lemma wins_cover : forall E0 m ws wl w, nonstack_windows m ws = Some wl -> In w (wins_of E0 m ws) ->
  w_kind w = K_STACK \/ exists k len kd, In (k, len, kd) wl /\ w = Win (bv_unsigned (ev E0 k)) (bv_unsigned (den E0 len)) (w2Z kd).
Proof.
  intros E0 m. induction m as [|m IH]; intros ws wl w H Hin; [destruct ws; cbn in Hin; destruct Hin|].
  destruct ws as [|wlo [|ln [|kdv ws']]]; try (cbn in Hin; destruct Hin; fail); try (cbn in H; discriminate).
  cbn [nonstack_windows] in H. destruct kdv as [kw| | | | | | | | | |]; try discriminate.
  destruct (nonstack_windows m ws') as [l|] eqn:NW; [|discriminate].
  rewrite wins_of_cons in Hin.
  destruct (weqb kw wzero) eqn:Z0.
  - apply Some_inj in H. subst wl. destruct Hin as [<-|Hin].
    + left. cbn [w_kind]. rewrite unsigned_VL. apply weqb_eq in Z0. subst kw. reflexivity.
    + exact (IH ws' l w NW Hin).
  - destruct wlo as [|k0 o0| | | | | | | | |]; try discriminate.
    destruct (weqb o0 wzero && negb (PrimInt63.eqb k0 0) && negb (PrimInt63.eqb k0 STACK_ID)) eqn:C; [|discriminate].
    apply Some_inj in H. subst wl. apply andb_prop in C as [C _]. apply andb_prop in C as [C1 _]. apply weqb_eq in C1. subst o0.
    destruct Hin as [<-|Hin].
    + right. exists k0, ln, kw. split; [left; reflexivity|]. rewrite den_VPz, unsigned_VL. reflexivity.
    + destruct (IH ws' l w NW Hin) as [S|(k & len & kd & I & ->)]; [left; exact S| right]. exists k, len, kd. split; [right; exact I| reflexivity].
Qed.

Lemma del_window_has : forall m ws kf ws' wl, del_window m ws (VP kf wzero) = Some ws' -> nonstack_windows m ws = Some wl ->
  exists len, In (kf, len, CtrLib.K_BLOCK) wl.
Proof.
  induction m as [|m IH]; intros ws kf ws' wl H N; [cbn in H; destruct ws; discriminate|].
  destruct ws as [|wlo [|ln [|kdv ws0]]]; try (cbn in H; discriminate). cbn [del_window] in H. cbn [nonstack_windows] in N.
  destruct kdv as [kw| | | | | | | | | |]; try discriminate.
  destruct (nonstack_windows m ws0) as [l|] eqn:NW; [|discriminate].
  destruct (sv_eqb wlo (VP kf wzero) && sv_eqb (VL kw) (VL CtrLib.K_BLOCK)) eqn:C.
  - apply andb_prop in C as [C1 C2]. apply sv_eqb_eq in C1. apply sv_eqb_eq in C2. injection C2 as ->. subst wlo.
    cbn [weqb wone wzero CtrLib.K_BLOCK] in N. rewrite weqb_refl in N || idtac.
    destruct (weqb CtrLib.K_BLOCK wzero) eqn:KZ; [apply weqb_eq in KZ; discriminate KZ|].
    cbn [andb negb] in N. destruct (PrimInt63.eqb kf 0); [discriminate|]. destruct (PrimInt63.eqb kf STACK_ID); [discriminate|].
    apply Some_inj in N. subst wl. exists ln. left. reflexivity.
  - destruct (del_window m ws0 (VP kf wzero)) as [ws''|] eqn:D; [|discriminate].
    assert (TL : forall l', (exists len, In (kf, len, CtrLib.K_BLOCK) l) -> (forall x, In x l -> In x l') -> exists len, In (kf, len, CtrLib.K_BLOCK) l').
    { intros l' [len I] SUB. exists len. apply SUB. exact I. }
    destruct (weqb kw wzero).
    + apply Some_inj in N. subst wl. exact (IH ws0 kf ws'' l D NW).
    + destruct wlo as [|k0 o0| | | | | | | | |]; try discriminate.
      destruct (weqb o0 wzero && negb (PrimInt63.eqb k0 0) && negb (PrimInt63.eqb k0 STACK_ID)); [|discriminate].
      apply Some_inj in N. subst wl. apply (TL _ (IH ws0 kf ws'' l D NW)). intros x Hx. right. exact Hx.
Qed.

Definition anchors (wl : list (int * sv * w64)) : list int := map (fun t => fst (fst t)) wl.

Lemma windows_anchored_nodup_anchors : forall R wl, windows_anchored R wl = true -> List.NoDup (anchors wl).
Proof.
  intros R wl. induction wl as [|[[k0 len0] kd0] wl IH]; intros H; [constructor|].
  cbn [windows_anchored] in H. destruct (IMap.find k0 R); [|discriminate]. destruct (win_lookup wl k0) eqn:WL; [discriminate|].
  cbn [anchors map fst]. constructor; [| apply IH; exact H].
  intros X. unfold anchors in X. apply in_map_iff in X as ([[k1 l1] d1] & E1 & I1). cbn [fst] in E1. subst k1.
  clear IH H. induction wl as [|[[k2 l2] d2] wl IH2]; [destruct I1|]. cbn [win_lookup] in WL.
  destruct (Uint63.eqb k2 k0) eqn:Q; [discriminate|]. destruct I1 as [I1|I1]; [injection I1 as -> -> ->; rewrite Uint63.eqb_refl in Q; discriminate|].
  exact (IH2 WL I1).
Qed.

Lemma del_window_prov : forall E0 m ws kf ws' wl, nonstack_windows m ws = Some wl -> del_window m ws (VP kf wzero) = Some ws' ->
  List.NoDup (anchors wl) ->
  forall w, In w (wins_of E0 (pred m) ws') ->
    w_kind w = K_STACK \/ exists k len kd, In (k, len, kd) wl /\ k <> kf /\ w = Win (bv_unsigned (ev E0 k)) (bv_unsigned (den E0 len)) (w2Z kd).
Proof.
  intros E0 m. induction m as [|m IH]; intros ws kf ws' wl N H ND w Hin; [cbn in H; destruct ws; discriminate|].
  destruct ws as [|wlo [|ln [|kdv ws0]]]; try (cbn in H; discriminate). cbn [del_window] in H. cbn [nonstack_windows] in N.
  destruct kdv as [kw| | | | | | | | | |]; try discriminate.
  destruct (nonstack_windows m ws0) as [l|] eqn:NW; [|discriminate].
  cbn [pred] in Hin.
  destruct (sv_eqb wlo (VP kf wzero) && sv_eqb (VL kw) (VL CtrLib.K_BLOCK)) eqn:C.
  -
    apply Some_inj in H. subst ws'. apply andb_prop in C as [C1 C2]. apply sv_eqb_eq in C1. apply sv_eqb_eq in C2. injection C2 as ->. subst wlo.
    destruct (weqb CtrLib.K_BLOCK wzero) eqn:KZ; [apply weqb_eq in KZ; discriminate KZ|].
    cbn [andb negb] in N. rewrite weqb_refl in N. cbn [andb negb] in N.
    destruct (PrimInt63.eqb kf 0); [discriminate|]. destruct (PrimInt63.eqb kf STACK_ID); [discriminate|].
    apply Some_inj in N. subst wl. cbn [anchors map fst] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
    destruct (wins_cover E0 m ws0 l w NW Hin) as [S|(k & len & kd & I & ->)]; [left; exact S| right].
    exists k, len, kd. split; [right; exact I|]. split; [| reflexivity].
    intros ->. apply NI. unfold anchors. apply in_map_iff. exists (kf, len, kd). auto.
  - destruct (del_window m ws0 (VP kf wzero)) as [ws''|] eqn:D; [|discriminate]. apply Some_inj in H. subst ws'.
    destruct m as [|m']; [cbn in D; destruct ws0; discriminate|].
    rewrite wins_of_cons in Hin.
    destruct (weqb kw wzero) eqn:Z0.
    + apply Some_inj in N. subst wl. destruct Hin as [<-|Hin].
      * left. cbn [w_kind]. rewrite unsigned_VL. apply weqb_eq in Z0. subst kw. reflexivity.
      * exact (IH ws0 kf ws'' l NW D ND w Hin).
    + destruct wlo as [|k0 o0| | | | | | | | |]; try discriminate.
      destruct (weqb o0 wzero && negb (PrimInt63.eqb k0 0) && negb (PrimInt63.eqb k0 STACK_ID)) eqn:CC; [|discriminate].
      apply Some_inj in N. subst wl. apply andb_prop in CC as [CC _]. apply andb_prop in CC as [C1 _]. apply weqb_eq in C1. subst o0.
      cbn [anchors map fst] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
      assert (NK : k0 <> kf).
      { intros ->. destruct (del_window_has _ ws0 kf ws'' l D NW) as [len I]. apply NI. unfold anchors. apply in_map_iff. exists (kf, len, CtrLib.K_BLOCK). auto. }
      destruct Hin as [<-|Hin].
      * right. exists k0, ln, kw. split; [left; reflexivity|]. split; [exact NK|]. rewrite den_VPz, unsigned_VL. reflexivity.
      * destruct (IH ws0 kf ws'' l NW D ND w Hin) as [S|(k & len & kd & I & NK' & ->)]; [left; exact S| right].
        exists k, len, kd. split; [right; exact I|]. auto.
Qed.

Lemma set_op_same : forall id os args, find_op id os = Some args -> set_op id args os = os.
Proof.
  intros id os args. induction os as [|o os IH]; intros H; [discriminate|]. cbn [find_op set_op] in H |- *.
  destruct (Uint63.eqb (op_id o) id) eqn:Q.
  - injection H as <-. apply Uint63.eqb_correct in Q. destruct o as [i a]. cbn [op_id op_args] in *. subst i. reflexivity.
  - rewrite (IH H). reflexivity.
Qed.

Lemma st_ok_fields : forall segs OPS0 E0 st1 st2 ms0 mo0,
  s_pc st2 = s_pc st1 -> s_rf st2 = s_rf st1 -> s_ff st2 = s_ff st1 -> s_resv st2 = s_resv st1 -> s_regs st2 = s_regs st1 ->
  s_facts st2 = s_facts st1 -> s_ops st2 = s_ops st1 -> s_priv st2 = s_priv st1 ->
  St.st_ok segs OPS0 E0 st1 ms0 mo0 -> St.st_ok segs OPS0 E0 st2 ms0 mo0.
Proof.
  intros segs OPS0 E0 st1 st2 ms0 mo0 E1 E2 E3 E4 E5 E6 E7 E8 HS. destruct HS. split; rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8; assumption.
Qed.

Lemma wsub_one_small : forall nw, wt nw = false -> 1 <= to_Z (wl nw) ->
  wt (wsub nw wone) = false /\ to_Z (wl (wsub nw wone)) = to_Z (wl nw) - 1.
Proof.
  intros nw T B.
  assert (E2 : w2Z (wsub nw wone) = w2Z nw - 1).
  { rewrite wsub_ok, (w2Z_nowt nw T). change (w2Z wone) with 1. pose proof (int_range (wl nw)). unfold two64, two63 in *. rewrite Z.mod_small; lia. }
  pose proof (w2Z_wt (wsub nw wone)) as WT. rewrite E2, (w2Z_nowt nw T) in WT. pose proof (int_range (wl nw)) as R.
  assert (T' : wt (wsub nw wone) = false) by (rewrite WT; apply Z.leb_gt; unfold two63 in *; lia).
  split; [exact T'|]. pose proof (w2Z_nowt _ T') as E3. rewrite E2, (w2Z_nowt nw T) in E3. lia.
Qed.

Lemma nonstack_windows_firstn : forall m ws, nonstack_windows m (firstn (3 * m) ws) = nonstack_windows m ws.
Proof.
  induction m as [|m IH]; intros ws; [reflexivity|].
  replace (3 * S m)%nat with (S (S (S (3 * m)))) by lia.
  destruct ws as [|a [|b [|c ws']]]; cbn [firstn nonstack_windows]; try reflexivity; try (destruct c; reflexivity).
  rewrite IH. reflexivity.
Qed.

Lemma wins_of_prefix : forall E0 m ws t, (3 * m <= length ws)%nat -> wins_of E0 m (ws ++ t) = wins_of E0 m ws.
Proof.
  intros E0 m. induction m as [|m IH]; intros ws t L; [reflexivity|].
  destruct ws as [|a [|b [|c ws']]]; cbn [length] in L; try lia. cbn [app]. rewrite !wins_of_cons, IH by lia. reflexivity.
Qed.

Lemma del_window_sub : forall m ws lo ws' x, del_window m ws lo = Some ws' -> In x ws' -> In x ws.
Proof.
  induction m as [|m IH]; intros ws lo ws' x H Hin; [cbn in H; destruct ws; discriminate|].
  destruct ws as [|a [|b [|c ws0]]]; try (cbn in H; discriminate). cbn [del_window] in H.
  destruct (sv_eqb a lo && sv_eqb c (VL CtrLib.K_BLOCK)).
  - apply Some_inj in H. subst ws'. do 3 right. exact Hin.
  - destruct (del_window m ws0 lo) as [ws''|] eqn:D; [|discriminate]. apply Some_inj in H. subst ws'.
    destruct Hin as [Hin|[Hin|[Hin|Hin]]]; [left| right; left| right; right; left| do 3 right; eapply IH; eauto]; assumption.
Qed.

Lemma del_window_split : forall E0 m ws kf ws' wl, del_window m ws (VP kf wzero) = Some ws' -> nonstack_windows m ws = Some wl ->
  (3 * m <= length ws)%nat ->
  exists l1 len l2, In (kf, len, CtrLib.K_BLOCK) wl
    /\ wins_of E0 m ws = l1 ++ Win (bv_unsigned (ev E0 kf)) (bv_unsigned (den E0 len)) K_BLOCK :: l2
    /\ wins_of E0 (pred m) ws' = l1 ++ l2 /\ length ws' = (length ws - 3)%nat /\ (1 <= m)%nat.
Proof.
  intros E0 m. induction m as [|m IH]; intros ws kf ws' wl H N L; [cbn in H; destruct ws; discriminate|].
  destruct ws as [|wlo [|ln [|kdv ws0]]]; try (cbn in H; discriminate). cbn [del_window] in H. cbn [nonstack_windows] in N. cbn [length] in L |- *.
  destruct kdv as [kw| | | | | | | | | |]; try discriminate.
  destruct (nonstack_windows m ws0) as [l|] eqn:NW; [|discriminate].
  destruct (sv_eqb wlo (VP kf wzero) && sv_eqb (VL kw) (VL CtrLib.K_BLOCK)) eqn:C.
  - apply Some_inj in H. subst ws'. apply andb_prop in C as [C1 C2]. apply sv_eqb_eq in C1. apply sv_eqb_eq in C2. injection C2 as ->. subst wlo.
    destruct (weqb CtrLib.K_BLOCK wzero) eqn:KZ; [apply weqb_eq in KZ; discriminate KZ|].
    rewrite weqb_refl in N. cbn [andb negb] in N.
    destruct (PrimInt63.eqb kf 0); [discriminate|]. destruct (PrimInt63.eqb kf STACK_ID); [discriminate|]. apply Some_inj in N. subst wl.
    exists [], ln, (wins_of E0 m ws0). split; [left; reflexivity|]. rewrite wins_of_cons, den_VPz, unsigned_VL. cbn [app pred].
    repeat split; try reflexivity; lia.
  - destruct (del_window m ws0 (VP kf wzero)) as [ws''|] eqn:D; [|discriminate]. apply Some_inj in H. subst ws'.
    assert (REC : forall l0, (forall x, In x l -> In x l0) -> nonstack_windows m ws0 = Some l ->
              exists l1 len l2, In (kf, len, CtrLib.K_BLOCK) l0
                /\ wins_of E0 (S m) (wlo :: ln :: VL kw :: ws0) = l1 ++ Win (bv_unsigned (ev E0 kf)) (bv_unsigned (den E0 len)) K_BLOCK :: l2
                /\ wins_of E0 m (wlo :: ln :: VL kw :: ws'') = l1 ++ l2 /\ length (wlo :: ln :: VL kw :: ws'') = (length ws0 + 3 - 3)%nat /\ (1 <= S m)%nat).
    { intros l0 SUB NW'. destruct (IH ws0 kf ws'' l D NW' ltac:(lia)) as (l1 & len & l2 & I & W1 & W2 & LEN & M1).
      exists (Win (bv_unsigned (den E0 wlo)) (bv_unsigned (den E0 ln)) (bv_unsigned (den E0 (VL kw))) :: l1), len, l2.
      split; [apply SUB; exact I|]. rewrite wins_of_cons, W1. cbn [app]. split; [reflexivity|].
      destruct m as [|m']; [lia|]. cbn [pred] in W2. rewrite wins_of_cons, W2. cbn [length]. repeat split; try reflexivity; lia. }
    cbn [pred]. replace (S (S (S (length ws0))) - 3)%nat with (length ws0 + 3 - 3)%nat by lia.
    destruct (weqb kw wzero).
    + apply Some_inj in N. subst wl. apply (REC l); [auto| exact NW].
    + destruct wlo as [|k0 o0| | | | | | | | |]; try discriminate.
      destruct (weqb o0 wzero && negb (PrimInt63.eqb k0 0) && negb (PrimInt63.eqb k0 STACK_ID)); [|discriminate].
      apply Some_inj in N. subst wl. apply (REC _); [intros x Hx; right; exact Hx| exact NW].
Qed.

Lemma perm_remove : forall (x : iv) l l', Permutation l l' -> Permutation (remove iv_eq_dec x l) (remove iv_eq_dec x l').
Proof.
  intros x l l' P. induction P as [| y l l' P IH | y z l | l l' l'' P1 IH1 P2 IH2].
  - constructor.
  - cbn [remove]. destruct (iv_eq_dec x y); [exact IH| apply perm_skip; exact IH].
  - cbn [remove]. destruct (iv_eq_dec x z), (iv_eq_dec x y); try apply Permutation_refl; try apply perm_swap; apply perm_skip; apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

Lemma block_windows_In : forall l k len, In (k, len) (block_windows l) -> In (k, len, CtrLib.K_BLOCK) l.
Proof.
  intros l. induction l as [|[[k0 len0] kd0] l IH]; intros k len H; [destruct H|]. cbn [block_windows] in H.
  destruct (weqb kd0 CtrLib.K_BLOCK) eqn:Q.
  - apply weqb_eq in Q. subst kd0. destruct H as [H|H]; [injection H as -> ->; left; reflexivity| right; apply IH; exact H].
  - right. apply IH. exact H.
Qed.

Lemma bufsz_pos : forall k, 0 < bufsz k.
Proof. intros k. unfold bufsz, BUF0. apply Z.mul_pos_pos; [lia|]. apply Z.pow_pos_nonneg; lia. Qed.
Lemma bufsz_S : forall k, bufsz (S k) = 2 * bufsz k.
Proof. intros k. unfold bufsz. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. Qed.
Lemma bufsz_le_10 : forall k, bufsz k <= 2 ^ 26 -> (k <= 10)%nat.
Proof.
  intros k H. destruct (Nat.le_gt_cases k 10) as [L|G]; [exact L|]. exfalso. unfold bufsz, BUF0 in H.
  assert (2 ^ 11 <= 2 ^ Z.of_nat k) by (apply Z.pow_le_mono_r; lia). change (2 ^ 26) with (65536 * 2 ^ 10) in H.
  assert (2 ^ 10 < 2 ^ 11) by (apply Z.pow_lt_mono_r; lia). nia.
Qed.

Lemma In_lb_remove : forall p0 L b, In b (lb_remove p0 L) <-> In b L /\ blk_id b <> p0.
Proof.
  intros p0 L b. induction L as [|x L IH].
  - cbn. tauto.
  - rewrite lb_remove_cons. destruct (bptr_eqb (blk_id x) p0) eqn:Q.
    + apply bptr_eqb_true in Q. rewrite IH. cbn [In]. split; [tauto|]. intros [[<-|H] N]; [congruence| auto].
    + assert (NQ : blk_id x <> p0) by (intros X; apply (proj2 (bptr_eqb_true _ _)) in X; congruence).
      cbn [In]. rewrite IH. split; [intros [<-|[H N]]; auto| intros [[<-|H] N]; auto].
Qed.

Lemma ev_above_lit : forall E0 nx Fv Gv (i : int), to_Z nx + to_Z i < wB -> ev (env_above E0 nx Fv Gv) (PrimInt63.add nx i) = Fv (to_Z i).
Proof.
  intros E0 nx Fv Gv i B. pose proof (int_range i) as R. cbn [env_above ev]. rewrite add_Z by exact B.
  destruct (Z.ltb_spec (to_Z nx + to_Z i) (to_Z nx)); [lia|]. f_equal. lia.
Qed.

Section POST.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model) (need r ksp : int) (hargs : list sv) (wnl : list (int * sv * w64)).
Variables (off : w64) (r1 : Mem.region) (n : nat) (md : w64) (A : sv) (nw : w64) (rest : list sv) (s : PState) (LBf : list block) (LB : blocks).
Hypothesis HS : St.st_ok rsegs OPS E st ms mo.
Hypothesis HPB : PB (eb E).
Hypothesis HMP : MP mo.
Hypothesis CG : callG Cw CANARY E st ms mo need r ksp hargs wnl off r1 n md A nw rest s LBf LB.

Variables (R' : bvmap 5 word) (M' : mem) (mo' : Model) (LBg : list block) (errv' : word).
Let base : Z := bv_unsigned (ev E STACK_ID).
Let sp : Z := base + keyZ ksp.
Let lo : Z := base + loZ r1.
Hypothesis GP : gpost (ms_regs ms) (ms_mem ms) mo LBg lo sp R' M' mo'.
Hypothesis HLBg : forall b, In b LBg -> In b LBf.
Hypothesis ERR' : rw_cells rsegs M' RERRNO [C4 errv'].
Hypothesis PUBS' : PUBS M'.

Variables (Fv : Z -> word) (Gv : Z -> Z -> byte).
Definition E' : env := env_above E (s_next st) Fv Gv.
Hypothesis HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x).
Hypothesis HF15 : Fv 15 = errv'.
Definition ms' : machine_state := MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None M' (seg_rom rsegs).
Variable st4 : sstate.
Hypothesis H4 : alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp = Some st4.

Lemma EXT : env_ext (s_next st) E E'.
Proof. apply env_above_ext. Qed.

Lemma NX : st_vars_below (s_next st) st = true /\ 0 < to_Z (s_next st) /\ to_Z (s_next st) + 256 <= 2 ^ 62.
Proof. apply fresh_ok_inv. exact (cg_fresh CG). Qed.

Lemma SVB_parts :
  rf_allb (sv_vars_below (s_next st)) (s_rf st) = true /\ rf_allb (sv_vars_below (s_next st)) (s_ff st) = true
  /\ resv_vars_below (s_next st) (s_resv st) = true
  /\ IMap.forallb (fun k r => PrimInt63.ltb k (s_next st) && region_vars_below (s_next st) r) (s_regs st) = true
  /\ forallb (fact_vars_below (s_next st)) (s_facts st) = true
  /\ forallb (fun o => forallb (sv_vars_below (s_next st)) (op_args o)) (s_ops st) = true.
Proof.
  destruct NX as (SVB & _). unfold st_vars_below in SVB.
  apply andb_prop in SVB as [SVB H6]. apply andb_prop in SVB as [SVB H5]. apply andb_prop in SVB as [SVB H4'].
  apply andb_prop in SVB as [SVB H3]. apply andb_prop in SVB as [H1 H2]. repeat split; assumption.
Qed.

Lemma HS' : St.st_ok rsegs OPS E' st ms mo.
Proof. destruct NX as (SVB & POS & _). exact (st_ok_reval rsegs OPS (s_next st) E E' EXT st ms mo POS SVB HS). Qed.

Lemma den_E' : forall v, sv_vars_below (s_next st) v = true -> den E' v = den E v.
Proof. intros v Hv. exact (den_reval (s_next st) E E' EXT v Hv). Qed.

Lemma ev_E'_below : forall k, to_Z k < to_Z (s_next st) -> ev E' k = ev E k.
Proof. intros k Hk. unfold E'. apply ev_below. exact Hk. Qed.

Lemma ev_E'_fresh : forall i, (i <= 200)%nat -> ev E' (addn (s_next st) i) = Fv (Z.of_nat i).
Proof.
  intros i Hi. destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  assert (EA : to_Z (addn (s_next st) i) = to_Z (s_next st) + Z.of_nat i) by (apply addn_Z; rewrite wB_two63, two63_eq; lia).
  unfold E'. rewrite ev_above by (rewrite EA; lia). rewrite EA. f_equal. lia.
Qed.

Lemma ST4 : exists r0, IMap.find 0%uint63 (s_regs st) = Some r0 /\ st4 = alloc_post_mk ERRNO LIBC GOT GUARD CANARY st r ksp r0 r1.
Proof. apply alloc_post_inv; [exact (cg_r1 CG) | exact H4]. Qed.

Lemma post_regs : forall v, den E' v = PropExec.getr R' 10%bv ->
  forall x, rget (Core R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None) (reg_of_r5 x)
            = den E' (rf_get (rf_set (s_rf (clobber st)) X10 v) x).
Proof.
  intros v Hv x. rewrite rget_core_getr.
  destruct (r5_eqb x X10) eqn:Q10.
  { apply r5_eqb_spec in Q10. subst x. rewrite rf_get_set_same. symmetry. exact Hv. }
  assert (N10 : x <> X10) by (intros ->; rewrite r5_eqb_refl in Q10; discriminate).
  rewrite rf_get_set_other by (intros Q; apply N10; symmetry; exact Q).
  change (rf_get (s_rf (clobber st)) x) with (getr (clobber st) x). rewrite getr_clobber.
  destruct (clob_pos x) as [i|] eqn:CP.
  - rewrite <- (HF x i CP). cbn [den]. rewrite ev_E'_fresh; [| destruct x; cbn in CP; try discriminate; injection CP as <-; lia].
    apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned, w2Z_wzero, Z.add_0_r. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
  - destruct (r5_eqb x X0) eqn:Q0.
    + apply r5_eqb_spec in Q0. subst x. rewrite getr_x0. change (getr st X0) with (rf_get (s_rf st) X0).
      rewrite (so_x0 _ _ _ _ _ _ HS'). rewrite den_VL. reflexivity.
    + assert (N0 : x <> X0) by (intros ->; rewrite r5_eqb_refl in Q0; discriminate).
      pose proof (gp_regs _ _ _ _ _ _ _ _ _ GP (reg_of_r5 x) (kept_or_clobbered x N0 N10 CP)) as K. rewrite K.
        rewrite (cg_regs CG x).
        symmetry. apply den_E'. destruct SVB_parts as (SVB & _). exact (rf_allb_get _ _ _ SVB x).
Qed.

Lemma reg_E' : forall k rg, IMap.find k (s_regs st) = Some rg ->
  ev E' k = ev E k /\ hiZ E' rg = hiZ E rg /\ PrimInt63.ltb k (s_next st) = true /\ region_vars_below (s_next st) rg = true.
Proof.
  intros k rg Hk. destruct SVB_parts as (_ & _ & _ & HR & _). exact (regs_reval_find (s_next st) E E' EXT _ k rg (so_bst _ _ _ _ _ _ HS) HR Hk).
Qed.

Lemma ev1_E' : ev E' STACK_ID = ev E STACK_ID.
Proof. destruct (reg_E' _ _ (cg_r1 CG)) as (X & _). exact X. Qed.

Lemma SP_R : bv_unsigned (PropExec.getr (ms_regs ms) 2%bv) = sp.
Proof. exact (cg_sp CG). Qed.

Lemma PRES : rheap_pres LBg sp (ms_mem ms) M'.
Proof. rewrite <- SP_R. exact (gp_pres _ _ _ _ _ _ _ _ _ GP). Qed.

Lemma STK' : stk rsegs M' lo sp.
Proof. rewrite <- SP_R. exact (gp_stk _ _ _ _ _ _ _ _ _ GP). Qed.

Lemma client_byte : forall a, 0 <= a < 2 ^ 64 -> rclient_addr LBg sp a ->
  M' (wa a) = ms_mem ms (wa a) /\ rb rsegs M' a = rb rsegs (ms_mem ms) a /\ (wb rsegs (ms_mem ms) a = true -> wb rsegs M' a = true).
Proof.
  intros a Ha HC. destruct (PRES a Ha HC) as [E1 W1]. split; [exact E1|]. split.
  - unfold rb. unfold wa in E1. rewrite E1. reflexivity.
  - intros W. apply wb_wview. apply W1. apply wb_wview. exact W.
Qed.

Lemma old_region_ok : forall k rg, IMap.find k (s_regs st) = Some rg -> PrimInt63.eqb k 0%uint63 = false ->
  (forall a, bv_unsigned (ev E k) + loZ rg <= a < bv_unsigned (ev E k) + hiZ E rg -> rclient_addr LBg sp a) ->
  St.region_ok rsegs (s_priv st) E' M' k rg.
Proof.
  intros k rg Hk K CL. pose proof (so_reg _ _ _ _ _ _ HS' k rg Hk) as RO. destruct (reg_E' k rg Hk) as (Ek & Eh & _).
  apply (region_ok_frame rsegs (s_priv st) E' (ms_mem ms) M' k rg (so_zero _ _ _ _ _ _ HS') RO).
  intros a Ha R _. rewrite Ek, Eh in R. destruct (client_byte a ltac:(unfold two64 in Ha; lia) (CL a (R K))) as (E1 & _). unfold wa in E1. exact E1.
Qed.

Lemma r1_ok : St.region_ok rsegs (s_priv st) E' M' STACK_ID (forget_r1 r1 ksp).
Proof.
  pose proof (cg_r1 CG) as Hr1. pose proof (cg_r1w CG) as HW. pose proof (cg_r1bg CG) as HBG. pose proof (cg_ksp CG) as Hksp.
  pose proof (cg_ksp16 CG) as K16. pose proof (cg_kspneg CG) as KNEG. pose proof (cg_lo0 CG) as LO0. pose proof (cg_room CG) as ROOM. pose proof (cg_hi CG) as HI.
  pose proof (so_reg _ _ _ _ _ _ HS' STACK_ID r1 Hr1) as RO.
  destruct (region_forget_sound rsegs (s_priv st) E' (ms_mem ms) STACK_ID r1 (Mem.granule (Mem.rg_lo r1)) (Mem.granule ksp) RO) as (RO' & Elo & Ehi & Ew & Ebg).
  fold (forget_r1 r1 ksp) in RO', Elo, Ehi, Ew, Ebg.
  destruct (reg_E' STACK_ID r1 Hr1) as (Ek & Eh & _).
  assert (LH : loZ (forget_r1 r1 ksp) = loZ r1 /\ hiZ E' (forget_r1 r1 ksp) = hiZ E r1).
  { unfold loZ, hiZ. rewrite Elo, Ehi. fold (hiZ E' r1). rewrite Eh. auto. }
  destruct LH as [Lq Hq].
  pose proof (okey_sound _ _ Hksp) as [_ Rksp]. rewrite half63 in Rksp.
  pose proof (int_range need) as Rn.
  apply (region_ok_fine_frame rsegs (s_priv st) E' (ms_mem ms) M' STACK_ID (forget_r1 r1 ksp) (so_zero _ _ _ _ _ _ HS') RO').
  - intros o R1 _ CL. specialize (R1 eq_refl). rewrite Lq, Hq in R1. rewrite Ek.
    destruct CL as [(g & gr & c & Hg & Hc & Eg & COV) | [U BG]].
    +
      unfold forget_r1, Mem.region_forget in Hg. rewrite HBG in Hg. cbn [Mem.is_bgnone Mem.rg_cells] in Hg.
      rewrite IMap.find_remove_range in Hg by exact (ro_bst _ _ _ _ _ _ RO).
      destruct (PrimInt63.leb (Mem.granule (Mem.rg_lo r1)) g && PrimInt63.ltb g (Mem.granule ksp))%bool eqn:RNG; [discriminate|].
      assert (LE : keyZ ksp <= o).
      { pose proof (keyZ_range (Mem.rg_lo r1)) as Rlo. pose proof (keyZ_range ksp) as Rk.
        destruct (granule_gidx (Mem.rg_lo r1) (key_range_half _)) as [Glo Ilo].
        destruct (granule_gidx ksp (key_range_half _)) as [Gk Ik].
        destruct (gidx_ok ksp) as [Gm _].
        assert (G0 : to_Z (Mem.gidx ksp) = 0).
        { rewrite Gm. destruct (keyZ_cases ksp) as [[_ EK]|[_ EK]]; rewrite EK in K16.
          - apply Z.mod_divide in K16; [|lia]. apply Z.mod_divide; [lia|]. destruct K16 as [q Qq]. exists (2 * q). lia.
          - replace (to_Z ksp - 2 ^ 63) with (to_Z ksp + (- 2 ^ 59) * 16) in K16 by lia. rewrite Z.mod_add in K16 by lia.
            apply Z.mod_divide in K16; [|lia]. apply Z.mod_divide; [lia|]. destruct K16 as [q Qq]. exists (2 * q). lia. }
        pose proof (Z.div_mod o 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound o 8 ltac:(lia)) as MB.
        unfold loZ in R1, ROOM, LO0.
        destruct (keyZ_cases g) as [[Rg Egk]|[Rg Egk]]; [lia|].
        destruct (keyZ_cases (Mem.granule (Mem.rg_lo r1))) as [[R2 E2]|[R2 E2]]; [lia|].
        destruct (keyZ_cases (Mem.granule ksp)) as [[R3 E3]|[R3 E3]]; [lia|].
        apply andb_false_iff in RNG. destruct RNG as [RNG|RNG].
        - destruct (lebP (Mem.granule (Mem.rg_lo r1)) g) as [X|X]; [rewrite RNG in *; discriminate || lia|]. lia.
        - destruct (ltbP g (Mem.granule ksp)) as [X|X]; [rewrite RNG in *; discriminate || lia|]. lia. }
      destruct (client_byte (bv_unsigned (ev E STACK_ID) + o) ltac:(unfold loZ in *; lia) ltac:(left; unfold sp, base; lia)) as (_ & E2 & _).
      exact E2.
    + exfalso. apply BG. unfold bg_byte. rewrite Ebg, HBG. reflexivity.
  - intros _ a Ha. rewrite Ek, Lq, Hq in Ha.
    destruct (Z_lt_le_dec a sp) as [LT|GE].
    + destruct STK' as (_ & _ & ST). destruct (ST a ltac:(unfold lo, sp in *; lia)) as [W [b Hb]].
      split; [rewrite rb_mrd, Hb; discriminate|]. intros _. apply wb_wview. exact W.
    + destruct (ro_valid _ _ _ _ _ _ RO eq_refl a ltac:(rewrite Ek, Eh; exact Ha)) as (V1 & V2 & _).
      destruct (client_byte a ltac:(lia) ltac:(left; lia)) as (_ & E2 & W2).
      split; [rewrite E2; exact V1|]. intros Wr. apply W2. apply V2. rewrite <- Ew. exact Wr.
Qed.

Lemma windows_off_image : forall a, RIMG_LO <= a < RIMG_HI -> ~ in_ws (wins_of E n rest) a.
Proof.
  intros a Ha IN. pose proof (cg_perm CG) as PERM. pose proof (cg_rheap CG) as RH. pose proof (cg_wf CG) as WF.
  apply RHEAP_split in RH as [RC _].
  unfold in_ws in IN. apply in_ivs_In in IN as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
  pose proof (proj1 (Forall_forall _ _) WF w Hw) as (W1 & W2 & W3 & [[K CE]|[[K B]|[K (b & Hb & SUB)]]]).
  - unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. pose_ceil. unfold CEIL_MIN, RIMG_HI in *. lia.
  - assert (Hb' : In (w_iv w) (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact B]).
    apply in_map_iff in Hb' as (blk & Eb & Hblk).
    destruct (RHEAP_core_block_range s LBf (ms_mem ms) blk RC Hblk) as (_ & _ & _ & B4 & _).
    unfold in_iv in Hin. rewrite <- Eb in Hin. cbn [fst snd] in Hin. unfold RIMG_LO, RIMG_HI in *. lia.
  - assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]).
    apply in_map_iff in Hb' as (blk & Eb & Hblk).
    destruct (RHEAP_core_block_range s LBf (ms_mem ms) blk RC Hblk) as (_ & _ & _ & B4 & _).
    specialize (SUB a Hin). unfold in_iv in SUB. rewrite <- Eb in SUB. cbn [fst snd] in SUB. unfold RIMG_LO, RIMG_HI in *. lia.
Qed.

Lemma heap_priv : forall a, RMLOCK <= a < RCTX + 936 -> in_priv (s_priv st) a.
Proof.
  intros a Ha. pose proof (cg_find CG) as Hf. pose proof (cg_decode CG) as D.
  assert (IMG : RIMG_LO <= a < RIMG_HI) by (unfold RMLOCK, RCTX, RIMG_LO, RIMG_HI in *; lia).
  apply (ops_apart_find rsegs OPS E (s_ops st) (s_regs st) (s_priv st) HEAP_ID hargs a (so_apart _ _ _ _ _ _ HS) Hf).
  - rewrite OPS_fp1. apply (proj2 (fp_spec IMGX _ _ _ _ _ a D)). split; [unfold RIMG_LO, RIMG_HI, two64 in *; lia|]. split.
    + intros I. apply in_IMGX in I. destruct I as [_ I2]. exact (I2 Ha).
    + apply windows_off_image. exact IMG.
  - apply hi_seg. unfold RMLOCK, RCTX in Ha. lia.
Qed.

Definition e15 : int := PrimInt63.add (s_next st) 15%uint63.
Lemma e15_addn : e15 = addn (s_next st) 15.
Proof.
  destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  unfold e15. symmetry. apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma ev_e15 : ev E' e15 = errv'.
Proof. rewrite e15_addn, ev_E'_fresh by lia. exact HF15. Qed.

Definition Me : mem := write_to_mem (ms_mem ms) (Z_to_bv 64 RERRNO) (store_bytes 4%uint63 errv').

Lemma can_write_abs : forall q a w, Mem.abs_writable rsegs (to_Z a) (to_Z w) = true -> PrimInt63.ltb a bit62i = true ->
  in_priv_b (s_priv st) a w = false -> can_write rsegs (s_facts st) (s_priv st) 0%uint63 q a w = true.
Proof. intros q a w H1 H2 H3. unfold can_write. rewrite Uint63.eqb_refl, H2, H1, H3. reflexivity. Qed.

Lemma statics_priv :
  in_priv_b (s_priv st) (PrimInt63.add LIBC 3%uint63) 1%uint63 = false /\ in_priv_b (s_priv st) (PrimInt63.add LIBC 48%uint63) 8%uint63 = false
  /\ in_priv_b (s_priv st) (PrimInt63.add LIBC 8%uint63) 8%uint63 = false /\ in_priv_b (s_priv st) GOT 8%uint63 = false
  /\ in_priv_b (s_priv st) GUARD 8%uint63 = false /\ in_priv_b (s_priv st) ERRNO 4%uint63 = false.
Proof.
  pose proof (cg_statics CG) as H. unfold statics_ok in H.
  apply andb_prop in H as [H Q6]. apply andb_prop in H as [H Q5]. apply andb_prop in H as [H Q4].
  apply andb_prop in H as [H Q3]. apply andb_prop in H as [Q1 Q2].
  apply is_litv_inv in Q1. apply is_litv_inv in Q2. apply is_sv_inv in Q3. apply is_litv_inv in Q4. apply is_sv_inv in Q5.
  destruct (aload rsegs st ERRNO 4%uint63) as [ve|] eqn:Q6'; [|discriminate].
  repeat split; eapply aload_priv; eassumption.
Qed.

Lemma claimed_dirty_r0 : forall r0 o, IMap.bst (Mem.rg_cells r0) -> 0 <= o < 2 ^ 62 ->
  claimed rsegs E' 0%uint63 (dirty_r0 LIBC r0) o -> ~ (RLIBC <= o < RLIBC + 112).
Proof.
  intros r0 o B Ho CL IN.
  destruct (dirty_range_spec (Mem.granule LIBC) LIBC_GRANS (Mem.rg_cells r0) B ltac:(rewrite wB_two63; vm_compute; reflexivity)) as [B' F].
  assert (Q : RLIBC = 8 * to_Z (Mem.granule LIBC)) by (vm_compute; reflexivity).
  set (gL := to_Z (Mem.granule LIBC)) in *.
  pose proof (Z.div_mod o 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound o 8 ltac:(lia)) as MB.
  destruct CL as [(g & gr & c & Hg & Hc & Eg & COV) | [U BG]].
  - cbn [dirty_r0 Mem.rg_cells] in Hg. rewrite F in Hg.
    destruct (keyZ_cases g) as [[Rg Ek]|[Rg Ek]]; [| lia].
    destruct (Z.leb_spec gL (to_Z g)), (Z.ltb_spec (to_Z g) (gL + Z.of_nat LIBC_GRANS)); cbn [andb] in Hg;
      try (injection Hg as <-; destruct Hc); unfold LIBC_GRANS in *; lia.
  -
    set (g := of_Z (o / 8)).
    assert (Tg : to_Z g = o / 8). { subst g. rewrite of_Z_spec. apply Z.mod_small. rewrite wB_two63, two63_eq. lia. }
    assert (Kg : keyZ g = o / 8). { destruct (keyZ_cases g) as [[_ ->]|[R _]]; lia. }
    specialize (U g (Mem.Gran true []) Kg). cbn [dirty_r0 Mem.rg_cells] in U. rewrite F, Tg in U.
    destruct (Z.leb_spec gL (o / 8)), (Z.ltb_spec (o / 8) (gL + Z.of_nat LIBC_GRANS)); cbn [andb] in U; unfold LIBC_GRANS in *; try lia.
    destruct (U eq_refl) as [D _]. discriminate D.
Qed.

Lemma r0_agree : forall o seg, 0 <= o < 2 ^ 62 -> find_segment rsegs o 1 = Some seg -> ~ in_priv (s_priv st) o ->
  ~ (RLIBC <= o < RLIBC + 112) -> ~ (RERRNO <= o < RERRNO + 4) -> rb rsegs M' o = rb rsegs (ms_mem ms) o.
Proof.
  intros o seg Ho Hseg NP NL NE.
  pose proof (cg_minv CG) as MINV. pose proof (gp_minv _ _ _ _ _ _ _ _ _ GP) as MINV'.
  pose proof (cg_pubs CG) as (PU1 & PU2 & PU3 & PU4). pose proof PUBS' as (PV1 & PV2 & PV3 & PV4).
  destruct (seg_writable seg) eqn:W.
  - pose proof (rw_seg_range o seg Hseg W) as RW.
    assert (STATIC : forall lo, lo <= o < lo + 8 ->
              rw_cells rsegs (ms_mem ms) lo [C8 (wz match lo with _ => 0 end)] -> True) by (intros; exact I). clear STATIC.
    destruct (Z_lt_le_dec o RSSP_GUARD) as [G1|G1]; [| destruct (Z_lt_le_dec o (RSSP_GUARD + 8)) as [G2|G2]].
    all: destruct (Z_lt_le_dec o RGOT_SSP) as [T1|T1]; [| destruct (Z_lt_le_dec o (RGOT_SSP + 8)) as [T2|T2]].
    all: destruct (Z_lt_le_dec o RMLOCK) as [L1|L1]; [| destruct (Z_lt_le_dec o (RCTX + 936)) as [L2|L2]].
    all: first
      [
        replace o with (RSSP_GUARD + Z.of_nat (Z.to_nat (o - RSSP_GUARD))) by lia;
        rewrite (rw_cell_rb (ms_mem ms) RSSP_GUARD (C8 (wz ssp_canary)) _ PU4) by (cbn [cbytes]; rewrite length_le8; lia);
        rewrite (rw_cell_rb M' RSSP_GUARD (C8 (wz ssp_canary)) _ PV4) by (cbn [cbytes]; rewrite length_le8; lia); reflexivity
      |
        replace o with (RGOT_SSP + Z.of_nat (Z.to_nat (o - RGOT_SSP))) by lia;
        rewrite (rw_cell_rb (ms_mem ms) RGOT_SSP (C8 (wz RSSP_GUARD)) _ PU3) by (cbn [cbytes]; rewrite length_le8; lia);
        rewrite (rw_cell_rb M' RGOT_SSP (C8 (wz RSSP_GUARD)) _ PV3) by (cbn [cbytes]; rewrite length_le8; lia); reflexivity
      |
        exfalso; apply NP; apply heap_priv; lia
      |
        destruct (client_byte o ltac:(lia) ltac:(right; left; unfold ralloc_static; unfold RLIBC, RCTX, RMLOCK, RERRNO, RSSP_GUARD, RGOT_SSP in *; lia)) as (_ & E2 & _); exact E2 ].
  - assert (N1 : ms_mem ms (wa o) = None).
    { destruct (ms_mem ms (wa o)) as [b|] eqn:Hb; [|reflexivity]. exfalso. pose proof (MINV _ _ Hb) as X. unfold ro_addr in X.
      unfold wa in X. rewrite Z_to_bv_unsigned, bv_wrap_small in X by (rewrite bv_modulus_64; unfold W64.two64; lia). rewrite Hseg, W in X. discriminate X. }
    assert (N2 : M' (wa o) = None).
    { destruct (M' (wa o)) as [b|] eqn:Hb; [|reflexivity]. exfalso. pose proof (MINV' _ _ Hb) as X. unfold ro_addr in X.
      unfold wa in X. rewrite Z_to_bv_unsigned, bv_wrap_small in X by (rewrite bv_modulus_64; unfold W64.two64; lia). rewrite Hseg, W in X. discriminate X. }
    unfold rb. unfold wa in N1, N2. rewrite N1, N2. reflexivity.
Qed.

Lemma r0_ok : forall r0, IMap.find 0%uint63 (s_regs st) = Some r0 ->
  St.region_ok rsegs (s_priv st) E' M' 0%uint63 (havoc_r0 ERRNO LIBC GOT GUARD CANARY r0 e15).
Proof.
  intros r0 Hr0.
  pose proof (cg_pubs CG) as PU. pose proof (cg_auxcell CG) as AC. destruct (cg_r3 CG) as [r3 Hr3]. destruct (cg_errno CG) as [errv ERR].
  destruct statics_priv as (P1 & P2 & P3 & P4 & P5 & P6).
  pose proof (so_zero _ _ _ _ _ _ HS') as Hz. pose proof (so_facts _ _ _ _ _ _ HS') as Hfs.
  pose proof (so_reg _ _ _ _ _ _ HS' 0%uint63 r0 Hr0) as RO0.

  pose proof (region_dirty_sound rsegs (s_priv st) E' (ms_mem ms) 0%uint63 r0 (Mem.granule LIBC) LIBC_GRANS
                ltac:(rewrite wB_two63; vm_compute; reflexivity) RO0) as RO1.
  change (St.region_ok rsegs (s_priv st) E' (ms_mem ms) 0%uint63 (dirty_r0 LIBC r0)) in RO1.

  set (Mh := write_to_mem M' (Z_to_bv 64 RERRNO) (le4 errv)).
  assert (FRh : forall a, 0 <= a < two64 -> ~ (RERRNO <= a < RERRNO + 4) -> Mh (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
  { intros a Ha Na. subst Mh. apply write_to_mem_frame; rewrite ?length_le4; unfold RERRNO, two64 in *; lia. }
  assert (INh : forall i, 0 <= i < 4 -> Mh (Z_to_bv 64 (RERRNO + i)) = nth_error (le4 errv) (Z.to_nat i)).
  { intros i Hi. subst Mh. apply write_to_mem_in; rewrite ?length_le4; unfold RERRNO, two64; lia. }
  assert (RO1h : St.region_ok rsegs (s_priv st) E' Mh 0%uint63 (dirty_r0 LIBC r0)).
  { apply (region_ok_fine_frame rsegs (s_priv st) E' (ms_mem ms) Mh 0%uint63 (dirty_r0 LIBC r0) Hz RO1); [| intros K; discriminate K].
    intros o _ H2 CL. destruct (H2 eq_refl) as (Ro & [seg Hseg] & NP). rewrite (ev0_zero E' Hz), Z.add_0_l. rewrite half63 in Ro.
    pose proof (claimed_dirty_r0 r0 o (ro_bst _ _ _ _ _ _ RO0) Ro CL) as NL.
    destruct (Z_lt_le_dec o RERRNO) as [E1|E1]; [| destruct (Z_lt_le_dec o (RERRNO + 4)) as [E2|E2]].
    2:{ unfold rb at 1. replace (Mh (Z_to_bv 64 o)) with (Mh (Z_to_bv 64 (RERRNO + (o - RERRNO)))) by (f_equal; f_equal; lia). rewrite INh by lia.
        replace o with (RERRNO + Z.of_nat (Z.to_nat (o - RERRNO))) at 2 by lia.
        rewrite (rw_cell_rb (ms_mem ms) RERRNO (C4 errv) _ ERR) by (cbn [cbytes]; rewrite length_le4; lia).
        cbn [cbytes]. destruct (nth_error (le4 errv) (Z.to_nat (o - RERRNO))) eqn:X; [reflexivity|].
        apply nth_error_None in X. rewrite length_le4 in X. lia. }
    all: unfold rb at 1; rewrite FRh by (unfold two64; lia); fold (rb rsegs M' o); apply (r0_agree o seg); try assumption; lia. }

  destruct (region_store_sound rsegs (s_priv st) E' Mh (s_facts st) 0%uint63 (dirty_r0 LIBC r0) ERRNO 4%uint63 (VP e15 wzero)
              Hfs Hz RO1h wok4 (can_write_abs (dirty_r0 LIBC r0) ERRNO 4%uint63 wr_ERRNO eq_refl P6)) as (_ & RO2 & Elo2 & Ehi2 & Ew2 & Ebg2 & FR2).
  cbv zeta in RO2, FR2. unfold addrZ in RO2, FR2. rewrite (ev0_zero E' Hz), Z.add_0_l in RO2, FR2.
  change (keyZ ERRNO) with RERRNO in RO2, FR2. change (to_Z 4%uint63) with 4 in FR2.
  replace (den E' (VP e15 wzero)) with errv' in RO2, FR2 by (rewrite den_VPz, ev_e15; reflexivity).
  set (Mhh := write_to_mem Mh (Z_to_bv 64 RERRNO) (store_bytes 4%uint63 errv')) in *.
  assert (RO2' : St.region_ok rsegs (s_priv st) E' M' 0%uint63 (Mem.region_store (dirty_r0 LIBC r0) ERRNO 4%uint63 (VP e15 wzero))).
  { apply (region_ok_fine_frame rsegs (s_priv st) E' Mhh M' 0%uint63 _ Hz RO2); [| intros K; discriminate K].
    intros o _ H2 _. destruct (H2 eq_refl) as (Ro & _ & _). rewrite (ev0_zero E' Hz), Z.add_0_l. rewrite half63 in Ro.
    destruct (Z_lt_le_dec o RERRNO) as [E1|E1]; [| destruct (Z_lt_le_dec o (RERRNO + 4)) as [E2|E2]].
    2:{ unfold rb at 2. subst Mhh.
        replace (write_to_mem Mh (Z_to_bv 64 RERRNO) (store_bytes 4 errv') (Z_to_bv 64 o))
           with (write_to_mem Mh (Z_to_bv 64 RERRNO) (store_bytes 4 errv') (Z_to_bv 64 (RERRNO + (o - RERRNO)))) by (f_equal; f_equal; lia).
        rewrite write_to_mem_in; [| unfold RERRNO; lia| rewrite store_bytes_length; change (to_Z 4%uint63) with 4; unfold RERRNO, two64; lia
                                 | rewrite store_bytes_length; change (to_Z 4%uint63) with 4; lia].
        rewrite store_bytes_nth_error by (change (to_Z 4%uint63) with 4; lia).
        replace o with (RERRNO + Z.of_nat (Z.to_nat (o - RERRNO))) at 1 by lia.
        rewrite (rw_cell_rb M' RERRNO (C4 errv') _ ERR') by (cbn [cbytes]; rewrite length_le4; lia). cbn [cbytes].
        rewrite byte_of_le4 by lia. f_equal. f_equal. lia. }
    all: unfold rb; subst Mhh; rewrite (FR2 o) by (unfold two64; lia); rewrite FRh by (unfold two64; lia); reflexivity. }

  unfold havoc_r0, store_pubs. fold e15.
  assert (E3 : ev E' AUXV_ID = ev E AUXV_ID) by (destruct (reg_E' _ _ Hr3) as (X & _); exact X).
  pose proof PUBS' as (PV1 & PV2 & PV3 & PV4).
  pose proof (gp_auxcell _ _ _ _ _ _ _ _ _ GP) as AP.
  apply (region_store_known (s_priv st) E' M' (s_facts st) 0%uint63 _ GUARD 8%uint63 CANARY Hfs Hz);
    [| exact wok8 | apply (can_write_abs _ GUARD 8%uint63 wr_GUARD eq_refl P5) |].
  apply (region_store_known (s_priv st) E' M' (s_facts st) 0%uint63 _ GOT 8%uint63 _ Hfs Hz);
    [| exact wok8 | apply (can_write_abs _ GOT 8%uint63 wr_GOT eq_refl P4) |].
  apply (region_store_known (s_priv st) E' M' (s_facts st) 0%uint63 _ (PrimInt63.add LIBC 48%uint63) 8%uint63 _ Hfs Hz);
    [| exact wok8 | apply (can_write_abs _ (PrimInt63.add LIBC 48%uint63) 8%uint63 wr_PAGE_SIZE eq_refl P2) |].
  apply (region_store_known (s_priv st) E' M' (s_facts st) 0%uint63 _ (PrimInt63.add LIBC 8%uint63) 8%uint63 _ Hfs Hz);
    [| exact wok8 | apply (can_write_abs _ (PrimInt63.add LIBC 8%uint63) 8%uint63 wr_AUXV_CELL eq_refl P3) |].
  apply (region_store_known (s_priv st) E' M' (s_facts st) 0%uint63 _ (PrimInt63.add LIBC 3%uint63) 1%uint63 _ Hfs Hz);
    [exact RO2' | exact wok1 | apply (can_write_abs _ (PrimInt63.add LIBC 3%uint63) 1%uint63 wr_NEED_LOCKS eq_refl P1) |].
  all: intros i Hi; unfold addrZ; rewrite (ev0_zero E' Hz), Z.add_0_l.
  - change (keyZ (PrimInt63.add LIBC 3%uint63)) with RNEED_LOCKS. change (to_Z 1%uint63) with 1 in Hi.
    replace (RNEED_LOCKS + i) with (RNEED_LOCKS + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (rw_cell_rb M' RNEED_LOCKS (C1 (b8 0)) _ PV1) by (cbn; lia). replace (Z.to_nat i) with 0%nat by lia. cbn [cbytes nth_error].
    f_equal. unfold byte_of, b8. rewrite den_VL. f_equal. replace i with 0 by lia. reflexivity.
  - change (keyZ (PrimInt63.add LIBC 8%uint63)) with RAUXV_CELL. change (to_Z 8%uint63) with 8 in Hi.
    replace (RAUXV_CELL + i) with (RAUXV_CELL + Z.of_nat (Z.to_nat i)) by lia.
    assert (RBq : rb rsegs M' (RAUXV_CELL + Z.of_nat (Z.to_nat i)) = rb rsegs (ms_mem ms) (RAUXV_CELL + Z.of_nat (Z.to_nat i))).
    { unfold rb. unfold wa in AP. rewrite (AP (RAUXV_CELL + Z.of_nat (Z.to_nat i))) by lia. reflexivity. }
    rewrite RBq, (rw_cell_rb (ms_mem ms) RAUXV_CELL (C8 (ev E AUXV_ID)) _ AC) by (cbn [cbytes]; rewrite length_le8; lia). cbn [cbytes].
    rewrite byte_of_le8 by lia. rewrite den_VPz, E3. f_equal. f_equal. lia.
  - change (keyZ (PrimInt63.add LIBC 48%uint63)) with RPAGE_SIZE. change (to_Z 8%uint63) with 8 in Hi.
    replace (RPAGE_SIZE + i) with (RPAGE_SIZE + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (rw_cell_rb M' RPAGE_SIZE (C8 (wz 4096)) _ PV2) by (cbn [cbytes]; rewrite length_le8; lia). cbn [cbytes].
    rewrite byte_of_le8 by lia. rewrite den_VL. f_equal. replace (Z.of_nat (Z.to_nat i)) with i by lia. reflexivity.
  - change (keyZ GOT) with RGOT_SSP. change (to_Z 8%uint63) with 8 in Hi.
    replace (RGOT_SSP + i) with (RGOT_SSP + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (rw_cell_rb M' RGOT_SSP (C8 (wz RSSP_GUARD)) _ PV3) by (cbn [cbytes]; rewrite length_le8; lia). cbn [cbytes].
    rewrite byte_of_le8 by lia. rewrite den_VL. f_equal. replace (Z.of_nat (Z.to_nat i)) with i by lia. reflexivity.
  - change (keyZ GUARD) with RSSP_GUARD. change (to_Z 8%uint63) with 8 in Hi.
    replace (RSSP_GUARD + i) with (RSSP_GUARD + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (rw_cell_rb M' RSSP_GUARD (C8 (wz ssp_canary)) _ PV4) by (cbn [cbytes]; rewrite length_le8; lia). cbn [cbytes].
    rewrite byte_of_le8 by lia. rewrite (PB_canary E') by (unfold E'; rewrite eb_above; exact HPB).
    f_equal. replace (Z.of_nat (Z.to_nat i)) with i by lia. reflexivity.
Qed.

Definition Rg4 (r0 : Mem.region) : IMap.t Mem.region :=
  IMap.add 0%uint63 (havoc_r0 ERRNO LIBC GOT GUARD CANARY r0 e15) (IMap.add STACK_ID (forget_r1 r1 ksp) (s_regs st)).

Lemma Rg4_bst : forall r0, IMap.bst (Rg4 r0).
Proof. intros r0. unfold Rg4. apply IMap.bst_add, IMap.bst_add. exact (so_bst _ _ _ _ _ _ HS). Qed.

Lemma region_store_fields : forall q o w v,
  Mem.rg_lo (Mem.region_store q o w v) = Mem.rg_lo q /\ Mem.rg_hi (Mem.region_store q o w v) = Mem.rg_hi q
  /\ Mem.rg_w (Mem.region_store q o w v) = Mem.rg_w q /\ Mem.rg_bg (Mem.region_store q o w v) = Mem.rg_bg q.
Proof.
  intros q o w v. unfold Mem.region_store. destruct (Mem.in_granule o w).
  - apply region_store1_fields.
  - cbv zeta.
    match goal with |- context [Mem.rg_lo (Mem.region_store1 ?q2 ?o2 ?w2 ?v2)] =>
      destruct (region_store1_fields q2 o2 w2 v2) as (-> & -> & -> & ->) end.
    apply region_store1_fields.
Qed.

Lemma havoc_fields : forall r0, Mem.rg_lo (havoc_r0 ERRNO LIBC GOT GUARD CANARY r0 e15) = Mem.rg_lo r0
  /\ Mem.rg_hi (havoc_r0 ERRNO LIBC GOT GUARD CANARY r0 e15) = Mem.rg_hi r0
  /\ Mem.rg_w (havoc_r0 ERRNO LIBC GOT GUARD CANARY r0 e15) = Mem.rg_w r0.
Proof.
  intros r0. unfold havoc_r0, store_pubs.
  repeat match goal with |- context [Mem.rg_lo (Mem.region_store ?q ?o ?w ?v)] =>
    let F := fresh in pose proof (region_store_fields q o w v) as F; destruct F as (-> & -> & -> & _) end.
  cbn [dirty_r0 Mem.rg_lo Mem.rg_hi Mem.rg_w]. repeat split; reflexivity.
Qed.

Lemma Rg4_find : forall r0 k rg, IMap.find 0%uint63 (s_regs st) = Some r0 -> IMap.find k (Rg4 r0) = Some rg ->
  (k = 0%uint63 /\ rg = havoc_r0 ERRNO LIBC GOT GUARD CANARY r0 e15)
  \/ (k = STACK_ID /\ rg = forget_r1 r1 ksp)
  \/ (k <> 0%uint63 /\ k <> STACK_ID /\ IMap.find k (s_regs st) = Some rg).
Proof.
  intros r0 k rg Hr0 H. unfold Rg4 in H. pose proof (so_bst _ _ _ _ _ _ HS) as B.
  destruct (Uint63.eqb 0%uint63 k) eqn:K0.
  - apply Uint63.eqb_correct in K0. subst k. rewrite IMap.find_add_same in H by (apply IMap.bst_add; exact B). injection H as <-. left; auto.
  - apply Uint63.eqb_false_spec in K0. rewrite IMap.find_add_other in H by (try apply IMap.bst_add; assumption || exact B || auto).
    destruct (Uint63.eqb STACK_ID k) eqn:K1.
    + apply Uint63.eqb_correct in K1. subst k. rewrite IMap.find_add_same in H by exact B. injection H as <-. right; left; auto.
    + apply Uint63.eqb_false_spec in K1. rewrite IMap.find_add_other in H by (exact B || auto). right; right. repeat split; auto.
Qed.

Lemma win_lookup_In : forall l k len kd, win_lookup l k = Some (len, kd) -> In (k, len, kd) l.
Proof.
  intros l. induction l as [|[[k' len'] kd'] l IH]; intros k len kd H; cbn in H; [discriminate|].
  destruct (Uint63.eqb k' k) eqn:Q.
  - apply Uint63.eqb_correct in Q. subst k'. injection H as <- <-. left. reflexivity.
  - right. apply IH. exact H.
Qed.

Lemma nonstack_windows_In : forall E0 m ws l k len kd, nonstack_windows m ws = Some l -> In (k, len, kd) l ->
  k <> 0%uint63 /\ k <> STACK_ID /\ w2Z kd <> 0 /\
  In (Win (bv_unsigned (ev E0 k)) (bv_unsigned (den E0 len)) (w2Z kd)) (wins_of E0 m ws).
Proof.
  intros E0 m. induction m as [|m IH]; intros ws wl0 k len kd H Hin.
  - cbn in H. injection H as <-. destruct Hin.
  - destruct ws as [|wlo [|ln [|kdv ws']]]; try (cbn in H; discriminate).
    cbn [nonstack_windows] in H. destruct kdv as [kw| | | | | | | | | |]; try discriminate.
    destruct (nonstack_windows m ws') as [l|] eqn:NW; [|discriminate].
    rewrite wins_of_cons.
    destruct (weqb kw wzero) eqn:Z0.
    + injection H as <-. destruct (IH ws' l k len kd NW Hin) as (A1 & A2 & A3 & A4). repeat split; try assumption. right. exact A4.
    + destruct wlo as [|k0 o0| | | | | | | | |]; try discriminate.
      destruct (weqb o0 wzero && negb (PrimInt63.eqb k0 0) && negb (PrimInt63.eqb k0 STACK_ID)) eqn:C; [|discriminate].
      injection H as <-. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
      destruct Hin as [Hin|Hin].
      * injection Hin as -> -> ->. apply weqb_eq in C1. subst o0.
        split; [intros ->; discriminate C2|]. split; [intros ->; discriminate C3|].
        split. { intros X. assert (Q : weqb kd wzero = true) by (apply weqb_w2Z; rewrite X; reflexivity). rewrite Q in Z0. discriminate Z0. }
        left. rewrite den_VPz, unsigned_VL. reflexivity.
      * destruct (IH ws' l k len kd NW Hin) as (A1 & A2 & A3 & A4). repeat split; try assumption. right. exact A4.
Qed.

Lemma justified_client : forall k rg, IMap.find k (s_regs st) = Some rg -> k <> 0%uint63 -> k <> STACK_ID ->
  (forall len kd b, win_lookup wnl k = Some (len, kd) -> In b LB -> 0 < bv_unsigned (den E len) ->
      (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) ->
      exists blk, In blk LBg /\ (blk_addr blk, blk_size blk) = b) ->
  forall a, bv_unsigned (ev E k) + loZ rg <= a < bv_unsigned (ev E k) + hiZ E rg -> rclient_addr LBg sp a.
Proof.
  intros k rg Hk K0 K1 WB a Ha.
  pose proof (cg_just CG) as J. unfold regions_justified in J. cbv zeta in J.
  pose proof (proj1 (IMap.forallb_spec _ _ (so_bst _ _ _ _ _ _ HS)) J k rg Hk) as Jk.
  destruct (region_justified_inv E _ _ _ _ _ (so_facts _ _ _ _ _ _ HS) Jk K0 K1) as (L0 & JJ).
  assert (LZ : loZ rg = 0) by (unfold loZ; rewrite L0; reflexivity). rewrite LZ in Ha.
  destruct JJ as [SJ|(len & kd & WL & WJ)].
  - left. rewrite <- (cg_regs CG X2), reg_of_X2, SP_R in SJ. lia.
  - apply (known_leu_q_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in WJ. fold (hiZ E rg) in WJ.
    destruct (nonstack_windows_In E n rest wnl k len kd (cg_wnl CG) (win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
    pose proof (proj1 (Forall_forall _ _) (cg_wf CG) _ INW) as (W1 & W2 & W3 & [[KS _]|[[KB B]|[KS (b & Hb & SUB)]]]); cbn [w_kind w_lo w_len w_iv] in *.
    + exfalso. exact (KD KS).
    + destruct (WB len kd _ WL B ltac:(lia) ltac:(intros x Hx; exact Hx)) as (blk & Hblk & Eblk).
      right; right. exists blk. split; [exact Hblk|]. unfold blk_addr, blk_size in *.
      pose proof (f_equal fst Eblk) as E1. pose proof (f_equal snd Eblk) as E2. cbn [fst snd w_iv w_lo w_len] in E1, E2.
      rewrite E1, E2. lia.
    + destruct (WB len kd b WL Hb ltac:(lia) SUB) as (blk & Hblk & Eblk).
      right; right. exists blk. split; [exact Hblk|].
      assert (INK : in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a) by (unfold in_iv; cbn [fst snd]; lia).
      specialize (SUB a INK). unfold in_iv in SUB. rewrite <- Eblk in SUB.
      unfold blk_addr, blk_size in *. cbn [fst snd] in SUB. lia.
Qed.

Lemma Rg4_ranges : forall r0 k rg, IMap.find 0%uint63 (s_regs st) = Some r0 -> IMap.find k (Rg4 r0) = Some rg ->
  exists rg', IMap.find k (s_regs st) = Some rg' /\ loZ rg = loZ rg' /\ (forall E0, hiZ E0 rg = hiZ E0 rg') /\ Mem.rg_w rg = Mem.rg_w rg'.
Proof.
  intros r0 k rg Hr0 H. destruct (Rg4_find r0 k rg Hr0 H) as [[-> ->]|[[-> ->]|(_ & _ & F)]].
  - exists r0. destruct (havoc_fields r0) as (L & Hh & W). unfold loZ, hiZ. rewrite L, Hh, W. auto.
  - exists r1. pose proof (cg_r1 CG) as Hr1.
    destruct (region_forget_sound rsegs (s_priv st) E (ms_mem ms) STACK_ID r1 (Mem.granule (Mem.rg_lo r1)) (Mem.granule ksp)
                (so_reg _ _ _ _ _ _ HS _ _ Hr1)) as (_ & L & Hh & W & _).
    fold (forget_r1 r1 ksp) in L, Hh, W. unfold loZ, hiZ. rewrite L, Hh, W. auto.
  - exists rg. auto.
Qed.

Lemma Rg4_disjoint : forall r0, IMap.find 0%uint63 (s_regs st) = Some r0 -> regions_disjoint E' (Rg4 r0).
Proof.
  intros r0 Hr0 k1 q1 k2 q2 H1 H2 N K1 K2 W a.
  destruct (Rg4_ranges r0 k1 q1 Hr0 H1) as (q1' & F1 & L1 & M1 & W1).
  destruct (Rg4_ranges r0 k2 q2 Hr0 H2) as (q2' & F2 & L2 & M2 & W2).
  rewrite L1, (M1 E'), L2, (M2 E'). rewrite W1, W2 in W.
  exact (so_disj _ _ _ _ _ _ HS' k1 q1' k2 q2' F1 F2 N K1 K2 W a).
Qed.

Lemma Rg4_in_based : forall r0 a, IMap.find 0%uint63 (s_regs st) = Some r0 -> in_based E' (Rg4 r0) a -> in_based E' (s_regs st) a.
Proof.
  intros r0 a Hr0 (k & rg & H & K & R). destruct (Rg4_ranges r0 k rg Hr0 H) as (rg' & F & L & M & _).
  exists k, rg'. rewrite <- L, <- (M E'). auto.
Qed.

Lemma other_ops_hold : forall o, In o (s_ops st) -> not_id HEAP_ID o ->
  St.op_holds OPS (op_id o) (map (den E') (op_args o)) (ms_mem ms) mo -> St.op_holds OPS (op_id o) (map (den E') (op_args o)) M' mo'.
Proof.
  intros o Ho NI H. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
  apply (OPS_mo_other _ _ _ mo mo' NI (gp_va _ _ _ _ _ _ _ _ _ GP)).
  apply (OPS_frame_other _ _ (ms_mem ms) M' mo NI H).
  intros a Ha FP. destruct (OPS_fp_other _ _ a NI FP) as [R NS].
  destruct (client_byte a ltac:(unfold two64 in Ha; lia) ltac:(right; left; auto)) as (E1 & _). unfold wa in E1. symmetry. exact E1.
Qed.

Lemma MP' : MP mo'.
Proof. exact (MP_vm mo mo' (gp_va _ _ _ _ _ _ _ _ _ GP) HMP). Qed.

Lemma mfacts' : mfacts mo'.
Proof. destruct (gp_mo _ _ _ _ _ _ _ _ _ GP) as (H1 & H2 & _). split; assumption. Qed.

Lemma minv' : forall a b, M' a = Some b -> forall seg, find_segment rsegs (bv_unsigned a) 1 = Some seg -> seg_writable seg = true.
Proof.
  intros a b H seg Hs. pose proof (gp_minv _ _ _ _ _ _ _ _ _ GP a b H) as X. unfold ro_addr in X. rewrite Hs in X.
  destruct (seg_writable seg); [reflexivity| discriminate X].
Qed.

Theorem post_N : forall v hargs',
  (forall b, In b LBf -> In b LBg) ->
  den E' v = PropExec.getr R' 10%bv ->
  St.op_holds OPS HEAP_ID (map (den E') hargs') M' mo' ->
  (forall a, Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E') hargs')) ->
             Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E) hargs))) ->
  St.st_ok rsegs OPS E' (setr (set_ops st4 (set_op HEAP_ID hargs' (s_ops st4))) X10 v) ms' mo' /\ MP mo'.
Proof.
  intros v hargs' ALL Hv HH FP. split; [| exact MP'].
  destruct ST4 as (r0 & Hr0 & ->).
  pose proof HS' as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (REGS : forall k rg, IMap.find k (Rg4 r0) = Some rg -> St.region_ok rsegs (s_priv st) E' M' k rg).
  { intros k rg H. destruct (Rg4_find r0 k rg Hr0 H) as [[-> ->]|[[-> ->]|(K0 & K1 & F)]].
    - apply r0_ok. exact Hr0.
    - apply r1_ok.
    - apply (old_region_ok k rg F); [apply Uint63.eqb_false_spec; exact K0|].
      apply (justified_client k rg F K0 K1). intros len kd b WL Hb SUB.
      assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
      apply in_map_iff in Hb' as (blk & Eb & Hblk). exists blk. split; [apply ALL; exact Hblk| exact Eb]. }
  unfold setr, set_ops, alloc_post_mk. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]. fold e15. fold (Rg4 r0).
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
  - reflexivity.
  - rewrite rf_get_set_other by discriminate. change (rf_get (s_rf (clobber st)) X0) with (getr (clobber st) X0). rewrite getr_clobber. cbn [clob_pos]. exact Px0.
  - apply post_regs. exact Hv.
  - exact Pfregs.
  - reflexivity.
  - pose proof (cg_ms CG) as MSE. pose proof Presv as X. unfold resv_ok in X |- *. destruct (s_resv st); [reflexivity| |exact I].
    exfalso. rewrite MSE in X. cbn in X. discriminate X.
  - exact Pfcsr.
  - reflexivity.
  - rewrite ev_E'_below; [exact (so_zero _ _ _ _ _ _ HS)|]. destruct NX as (_ & P & _). change (to_Z 0%uint63) with 0. lia.
  - apply Rg4_bst.
  - exact REGS.
  - apply Rg4_disjoint. exact Hr0.
  - eapply pub_of_regions. exact REGS.
  - exact Pfacts.
  - eapply (ops_hold_set_op OPS E' E' (s_ops st) HEAP_ID hargs hargs' (ms_mem ms) M' mo mo' (cg_find CG) (cg_count CG) Pops).
    + exact other_ops_hold.
    + exact HH.
  - eapply (ops_apart_set_op rsegs OPS E' E' (s_ops st) HEAP_ID hargs hargs' (s_regs st) (Rg4 r0) (s_priv st) (cg_find CG) (cg_count CG) Papart).
    + intros o a Ho NI IMP X. destruct (IMP X) as [NB PR]. split; [| exact PR]. intros IB. apply NB. eapply Rg4_in_based; eauto.
    + intros a X. assert (X' : Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E') hargs))).
      { rewrite (map_ext_in (den E') (den E) hargs) ; [apply FP; exact X|]. intros u Hu. apply den_E'.
        destruct SVB_parts as (_ & _ & _ & _ & _ & OV). exact (forallb_In _ _ _ u (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) Hu). }
      destruct (ops_apart_find rsegs OPS E' (s_ops st) (s_regs st) (s_priv st) HEAP_ID hargs a Papart (cg_find CG) X') as [NB PR].
      split; [| exact PR]. intros IB. apply NB. eapply Rg4_in_based; eauto.
  - apply (St.plain_minv _ _ OPS_plain). apply mfacts'.
  - intros xa _. apply St.plain_cover. exact OPS_plain.
  - exact minv'.
Qed.

Definition k16 : int := PrimInt63.add (s_next st) 16%uint63.
Lemma k16_addn : k16 = addn (s_next st) 16.
Proof.
  destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  unfold k16. symmetry. apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma ev_k16 : ev E' k16 = Fv 16.
Proof. rewrite k16_addn, ev_E'_fresh by lia. reflexivity. Qed.
Lemma k16_Z : to_Z k16 = to_Z (s_next st) + 16.
Proof.
  destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  rewrite k16_addn, addn_Z; [lia| rewrite wB_two63, two63_eq; lia].
Qed.

Definition blk_region (nsv : sv) : Mem.region := Mem.Region 0%uint63 nsv true Mem.BGUnk IMap.empty.

Lemma block_post_shape : forall (S : sstate) (k nx : int) (RG : Mem.region) (hargs' : list sv) (f1 f2 f3 : fact) (v : sv),
  setr (addfact (addfact (addfact
         (set_ops (setregs (set_next S nx) (IMap.add k RG (s_regs (set_next S nx))))
                  (set_op HEAP_ID hargs' (s_ops (setregs (set_next S nx) (IMap.add k RG (s_regs (set_next S nx)))))))
         f1) f2) f3) X10 v
  = SS (s_pc S) (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (IMap.add k RG (s_regs S))
       (f3 :: f2 :: f1 :: s_facts S) (set_op HEAP_ID hargs' (s_ops S)) (s_priv S) nx.
Proof. intros. destruct S. reflexivity. Qed.

Lemma block_post_inv : forall r0 hargsB nsv rg stB,
  IMap.find 0%uint63 (s_regs st) = Some r0 -> st4 = alloc_post_mk ERRNO LIBC GOT GUARD CANARY st r ksp r0 r1 ->
  block_post st4 hargsB nsv rg = Some stB ->
  exists hargs', heap_add_window hargsB (VP k16 wzero) nsv (VL CtrLib.K_BLOCK) = Some hargs' /\
    stB = SS r (rf_set (s_rf (clobber st)) X10 (VP k16 wzero)) (s_ff st) (s_resv st)
             (IMap.add k16 (blk_region nsv) (Rg4 r0))
             (FULt nsv (VL two47) :: FAlign k16 4%uint63 :: FRange k16 (fst rg) (snd rg) :: s_facts st)
             (set_op HEAP_ID hargs' (s_ops st)) (s_priv st) (PrimInt63.add k16 1%uint63).
Proof.
  intros r0 hargsB nsv rg stB Hr0 E4 H. unfold block_post, fresh in H. rewrite E4 in H.
  cbn [fst snd s_next alloc_post_mk] in H. fold k16 in H.
  destruct (heap_add_window hargsB (VP k16 wzero) nsv (VL CtrLib.K_BLOCK)) as [hargs'|] eqn:AW; [|discriminate].
  apply Some_inj in H. exists hargs'. split; [reflexivity|]. subst stB.
  rewrite block_post_shape. unfold alloc_post_mk. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]. fold e15. reflexivity.
Qed.

Lemma blk_region_ok : forall nsv Ablk nZ junk,
  sv_vars_below (s_next st) nsv = true -> nZ = bv_unsigned (den E nsv) ->
  Fv 16 = Z_to_bv 64 Ablk -> (forall o, 0 <= o < nZ -> nth_error junk (Z.to_nat o) = Some (Gv 16 o)) ->
  rw_cells rsegs M' Ablk [CB (Z.to_nat nZ) junk] ->
  0 <= Ablk -> Ablk + nZ <= alloc_ceiling -> (Ablk + nZ <= RIMG_LO \/ RIMG_HI <= Ablk) ->
  St.region_ok rsegs (s_priv st) E' M' k16 (blk_region nsv).
Proof.
  intros nsv Ablk nZ junk SV EN F16 GJ RW A0 AC AI.
  pose proof alloc_ceiling_lt64 as C64. pose proof (bv_unsigned_in_range 64 (den E nsv)) as RN. unfold bv_modulus in RN.
  assert (EK : bv_unsigned (ev E' k16) = Ablk).
  { rewrite ev_k16, F16, Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. unfold W64.two64. lia. }
  assert (EH : hiZ E' (blk_region nsv) = nZ). { unfold hiZ, blk_region. cbn [Mem.rg_hi]. rewrite (den_E' nsv SV). symmetry. exact EN. }
  assert (EL : loZ (blk_region nsv) = 0) by reflexivity.
  assert (K0 : PrimInt63.eqb k16 0%uint63 = false).
  { apply Uint63.eqb_false_spec. intros X. pose proof k16_Z as KZ. rewrite X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NX as (_ & P & _). lia. }
  destruct RW as [[CW BA] WR]. cbn [cells_bytes cells_size] in BA, WR. rewrite app_nil_r in BA. rewrite Nat.add_0_r in WR.
  destruct BA as (_ & BL & BY). cbn [Cells.cells_wf Cells.cell_wf] in CW. destruct CW as [LJ _]. cbn [cbytes] in BL, BY. rewrite LJ in BL, BY.
  constructor; rewrite ?EK, ?EH, ?EL.
  - apply IMap.bst_empty || constructor.
  - intros _. unfold two64. lia.
  - intros _ a Ha. split; [| split].
    + rewrite rb_mrd. replace a with (Ablk + Z.of_nat (Z.to_nat (a - Ablk))) by lia. rewrite BY by lia. cbn [cbytes].
      destruct (nth_error junk (Z.to_nat (a - Ablk))) eqn:X; [congruence|]. apply nth_error_None in X. lia.
    + intros _. apply (proj2 (wb_wview _ _)). destruct WR as (_ & _ & W). replace a with (Ablk + (a - Ablk)) by lia. apply W.
      cbn [csize] in *. lia.
    + apply ref_find_segment_none; [lia|]. unfold RIMG_LO, RIMG_HI in AI. lia.
  - intros g gr Hg. cbn [blk_region Mem.rg_cells] in Hg. rewrite IMap.find_empty in Hg || cbn in Hg. discriminate Hg.
  - intros g gr c i Hg. cbn [blk_region Mem.rg_cells] in Hg. cbn in Hg. discriminate Hg.
  - intros o H1 _ _. specialize (H1 K0). unfold bg_byte. cbn [blk_region Mem.rg_bg]. unfold E'. rewrite eg_above by (rewrite k16_Z; lia).
    rewrite k16_Z. replace (to_Z (s_next st) + 16 - to_Z (s_next st)) with 16 by lia.
    rewrite rb_mrd. replace (Ablk + o) with (Ablk + Z.of_nat (Z.to_nat o)) by lia. rewrite BY by lia. rewrite GJ by lia. reflexivity.
Qed.

Lemma windows_wf_mono : forall ws L1 L2 c, windows_wf ws L1 c -> (forall b, In b L1 -> In b L2) -> windows_wf ws L2 c.
Proof.
  intros ws L1 L2 c WF SUB. apply Forall_forall. intros w Hw.
  pose proof (proj1 (Forall_forall _ _) WF w Hw) as (W1 & W2 & W3 & [[K S]|[[K B]|[K (b & Hb & SB)]]]).
  - split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. left; auto.
  - split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. right; left; auto.
  - split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. right; right. split; [exact K|]. exists b. auto.
Qed.

Lemma wins_of_E' : forall m l, forallb (sv_vars_below (s_next st)) l = true -> wins_of E' m l = wins_of E m l.
Proof.
  induction m as [|m IH]; intros l AV; [reflexivity|]. destruct l as [|x [|y [|z l']]]; try reflexivity. cbn [forallb] in AV.
  apply andb_prop in AV as [A1 AV]. apply andb_prop in AV as [A2 AV]. apply andb_prop in AV as [A3 AV].
  rewrite !wins_of_cons, (IH l' AV), !den_E' by assumption. reflexivity.
Qed.

Theorem post_B : forall hargsB a' nsv rlo rhi stB Ablk nZ junk,
  hargsB = VL md :: a' :: VL nw :: rest ->
  block_post st4 hargsB nsv (rlo, rhi) = Some stB ->
  sv_vars_below (s_next st) nsv = true -> sv_vars_below (s_next st) a' = true -> nZ = bv_unsigned (den E nsv) ->
  Fv 16 = Z_to_bv 64 Ablk -> (forall o, 0 <= o < nZ -> nth_error junk (Z.to_nat o) = Some (Gv 16 o)) ->
  rw_cells rsegs M' Ablk [CB (Z.to_nat nZ) junk] ->
  4096 <= Ablk -> Ablk + nZ <= alloc_ceiling -> Ablk mod 16 = 0 -> (Ablk + nZ <= RIMG_LO \/ RIMG_HI <= Ablk) ->
  w2Z rlo <= Ablk <= w2Z rhi ->
  (forall b a, In b LB -> in_iv b a -> ~ (Ablk <= a < Ablk + nZ)) ->
  (forall b, In b LBf -> In b LBg) ->
  aw_holdsI (den E a') ((Ablk, nZ) :: LB) M' mo' ->
  PropExec.getr R' 10%bv = Z_to_bv 64 Ablk ->
  St.st_ok rsegs OPS E' stB ms' mo' /\ MP mo'.
Proof.
  intros hargsB a' nsv rlo rhi stB Ablk nZ junk EhB HB SVn SVa EN F16 GJ RW A4096 AC A16 AI FR NEW ALL AWH Ha0.
  split; [| exact MP'].
  destruct ST4 as (r0 & Hr0 & E4).
  destruct (block_post_inv r0 hargsB nsv (rlo, rhi) stB Hr0 E4 HB) as (hargs' & AW & ->). cbn [fst snd].
  pose proof HS' as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  pose proof (cg_nwin CG) as NW. pose proof (cg_nw CG) as (T & N & L). pose proof (cg_hargs CG) as EH.
  pose proof alloc_ceiling_lt64 as C64. pose proof (bv_unsigned_in_range 64 (den E nsv)) as RN. unfold bv_modulus in RN.
  subst hargsB. assert (NW' : heap_nwin (VL md :: a' :: VL nw :: rest) = Some n) by (rewrite EH in NW; exact NW).
  rewrite (heap_add_window_eq md a' nw rest n _ nsv _ NW') in AW. apply Some_inj in AW. subst hargs'.
  assert (EK : bv_unsigned (ev E' k16) = Ablk).
  { rewrite ev_k16, F16, Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. unfold W64.two64. lia. }
  assert (DK : den E' (VP k16 wzero) = Z_to_bv 64 Ablk) by (rewrite den_VPz, ev_k16; exact F16).
  assert (EH' : hiZ E' (blk_region nsv) = nZ). { unfold hiZ, blk_region. cbn [Mem.rg_hi]. rewrite (den_E' nsv SVn). symmetry. exact EN. }
  assert (EL0 : loZ (blk_region nsv) = 0) by reflexivity.
  assert (K0 : PrimInt63.eqb k16 0%uint63 = false).
  { apply Uint63.eqb_false_spec. intros X. pose proof k16_Z as KZ. rewrite X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NX as (_ & P & _). lia. }
  assert (KF : forall k rg, IMap.find k (s_regs st) = Some rg -> k <> k16).
  { intros k rg Hk ->. destruct (reg_E' _ _ Hk) as (_ & _ & LT & _). apply Uint63.ltb_spec in LT. rewrite k16_Z in LT. lia. }
  assert (KF4 : IMap.find k16 (Rg4 r0) = None).
  { destruct (IMap.find k16 (Rg4 r0)) as [rg|] eqn:X; [|reflexivity]. exfalso.
    destruct (Rg4_ranges r0 k16 rg Hr0 X) as (rg' & F & _). exact (KF _ _ F eq_refl). }

  assert (NB : to_Z (wl nw) + 1 < two63).
  { pose proof (cg_n255 CG) as N255. pose proof (int_range (wl nw)) as R. unfold two63. rewrite N in N255. lia. }
  assert (DEC' : decode (map (den E') (VL md :: a' :: VL (wadd nw wone) :: firstn (3 * n) rest ++ [VP k16 wzero; nsv; VL CtrLib.K_BLOCK] ++ skipn (3 * n) rest))
                 = Some (w2Z md, den E' a', wins_of E n rest ++ [Win Ablk nZ K_BLOCK], map (den E) (skipn (3 * n) rest))).
  { rewrite (decode_add_window E' md a' nw rest n _ nsv _ T N L NB).
    rewrite DK, Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64; lia).
    rewrite (den_E' nsv SVn), <- EN, unsigned_VL. change (w2Z CtrLib.K_BLOCK) with K_BLOCK.
    destruct SVB_parts as (_ & _ & _ & _ & _ & OV).
    pose proof (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) as AV. rewrite EH in AV. cbn [op_args forallb] in AV.
    apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV].
    assert (CE : map (den E') (skipn (3 * n) rest) = map (den E) (skipn (3 * n) rest)).
    { apply map_ext_in. intros u Hu. apply den_E'. apply (forallb_In _ _ _ u AV). rewrite <- (firstn_skipn (3 * n) rest). apply in_app_iff. right. exact Hu. }
    rewrite (wins_of_E' n rest AV), CE. reflexivity. }
  assert (MAPH : map (den E') hargs = map (den E) hargs).
  { apply map_ext_in. intros u Hu. apply den_E'. destruct SVB_parts as (_ & _ & _ & _ & _ & OV).
    exact (forallb_In _ _ _ u (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) Hu). }

  assert (NEWR : forall a k rg, Ablk <= a < Ablk + nZ -> IMap.find k (Rg4 r0) = Some rg -> PrimInt63.eqb k 0%uint63 = false ->
            ~ (bv_unsigned (ev E' k) + loZ rg <= a < bv_unsigned (ev E' k) + hiZ E' rg)).
  { intros a k rg Ha Hk K R. destruct (Rg4_ranges r0 k rg Hr0 Hk) as (rg' & F & L' & Mq & _). rewrite L', (Mq E') in R.
    destruct (reg_E' _ _ F) as (Ek & Eh & _). rewrite Ek, Eh in R.
    destruct (Uint63.eqb k STACK_ID) eqn:K1.
    - apply Uint63.eqb_correct in K1. subst k. rewrite (cg_r1 CG) in F. injection F as <-.
      pose proof (cg_ceil CG) as CE. unfold lo, base in *. lia.
    - apply Uint63.eqb_false_spec in K1. apply Uint63.eqb_false_spec in K.
      assert (CL : rclient_addr LBg sp a).
      { apply (justified_client k rg' F K K1); [| exact R]. intros len kd b WL Hb SUB.
        assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
        apply in_map_iff in Hb' as (blk & Eb & Hblk). exists blk. split; [apply ALL; exact Hblk| exact Eb]. }
      destruct CL as [S1|[[I1 I2]|(blk & Hblk & Rb)]].
      + pose proof (cg_ceil CG) as CE. pose proof (cg_room CG) as RM. pose proof (int_range need). unfold sp, lo, base in *. lia.
      + unfold RIMG_LO, RIMG_HI in AI. lia.
      + apply HLBg in Hblk. apply (NEW (blk_addr blk, blk_size blk) a); [| unfold in_iv; cbn [fst snd]; lia| lia].
        eapply Permutation_in; [exact (cg_perm CG)|]. apply in_map_iff. exists blk. auto. }
  set (R5 := IMap.add k16 (blk_region nsv) (Rg4 r0)).
  pose proof (Rg4_bst r0) as B4.
  assert (F5 : forall k rg, IMap.find k R5 = Some rg -> (k = k16 /\ rg = blk_region nsv) \/ (k <> k16 /\ IMap.find k (Rg4 r0) = Some rg)).
  { intros k rg H. subst R5. destruct (Uint63.eqb k16 k) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_add_same in H by exact B4. injection H as <-. left; auto.
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other in H by (exact B4 || exact Q). right. split; [congruence| exact H]. }
  assert (REGS : forall k rg, IMap.find k R5 = Some rg -> St.region_ok rsegs (s_priv st) E' M' k rg).
  { intros k rg H. destruct (F5 k rg H) as [[-> ->]|[NK H4']].
    - apply (blk_region_ok nsv Ablk nZ junk); try assumption. lia.
    - destruct (Rg4_find r0 k rg Hr0 H4') as [[-> ->]|[[-> ->]|(K0' & K1 & F)]].
      + apply r0_ok. exact Hr0.
      + apply r1_ok.
      + apply (old_region_ok k rg F); [apply Uint63.eqb_false_spec; exact K0'|].
        apply (justified_client k rg F K0' K1). intros len kd b WL Hb SUB.
        assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
        apply in_map_iff in Hb' as (blk & Eb & Hblk). exists blk. split; [apply ALL; exact Hblk| exact Eb]. }
  assert (NEWB : forall a, in_based E' R5 a -> (Ablk <= a < Ablk + nZ) \/ in_based E' (s_regs st) a).
  { intros a (k & rg & H & K & R). destruct (F5 k rg H) as [[-> ->]|[NK H4']].
    - left. rewrite EK, EH', EL0 in R. lia.
    - right. apply (Rg4_in_based r0 a Hr0). exists k, rg. auto. }

  assert (HH : St.op_holds OPS HEAP_ID (map (den E') (VL md :: a' :: VL (wadd nw wone) :: firstn (3 * n) rest ++ [VP k16 wzero; nsv; VL CtrLib.K_BLOCK] ++ skipn (3 * n) rest)) M' mo').
  { rewrite OPS_holds1. exists (w2Z md), (den E' a'), (wins_of E n rest ++ [Win Ablk nZ K_BLOCK]), (map (den E) (skipn (3 * n) rest)), ((Ablk, nZ) :: LB).
    split; [exact DEC'|]. split; [apply aw_holdsW_intro; [rewrite (den_E' a' SVa); exact AWH| apply NG_app_block; exact (cg_ng CG)]|]. split.
    - apply Forall_app. split.
      + apply (windows_wf_mono _ LB). { exact (cg_wf CG). } intros b Hb. right. exact Hb.
      + constructor; [| constructor]. split; [cbn [w_lo]; lia|]. split; [cbn [w_len]; lia|]. split; [cbn [w_lo w_len]; unfold two64; lia|].
        right; left. split; [reflexivity|]. left. reflexivity.
    - apply (cw_grow Cw). 2:{ intros a Ha U. unfold in_user in U. apply in_ivs_In in U as (b & Hb & Hin). exact (NEW b a Hb Hin Ha). }
      apply (cw_frame Cw _ _ _ _ (ms_mem ms) M' (cg_cw CG)). intros a Ha U _.
      unfold in_user in U. apply in_ivs_In in U as (b & Hb & Hin).
      assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
      apply in_map_iff in Hb' as (blk & Eb & Hblk).
      destruct (client_byte a ltac:(unfold two64 in Ha; lia)) as (E1 & _); [| unfold wa in E1; symmetry; exact E1].
      right; right. exists blk. split; [apply ALL; exact Hblk|]. unfold in_iv in Hin. rewrite <- Eb in Hin. cbn [fst snd] in Hin. exact Hin. }
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
  - reflexivity.
  - rewrite rf_get_set_other by discriminate. change (rf_get (s_rf (clobber st)) X0) with (getr (clobber st) X0). rewrite getr_clobber. cbn [clob_pos]. exact Px0.
  - apply post_regs. rewrite DK. symmetry. exact Ha0.
  - exact Pfregs.
  - reflexivity.
  - pose proof (cg_ms CG) as MSE. pose proof Presv as X. unfold resv_ok in X |- *. destruct (s_resv st); [reflexivity| |exact I].
    exfalso. rewrite MSE in X. cbn in X. discriminate X.
  - exact Pfcsr.
  - reflexivity.
  - rewrite ev_E'_below; [exact (so_zero _ _ _ _ _ _ HS)|]. destruct NX as (_ & P & _). change (to_Z 0%uint63) with 0. lia.
  - subst R5. apply IMap.bst_add. exact B4.
  - exact REGS.
  - intros k1 q1 k2 q2 H1 H2 NE K1 K2 W a [X1 X2].
    destruct (F5 k1 q1 H1) as [[-> ->]|[N1 G1]]; destruct (F5 k2 q2 H2) as [[-> ->]|[N2 G2]].
    + exact (NE eq_refl).
    + rewrite EK, EH', EL0 in X1. exact (NEWR a k2 q2 ltac:(lia) G2 K2 X2).
    + rewrite EK, EH', EL0 in X2. exact (NEWR a k1 q1 ltac:(lia) G1 K1 X1).
    + exact (Rg4_disjoint r0 Hr0 k1 q1 k2 q2 G1 G2 NE K1 K2 W a (conj X1 X2)).
  - eapply pub_of_regions. exact REGS.
  - constructor; [| constructor; [| constructor; [| exact Pfacts]]].
    + cbn [fact_holds]. rewrite (den_E' nsv SVn), <- EN, unsigned_VL. change (w2Z two47) with (2 ^ 47).
      pose_ceil. unfold CEIL_MIN, CEIL_MAX in *. lia.
    + cbn [fact_holds]. rewrite EK. change (2 ^ to_Z 4%uint63) with 16. exact A16.
    + cbn [fact_holds]. rewrite EK. exact FR.
  - eapply (ops_hold_set_op OPS E' E' (s_ops st) HEAP_ID hargs _ (ms_mem ms) M' mo mo' (cg_find CG) (cg_count CG) Pops).
    + exact other_ops_hold.
    + exact HH.
  - eapply (ops_apart_set_op rsegs OPS E' E' (s_ops st) HEAP_ID hargs _ (s_regs st) R5 (s_priv st) (cg_find CG) (cg_count CG) Papart).
    + intros o a Ho NI IMP X. destruct (IMP X) as [NB' PR]. split; [| exact PR]. intros IB.
      destruct (NEWB a IB) as [BL|OLD]; [| exact (NB' OLD)].
      unfold not_id in NI. apply Uint63.eqb_false_spec in NI. destruct (OPS_fp_other _ _ a NI X) as [RNG _]. unfold RIMG_LO, RIMG_HI in AI. lia.
    + intros a X. rewrite OPS_fp1 in X. apply (proj1 (fp_spec IMGX _ _ _ _ _ a DEC')) in X as (Ra & NI & NWS).
      assert (X' : Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E') hargs))).
      { rewrite OPS_fp1, MAPH. apply (proj2 (fp_spec IMGX _ _ _ _ _ a (cg_decode CG))). split; [exact Ra|]. split; [exact NI|].
        intros W. apply NWS. unfold in_ws in *. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). left. exact W. }
      destruct (ops_apart_find rsegs OPS E' (s_ops st) (s_regs st) (s_priv st) HEAP_ID hargs a Papart (cg_find CG) X') as [NB' PR].
      split; [| exact PR]. intros IB. destruct (NEWB a IB) as [BL|OLD]; [| exact (NB' OLD)].
      apply NWS. unfold in_ws. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). right. cbn [map].
      apply (proj2 (in_ivs_cons _ _ _)). left. unfold in_iv, w_iv. cbn [fst snd w_lo w_len]. exact BL.
  - apply (St.plain_minv _ _ OPS_plain). apply mfacts'.
  - intros xa _. apply St.plain_cover. exact OPS_plain.
  - exact minv'.
Qed.

Lemma blk_by_id : forall (l : list block) b1 b2, List.NoDup (map blk_id l) -> In b1 l -> In b2 l -> blk_id b1 = blk_id b2 -> b1 = b2.
Proof.
  intros l. induction l as [|x l IH]; intros b1 b2 ND I1 I2 E12; [destruct I1|].
  cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
  destruct I1 as [<-|I1]; destruct I2 as [<-|I2].
  - reflexivity.
  - exfalso. apply NI. rewrite E12. apply in_map. exact I2.
  - exfalso. apply NI. rewrite <- E12. apply in_map. exact I1.
  - exact (IH b1 b2 ND I1 I2 E12).
Qed.

Theorem post_F : forall r0 kf rf lenf p Af nf a' hargs' l1 l2 stF,
  IMap.find 0%uint63 (s_regs st) = Some r0 -> st4 = alloc_post_mk ERRNO LIBC GOT GUARD CANARY st r ksp r0 r1 ->
  IMap.find kf (s_regs st) = Some rf -> kf <> 0%uint63 -> kf <> STACK_ID ->
  free_ok st wnl kf = Some lenf ->
  In (p, Af, nf) LBf -> Af = bv_unsigned (ev E kf) -> nf = bv_unsigned (den E lenf) ->
  (forall b, In b LBf -> blk_id b <> p -> In b LBg) -> (forall b, In b LBg -> blk_id b <> p) ->
  wins_of E n rest = l1 ++ Win Af nf K_BLOCK :: l2 ->
  (forall w, In w (l1 ++ l2) -> w_kind w = K_STACK \/ exists k len kd, In (k, len, kd) wnl /\ k <> kf /\
                                  w = Win (bv_unsigned (ev E k)) (bv_unsigned (den E len)) (w2Z kd)) ->
  decode (map (den E') hargs') = Some (w2Z md, den E' a', l1 ++ l2, map (den E) (skipn (3 * n) rest)) ->
  sv_vars_below (s_next st) a' = true ->
  aw_holdsI (den E a') (remove iv_eq_dec (Af, nf) LB) M' mo' ->
  Fv 16 = PropExec.getr R' 10%bv ->
  stF = SS r (rf_set (s_rf (clobber st)) X10 (VP k16 wzero)) (s_ff st) (s_resv st) (IMap.remove kf (Rg4 r0)) (s_facts st)
           (set_op HEAP_ID hargs' (s_ops st)) (s_priv st) (PrimInt63.add k16 1%uint63) ->
  St.st_ok rsegs OPS E' stF ms' mo' /\ MP mo'.
Proof.
  intros r0 kf rf lenf p Af nf a' hargs' l1 l2 stF Hr0 E4 Hkf K0 K1 FOK INf EAf Enf LBG LBGid WS PROV DEC' SVa AWH F16 ->.
  split; [| exact MP'].
  pose proof HS' as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  pose proof (Rg4_bst r0) as B4. pose proof alloc_ceiling_lt64 as C64.
  pose proof (cg_rheap CG) as RH. apply RHEAP_split in RH as [RC _].
  pose proof (RHEAP_core_nodup s LBf (ms_mem ms) RC) as NDid.
  destruct (free_ok_inv st wnl kf lenf FOK) as (rf' & Hrf' & WLf & LOf & NEf & LEf & OTH). rewrite Hkf in Hrf'. injection Hrf' as <-.
  apply (known_ltu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in NEf. rewrite unsigned_VL in NEf. change (w2Z wzero) with 0 in NEf. fold (hiZ E rf) in NEf.
  apply (known_leu_q_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in LEf. fold (hiZ E rf) in LEf. rewrite <- Enf in LEf.
  assert (LZf : loZ rf = 0) by (unfold loZ; rewrite LOf; reflexivity).

  destruct (RHEAP_core_block_range s LBf (ms_mem ms) _ RC INf) as (Bf1 & Bf2 & Bf3 & Bf4 & _). cbn [blk_addr blk_size fst snd] in Bf1, Bf2, Bf3, Bf4.

  assert (FREED : forall k2 len2 kd2, In (k2, len2, kd2) wnl -> k2 <> kf ->
            (0 < bv_unsigned (den E len2)
             \/ (bv_unsigned (den E len2) = 0 /\ exists k3 len3, In (k3, len3, CtrLib.K_BLOCK) wnl /\ k3 <> kf)) /\
            forall a, bv_unsigned (ev E k2) <= a < bv_unsigned (ev E k2) + bv_unsigned (den E len2) -> ~ (Af <= a < Af + nf)).
  { intros k2 len2 kd2 I2 NK.
    destruct (OTH k2 len2 kd2 I2 NK) as (rg2 & Hk2 & LO2 & NE2' & LE2 & WW & FULL).
    apply (known_leu_q_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in LE2. fold (hiZ E rg2) in LE2.
    pose proof (bv_unsigned_in_range 64 (den E (Mem.rg_hi rg2))) as HR2. rewrite bv_modulus_64 in HR2. fold (hiZ E rg2) in HR2.
    assert (NE2 : 0 < hiZ E rg2 \/ (bv_unsigned (den E len2) = 0 /\ exists k3 len3, In (k3, len3, CtrLib.K_BLOCK) wnl /\ k3 <> kf)).
    { destruct NE2' as [NE2|(KNB & HEQ & OB)].
      - left. apply (known_ltu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in NE2. rewrite unsigned_VL in NE2. change (w2Z wzero) with 0 in NE2. fold (hiZ E rg2) in NE2. exact NE2.
      - destruct (Z_lt_le_dec 0 (hiZ E rg2)) as [POS2|Z2]; [left; exact POS2| right]. split; [| exact OB].
        apply (known_eq_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in HEQ. apply (f_equal bv_unsigned) in HEQ. fold (hiZ E rg2) in HEQ. lia. }
    assert (LZ2 : loZ rg2 = 0) by (unfold loZ; rewrite LO2; reflexivity).
    destruct (nonstack_windows_In E n rest wnl k2 len2 kd2 (cg_wnl CG) I2) as (K20 & K21 & KD2 & INW2).
    split; [destruct NE2 as [NE2|NE2]; [left; lia| right; exact NE2]|]. intros a Ha INA.
    destruct NE2 as [NE2|[Z2 _]]; [| lia].

    assert (DISJ := so_disj _ _ _ _ _ _ HS kf rf k2 rg2 Hkf Hk2 ltac:(congruence) ltac:(apply Uint63.eqb_false_spec; exact K0) ltac:(apply Uint63.eqb_false_spec; exact K20)
                     ltac:(destruct WW; [left|right]; assumption)).
    rewrite LZf, LZ2, <- EAf in DISJ.
    pose proof (proj1 (Forall_forall _ _) (cg_wf CG) _ INW2) as (_ & _ & _ & [[KS _]|[[KB B2]|[KS (b & Hb & SUB)]]]); cbn [w_kind w_lo w_len w_iv] in *.
    - exact (KD2 KS).
    -
      assert (B2' : In (bv_unsigned (ev E k2), bv_unsigned (den E len2)) (blocks_of LBf))
        by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact B2]).
      apply in_map_iff in B2' as (blk2 & Eb2 & Hblk2).
      destruct (bptr_eqb (blk_id blk2) p) eqn:BP.
      + apply bptr_eqb_true in BP. pose proof (blk_by_id LBf blk2 (p, Af, nf) NDid Hblk2 INf BP) as ->.
        cbn [blk_addr blk_size fst snd] in Eb2. injection Eb2 as EA2 EN2.
        apply (DISJ Af). rewrite <- EA2. lia.
      + assert (NEb : blk_id (p, Af, nf) <> blk_id blk2).
        { cbn [blk_id fst]. intros X. rewrite <- X in BP. rewrite (proj2 (bptr_eqb_true p p) eq_refl) in BP. discriminate BP. }
        pose proof (f_equal fst Eb2) as E1. pose proof (f_equal snd Eb2) as E2. unfold blk_addr, blk_size in E1, E2. cbn [fst snd] in E1, E2.
        destruct (RHEAP_core_blocks_disjoint s LBf (ms_mem ms) (p, Af, nf) blk2 RC INf Hblk2 NEb) as [D|D];
          unfold blk_addr, blk_size in D; cbn [fst snd] in D; lia.
    -
      assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
      apply in_map_iff in Hb' as (blk2 & Eb2 & Hblk2).
      destruct (bptr_eqb (blk_id blk2) p) eqn:BP.
      + apply bptr_eqb_true in BP. pose proof (blk_by_id LBf blk2 (p, Af, nf) NDid Hblk2 INf BP) as ->.
        cbn [blk_addr blk_size fst snd] in Eb2. subst b.
        destruct FULL as [KDB|FU]; [rewrite KDB in KS; unfold K_SUB in KS; change (w2Z CtrLib.K_BLOCK) with 1 in KS; lia|].
        apply (known_eq_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in FU. apply (f_equal bv_unsigned) in FU. fold (hiZ E rf) in FU. rewrite <- Enf in FU.
        assert (INK : in_iv (bv_unsigned (ev E k2), bv_unsigned (den E len2)) (bv_unsigned (ev E k2))) by (unfold in_iv; cbn [fst snd]; lia).
        specialize (SUB (bv_unsigned (ev E k2)) INK). unfold in_iv in SUB. cbn [fst snd] in SUB.
        apply (DISJ (bv_unsigned (ev E k2))). lia.
      + assert (NEb : blk_id (p, Af, nf) <> blk_id blk2).
        { cbn [blk_id fst]. intros X. rewrite <- X in BP. rewrite (proj2 (bptr_eqb_true p p) eq_refl) in BP. discriminate BP. }
        assert (INK : in_iv (bv_unsigned (ev E k2), bv_unsigned (den E len2)) a) by (unfold in_iv; cbn [fst snd]; lia).
        specialize (SUB a INK). unfold in_iv in SUB. rewrite <- Eb2 in SUB. unfold blk_addr, blk_size in SUB. cbn [fst snd] in SUB.
        destruct (RHEAP_core_blocks_disjoint s LBf (ms_mem ms) (p, Af, nf) blk2 RC INf Hblk2 NEb) as [D|D];
          unfold blk_addr, blk_size in D; cbn [fst snd] in D; lia. }
  set (R6 := IMap.remove kf (Rg4 r0)).
  assert (F6 : forall k rg, IMap.find k R6 = Some rg -> k <> kf /\ IMap.find k (Rg4 r0) = Some rg).
  { intros k rg H. subst R6. destruct (Uint63.eqb kf k) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_remove_same in H by exact B4. discriminate H.
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_remove_other in H by (exact B4 || exact Q). split; [congruence| exact H]. }

  assert (LIVE : forall len kd b k, win_lookup wnl k = Some (len, kd) -> k <> kf -> In b LB -> 0 < bv_unsigned (den E len) ->
            (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) ->
            exists blk, In blk LBg /\ (blk_addr blk, blk_size blk) = b).
  { intros len kd b k WL NK Hb POS SUB.
    assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
    apply in_map_iff in Hb' as (blk & Eb & Hblk). exists blk. split; [| exact Eb]. apply LBG; [exact Hblk|]. intros EQ.
    pose proof (blk_by_id LBf blk (p, Af, nf) NDid Hblk INf EQ) as ->. unfold blk_addr, blk_size in Eb. cbn [fst snd] in Eb. subst b.
    destruct (FREED k len kd (win_lookup_In _ _ _ _ WL) NK) as [_ FR'].
    assert (INK : in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) (bv_unsigned (ev E k))) by (unfold in_iv; cbn [fst snd]; lia).
    pose proof (SUB _ INK) as IB. unfold in_iv in IB. cbn [fst snd] in IB.
    exact (FR' (bv_unsigned (ev E k)) ltac:(lia) IB). }
  assert (REGS : forall k rg, IMap.find k R6 = Some rg -> St.region_ok rsegs (s_priv st) E' M' k rg).
  { intros k rg H. destruct (F6 k rg H) as [NK H4']. destruct (Rg4_find r0 k rg Hr0 H4') as [[-> ->]|[[-> ->]|(K0' & K1' & F)]].
    - apply r0_ok. exact Hr0.
    - apply r1_ok.
    - apply (old_region_ok k rg F); [apply Uint63.eqb_false_spec; exact K0'|].
      apply (justified_client k rg F K0' K1'). intros len kd b WL Hb POS SUB. exact (LIVE len kd b k WL NK Hb POS SUB). }
  assert (NEWB : forall a, in_based E' R6 a -> in_based E' (s_regs st) a).
  { intros a (k & rg & H & K & R). destruct (F6 k rg H) as [_ H4']. apply (Rg4_in_based r0 a Hr0). exists k, rg. auto. }

  pose proof (cg_wf CG) as WF. rewrite WS in WF.
  assert (WIN : forall w, In w (l1 ++ l2) -> In w (l1 ++ Win Af nf K_BLOCK :: l2)) by (intros w Hw; apply in_app_iff in Hw as [Hw|Hw]; apply in_app_iff; [left| right; right]; exact Hw).
  assert (NOTF : forall w, In w (l1 ++ l2) -> w <> Win Af nf K_BLOCK).
  { intros w Hw ->. destruct (PROV _ Hw) as [S|(k2 & len2 & kd2 & I2 & NK2 & EW)]; [cbn in S; unfold K_STACK, K_BLOCK in S; lia|].
    injection EW as EA2 EN2 _. destruct (FREED k2 len2 kd2 I2 NK2) as [_ FR']. apply (FR' Af); lia. }
  assert (HH : St.op_holds OPS HEAP_ID (map (den E') hargs') M' mo').
  { rewrite OPS_holds1. exists (w2Z md), (den E' a'), (l1 ++ l2), (map (den E) (skipn (3 * n) rest)), (remove iv_eq_dec (Af, nf) LB).
    split; [exact DEC'|]. split; [apply aw_holdsW_intro; [rewrite (den_E' a' SVa); exact AWH| apply (NG_incl _ _ (cg_ng CG)); intros w Hw; rewrite WS; exact (WIN w Hw)]|]. split.
    - apply Forall_forall. intros w Hw.
      pose proof (proj1 (Forall_forall _ _) WF w (WIN w Hw)) as (W1 & W2 & W3 & ALT).
      split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
      destruct ALT as [[K S]|[[K B]|[K (b & Hb & SUB)]]]; [left; auto| right; left| right; right].
      + split; [exact K|]. apply in_in_remove; [| exact B]. intros EQ.
        destruct (PROV _ Hw) as [S|(k2 & len2 & kd2 & I2 & NK2 & ->)]; [rewrite K in S; unfold K_STACK, K_BLOCK in S; lia|].
        cbn [w_iv w_lo w_len] in EQ. injection EQ as EA2 EN2. destruct (FREED k2 len2 kd2 I2 NK2) as [_ FR']. apply (FR' Af); lia.
      + split; [exact K|].
        destruct (PROV _ Hw) as [S|(k2 & len2 & kd2 & I2 & NK2 & ->)]; [rewrite S in K; unfold K_STACK, K_SUB in K; lia|].
        cbn [w_iv w_lo w_len] in SUB. destruct (FREED k2 len2 kd2 I2 NK2) as [[POS|(Z0 & k3 & len3 & I3 & NK3)] FR'].
        * exists b. split; [| exact SUB]. apply in_in_remove; [| exact Hb]. intros ->.
          assert (INK : in_iv (bv_unsigned (ev E k2), bv_unsigned (den E len2)) (bv_unsigned (ev E k2))) by (unfold in_iv; cbn [fst snd]; lia).
          pose proof (SUB _ INK) as IB. unfold in_iv in IB. cbn [fst snd] in IB. apply (FR' (bv_unsigned (ev E k2))); lia.
        *
          destruct (nonstack_windows_In E n rest wnl k3 len3 CtrLib.K_BLOCK (cg_wnl CG) I3) as (K30 & K31 & _ & INW3).
          pose proof (proj1 (Forall_forall _ _) (cg_wf CG) _ INW3) as (_ & _ & _ & ALT3). cbn [w_kind w_lo w_len w_iv] in ALT3.
          change (w2Z CtrLib.K_BLOCK) with 1 in ALT3.
          destruct ALT3 as [[KS3 _]|[[_ B3]|[KS3 _]]]; [unfold K_STACK in KS3; lia| | unfold K_SUB in KS3; lia].
          exists (bv_unsigned (ev E k3), bv_unsigned (den E len3)). split.
          -- apply in_in_remove; [| exact B3]. intros EQ. injection EQ as EA3 EN3.
             destruct (FREED k3 len3 CtrLib.K_BLOCK I3 NK3) as [[POS3|[Z3 _]] FR3']; [| lia].
             apply (FR3' (bv_unsigned (ev E k3))); lia.
          -- intros a Ha. exfalso. unfold in_iv in Ha. cbn [w_iv w_lo w_len fst snd] in Ha. lia.
    - apply (cw_free Cw (w2Z md) _ LB (l1 ++ Win Af nf K_BLOCK :: l2) M' Af nf (l1 ++ l2)).
      + apply (cw_frame Cw _ _ _ _ (ms_mem ms) M'); [rewrite <- WS; exact (cg_cw CG)|]. intros a Ha U NW.
        unfold in_user in U. apply in_ivs_In in U as (b & Hb & Hin).
        assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
        apply in_map_iff in Hb' as (blk & Eb & Hblk).
        destruct (bptr_eqb (blk_id blk) p) eqn:BP.
        * exfalso. apply bptr_eqb_true in BP. pose proof (blk_by_id LBf blk (p, Af, nf) NDid Hblk INf BP) as ->.
          unfold blk_addr, blk_size in Eb. cbn [fst snd] in Eb. subst b. apply NW. unfold in_ws, heap_ws. apply in_ivs_In.
          exists (Af, nf). split; [| exact Hin]. apply in_map_iff. exists (Win Af nf K_BLOCK). split; [reflexivity|].
          apply filter_In. split; [apply in_app_iff; right; left; reflexivity| reflexivity].
        * assert (NEp : blk_id blk <> p) by (intros X; rewrite X, (proj2 (bptr_eqb_true p p) eq_refl) in BP; discriminate BP).
          destruct (client_byte a ltac:(unfold two64 in Ha; lia)) as (E1 & _); [| unfold wa in E1; symmetry; exact E1].
          right; right. exists blk. split; [apply LBG; assumption|]. unfold in_iv in Hin. rewrite <- Eb in Hin. cbn [fst snd] in Hin. exact Hin.
      + apply in_app_iff. right. left. reflexivity.
      + intros w. split.
        * intros Hw. split; [exact (WIN w Hw)| exact (NOTF w Hw)].
        * intros [Hw NE]. apply in_app_iff in Hw. apply in_app_iff. destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw| exfalso; exact (NE (eq_sym Hw))| right; exact Hw]. }
  assert (DK : den E' (VP k16 wzero) = PropExec.getr R' 10%bv) by (rewrite den_VPz, ev_k16; exact F16).
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
  - reflexivity.
  - rewrite rf_get_set_other by discriminate. change (rf_get (s_rf (clobber st)) X0) with (getr (clobber st) X0). rewrite getr_clobber. cbn [clob_pos]. exact Px0.
  - apply post_regs. exact DK.
  - exact Pfregs.
  - reflexivity.
  - pose proof (cg_ms CG) as MSE. pose proof Presv as X. unfold resv_ok in X |- *. destruct (s_resv st); [reflexivity| |exact I].
    exfalso. rewrite MSE in X. cbn in X. discriminate X.
  - exact Pfcsr.
  - reflexivity.
  - rewrite ev_E'_below; [exact (so_zero _ _ _ _ _ _ HS)|]. destruct NX as (_ & P & _). change (to_Z 0%uint63) with 0. lia.
  - subst R6. apply IMap.bst_remove. exact B4.
  - exact REGS.
  - intros k1 q1 k2 q2 H1 H2 NE K1' K2' W a X. destruct (F6 k1 q1 H1) as [_ G1]. destruct (F6 k2 q2 H2) as [_ G2].
    exact (Rg4_disjoint r0 Hr0 k1 q1 k2 q2 G1 G2 NE K1' K2' W a X).
  - eapply pub_of_regions. exact REGS.
  - exact Pfacts.
  - eapply (ops_hold_set_op OPS E' E' (s_ops st) HEAP_ID hargs _ (ms_mem ms) M' mo mo' (cg_find CG) (cg_count CG) Pops).
    + exact other_ops_hold.
    + exact HH.
  - assert (MAPH : map (den E') hargs = map (den E) hargs).
    { apply map_ext_in. intros u Hu. apply den_E'. destruct SVB_parts as (_ & _ & _ & _ & _ & OV).
      exact (forallb_In _ _ _ u (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) Hu). }
    eapply (ops_apart_set_op rsegs OPS E' E' (s_ops st) HEAP_ID hargs _ (s_regs st) R6 (s_priv st) (cg_find CG) (cg_count CG) Papart).
    + intros o a Ho NI IMP X. destruct (IMP X) as [NB' PR]. split; [| exact PR]. intros IB. exact (NB' (NEWB a IB)).
    + intros a X. rewrite OPS_fp1 in X. apply (proj1 (fp_spec IMGX _ _ _ _ _ a DEC')) in X as (Ra & NI & NWS).
      assert (OUTF : ~ (Af <= a < Af + nf) -> ~ in_ws (wins_of E n rest) a).
      { intros NA IW. apply NWS. unfold in_ws in IW |- *. rewrite WS in IW. rewrite map_app in IW |- *. cbn [map] in IW.
        apply (proj1 (in_ivs_app _ _ _)) in IW. apply (proj2 (in_ivs_app _ _ _)).
        destruct IW as [IW|IW]; [left; exact IW| right]. apply (proj1 (in_ivs_cons _ _ _)) in IW. destruct IW as [IW|IW]; [| exact IW].
        exfalso. unfold in_iv, w_iv in IW. cbn [fst snd w_lo w_len] in IW. lia. }
      assert (CASE : (Af <= a < Af + nf) \/ ~ in_ws (wins_of E n rest) a).
      { destruct (Z_lt_le_dec a Af) as [L|G]; [right; apply OUTF; lia|].
        destruct (Z_lt_le_dec a (Af + nf)) as [L2|G2]; [left; lia| right; apply OUTF; lia]. }
      destruct CASE as [INA|OLD].
      * split.
        -- intros (k & rg & H & K & R). destruct (F6 k rg H) as [NK H4']. rewrite <- (Uint63.eqb_false_spec k 0%uint63) in K || idtac.
           pose proof (Rg4_ranges r0 k rg Hr0 H4') as (rg' & F & L' & Mq & _). rewrite L', (Mq E') in R.
           destruct (reg_E' _ _ F) as (Ek & Eh & _). rewrite Ek, Eh in R.
           destruct (Uint63.eqb k STACK_ID) eqn:Q1.
           ++ apply Uint63.eqb_correct in Q1. subst k. rewrite (cg_r1 CG) in F. injection F as <-. pose proof (cg_ceil CG) as CE. unfold lo, base in *. lia.
           ++ apply Uint63.eqb_false_spec in Q1. assert (K' : k <> 0%uint63) by (apply Uint63.eqb_false_spec; exact K).
              assert (CL : rclient_addr LBg sp a).
              { apply (justified_client k rg' F K' Q1); [| exact R]. intros len kd b WL Hb POS SUB. exact (LIVE len kd b k WL NK Hb POS SUB). }
              destruct CL as [S1|[[I1 I2]|(blk & Hblk & Rb)]].
              ** pose proof (cg_ceil CG) as CE. pose proof (cg_room CG) as RM. pose proof (int_range need). unfold sp, lo, base in *. lia.
              ** unfold RIMG_LO, RIMG_HI in Bf4. lia.
              ** pose proof (HLBg _ Hblk) as Hblk'.
                 assert (NEb : blk_id (p, Af, nf) <> blk_id blk).
                 { cbn [blk_id fst]. intros X2. exact (LBGid blk Hblk (eq_sym X2)). }
                 destruct (RHEAP_core_blocks_disjoint s LBf (ms_mem ms) (p, Af, nf) blk RC INf Hblk' NEb) as [D|D];
                   unfold blk_addr, blk_size in D, Rb; cbn [fst snd] in D; lia.
        -- intros [seg Hs]. exfalso. rewrite ref_find_segment_none in Hs; [discriminate Hs| lia| unfold RIMG_LO, RIMG_HI in Bf4; lia].
      * assert (X' : Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E') hargs))).
        { rewrite OPS_fp1, MAPH. apply (proj2 (fp_spec IMGX _ _ _ _ _ a (cg_decode CG))). auto. }
        destruct (ops_apart_find rsegs OPS E' (s_ops st) (s_regs st) (s_priv st) HEAP_ID hargs a Papart (cg_find CG) X') as [NB' PR].
        split; [| exact PR]. intros IB. exact (NB' (NEWB a IB)).
  - apply (St.plain_minv _ _ OPS_plain). apply mfacts'.
  - intros xa _. apply St.plain_cover. exact OPS_plain.
  - exact minv'.
Qed.

Theorem post_FB : forall r0 kf rf lenf p Af nf a' hargs' l1 l2 nsv rlo rhi Ablk nZ junk stFB,
  IMap.find 0%uint63 (s_regs st) = Some r0 -> st4 = alloc_post_mk ERRNO LIBC GOT GUARD CANARY st r ksp r0 r1 ->
  IMap.find kf (s_regs st) = Some rf -> kf <> 0%uint63 -> kf <> STACK_ID ->
  free_ok st wnl kf = Some lenf ->
  In (p, Af, nf) LBf -> Af = bv_unsigned (ev E kf) -> nf = bv_unsigned (den E lenf) ->
  (forall b, In b LBf -> blk_id b <> p -> In b LBg) -> (forall b, In b LBg -> blk_id b <> p) ->
  wins_of E n rest = l1 ++ Win Af nf K_BLOCK :: l2 ->
  (forall w, In w (l1 ++ l2) -> w_kind w = K_STACK \/ exists k len kd, In (k, len, kd) wnl /\ k <> kf /\
                                  w = Win (bv_unsigned (ev E k)) (bv_unsigned (den E len)) (w2Z kd)) ->
  decode (map (den E') hargs') = Some (w2Z md, den E' a', (l1 ++ l2) ++ [Win Ablk nZ K_BLOCK], map (den E) (skipn (3 * n) rest)) ->
  sv_vars_below (s_next st) a' = true ->
  sv_vars_below (s_next st) nsv = true -> nZ = bv_unsigned (den E nsv) ->
  Fv 16 = Z_to_bv 64 Ablk -> (forall o, 0 <= o < nZ -> nth_error junk (Z.to_nat o) = Some (Gv 16 o)) ->
  rw_cells rsegs M' Ablk [CB (Z.to_nat nZ) junk] ->
  4096 <= Ablk -> Ablk + nZ <= alloc_ceiling -> Ablk mod 16 = 0 -> (Ablk + nZ <= RIMG_LO \/ RIMG_HI <= Ablk) ->
  w2Z rlo <= Ablk <= w2Z rhi ->
  (forall blk a, In blk LBg -> blk_addr blk <= a < blk_addr blk + blk_size blk -> ~ (Ablk <= a < Ablk + nZ)) ->
  aw_holdsI (den E a') ((Ablk, nZ) :: remove iv_eq_dec (Af, nf) LB) M' mo' ->
  PropExec.getr R' 10%bv = Z_to_bv 64 Ablk ->
  stFB = SS r (rf_set (s_rf (clobber st)) X10 (VP k16 wzero)) (s_ff st) (s_resv st)
            (IMap.add k16 (blk_region nsv) (IMap.remove kf (Rg4 r0)))
            (FULt nsv (VL two47) :: FAlign k16 4%uint63 :: FRange k16 rlo rhi :: s_facts st)
            (set_op HEAP_ID hargs' (s_ops st)) (s_priv st) (PrimInt63.add k16 1%uint63) ->
  St.st_ok rsegs OPS E' stFB ms' mo' /\ MP mo'.
Proof.
  intros r0 kf rf lenf p Af nf a' hargs' l1 l2 nsv rlo rhi Ablk nZ junk stFB Hr0 E4 Hkf K0 K1 FOK INf EAf Enf LBG LBGid WS PROV DEC' SVa
         SVn EN F16 GJ RW A4096 AC A16 AI FR NEW AWH Ha0 ->.
  split; [| exact MP'].
  pose proof HS' as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  pose proof (Rg4_bst r0) as B4. pose proof alloc_ceiling_lt64 as C64.
  pose proof (bv_unsigned_in_range 64 (den E nsv)) as RN. unfold bv_modulus in RN.
  pose proof (cg_rheap CG) as RH. apply RHEAP_split in RH as [RC _].
  pose proof (RHEAP_core_nodup s LBf (ms_mem ms) RC) as NDid.
  destruct (free_ok_inv st wnl kf lenf FOK) as (rf' & Hrf' & WLf & LOf & NEf & LEf & OTH). rewrite Hkf in Hrf'. injection Hrf' as <-.
  apply (known_ltu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in NEf. rewrite unsigned_VL in NEf. change (w2Z wzero) with 0 in NEf. fold (hiZ E rf) in NEf.
  apply (known_leu_q_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in LEf. fold (hiZ E rf) in LEf. rewrite <- Enf in LEf.
  assert (LZf : loZ rf = 0) by (unfold loZ; rewrite LOf; reflexivity).

  assert (EK : bv_unsigned (ev E' k16) = Ablk).
  { rewrite ev_k16, F16, Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. unfold W64.two64. lia. }
  assert (DK : den E' (VP k16 wzero) = Z_to_bv 64 Ablk) by (rewrite den_VPz, ev_k16; exact F16).
  assert (EH' : hiZ E' (blk_region nsv) = nZ). { unfold hiZ, blk_region. cbn [Mem.rg_hi]. rewrite (den_E' nsv SVn). symmetry. exact EN. }
  assert (EL0 : loZ (blk_region nsv) = 0) by reflexivity.
  assert (K160 : PrimInt63.eqb k16 0%uint63 = false).
  { apply Uint63.eqb_false_spec. intros X. pose proof k16_Z as KZ. rewrite X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NX as (_ & P & _). lia. }
  assert (KF : forall k rg, IMap.find k (s_regs st) = Some rg -> k <> k16).
  { intros k rg Hk ->. destruct (reg_E' _ _ Hk) as (_ & _ & LT & _). apply Uint63.ltb_spec in LT. rewrite k16_Z in LT. lia. }

  destruct (RHEAP_core_block_range s LBf (ms_mem ms) _ RC INf) as (Bf1 & Bf2 & Bf3 & Bf4 & _). cbn [blk_addr blk_size fst snd] in Bf1, Bf2, Bf3, Bf4.

  assert (FREED : forall k2 len2 kd2, In (k2, len2, kd2) wnl -> k2 <> kf ->
            (0 < bv_unsigned (den E len2)
             \/ (bv_unsigned (den E len2) = 0 /\ exists k3 len3, In (k3, len3, CtrLib.K_BLOCK) wnl /\ k3 <> kf)) /\
            forall a, bv_unsigned (ev E k2) <= a < bv_unsigned (ev E k2) + bv_unsigned (den E len2) -> ~ (Af <= a < Af + nf)).
  { intros k2 len2 kd2 I2 NK.
    destruct (OTH k2 len2 kd2 I2 NK) as (rg2 & Hk2 & LO2 & NE2' & LE2 & WW & FULL).
    apply (known_leu_q_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in LE2. fold (hiZ E rg2) in LE2.
    pose proof (bv_unsigned_in_range 64 (den E (Mem.rg_hi rg2))) as HR2. rewrite bv_modulus_64 in HR2. fold (hiZ E rg2) in HR2.
    assert (NE2 : 0 < hiZ E rg2 \/ (bv_unsigned (den E len2) = 0 /\ exists k3 len3, In (k3, len3, CtrLib.K_BLOCK) wnl /\ k3 <> kf)).
    { destruct NE2' as [NE2|(KNB & HEQ & OB)].
      - left. apply (known_ltu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in NE2. rewrite unsigned_VL in NE2. change (w2Z wzero) with 0 in NE2. fold (hiZ E rg2) in NE2. exact NE2.
      - destruct (Z_lt_le_dec 0 (hiZ E rg2)) as [POS2|Z2]; [left; exact POS2| right]. split; [| exact OB].
        apply (known_eq_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in HEQ. apply (f_equal bv_unsigned) in HEQ. fold (hiZ E rg2) in HEQ. lia. }
    assert (LZ2 : loZ rg2 = 0) by (unfold loZ; rewrite LO2; reflexivity).
    destruct (nonstack_windows_In E n rest wnl k2 len2 kd2 (cg_wnl CG) I2) as (K20 & K21 & KD2 & INW2).
    split; [destruct NE2 as [NE2|NE2]; [left; lia| right; exact NE2]|]. intros a Ha INA.
    destruct NE2 as [NE2|[Z2 _]]; [| lia].
    assert (DISJ := so_disj _ _ _ _ _ _ HS kf rf k2 rg2 Hkf Hk2 ltac:(congruence) ltac:(apply Uint63.eqb_false_spec; exact K0) ltac:(apply Uint63.eqb_false_spec; exact K20)
                     ltac:(destruct WW; [left|right]; assumption)).
    rewrite LZf, LZ2, <- EAf in DISJ.
    pose proof (proj1 (Forall_forall _ _) (cg_wf CG) _ INW2) as (_ & _ & _ & [[KS _]|[[KB B2]|[KS (b & Hb & SUB)]]]); cbn [w_kind w_lo w_len w_iv] in *.
    - exact (KD2 KS).
    - assert (B2' : In (bv_unsigned (ev E k2), bv_unsigned (den E len2)) (blocks_of LBf))
        by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact B2]).
      apply in_map_iff in B2' as (blk2 & Eb2 & Hblk2).
      destruct (bptr_eqb (blk_id blk2) p) eqn:BP.
      + apply bptr_eqb_true in BP. pose proof (blk_by_id LBf blk2 (p, Af, nf) NDid Hblk2 INf BP) as ->.
        cbn [blk_addr blk_size fst snd] in Eb2. injection Eb2 as EA2 EN2.
        apply (DISJ Af). rewrite <- EA2. lia.
      + assert (NEb : blk_id (p, Af, nf) <> blk_id blk2).
        { cbn [blk_id fst]. intros X. rewrite <- X in BP. rewrite (proj2 (bptr_eqb_true p p) eq_refl) in BP. discriminate BP. }
        pose proof (f_equal fst Eb2) as E1. pose proof (f_equal snd Eb2) as E2. unfold blk_addr, blk_size in E1, E2. cbn [fst snd] in E1, E2.
        destruct (RHEAP_core_blocks_disjoint s LBf (ms_mem ms) (p, Af, nf) blk2 RC INf Hblk2 NEb) as [D|D];
          unfold blk_addr, blk_size in D; cbn [fst snd] in D; lia.
    - assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
      apply in_map_iff in Hb' as (blk2 & Eb2 & Hblk2).
      destruct (bptr_eqb (blk_id blk2) p) eqn:BP.
      + apply bptr_eqb_true in BP. pose proof (blk_by_id LBf blk2 (p, Af, nf) NDid Hblk2 INf BP) as ->.
        cbn [blk_addr blk_size fst snd] in Eb2. subst b.
        destruct FULL as [KDB|FU]; [rewrite KDB in KS; unfold K_SUB in KS; change (w2Z CtrLib.K_BLOCK) with 1 in KS; lia|].
        apply (known_eq_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in FU. apply (f_equal bv_unsigned) in FU. fold (hiZ E rf) in FU. rewrite <- Enf in FU.
        assert (INK : in_iv (bv_unsigned (ev E k2), bv_unsigned (den E len2)) (bv_unsigned (ev E k2))) by (unfold in_iv; cbn [fst snd]; lia).
        specialize (SUB (bv_unsigned (ev E k2)) INK). unfold in_iv in SUB. cbn [fst snd] in SUB.
        apply (DISJ (bv_unsigned (ev E k2))). lia.
      + assert (NEb : blk_id (p, Af, nf) <> blk_id blk2).
        { cbn [blk_id fst]. intros X. rewrite <- X in BP. rewrite (proj2 (bptr_eqb_true p p) eq_refl) in BP. discriminate BP. }
        assert (INK : in_iv (bv_unsigned (ev E k2), bv_unsigned (den E len2)) a) by (unfold in_iv; cbn [fst snd]; lia).
        specialize (SUB a INK). unfold in_iv in SUB. rewrite <- Eb2 in SUB. unfold blk_addr, blk_size in SUB. cbn [fst snd] in SUB.
        destruct (RHEAP_core_blocks_disjoint s LBf (ms_mem ms) (p, Af, nf) blk2 RC INf Hblk2 NEb) as [D|D];
          unfold blk_addr, blk_size in D; cbn [fst snd] in D; lia. }
  set (R6 := IMap.remove kf (Rg4 r0)).
  assert (B6 : IMap.bst R6) by (subst R6; apply IMap.bst_remove; exact B4).
  assert (F6 : forall k rg, IMap.find k R6 = Some rg -> k <> kf /\ IMap.find k (Rg4 r0) = Some rg).
  { intros k rg H. subst R6. destruct (Uint63.eqb kf k) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_remove_same in H by exact B4. discriminate H.
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_remove_other in H by (exact B4 || exact Q). split; [congruence| exact H]. }
  set (R7 := IMap.add k16 (blk_region nsv) R6).
  assert (F7 : forall k rg, IMap.find k R7 = Some rg -> (k = k16 /\ rg = blk_region nsv) \/ (k <> k16 /\ IMap.find k R6 = Some rg)).
  { intros k rg H. subst R7. destruct (Uint63.eqb k16 k) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_add_same in H by exact B6. injection H as <-. left; auto.
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other in H by (exact B6 || exact Q). right. split; [congruence| exact H]. }

  assert (LIVE : forall len kd b k, win_lookup wnl k = Some (len, kd) -> k <> kf -> In b LB -> 0 < bv_unsigned (den E len) ->
            (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) ->
            exists blk, In blk LBg /\ (blk_addr blk, blk_size blk) = b).
  { intros len kd b k WL NK Hb POS SUB.
    assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
    apply in_map_iff in Hb' as (blk & Eb & Hblk). exists blk. split; [| exact Eb]. apply LBG; [exact Hblk|]. intros EQ.
    pose proof (blk_by_id LBf blk (p, Af, nf) NDid Hblk INf EQ) as ->. unfold blk_addr, blk_size in Eb. cbn [fst snd] in Eb. subst b.
    destruct (FREED k len kd (win_lookup_In _ _ _ _ WL) NK) as [_ FR'].
    assert (INK : in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) (bv_unsigned (ev E k))) by (unfold in_iv; cbn [fst snd]; lia).
    pose proof (SUB _ INK) as IB. unfold in_iv in IB. cbn [fst snd] in IB.
    exact (FR' (bv_unsigned (ev E k)) ltac:(lia) IB). }

  assert (NEWR : forall a k rg, Ablk <= a < Ablk + nZ -> IMap.find k R6 = Some rg -> PrimInt63.eqb k 0%uint63 = false ->
            ~ (bv_unsigned (ev E' k) + loZ rg <= a < bv_unsigned (ev E' k) + hiZ E' rg)).
  { intros a k rg Ha Hk6 K R. destruct (F6 k rg Hk6) as [NK Hk]. destruct (Rg4_ranges r0 k rg Hr0 Hk) as (rg' & F & L' & Mq & _). rewrite L', (Mq E') in R.
    destruct (reg_E' _ _ F) as (Ek & Eh & _). rewrite Ek, Eh in R.
    destruct (Uint63.eqb k STACK_ID) eqn:Q1.
    - apply Uint63.eqb_correct in Q1. subst k. rewrite (cg_r1 CG) in F. injection F as <-.
      pose proof (cg_ceil CG) as CE. unfold lo, base in *. lia.
    - apply Uint63.eqb_false_spec in Q1. apply Uint63.eqb_false_spec in K.
      assert (CL : rclient_addr LBg sp a).
      { apply (justified_client k rg' F K Q1); [| exact R]. intros len kd b WL Hb POS SUB. exact (LIVE len kd b k WL NK Hb POS SUB). }
      destruct CL as [S1|[[I1 I2]|(blk & Hblk & Rb)]].
      + pose proof (cg_ceil CG) as CE. pose proof (cg_room CG) as RM. pose proof (int_range need). unfold sp, lo, base in *. lia.
      + unfold RIMG_LO, RIMG_HI in AI. lia.
      + exact (NEW blk a Hblk Rb Ha). }
  assert (REGS : forall k rg, IMap.find k R7 = Some rg -> St.region_ok rsegs (s_priv st) E' M' k rg).
  { intros k rg H. destruct (F7 k rg H) as [[-> ->]|[NK16 H6]].
    - apply (blk_region_ok nsv Ablk nZ junk); try assumption. lia.
    - destruct (F6 k rg H6) as [NK H4']. destruct (Rg4_find r0 k rg Hr0 H4') as [[-> ->]|[[-> ->]|(K0' & K1' & F)]].
      + apply r0_ok. exact Hr0.
      + apply r1_ok.
      + apply (old_region_ok k rg F); [apply Uint63.eqb_false_spec; exact K0'|].
        apply (justified_client k rg F K0' K1'). intros len kd b WL Hb POS SUB. exact (LIVE len kd b k WL NK Hb POS SUB). }
  assert (NEWB7 : forall a, in_based E' R7 a -> (Ablk <= a < Ablk + nZ) \/ in_based E' R6 a).
  { intros a (k & rg & H & K & R). destruct (F7 k rg H) as [[-> ->]|[NK16 H6]].
    - left. rewrite EK, EH', EL0 in R. lia.
    - right. exists k, rg. auto. }
  assert (NEWB6 : forall a, in_based E' R6 a -> in_based E' (s_regs st) a).
  { intros a (k & rg & H & K & R). destruct (F6 k rg H) as [_ H4']. apply (Rg4_in_based r0 a Hr0). exists k, rg. auto. }
  assert (NEWB : forall a, in_based E' R7 a -> (Ablk <= a < Ablk + nZ) \/ in_based E' (s_regs st) a).
  { intros a IB. destruct (NEWB7 a IB) as [BL|IB6]; [left; exact BL| right; exact (NEWB6 a IB6)]. }

  pose proof (cg_wf CG) as WF. rewrite WS in WF.
  assert (WIN : forall w, In w (l1 ++ l2) -> In w (l1 ++ Win Af nf K_BLOCK :: l2)) by (intros w Hw; apply in_app_iff in Hw as [Hw|Hw]; apply in_app_iff; [left| right; right]; exact Hw).
  assert (NOTF : forall w, In w (l1 ++ l2) -> w <> Win Af nf K_BLOCK).
  { intros w Hw ->. destruct (PROV _ Hw) as [S|(k2 & len2 & kd2 & I2 & NK2 & EW)]; [cbn in S; unfold K_STACK, K_BLOCK in S; lia|].
    injection EW as EA2 EN2 _. destruct (FREED k2 len2 kd2 I2 NK2) as [_ FR']. apply (FR' Af); lia. }

  assert (NEWU : forall a, in_iv (Ablk, nZ) a -> ~ in_user (remove iv_eq_dec (Af, nf) LB) a).
  { intros a Ha U. unfold in_user in U. apply in_ivs_In in U as (b & Hb & Hin). apply in_remove in Hb as [Hb NEb0].
    assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
    apply in_map_iff in Hb' as (blk & Eb & Hblk).
    destruct (bptr_eqb (blk_id blk) p) eqn:BP.
    - apply bptr_eqb_true in BP. pose proof (blk_by_id LBf blk (p, Af, nf) NDid Hblk INf BP) as ->.
      unfold blk_addr, blk_size in Eb. cbn [fst snd] in Eb. exact (NEb0 (eq_sym Eb)).
    - assert (NEp : blk_id blk <> p) by (intros X; rewrite X, (proj2 (bptr_eqb_true p p) eq_refl) in BP; discriminate BP).
      unfold in_iv in Hin, Ha. rewrite <- Eb in Hin. cbn [fst snd] in Hin, Ha.
      exact (NEW blk a (LBG blk Hblk NEp) Hin Ha). }
  assert (HH : St.op_holds OPS HEAP_ID (map (den E') hargs') M' mo').
  { rewrite OPS_holds1. exists (w2Z md), (den E' a'), ((l1 ++ l2) ++ [Win Ablk nZ K_BLOCK]), (map (den E) (skipn (3 * n) rest)), ((Ablk, nZ) :: remove iv_eq_dec (Af, nf) LB).
    split; [exact DEC'|]. split; [apply aw_holdsW_intro; [rewrite (den_E' a' SVa); exact AWH| apply NG_app_block; apply (NG_incl _ _ (cg_ng CG)); intros w Hw; rewrite WS; exact (WIN w Hw)]|]. split.
    - apply Forall_app. split.
      + apply Forall_forall. intros w Hw.
        pose proof (proj1 (Forall_forall _ _) WF w (WIN w Hw)) as (W1 & W2 & W3 & ALT).
        split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
        destruct ALT as [[K S]|[[K B]|[K (b & Hb & SUB)]]]; [left; auto| right; left| right; right].
        * split; [exact K|]. right. apply in_in_remove; [| exact B]. intros EQ.
          destruct (PROV _ Hw) as [S|(k2 & len2 & kd2 & I2 & NK2 & ->)]; [rewrite K in S; unfold K_STACK, K_BLOCK in S; lia|].
          cbn [w_iv w_lo w_len] in EQ. injection EQ as EA2 EN2. destruct (FREED k2 len2 kd2 I2 NK2) as [_ FR']. apply (FR' Af); lia.
        * split; [exact K|].
          destruct (PROV _ Hw) as [S|(k2 & len2 & kd2 & I2 & NK2 & ->)]; [rewrite S in K; unfold K_STACK, K_SUB in K; lia|].
          cbn [w_iv w_lo w_len] in SUB. destruct (FREED k2 len2 kd2 I2 NK2) as [[POS|(Z0 & _)] FR'].
          -- exists b. split; [| exact SUB]. right. apply in_in_remove; [| exact Hb]. intros ->.
             assert (INK : in_iv (bv_unsigned (ev E k2), bv_unsigned (den E len2)) (bv_unsigned (ev E k2))) by (unfold in_iv; cbn [fst snd]; lia).
             pose proof (SUB _ INK) as IB. unfold in_iv in IB. cbn [fst snd] in IB. apply (FR' (bv_unsigned (ev E k2))); lia.
          --
             eexists. split; [left; reflexivity|]. intros a Ha. exfalso. unfold in_iv in Ha. cbn [w_iv w_lo w_len fst snd] in Ha. lia.
      + constructor; [| constructor]. split; [cbn [w_lo]; lia|]. split; [cbn [w_len]; lia|]. split; [cbn [w_lo w_len]; unfold two64; lia|].
        right; left. split; [reflexivity|]. left. reflexivity.
    - apply (cw_grow Cw). 2:{ exact NEWU. }
      apply (cw_free Cw (w2Z md) _ LB (l1 ++ Win Af nf K_BLOCK :: l2) M' Af nf (l1 ++ l2)).
      + apply (cw_frame Cw _ _ _ _ (ms_mem ms) M'); [rewrite <- WS; exact (cg_cw CG)|]. intros a Ha U NW.
        unfold in_user in U. apply in_ivs_In in U as (b & Hb & Hin).
        assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
        apply in_map_iff in Hb' as (blk & Eb & Hblk).
        destruct (bptr_eqb (blk_id blk) p) eqn:BP.
        * exfalso. apply bptr_eqb_true in BP. pose proof (blk_by_id LBf blk (p, Af, nf) NDid Hblk INf BP) as ->.
          unfold blk_addr, blk_size in Eb. cbn [fst snd] in Eb. subst b. apply NW. unfold in_ws, heap_ws. apply in_ivs_In.
          exists (Af, nf). split; [| exact Hin]. apply in_map_iff. exists (Win Af nf K_BLOCK). split; [reflexivity|].
          apply filter_In. split; [apply in_app_iff; right; left; reflexivity| reflexivity].
        * assert (NEp : blk_id blk <> p) by (intros X; rewrite X, (proj2 (bptr_eqb_true p p) eq_refl) in BP; discriminate BP).
          destruct (client_byte a ltac:(unfold two64 in Ha; lia)) as (E1 & _); [| unfold wa in E1; symmetry; exact E1].
          right; right. exists blk. split; [apply LBG; assumption|]. unfold in_iv in Hin. rewrite <- Eb in Hin. cbn [fst snd] in Hin. exact Hin.
      + apply in_app_iff. right. left. reflexivity.
      + intros w. split.
        * intros Hw. split; [exact (WIN w Hw)| exact (NOTF w Hw)].
        * intros [Hw NE]. apply in_app_iff in Hw. apply in_app_iff. destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw| exfalso; exact (NE (eq_sym Hw))| right; exact Hw]. }
  assert (MAPH : map (den E') hargs = map (den E) hargs).
  { apply map_ext_in. intros u Hu. apply den_E'. destruct SVB_parts as (_ & _ & _ & _ & _ & OV).
    exact (forallb_In _ _ _ u (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) Hu). }
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
  - reflexivity.
  - rewrite rf_get_set_other by discriminate. change (rf_get (s_rf (clobber st)) X0) with (getr (clobber st) X0). rewrite getr_clobber. cbn [clob_pos]. exact Px0.
  - apply post_regs. rewrite DK. symmetry. exact Ha0.
  - exact Pfregs.
  - reflexivity.
  - pose proof (cg_ms CG) as MSE. pose proof Presv as X. unfold resv_ok in X |- *. destruct (s_resv st); [reflexivity| |exact I].
    exfalso. rewrite MSE in X. cbn in X. discriminate X.
  - exact Pfcsr.
  - reflexivity.
  - rewrite ev_E'_below; [exact (so_zero _ _ _ _ _ _ HS)|]. destruct NX as (_ & P & _). change (to_Z 0%uint63) with 0. lia.
  - subst R7. apply IMap.bst_add. exact B6.
  - exact REGS.
  - intros k1 q1 k2 q2 H1 H2 NE K1' K2' W a [X1 X2].
    destruct (F7 k1 q1 H1) as [[-> ->]|[N1 G1]]; destruct (F7 k2 q2 H2) as [[-> ->]|[N2 G2]].
    + exact (NE eq_refl).
    + rewrite EK, EH', EL0 in X1. exact (NEWR a k2 q2 ltac:(lia) G2 K2' X2).
    + rewrite EK, EH', EL0 in X2. exact (NEWR a k1 q1 ltac:(lia) G1 K1' X1).
    + destruct (F6 k1 q1 G1) as [_ G1']. destruct (F6 k2 q2 G2) as [_ G2'].
      exact (Rg4_disjoint r0 Hr0 k1 q1 k2 q2 G1' G2' NE K1' K2' W a (conj X1 X2)).
  - eapply pub_of_regions. exact REGS.
  - constructor; [| constructor; [| constructor; [| exact Pfacts]]].
    + cbn [fact_holds]. rewrite (den_E' nsv SVn), <- EN, unsigned_VL. change (w2Z two47) with (2 ^ 47).
      pose_ceil. unfold CEIL_MIN, CEIL_MAX in *. lia.
    + cbn [fact_holds]. rewrite EK. change (2 ^ to_Z 4%uint63) with 16. exact A16.
    + cbn [fact_holds]. rewrite EK. exact FR.
  - eapply (ops_hold_set_op OPS E' E' (s_ops st) HEAP_ID hargs _ (ms_mem ms) M' mo mo' (cg_find CG) (cg_count CG) Pops).
    + exact other_ops_hold.
    + exact HH.
  - eapply (ops_apart_set_op rsegs OPS E' E' (s_ops st) HEAP_ID hargs _ (s_regs st) R7 (s_priv st) (cg_find CG) (cg_count CG) Papart).
    + intros o a Ho NI IMP X. destruct (IMP X) as [NB' PR]. split; [| exact PR]. intros IB.
      destruct (NEWB a IB) as [BL|OLD]; [| exact (NB' OLD)].
      unfold not_id in NI. apply Uint63.eqb_false_spec in NI. destruct (OPS_fp_other _ _ a NI X) as [RNG _]. unfold RIMG_LO, RIMG_HI in AI. lia.
    + intros a X. rewrite OPS_fp1 in X. apply (proj1 (fp_spec IMGX _ _ _ _ _ a DEC')) in X as (Ra & NI & NWS).
      assert (NOTNEW : ~ (Ablk <= a < Ablk + nZ)).
      { intros BL. apply NWS. unfold in_ws. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). right. cbn [map].
        apply (proj2 (in_ivs_cons _ _ _)). left. unfold in_iv, w_iv. cbn [fst snd w_lo w_len]. exact BL. }
      assert (OUTF : ~ (Af <= a < Af + nf) -> ~ in_ws (wins_of E n rest) a).
      { intros NA IW. apply NWS. unfold in_ws in IW |- *. rewrite WS in IW. rewrite !map_app in IW |- *. cbn [map] in IW.
        apply (proj1 (in_ivs_app _ _ _)) in IW. apply (proj2 (in_ivs_app _ _ _)). left. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)).
        destruct IW as [IW|IW]; [left; exact IW| right]. apply (proj1 (in_ivs_cons _ _ _)) in IW. destruct IW as [IW|IW]; [| exact IW].
        exfalso. unfold in_iv, w_iv in IW. cbn [fst snd w_lo w_len] in IW. lia. }
      assert (CASE : (Af <= a < Af + nf) \/ ~ in_ws (wins_of E n rest) a).
      { destruct (Z_lt_le_dec a Af) as [L|G]; [right; apply OUTF; lia|].
        destruct (Z_lt_le_dec a (Af + nf)) as [L2|G2]; [left; lia| right; apply OUTF; lia]. }
      destruct CASE as [INA|OLD].
      * split.
        -- intros IB7. destruct (NEWB7 a IB7) as [BL|(k & rg & H & K & R)]; [exact (NOTNEW BL)|].
           destruct (F6 k rg H) as [NK H4']. rewrite <- (Uint63.eqb_false_spec k 0%uint63) in K || idtac.
           pose proof (Rg4_ranges r0 k rg Hr0 H4') as (rg' & F & L' & Mq & _). rewrite L', (Mq E') in R.
           destruct (reg_E' _ _ F) as (Ek & Eh & _). rewrite Ek, Eh in R.
           destruct (Uint63.eqb k STACK_ID) eqn:Q1.
           ++ apply Uint63.eqb_correct in Q1. subst k. rewrite (cg_r1 CG) in F. injection F as <-. pose proof (cg_ceil CG) as CE. unfold lo, base in *. lia.
           ++ apply Uint63.eqb_false_spec in Q1. assert (K' : k <> 0%uint63) by (apply Uint63.eqb_false_spec; exact K).
              assert (CL : rclient_addr LBg sp a).
              { apply (justified_client k rg' F K' Q1); [| exact R]. intros len kd b WL Hb POS SUB. exact (LIVE len kd b k WL NK Hb POS SUB). }
              destruct CL as [S1|[[I1 I2]|(blk & Hblk & Rb)]].
              ** pose proof (cg_ceil CG) as CE. pose proof (cg_room CG) as RM. pose proof (int_range need). unfold sp, lo, base in *. lia.
              ** unfold RIMG_LO, RIMG_HI in Bf4. lia.
              ** pose proof (HLBg _ Hblk) as Hblk'.
                 assert (NEb : blk_id (p, Af, nf) <> blk_id blk).
                 { cbn [blk_id fst]. intros X2. exact (LBGid blk Hblk (eq_sym X2)). }
                 destruct (RHEAP_core_blocks_disjoint s LBf (ms_mem ms) (p, Af, nf) blk RC INf Hblk' NEb) as [D|D];
                   unfold blk_addr, blk_size in D, Rb; cbn [fst snd] in D; lia.
        -- intros [seg Hs]. exfalso. rewrite ref_find_segment_none in Hs; [discriminate Hs| lia| unfold RIMG_LO, RIMG_HI in Bf4; lia].
      * assert (X' : Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E') hargs))).
        { rewrite OPS_fp1, MAPH. apply (proj2 (fp_spec IMGX _ _ _ _ _ a (cg_decode CG))). auto. }
        destruct (ops_apart_find rsegs OPS E' (s_ops st) (s_regs st) (s_priv st) HEAP_ID hargs a Papart (cg_find CG) X') as [NB' PR].
        split; [| exact PR]. intros IB. destruct (NEWB a IB) as [BL|OLD']; [exact (NOTNEW BL)| exact (NB' OLD')].
  - apply (St.plain_minv _ _ OPS_plain). apply mfacts'.
  - intros xa _. apply St.plain_cover. exact OPS_plain.
  - exact minv'.
Qed.

End POST.

Definition Fv_of (R' : bvmap 5 word) (e a : word) (i : Z) : word :=
  nth (Z.to_nat i)
      [PropExec.getr R' 1%bv; PropExec.getr R' 5%bv; PropExec.getr R' 6%bv; PropExec.getr R' 7%bv;
       PropExec.getr R' 11%bv; PropExec.getr R' 12%bv; PropExec.getr R' 13%bv; PropExec.getr R' 14%bv;
       PropExec.getr R' 15%bv; PropExec.getr R' 16%bv; PropExec.getr R' 17%bv;
       PropExec.getr R' 28%bv; PropExec.getr R' 29%bv; PropExec.getr R' 30%bv; PropExec.getr R' 31%bv; e; a]
      (Z_to_bv 64 0).

Lemma Fv_of_clob : forall R' e a x i, clob_pos x = Some i -> Fv_of R' e a (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x).
Proof.
  intros R' e a x i H. destruct x; cbn in H; try discriminate; injection H as <-; cbn; f_equal; apply bv_eq; reflexivity.
Qed.
Lemma Fv_of_15 : forall R' e a, Fv_of R' e a 15 = e. Proof. reflexivity. Qed.
Lemma Fv_of_16 : forall R' e a, Fv_of R' e a 16 = a. Proof. reflexivity. Qed.

Definition Gv_of (junk : list byte) (i : Z) (o : Z) : byte := nth (Z.to_nat o) junk (Z_to_bv 8 0).

Lemma size_ok_sound : forall E fs v, facts_hold E fs -> size_ok fs v = true -> 0 < bv_unsigned (den E v) < 2 ^ 48.
Proof.
  intros E fs v Hfs H. unfold size_ok in H. apply andb_prop in H as [H1 H2].
  apply (known_ltu_sound E _ _ _ Hfs) in H1. apply (known_ltu_sound E _ _ _ Hfs) in H2.
  rewrite unsigned_VL in H1, H2. change (w2Z wzero) with 0 in H1. change (w2Z size_lim) with (2 ^ 48) in H2. lia.
Qed.
Lemma size_ok32_sound : forall E fs v, facts_hold E fs -> size_ok32 fs v = true -> 0 < bv_unsigned (den E v) < 2 ^ 32.
Proof.
  intros E fs v Hfs H. unfold size_ok32 in H. apply andb_prop in H as [H1 H2].
  apply (known_ltu_sound E fs) in H1; [| exact Hfs]. apply (known_ltu_sound E fs) in H2; [| exact Hfs].
  rewrite unsigned_VL in H1, H2. change (w2Z wzero) with 0 in H1. change (w2Z two32) with (2 ^ 32) in H2. lia.
Qed.

Lemma heap_drop_A_eq : forall md A nw rest, heap_drop_A (VL md :: A :: VL nw :: rest) = Some (VL md :: VL wones :: VL nw :: rest).
Proof. reflexivity. Qed.

Lemma cw_post : forall LBf LB SP M M' md ca ws, Permutation (blocks_of LBf) LB -> rheap_pres LBf SP M M' ->
  cw_holds Cw md ca LB ws M -> cw_holds Cw md ca LB ws M'.
Proof.
  intros LBf LB SP M M' md ca ws P PR HC. apply (cw_frame Cw md ca LB ws M M' HC). intros a Ha U _.
  unfold in_user in U. apply in_ivs_In in U as (b & Hb & Hin).
  assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact P| exact Hb]).
  apply in_map_iff in Hb' as (blk & Eb & Hblk). unfold in_iv in Hin. rewrite <- Eb in Hin. cbn [fst snd] in Hin.
  destruct (PR a ltac:(unfold two64 in Ha; lia) ltac:(right; right; exists blk; split; [exact Hblk| exact Hin])) as [E1 _].
  unfold wa in E1. symmetry. exact E1.
Qed.

Lemma repl_post : forall LBf SP M M', rheap_pres LBf SP M M' -> rw_cells rsegs M RMREPL [C4 (wz 0)] -> rw_cells rsegs M' RMREPL [C4 (wz 0)].
Proof.
  intros LBf SP M M' PR RC. eapply rheap_pres_rw_cells; [exact PR| exact RC|]. right; left. cbn [cells_size csize Nat.add].
  unfold RMREPL, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia.
Qed.

Theorem malloc_s_sound : forall pc, to_Z pc = RMALLOC_SYM ->
  contract_sound rsegs OPS MP PB (malloc_s_c rsegs ERRNO LIBC GOT GUARD TP CANARY pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply malloc_s_c] in Happ. unfold malloc_s_apply in Happ.
  destruct (alloc_call rsegs ERRNO LIBC GOT GUARD TP CANARY ALLOC_STACK st) as [[[[r ksp] hargs0] wnl]|] eqn:AC; [|discriminate].
  destruct (alloc_call_sound Cw OPS OPS_plain OPS_holds1 PB CANARY PB_canary PB_secret E st ms mo ALLOC_STACK r ksp hargs0 wnl HS HPB ltac:(vm_compute; reflexivity) AC)
    as (off & r1 & n & md & A & nw & rest & s & LBf & LB & CG).
  pose proof (cg_hargs CG) as EH. rewrite EH, heap_drop_A_eq in Happ.
  destruct (size_ok (s_facts st) (getr st X10)) eqn:SZ; [|discriminate].
  unfold malloc_posts, malloc_posts_rg in Happ.
  destruct (alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp) as [st4|] eqn:H4; [|discriminate].
  cbn [block_posts] in Happ.
  destruct (block_post st4 (VL md :: VL wones :: VL nw :: rest) (getr st X10) (BLK_LO, BLK_HI)) as [stB|] eqn:HB; [|discriminate].
  apply Some_inj in Happ. subst sts.
  pose proof (size_ok_sound E _ _ (so_facts _ _ _ _ _ _ HS) SZ) as NZ. set (nZ := bv_unsigned (den E (getr st X10))) in *.
  pose proof (cg_nw CG) as (T & N & L).
  assert (SVn : sv_vars_below (s_next st) (getr st X10) = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB.
    do 5 (apply andb_prop in SVB as [SVB ?]). exact (rf_allb_get _ _ _ SVB X10). }
  assert (AVB : forallb (sv_vars_below (s_next st)) rest = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB. apply andb_prop in SVB as [_ OV].
    pose proof (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) as AV. rewrite EH in AV. cbn [op_args forallb] in AV.
    apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. exact AV. }

  pose proof (cg_ms CG) as MSE. rewrite Hspc in MSE. cbn [c_pc malloc_s_c] in MSE. rewrite Hpc in MSE. rewrite MSE.
  pose proof (cg_stk CG) as STK. pose proof (cg_room CG) as ROOM. pose proof (cg_hi CG) as HI. pose proof (cg_ceil CG) as CE.
  pose proof (int_range ALLOC_STACK) as RAS. change (to_Z ALLOC_STACK) with 8192 in ROOM, RAS.
  destruct (stk_split rsegs (ms_mem ms) _ (bv_unsigned (ev E STACK_ID) + keyZ ksp) _ STK ltac:(lia)) as [STK1 _].
  destruct (cg_errno CG) as [errv ERR].
  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 nZ).
  { subst nZ. rewrite <- reg_of_X10, (cg_regs CG X10). symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (cg_sp CG) as SP.
  apply (malloc_silent_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo s LBf nZ
           (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + keyZ ksp) errv K
           A0 ltac:(lia) (cg_tp CG) (cg_ra CG) (cg_rheap CG) (cg_krel CG) (cg_auxv CG) ltac:(rewrite SP; lia)
           ltac:(rewrite SP; exact STK1) CE ltac:(rewrite SP; unfold RMALLOC_STACK; lia) ERR (cg_minv CG) (cg_mo CG)).
  -
    intros R' M' mo' s' errv' GP MPATH MTR Ha0 ERR' RH' KR'. apply RHEAP_split in RH' as [RC' PU'].
    set (Fv := Fv_of R' errv' (Z_to_bv 64 0)). set (Gv := Gv_of []).
    assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
    assert (DECN : decode (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest)) = Some (w2Z md, wbv wones, wins_of E n rest, map (den E) (skipn (3 * n) rest))).
    { rewrite (decode_hargs (E' E st Fv Gv) md (VL wones) nw rest n T N L), (wins_of_E' E st Fv Gv n rest AVB), den_VL. f_equal. f_equal.
      apply map_ext_in. intros u Hu. apply (den_E' E st Fv Gv). apply (forallb_In _ _ _ u AVB).
      rewrite <- (firstn_skipn (3 * n) rest). apply in_app_iff. right. exact Hu. }
    assert (HH : St.op_holds OPS HEAP_ID (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest)) M' mo').
    { rewrite OPS_holds1. exists (w2Z md), (wbv wones), (wins_of E n rest), (map (den E) (skipn (3 * n) rest)), LB.
      split; [exact DECN|]. split; [| split; [exact (cg_wf CG)| exact (cw_post LBf LB _ _ _ _ _ _ (cg_perm CG) (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_cw CG))]].
      apply aw_holdsW_intro; [| exact (cg_ng CG)]. exists s', LBf. split; [exact (cg_perm CG)|]. split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
      split; [apply pclaim_none; rewrite wbv_unsigned; change (w2Z wones) with (2 ^ 64 - 1); lia|].
      exact (repl_post LBf _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG)). }
    assert (FP : forall a, Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest))) ->
                           Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E) hargs0))).
    { intros a X. rewrite OPS_fp1 in X |- *. unfold heap_fp in X |- *. rewrite DECN in X. rewrite (cg_decode CG). exact X. }
    destruct (post_N E st ms mo ALLOC_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP ERR' PU' Fv Gv HF
                (Fv_of_15 _ _ _) st4 H4 (VL wzero) (VL md :: VL wones :: VL nw :: rest) (fun b H => H)
                ltac:(rewrite den_VL, Ha0; reflexivity) HH FP) as [ST MP'].
    rewrite (cg_ra_r CG). exact (HK _ (or_introl eq_refl) _ _ _ (EXT E st Fv Gv) MP' ST).
  -
    intros R' M' mo' s' errv' p Ab junk GP MPATH MTR Ha0 ERR' RNG CELLS EXP RH' KR'. apply RHEAP_split in RH' as [RC' PU'].
    destruct RNG as (Apos & A16 & Nn & AC' & AI).
    set (Fv := Fv_of R' errv' (Z_to_bv 64 Ab)). set (Gv := Gv_of junk).
    assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
    destruct (RHEAP_core_block_range s' ((p, Ab, nZ) :: LBf) M' (p, Ab, nZ) RC' (or_introl eq_refl)) as (B4096 & _). cbn [blk_addr fst snd] in B4096.
    pose proof (RHEAP_core_nodup s' _ M' RC') as ND. cbn [map blk_id fst] in ND. apply List.NoDup_cons_iff in ND as [NI ND'].
    assert (NEW : forall b a, In b LB -> in_iv b a -> ~ (Ab <= a < Ab + nZ)).
    { intros b a Hb Hin R5.
      assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
      apply in_map_iff in Hb' as (blk & Eb & Hblk).
      assert (NEb : blk_id (p, Ab, nZ) <> blk_id blk).
      { cbn [blk_id fst]. intros X. apply NI. rewrite X. apply in_map_iff. exists blk. auto. }
      destruct (RHEAP_core_blocks_disjoint s' _ M' (p, Ab, nZ) blk RC' (or_introl eq_refl) (or_intror Hblk) NEb) as [D|D];
        unfold in_iv in Hin; rewrite <- Eb in Hin; unfold blk_addr, blk_size in D, Hin; cbn [fst snd] in D, Hin; lia. }
    assert (LJ : length junk = Z.to_nat nZ) by (destruct CELLS as [[[LJ _] _] _]; exact LJ).
    assert (GJ : forall o, 0 <= o < nZ -> nth_error junk (Z.to_nat o) = Some (Gv 16 o)).
    { intros o Ho. unfold Gv, Gv_of. apply nth_error_nth'. rewrite LJ. lia. }
    assert (AWH : aw_holdsI (den E (VL wones)) ((Ab, nZ) :: LB) M' mo').
    { exists s', ((p, Ab, nZ) :: LBf). split; [cbn [blocks_of map blk_addr blk_size fst snd]; apply perm_skip; exact (cg_perm CG)|].
      split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
      split; [apply pclaim_none; rewrite den_VL, wbv_unsigned; change (w2Z wones) with (2 ^ 64 - 1); lia|].
      exact (repl_post LBf _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG)). }
    pose proof alloc_ceiling_lt47 as C47.
    destruct (post_B E st ms mo ALLOC_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP (fun b H => H) ERR' PU' Fv Gv HF
                (Fv_of_15 _ _ _) st4 H4 (VL md :: VL wones :: VL nw :: rest) (VL wones) (getr st X10) BLK_LO BLK_HI stB Ab nZ junk
                eq_refl HB SVn eq_refl eq_refl (Fv_of_16 _ _ _) GJ CELLS B4096 AC' A16 ltac:(unfold RIMG_LO, RIMG_HI; lia)
                ltac:(change (w2Z BLK_LO) with 4096; change (w2Z BLK_HI) with (2 ^ 47 - 1); lia) NEW (fun b H => H) AWH Ha0) as [ST MP'].
    rewrite (cg_ra_r CG). exact (HK _ (or_intror (or_introl eq_refl)) _ _ _ (EXT E st Fv Gv) MP' ST).
Qed.

Theorem aligned_alloc_sound : forall IMG_HI pc, to_Z IMG_HI = RIMG_HI -> to_Z pc = RALIGNED16_SYM ->
  contract_sound rsegs OPS MP PB (aligned_alloc_c rsegs ERRNO LIBC GOT GUARD TP CANARY IMG_HI pc).
Proof.
  intros IMG_HI pc HIMG Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply aligned_alloc_c] in Happ. unfold aligned_alloc_apply in Happ.
  destruct (alloc_call rsegs ERRNO LIBC GOT GUARD TP CANARY ALIGNED_STACK st) as [[[[r ksp] hargs0] wnl]|] eqn:AC; [|discriminate].
  destruct (getr st X10) as [al| | | | | | | | | |] eqn:HX10; try discriminate.
  destruct (alloc_call_sound Cw OPS OPS_plain OPS_holds1 PB CANARY PB_canary PB_secret E st ms mo ALIGNED_STACK r ksp hargs0 wnl HS HPB ltac:(vm_compute; reflexivity) AC)
    as (off & r1 & n & md & A & nw & rest & s & LBf & LB & CG).
  pose proof (cg_hargs CG) as EH. rewrite EH, heap_drop_A_eq in Happ.
  destruct (weqb al (wlit 16%uint63)) eqn:AL; [|discriminate]. apply weqb_eq in AL. subst al.
  destruct (size_ok (s_facts st) (getr st X11)) eqn:SZ; [|discriminate]. cbn [andb] in Happ.
  unfold malloc_posts_rg in Happ.
  destruct (alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp) as [st4|] eqn:H4; [|discriminate].
  cbn [block_posts] in Happ.
  destruct (block_post st4 (VL md :: VL wones :: VL nw :: rest) (getr st X11) (BLK_LO, wsub IMG_LO wone)) as [stB1|] eqn:HB1; [|discriminate].
  destruct (block_post st4 (VL md :: VL wones :: VL nw :: rest) (getr st X11) (wlit IMG_HI, BLK_HI)) as [stB2|] eqn:HB2; [|discriminate].
  apply Some_inj in Happ. subst sts.
  pose proof (size_ok_sound E _ _ (so_facts _ _ _ _ _ _ HS) SZ) as NZ. set (nZ := bv_unsigned (den E (getr st X11))) in *.
  pose proof (cg_nw CG) as (T & N & L).
  assert (SVn : sv_vars_below (s_next st) (getr st X11) = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB.
    do 5 (apply andb_prop in SVB as [SVB ?]). exact (rf_allb_get _ _ _ SVB X11). }
  assert (AVB : forallb (sv_vars_below (s_next st)) rest = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB. apply andb_prop in SVB as [_ OV].
    pose proof (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) as AV. rewrite EH in AV. cbn [op_args forallb] in AV.
    apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. exact AV. }
  pose proof (cg_ms CG) as MSE. rewrite Hspc in MSE. cbn [c_pc aligned_alloc_c] in MSE. rewrite Hpc in MSE. rewrite MSE.
  pose proof (cg_stk CG) as STK. pose proof (cg_room CG) as ROOM. pose proof (cg_hi CG) as HI. pose proof (cg_ceil CG) as CE.
  pose proof (int_range ALIGNED_STACK) as RAS. change (to_Z ALIGNED_STACK) with 8224 in ROOM, RAS.
  destruct (stk_split rsegs (ms_mem ms) _ (bv_unsigned (ev E STACK_ID) + keyZ ksp) _ STK ltac:(lia)) as [STK1 _].
  destruct (cg_errno CG) as [errv ERR].
  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 16).
  { rewrite <- reg_of_X10, (cg_regs CG X10), HX10, den_VL. reflexivity. }
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 nZ).
  { subst nZ. rewrite <- reg_of_X11, (cg_regs CG X11). symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (cg_sp CG) as SP.
  apply (aligned16_silent_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo s LBf nZ
           (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + keyZ ksp) errv K
           A0 A1 ltac:(lia) (cg_tp CG) (cg_ra CG) (cg_rheap CG) (cg_krel CG) (cg_auxv CG) ltac:(rewrite SP; lia)
           ltac:(rewrite SP; exact STK1) CE ltac:(rewrite SP; unfold RALIGNED16_STACK, RMALLOC_STACK; lia) ERR (cg_minv CG) (cg_repl CG) (cg_mo CG)).
  -
    intros R' M' mo' s' errv' GP MPATH MTR Ha0 ERR' RH' KR'. apply RHEAP_split in RH' as [RC' PU'].
    set (Fv := Fv_of R' errv' (Z_to_bv 64 0)). set (Gv := Gv_of []).
    assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
    assert (DECN : decode (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest)) = Some (w2Z md, wbv wones, wins_of E n rest, map (den E) (skipn (3 * n) rest))).
    { rewrite (decode_hargs (E' E st Fv Gv) md (VL wones) nw rest n T N L), (wins_of_E' E st Fv Gv n rest AVB), den_VL. f_equal. f_equal.
      apply map_ext_in. intros u Hu. apply (den_E' E st Fv Gv). apply (forallb_In _ _ _ u AVB).
      rewrite <- (firstn_skipn (3 * n) rest). apply in_app_iff. right. exact Hu. }
    assert (HH : St.op_holds OPS HEAP_ID (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest)) M' mo').
    { rewrite OPS_holds1. exists (w2Z md), (wbv wones), (wins_of E n rest), (map (den E) (skipn (3 * n) rest)), LB.
      split; [exact DECN|]. split; [| split; [exact (cg_wf CG)| exact (cw_post LBf LB _ _ _ _ _ _ (cg_perm CG) (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_cw CG))]].
      apply aw_holdsW_intro; [| exact (cg_ng CG)]. exists s', LBf. split; [exact (cg_perm CG)|]. split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
      split; [apply pclaim_none; rewrite wbv_unsigned; change (w2Z wones) with (2 ^ 64 - 1); lia|].
      exact (repl_post LBf _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG)). }
    assert (FP : forall a, Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest))) ->
                           Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E) hargs0))).
    { intros a X. rewrite OPS_fp1 in X |- *. unfold heap_fp in X |- *. rewrite DECN in X. rewrite (cg_decode CG). exact X. }
    destruct (post_N E st ms mo ALIGNED_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP ERR' PU' Fv Gv HF
                (Fv_of_15 _ _ _) st4 H4 (VL wzero) (VL md :: VL wones :: VL nw :: rest) (fun b H => H)
                ltac:(rewrite den_VL, Ha0; reflexivity) HH FP) as [ST MP'].
    rewrite (cg_ra_r CG). exact (HK _ (or_introl eq_refl) _ _ _ (EXT E st Fv Gv) MP' ST).
  -
    intros R' M' mo' s' errv' p Ab junk GP MPATH MTR Ha0 ERR' RNG CELLS EXP RH' KR'. apply RHEAP_split in RH' as [RC' PU'].
    destruct RNG as (Apos & A16 & Nn & AC' & AI).
    set (Fv := Fv_of R' errv' (Z_to_bv 64 Ab)). set (Gv := Gv_of junk).
    assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
    destruct (RHEAP_core_block_range s' ((p, Ab, nZ) :: LBf) M' (p, Ab, nZ) RC' (or_introl eq_refl)) as (B4096 & _). cbn [blk_addr fst snd] in B4096.
    pose proof (RHEAP_core_nodup s' _ M' RC') as ND. cbn [map blk_id fst] in ND. apply List.NoDup_cons_iff in ND as [NI ND'].
    assert (NEW : forall b a, In b LB -> in_iv b a -> ~ (Ab <= a < Ab + nZ)).
    { intros b a Hb Hin R5.
      assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
      apply in_map_iff in Hb' as (blk & Eb & Hblk).
      assert (NEb : blk_id (p, Ab, nZ) <> blk_id blk).
      { cbn [blk_id fst]. intros X. apply NI. rewrite X. apply in_map_iff. exists blk. auto. }
      destruct (RHEAP_core_blocks_disjoint s' _ M' (p, Ab, nZ) blk RC' (or_introl eq_refl) (or_intror Hblk) NEb) as [D|D];
        unfold in_iv in Hin; rewrite <- Eb in Hin; unfold blk_addr, blk_size in D, Hin; cbn [fst snd] in D, Hin; lia. }
    assert (LJ : length junk = Z.to_nat nZ) by (destruct CELLS as [[[LJ _] _] _]; exact LJ).
    assert (GJ : forall o, 0 <= o < nZ -> nth_error junk (Z.to_nat o) = Some (Gv 16 o)).
    { intros o Ho. unfold Gv, Gv_of. apply nth_error_nth'. rewrite LJ. lia. }
    assert (AWH : aw_holdsI (den E (VL wones)) ((Ab, nZ) :: LB) M' mo').
    { exists s', ((p, Ab, nZ) :: LBf). split; [cbn [blocks_of map blk_addr blk_size fst snd]; apply perm_skip; exact (cg_perm CG)|].
      split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
      split; [apply pclaim_none; rewrite den_VL, wbv_unsigned; change (w2Z wones) with (2 ^ 64 - 1); lia|].
      exact (repl_post LBf _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG)). }
    pose proof alloc_ceiling_lt47 as C47.
    destruct AI as [LOW|HIGH].
    + destruct (post_B E st ms mo ALIGNED_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP (fun b H => H) ERR' PU' Fv Gv HF
                  (Fv_of_15 _ _ _) st4 H4 (VL md :: VL wones :: VL nw :: rest) (VL wones) (getr st X11) BLK_LO (wsub IMG_LO wone) stB1 Ab nZ junk
                  eq_refl HB1 SVn eq_refl eq_refl (Fv_of_16 _ _ _) GJ CELLS B4096 AC' A16 ltac:(unfold RIMG_LO, RIMG_HI; lia)
                  ltac:(change (w2Z BLK_LO) with 4096; change (w2Z (wsub IMG_LO wone)) with 65535; lia) NEW (fun b H => H) AWH Ha0) as [ST MP'].
      rewrite (cg_ra_r CG). exact (HK _ (or_intror (or_introl eq_refl)) _ _ _ (EXT E st Fv Gv) MP' ST).
    + destruct (post_B E st ms mo ALIGNED_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP (fun b H => H) ERR' PU' Fv Gv HF
                  (Fv_of_15 _ _ _) st4 H4 (VL md :: VL wones :: VL nw :: rest) (VL wones) (getr st X11) (wlit IMG_HI) BLK_HI stB2 Ab nZ junk
                  eq_refl HB2 SVn eq_refl eq_refl (Fv_of_16 _ _ _) GJ CELLS B4096 AC' A16 ltac:(unfold RIMG_LO, RIMG_HI; lia)
                  ltac:(rewrite wlit_ok, HIMG; change (w2Z BLK_HI) with (2 ^ 47 - 1); unfold RIMG_HI in *; lia) NEW (fun b H => H) AWH Ha0) as [ST MP'].
      rewrite (cg_ra_r CG). exact (HK _ (or_intror (or_intror (or_introl eq_refl))) _ _ _ (EXT E st Fv Gv) MP' ST).
Qed.

Theorem free_sound : forall pc, to_Z pc = RFREE_SYM ->
  contract_sound rsegs OPS MP PB (free_c rsegs ERRNO LIBC GOT GUARD TP CANARY pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply free_c] in Happ. unfold free_apply in Happ.
  destruct (alloc_call rsegs ERRNO LIBC GOT GUARD TP CANARY ALLOC_STACK st) as [[[[r ksp] hargs0] wnl]|] eqn:AC; [|discriminate].
  destruct (alloc_call_sound Cw OPS OPS_plain OPS_holds1 PB CANARY PB_canary PB_secret E st ms mo ALLOC_STACK r ksp hargs0 wnl HS HPB ltac:(vm_compute; reflexivity) AC)
    as (off & r1 & n & md & A & nw & rest & s & LBf & LB & CG).
  pose proof (cg_hargs CG) as EH. rewrite EH, heap_A_eq in Happ.
  destruct A as [a| | | | | | | | | |]; try discriminate.
  pose proof (cg_nw CG) as (T & N & L).
  assert (AVB : forallb (sv_vars_below (s_next st)) rest = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB. apply andb_prop in SVB as [_ OV].
    pose proof (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) as AV. rewrite EH in AV. cbn [op_args forallb] in AV.
    apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. exact AV. }
  pose proof (cg_ms CG) as MSE. rewrite Hspc in MSE. cbn [c_pc free_c] in MSE. rewrite Hpc in MSE. rewrite MSE.
  pose proof (cg_stk CG) as STK. pose proof (cg_room CG) as ROOM. pose proof (cg_hi CG) as HI. pose proof (cg_ceil CG) as CE.
  pose proof (int_range ALLOC_STACK) as RAS. change (to_Z ALLOC_STACK) with 8192 in ROOM, RAS.
  destruct (stk_split rsegs (ms_mem ms) _ (bv_unsigned (ev E STACK_ID) + keyZ ksp) _ STK ltac:(lia)) as [STK1 _].
  destruct (cg_errno CG) as [errv ERR]. pose proof (cg_sp CG) as SP.
  pose proof (fresh_ok_inv st (cg_fresh CG)) as (_ & NXpos & NX256).
  assert (K16 : to_Z (s_next st) + to_Z 16%uint63 < wB) by (change (to_Z 16%uint63) with 16; rewrite wB_two63, two63_eq; lia).
  destruct (getr st X10) as [w|kf o| | | | | | | | |] eqn:HX10; try discriminate.
  -
    destruct (weqb w wzero && is_lib a) eqn:C; [|discriminate]. apply andb_prop in C as [W0 LIB]. apply weqb_eq in W0. subst w.
    destruct (alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp) as [st4|] eqn:H4; [|discriminate].
    unfold fresh in Happ. cbn [fst snd] in Happ. apply Some_inj in Happ. subst sts.
    destruct (alloc_post_inv st r ksp st4 r1 (cg_r1 CG) H4) as (r0 & Hr0 & E4).
    assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 0).
    { rewrite <- reg_of_X10, (cg_regs CG X10), HX10, den_VL. reflexivity. }
    apply realizes_to_mkR. unfold mkR_of.
    eapply (evt_realizes rsegs _ _ mo K).
    + apply (rfree_null_spec (PropExec.getr (ms_regs ms) 1%bv)). exact A0.
    + exact (mo_ok_halted _ (cg_mo CG)).
    + exact (mo_ok_lazy _ (cg_mo CG)).
    + intros ms' ->.
      set (R' := mkR (PropExec.getr (ms_regs ms) 1%bv) (PropExec.getr (ms_regs ms) 2%bv) (PropExec.getr (ms_regs ms) 3%bv) (PropExec.getr (ms_regs ms) 4%bv)
                     (PropExec.getr (ms_regs ms) 5%bv) (PropExec.getr (ms_regs ms) 6%bv) (PropExec.getr (ms_regs ms) 7%bv) (PropExec.getr (ms_regs ms) 8%bv)
                     (PropExec.getr (ms_regs ms) 9%bv) (PropExec.getr (ms_regs ms) 10%bv) (PropExec.getr (ms_regs ms) 11%bv) (PropExec.getr (ms_regs ms) 12%bv)
                     (PropExec.getr (ms_regs ms) 13%bv) (PropExec.getr (ms_regs ms) 14%bv) (PropExec.getr (ms_regs ms) 15%bv) (PropExec.getr (ms_regs ms) 16%bv)
                     (PropExec.getr (ms_regs ms) 17%bv) (PropExec.getr (ms_regs ms) 18%bv) (PropExec.getr (ms_regs ms) 19%bv) (PropExec.getr (ms_regs ms) 20%bv)
                     (PropExec.getr (ms_regs ms) 21%bv) (PropExec.getr (ms_regs ms) 22%bv) (PropExec.getr (ms_regs ms) 23%bv) (PropExec.getr (ms_regs ms) 24%bv)
                     (PropExec.getr (ms_regs ms) 25%bv) (PropExec.getr (ms_regs ms) 26%bv) (PropExec.getr (ms_regs ms) 27%bv) (PropExec.getr (ms_regs ms) 28%bv)
                     (PropExec.getr (ms_regs ms) 29%bv) (PropExec.getr (ms_regs ms) 30%bv) (PropExec.getr (ms_regs ms) 31%bv)).
      rewrite (cg_ra CG), (cg_ra_r CG).
      set (Fv := Fv_of R' errv (PropExec.getr R' 10%bv)). set (Gv := Gv_of []).
      assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
      assert (GP : gpost (ms_regs ms) (ms_mem ms) mo LBf (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + keyZ ksp) R' (ms_mem ms) mo).
      { constructor.
        - intros x Hx. subst R'. apply kept_mkR. exact Hx.
        - exact (cg_minv CG).
        - rewrite SP. exact STK1.
        - exact (cg_auxv CG).
        - apply rauxcell_pres_refl.
        - apply rheap_pres_refl.
        - exact (cg_mo CG).
        - apply vm_agree_refl. }
      assert (MAPH : map (den (E' E st Fv Gv)) hargs0 = map (den E) hargs0).
      { apply map_ext_in. intros u Hu. apply (den_E' E st Fv Gv). destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB.
        apply andb_prop in SVB as [_ OV]. exact (forallb_In _ _ _ u (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) Hu). }
      assert (HH : St.op_holds OPS HEAP_ID (map (den (E' E st Fv Gv)) hargs0) (ms_mem ms) mo).
      { rewrite MAPH. exact (ops_hold_find OPS E (s_ops st) (ms_mem ms) mo HEAP_ID _ (so_ops _ _ _ _ _ _ HS) (cg_find CG)). }
      destruct (post_N E st ms mo ALLOC_STACK r ksp hargs0 wnl off r1 n md (VL a) nw rest s LBf LB HS HPB HMP CG R' (ms_mem ms) mo LBf errv GP ERR (cg_pubs CG) Fv Gv HF
                  (Fv_of_15 _ _ _) st4 H4 (VP (PrimInt63.add (s_next st) 16%uint63) wzero) hargs0 (fun b H => H)
                  ltac:(rewrite den_VPz; unfold E'; rewrite (ev_above_lit E (s_next st) Fv Gv 16%uint63 K16); reflexivity) HH ltac:(intros a0 X; rewrite MAPH in X; exact X)) as [ST MP'].
      refine (HK _ (or_introl eq_refl) _ _ _ (EXT E st Fv Gv) MP' _).
      refine (st_ok_fields rsegs OPS _ _ _ _ _ _ _ _ _ _ _ _ _ ST); subst st4; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next setr set_ops set_next alloc_post_mk]; try reflexivity.
      rewrite (set_op_same HEAP_ID (s_ops st) hargs0 (cg_find CG)). reflexivity.
  -
    destruct (negb (weqb o wzero) || PrimInt63.eqb kf 0 || PrimInt63.eqb kf STACK_ID) eqn:C; [discriminate|].
    apply orb_false_iff in C as [C K1]. apply orb_false_iff in C as [O0 K0]. apply negb_false_iff in O0. apply weqb_eq in O0. subst o.
    apply Uint63.eqb_false_spec in K0. apply Uint63.eqb_false_spec in K1.
    match type of Happ with context [match ?na with Some _ => _ | None => None end = Some sts] =>
      match na with (if is_lib a then _ else _) => destruct na as [av|] eqn:NA; [|discriminate] end end.
    destruct (free_ok st wnl kf) as [lenf|] eqn:FOK; [|discriminate].
    unfold heap_del_window in Happ.
    assert (NW' : heap_nwin (VL md :: VL a :: VL nw :: rest) = Some n) by (pose proof (cg_nwin CG) as X; rewrite EH in X; exact X).
    rewrite NW' in Happ.
    destruct (del_window n (firstn (3 * n) rest) (VP kf wzero)) as [ws'|] eqn:DEL; [|discriminate].
    destruct (alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp) as [st4|] eqn:H4; [|discriminate].
    cbn [heap_set_A] in Happ. unfold fresh in Happ. cbn [fst snd] in Happ. apply Some_inj in Happ. subst sts.
    destruct (alloc_post_inv st r ksp st4 r1 (cg_r1 CG) H4) as (r0 & Hr0 & E4).

    destruct (free_ok_inv st wnl kf lenf FOK) as (rf & Hkf & WLf & LOf & NEf & LEf & OTH).
    apply (known_ltu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in NEf. rewrite unsigned_VL in NEf. change (w2Z wzero) with 0 in NEf.
    apply (known_leu_q_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in LEf.
    set (Af := bv_unsigned (ev E kf)). set (nf := bv_unsigned (den E lenf)).
    destruct (nonstack_windows_In E n rest wnl kf lenf CtrLib.K_BLOCK (cg_wnl CG) (win_lookup_In _ _ _ _ WLf)) as (_ & _ & _ & INW).
    pose proof (cg_rheap CG) as RH. pose proof RH as RH0. apply RHEAP_split in RH0 as [RC _]. pose proof (RHEAP_core_nodup s LBf (ms_mem ms) RC) as NDid.
    pose proof (proj1 (Forall_forall _ _) (cg_wf CG) _ INW) as (_ & _ & _ & [[KS _]|[[_ BLB]|[KS _]]]); cbn [w_kind w_lo w_len w_iv] in *;
      [exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_STACK in KS; lia| | exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_SUB in KS; lia].
    fold Af nf in BLB.
    assert (BLB' : In (Af, nf) (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact BLB]).
    apply in_map_iff in BLB' as ([[p A1] n1] & Eb & INf). cbn [blk_addr blk_size fst snd] in Eb. injection Eb as -> ->.
    assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 Af).
    { rewrite <- reg_of_X10, (cg_regs CG X10), HX10, den_VPz. subst Af. symmetry. apply Z_to_bv_bv_unsigned. }
    apply (free_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo s LBf p Af nf
             (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + keyZ ksp) errv K
             A0 INf (cg_tp CG) (cg_ra CG) RH (cg_krel CG) (cg_auxv CG) ltac:(rewrite SP; lia)
             ltac:(rewrite SP; exact STK1) CE ltac:(rewrite SP; unfold RFREE_STACK; lia) ERR (cg_minv CG) (cg_mo CG)).
    intros R' M' mo' s' GP MPATH MTR ERR' RH' KR'. pose proof RH' as RH1. apply RHEAP_split in RH1 as [RC' PU'].
    set (Fv := Fv_of R' errv (PropExec.getr R' 10%bv)). set (Gv := Gv_of []).
    assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).

    assert (L3 : length (firstn (3 * n) rest) = (3 * n)%nat) by (apply firstn_length_le; exact L).
    assert (NWf : nonstack_windows n (firstn (3 * n) rest) = Some wnl) by (rewrite nonstack_windows_firstn; exact (cg_wnl CG)).
    destruct (del_window_split E n (firstn (3 * n) rest) kf ws' wnl DEL NWf ltac:(lia)) as (l1 & len & l2 & INlen & WS & WS' & LEN & M1).
    rewrite <- (app_nil_r (firstn (3 * n) rest)), (wins_of_firstn E n rest []) in WS by exact L.
    destruct (windows_anchored_nodup _ _ _ _ _ _ _ (cg_anch CG) INlen (win_lookup_In _ _ _ _ WLf)) as [-> _]. fold Af nf in WS.
    pose proof (del_window_prov E n (firstn (3 * n) rest) kf ws' wnl NWf DEL (windows_anchored_nodup_anchors _ _ (cg_anch CG))) as PROV. rewrite WS' in PROV.
    assert (AVW : forallb (sv_vars_below (s_next st)) ws' = true).
    { apply forallb_forall. intros x Hx. apply (proj1 (forallb_forall _ _) AVB).
      pose proof (del_window_sub _ _ _ _ _ DEL Hx) as X. rewrite <- (firstn_skipn (3 * n) rest). apply in_app_iff. left. exact X. }
    destruct (wsub_one_small nw T ltac:(lia)) as [T' EN'].
    assert (DEC' : decode (map (den (E' E st Fv Gv)) (VL md :: av :: VL (wsub nw wone) :: ws' ++ skipn (3 * n) rest))
                   = Some (w2Z md, den (E' E st Fv Gv) av, l1 ++ l2, map (den E) (skipn (3 * n) rest))).
    { rewrite (decode_hargs (E' E st Fv Gv) md av (wsub nw wone) (ws' ++ skipn (3 * n) rest) (pred n) T' ltac:(rewrite EN'; lia) ltac:(rewrite app_length; lia)).
      rewrite (wins_of_prefix _ (pred n) ws' _ ltac:(lia)), (wins_of_E' E st Fv Gv (pred n) ws' AVW), WS'.
      rewrite (skipn_app_exact ws' (skipn (3 * n) rest) (3 * pred n) ltac:(lia)). f_equal. f_equal.
      apply map_ext_in. intros u Hu. apply (den_E' E st Fv Gv). apply (forallb_In _ _ _ u AVB).
      rewrite <- (firstn_skipn (3 * n) rest). apply in_app_iff. right. exact Hu. }

    pose proof (lb_remove_perm p Af nf LBf INf NDid) as PL.
    assert (NOTIN : ~ In (Af, nf) (blocks_of (lb_remove p LBf))).
    { intros X. apply in_map_iff in X as (blk & Eb & Hblk). apply In_lb_remove in Hblk as [Hblk NEp].
      assert (NEb : blk_id (p, Af, nf) <> blk_id blk) by (cbn [blk_id fst]; congruence).
      pose proof (f_equal fst Eb) as E1. pose proof (f_equal snd Eb) as E2. unfold blk_addr, blk_size in E1, E2. cbn [fst snd] in E1, E2.
      destruct (RHEAP_core_blocks_disjoint s LBf (ms_mem ms) (p, Af, nf) blk RC INf Hblk NEb) as [D|D]; unfold blk_addr, blk_size in D; cbn [fst snd] in D; lia. }
    assert (PERM' : Permutation (blocks_of (lb_remove p LBf)) (remove iv_eq_dec (Af, nf) LB)).
    { apply Permutation_sym. eapply Permutation_trans. { apply perm_remove. apply Permutation_sym. exact (cg_perm CG). }
      eapply Permutation_trans. { apply perm_remove. apply (Permutation_map (fun b => (blk_addr b, blk_size b))) in PL. exact PL. }
      cbn [map blk_addr blk_size fst snd remove]. destruct (iv_eq_dec (Af, nf) (Af, nf)); [| congruence].
      rewrite notin_remove by exact NOTIN. apply Permutation_refl. }

    assert (SVa : sv_vars_below (s_next st) av = true) by (destruct (is_lib a); [injection NA as <-; reflexivity|]; destruct (pw_ok a && free_stage_ok a wnl kf); [injection NA as <-; reflexivity| discriminate]).
    assert (AWH : aw_holdsI (den E av) (remove iv_eq_dec (Af, nf) LB) M' mo').
    { exists s', (lb_remove p LBf). split; [exact PERM'|]. split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
      split; [| exact (repl_post _ _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG))].
      destruct (is_lib a) eqn:LIB.
      - injection NA as <-. unfold is_lib in LIB. apply weqb_eq in LIB. subst a. apply pclaim_none. rewrite den_VL, wbv_unsigned. change (w2Z wones) with (2 ^ 64 - 1). lia.
      - destruct (pw_ok a && free_stage_ok a wnl kf) eqn:PW; [|discriminate]. injection NA as <-.
        apply andb_prop in PW as [PWA FSO]. destruct (pw_ok_inv a PWA) as (Ta & Ra & Ea).
        unfold free_stage_ok in FSO. apply andb_prop in FSO as [FSO BW]. apply andb_prop in FSO as [NB2 JLT].
        apply Uint63.eqb_correct in NB2. pose proof (pw_nb_eq a) as NBE. rewrite NB2 in NBE. change (to_Z 2%uint63) with 2 in NBE.
        apply Uint63.ltb_spec in JLT. rewrite pw_j_eq in JLT. change (to_Z 255%uint63) with 255 in JLT.

        pose proof (cg_claim CG) as CL. rewrite den_VL, wbv_unsigned, Ea in CL.
        destruct (CL ltac:(lia)) as [RM HP]. rewrite <- NBE in HP.
        replace (to_Z (wl a) / 256) with 2 in HP by lia.
        destruct HP as [[X _]|[[X _]|[_ (k & po & Ao & p' & A' & sp0 & K10 & HIS & MM & PLB)]]]; [lia| lia|].

        assert (TWO : exists ks cf cs, In (kf, VL cf, CtrLib.K_BLOCK) wnl /\ In (ks, VL cs, CtrLib.K_BLOCK) wnl /\ ks <> kf
                 /\ cs = wadd cf cf /\ wleu cs CAP_MAX = true).
        { destruct (block_windows wnl) as [|[k1 [c1| | | | | | | | | |]] [|[k2 [c2| | | | | | | | | |]] [|]]] eqn:BWE; try discriminate.
          pose proof (block_windows_In wnl k1 (VL c1) ltac:(rewrite BWE; left; reflexivity)) as I1.
          pose proof (block_windows_In wnl k2 (VL c2) ltac:(rewrite BWE; right; left; reflexivity)) as I2.
          destruct (Uint63.eqb k1 kf) eqn:Q1.
          - apply Uint63.eqb_correct in Q1. subst k1. apply andb_prop in BW as [BW NK2]. apply andb_prop in BW as [EC LE].
            apply weqb_eq in EC. apply negb_true_iff in NK2. apply Uint63.eqb_false_spec in NK2.
            exists k2, c1, c2. repeat split; assumption.
          - apply Uint63.eqb_false_spec in Q1. apply andb_prop in BW as [BW LE]. apply andb_prop in BW as [Q2 EC].
            apply Uint63.eqb_correct in Q2. subst k2. apply weqb_eq in EC.
            exists k1, c2, c1. repeat split; auto. }
        destruct TWO as (ks & cf & cs & Ikf & Iks & NKS & ECS & LECS).
        destruct (windows_anchored_nodup _ _ _ _ _ _ _ (cg_anch CG) Ikf (win_lookup_In _ _ _ _ WLf)) as [ELF _].
        destruct (nonstack_windows_In E n rest wnl ks (VL cs) CtrLib.K_BLOCK (cg_wnl CG) Iks) as (_ & _ & _ & INWs).
        pose proof (proj1 (Forall_forall _ _) (cg_wf CG) _ INWs) as (_ & _ & Ws3 & [[KS _]|[[_ BLs]|[KS _]]]); cbn [w_kind w_lo w_len w_iv] in *;
          [exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_STACK in KS; lia| | exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_SUB in KS; lia].
        rewrite unsigned_VL in BLs, Ws3.
        assert (NF : nf = w2Z cf) by (subst nf; rewrite <- ELF, unsigned_VL; reflexivity).
        pose proof (Permutation_map (fun b => (blk_addr b, blk_size b)) PLB) as PM. cbn [map blk_addr blk_size fst snd] in PM.
        change (map (fun b => (blk_addr b, blk_size b)) LBf) with (blocks_of LBf) in PM.
        assert (IN2 : forall x, In x LB -> x = (A', bufsz (S k)) \/ x = (Ao, bufsz k)).
        { intros x Hx. assert (Hx' : In x (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hx]).
          pose proof (Permutation_in _ PM Hx') as Hx''. cbn [In] in Hx''. destruct Hx'' as [<-|[<-|[]]]; auto. }
        pose proof (bufsz_pos k) as BP0. pose proof (bufsz_S k) as BS1. pose proof (bufsz_S (S k)) as BS2.
        destruct (RHEAP_core_block_range s LBf (ms_mem ms) _ RC INf) as (Bf1 & Bf2 & Bf3 & Bf4 & _). cbn [blk_addr blk_size fst snd] in Bf1, Bf2, Bf3, Bf4.
        assert (CS2 : w2Z cs = 2 * nf).
        { rewrite ECS, wadd_ok, <- NF. pose proof alloc_ceiling_lt47. unfold two64. rewrite Z.mod_small; lia. }
        rewrite CS2 in BLs.
        assert (FREED_OLD : Af = Ao /\ nf = bufsz k).
        { destruct (IN2 _ BLB) as [E1|E1]; injection E1 as Ea1 En1; [| auto].
          exfalso. destruct (IN2 _ BLs) as [E2|E2]; injection E2 as Ea2 En2; lia. }
        destruct FREED_OLD as [EAo ENo].
        assert (PP0 : p = po).
        { assert (INo : In (po, Ao, bufsz k) LBf) by (eapply Permutation_in; [apply Permutation_sym; exact PLB| right; left; reflexivity]).
          destruct (bptr_eqb p po) eqn:Q; [apply bptr_eqb_true in Q; exact Q| exfalso].
          assert (NEb : blk_id (p, Af, nf) <> blk_id (po, Ao, bufsz k)) by (cbn [blk_id fst]; intros X; rewrite X, (proj2 (bptr_eqb_true po po) eq_refl) in Q; discriminate Q).
          destruct (RHEAP_core_blocks_disjoint s LBf (ms_mem ms) _ _ RC INf INo NEb) as [D|D]; unfold blk_addr, blk_size in D; cbn [fst snd] in D; lia. }
        subst po.
        assert (INn : In (p', A', bufsz (S k)) LBf) by (eapply Permutation_in; [apply Permutation_sym; exact PLB| left; reflexivity]).
        rewrite EAo, ENo in INf.
        pose proof (MF3_F_i k sp0 p Ao p' A' s mo (to_Z (wl a) mod 256) s' mo' LBf HIS MM (cg_krel CG) INf INn (cg_mo CG) RM ltac:(pose proof (Z.mod_pos_bound (to_Z (wl a)) 256); lia) MPATH) as RM'.

        assert (EX : bv_unsigned (den E (VL (W64 false (PrimInt63.sub (PrimInt63.add (wl a) 1%uint63) PW_NB)))) = to_Z (wl a) + 1 - 256).
        { rewrite unsigned_VL. unfold w2Z. cbn [wt wl]. rewrite Uint63.sub_spec, Uint63.add_spec. change (to_Z 1%uint63) with 1. change (to_Z PW_NB) with 256.
          pose proof (Z.div_mod (to_Z (wl a)) 256 ltac:(lia)). pose proof (Z.mod_pos_bound (to_Z (wl a)) 256 ltac:(lia)).
          rewrite (Z.mod_small (to_Z (wl a) + 1)) by (rewrite wB_two63; unfold two63; lia). rewrite Z.mod_small by (rewrite wB_two63; unfold two63; lia). lia. }
        rewrite EX. intros _. pose proof (Z.div_mod (to_Z (wl a)) 256 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (to_Z (wl a)) 256 ltac:(lia)) as MB.
        assert (EQM : (to_Z (wl a) + 1 - 256) mod 256 = to_Z (wl a) mod 256 + 1).
        { replace (to_Z (wl a) + 1 - 256) with ((to_Z (wl a) mod 256 + 1) + 1 * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
        assert (EQD : (to_Z (wl a) + 1 - 256) / 256 = 1).
        { replace (to_Z (wl a) + 1 - 256) with ((to_Z (wl a) mod 256 + 1) + 1 * 256) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. reflexivity. }
        split.
        + rewrite EQM. exact RM'.
        + rewrite EQD.
          right; left. split; [reflexivity|]. exists (S k), p', A'. split; [lia|]. split; [eapply histR_S; eauto|].
          pose proof (RHEAP_core_nodup s LBf (ms_mem ms) RC) as ND2.
          assert (NPP : p' <> p).
          { intros ->. pose proof (Permutation_NoDup (Permutation_map blk_id PLB) ND2) as ND3. cbn [map blk_id fst] in ND3.
            apply List.NoDup_cons_iff in ND3 as [NI3 _]. apply NI3. left. reflexivity. }
          assert (QP : bptr_eqb p' p = false) by (destruct (bptr_eqb p' p) eqn:Q; [apply bptr_eqb_true in Q; congruence| reflexivity]).
          destruct (Permutation_length_2_inv (Permutation_sym PLB)) as [EL|EL]; rewrite EL;
            rewrite !lb_remove_cons; cbn [blk_id fst]; rewrite QP, (proj2 (bptr_eqb_true p p) eq_refl); reflexivity. }
    destruct (post_F E st ms mo ALLOC_STACK r ksp hargs0 wnl off r1 n md (VL a) nw rest s LBf LB HS HPB HMP CG R' M' mo' (lb_remove p LBf) errv GP
                ltac:(intros b Hb; apply In_lb_remove in Hb; exact (proj1 Hb)) ERR' PU' Fv Gv HF (Fv_of_15 _ _ _) st4
                r0 kf rf lenf p Af nf av _ l1 l2 _ Hr0 E4 Hkf K0 K1 FOK INf eq_refl eq_refl
                ltac:(intros b Hb Nb; apply In_lb_remove; auto) ltac:(intros b Hb; apply In_lb_remove in Hb; exact (proj2 Hb))
                WS PROV DEC' SVa AWH (Fv_of_16 _ _ _) eq_refl) as [ST MP'].
    rewrite (cg_ra_r CG). refine (HK _ (or_introl eq_refl) _ _ _ (EXT E st Fv Gv) MP' _).
    refine (st_ok_fields rsegs OPS _ _ _ _ _ _ _ _ _ _ _ _ _ ST); subst st4; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next setr set_ops setregs set_next alloc_post_mk]; try reflexivity.
Qed.

Lemma bufsz_lt_10 : forall k, bufsz k < 2 ^ 26 -> (k < 10)%nat.
Proof.
  intros k H. destruct (Nat.lt_ge_cases k 10) as [L|G]; [exact L|]. exfalso. unfold bufsz, BUF0 in H.
  assert (2 ^ 10 <= 2 ^ Z.of_nat k) by (apply Z.pow_le_mono_r; lia). change (2 ^ 26) with (65536 * 2 ^ 10) in H. nia.
Qed.
Lemma cap_ok_sound : forall c, cap_ok c = true -> exists k, (k <= 10)%nat /\ w2Z c = bufsz k.
Proof.
  intros c H. unfold cap_ok in H. cbn [existsb] in H.
  repeat match type of H with (?x || ?y) = true => destruct x eqn:?Q; [clear H| cbn [orb] in H] end;
  repeat match goal with Q : weqb c (wlit ?l) = true |- _ => apply weqb_eq in Q; subst c;
      match l with of_Z (65536 * 2 ^ ?z) => exists (Z.to_nat z) end; split; [lia| vm_compute; reflexivity] end.
  discriminate H.
Qed.

Theorem malloc_nofork : forall pc st stA stB (KB : TSet) E ms mo,
  to_Z pc = RMALLOC_SYM -> s_pc st = pc ->
  malloc_apply rsegs ERRNO LIBC GOT GUARD TP CANARY st = Some [stA; stB] ->
  St.st_ok rsegs OPS E st ms mo -> MP mo -> PB (eb E) ->
  (forall E2 ms2 mo2, env_ext (s_next st) E E2 -> MP mo2 -> St.st_ok rsegs OPS E2 stB ms2 mo2 -> realizes rsegs (mkCfg ms2 mo2) KB) ->
  realizes rsegs (mkCfg ms mo) KB.
Proof.
  intros pc st stA stB KB E ms mo Hpc Hspc Happ HS HMP HPB HKB.
  unfold malloc_apply in Happ.
  destruct (alloc_call rsegs ERRNO LIBC GOT GUARD TP CANARY ALLOC_STACK st) as [[[[r ksp] hargs0] wnl]|] eqn:AC; [|discriminate].
  destruct (alloc_call_sound Cw OPS OPS_plain OPS_holds1 PB CANARY PB_canary PB_secret E st ms mo ALLOC_STACK r ksp hargs0 wnl HS HPB ltac:(vm_compute; reflexivity) AC)
    as (off & r1 & n & md & A & nw & rest & s & LBf & LB & CG).
  pose proof (cg_hargs CG) as EH. rewrite EH, heap_A_eq in Happ.
  destruct A as [a| | | | | | | | | |]; try discriminate.
  destruct (pw_ok a && PrimInt63.leb (pw_j a) J_MAX && size_ok32 (s_facts st) (getr st X10)) eqn:C; [|discriminate].
  apply andb_prop in C as [C SZ]. apply andb_prop in C as [PWA JMAX].
  destruct (malloc_stage_ok (s_facts st) a wnl (getr st X10)) as [grow|] eqn:STG; [|discriminate].
  cbn [heap_set_A] in Happ. unfold malloc_posts, malloc_posts_rg in Happ.
  destruct (alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp) as [st4|] eqn:H4; [|discriminate].
  cbn [block_posts] in Happ.
  set (aB := if grow then VL (wadd a (wlit 257%uint63)) else VL wones) in Happ.
  destruct (block_post st4 (VL md :: aB :: VL nw :: rest) (getr st X10) (BLK_LO, BLK_HI)) as [stB'|] eqn:HB; [|discriminate].
  apply Some_inj in Happ. injection Happ as <- <-.
  pose proof (size_ok32_sound E _ _ (so_facts _ _ _ _ _ _ HS) SZ) as NZ. set (nZ := bv_unsigned (den E (getr st X10))) in *.
  pose proof (cg_nw CG) as (T & N & L).
  assert (SVn : sv_vars_below (s_next st) (getr st X10) = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB.
    do 5 (apply andb_prop in SVB as [SVB ?]). exact (rf_allb_get _ _ _ SVB X10). }
  assert (AVB : forallb (sv_vars_below (s_next st)) rest = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB. apply andb_prop in SVB as [_ OV].
    pose proof (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) as AV. rewrite EH in AV. cbn [op_args forallb] in AV.
    apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. exact AV. }

  destruct (pw_ok_inv a PWA) as (Ta & Ra & Ea). apply Uint63.leb_spec in JMAX. rewrite pw_j_eq in JMAX. change (to_Z J_MAX) with 27 in JMAX.
  pose proof (cg_claim CG) as CL. rewrite den_VL, wbv_unsigned, Ea in CL. destruct (CL ltac:(lia)) as [RM HP].
  pose proof (Z.div_mod (to_Z (wl a)) 256 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (to_Z (wl a)) 256 ltac:(lia)) as MB.
  pose proof (cg_rheap CG) as RH. pose proof RH as RH0. apply RHEAP_split in RH0 as [RC _].

  assert (STAGE : malloc_must_succeed s mo nZ /\
            (grow = true -> forall s' mo' p Ab rr, mpath (raw_malloc nZ) s mo rr s' mo' -> mtr_malloc s nZ (Some p) s' ->
               pclaim (to_Z (wl a) + 257) s' ((p, Ab, nZ) :: LBf) mo')).
  { unfold malloc_stage_ok in STG.
    destruct (Uint63.eqb (pw_nb a) 0%uint63) eqn:NB0.
    -
      apply Uint63.eqb_correct in NB0. pose proof (pw_nb_eq a) as NBE. rewrite NB0 in NBE. change (to_Z 0%uint63) with 0 in NBE.
      destruct (PrimInt63.eqb (pw_j a) 0 && sv_eqb (getr st X10) (VL (wlit 65536))) eqn:C0; [|discriminate]. apply Some_inj in STG. subst grow.
      apply andb_prop in C0 as [J0 N0]. apply Uint63.eqb_correct in J0. pose proof (pw_j_eq a) as JE. rewrite J0 in JE. change (to_Z 0%uint63) with 0 in JE.
      apply sv_eqb_eq in N0.
      assert (A0 : to_Z (wl a) = 0) by lia.
      assert (EN : nZ = BUF0) by (subst nZ; rewrite N0, unsigned_VL; reflexivity).
      rewrite <- NBE in HP. replace (to_Z (wl a) / 256) with 0 in HP by lia.
      destruct HP as [[_ [Es ELB]]|[[X _]|[X _]]]; [| lia| lia]. subst s LBf.
      pose proof (cg_krel CG) as KR0. rewrite A0 in RM. rewrite (Z.mod_0_l 256 ltac:(lia)) in RM.
      rewrite EN. split; [exact (MF_A_must_i mo KR0 (cg_mo CG) RM)|].
      intros _ s' mo' p Ab rr MPATH MTR. rewrite A0. unfold pclaim. intros _.
      replace ((0 + 257) mod 256) with (0 + 1) by reflexivity. replace ((0 + 257) / 256) with 1 by reflexivity.
      split.
      + exact (MF3_A_i mo 0 rr s' mo' KR0 (cg_mo CG) RM ltac:(lia) MPATH).
      + right; left. split; [reflexivity|]. exists O, p, Ab. split; [lia|]. split; [apply histR_O; exact MTR|].
        unfold bufsz; rewrite Z.pow_0_r, Z.mul_1_r; reflexivity.
    - destruct (Uint63.eqb (pw_nb a) 1%uint63) eqn:NB1; [|discriminate].
      apply Uint63.eqb_correct in NB1. pose proof (pw_nb_eq a) as NBE. rewrite NB1 in NBE. change (to_Z 1%uint63) with 1 in NBE.
      rewrite <- NBE in HP. replace (to_Z (wl a) / 256) with 1 in HP by lia.
      destruct HP as [[X _]|[[_ (k & p0 & A0 & K10 & HIS & ELB)]|[X _]]]; [lia| | lia].
      destruct (block_windows wnl) as [|[kb [c| | | | | | | | | |]] [|]] eqn:BWE; try discriminate.
      destruct (cap_ok c) eqn:CAP; [cbn [negb] in STG| discriminate].

      pose proof (block_windows_In wnl kb (VL c) ltac:(rewrite BWE; left; reflexivity)) as Ikb.
      destruct (nonstack_windows_In E n rest wnl kb (VL c) CtrLib.K_BLOCK (cg_wnl CG) Ikb) as (_ & _ & _ & INWb).
      pose proof (proj1 (Forall_forall _ _) (cg_wf CG) _ INWb) as (_ & _ & _ & [[KS _]|[[_ BLb]|[KS _]]]); cbn [w_kind w_lo w_len w_iv] in *;
        [exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_STACK in KS; lia| | exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_SUB in KS; lia].
      rewrite unsigned_VL in BLb.
      assert (BLb' : In (bv_unsigned (ev E kb), w2Z c) (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact BLb]).
      rewrite ELB in BLb'. cbn [blocks_of map blk_addr blk_size fst snd In] in BLb'. destruct BLb' as [BLb'|[]]. injection BLb' as _ EC.
      pose proof (bufsz_pos k) as BP0. pose proof (bufsz_S k) as BS1.
      pose proof (cg_krel CG) as KR1. rewrite ELB in KR1.
      destruct (sv_eqb (getr st X10) (VL (wadd c c)) && wltu c CAP_MAX) eqn:GR.
      +
        apply Some_inj in STG. subst grow. apply andb_prop in GR as [N2 CLT]. apply sv_eqb_eq in N2.
        rewrite wltu_w2Z in CLT || (unfold wltu in CLT). apply Z.ltb_lt in CLT. change (w2Z CAP_MAX) with (2 ^ 26) in CLT. rewrite <- EC in CLT.
        pose proof (bufsz_lt_10 k CLT) as K9.
        assert (EN : nZ = bufsz (S k)).
        { subst nZ. rewrite N2, unsigned_VL, wadd_ok, <- EC, BS1. unfold two64. rewrite Z.mod_small; lia. }
        rewrite EN. split; [exact (MF_B_must_i k s p0 A0 mo _ HIS KR1 (cg_mo CG) K9 RM ltac:(lia))|].
        intros _ s' mo' p Ab rr MPATH MTR LT. split.
        * replace ((to_Z (wl a) + 257) mod 256) with (to_Z (wl a) mod 256 + 1).
          { exact (MF3_B_i k s p0 A0 mo _ rr s' mo' HIS KR1 (cg_mo CG) K9 RM ltac:(lia) MPATH). }
          apply (Z.mod_unique_pos _ 256 (to_Z (wl a) / 256 + 1)); lia.
        * replace ((to_Z (wl a) + 257) / 256) with 2 by (apply (Z.div_unique_pos _ 256 2 (to_Z (wl a) mod 256 + 1)); lia).
          right; right. split; [reflexivity|]. exists k, p0, A0, p, Ab, s. split; [exact K9|]. split; [exact HIS|]. split; [exact MTR|]. rewrite ELB. apply Permutation_refl.
      +
        destruct (known_ltu (s_facts st) (VL wzero) (getr st X10) && known_ltu (s_facts st) (getr st X10) (VL CAP_MAX)) eqn:PC; [|discriminate].
        apply Some_inj in STG. subst grow. apply andb_prop in PC as [P1 P2].
        apply (known_ltu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in P1. apply (known_ltu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in P2.
        rewrite unsigned_VL in P1, P2. change (w2Z wzero) with 0 in P1. change (w2Z CAP_MAX) with (2 ^ 26) in P2. fold nZ in P1, P2.
        split; [exact (MF_C_must_i k s p0 A0 mo nZ _ HIS KR1 (cg_mo CG) K10 ltac:(lia) RM ltac:(lia))|].
        intros X; discriminate X. }
  destruct STAGE as (MUST & GCLAIM).

  pose proof (cg_ms CG) as MSE. rewrite Hspc, Hpc in MSE. rewrite MSE.
  pose proof (cg_stk CG) as STK. pose proof (cg_room CG) as ROOM. pose proof (cg_hi CG) as HI. pose proof (cg_ceil CG) as CE.
  pose proof (int_range ALLOC_STACK) as RAS. change (to_Z ALLOC_STACK) with 8192 in ROOM, RAS.
  destruct (stk_split rsegs (ms_mem ms) _ (bv_unsigned (ev E STACK_ID) + keyZ ksp) _ STK ltac:(lia)) as [STK1 _].
  destruct (cg_errno CG) as [errv ERR].
  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 nZ).
  { subst nZ. rewrite <- reg_of_X10, (cg_regs CG X10). symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (cg_sp CG) as SP.
  apply (malloc_must_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo s LBf nZ
           (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + keyZ ksp) errv KB
           A0 ltac:(lia) (cg_tp CG) (cg_ra CG) RH (cg_krel CG) (cg_auxv CG) ltac:(rewrite SP; lia)
           ltac:(rewrite SP; exact STK1) CE ltac:(rewrite SP; unfold RMALLOC_STACK; lia) ERR (cg_minv CG) (cg_mo CG) MUST).
  -
    intros R' M' mo' s' errv' p Ab junk GP MPATH MTR Ha0 ERR' RNG CELLS EXP RH' KR'. apply RHEAP_split in RH' as [RC' PU'].
    destruct RNG as (Apos & A16 & Nn & AC' & AI).
    set (Fv := Fv_of R' errv' (Z_to_bv 64 Ab)). set (Gv := Gv_of junk).
    assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
    destruct (RHEAP_core_block_range s' ((p, Ab, nZ) :: LBf) M' (p, Ab, nZ) RC' (or_introl eq_refl)) as (B4096 & _). cbn [blk_addr fst snd] in B4096.
    pose proof (RHEAP_core_nodup s' _ M' RC') as ND. cbn [map blk_id fst] in ND. apply List.NoDup_cons_iff in ND as [NI ND'].
    assert (NEW : forall b a1, In b LB -> in_iv b a1 -> ~ (Ab <= a1 < Ab + nZ)).
    { intros b a1 Hb Hin R5.
      assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
      apply in_map_iff in Hb' as (blk & Eb & Hblk).
      assert (NEb : blk_id (p, Ab, nZ) <> blk_id blk).
      { cbn [blk_id fst]. intros X. apply NI. rewrite X. apply in_map_iff. exists blk. auto. }
      destruct (RHEAP_core_blocks_disjoint s' _ M' (p, Ab, nZ) blk RC' (or_introl eq_refl) (or_intror Hblk) NEb) as [D|D];
        unfold in_iv in Hin; rewrite <- Eb in Hin; unfold blk_addr, blk_size in D, Hin; cbn [fst snd] in D, Hin; lia. }
    assert (LJ : length junk = Z.to_nat nZ) by (destruct CELLS as [[[LJ _] _] _]; exact LJ).
    assert (GJ : forall o, 0 <= o < nZ -> nth_error junk (Z.to_nat o) = Some (Gv 16 o)).
    { intros o Ho. unfold Gv, Gv_of. apply nth_error_nth'. rewrite LJ. lia. }
    assert (SVaB : sv_vars_below (s_next st) aB = true) by (subst aB; destruct grow; reflexivity).
    assert (AWH : aw_holdsI (den E aB) ((Ab, nZ) :: LB) M' mo').
    { exists s', ((p, Ab, nZ) :: LBf). split; [cbn [blocks_of map blk_addr blk_size fst snd]; apply perm_skip; exact (cg_perm CG)|].
      split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
      split; [| exact (repl_post LBf _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG))].
      subst aB. destruct grow.
      - rewrite den_VL, wbv_unsigned, wadd_ok, Ea, wlit_ok. change (to_Z 257%uint63) with 257. unfold two64. rewrite Z.mod_small by lia.
        exact (GCLAIM eq_refl s' mo' p Ab (Some p) MPATH MTR).
      - apply pclaim_none. rewrite den_VL, wbv_unsigned. change (w2Z wones) with (2 ^ 64 - 1). lia. }
    pose proof alloc_ceiling_lt47 as C47.
    destruct (post_B E st ms mo ALLOC_STACK r ksp hargs0 wnl off r1 n md (VL a) nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP (fun b H => H) ERR' PU' Fv Gv HF
                (Fv_of_15 _ _ _) st4 H4 (VL md :: aB :: VL nw :: rest) aB (getr st X10) BLK_LO BLK_HI stB' Ab nZ junk
                eq_refl HB SVn SVaB eq_refl (Fv_of_16 _ _ _) GJ CELLS B4096 AC' A16 ltac:(unfold RIMG_LO, RIMG_HI; lia)
                ltac:(change (w2Z BLK_LO) with 4096; change (w2Z BLK_HI) with (2 ^ 47 - 1); lia) NEW (fun b H => H) AWH Ha0) as [ST MP'].
    rewrite (cg_ra_r CG). exact (HKB _ _ _ (EXT E st Fv Gv) MP' ST).
Qed.

Theorem malloc1_sound : forall pc, to_Z pc = RMALLOC_SYM ->
  contract_sound rsegs OPS MP PB (CtrN.malloc1_c rsegs ERRNO LIBC GOT GUARD TP CANARY pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrN.malloc1_c] in Happ. unfold CtrN.malloc1_apply in Happ.
  destruct (malloc_apply rsegs ERRNO LIBC GOT GUARD TP CANARY st) as [[| stA [| stB [| stC l]]]|] eqn:MA; try discriminate.
  apply Some_inj in Happ. subst sts.
  apply (malloc_nofork pc st stA stB K E ms mo Hpc Hspc MA HS HMP HPB).
  intros E2 ms2 mo2 EXT2 MP2 ST2. exact (HK stB (or_introl eq_refl) E2 ms2 mo2 EXT2 MP2 ST2).
Qed.

Lemma block_bytes : forall s LB m p A old, RHEAP_core s LB m -> In (p, A, old) LB ->
  exists bs, bytes_at rsegs m A bs /\ Z.of_nat (length bs) = old.
Proof.
  intros s LB m p A old RC Hin.
  destruct (RHEAP_core_block_range s LB m _ RC Hin) as (B1 & B2 & B3 & B4 & B5). cbn [blk_addr blk_size fst snd] in B1, B2, B3, B4, B5.
  pose proof alloc_ceiling_lt64 as C64.
  exists (map (fun i => match m (wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 (Z.to_nat old))).
  unfold bytes_at. rewrite !length_map, !length_seq. split; [| lia]. split; [lia|]. split; [lia|].
  intros i Hi. rewrite nth_error_map, Stdlib.Lists.List.nth_error_seq.
  destruct (Nat.ltb i (Z.to_nat old)) eqn:LT; [| apply Nat.ltb_ge in LT; lia]. cbn [option_map Nat.add].
  unfold mrd. destruct (m (wa (A + Z.of_nat i))) as [b|] eqn:Hm; [reflexivity|]. exfalso. exact (B5 (A + Z.of_nat i) ltac:(lia) Hm).
Qed.

Theorem realloc_sound : forall pc, to_Z pc = RREALLOC_SYM ->
  contract_sound rsegs OPS MP PB (realloc_c rsegs ERRNO LIBC GOT GUARD TP CANARY pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply realloc_c] in Happ. unfold realloc_apply in Happ.
  destruct (alloc_call rsegs ERRNO LIBC GOT GUARD TP CANARY REALLOC_STACK st) as [[[[r ksp] hargs0] wnl]|] eqn:AC; [|discriminate].
  destruct (alloc_call_sound Cw OPS OPS_plain OPS_holds1 PB CANARY PB_canary PB_secret E st ms mo REALLOC_STACK r ksp hargs0 wnl HS HPB ltac:(vm_compute; reflexivity) AC)
    as (off & r1 & n & md & A & nw & rest & s & LBf & LB & CG).
  pose proof (cg_hargs CG) as EH. rewrite EH, heap_drop_A_eq in Happ.
  destruct (size_ok (s_facts st) (getr st X11)) eqn:SZ; [cbn [negb] in Happ| discriminate].
  pose proof (size_ok_sound E _ _ (so_facts _ _ _ _ _ _ HS) SZ) as NZ. set (nZ := bv_unsigned (den E (getr st X11))) in *.
  pose proof (cg_nw CG) as (T & N & L).
  assert (SVn : sv_vars_below (s_next st) (getr st X11) = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB.
    do 5 (apply andb_prop in SVB as [SVB ?]). exact (rf_allb_get _ _ _ SVB X11). }
  assert (AVB : forallb (sv_vars_below (s_next st)) rest = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB. apply andb_prop in SVB as [_ OV].
    pose proof (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) as AV. rewrite EH in AV. cbn [op_args forallb] in AV.
    apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. exact AV. }

  pose proof (cg_ms CG) as MSE. rewrite Hspc in MSE. cbn [c_pc realloc_c] in MSE. rewrite Hpc in MSE. rewrite MSE.
  pose proof (cg_stk CG) as STK. pose proof (cg_room CG) as ROOM. pose proof (cg_hi CG) as HI. pose proof (cg_ceil CG) as CE.
  pose proof (int_range REALLOC_STACK) as RAS. change (to_Z REALLOC_STACK) with 8256 in ROOM, RAS.
  destruct (stk_split rsegs (ms_mem ms) _ (bv_unsigned (ev E STACK_ID) + keyZ ksp) _ STK ltac:(lia)) as [STK1 _].
  destruct (cg_errno CG) as [errv ERR].
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 nZ).
  { subst nZ. rewrite <- reg_of_X11, (cg_regs CG X11). symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (cg_sp CG) as SP. pose proof alloc_ceiling_lt47 as C47.
  pose proof (cg_rheap CG) as RH. pose proof RH as RH0. apply RHEAP_split in RH0 as [RC _]. pose proof (RHEAP_core_nodup s LBf (ms_mem ms) RC) as NDid.
  pose proof (fresh_ok_inv st (cg_fresh CG)) as (_ & NXpos & NX256).
  assert (K16 : to_Z (s_next st) + to_Z 16%uint63 < wB) by (change (to_Z 16%uint63) with 16; rewrite wB_two63, two63_eq; lia).

  assert (DECN : forall Fv Gv, decode (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest)) = Some (w2Z md, wbv wones, wins_of E n rest, map (den E) (skipn (3 * n) rest))).
  { intros Fv Gv. rewrite (decode_hargs (E' E st Fv Gv) md (VL wones) nw rest n T N L), (wins_of_E' E st Fv Gv n rest AVB), den_VL. f_equal. f_equal.
    apply map_ext_in. intros u Hu. apply (den_E' E st Fv Gv). apply (forallb_In _ _ _ u AVB).
    rewrite <- (firstn_skipn (3 * n) rest). apply in_app_iff. right. exact Hu. }
  assert (FPN : forall Fv Gv a, Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest))) ->
                         Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E) hargs0))).
  { intros Fv Gv a X. rewrite OPS_fp1 in X |- *. unfold heap_fp in X |- *. rewrite DECN in X. rewrite (cg_decode CG). exact X. }

  assert (POSTN : forall st4 R' M' mo' s' errv',
            alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp = Some st4 ->
            In (setr (set_ops st4 (set_op HEAP_ID (VL md :: VL wones :: VL nw :: rest) (s_ops st4))) X10 (VL wzero)) sts ->
            gpost (ms_regs ms) (ms_mem ms) mo LBf (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + keyZ ksp) R' M' mo' ->
            PropExec.getr R' 10%bv = Z_to_bv 64 0 -> rw_cells rsegs M' RERRNO [C4 errv'] -> RHEAP s' LBf M' -> KREL s' LBf mo' ->
            realizes rsegs (mkCfg (MS R' (ms_fregs ms) (PropExec.getr (ms_regs ms) 1%bv) (ms_fcsr ms) None M' (seg_rom rsegs)) mo') K).
  { intros st4 R' M' mo' s' errv' H4 HIN GP Ha0 ERR' RH'. intros KR'. apply RHEAP_split in RH' as [RC' PU'].
    set (Fv := Fv_of R' errv' (Z_to_bv 64 0)). set (Gv := Gv_of []).
    assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
    assert (HH : St.op_holds OPS HEAP_ID (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest)) M' mo').
    { rewrite OPS_holds1. exists (w2Z md), (wbv wones), (wins_of E n rest), (map (den E) (skipn (3 * n) rest)), LB.
      split; [exact (DECN Fv Gv)|]. split; [| split; [exact (cg_wf CG)| exact (cw_post LBf LB _ _ _ _ _ _ (cg_perm CG) (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_cw CG))]].
      apply aw_holdsW_intro; [| exact (cg_ng CG)]. exists s', LBf. split; [exact (cg_perm CG)|]. split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
      split; [apply pclaim_none; rewrite wbv_unsigned; change (w2Z wones) with (2 ^ 64 - 1); lia|].
      exact (repl_post LBf _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG)). }
    destruct (post_N E st ms mo REALLOC_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP ERR' PU' Fv Gv HF
                (Fv_of_15 _ _ _) st4 H4 (VL wzero) (VL md :: VL wones :: VL nw :: rest) (fun b H => H)
                ltac:(rewrite den_VL, Ha0; reflexivity) HH (FPN Fv Gv)) as [ST MP'].
    rewrite (cg_ra_r CG). exact (HK _ HIN _ _ _ (EXT E st Fv Gv) MP' ST). }
  destruct (getr st X10) as [w|kf o| | | | | | | | |] eqn:HX10; try discriminate.
  -
    destruct (weqb w wzero) eqn:W0; [|discriminate]. apply weqb_eq in W0. subst w.
    unfold malloc_posts, malloc_posts_rg in Happ.
    destruct (alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp) as [st4|] eqn:H4; [|discriminate].
    cbn [block_posts] in Happ.
    destruct (block_post st4 (VL md :: VL wones :: VL nw :: rest) (getr st X11) (BLK_LO, BLK_HI)) as [stB|] eqn:HB; [|discriminate].
    apply Some_inj in Happ. subst sts.
    assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 0).
    { rewrite <- reg_of_X10, (cg_regs CG X10), HX10, den_VL. reflexivity. }
    apply (realloc_null_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo s LBf nZ
             (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + keyZ ksp) errv K
             A0 A1 ltac:(lia) (cg_tp CG) (cg_ra CG) RH (cg_krel CG) (cg_auxv CG) ltac:(rewrite SP; lia)
             ltac:(rewrite SP; exact STK1) CE ltac:(rewrite SP; unfold RREALLOC_STACK, RMALLOC_STACK; lia) ERR (cg_minv CG) (cg_mo CG)).
    +
      intros R' M' mo' s' errv' GP MPATH MTR Ha0 ERR' RH' KR'. exact (POSTN st4 R' M' mo' s' errv' eq_refl (or_introl eq_refl) GP Ha0 ERR' RH' KR').
    +
      intros R' M' mo' s' errv' p Ab junk GP MPATH MTR Ha0 ERR' RNG CELLS EXP RH' KR'. apply RHEAP_split in RH' as [RC' PU'].
      destruct RNG as (Apos & A16 & Nn & AC' & AI).
      set (Fv := Fv_of R' errv' (Z_to_bv 64 Ab)). set (Gv := Gv_of junk).
      assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
      destruct (RHEAP_core_block_range s' ((p, Ab, nZ) :: LBf) M' (p, Ab, nZ) RC' (or_introl eq_refl)) as (B4096 & _). cbn [blk_addr fst snd] in B4096.
      pose proof (RHEAP_core_nodup s' _ M' RC') as ND. cbn [map blk_id fst] in ND. apply List.NoDup_cons_iff in ND as [NI ND'].
      assert (NEW : forall b a, In b LB -> in_iv b a -> ~ (Ab <= a < Ab + nZ)).
      { intros b a Hb Hin R5.
        assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
        apply in_map_iff in Hb' as (blk & Eb & Hblk).
        assert (NEb : blk_id (p, Ab, nZ) <> blk_id blk).
        { cbn [blk_id fst]. intros X. apply NI. rewrite X. apply in_map_iff. exists blk. auto. }
        destruct (RHEAP_core_blocks_disjoint s' _ M' (p, Ab, nZ) blk RC' (or_introl eq_refl) (or_intror Hblk) NEb) as [D|D];
          unfold in_iv in Hin; rewrite <- Eb in Hin; unfold blk_addr, blk_size in D, Hin; cbn [fst snd] in D, Hin; lia. }
      assert (LJ : length junk = Z.to_nat nZ) by (destruct CELLS as [[[LJ _] _] _]; exact LJ).
      assert (GJ : forall o, 0 <= o < nZ -> nth_error junk (Z.to_nat o) = Some (Gv 16 o)).
      { intros o Ho. unfold Gv, Gv_of. apply nth_error_nth'. rewrite LJ. lia. }
      assert (AWH : aw_holdsI (den E (VL wones)) ((Ab, nZ) :: LB) M' mo').
      { exists s', ((p, Ab, nZ) :: LBf). split; [cbn [blocks_of map blk_addr blk_size fst snd]; apply perm_skip; exact (cg_perm CG)|].
        split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
        split; [apply pclaim_none; rewrite den_VL, wbv_unsigned; change (w2Z wones) with (2 ^ 64 - 1); lia|].
        exact (repl_post LBf _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG)). }
      destruct (post_B E st ms mo REALLOC_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP (fun b H => H) ERR' PU' Fv Gv HF
                  (Fv_of_15 _ _ _) st4 H4 (VL md :: VL wones :: VL nw :: rest) (VL wones) (getr st X11) BLK_LO BLK_HI stB Ab nZ junk
                  eq_refl HB SVn eq_refl eq_refl (Fv_of_16 _ _ _) GJ CELLS B4096 AC' A16 ltac:(unfold RIMG_LO, RIMG_HI; lia)
                  ltac:(change (w2Z BLK_LO) with 4096; change (w2Z BLK_HI) with (2 ^ 47 - 1); lia) NEW (fun b H => H) AWH Ha0) as [ST MP'].
      rewrite (cg_ra_r CG). exact (HK _ (or_intror (or_introl eq_refl)) _ _ _ (EXT E st Fv Gv) MP' ST).
  -
    destruct (negb (weqb o wzero) || PrimInt63.eqb kf 0 || PrimInt63.eqb kf STACK_ID) eqn:C; [discriminate|].
    apply orb_false_iff in C as [C K1]. apply orb_false_iff in C as [O0 K0]. apply negb_false_iff in O0. apply weqb_eq in O0. subst o.
    apply Uint63.eqb_false_spec in K0. apply Uint63.eqb_false_spec in K1.
    destruct (IMap.find kf (s_regs st)) as [rg|] eqn:Hkf; [|discriminate].
    destruct (free_ok st wnl kf) as [old|] eqn:FOK; [|discriminate].
    destruct (negb (sv_eqb (Mem.rg_hi rg) old) || negb (Mem.rg_w rg)) eqn:C2; [discriminate|].
    apply orb_false_iff in C2 as [HIo Wo].
    apply negb_false_iff in HIo. apply sv_eqb_eq in HIo. apply negb_false_iff in Wo.
    destruct (alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp) as [st4|] eqn:H4; [|discriminate].
    unfold heap_del_window in Happ.
    assert (NW' : heap_nwin (VL md :: VL wones :: VL nw :: rest) = Some n) by (pose proof (cg_nwin CG) as X; rewrite EH in X; exact X).
    rewrite NW' in Happ.
    destruct (del_window n (firstn (3 * n) rest) (VP kf wzero)) as [ws'|] eqn:DEL; [|discriminate].
    unfold fresh in Happ. cbn [fst snd] in Happ.

    assert (L3 : length (firstn (3 * n) rest) = (3 * n)%nat) by (apply firstn_length_le; exact L).
    assert (NWf : nonstack_windows n (firstn (3 * n) rest) = Some wnl) by (rewrite nonstack_windows_firstn; exact (cg_wnl CG)).
    destruct (free_ok_inv st wnl kf old FOK) as (rf & Hkf' & WLf & LOf & NEf & LEf & OTH). rewrite Hkf in Hkf'. injection Hkf' as <-.
    destruct (del_window_split E n (firstn (3 * n) rest) kf ws' wnl DEL NWf ltac:(lia)) as (l1 & len & l2 & INlen & WS & WS' & LEN & M1).
    rewrite <- (app_nil_r (firstn (3 * n) rest)), (wins_of_firstn E n rest []) in WS by exact L.
    destruct (windows_anchored_nodup _ _ _ _ _ _ _ (cg_anch CG) INlen (win_lookup_In _ _ _ _ WLf)) as [-> _].
    destruct (wsub_one_small nw T ltac:(lia)) as [T' EN'].
    assert (NW1 : heap_nwin (VL md :: VL wones :: VL (wsub nw wone) :: ws' ++ skipn (3 * n) rest) = Some (pred n)).
    { unfold heap_nwin. rewrite T', EN'. replace (Z.to_nat (to_Z (wl nw) - 1)) with (pred n) by lia.
      rewrite length_app. replace (Nat.leb (3 * pred n) (length ws' + length (skipn (3 * n) rest))) with true; [reflexivity|].
      symmetry. apply Nat.leb_le. lia. }
    rewrite (heap_add_window_eq md (VL wones) (wsub nw wone) (ws' ++ skipn (3 * n) rest) (pred n) _ _ _ NW1) in Happ.
    apply Some_inj in Happ. subst sts.
    destruct (alloc_post_inv st r ksp st4 r1 (cg_r1 CG) H4) as (r0 & Hr0 & E4).

    apply (known_ltu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS)) in NEf. rewrite unsigned_VL in NEf. change (w2Z wzero) with 0 in NEf. rewrite HIo in NEf.
    set (Af := bv_unsigned (ev E kf)). set (nf := bv_unsigned (den E old)) in *.
    destruct (nonstack_windows_In E n rest wnl kf old CtrLib.K_BLOCK (cg_wnl CG) (win_lookup_In _ _ _ _ WLf)) as (_ & _ & _ & INW).
    pose proof (proj1 (Forall_forall _ _) (cg_wf CG) _ INW) as (_ & _ & _ & [[KS _]|[[_ BLB]|[KS _]]]); cbn [w_kind w_lo w_len w_iv] in *;
      [exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_STACK in KS; lia| | exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS; unfold K_SUB in KS; lia].
    fold Af nf in BLB.
    assert (BLB' : In (Af, nf) (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact BLB]).
    apply in_map_iff in BLB' as ([[p A1'] n1] & Eb & INf). cbn [blk_addr blk_size fst snd] in Eb. injection Eb as -> ->.
    destruct (block_bytes s LBf (ms_mem ms) p Af nf RC INf) as (oldbs & OLDBS & OLDLEN).
    assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 Af).
    { rewrite <- reg_of_X10, (cg_regs CG X10), HX10, den_VPz. subst Af. symmetry. apply Z_to_bv_bv_unsigned. }
    fold Af nf in WS.
    pose proof (del_window_prov E n (firstn (3 * n) rest) kf ws' wnl NWf DEL (windows_anchored_nodup_anchors _ _ (cg_anch CG))) as PROV. rewrite WS' in PROV.
    assert (AVW : forallb (sv_vars_below (s_next st)) ws' = true).
    { apply forallb_forall. intros x Hx. apply (proj1 (forallb_forall _ _) AVB).
      pose proof (del_window_sub _ _ _ _ _ DEL Hx) as X. rewrite <- (firstn_skipn (3 * n) rest). apply in_app_iff. left. exact X. }
    apply (realloc_silent_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo s LBf p Af nf nZ
             (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + keyZ ksp) errv oldbs K
             A0 A1 ltac:(lia) INf OLDBS OLDLEN (cg_tp CG) (cg_ra CG) RH (cg_krel CG) (cg_auxv CG) ltac:(rewrite SP; lia)
             ltac:(rewrite SP; exact STK1) CE ltac:(rewrite SP; unfold RREALLOC_STACK, RMALLOC_STACK; lia) ERR (cg_minv CG) (cg_mo CG)).
    +
      intros R' M' mo' s' errv' GP MTR Ha0 ERR' RH' KR'. exact (POSTN st4 R' M' mo' s' errv' eq_refl (or_introl eq_refl) GP Ha0 ERR' RH' KR').
    +
      intros R' M' mo' s' errv' p' Ab junk GP MTR Ha0 ERR' RNG CELLS RH' KR'. pose proof RH' as RH1. apply RHEAP_split in RH1 as [RC' PU'].
      destruct RNG as (Apos & A16 & Nn & AC' & AI).
      set (bs := firstn (Z.to_nat (Z.min nf nZ)) oldbs ++ junk) in CELLS.
      set (Fv := Fv_of R' errv' (Z_to_bv 64 Ab)). set (Gv := Gv_of bs).
      assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
      destruct (RHEAP_core_block_range s' ((p', Ab, nZ) :: lb_remove p LBf) M' (p', Ab, nZ) RC' (or_introl eq_refl)) as (B4096 & _). cbn [blk_addr fst snd] in B4096.
      pose proof (RHEAP_core_nodup s' _ M' RC') as ND. cbn [map blk_id fst] in ND. apply List.NoDup_cons_iff in ND as [NI ND'].
      assert (NEW : forall blk a, In blk (lb_remove p LBf) -> blk_addr blk <= a < blk_addr blk + blk_size blk -> ~ (Ab <= a < Ab + nZ)).
      { intros blk a Hblk Hin R5.
        assert (NEb : blk_id (p', Ab, nZ) <> blk_id blk).
        { cbn [blk_id fst]. intros X. apply NI. rewrite X. apply in_map_iff. exists blk. auto. }
        destruct (RHEAP_core_blocks_disjoint s' _ M' (p', Ab, nZ) blk RC' (or_introl eq_refl) (or_intror Hblk) NEb) as [D|D];
          unfold blk_addr, blk_size in D, Hin; cbn [fst snd] in D, Hin; lia. }
      assert (LJ : length bs = Z.to_nat nZ) by (destruct CELLS as [[[LJ _] _] _]; exact LJ).
      assert (GJ : forall o, 0 <= o < nZ -> nth_error bs (Z.to_nat o) = Some (Gv 16 o)).
      { intros o Ho. unfold Gv, Gv_of. apply nth_error_nth'. rewrite LJ. lia. }

      pose proof (lb_remove_perm p Af nf LBf INf NDid) as PL.
      assert (NOTIN : ~ In (Af, nf) (blocks_of (lb_remove p LBf))).
      { intros X. apply in_map_iff in X as (blk & Eb & Hblk). apply In_lb_remove in Hblk as [Hblk NEp].
        assert (NEb : blk_id (p, Af, nf) <> blk_id blk) by (cbn [blk_id fst]; congruence).
        pose proof (f_equal fst Eb) as E1. pose proof (f_equal snd Eb) as E2. unfold blk_addr, blk_size in E1, E2. cbn [fst snd] in E1, E2.
        destruct (RHEAP_core_blocks_disjoint s LBf (ms_mem ms) (p, Af, nf) blk RC INf Hblk NEb) as [D|D]; unfold blk_addr, blk_size in D; cbn [fst snd] in D; lia. }
      assert (PERM' : Permutation (blocks_of (lb_remove p LBf)) (remove iv_eq_dec (Af, nf) LB)).
      { apply Permutation_sym. eapply Permutation_trans. { apply perm_remove. apply Permutation_sym. exact (cg_perm CG). }
        eapply Permutation_trans. { apply perm_remove. apply (Permutation_map (fun b => (blk_addr b, blk_size b))) in PL. exact PL. }
        cbn [map blk_addr blk_size fst snd remove]. destruct (iv_eq_dec (Af, nf) (Af, nf)); [| congruence].
        rewrite notin_remove by exact NOTIN. apply Permutation_refl. }
      assert (AWH : aw_holdsI (den E (VL wones)) ((Ab, nZ) :: remove iv_eq_dec (Af, nf) LB) M' mo').
      { exists s', ((p', Ab, nZ) :: lb_remove p LBf). split; [cbn [blocks_of map blk_addr blk_size fst snd]; apply perm_skip; exact PERM'|].
        split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
        split; [apply pclaim_none; rewrite den_VL, wbv_unsigned; change (w2Z wones) with (2 ^ 64 - 1); lia|].
        apply (repl_post (lb_remove p LBf) _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG)). }

      assert (NB : to_Z (wl (wsub nw wone)) + 1 < two63) by (rewrite EN'; pose proof (cg_n255 CG) as N255; rewrite N in N255; unfold two63; lia).
      assert (DEC' : decode (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL (wadd (wsub nw wone) wone)
                                 :: firstn (3 * pred n) (ws' ++ skipn (3 * n) rest) ++ [VP (PrimInt63.add (s_next st) 16%uint63) wzero; getr st X11; VL CtrLib.K_BLOCK]
                                    ++ skipn (3 * pred n) (ws' ++ skipn (3 * n) rest)))
                     = Some (w2Z md, den (E' E st Fv Gv) (VL wones), (l1 ++ l2) ++ [Win Ab nZ K_BLOCK], map (den E) (skipn (3 * n) rest))).
      { rewrite (decode_add_window (E' E st Fv Gv) md (VL wones) (wsub nw wone) (ws' ++ skipn (3 * n) rest) (pred n) _ _ _ T' ltac:(rewrite EN'; lia) ltac:(rewrite length_app; lia) NB).
        rewrite (wins_of_prefix _ (pred n) ws' _ ltac:(lia)), (wins_of_E' E st Fv Gv (pred n) ws' AVW), WS'.
        rewrite (skipn_app_exact ws' (skipn (3 * n) rest) (3 * pred n) ltac:(lia)).
        assert (EVK : ev (E' E st Fv Gv) (PrimInt63.add (s_next st) 16%uint63) = Z_to_bv 64 Ab).
        { unfold E'. rewrite (ev_above_lit E (s_next st) Fv Gv 16%uint63 K16). reflexivity. }
        rewrite den_VPz, EVK, Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64 in *; lia).
        rewrite (den_E' E st Fv Gv _ SVn), unsigned_VL. change (w2Z CtrLib.K_BLOCK) with K_BLOCK. fold nZ. f_equal. f_equal.
        apply map_ext_in. intros u Hu. apply (den_E' E st Fv Gv). apply (forallb_In _ _ _ u AVB).
        rewrite <- (firstn_skipn (3 * n) rest). apply in_app_iff. right. exact Hu. }
      destruct (post_FB E st ms mo REALLOC_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' (lb_remove p LBf) errv' GP
                  ltac:(intros b Hb; apply In_lb_remove in Hb; exact (proj1 Hb)) ERR' PU' Fv Gv HF (Fv_of_15 _ _ _) st4
                  r0 kf rg old p Af nf (VL wones) _ l1 l2 (getr st X11) BLK_LO BLK_HI Ab nZ bs _ Hr0 E4 Hkf K0 K1 FOK INf eq_refl eq_refl
                  ltac:(intros b Hb Nb; apply In_lb_remove; auto) ltac:(intros b Hb; apply In_lb_remove in Hb; exact (proj2 Hb))
                  WS PROV DEC' eq_refl SVn eq_refl (Fv_of_16 _ _ _) GJ CELLS B4096 AC' A16 ltac:(unfold RIMG_LO, RIMG_HI; lia)
                  ltac:(change (w2Z BLK_LO) with 4096; change (w2Z BLK_HI) with (2 ^ 47 - 1); lia) NEW AWH Ha0 eq_refl) as [ST MP'].
      rewrite (cg_ra_r CG). refine (HK _ (or_intror (or_introl eq_refl)) _ _ _ (EXT E st Fv Gv) MP' _).
      refine (st_ok_fields rsegs OPS _ _ _ _ _ _ _ _ _ _ _ _ _ ST); subst st4; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next setr set_ops setregs set_next addfact alloc_post_mk fst snd]; try reflexivity.
Qed.

Theorem aligned_alloc1_sound : forall pc, to_Z pc = RALIGNED16_SYM ->
  contract_sound rsegs OPS MP PB (CtrE.aligned_alloc1_c rsegs ERRNO LIBC GOT GUARD TP CANARY pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrE.aligned_alloc1_c] in Happ. unfold CtrE.aligned_alloc1_apply in Happ.
  destruct (alloc_call rsegs ERRNO LIBC GOT GUARD TP CANARY ALIGNED_STACK st) as [[[[r ksp] hargs0] wnl]|] eqn:AC; [|discriminate].
  destruct (getr st X10) as [al| | | | | | | | | |] eqn:HX10; try discriminate.
  destruct (alloc_call_sound Cw OPS OPS_plain OPS_holds1 PB CANARY PB_canary PB_secret E st ms mo ALIGNED_STACK r ksp hargs0 wnl HS HPB ltac:(vm_compute; reflexivity) AC)
    as (off & r1 & n & md & A & nw & rest & s & LBf & LB & CG).
  pose proof (cg_hargs CG) as EH. rewrite EH, heap_drop_A_eq in Happ.
  destruct (weqb al (wlit 16%uint63)) eqn:AL; [|discriminate]. apply weqb_eq in AL. subst al.
  destruct (size_ok (s_facts st) (getr st X11)) eqn:SZ; [|discriminate]. cbn [andb] in Happ.
  unfold malloc_posts, malloc_posts_rg in Happ.
  destruct (alloc_post ERRNO LIBC GOT GUARD CANARY st r ksp) as [st4|] eqn:H4; [|discriminate].
  cbn [block_posts] in Happ.
  destruct (block_post st4 (VL md :: VL wones :: VL nw :: rest) (getr st X11) (BLK_LO, BLK_HI)) as [stB|] eqn:HB; [|discriminate].
  apply Some_inj in Happ. subst sts.
  pose proof (size_ok_sound E _ _ (so_facts _ _ _ _ _ _ HS) SZ) as NZ. set (nZ := bv_unsigned (den E (getr st X11))) in *.
  pose proof (cg_nw CG) as (T & N & L).
  assert (SVn : sv_vars_below (s_next st) (getr st X11) = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB.
    do 5 (apply andb_prop in SVB as [SVB ?]). exact (rf_allb_get _ _ _ SVB X11). }
  assert (AVB : forallb (sv_vars_below (s_next st)) rest = true).
  { destruct (fresh_ok_inv st (cg_fresh CG)) as (SVB & _). unfold st_vars_below in SVB. apply andb_prop in SVB as [_ OV].
    pose proof (forallb_In _ _ _ _ OV (find_op_In _ _ _ (cg_find CG))) as AV. rewrite EH in AV. cbn [op_args forallb] in AV.
    apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. apply andb_prop in AV as [_ AV]. exact AV. }
  pose proof (cg_ms CG) as MSE. rewrite Hspc in MSE. cbn [c_pc CtrE.aligned_alloc1_c] in MSE. rewrite Hpc in MSE. rewrite MSE.
  pose proof (cg_stk CG) as STK. pose proof (cg_room CG) as ROOM. pose proof (cg_hi CG) as HI. pose proof (cg_ceil CG) as CE.
  pose proof (int_range ALIGNED_STACK) as RAS. change (to_Z ALIGNED_STACK) with 8224 in ROOM, RAS.
  destruct (stk_split rsegs (ms_mem ms) _ (bv_unsigned (ev E STACK_ID) + keyZ ksp) _ STK ltac:(lia)) as [STK1 _].
  destruct (cg_errno CG) as [errv ERR].
  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 16).
  { rewrite <- reg_of_X10, (cg_regs CG X10), HX10, den_VL. reflexivity. }
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 nZ).
  { subst nZ. rewrite <- reg_of_X11, (cg_regs CG X11). symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (cg_sp CG) as SP.
  apply (aligned16_silent_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo s LBf nZ
           (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + keyZ ksp) errv K
           A0 A1 ltac:(lia) (cg_tp CG) (cg_ra CG) (cg_rheap CG) (cg_krel CG) (cg_auxv CG) ltac:(rewrite SP; lia)
           ltac:(rewrite SP; exact STK1) CE ltac:(rewrite SP; unfold RALIGNED16_STACK, RMALLOC_STACK; lia) ERR (cg_minv CG) (cg_repl CG) (cg_mo CG)).
  -
    intros R' M' mo' s' errv' GP MPATH MTR Ha0 ERR' RH' KR'. apply RHEAP_split in RH' as [RC' PU'].
    set (Fv := Fv_of R' errv' (Z_to_bv 64 0)). set (Gv := Gv_of []).
    assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
    assert (DECN : decode (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest)) = Some (w2Z md, wbv wones, wins_of E n rest, map (den E) (skipn (3 * n) rest))).
    { rewrite (decode_hargs (E' E st Fv Gv) md (VL wones) nw rest n T N L), (wins_of_E' E st Fv Gv n rest AVB), den_VL. f_equal. f_equal.
      apply map_ext_in. intros u Hu. apply (den_E' E st Fv Gv). apply (forallb_In _ _ _ u AVB).
      rewrite <- (firstn_skipn (3 * n) rest). apply in_app_iff. right. exact Hu. }
    assert (HH : St.op_holds OPS HEAP_ID (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest)) M' mo').
    { rewrite OPS_holds1. exists (w2Z md), (wbv wones), (wins_of E n rest), (map (den E) (skipn (3 * n) rest)), LB.
      split; [exact DECN|]. split; [| split; [exact (cg_wf CG)| exact (cw_post LBf LB _ _ _ _ _ _ (cg_perm CG) (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_cw CG))]].
      apply aw_holdsW_intro; [| exact (cg_ng CG)]. exists s', LBf. split; [exact (cg_perm CG)|]. split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
      split; [apply pclaim_none; rewrite wbv_unsigned; change (w2Z wones) with (2 ^ 64 - 1); lia|].
      exact (repl_post LBf _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG)). }
    assert (FP : forall a, Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den (E' E st Fv Gv)) (VL md :: VL wones :: VL nw :: rest))) ->
                           Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS HEAP_ID (map (den E) hargs0))).
    { intros a X. rewrite OPS_fp1 in X |- *. unfold heap_fp in X |- *. rewrite DECN in X. rewrite (cg_decode CG). exact X. }
    destruct (post_N E st ms mo ALIGNED_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP ERR' PU' Fv Gv HF
                (Fv_of_15 _ _ _) st4 H4 (VL wzero) (VL md :: VL wones :: VL nw :: rest) (fun b H => H)
                ltac:(rewrite den_VL, Ha0; reflexivity) HH FP) as [ST MP'].
    rewrite (cg_ra_r CG). exact (HK _ (or_introl eq_refl) _ _ _ (EXT E st Fv Gv) MP' ST).
  -
    intros R' M' mo' s' errv' p Ab junk GP MPATH MTR Ha0 ERR' RNG CELLS EXP RH' KR'. apply RHEAP_split in RH' as [RC' PU'].
    destruct RNG as (Apos & A16 & Nn & AC' & AI).
    set (Fv := Fv_of R' errv' (Z_to_bv 64 Ab)). set (Gv := Gv_of junk).
    assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) by (intros; apply Fv_of_clob; assumption).
    destruct (RHEAP_core_block_range s' ((p, Ab, nZ) :: LBf) M' (p, Ab, nZ) RC' (or_introl eq_refl)) as (B4096 & _). cbn [blk_addr fst snd] in B4096.
    pose proof (RHEAP_core_nodup s' _ M' RC') as ND. cbn [map blk_id fst] in ND. apply List.NoDup_cons_iff in ND as [NI ND'].
    assert (NEW : forall b a, In b LB -> in_iv b a -> ~ (Ab <= a < Ab + nZ)).
    { intros b a Hb Hin R5.
      assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact (cg_perm CG)| exact Hb]).
      apply in_map_iff in Hb' as (blk & Eb & Hblk).
      assert (NEb : blk_id (p, Ab, nZ) <> blk_id blk).
      { cbn [blk_id fst]. intros X. apply NI. rewrite X. apply in_map_iff. exists blk. auto. }
      destruct (RHEAP_core_blocks_disjoint s' _ M' (p, Ab, nZ) blk RC' (or_introl eq_refl) (or_intror Hblk) NEb) as [D|D];
        unfold in_iv in Hin; rewrite <- Eb in Hin; unfold blk_addr, blk_size in D, Hin; cbn [fst snd] in D, Hin; lia. }
    assert (LJ : length junk = Z.to_nat nZ) by (destruct CELLS as [[[LJ _] _] _]; exact LJ).
    assert (GJ : forall o, 0 <= o < nZ -> nth_error junk (Z.to_nat o) = Some (Gv 16 o)).
    { intros o Ho. unfold Gv, Gv_of. apply nth_error_nth'. rewrite LJ. lia. }
    assert (AWH : aw_holdsI (den E (VL wones)) ((Ab, nZ) :: LB) M' mo').
    { exists s', ((p, Ab, nZ) :: LBf). split; [cbn [blocks_of map blk_addr blk_size fst snd]; apply perm_skip; exact (cg_perm CG)|].
      split; [exact RC'|]. split; [exact KR'|]. split; [exact (mo_ok_materialized _ (gp_mo _ _ _ _ _ _ _ _ _ GP))|].
      split; [apply pclaim_none; rewrite den_VL, wbv_unsigned; change (w2Z wones) with (2 ^ 64 - 1); lia|].
      exact (repl_post LBf _ _ _ (gp_pres _ _ _ _ _ _ _ _ _ GP) (cg_repl CG)). }
    pose proof alloc_ceiling_lt47 as C47.
    destruct (post_B E st ms mo ALIGNED_STACK r ksp hargs0 wnl off r1 n md A nw rest s LBf LB HS HPB HMP CG R' M' mo' LBf errv' GP (fun b H => H) ERR' PU' Fv Gv HF
                (Fv_of_15 _ _ _) st4 H4 (VL md :: VL wones :: VL nw :: rest) (VL wones) (getr st X11) BLK_LO BLK_HI stB Ab nZ junk
                eq_refl HB SVn eq_refl eq_refl (Fv_of_16 _ _ _) GJ CELLS B4096 AC' A16 ltac:(unfold RIMG_LO, RIMG_HI in *; lia)
                ltac:(change (w2Z BLK_LO) with 4096; change (w2Z BLK_HI) with (2 ^ 47 - 1); lia) NEW (fun b H => H) AWH Ha0) as [ST MP'].
    rewrite (cg_ra_r CG). exact (HK _ (or_intror (or_introl eq_refl)) _ _ _ (EXT E st Fv Gv) MP' ST).
Qed.

Lemma has_block_window_sound : forall E fs k n rest, facts_hold E fs ->
  CtrE.has_block_window fs k n rest = true ->
  exists w, In w (wins_of E n rest) /\ w_lo w = bv_unsigned (ev E k) /\ 0 < w_len w /\ w_kind w = K_BLOCK.
Proof.
  intros E fs k n. induction n as [|n IH]; intros rest FH H; [discriminate H|].
  destruct rest as [|lo [|len [|kd rest']]]; try discriminate H.
  cbn [CtrE.has_block_window] in H. apply orb_prop in H as [H|H].
  - destruct lo as [|k' o| | | | | | | | |]; try discriminate H. destruct kd as [kw| | | | | | | | | |]; try discriminate H.
    apply andb_prop in H as [H LT]. apply andb_prop in H as [H KB]. apply andb_prop in H as [KE O].
    apply Uint63.eqb_correct in KE. subst k'. apply weqb_eq in O. subst o. apply weqb_eq in KB. subst kw.
    pose proof (known_ltu_sound E fs _ _ FH LT) as LT'. rewrite den_VL in LT'.
    eexists. split; [rewrite wins_of_cons; left; reflexivity|]. cbn [w_lo w_len w_kind].
    split; [rewrite den_VPz; reflexivity|]. split; [change (bv_unsigned (wbv wzero)) with 0 in LT'; exact LT'|].
    rewrite den_VL. reflexivity.
  - destruct (IH rest' FH H) as (w & IN & P). exists w. split; [rewrite wins_of_cons; right; exact IN| exact P].
Qed.

Theorem blk_side_sound : forall IMG_HI pc, to_Z IMG_HI = RIMG_HI ->
  contract_sound rsegs OPS MP PB (CtrE.blk_side_c IMG_HI pc).
Proof.
  intros IMG_HI pc HIMG st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrE.blk_side_c] in Happ. unfold CtrE.blk_side_apply in Happ.
  destruct (getr st X10) as [|k o| | | | | | | | |] eqn:HX10; try discriminate.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|] eqn:Hf; [|discriminate].
  destruct (heap_nwin hargs) as [n|] eqn:Hn; [|discriminate].
  destruct (heap_nwin_shape hargs n Hn) as (md & A & nw & rest & Eh & T & N & L). subst hargs.
  destruct (weqb o wzero && CtrE.has_block_window (s_facts st) k n rest) eqn:C; [|discriminate].
  apply andb_prop in C as [_ W]. apply Some_inj in Happ. subst sts.
  pose proof (ops_hold_find OPS E (s_ops st) (ms_mem ms) mo HEAP_ID _ (so_ops _ _ _ _ _ _ HS) Hf) as HH.
  rewrite OPS_holds1 in HH. destruct HH as (md' & aw & ws & ca & LB & D & HA & WF & HC).
  rewrite (decode_hargs E md A nw rest n T N L) in D. injection D as <- <- <- <-.
  destruct HA as ((s & LBf & P & RC & KR & MT & CL & RP) & _).
  destruct (has_block_window_sound E (s_facts st) k n rest (so_facts _ _ _ _ _ _ HS) W) as (w & INw & WLO & WLEN & WK).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & [[KS _]|[[_ INB]|[KS _]]]);
    [rewrite WK in KS; unfold K_BLOCK, K_STACK in KS; lia| | rewrite WK in KS; unfold K_SUB, K_BLOCK in KS; lia].
  assert (INB' : In (w_iv w) (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact P| exact INB]).
  apply in_map_iff in INB' as (blk & Eb & Hblk).
  destruct (RHEAP_core_block_range s LBf (ms_mem ms) blk RC Hblk) as (B4096 & _ & BC & BI & _).
  assert (EA : blk_addr blk = bv_unsigned (ev E k)) by (rewrite <- WLO; unfold w_iv in Eb; injection Eb as E1 E2; exact E1).
  assert (EN : blk_size blk = w_len w) by (unfold w_iv in Eb; injection Eb as E1 E2; exact E2).
  rewrite EA in B4096, BC, BI. rewrite EN in BC, BI.
  pose proof alloc_ceiling_lt47 as C47.
  destruct BI as [LOW|HIGH].
  - refine (HK _ (or_introl eq_refl) E ms mo (env_ext_refl (s_next st) E) HMP _).
    apply addfact_sound; [exact HS|]. cbn [fact_holds].
    change (w2Z BLK_LO) with 4096. change (w2Z (wsub IMG_LO wone)) with 65535. unfold RIMG_LO in LOW. lia.
  - refine (HK _ (or_intror (or_introl eq_refl)) E ms mo (env_ext_refl (s_next st) E) HMP _).
    apply addfact_sound; [exact HS|]. cbn [fact_holds].
    rewrite wlit_ok, HIMG. change (w2Z BLK_HI) with (2 ^ 47 - 1). lia.
Qed.

End CEIL.
End TwinB.
