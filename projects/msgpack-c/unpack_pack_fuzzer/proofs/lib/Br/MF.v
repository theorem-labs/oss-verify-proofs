(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (room_init, in both copies, takes the kernel build and reads the start ledger as the model's init_reserved: the image's reservations followed by the vvar/vDSO pair, whose two entries are measured by the size and count bounds; the image's reservations' size and count bounds as the lemmas rsegs_sizes and rsegs_len). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem ITree Nodes NodesM Decode DecodeM.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad MSafe Prog KLink KStep A_MallocBlocks.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import F_syscalls.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue NodeSound TreeBridgeN KRel MPath Room Grant MMeas.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition s0 : PState := ps_init (reservedZ rsegs).

Definition BUF0 : Z := 65536.
Definition bufsz (k : nat) : Z := BUF0 * 2 ^ (Z.of_nat k).

Inductive histR : nat -> PState -> bptr -> Prop :=
| histR_O : forall p s1,
    mtr_malloc s0 BUF0 (Some p) s1 ->
    histR O s1 p
| histR_S : forall k s p p' s1 s2,
    histR k s p ->
    mtr_malloc s (bufsz (S k)) (Some p') s1 ->
    mtr_free s1 p s2 ->
    histR (S k) s2 p'.

Lemma room_step : forall mo mo' j (k : nat) E,
  room mo j -> 0 <= j -> msteps k E mo mo' -> (k <= 64)%nat -> E <= (2 ^ 26 + 2 ^ 20) -> room mo' (j + 1).
Proof.
  intros mo mo' j k E [A B C D] Hj [M1 M2 M3 M4] Hk HE. constructor.
  - apply M3; [| unfold PGSZ; lia | exact A]. lia.
  - lia.
  - nia.
  - rewrite M4. exact D.
Qed.

Lemma forallb_sizes : forall (l : list (word * word)) B,
  forallb (fun z => z <=? B) (map (fun p => bv_unsigned (snd p)) l) = true -> sizes_le B l.
Proof.
  intros l B H. unfold sizes_le. induction l as [|p l IH]; [constructor|]. cbn [map forallb] in H.
  apply andb_prop in H as [H1 H2]. constructor; [apply Z.leb_le; exact H1 | apply IH; exact H2].
Qed.

(* the image's own reservations, as separate lemmas: computed once, closed (written inside room_init's
   proof as a tactic-in-term and an asserted vm_compute, the step grew without bound) *)
Lemma rsegs_sizes : sizes_le (2 ^ 30) (segments_reserved rsegs).
Proof. apply forallb_sizes. vm_compute. reflexivity. Qed.
Lemma rsegs_len : (length (segments_reserved rsegs) <= 98)%nat.
Proof. vm_compute. lia. Qed.

(* The launch seeds [vm_reserved] with [State.init_reserved]: the image's
   reservations AND the vdso/vvar pair.  [room]'s size and count bounds read
   [vmaps = vm_reserved ++ vm_maps], so the pair has to be measured; [rm_live]
   reads [vm_maps] alone and is untouched. *)
Lemma room_init : forall mo kb brk lim mbase sp,
  m_vmmaps mo = mkVmMapsFull (init_reserved (segments_reserved rsegs) mbase sp kb) [] [] brk brk lim mbase sp ->
  2 ^ 31 <= lim -> room mo 0.
Proof.
  intros mo kb brk lim mbase sp E Hlim.
  pose proof (vdso_text_pages_pos kb). pose proof (vdso_text_pages_le kb).
  assert (HV : forall top, sizes_le (2 ^ 30) (vdso_reserved kb top)
                           /\ (length (vdso_reserved kb top) <= 2)%nat).
  { intros top. unfold sizes_le, vdso_reserved. cbv zeta.
    destruct ((top - vdso_len kb) <? page_size)%Z; cbn [length].
    - split; [apply Forall_nil | lia].
    - split; [| lia].
      repeat (apply Forall_cons;
        [cbn [snd]; rewrite bv_unsigned_Z_to_bv_u64
           by (unfold vdso_vvar_pages, page_size, two_pow_64; lia);
         unfold vdso_vvar_pages, page_size; lia |]).
      apply Forall_nil. }
  constructor; unfold vmaps; rewrite E; cbn [vm_reserved vm_maps vm_limit vm_live_bytes live_bytes]; rewrite ?app_nil_r.
  - unfold init_reserved, sizes_le. apply Forall_forall. intros p Hp.
    apply in_app_or in Hp as [Hp|Hp].
    + exact (proj1 (Forall_forall _ _) rsegs_sizes p Hp).
    + exact (proj1 (Forall_forall _ _) (proj1 (HV _)) p Hp).
  - unfold init_reserved. rewrite length_app.
    pose proof rsegs_len. pose proof (proj2 (HV (page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size))))). lia.
  - lia.
  - exact Hlim.
Qed.

Definition MF_A_succ_stmt : Prop :=
  forall mo, KREL s0 [] mo -> mo_ok mo -> room mo 0 -> malloc_can_succeed s0 mo BUF0.
Definition MF_B_succ_stmt : Prop :=
  forall k s p A mo j, histR k s p -> KREL s [(p, A, bufsz k)] mo -> mo_ok mo -> (k < 10)%nat ->
  room mo j -> 0 <= j <= 27 -> malloc_can_succeed s mo (bufsz (S k)).
Definition MF_C_succ_stmt : Prop :=
  forall k s p A mo n j, histR k s p -> KREL s [(p, A, bufsz k)] mo -> mo_ok mo -> (k <= 10)%nat ->
  0 < n < 2 ^ 26 -> room mo j -> 0 <= j <= 27 -> malloc_can_succeed s mo n.

Definition MF_A_must_stmt : Prop :=
  forall mo, KREL s0 [] mo -> mo_ok mo -> room mo 0 -> malloc_must_succeed s0 mo BUF0.
Definition MF_B_must_stmt : Prop :=
  forall k s p A mo j, histR k s p -> KREL s [(p, A, bufsz k)] mo -> mo_ok mo -> (k < 10)%nat ->
  room mo j -> 0 <= j <= 27 -> malloc_must_succeed s mo (bufsz (S k)).
Definition MF_C_must_stmt : Prop :=
  forall k s p A mo n j, histR k s p -> KREL s [(p, A, bufsz k)] mo -> mo_ok mo -> (k <= 10)%nat ->
  0 < n < 2 ^ 26 -> room mo j -> 0 <= j <= 27 -> malloc_must_succeed s mo n.

Definition MF3_A_stmt : Prop :=
  forall mo j r s' mo', KREL s0 [] mo -> mo_ok mo -> room mo j -> 0 <= j ->
  mpath (raw_malloc BUF0) s0 mo r s' mo' -> room mo' (j + 1).
Definition MF3_B_stmt : Prop :=
  forall k s p A mo j r s' mo', histR k s p -> KREL s [(p, A, bufsz k)] mo -> mo_ok mo -> (k < 10)%nat -> room mo j -> 0 <= j ->
  mpath (raw_malloc (bufsz (S k))) s mo r s' mo' -> room mo' (j + 1).
Definition MF3_F_stmt : Prop :=
  forall k s p A p' A' s1 mo1 j s2 mo2 LB,
  histR k s p -> mtr_malloc s (bufsz (S k)) (Some p') s1 ->
  KREL s1 LB mo1 -> In (p, A, bufsz k) LB -> In (p', A', bufsz (S k)) LB -> mo_ok mo1 -> room mo1 j -> 0 <= j ->
  mpath (raw_free p) s1 mo1 tt s2 mo2 -> room mo2 (j + 1).
Definition MF3_C_stmt : Prop :=
  forall k s p A mo n j r s' mo', histR k s p -> KREL s [(p, A, bufsz k)] mo -> mo_ok mo -> (k <= 10)%nat ->
  0 < n < 2 ^ 26 -> room mo j -> 0 <= j -> mpath (raw_malloc n) s mo r s' mo' -> room mo' (j + 1).

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.NodesM OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.DecodeM.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Prelim OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.KInv.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.MSafe OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KLink OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocBlocks.
Import F_syscalls.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.StateGlue OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.NodeSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.TreeBridgeN OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.KRel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MPath OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.Room OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.Grant OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MMeas.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition s0 : PState := ps_init (reservedZ rsegs).

Definition BUF0 : Z := 65536.
Definition bufsz (k : nat) : Z := BUF0 * 2 ^ (Z.of_nat k).

Inductive histR : nat -> PState -> bptr -> Prop :=
| histR_O : forall p s1,
    mtr_malloc s0 BUF0 (Some p) s1 ->
    histR O s1 p
| histR_S : forall k s p p' s1 s2,
    histR k s p ->
    mtr_malloc s (bufsz (S k)) (Some p') s1 ->
    mtr_free s1 p s2 ->
    histR (S k) s2 p'.

Lemma room_step : forall mo mo' j (k : nat) E,
  room mo j -> 0 <= j -> msteps k E mo mo' -> (k <= 64)%nat -> E <= (2 ^ 26 + 2 ^ 20) -> room mo' (j + 1).
Proof.
  intros mo mo' j k E [A B C D] Hj [M1 M2 M3 M4] Hk HE. constructor.
  - apply M3; [| unfold PGSZ; lia | exact A]. lia.
  - lia.
  - nia.
  - rewrite M4. exact D.
Qed.

Lemma forallb_sizes : forall (l : list (word * word)) B,
  forallb (fun z => z <=? B) (map (fun p => bv_unsigned (snd p)) l) = true -> sizes_le B l.
Proof.
  intros l B H. unfold sizes_le. induction l as [|p l IH]; [constructor|]. cbn [map forallb] in H.
  apply andb_prop in H as [H1 H2]. constructor; [apply Z.leb_le; exact H1 | apply IH; exact H2].
Qed.

(* the image's own reservations, as separate lemmas: computed once, closed (written inside room_init's
   proof as a tactic-in-term and an asserted vm_compute, the step grew without bound) *)
Lemma rsegs_sizes : sizes_le (2 ^ 30) (segments_reserved rsegs).
Proof. apply forallb_sizes. vm_compute. reflexivity. Qed.
Lemma rsegs_len : (length (segments_reserved rsegs) <= 98)%nat.
Proof. vm_compute. lia. Qed.

(* twin of the module above; kept byte-identical in shape *)
Lemma room_init : forall mo kb brk lim mbase sp,
  m_vmmaps mo = mkVmMapsFull (init_reserved (segments_reserved rsegs) mbase sp kb) [] [] brk brk lim mbase sp ->
  2 ^ 31 <= lim -> room mo 0.
Proof.
  intros mo kb brk lim mbase sp E Hlim.
  pose proof (vdso_text_pages_pos kb). pose proof (vdso_text_pages_le kb).
  assert (HV : forall top, sizes_le (2 ^ 30) (vdso_reserved kb top)
                           /\ (length (vdso_reserved kb top) <= 2)%nat).
  { intros top. unfold sizes_le, vdso_reserved. cbv zeta.
    destruct ((top - vdso_len kb) <? page_size)%Z; cbn [length].
    - split; [apply Forall_nil | lia].
    - split; [| lia].
      repeat (apply Forall_cons;
        [cbn [snd]; rewrite bv_unsigned_Z_to_bv_u64
           by (unfold vdso_vvar_pages, page_size, two_pow_64; lia);
         unfold vdso_vvar_pages, page_size; lia |]).
      apply Forall_nil. }
  constructor; unfold vmaps; rewrite E; cbn [vm_reserved vm_maps vm_limit vm_live_bytes live_bytes]; rewrite ?app_nil_r.
  - unfold init_reserved, sizes_le. apply Forall_forall. intros p Hp.
    apply in_app_or in Hp as [Hp|Hp].
    + exact (proj1 (Forall_forall _ _) rsegs_sizes p Hp).
    + exact (proj1 (Forall_forall _ _) (proj1 (HV _)) p Hp).
  - unfold init_reserved. rewrite length_app.
    pose proof rsegs_len. pose proof (proj2 (HV (page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size))))). lia.
  - lia.
  - exact Hlim.
Qed.

Definition MF_A_succ_stmt : Prop :=
  forall mo, KREL s0 [] mo -> mo_ok mo -> room mo 0 -> malloc_can_succeed s0 mo BUF0.
Definition MF_B_succ_stmt : Prop :=
  forall k s p A mo j, histR k s p -> KREL s [(p, A, bufsz k)] mo -> mo_ok mo -> (k < 10)%nat ->
  room mo j -> 0 <= j <= 27 -> malloc_can_succeed s mo (bufsz (S k)).
Definition MF_C_succ_stmt : Prop :=
  forall k s p A mo n j, histR k s p -> KREL s [(p, A, bufsz k)] mo -> mo_ok mo -> (k <= 10)%nat ->
  0 < n < 2 ^ 26 -> room mo j -> 0 <= j <= 27 -> malloc_can_succeed s mo n.

Definition MF_A_must_stmt : Prop :=
  forall mo, KREL s0 [] mo -> mo_ok mo -> room mo 0 -> malloc_must_succeed s0 mo BUF0.
Definition MF_B_must_stmt : Prop :=
  forall k s p A mo j, histR k s p -> KREL s [(p, A, bufsz k)] mo -> mo_ok mo -> (k < 10)%nat ->
  room mo j -> 0 <= j <= 27 -> malloc_must_succeed s mo (bufsz (S k)).
Definition MF_C_must_stmt : Prop :=
  forall k s p A mo n j, histR k s p -> KREL s [(p, A, bufsz k)] mo -> mo_ok mo -> (k <= 10)%nat ->
  0 < n < 2 ^ 26 -> room mo j -> 0 <= j <= 27 -> malloc_must_succeed s mo n.

Definition MF3_A_stmt : Prop :=
  forall mo j r s' mo', KREL s0 [] mo -> mo_ok mo -> room mo j -> 0 <= j ->
  mpath (raw_malloc BUF0) s0 mo r s' mo' -> room mo' (j + 1).
Definition MF3_B_stmt : Prop :=
  forall k s p A mo j r s' mo', histR k s p -> KREL s [(p, A, bufsz k)] mo -> mo_ok mo -> (k < 10)%nat -> room mo j -> 0 <= j ->
  mpath (raw_malloc (bufsz (S k))) s mo r s' mo' -> room mo' (j + 1).
Definition MF3_F_stmt : Prop :=
  forall k s p A p' A' s1 mo1 j s2 mo2 LB,
  histR k s p -> mtr_malloc s (bufsz (S k)) (Some p') s1 ->
  KREL s1 LB mo1 -> In (p, A, bufsz k) LB -> In (p', A', bufsz (S k)) LB -> mo_ok mo1 -> room mo1 j -> 0 <= j ->
  mpath (raw_free p) s1 mo1 tt s2 mo2 -> room mo2 (j + 1).
Definition MF3_C_stmt : Prop :=
  forall k s p A mo n j r s' mo', histR k s p -> KREL s [(p, A, bufsz k)] mo -> mo_ok mo -> (k <= 10)%nat ->
  0 < n < 2 ^ 26 -> room mo j -> 0 <= j -> mpath (raw_malloc n) s mo r s' mo' -> room mo' (j + 1).

End CEIL.
End TwinB.
