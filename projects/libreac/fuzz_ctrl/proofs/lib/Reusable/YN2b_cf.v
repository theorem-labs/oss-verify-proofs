(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN2b.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0s YK0h YK0i YK15 YM06 YM02 YP09 YK0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0g YO0x YO0u YO0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN03 YN31.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN2b YM06_cf YO0d_cf YM01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mreal_cf_itok {R} : forall segs (t : itree astate R) c (P : R -> config -> Prop) (Q : R -> Prop),
mreal_cf segs c t P -> itok t Q -> mreal_cf segs c t (fun r c' => P r c' /\ Q r).
Proof.
intros segs t. induction t as [r | q s k IH | f]; intros c P Q HM HT; cbn in *.
- eapply SR_cfv_mono; [exact HM|]. intros c' HP. split; [exact HP | exact HT].
- destruct HT as [_ HT]. eapply SR_cfv_mono; [exact HM|]. intros c1 [Hk Hx]. split; [| exact Hx].
destruct q;
try (destruct Hk as (J & nx & bit & j0 & Hn & Hc & Hcl); exists J, nx, bit, j0;
split; [exact Hn|]; split; [| exact Hcl]; intros j; apply IH; [apply Hc | apply HT; exact I]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. apply IH; [exact Hc | apply HT; exact Hz].
- exact I.
Qed.
Section o.
Variable B : malloc_syms.
Let segs := ms_segs B.
Definition alloc_meta_hyp_cf : Prop :=
forall X R U L A regs mem md,
Inv X R U A ->
(forall x am, In x X -> MT A x <> Some (MUsed am)) ->
ama_ok A -> bounded A ->
midrep B L A mem md ->
(st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem) ->
callee_pre B regs mem AM_STACK ->
mreal_cf segs (mkCfg (mkst regs (Z_to_bv 64 (pc_alloc_meta (ms_pcs B))) mem (seg_rom segs)) md)
(alloc_meta A)
(fun r c' => exists L' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
callee_post B L A regs mem md AM_STACK L' (snd r) regs' mem' md' /\ ama_ok (snd r) /\ bounded (snd r) /\
getr regs' 10 = Z_to_bv 64 (match fst r with None => 0 | Some m => ptr_addr L' m end) /\
(match fst r with Some m => ptr_addr L' m <> 0 | None => True end)).
Definition alloc_slot_hyp_cf : Prop :=
forall L A regs mem md sc n,
Inv [] None U0 A -> ama_ok A -> bounded A -> rsv_ok A -> span_ok A -> 0 <= sc < 48 -> 0 <= n < MMAP_THRESHOLD -> n + IB <= class_size sc ->
midrep B L A mem md ->
(st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem) ->
callee_pre B regs mem AS_STACK ->
getr regs 10 = Z_to_bv 64 sc -> getr regs 11 = Z_to_bv 64 n ->
mreal_cf segs (mkCfg (mkst regs (Z_to_bv 64 (pc_alloc_slot (ms_pcs B))) mem (seg_rom segs)) md)
(alloc_slot NEST_FUEL sc n A)
(fun r c' => exists L' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
midrep B L' (snd r) mem' md' /\ ama_ok (snd r) /\ bounded (snd r) /\ rsv_ok (snd r) /\ span_ok (snd r) /\ layout_le A L L' /\
regs_preserved regs regs' /\
(exists vm', md' = with_vmmaps vm' md) /\
(forall x, 0 <= x < 2 ^ 64 ->
~ owned B L A x -> ~ owned B L' (snd r) x -> ~ in_nonmap_region L' (snd r) x ->
~ call_scratch B (spZ regs) AS_STACK x ->
mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) /\
(forall a, call_scratch B (spZ regs) AS_STACK a -> writable_at segs mem' a) /\
getr regs' 10 = Z_to_bv 64 (fst r) /\
(0 <= fst r -> forall g am, active_hd (snd r) sc = Some g -> MT (snd r) g = Some (MUsed am) ->
stride_of am < class_size sc ->
forall i, 0 <= i < stride_of am - IB ->
mbyte segs mem' (ptr_addr L' (slot_start am (fst r)) + i) = Some (Z_to_bv 8 0))).
Definition malloc_small_hyp_cf : Prop :=
forall L A regs mem md n,
call_pre B (MRx B) L A regs mem md ->
getr regs 10 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD ->
mreal_cf segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
(malloc n A)
(malloc_leaf B (MRx B) L A regs mem md n).

(* The ledger counts the policy's window count needs at a placement request of the walk (YN02_cf.knode_cf_mmap_rw,
   knode_cf_mmap_none): the image's reserved segments (at most 8 of at most 2^30 bytes) and one map per slot. *)
Lemma node_ledger_of : forall L A md, ledger_ok B L A md -> ledger_x L A md ->
  (length (segments_reserved (ms_segs B)) <= 8)%nat -> ivs_bytes (segments_reserved (ms_segs B)) <= 2 ^ 30 ->
  Z.of_nat (length (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md))) <= nslots A + KRES /\
  ivs_bytes (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) <= live_bytes A + 2 ^ 30 /\
  140735332483072 <= alloc_top (m_vmmaps md).
Proof.
intros L A md G LX RL RB. split; [|split].
- rewrite length_app, (lg_reserved _ _ _ _ G). pose proof (lg_count _ _ _ _ G). unfold KRES. lia.
- rewrite ivs_bytes_app, (lg_reserved _ _ _ _ G), (ivs_bytes_live_bytes (vm_maps (m_vmmaps md))).
  pose proof (lx_lb _ _ _ LX). lia.
- pose proof (YM05.ceil_le_top _ (lg_ceil _ _ _ _ G)). pose proof (proj1 alloc_ceiling_value). lia.
Qed.
End o.
End d.
