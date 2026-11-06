From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Export MemNorm.
Import ListNotations.
Local Open Scope Z_scope.

Section RF.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition relay_post (K : Z) (E : Z -> Prop) (F : Z -> Prop)
    (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ layout_le A L L' /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ~ F (ptr_addr L p) ->
     ptr_addr L' p = ptr_addr L p) /\
  (forall p n, In (p, n) (user_blocks A) -> 0 < n -> ~ F (ptr_addr L p) -> In (p, n) (user_blocks A')) /\
  (forall p, In (p, 0) (user_blocks A) -> In (p, 0) (user_blocks A') /\ ptr_addr L' p = ptr_addr L p) /\
  (forall a, in_img Bm a -> owned Bm L' A' a -> owned Bm L A a) /\
  regs_preserved regs regs' /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img Bm a) ->
     ~ owned Bm L A a -> ~ owned Bm L' A' a -> ~ scratch_k Bm K regs a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ~ F (ptr_addr L p) -> 0 <= i < n ->
     ~ E (ptr_addr L p + i) ->
     mbyte segs mem' (ptr_addr L p + i) = mbyte segs mem (ptr_addr L p + i)) /\
  (forall a, scratch_k Bm K regs a -> writable_at segs mem' a).

Definition img_plain (a : Z) : Prop :=
  in_img Bm a /\ ~ static_owned Bm a /\ ~ (ms_ctx Bm <= a < ms_ctx Bm + CTX_SIZE) /\
  ~ (errno_addr Bm <= a < errno_addr Bm + 4).

Lemma blocks_disjoint : forall L A mem md p n q k,
    MR L A mem md -> In (p, n) (blocks L A) -> In (q, k) (blocks L A) -> p <> q ->
    p + n <= q \/ q + k <= p.
Proof.
  intros L A mem md p n q k HM Hp Hq Hne.
  pose proof (mr_blocks_disjoint Bm MR (aa_laws API) L A mem md HM) as HD.
  assert (Hpq : (p, n) <> (q, k)) by congruence.
  destruct (YI04.pairwise_in2 _ _ _ _ HD Hp Hq Hpq) as [H|H]; unfold ranges_disjoint in H; simpl in H; lia.
Qed.

End RF.
