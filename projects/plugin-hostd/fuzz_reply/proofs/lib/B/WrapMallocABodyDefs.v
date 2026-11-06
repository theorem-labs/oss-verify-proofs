(* CARRIED BY PATH from commit 9e87119fcf60, proofs/omx-clap-core/fuzz_preset/lib/A/WrapMallocABodyDefs.v, sha256 b67b4cf4e2be; internal record; image numerals relocated to fuzz_reply image A by alreloc frozen-a5c53bb2bed4ad03. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30: the malloc interceptor's BODY contract for omx-clap-core/fuzz_preset image A (asan, pin
   1be0f53d96cb), the text it is proved against, and the window-generic forms the body walk uses.
   - LOCAL COPY of the layer text a Theorem Labs lane drafted for Reusable/YG0dcf.v (amalloc-body-text.v, a Theorem Labs lane option (a) of
     08:45Z), AMENDED as a Theorem Labs lane decided at 08:59Z after a Theorem Labs lane's STOP (the body pre had no ly_bot bound, so it was not
     derivable from Allocate's alloc_pre, Reusable/AllocG.v:75): (1) acall_pre_cf_w's stack-bottom premise is
     `ly_bot ly + MALLOC_BODY_FRAME_CF < spZ regs` (2,144, the max over the units of the body's sp drop to Allocate's
     entry; A' 2,144); (2) inner_trace_cf is deleted: the trace is call_trace. Final text: a Theorem Labs lane 09:03Z. The names carry
     the suffix _L until TkSecLink's layer commit lands; then they are replaced by the layer's and this copy is deleted.
   - bpre_w STK BF: acall_pre_cf (YG0dcf.v:54-245) with ASTACK -> STK and ACALL_PREFIX -> BF, IN THE SAME CONJUNCT ORDER,
     so the walk files' destructs are the wrapper walk's; acall_pre_cf is bpre_w ASTACK ACALL_PREFIX (bpre_w_cf) and the
     body text's acall_pre_cf_w STK is bpre_w STK MALLOC_BODY_FRAME_CF (bpre_w_body), both by reflexivity.
   - rin_w / rwin_w / rkeep_w STK: RGtop.rin / rwin / rkeep (RGtop.v:210-220) with ASTACK -> STK.
   - K_w STK: K_A (WrapMallocADefs.v:50-63) with ASTACK -> STK. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfMallocCompose.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v WrapMallocAConsts.
Import ListNotations.
Local Open Scope Z_scope.

(* amalloc-body-text.v:19 / :22 (final, a Theorem Labs lane 09:03Z) *)
Definition MALLOC_IN_STK_L : Z := 14208.
Definition MALLOC_BODY_FRAME_L : Z := 2144.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section J.
Variable segs : list Segment.
Variable B : asyms.
Let code := as_code B.

(* amalloc-body-text.v:27-40, acall_pre_cf_w (final); round-3 re-fit: the layer's new budget conjunct (with the
   shadow / 8) and its last two conjuncts (cf_hull_ok, arodata_ok_cf; part 3c: no memnorm), Reusable/YG0dcf.v acall_pre_cf_w *)
Definition acall_pre_cf_w_L (stk : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) : Prop :=
ARcf segs B ly S Hp W mem md /\
YK0s.ret_ok (getr regs 1) /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + stk <= spZ regs /\ ly_bot ly + MALLOC_BODY_FRAME_L < spZ regs /\
spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
chain_pre ly (aview segs (w_H W) mem) regs ch /\
qmeter_cf S /\
Z.of_nat (length (st_sec_arr S)) < cf_sec_live_max /\
ERRB_ROOM S /\
abudget_cf S + FA_GROW_MAX + FA_GROW_MAX / 8 <= CF_MAX /\
batch_room_cf S /\
cf_hull_ok S /\
arodata_ok_cf segs B mem.

(* amalloc-body-text.v:44-63, malloc_leaf_cf_w *)
Definition malloc_leaf_cf_w_L (stk : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
acall_post_cf segs B stk ly S Hp W regs mem md
(fun a => (fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
\/ Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' (snd r)))
ly' (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
qtight (snd r) /\
(fst r = PNull -> rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\ aview segs (w_H W') mem' (as_oom_byte B) = Some 1) /\
xs_placed_cf ly' (snd r) /\
(fst r <> PNull -> forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
 ~ ascratch B stk regs (bv_unsigned x) ->
 ~ ((fst r <> PNull /\ sptr_addr B ly' (fst r) <= bv_unsigned x < sptr_addr B ly' (fst r) + req_size n)
    \/ Exists (in_zr (bv_unsigned x)) (xs_cf ly S ++ xs_cf ly' (snd r))) ->
 mem' x = mem x).

(* amalloc-body-text.v:68-75 (final) *)
Definition amalloc_body_realizes_L (pc_ra0 : Z) : Prop :=
forall ly S Hp W regs mem md n ch,
acall_pre_cf_w_L MALLOC_IN_STK_L ly S Hp W regs mem md ch ->
getr regs 10 = w64 n -> 0 <= n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly pc_ra0 regs ch) S ->
amreal segs (malloc_cf n (call_trace ly pc_ra0 regs ch) S) W
(cfg_at segs (pc_malloc code) regs mem md)
(malloc_leaf_cf_w_L MALLOC_IN_STK_L ly S Hp W regs mem md n).

(* acall_pre_cf with ASTACK -> stk, ACALL_PREFIX -> bf, same conjunct order (round-3 re-fit: the layer's new budget
   conjunct and last two conjuncts, part 3c). *)
Definition bpre_w (stk bf : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) : Prop :=
ARcf segs B ly S Hp W mem md /\
YK0s.ret_ok (getr regs 1) /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + stk <= spZ regs /\ ly_bot ly + bf < spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
chain_pre ly (aview segs (w_H W) mem) regs ch /\
qmeter_cf S /\
Z.of_nat (length (st_sec_arr S)) < cf_sec_live_max /\
ERRB_ROOM S /\
abudget_cf S + FA_GROW_MAX + FA_GROW_MAX / 8 <= CF_MAX /\
batch_room_cf S /\
cf_hull_ok S /\
arodata_ok_cf segs B mem.

Lemma bpre_w_cf : forall ly S Hp W regs mem md ch,
acall_pre_cf segs B ly S Hp W regs mem md ch <-> bpre_w ASTACK ACALL_PREFIX ly S Hp W regs mem md ch.
Proof. intros. unfold acall_pre_cf, bpre_w. reflexivity. Qed.

Lemma bpre_w_body : forall stk ly S Hp W regs mem md ch,
acall_pre_cf_w_L stk ly S Hp W regs mem md ch <-> bpre_w stk MALLOC_BODY_FRAME_L ly S Hp W regs mem md ch.
Proof. intros. unfold acall_pre_cf_w_L, bpre_w. reflexivity. Qed.

(* RGtop.v:210-220 with ASTACK -> stk. *)
Definition rkeep_w (stk : Z) (regs : bvmap 5 word) (W : world segs) (mem : word -> option byte)
(W' : world segs) (mem' : word -> option byte) : Prop :=
(forall a, 0 <= a < 2 ^ 64 -> ~ ascratch B stk regs a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall x : word, ~ ascratch B stk regs (bv_unsigned x) -> mem' x = mem x).
Definition rwin_w (stk : Z) (regs : bvmap 5 word) (W : world segs) (mem : word -> option byte) : Prop :=
forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) mem a.
Definition rin_w (stk : Z) (regs : bvmap 5 word) (sp stk' : Z) : Prop := spZ regs - stk <= sp - stk' /\ sp <= spZ regs.
(* YGcfMallocCompose.ikeep_cf (YGcfMallocCompose.v:91-96) with ASTACK -> stk. *)
Definition ikeep_w (stk : Z) (ly : alayout) (S : astate) (regs : bvmap 5 word) (W : world segs) (mem : word -> option byte)
(W' : world segs) (mem' : word -> option byte) : Prop :=
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ ascratch B stk regs a ->
 aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ ascratch B stk regs (bv_unsigned x) -> mem' x = mem x) /\
(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem').
(* YGcfMallocCompose.mentry_cf (YGcfMallocCompose.v:111-115) at bpre_w stk bf. *)
Definition bentry_w (stk bf : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z) (ch : list (Z * Z * Z)) : Prop :=
bpre_w stk bf ly S Hp W regs mem md ch /\
getr regs 10 = w64 n /\ 0 <= n < cf_malloc_max /\ blocks_bytes S + n <= LIVE_MAX /\
admits (as_universe B) (YGcfMallocCompose.mtr_cf B ly regs ch) S.
End J.

(* K_A (WrapMallocADefs.v:50-63) with ASTACK -> stk. *)
Definition K_w (stk : Z) : YGcfMallocCompose.Kmalloc_t tfibsegs := fun ly S Hp W regs mem md n ch W1 regsA memA mdA =>
W1 = W /\ getr regsA 2 = w64 (spZ regs - 2144) /\ getr regsA 1 = w64 RA_ALLOC /\
getr regsA 8 = getr regs 2 /\ getr regsA 3 = getr regs 3 /\ getr regsA 4 = getr regs 4 /\
(forall r : Z, 22 <= r <= 27 -> getr regsA (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (spZ regs - 2144) 8 (spZ regs) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (spZ regs - 2136) 8 RA_ASAN_MALLOC /\
val_mem tfibsegs (mrestrict (w_H W) memA) (spZ regs - 8) 8 (raZ regs) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (spZ regs - 16) 8 (s0Z regs) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) /\
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) memA a).
End G.
