(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCSpec.v at 0de5d668c87 (rl_post and rl_pre, its lines 124-148, as pw_post and pw_pre, word for word); the contract pod_write_ent_specX, its constants and the two bridge lemmas are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/PweSpec.v at 517c313c5a9; only the logical path of every Require changed (reac_pw.fuzz_rate.lib -> reac_pw.fuzz_headamp.lib); the text is image-independent, and this unit's lib/Pod/Model.v, Layout.v and lib/Reusable kit files are the rate unit's up to that path. *)
(* The ASan-level contract of pod_write_ent(pp, e) (fuzz/pod.h:200-206, with pod_put :175-182, pod_pad :184-188,
   pod_put32 :190-193). Only the asan-ubsan builds keep this function out of line (the asan builds inline it), so this
   is a contract of image B. IMAGE-INDEPENDENT: no image module is Required; segs, the symbol record B, the meter MT and
   the entry address are Section variables or parameters, and the pod sizes are the shared lib/Pod/Layout.v definitions
   (PP_SIZE = sizeof(struct pod_props), OFF_LEN = offsetof(len) = sizeof buf, POD_BUF_MAX, ENT_SIZE =
   sizeof(struct pod_ent)), so the asan-ubsan images of reac-pw's fuzz_rate, fuzz_role and fuzz_headamp instantiate the
   same text. Statement text only: no function is proved here.

   The code (measured on the unstripped fuzz_rate.asan-ubsan, sha256
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, at 0x83cc4: 776 bytes, 194 instructions; the same
   code, level-3 identical, is at 0x82bac in fuzz_role.asan-ubsan and at 0x84634 in fuzz_headamp.asan-ubsan):
   - `addi sp,sp,-48` and the saves of ra, s0-s3 at sp - 8 .. sp - 40; no side-stack frame and no shadow store;
   - the alignment tests e & 3 (pod.h:202) and pp & 7 (pod.h:177), each a branch to the trap `unimp`;
   - the runtime's shadow offset K, read through the image's GOT cell (two 8-byte loads without a check);
   - 14 instrumented checks (a load of the shadow byte at (a >> 3) + K and a compare): the 4-byte loads of e->size at
     e + 4 (twice) and of e->type at e, the 8-byte loads of pp->len at pp + OFF_LEN (seven times), and the first and
     last byte of the two 4-byte puts; the 4-byte checks take the second test `andi 7; addi 3; blt` when the shadow
     byte is not 0; each failing check reaches the error path (a call of an __asan_report_ entry);
   - four capacity guards (len + 4, len + 4, len + size, len + pad <= POD_BUF_MAX, else that put is skipped), and
     before each put the UBSan pair `bgeu len, 16385` / `bltu ~pp, len`, each a branch to the trap;
   - put32 e->size and put32 e->type (four byte stores each), len += 4 after each; __asan_memcpy(pp + len, e + 8,
     size) and len += size; pad = (-len) & 7, __asan_memset(pp + len, 0, pad) and len += pad (both runtime calls are
     made also when their count is 0); the restores and `ret`.
   So under the premises below every guard falls through, no trap and no error path is taken, and the n = |enc_pod e|
   bytes at pp + len become Model.enc_pod e (the size word first; pod_pad pads pp->len, not e->size, hence len mod 8 =
   0), and the len cell becomes len + n.

   What it writes: the n bytes at pp + len and the 8 bytes of the len cell (pwe_E), its frame [sp - 48, sp) and the two
   runtime callees' stack below sp - 48 (ESTACK each): T_pwe_STK below sp in all. It writes NO shadow byte: the post
   says every shadow byte of the application range [0, kHighMemEnd) is as at the call, and, as the cases a caller
   reads, that pp's block and e's 104 bytes are still marked usable. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* The stack pod_write_ent uses below its caller's sp: its own frame of 48 bytes, and below that the stack of the
   runtime callee it calls (__asan_memcpy, then __asan_memset), bounded by the kit's ESTACK (YG0d.v aintrin_realizes). *)
Definition T_pwe_STK : Z := 48 + ESTACK.
(* n, the number of bytes pod_write_ent puts at pp + len. *)
Definition pwe_len (e : Model.ent) : Z := Z.of_nat (length (Model.enc_pod e)).
(* The bytes it writes for its caller: the n bytes at pp + len and the 8-byte len cell at pp + OFF_LEN. *)
Definition pwe_E (pp len : Z) (e : Model.ent) (x : Z) : Prop :=
pp + len <= x < pp + len + pwe_len e \/ pp + Layout.OFF_LEN <= x < pp + Layout.OFF_LEN + 8.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================================== the post of a callee =====================================
   RPgCSpec.v's rl_post: the call returns to ra (getr regs 1) at some float state fx2 with FX fx2, its journal extends
   the caller's (k events: the function allocates nothing), the callee-saved registers are kept, the frames, blocks,
   I/O state and meter are as at the call, and every byte outside its stack [sp - T, sp) and outside E is as at the
   call. R is what the function computes. *)
Definition pw_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k T : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
(FX : YK11.FPState -> Prop) (E : Z -> Prop) (R : world segs -> bvmap 5 word -> (word -> option byte) -> Prop)
: world segs -> config -> Prop :=
fun W2 c2 => exists (fx2 : YK11.FPState) ly2 S2 regs2 mem2 md2,
c2 = mkCfg (@mkst fx2 regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\ FX fx2 /\
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T <= a < spZ regs) -> ~ E a ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
R W2 regs2 mem2.

(* RPgCSpec.v's rl_pre: the caller's journal from its own entry to the call, the call's ra / gp / tp, and the callee's
   stack T inside the caller's stack window. *)
Definition pw_pre (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k T : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) : Prop :=
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - T /\ spZ regs <= sp0 /\
st_nev S + k <= EV_MAX.

(* ========================== pod_write_ent(pp, e) (pod.h:200-206) ==========================
   a0 = pp, the pod buffer (struct pod_props, PP_SIZE bytes); a1 = q, the address of the struct pod_ent e (ENT_SIZE
   bytes: type, size, the body array). The premises:
   - pp: 8-aligned (the test pp & 7), pp + PP_SIZE <= 2^63 (so no `bltu ~pp, len` is taken), its PP_SIZE bytes in the
     range the shadow map covers, marked usable, with a readable shadow hull (the instrumented checks of the len cell
     and of the puts, and the two runtime calls, read them); each byte it writes (pwe_E) the caller's to write under
     its journal (YCbq.v awr_byte; pwe_awr_fresh gives it for a block made since the journal's start); the block
     apart from the callee's stack;
   - len: the 8-byte len cell at pp + OFF_LEN holds len, 8-aligned, and len + n <= POD_BUF_MAX (so every capacity
     guard falls through and no `bgeu len, 16385` is taken);
   - e: q 8-aligned, which implies the alignment the code itself tests (e & 3, pod.h:202). Every struct pod_ent
     pod_write_ent is called on is a frame object of the entry function's side-stack frame, and the runtime's frame
     layout puts each object on a shadow granule, so 8 | q at each of the three units' call sites (rate's frame
     description at 0x113f3 reads "32 96 ... 160 24 ... 224 4 ... 240 104 3 e.i 384 104 5 e42.i 528 104 5 e62.i
     672 4 ...": every offset is a multiple of 8). The walk needs it: the shadow byte of e->size at e + 4 is read
     through ((e + 4) >> 3) + K, and that address is a function of e >> 3 only when 8 | e. Its ENT_SIZE bytes are
     Layout.ent_mem e with the body's length e_size <= ENT_SIZE - 8 and the type word in range (both are part of
     Model.ent_wf, which the harness's record carries), in the range the shadow map covers, marked usable, with a
     readable shadow hull (the checks of e->type and e->size, and __asan_memcpy's source range e + 8 ..
     e + 8 + size, read them); e apart from pp's block
     (its size is read again after the puts) and from the callee's stack.
   The post: rl_post's shape with the float state kept, E = pwe_E pp len e, and R: the n bytes at pp + len are
   Model.enc_pod e, the len cell holds len + n, every shadow byte of [0, kHighMemEnd) is as at the call, and pp's
   block and e's bytes are still marked usable. *)
Definition pod_write_ent_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (pp q len : Z) (e : Model.ent),
pw_pre STK sp0 FP ly S W0 mem0 md0 own k T_pwe_STK regs lyc Sc W memc mdc ->
getr regs 10 = w64 pp -> getr regs 11 = w64 q ->
0 <= pp -> pp mod 8 = 0 -> pp + Layout.PP_SIZE <= 2 ^ 63 -> amem_range pp Layout.PP_SIZE ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF pp Layout.PP_SIZE ->
shadow_hull_vis (aview segs (w_H W) memc) pp Layout.PP_SIZE ->
(forall x, pwe_E pp len e x -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x) ->
(pp + Layout.PP_SIZE <= spZ regs - T_pwe_STK \/ spZ regs <= pp) ->
val_mem segs (mrestrict (w_H W) memc) (pp + Layout.OFF_LEN) 8 len ->
0 <= len -> len mod 8 = 0 -> len + pwe_len e <= Layout.POD_BUF_MAX ->
0 <= q -> q mod 8 = 0 -> amem_range q Layout.ENT_SIZE ->
Z.of_nat (length (Model.e_body e)) = Model.e_size e -> Model.e_size e <= Layout.ENT_SIZE - 8 ->
0 <= Model.e_type e < 2 ^ 32 ->
garr8 segs (mrestrict (w_H W) memc) q (map (fun x : byte => bv_unsigned x) (Layout.ent_mem e)) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF q Layout.ENT_SIZE ->
shadow_hull_vis (aview segs (w_H W) memc) q Layout.ENT_SIZE ->
(pp + Layout.PP_SIZE <= q \/ q + Layout.ENT_SIZE <= pp) ->
(q + Layout.ENT_SIZE <= spZ regs - T_pwe_STK \/ spZ regs <= q) ->
SRr segs W (cfg_at segs a regs memc mdc)
(pw_post STK sp0 FP ly S W0 mem0 md0 own k T_pwe_STK regs lyc Sc W memc mdc
(fun f => f = fx) (pwe_E pp len e)
(fun W2 _ mem2 =>
garr8 segs (mrestrict (w_H W2) mem2) (pp + len) (map (fun x : byte => bv_unsigned x) (Model.enc_pod e)) /\
val_mem segs (mrestrict (w_H W2) mem2) (pp + Layout.OFF_LEN) 8 (len + pwe_len e) /\
(forall x, 0 <= x < kHighMemEnd ->
 aview segs (w_H W2) mem2 (shadow_addr x) = aview segs (w_H W) memc (shadow_addr x)) /\
range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF pp Layout.PP_SIZE /\
range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF q Layout.ENT_SIZE)).

(* ========================== how a caller supplies the pp premises ==========================
   The write right: a pod buffer allocated since the caller's journal began (in the current blocks, not in the
   journal's start blocks) is the journal's to write (YCbq.v awr_byte, its in_tmp_block case). This is how the
   harness's call sites hold it: pp is the harness's malloc(PP_SIZE), made after the harness's own entry. *)
Lemma pwe_awr_fresh : forall STK sp0 FP ly S lyc Sc own pp len e,
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
0 <= len -> len + pwe_len e <= Layout.POD_BUF_MAX ->
forall x, pwe_E pp len e x -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x.
Proof.
intros STK sp0 FP ly S lyc Sc own pp len e Hin Hout Hl0 Hln x Hx.
right. right. left. exists pp, Layout.PP_SIZE. split; [exact Hin|]. split; [exact Hout|].
assert (Hn : 0 <= pwe_len e) by (unfold pwe_len; lia).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
rewrite Hrq.
unfold pwe_E in Hx. unfold Layout.PP_SIZE, Layout.OFF_LEN, Layout.POD_BUF_MAX in *. lia.
Qed.

(* The memory premises on pp from the block law: a live block of PP_SIZE bytes is 16-aligned, below the allocator's
   ceiling, in the application range, marked usable (PP_SIZE is a multiple of 8, so no partial granule) and has a
   readable shadow hull (YG0d.v AR_blocks_law and AR_shadow_law, through YCbq.v's block lemmas). *)
Lemma pwe_pp_of_block : forall ly S W mem md pp,
AR segs B ly S W mem md -> In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
0 <= pp /\ pp mod 8 = 0 /\ pp + Layout.PP_SIZE <= 2 ^ 63 /\ amem_range pp Layout.PP_SIZE /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF pp Layout.PP_SIZE /\
shadow_hull_vis (aview segs (w_H W) mem) pp Layout.PP_SIZE.
Proof.
intros ly S W mem md pp HAR Hin.
pose proof (YG0q.AR_laws_ok segs B) as LAWS.
destruct ((al_blocks _ _ LAWS) ly S W mem md pp Layout.PP_SIZE HAR Hin) as (H16 & H4096 & Hceil & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
rewrite Hrq in Hceil.
pose proof (@alloc_ceiling_lt rc) as Hc47.
assert (HP47 : 2 ^ 47 = 140737488355328) by reflexivity.
assert (HP63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
rewrite HP47 in Hc47.
assert (H8 : pp mod 8 = 0).
{ pose proof (Z.div_mod pp 16 ltac:(lia)) as Hd. rewrite H16, Z.add_0_r in Hd.
  rewrite Hd at 1. replace (16 * (pp / 16)) with ((2 * (pp / 16)) * 8) by ring. apply Z.mod_mul. lia. }
split; [lia|]. split; [exact H8|].
split; [rewrite HP63; unfold Layout.PP_SIZE in *; lia|].
split; [apply (amem_range_of_block segs B LAWS ly S W mem md pp Layout.PP_SIZE); [exact HAR | exact Hin | lia | rewrite Hrq; lia]|].
split; [apply (range_addressable_of_block segs B LAWS ly S W mem md pp Layout.PP_SIZE); [exact HAR | exact Hin | lia | rewrite Hrq; lia]|].
apply (shadow_hull_vis_of_block segs B LAWS ly S W mem md pp Layout.PP_SIZE); [exact HAR | exact Hin | lia | rewrite Hrq; lia | unfold Layout.PP_SIZE; lia].
Qed.
End b.

Print Assumptions pwe_awr_fresh.
Print Assumptions pwe_pp_of_block.
