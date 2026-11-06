(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk technique (a seed proved from the call precondition, srr_run_to_sh to
   each call site, a callee contract applied there with SRr_bind, a new seed after the call) is ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/AFj0.v (the seed) and A/AFip.v (segA: the run to the unwinder's call, the
   contract application, the frame transport), to libreac/fuzz_decode's asan_calloc in image A (fuzz_decode.asan);
   [amreal_post_SRr] is YG0d.v:119 amreal_ibind's induction with an SRr continuation in place of a tree. *)
(* The walk of __asan::asan_calloc (image A, 0x31bd4 .. 0x31cb4, 56 instructions) over the Allocate contract of
   lib/Reusable/YGAlloc.v and the fill contract of lib/A/DecodeCallocRt.v.

   [entry_walk] starts at asan_calloc's first instruction with a0 = nm, a1 = sz, a2 = the trace object, any return
   address, and the premises [entry_pre], which include nm * sz <= PRIM_MAX = 64512 (YGCalloc.v: the largest request
   the primary allocator serves); it realizes the malloc tree at n = nm * sz (YG00.malloc, the tree Allocate's
   contract realizes) and lands in [entry_leaf] at the caller's return address: Allocate's leaf at n (the allocator
   relation, layout_le, wle, the callee-saved registers, same_io, the memory frame, the stack window, a0 = the block,
   qtight, the granted path), the block not NULL, and every byte of [a0, a0 + n) reading 0.  It does not know how
   the caller got there: the wrapper's walk (lib/A/DecodeCallocWrap.v) meets it at 0x524a4 `jal 0x31bd4` with
   ra = 0x524a8 ([entry_leaf_at_wrapper]).  [entry_walk_SRr] is the same run in SRr form through YG0d.v:185
   amreal_SRr04, the granted path in its leaf.

   What the instructions do, and where the proof takes each (addresses and words read with capstone and pyelftools
   from the ORIGINAL unstripped binary
   fuzz_decode.asan; the symbolic
   runs below decode the same words from the image module, lib/A/DecodeCallocTbl.v tbl_calloc_A):
     0x31bd4 `addi sp, sp, -0x30`; 0x31bd8 .. 0x31be8 ra, s0, s1, s2, s3 stored at sp + 40 .. sp + 8;
     0x31bec `mv s1, a2`                                       [walk_A: the prologue]
     0x31bf0 `beqz a1, 0x31bfc`; 0x31bf4 `mulhu a2, a1, a0`; 0x31bf8 `bnez a2, 0x31c64`
       [walk_A: both arms of the size test; with nm * sz < MALLOC_MAX = 2 ^ 28 the high half of the product is
        (sz * nm) >> 64 = 0, so the branch to the overflow arm 0x31c64 is refuted, not assumed]
     0x31bfc `mul s0, a1, a0`; 0x31c00 `auipc a0, 0x6c` + 0x31c08 `addi s2, a0, -0x4a8` (s2 = 0x9d758, the
     allocator instance); a2 = 8; a4 = 1; s3 = 1; a0 = s2; a1 = s0; a3 = s1; a5 = 0; 0x31c24 `jal 0x3124c`
       [walk_A, close_A: the state at Allocate's entry; alloc_pre_of: YGAlloc.alloc_pre there; entry_walk_i:
        Allocate's contract, decode_aalloc_A]
     0x31c28 `beqz a0, 0x31c74`   [post_alloc: refuted by YGCallocModel.calloc_nonnull from the leaf's granted path]
     0x31c2c `ld a1, 0x20(s2)` (the word at 0x9d778); 0x31c30 `bltu a0, a1, 0x31c7c`;
     0x31c34 `slli s3, s3, 0x25` (2 ^ 37); 0x31c38 `add a1, a1, s3`; 0x31c3c `bgeu a0, a1, 0x31c7c`
       [post_alloc: both branches to 0x31c7c refuted (below); the run goes on to the fill]
     0x31c40 `auipc a1, 0x67` + 0x31c44 `ld a1, 0x120(a1)` (the slot 0x98d60, holding 0x9abc0);
     0x31c48 `ld a3, 0(a1)` (0x9abc0, holding musl memset 0x92474); 0x31c4c `mv s1, a0`; a1 = 0; a2 = s0;
     0x31c58 `jalr a3`; 0x31c5c `mv a0, s1`; 0x31c60 `j 0x31c7c`
       [post_alloc, primary arm: the fill contract decode_zero_fill_spec_A at 0x92474 gives the n zero bytes]
     0x31c7c .. 0x31c90 ra, s0, s1, s2, s3 reloaded, sp += 0x30; 0x31c94 `ret`   [ret_leaf]
   The overflow arm 0x31c64 .. 0x31cb0, the NULL arm 0x31c74 and the two skips of the fill at 0x31c30 / 0x31c3c are
   not reached.

   THE ZERO BYTES.  The size premise gives from_primary n = true ([prim_fp], ported from cgif A/AFij.v:38-49), so the
   block is a primary one: the granted path puts (fst r, n) in the block table (YGCallocModel.v calloc_block_table),
   and the chunk facts of the allocator relation after the call (YG0s.v:240 chunk_facts) make it PPrim off with its
   address in [ly_space ly', ly_space ly' + 2 ^ 37) ([prim_block_in_space]).  The word at 0x9d778 is ly_space ly'
   (the IMG_CONST cell), so a0 >= P and a0 < P + 2 ^ 37 < 2 ^ 64: neither skip is taken.  The run reaches 0x92474 with
   a0 = the block, a1 = 0, a2 = n, ra = 0x31c5c, and the fill contract gives aview (d + i) = Some (0 mod 256) for
   i < n, keeps the allocator relation, and keeps every byte outside [d, d + n) and the fill's own 4096 stack bytes;
   the run from 0x31c5c to the `ret` writes nothing.  No fact about the bytes of a secondary (freshly mapped) block
   is used.

   Section Hypotheses, each named in the report:
   - [ALLOC]: Allocate's contract at decode's values (lib/A/DecodeCalloc.v decode_aalloc_A: alloc_pc 0x3124c, the
     instance 0x9d758, the out-of-memory byte 0x123020, al = 8, atp = 1, cf = 0).
   - [FILL]: the fill contract (lib/A/DecodeCallocRt.v decode_zero_fill_spec_A: musl memset at 0x92474).
   - [LAWS]: the allocator relation's law record (YG0d.v:496 AR_laws), which the unit's AsanAPI carries (YG0d.v:532
     aa_laws) and every call rule of the walk layer takes as its Section hypothesis (YCbq.v:207, :815).  Used for:
     the relation survives the stack stores below sp and the model's materialization step (al_frame, al_stack), and
     the block's bytes are present and not the allocator's (al_blocks, for the fill's dest_ok).
   - [IMG_CONST]: the image's constant cells the walk reads, as cells of the allocator relation's constant list
     (as_const, held by ARm am_const at every state): the fill pointer's two words, 0x98d60 holds 0x9abc0 and 0x9abc0
     holds musl memset 0x92474 (the indirect call at 0x31c58), stated at image addresses (ANum), and the allocator
     instance's space-base word, as_inst B + o_space holds ly_space ly (the load at 0x31c2c), stated in the symbol
     record's own form `c8 (AInst o_space) (ASp 0)` (lib/A/AF0m.v Tfib_const_sym).  The image bytes of the first
     two are these values (DecodeCallocRt.v dec_A_got_real_memset_val, dec_A_real_memset_val); the third is .bss,
     written at start-up.  The walk reads all three after Allocate, so it needs them as cells of the relation, not
     as image bytes.  cgif gets the same three from its symbol record TfibSyms (ts_const): A/AF0m.v:27 `c8 (AInst
     o_space) (ASp 0)`, :178 `z8 (ANum 0x9dfb8) 0x9fe28` and :96 `z8 (ANum 0x9fe28) 0x97698`; decode's (lib/A/AF0m.v
     GrantSyms) gives all three in lib/A/DecodeARows.v dec_a_img_const.
   - [HINST]: B's allocator instance is __asan::instance, as_inst B = DEC_A_instance = 0x9d758, so the third
     IMG_CONST cell is the word at DEC_A_space_cell = 0x9d778 that 0x31c2c reads (cgif: ts_inst, as c5 lib/AGiy.v
     inst_cells uses it); decode's GrantSyms gives it in lib/A/DecodeARows.v dec_a_inst.
   - [ERRNO_LOW]: errno lies in low memory, below kLowMemEnd: the first conjunct of the walk layer's YCbq.v:808
     api_env (YCbq.v:817 Hypothesis errno_low).  Allocate's post may write errno (ascratch); this keeps the 48
     saved bytes of the frame, which lie in high memory, out of that range. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import
DecodeTFIB DecodeCallocTbl DecodeCalloc DecodeCallocSkel DecodeCallocSeed DecodeCallocRt.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import DecodeCallocKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YGCalloc YGCallocModel.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YGAlloc YO0f YG04 YG0s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================================================================
   Addresses (image A), read with capstone from the original binary and decoded again by the runs below. *)
(* asan_calloc's frame: 0x31bd4 `addi sp, sp, -0x30`. *)
Definition ENTRY_FRAME : Z := 0x30.
(* The stack bytes below the entry sp the walk uses: the frame, and Allocate's 4096 below it (YGAlloc.AFSTACK_G);
   the fill uses 4096 (ESTACK) below the same sp - 0x30. *)
Definition ENTRY_STK : Z := ENTRY_FRAME + YGAlloc.AFSTACK_G.
(* The return address of 0x31c24 `jal 0x3124c`, of 0x31c58 `jalr a3`, and the `ret` at 0x31c94. *)
Definition DEC_A_calloc_alloc_ret : Z := 0x31c28.
Definition DEC_A_calloc_fill_ret : Z := 0x31c5c.
Definition DEC_A_calloc_ret_insn : Z := 0x31c94.
(* 0x31c2c `ld a1, 0x20(s2)` with s2 = 0x9d758: the word at 0x9d778, the base of the primary space. *)
Definition DEC_A_space_cell : Z := DEC_A_instance + 0x20.
(* 0x31c10 `addi s3, zero, 1`, 0x31c34 `slli s3, s3, 0x25`: the size of the primary space (= YG0f.kSpaceSize). *)
Definition PRIM_SPACE_SIZE : Z := 2 ^ 37.
(* The wrapper's call of asan_calloc: 0x524a4 `jal 0x31bd4` (word 0xf30df0ef); its return address. *)
Definition DEC_A_wrap_after_call : Z := 0x524a8.

(* The room premise bounds the product far below 2 ^ 64, so the 64-bit product is the product and its high half is 0. *)
Lemma calloc_prod_mod : forall nm sz, 0 <= nm -> 0 <= sz -> nm * sz < MALLOC_MAX ->
(sz mod 2 ^ 64) * (nm mod 2 ^ 64) = nm * sz /\ 0 <= nm * sz < 2 ^ 28.
Proof.
intros nm sz Hnm Hsz Hn. unfold MALLOC_MAX in Hn.
assert (H0 : 0 <= nm * sz) by nia.
destruct (Z.eq_dec nm 0) as [->|Hn0]; [rewrite Z.mod_0_l by lia; split; lia|].
destruct (Z.eq_dec sz 0) as [->|Hs0]; [rewrite Z.mod_0_l by lia; split; lia|].
assert (nm < 2 ^ 28) by nia. assert (sz < 2 ^ 28) by nia.
rewrite !Z.mod_small by lia. split; lia.
Qed.

Lemma lit64_unsigned : forall z, bv_unsigned (Z_to_bv 64 z) = z mod 2 ^ 64.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* Reading the symbolic state back: a chunk of a region of [ss] is a value in memory, a writable byte of a region
   above the image is present. *)
Lemma st_chunk_val : forall E ss ms (H : word -> bool) r off (n : N) e v,
st_ok decodesegs0 E ss (restrict H ms) -> In r (ss_mem ss) -> In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem decodesegs0 (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros E ss ms H r off n e v HS Hr Hc He Hv Hn.
pose proof (st_ok_mem_ok decodesegs0 E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (_ & _ & _ & Hcs).
apply (val_of_chunk_ok decodesegs0 E _ _ off n e v); [|exact He | exact Hv | exact Hn].
exact (proj1 (Forall_forall _ _) Hcs _ Hc).
Qed.
Lemma st_window_present : forall E ss ms (H : word -> bool) r a,
st_ok decodesegs0 E ss (restrict H ms) -> In r (ss_mem ss) ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
IMG_TOP <= a < 2 ^ 64 -> apresent H (ms_mem ms) a.
Proof.
intros E ss ms H r a HS Hr Ha Hhi.
pose proof (st_ok_mem_ok decodesegs0 E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (_ & _ & Hw & _).
apply apresent_of_writable_high; [exact Hhi|].
replace a with (base_val E (YP09.r_base r) + (a - base_val E (YP09.r_base r))) by lia. apply Hw. lia.
Qed.
Lemma apresent_same : forall (H : word -> bool) (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> apresent H m a -> apresent H m' a.
Proof. intros H m m' a E [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite E. exact Hb. Qed.

Section a.
Variables (W : world decodesegs0) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (nm sz so : Z).
Let sp : Z := spZ regs.
Hypothesis Hsp : kHighMemBeg + ENTRY_STK <= sp <= kHighMemEnd.
Hypothesis Hal : sp mod 16 = 0.
Hypothesis Hpres : forall a, sp - ENTRY_STK <= a < sp -> apresent (w_H W) mem a.
Hypothesis Hnm : YK11.getr regs 10 = w64 nm.
Hypothesis Hsz : YK11.getr regs 11 = w64 sz.
Hypothesis Hso : YK11.getr regs 12 = w64 so.
Hypothesis Hroom : 0 <= nm /\ 0 <= sz /\ nm * sz < MALLOC_MAX.

(* The seed at asan_calloc's entry: every register its own atom, the 48-byte frame below sp writable and empty. *)
Definition FG_E : facts := mkFacts [(2%nat, mkAF (kHighMemBeg + ENTRY_STK) kHighMemEnd 4)] [] [].
Definition REG_E : smem := [YP09.mkRegion (Some 2%nat) (- ENTRY_FRAME) 0 (- ENTRY_FRAME) 0 []].
Definition SS_E : sstate := mkSS DEC_A_asan_calloc sr_atoms REG_E None FG_E.
Definition E_E : env := Ereg regs [].

Lemma E_E2 : bv_unsigned (ew E_E 2) = sp.
Proof. unfold E_E. rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl). reflexivity. Qed.
Lemma E_E_reg (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E_E k = YK11.getr regs r.
Proof. intros Hk. exact (ew_Ereg_nat regs [] k r Hk). Qed.

Lemma SEED_E : st_ok decodesegs0 E_E SS_E
(restrict (w_H W) (YK11.mkst regs (w64 DEC_A_asan_calloc) mem (YK11.seg_rom decodesegs0))).
Proof.
pose proof E_E2 as E2.
rewrite restrict_mkst_fx. unfold SS_E, w64, E_E. apply (entry_st_ok_full decodesegs0).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold REG_E.
apply (region_ok_stack decodesegs0 (Ereg regs []) _ 2 sp (- ENTRY_FRAME) E2).
+ unfold ENTRY_STK, ENTRY_FRAME, YGAlloc.AFSTACK_G, kHighMemBeg in *. lia.
+ pose proof (u64_range (YK11.getr regs 2)). unfold sp, spZ in *. lia.
+ intros a Ha. destruct (Hpres a ltac:(unfold ENTRY_STK, ENTRY_FRAME, YGAlloc.AFSTACK_G in *; lia)) as [Hh [b Hb]].
unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate.
- cbn. split; exact I.
- split; [|split; exact I]. unfold FG_E. cbn [f_atoms atoms_ok]. split; [|exact I].
unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E_E. rewrite E2. split; [lia|]. split; [exact Hal | lia].
Qed.

(* The machine facts at Allocate's entry: the six arguments (a0 = instance, a1 = n, a2 = 8, a3 = the trace object,
   a4 = 1, a5 = 0), ra = 0x31c28, sp = entry sp - 0x30, s0 = n, s1 = the trace object, s2 = instance, s3 = 1, the other
   callee-saved registers as at the entry; memory changed only in the 48-byte frame, which holds the five saved
   registers. *)
Definition A_regs (regs1 : bvmap 5 word) : Prop :=
YK11.getr regs1 1 = w64 DEC_A_calloc_alloc_ret /\ YK11.getr regs1 2 = w64 (sp - ENTRY_FRAME) /\
YK11.getr regs1 8 = w64 (nm * sz) /\ YK11.getr regs1 9 = w64 so /\
YK11.getr regs1 10 = w64 DEC_A_instance /\ YK11.getr regs1 11 = w64 (nm * sz) /\
YK11.getr regs1 12 = w64 ALLOC_ALIGN /\ YK11.getr regs1 13 = w64 so /\
YK11.getr regs1 14 = w64 AT_FROM_MALLOC /\ YK11.getr regs1 15 = w64 CF_CALLOC /\
YK11.getr regs1 18 = w64 DEC_A_instance /\ YK11.getr regs1 19 = w64 1 /\
(forall r, r = 3 \/ r = 4 \/ 20 <= r <= 27 -> YK11.getr regs1 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
Definition A_mem (mem1 : word -> option byte) : Prop :=
(forall x : word, ~ (sp - ENTRY_FRAME <= bv_unsigned x < sp) -> mem1 x = mem x) /\
(forall a, sp - ENTRY_STK <= a < sp -> apresent (w_H W) mem1 a) /\
val_mem decodesegs0 (mrestrict (w_H W) mem1) (sp - 8) 8 (raZ regs) /\
val_mem decodesegs0 (mrestrict (w_H W) mem1) (sp - 16) 8 (bv_unsigned (YK11.getr regs 8)) /\
val_mem decodesegs0 (mrestrict (w_H W) mem1) (sp - 24) 8 (bv_unsigned (YK11.getr regs 9)) /\
val_mem decodesegs0 (mrestrict (w_H W) mem1) (sp - 32) 8 (bv_unsigned (YK11.getr regs 18)) /\
val_mem decodesegs0 (mrestrict (w_H W) mem1) (sp - 40) 8 (bv_unsigned (YK11.getr regs 19)).
Definition at_alloc (W' : world decodesegs0) (c' : config) : Prop :=
W' = W /\ exists regs1 mem1 mat,
c' = cfg_at decodesegs0 DEC_A_allocate regs1 mem1 (with_vm_backing (m_vm_lazy md) mat md) /\
A_regs regs1 /\ A_mem mem1.

(* The symbolic state the run reaches at Allocate's entry, on both arms of the size test. *)
Definition SR_A : list sv :=
[SLit 0; SLit DEC_A_calloc_alloc_ret; SOff 2 (- ENTRY_FRAME); SOff 3 0; SOff 4 0;
SOff 5 0; SOff 6 0; SOff 7 0; SMd M_MUL (SOff 11 0) (SOff 10 0);
SOff 12 0; SLit DEC_A_instance;
SAlu ALU_ADD (SMd M_MUL (SOff 11 0) (SOff 10 0)) (SLit 0);
SLit 8; SOff 12 0; SLit 1; SLit 0; SOff 16 0;
SOff 17 0; SLit DEC_A_instance; SLit 1; SOff 20 0; SOff 21 0;
SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0;
SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition REG_A : smem :=
[YP09.mkRegion (Some 2%nat) (- ENTRY_FRAME) 0 (- ENTRY_FRAME) 0
[YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]].

Lemma mul_denot : forall E, ew E 11 = w64 sz -> ew E 10 = w64 nm ->
sv_denot E (SMd M_MUL (SOff 11 0) (SOff 10 0)) = w64 (nm * sz).
Proof.
intros E H11 H10. destruct Hroom as (H1 & H2 & H3).
destruct (calloc_prod_mod nm sz H1 H2 H3) as [Hp Hr].
rewrite denot_lit_U, U_SMd. cbn [zmd_raw]. rewrite !U_SOff, H11, H10, !Z.add_0_r. unfold w64, zcanon, M64.
rewrite !lit64_unsigned, !Z.mod_mod by lia. rewrite Hp, (Z.mod_small (nm * sz)) by lia. reflexivity.
Qed.

(* Every region the run writes is the 48-byte frame below sp. *)
Lemma frame_sp : forall rs (m m' : word -> option byte), frame_of E_E rs m m' ->
Forall (fun r => YP09.r_base r = Some 2%nat /\ - ENTRY_FRAME <= YP09.r_wlo r /\ YP09.r_whi r <= 0) rs ->
forall x : word, ~ (sp - ENTRY_FRAME <= bv_unsigned x < sp) -> m' x = m x.
Proof.
intros rs m m' HF Hrs x Hx. apply HF. intros (r & Hin & Hr).
destruct (proj1 (Forall_forall _ _) Hrs r Hin) as (Hb & Hlo & Hhi).
rewrite Hb in Hr. cbn [base_val] in Hr. rewrite E_E2 in Hr. lia.
Qed.

Lemma close_A : forall ss ms mat,
st_ok decodesegs0 E_E ss (restrict (w_H W) ms) ->
ss_pc ss = DEC_A_allocate -> ss_regs ss = SR_A -> ss_mem ss = REG_A -> ss_resv ss = None ->
(forall x : word, ~ (sp - ENTRY_FRAME <= bv_unsigned x < sp) -> ms_mem ms x = mem x) ->
at_alloc W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)).
Proof.
intros ss ms mat HS Hpc Hr Hm Hrv FR.
pose proof E_E2 as E2.
assert (R : forall r : bv 5, YK11.getr (ms_regs ms) r = sv_denot E_E (sr_get SR_A r))
by (intros r; rewrite <- Hr; exact (st_ok_restrict_reg decodesegs0 (w_H W) E_E ss ms r HS)).
assert (K : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> sv_denot E_E (SOff k 0) = YK11.getr regs r).
{ intros k r Hk. rewrite denot_off0. exact (E_E_reg k r Hk). }
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), mat.
split.
{ pose proof (st_ok_restrict_mkst decodesegs0 (w_H W) E_E ss ms HS Hrv) as Hshape.
rewrite Hpc in Hshape. unfold cfg_at, w64. rewrite Hshape at 1. reflexivity. }
split.
- assert (M : sv_denot E_E (SMd M_MUL (SOff 11 0) (SOff 10 0)) = w64 (nm * sz)).
{ apply mul_denot; [rewrite (E_E_reg 11 11%bv eq_refl); exact Hsz | rewrite (E_E_reg 10 10%bv eq_refl); exact Hnm]. }
split; [rewrite R; reflexivity|].
split; [rewrite R; change (sr_get SR_A 2%bv) with (SOff 2 (- ENTRY_FRAME)); cbn [sv_denot]; rewrite E2; reflexivity|].
split; [rewrite R; change (sr_get SR_A 8%bv) with (SMd M_MUL (SOff 11 0) (SOff 10 0)); exact M|].
split; [rewrite R; change (sr_get SR_A 9%bv) with (SOff 12 0); rewrite (K 12%nat 12%bv eq_refl); exact Hso|].
split; [rewrite R; reflexivity|].
split.
{ rewrite R. change (sr_get SR_A 11%bv) with (SAlu ALU_ADD (SMd M_MUL (SOff 11 0) (SOff 10 0)) (SLit 0)).
rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite U_SLit, Z.add_0_r.
unfold U. rewrite M. unfold zcanon, M64, w64. rewrite lit64_unsigned. f_equal. rewrite Z.mod_mod by lia.
destruct Hroom as (H1 & H2 & H3). pose proof (proj2 (calloc_prod_mod nm sz H1 H2 H3)). apply Z.mod_small. lia. }
split; [rewrite R; reflexivity|].
split; [rewrite R; change (sr_get SR_A 13%bv) with (SOff 12 0); rewrite (K 12%nat 12%bv eq_refl); exact Hso|].
split; [rewrite R; reflexivity|].
split; [rewrite R; reflexivity|].
split; [rewrite R; reflexivity|].
split; [rewrite R; reflexivity|].
intros r Hr'. rewrite R.
destruct Hr' as [->|[->|Hr']]; [change (sr_get SR_A (Z_to_bv 5 3)) with (SOff 3 0); apply K; vm_compute; reflexivity
| change (sr_get SR_A (Z_to_bv 5 4)) with (SOff 4 0); apply K; vm_compute; reflexivity|].
assert (Hc : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct Hc as [->|Hc]; [match goal with |- sv_denot _ (sr_get _ (Z_to_bv 5 ?z)) = _ =>
let t := eval vm_compute in (sr_get SR_A (Z_to_bv 5 z)) in change (sr_get SR_A (Z_to_bv 5 z)) with t end;
apply K; vm_compute; reflexivity|]).
subst r. change (sr_get SR_A (Z_to_bv 5 27)) with (SOff 27 0). apply K; vm_compute; reflexivity.
- (* memory *)
assert (HM : In (YP09.mkRegion (Some 2%nat) (- ENTRY_FRAME) 0 (- ENTRY_FRAME) 0
[YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) (ss_mem ss)) by (rewrite Hm; left; reflexivity).
assert (CV : forall off (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r ->
In (YP09.mkChunk off (CVal 8 (SOff k 0))) [YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
val_mem decodesegs0 (mrestrict (w_H W) (ms_mem ms)) (sp + off) 8 (bv_unsigned (YK11.getr regs r))).
{ intros off k r Hk Hin. rewrite <- E2.
apply (st_chunk_val E_E ss ms (w_H W) _ off 8 (SOff k 0) _ HS HM Hin); [|apply u64_range | lia].
rewrite denot_off0, (E_E_reg k r Hk). symmetry. apply Z_to_bv_bv_unsigned. }
split; [exact FR|].
split.
{ intros a Ha. destruct (Z_lt_le_dec a (sp - ENTRY_FRAME)) as [Hlo|Hge].
- apply (apresent_same (w_H W) mem); [|apply Hpres; exact Ha].
apply FR. rewrite unsigned_lit_small by (unfold ENTRY_STK, ENTRY_FRAME, YGAlloc.AFSTACK_G, kHighMemBeg, kHighMemEnd in *; lia). lia.
- apply (st_window_present E_E ss ms (w_H W) _ a HS HM).
+ cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite E2. lia.
+ rewrite IMG_TOP_val. unfold ENTRY_STK, ENTRY_FRAME, YGAlloc.AFSTACK_G, kHighMemBeg, kHighMemEnd in *. lia. }
split; [replace (sp - 8) with (sp + -8) by lia; exact (CV (-8) 1%nat 1%bv eq_refl ltac:(cbn; tauto))|].
split; [replace (sp - 16) with (sp + -16) by lia; exact (CV (-16) 8%nat 8%bv eq_refl ltac:(cbn; tauto))|].
split; [replace (sp - 24) with (sp + -24) by lia; exact (CV (-24) 9%nat 9%bv eq_refl ltac:(cbn; tauto))|].
split; [replace (sp - 32) with (sp + -32) by lia; exact (CV (-32) 18%nat 18%bv eq_refl ltac:(cbn; tauto))|].
replace (sp - 40) with (sp + -40) by lia; exact (CV (-40) 19%nat 19%bv eq_refl ltac:(cbn; tauto)).
Qed.

(* Item 1-3: the prologue, the size test (both arms; the overflow branch refuted from the room premise), the product
   and the arguments, to Allocate's entry. *)
Lemma walk_A : SRr decodesegs0 W (cfg_at decodesegs0 DEC_A_asan_calloc regs mem md) at_alloc.
Proof.
pose proof decode_wx as Hwx. pose proof SEED_E as HS. pose proof E_E2 as E2.
destruct Hroom as (Hn0 & Hs0 & Hns). pose proof (calloc_prod_mod nm sz Hn0 Hs0 Hns) as [Hp Hr].
assert (U10 : U E_E (SOff 10 0) = nm mod 2 ^ 64).
{ rewrite U_SOff, (E_E_reg 10 10%bv eq_refl), Hnm, Z.add_0_r. unfold w64, zcanon, M64. rewrite lit64_unsigned. apply Z.mod_mod. lia. }
assert (U11 : U E_E (SOff 11 0) = sz mod 2 ^ 64).
{ rewrite U_SOff, (E_E_reg 11 11%bv eq_refl), Hsz, Z.add_0_r. unfold w64, zcanon, M64. rewrite lit64_unsigned. apply Z.mod_mod. lia. }
unfold cfg_at.
srr_run_to_sh tbl_calloc_A_ok HS DEC_A_allocate.
srr_branch_sh tbl_calloc_A_ok HS.
- srr_run_to_sh tbl_calloc_A_ok HS DEC_A_allocate.
apply SRr_ret. eapply close_A; [exact HS | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity |].
intros x Hx. rewrite (frame_sp _ _ _ HF0 ltac:(vm_compute; repeat constructor; discriminate) x Hx).
exact (frame_sp _ _ _ HF ltac:(vm_compute; repeat constructor; discriminate) x Hx).
- srr_run_to_sh tbl_calloc_A_ok HS DEC_A_allocate.
srr_branch_sh tbl_calloc_A_ok HS.
+ exfalso. rewrite branch_ne_U, U_SMd in Hc0. cbn [zmd_raw] in Hc0. rewrite U10, U11, Hp in Hc0.
rewrite Z.shiftr_div_pow2, Z.div_small in Hc0 by lia. rewrite U_SLit in Hc0. vm_compute in Hc0. discriminate.
+ srr_run_to_sh tbl_calloc_A_ok HS DEC_A_allocate.
apply SRr_ret. eapply close_A; [exact HS | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity |].
intros x Hx. rewrite (frame_sp _ _ _ HF1 ltac:(vm_compute; repeat constructor; discriminate) x Hx).
rewrite (frame_sp _ _ _ HF0 ltac:(vm_compute; repeat constructor; discriminate) x Hx).
exact (frame_sp _ _ _ HF ltac:(vm_compute; repeat constructor; discriminate) x Hx).
Qed.
End a.
End d.

(* ================================================================================================================
   Generic facts used after Allocate returns. *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* An amreal run whose every leaf continues by an SRr run to a second leaf realizes the same tree to the second
   leaf: the leaf of [amreal] at a [IRet] is an SRr, and the continuation is bound there. *)
Lemma amreal_post_SRr {R} : forall segs (t : itree astate R) W c (P Q : R -> world segs -> config -> Prop),
amreal segs t W c P -> (forall r W' c', P r W' c' -> SRr segs W' c' (Q r)) -> amreal segs t W c Q.
Proof.
intros segs t. induction t as [r | q s k IH | pc | f]; intros W c P Q H HQ; cbn in *.
- eapply SRr_bind; [exact H | intros W' c' _ HP; exact (HQ r W' c' HP)].
- eapply SRr_mono; [exact H |]. intros W1 c1 _ Hk. destruct q;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc); exists J, nx, bit, sp, i0;
split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|]; split; [exact Hr|];
split; [exact Hz|]; intros i Hi; eapply IH; [apply Hc, Hi | exact HQ]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. eapply IH; [exact Hc | exact HQ].
- exact H.
- exact I.
Qed.

Lemma aview_eq_of_mem : forall (H : word -> bool) (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview decodesegs0 H m' a = aview decodesegs0 H m a.
Proof. intros H m m' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.
Lemma aview_mod : forall (H : word -> bool) (m : word -> option byte) a,
aview decodesegs0 H m a = aview decodesegs0 H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte.
assert (E : Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a).
{ apply bv_eq. rewrite !lit64_unsigned. apply Z.mod_mod. lia. }
rewrite E. reflexivity.
Qed.
Lemma mbyte_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a,
aview decodesegs0 H' m' a = aview decodesegs0 H m a ->
mbyte decodesegs0 (mrestrict H' m') a = mbyte decodesegs0 (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (mbyte decodesegs0 (mrestrict H' m') a) as [b'|], (mbyte decodesegs0 (mrestrict H m) a) as [b|];
cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma val_mem_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a n v,
(forall k, (k < n)%nat -> aview decodesegs0 H' m' (a + Z.of_nat k) = aview decodesegs0 H m (a + Z.of_nat k)) ->
val_mem decodesegs0 (mrestrict H m) a n v -> val_mem decodesegs0 (mrestrict H' m') a n v.
Proof. intros H H' m m' a n v E Hv k Hk. rewrite (mbyte_of_aview H H' m m' _ (E k Hk)). exact (Hv k Hk). Qed.
Lemma aview_of_apresent : forall (H : word -> bool) (m : word -> option byte) a,
apresent H m a -> aview decodesegs0 H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.
Lemma apresent_writable : forall (H : word -> bool) (m : word -> option byte) a,
apresent H m a -> writable_at decodesegs0 (mrestrict H m) a.
Proof. intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate. Qed.
Lemma apresent_of_aview_high : forall (H : word -> bool) (m : word -> option byte) a,
IMG_TOP <= a < 2 ^ 64 -> aview decodesegs0 H m a <> None -> apresent H m a.
Proof.
intros H m a Ha Hv. pose proof IMG_TOP_val as HT.
assert (HF : find_segment decodesegs0 (bv_unsigned (Z_to_bv 64 a)) 1 = None).
{ rewrite (unsigned_lit_small a) by lia. exact (find_segment_above decodesegs0 a segs_in_asan (proj1 Ha)). }
assert (HR : seg_rom decodesegs0 (Z_to_bv 64 a) = None) by (unfold seg_rom, memory_read; cbn [Z.of_N]; rewrite HF; reflexivity).
unfold aview, mbyte, mrestrict in Hv. unfold apresent. rewrite HR in Hv.
destruct (H (Z_to_bv 64 a)) eqn:Hh; [exfalso; apply Hv; reflexivity|].
split; [reflexivity|]. destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; apply Hv; reflexivity].
Qed.
(* A request of at most 64512 bytes is a primary one.  Ported from cgif A/AFij.v:38-49 (prim_fp). *)
Lemma prim_fp : forall n, 0 <= n <= PRIM_MAX -> from_primary n = true.
Proof.
intros n Nrange. unfold PRIM_MAX in Nrange.
unfold from_primary, needed_primary, rounded_size, round_up, rz_size, rz_log, kMaxSize. apply Z.leb_le.
pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)) as M.
destruct (Z.leb_spec n 48); [change (Z.shiftl 16 0) with 16; lia|].
destruct (Z.leb_spec n 96); [change (Z.shiftl 16 1) with 32; lia|].
destruct (Z.leb_spec n 448); [change (Z.shiftl 16 2) with 64; lia|].
destruct (Z.leb_spec n 3968); [change (Z.shiftl 16 3) with 128; lia|].
destruct (Z.leb_spec n 16128); [change (Z.shiftl 16 4) with 256; lia|].
destruct (Z.leb_spec n 32256); [change (Z.shiftl 16 5) with 512; lia|].
destruct (Z.leb_spec n 64512); [change (Z.shiftl 16 6) with 1024; lia|]. lia.
Qed.
(* A primary block of the block table lies in the primary space [ly_space ly, ly_space ly + 2 ^ 37), which ends
   below 2 ^ 64: the chunk facts of the allocator relation (YG0s.v:240 chunk_facts) place a PPrim chunk of class
   c <= 30 at region_base ly c + x with x + class_size c <= 2 ^ 31, and a request with from_primary true is never
   a PSec chunk. *)
Lemma prim_block_in_space : forall B ly S W mem md p n,
AR decodesegs0 B ly S W mem md -> In (p, n) (blocks S) -> from_primary n = true ->
0 <= ly_space ly /\ ly_space ly <= sptr_addr B ly p /\ sptr_addr B ly p < ly_space ly + PRIM_SPACE_SIZE /\
ly_space ly + PRIM_SPACE_SIZE < 2 ^ 64.
Proof.
intros B ly S W mem md p n HAR Hin Hp.
pose proof (am_layout _ _ _ _ (proj1 HAR)) as LO.
pose proof (lo_space_in _ LO) as [S1 S2]. pose proof (lo_high _ LO) as [H1 H2].
pose proof (@ASAN_CEIL_range rc) as [[CR1 CR2] _].
unfold in_high, kSpaceSize, kPrimResvSize, kHighMemBeg in *.
apply YG04.In_blocks in Hin as (k & Hk & _ & Hu & Hq).
pose proof (YG0s.chunk_facts B ly S _ k (proj1 HAR) Hk) as (_ & _ & _ & G4 & G5 & _ & G7 & G8 & GG).
rewrite Hu in G4. rewrite Hq in G7, G8, GG.
assert (RQ : 1 <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
destruct (ck_beg k) as [|off|r o|c q] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. set (x := off - region_off (prim_class off)) in *. set (c := prim_class off) in *.
destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Ga1 & Ga2).
unfold region_base in Gbase. rewrite (YG0s.region_off_eq c) in Gbase by lia.
rewrite G4, Gbase. unfold PRIM_SPACE_SIZE, kFreeArrayOffset in *. lia.
- destruct GG as (_ & Hf & _). rewrite Hf in Hp. discriminate.
Qed.
(* The cells the allocator relation pins: a [c8] cell of [as_const] reads its value at its address. *)
Lemma const_cell_val : forall B ly S W mem md e e',
AR decodesegs0 B ly S W mem md -> In (c8 e e') (as_const B ly) ->
val_mem decodesegs0 (mrestrict (w_H W) mem) (aeval B ly e) 8 (aeval B ly e').
Proof.
intros B ly S W mem md e e' HAR Hin.
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ (proj1 HAR)) _ Hin) as Hc.
unfold cell_holds, c8 in Hc. cbn [c_at YG0f.c_val c_w] in Hc.
intros k Hk. specialize (Hc k Hk). unfold aview in Hc.
destruct (mbyte decodesegs0 (mrestrict (w_H W) mem) (aeval B ly e + Z.of_nat k)) as [b|]; [|discriminate].
injection Hc as Hc. unfold YO0f.le_byte, YG0f.le_byte in *. rewrite <- Hc. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma same_io_trans : forall md1 md2 md3, same_io md1 md2 -> same_io md2 md3 -> same_io md1 md3.
Proof. intros md1 md2 md3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold same_io. rewrite B1, B2, B3, B4. auto. Qed.
Lemma same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. unfold same_io. cbn. auto. Qed.
Lemma same_io_sbm : forall md md', same_but_materialized md md' -> same_io md md'.
Proof. intros md md' H. rewrite (same_but_materialized_wvb md md' H). apply same_io_wvb. Qed.
Lemma lit_region_ok : forall E (m : word -> option byte) a v e,
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
val_mem decodesegs0 m a 8 v ->
YP09.region_ok decodesegs0 E m (YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 e)]).
Proof.
intros E m a v e He Hv Ha Ha8 Hm. unfold YP09.region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. apply (chunk_ok_val decodesegs0 E m 0 a 8 e v He); [exact Hv | lia | exact Hm].
Qed.

Lemma bv_ne0 : forall r : bv 5, bv_unsigned r <> 0 -> r <> 0%bv.
Proof. intros r Hr Hc. subst r. apply Hr. reflexivity. Qed.

End g.

(* ================================================================================================================
   The walk over the two contracts. *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis ALLOC : decode_aalloc_A B.
Hypothesis FILL : decode_zero_fill_spec_A B.
Hypothesis LAWS : AR_laws decodesegs0 B.
(* IMG_CONST: the image's constant cells the walk reads, as cells of the allocator relation's constant list: the
   fill pointer's two words (0x98d60 holds 0x9abc0, 0x9abc0 holds musl memset 0x92474; read at 0x31c44 / 0x31c48)
   and the allocator instance's space-base word (as_inst B + o_space holds ly_space ly; read at 0x31c2c).  The first
   two are stated at image addresses (ANum), the third in the record's own form (lib/A/AF0m.v Tfib_const_sym
   `c8 (AInst o_space) (ASp 0)`, cgif's A/AF0m.v:27).  lib/A/DecodeARows.v dec_a_img_const proves all three from
   the symbol record (GrantSyms: ts_const). *)
Hypothesis IMG_CONST : forall ly,
In (z8 (ANum DEC_A_got_real_memset) DEC_A_real_memset) (as_const B ly) /\
In (z8 (ANum DEC_A_real_memset) DEC_A_memset) (as_const B ly) /\
In (c8 (AInst o_space) (ASp 0)) (as_const B ly).
(* HINST: B's allocator instance is __asan::instance at 0x9d758 (DecodeCalloc.v DEC_A_instance; asan_calloc forms
   it at 0x31c00 `auipc a0, 0x6c` + 0x31c08 `addi s2, a0, -1192`), so the third IMG_CONST cell is the word at
   DEC_A_space_cell = 0x9d778.  lib/A/DecodeARows.v dec_a_inst proves it from the symbol record (ts_inst). *)
Hypothesis HINST : as_inst B = DEC_A_instance.
Hypothesis ERRNO_LOW : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd.

Local Abbreviation apre := (YGAlloc.alloc_pre decodesegs0 B (fun tr _ => In tr (as_universe B)) (ARX_cgif decodesegs0 B DEC_A_instance)
rpre_cgif MALLOC_MAX LIVE_MAX ALLOC_ALIGN AT_FROM_MALLOC CF_CALLOC DEC_A_instance).
Local Abbreviation aleaf := (YGAlloc.alloc_leaf decodesegs0 B malloc (ARX_cgif decodesegs0 B DEC_A_instance) (aowned B)
qtight DEC_A_oom DEC_A_instance).

(* The state at asan_calloc's entry: the allocator relation and the call premises of Allocate's contract, with the
   stack window [sp - 0x30 - 4096, sp) present, a0 = nm, a1 = sz, a2 = the trace object above sp with its buffer
   pointer, its length and the trace, the room premises of the calloc contract (YGCalloc.v acalloc_realizesP), and
   nm * sz <= PRIM_MAX: every request is a primary one (YGCalloc.v acalloc_of_allocateP's cmax <= PRIM_MAX). *)
Definition entry_pre (ly : alayout) (S : astate) (W : world decodesegs0) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (nm sz so bp : Z) (tr : list Z) : Prop :=
AR decodesegs0 B ly S W mem md /\ aregime S /\ qmeter S /\
YK0s.ret_ok (YK11.getr regs 1) /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + ENTRY_STK <= spZ regs /\ ly_bot ly < spZ regs - ENTRY_FRAME /\
spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - ENTRY_STK <= a < spZ regs -> apresent (w_H W) mem a) /\
YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
YK11.getr regs 10 = w64 nm /\ YK11.getr regs 11 = w64 sz /\ YK11.getr regs 12 = w64 so /\
spZ regs <= so /\ so + 16 <= ly_stk_hi ly /\ so mod 8 = 0 /\
spZ regs <= bp /\ bp + 8 * 30 <= ly_stk_hi ly /\ bp mod 8 = 0 /\
(1 <= length tr <= 30)%nat /\
val_mem decodesegs0 (mrestrict (w_H W) mem) so 8 bp /\
val_mem decodesegs0 (mrestrict (w_H W) mem) (so + 8) 8 (Z.of_nat (length tr)) /\
(forall i, (i < length tr)%nat -> val_mem decodesegs0 (mrestrict (w_H W) mem) (bp + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
In tr (as_universe B) /\
0 <= nm /\ 0 <= sz /\ nm * sz < MALLOC_MAX /\ nm * sz <= PRIM_MAX /\ blocks_bytes S + nm * sz <= LIVE_MAX.

(* The leaf at the caller's return address: Allocate's leaf at n (YGAlloc.v alloc_leaf, with asan_calloc's 48-byte
   frame added to the scratch window), the block not NULL, and its n user bytes reading 0 (YGCalloc.v calloc_zeroed). *)
Definition entry_leaf (ly : alayout) (S : astate) (W : world decodesegs0) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z) (tr : list Z)
(r : sptr * astate) (W' : world decodesegs0) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at decodesegs0 (raZ regs) regs' mem' md' /\
AR decodesegs0 B ly' (snd r) W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ wle W W' /\
aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' (snd r) a -> ~ ascratch B ENTRY_STK regs a ->
~ (fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n) ->
aview decodesegs0 (w_H W') mem' a = aview decodesegs0 (w_H W) mem a) /\
(forall a, spZ regs - ENTRY_STK <= a < spZ regs -> apresent (w_H W') mem' a) /\
YK11.getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
qtight (snd r) /\
(exists trc, apath (malloc n tr S) trc r /\ gflag trc = true) /\
fst r <> PNull /\
(forall i, 0 <= i < n -> aview decodesegs0 (w_H W') mem' (sptr_addr B ly' (fst r) + i) = Some 0).

(* The allocator relation survives a change of the memory in a stack window it does not own, and the model's
   materialization step of a run (AR_frame_law). *)
Lemma AR_frame_wvb : forall ly S W mem mem' md X lo hi,
AR decodesegs0 B ly S W mem md -> 0 <= lo -> hi <= 2 ^ 64 ->
(forall x : word, ~ (lo <= bv_unsigned x < hi) -> mem' x = mem x) ->
(forall a, lo <= a < hi -> ly_stk_lo ly <= a < ly_stk_hi ly /\ apresent (w_H W) mem a /\ apresent (w_H W) mem' a) ->
AR decodesegs0 B ly S W mem' (with_vm_backing (m_vm_lazy md) X md).
Proof.
intros ly S W mem mem' md X lo hi HAR Hlo Hhi Hfr Hin.
apply (al_frame _ _ LAWS ly S W mem md mem' _ HAR).
- intros a Ha Hown. destruct (Z_lt_le_dec a lo) as [H1|H1]; [|destruct (Z_lt_le_dec a hi) as [H2|H2]].
+ apply aview_eq_of_mem. apply Hfr. rewrite unsigned_lit_small by lia. lia.
+ exfalso. destruct (Hin a ltac:(lia)) as (Hs & _ & _). exact (al_stack _ _ LAWS ly S W mem md a HAR Hs Hown).
+ apply aview_eq_of_mem. apply Hfr. rewrite unsigned_lit_small by lia. lia.
- intros a Hv. rewrite aview_mod. rewrite aview_mod in Hv.
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hm.
destruct (Z_lt_le_dec (a mod 2 ^ 64) lo) as [H1|H1]; [|destruct (Z_lt_le_dec (a mod 2 ^ 64) hi) as [H2|H2]].
+ rewrite aview_eq_of_mem with (m := mem); [exact Hv|]. apply Hfr. rewrite unsigned_lit_small by lia. lia.
+ destruct (Hin (a mod 2 ^ 64) ltac:(lia)) as (_ & _ & Hp). exact (aview_of_apresent _ _ _ Hp).
+ rewrite aview_eq_of_mem with (m := mem); [exact Hv|]. apply Hfr. rewrite unsigned_lit_small by lia. lia.
- reflexivity.
- apply m_vm_lazy_wvb.
- unfold eager_used. rewrite m_vm_lazy_wvb. reflexivity.
- intros a Hband Hh. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hband.
destruct (Z_lt_le_dec a lo) as [H1|H1]; [|destruct (Z_lt_le_dec a hi) as [H2|H2]].
+ apply Hfr. unfold w64. rewrite unsigned_lit_small by lia. lia.
+ exfalso. destruct (Hin a ltac:(lia)) as (_ & [Hf _] & _). unfold w64 in Hh. rewrite Hf in Hh. discriminate.
+ apply Hfr. unfold w64. rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma AR_wvb : forall ly S W mem md X,
AR decodesegs0 B ly S W mem md -> AR decodesegs0 B ly S W mem (with_vm_backing (m_vm_lazy md) X md).
Proof.
intros ly S W mem md X HAR. apply (AR_frame_wvb ly S W mem mem md X 0 0 HAR); [lia | lia | intros; reflexivity | intros a Ha; lia].
Qed.

(* The environment of the walk after Allocate returns: the registers of that point, then the word at
   instance + 0x20 and the five registers asan_calloc's prologue saved (ra, s0, s1, s2, s3 at its entry). *)
Definition E_X (regs regsB : bvmap 5 word) (P : Z) : env :=
Ereg regsB [w64 P; YK11.getr regs 1; YK11.getr regs 8; YK11.getr regs 9; YK11.getr regs 18; YK11.getr regs 19].

Definition R_SAVED : YP09.region := YP09.mkRegion (Some 2%nat) 0 ENTRY_FRAME 0 0
[YP09.mkChunk 8 (CVal 8 (SOff 37 0)); YP09.mkChunk 16 (CVal 8 (SOff 36 0)); YP09.mkChunk 24 (CVal 8 (SOff 35 0));
YP09.mkChunk 32 (CVal 8 (SOff 34 0)); YP09.mkChunk 40 (CVal 8 (SOff 33 0))].
Definition lit8r (a v : Z) : YP09.region := YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 (SLit v))].
Definition REG_C : smem :=
[R_SAVED; YP09.mkRegion None DEC_A_space_cell (DEC_A_space_cell + 8) 0 0 [YP09.mkChunk DEC_A_space_cell (CVal 8 (SOff 32 0))];
lit8r DEC_A_got_real_memset DEC_A_real_memset; lit8r DEC_A_real_memset DEC_A_memset].
Definition FG_C : facts := mkFacts [(2%nat, mkAF (kHighMemBeg + YGAlloc.AFSTACK_G) kHighMemEnd 4)] [] [].
Definition SR_C : list sv := sr_set (sr_set sr_atoms 18%bv (SLit DEC_A_instance)) 19%bv (SLit 1).
Definition SS_C : sstate := mkSS DEC_A_calloc_alloc_ret SR_C REG_C None FG_C.
Definition SS_D : sstate := mkSS DEC_A_calloc_fill_ret sr_atoms [R_SAVED] None FG_C.

Section x.
Variables (regs regsB : bvmap 5 word) (P : Z).
Lemma EX_lo (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew (E_X regs regsB P) k = YK11.getr regsB r.
Proof. intros Hk. exact (ew_Ereg_nat regsB _ k r Hk). Qed.
Lemma EX_32 : ew (E_X regs regsB P) 32 = w64 P. Proof. reflexivity. Qed.
Lemma EX_33 : ew (E_X regs regsB P) 33 = YK11.getr regs 1. Proof. reflexivity. Qed.
Lemma EX_34 : ew (E_X regs regsB P) 34 = YK11.getr regs 8. Proof. reflexivity. Qed.
Lemma EX_35 : ew (E_X regs regsB P) 35 = YK11.getr regs 9. Proof. reflexivity. Qed.
Lemma EX_36 : ew (E_X regs regsB P) 36 = YK11.getr regs 18. Proof. reflexivity. Qed.
Lemma EX_37 : ew (E_X regs regsB P) 37 = YK11.getr regs 19. Proof. reflexivity. Qed.

Lemma R_SAVED_ok : forall (m : word -> option byte),
let b := bv_unsigned (YK11.getr regsB 2) in
b + ENTRY_FRAME <= 2 ^ 64 ->
val_mem decodesegs0 m (b + 40) 8 (raZ regs) ->
val_mem decodesegs0 m (b + 32) 8 (bv_unsigned (YK11.getr regs 8)) ->
val_mem decodesegs0 m (b + 24) 8 (bv_unsigned (YK11.getr regs 9)) ->
val_mem decodesegs0 m (b + 16) 8 (bv_unsigned (YK11.getr regs 18)) ->
val_mem decodesegs0 m (b + 8) 8 (bv_unsigned (YK11.getr regs 19)) ->
YP09.region_ok decodesegs0 (E_X regs regsB P) m R_SAVED.
Proof.
intros m b Hb V40 V32 V24 V16 V8.
assert (E2 : bv_unsigned (ew (E_X regs regsB P) 2) = b) by (rewrite (EX_lo 2 2%bv eq_refl); reflexivity).
pose proof (u64_range (YK11.getr regsB 2)) as Hr.
unfold YP09.region_ok, R_SAVED. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E2. split; [fold b in Hr; lia|]. split; [unfold ENTRY_FRAME in *; lia|]. split; [intros o Ho; lia|].
assert (CK : forall off (k : nat) (w : word), ew (E_X regs regsB P) k = w ->
val_mem decodesegs0 m (b + off) 8 (bv_unsigned w) -> YP09.chunk_ok decodesegs0 (E_X regs regsB P) m b (YP09.mkChunk off (CVal 8 (SOff k 0)))).
{ intros off k w Hk Hv. apply (chunk_ok_val decodesegs0 _ _ b off 8 (SOff k 0) (bv_unsigned w)).
- rewrite denot_off0, Hk. symmetry. apply Z_to_bv_bv_unsigned.
- apply u64_range.
- lia.
- exact Hv. }
constructor; [exact (CK 8 37%nat _ EX_37 V8)|].
constructor; [exact (CK 16 36%nat _ EX_36 V16)|].
constructor; [exact (CK 24 35%nat _ EX_35 V24)|].
constructor; [exact (CK 32 34%nat _ EX_34 V32)|].
constructor; [exact (CK 40 33%nat _ EX_33 V40)|].
constructor.
Qed.
End x.

Lemma getr_lit : forall (rg : bvmap 5 word) (k : Z) (r : bv 5), bv_unsigned r = k -> YK11.getr rg (Z_to_bv 5 k) = YK11.getr rg r.
Proof. intros rg k r Hk. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- Hk. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Section i.
Variables (ly : alayout) (S : astate) (W : world decodesegs0) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (nm sz so bp : Z) (tr : list Z).
Hypothesis PRE : entry_pre ly S W regs mem md nm sz so bp tr.
Let sp : Z := spZ regs.
Let n : Z := nm * sz.

Local Ltac pre := pose proof PRE as (HAR & Hreg & Hqm & Hra & Hal & Hslo & Hbot & Hshi & Hpres & Hgp & Htp & Hnm & Hsz & Hso
& Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Hlen & Hv1 & Hv2 & Hv3 & Htr & Hn0 & Hs0 & Hns & Hpm & Hlive).

Lemma pre_layout : layout_ok ly.
Proof. pre. exact (am_layout _ _ _ _ (proj1 HAR)). Qed.
Lemma pre_sp : kHighMemBeg + ENTRY_STK <= sp <= kHighMemEnd /\ ly_stk_lo ly + ENTRY_STK <= sp /\ sp <= ly_stk_hi ly /\
sp mod 16 = 0 /\ alloc_ceiling <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly.
Proof.
pre. pose proof pre_layout as LY. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (lo_stk_ceil ly LY) as C. unfold ASAN_CEIL in C. unfold sp. repeat split; lia.
Qed.
Lemma pre_n : 0 <= n < 2 ^ 28.
Proof. pre. exact (proj2 (calloc_prod_mod nm sz Hn0 Hs0 Hns)). Qed.

(* Part 1: from the entry to Allocate's entry. *)
Lemma walk_to_alloc : SRr decodesegs0 W (cfg_at decodesegs0 DEC_A_asan_calloc regs mem md) (at_alloc W regs mem md nm sz so).
Proof.
pre. pose proof pre_sp as (SP1 & SP2 & SP3 & SP4 & SP5 & SP6 & SP7).
apply walk_A; [exact SP1 | exact Hal | exact Hpres | exact Hnm | exact Hsz | exact Hso | split; [exact Hn0 | split; [exact Hs0 | exact Hns]]].
Qed.

(* Part 2: Allocate's precondition at its entry. *)
Lemma alloc_pre_of : forall regs1 mem1 mat, A_regs regs nm sz so regs1 -> A_mem W regs mem mem1 ->
apre so bp ly S W regs1 mem1 (with_vm_backing (m_vm_lazy md) mat md) n tr.
Proof.
intros regs1 mem1 mat HR HM. pre. pose proof pre_sp as (SP1 & SP2 & SP3 & SP4 & SP5 & SP6 & SP7). pose proof pre_n as PN.
destruct HR as (R1 & R2 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R18 & R19 & Rp).
destruct HM as (MF & MP & _).
unfold ENTRY_STK, ENTRY_FRAME, YGAlloc.AFSTACK_G, kHighMemBeg, kHighMemEnd in SP1, SP6, SP7.
assert (S1 : spZ regs1 = sp - ENTRY_FRAME).
{ unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. unfold ENTRY_STK, ENTRY_FRAME, YGAlloc.AFSTACK_G, kHighMemBeg, kHighMemEnd in *. lia. }
assert (VT : forall a k v, sp <= a -> a + Z.of_nat k <= 2 ^ 64 ->
val_mem decodesegs0 (mrestrict (w_H W) mem) a k v -> val_mem decodesegs0 (mrestrict (w_H W) mem1) a k v).
{ intros a k v Ha Hk. apply val_mem_of_aview. intros j Hj. apply aview_eq_of_mem. apply MF.
rewrite unsigned_lit_small by lia. lia. }
assert (KS : ly_stk_hi ly <= kHighMemEnd) by exact SP6.
unfold YGAlloc.alloc_pre.
split.
{ split; [reflexivity|]. apply (AR_frame_wvb ly S W mem mem1 md mat (sp - ENTRY_FRAME) sp HAR).
- unfold ENTRY_STK, ENTRY_FRAME, YGAlloc.AFSTACK_G, kHighMemBeg in *. lia.
- unfold kHighMemEnd in *. lia.
- exact MF.
- intros a Ha. split; [unfold ENTRY_STK, ENTRY_FRAME, YGAlloc.AFSTACK_G in *; lia|].
split; [apply Hpres | apply MP]; unfold ENTRY_STK, ENTRY_FRAME, YGAlloc.AFSTACK_G in *; lia. }
split; [split; [exact Hreg | exact Hqm]|].
split; [rewrite R1; apply ret_ok_even; vm_compute; reflexivity|].
split; [unfold raZ; rewrite R1; vm_compute; discriminate|].
split; [rewrite S1; unfold ENTRY_FRAME; replace (sp - 0x30) with (sp + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
split; [rewrite S1; unfold ENTRY_STK, ENTRY_FRAME, YGAlloc.AFSTACK_G in *; lia|].
split; [rewrite S1; exact Hbot|].
split; [rewrite S1; unfold ENTRY_FRAME; lia|].
split; [intros a Ha; rewrite S1 in Ha; apply MP; unfold ENTRY_STK, ENTRY_FRAME, YGAlloc.AFSTACK_G in *; lia|].
split; [rewrite <- (getr_lit regs1 3 3%bv eq_refl), (Rp 3 (or_introl eq_refl)), (getr_lit regs 3 3%bv eq_refl); exact Hgp|].
split; [rewrite <- (getr_lit regs1 4 4%bv eq_refl), (Rp 4 (or_intror (or_introl eq_refl))), (getr_lit regs 4 4%bv eq_refl); exact Htp|].
split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|]. split; [exact R14|]. split; [exact R15|].
split; [rewrite S1; unfold ENTRY_FRAME; lia|]. split; [exact Hso2|]. split; [exact Hso3|].
split; [rewrite S1; unfold ENTRY_FRAME; lia|]. split; [exact Hbp2|]. split; [exact Hbp3|].
split; [exact Hlen|].
split; [apply VT; [lia | cbn; unfold kHighMemEnd in *; lia | exact Hv1]|].
split; [apply VT; [lia | cbn; unfold kHighMemEnd in *; lia | exact Hv2]|].
split; [intros i Hi; apply VT; [lia | cbn; unfold kHighMemEnd in *; lia | exact (Hv3 i Hi)]|].
split; [exact Htr|]. split; [unfold n; lia | exact Hlive].
Qed.

(* Part 3: the seeds after Allocate and after the fill, and the return. *)
Lemma SEED_C : forall (W2 : world decodesegs0) regsB memB P,
let b := bv_unsigned (YK11.getr regsB 2) in
kHighMemBeg + YGAlloc.AFSTACK_G <= b <= kHighMemEnd - ENTRY_FRAME -> b mod 16 = 0 ->
YK11.getr regsB 18 = w64 DEC_A_instance -> YK11.getr regsB 19 = w64 1 ->
val_mem decodesegs0 (mrestrict (w_H W2) memB) (b + 40) 8 (raZ regs) ->
val_mem decodesegs0 (mrestrict (w_H W2) memB) (b + 32) 8 (bv_unsigned (YK11.getr regs 8)) ->
val_mem decodesegs0 (mrestrict (w_H W2) memB) (b + 24) 8 (bv_unsigned (YK11.getr regs 9)) ->
val_mem decodesegs0 (mrestrict (w_H W2) memB) (b + 16) 8 (bv_unsigned (YK11.getr regs 18)) ->
val_mem decodesegs0 (mrestrict (w_H W2) memB) (b + 8) 8 (bv_unsigned (YK11.getr regs 19)) ->
0 <= P < 2 ^ 64 -> val_mem decodesegs0 (mrestrict (w_H W2) memB) DEC_A_space_cell 8 P ->
val_mem decodesegs0 (mrestrict (w_H W2) memB) DEC_A_got_real_memset 8 DEC_A_real_memset ->
val_mem decodesegs0 (mrestrict (w_H W2) memB) DEC_A_real_memset 8 DEC_A_memset ->
st_ok decodesegs0 (E_X regs regsB P) SS_C
(restrict (w_H W2) (YK11.mkst regsB (w64 DEC_A_calloc_alloc_ret) memB (YK11.seg_rom decodesegs0))).
Proof.
intros W2 regsB memB P b Hb Hal2 H18 H19 V40 V32 V24 V16 V8 HP VP VG1 VG2.
assert (E2 : bv_unsigned (ew (E_X regs regsB P) 2) = b) by (rewrite (EX_lo regs regsB P 2 2%bv eq_refl); reflexivity).
unfold kHighMemBeg, kHighMemEnd, YGAlloc.AFSTACK_G, ENTRY_FRAME in Hb.
rewrite restrict_mkst_fx. unfold SS_C, w64. apply (entry_st_ok_full decodesegs0).
- unfold SR_C. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | apply bv_ne0; vm_compute; discriminate | exact H18]
| apply bv_ne0; vm_compute; discriminate | exact H19].
- vm_compute. reflexivity.
- unfold REG_C. constructor; [apply R_SAVED_ok; [fold b; unfold ENTRY_FRAME; lia | exact V40 | exact V32 | exact V24 | exact V16 | exact V8]|].
constructor; [apply (lit_region_ok _ _ _ P); [rewrite denot_off0; exact (EX_32 regs regsB P) | exact HP | unfold DEC_A_space_cell, DEC_A_instance, DEC_A_got_real_memset, DEC_A_real_memset, DEC_A_memset; lia | unfold DEC_A_space_cell, DEC_A_instance, DEC_A_got_real_memset, DEC_A_real_memset, DEC_A_memset; lia | exact VP]|].
constructor; [apply (lit_region_ok _ _ _ DEC_A_real_memset); [reflexivity | unfold DEC_A_space_cell, DEC_A_instance, DEC_A_got_real_memset, DEC_A_real_memset, DEC_A_memset; lia | unfold DEC_A_space_cell, DEC_A_instance, DEC_A_got_real_memset, DEC_A_real_memset, DEC_A_memset; lia | unfold DEC_A_space_cell, DEC_A_instance, DEC_A_got_real_memset, DEC_A_real_memset, DEC_A_memset; lia | exact VG1]|].
constructor; [apply (lit_region_ok _ _ _ DEC_A_memset); [reflexivity | unfold DEC_A_space_cell, DEC_A_instance, DEC_A_got_real_memset, DEC_A_real_memset, DEC_A_memset; lia | unfold DEC_A_space_cell, DEC_A_instance, DEC_A_got_real_memset, DEC_A_real_memset, DEC_A_memset; lia | unfold DEC_A_space_cell, DEC_A_instance, DEC_A_got_real_memset, DEC_A_real_memset, DEC_A_memset; lia | exact VG2]|].
constructor.
- unfold REG_C, R_SAVED, lit8r. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold (E_X regs regsB P). rewrite E2.
unfold DEC_A_space_cell, DEC_A_instance, DEC_A_got_real_memset, DEC_A_real_memset, ENTRY_FRAME. repeat split; lia.
- split; [|split; exact I]. unfold FG_C. cbn [f_atoms atoms_ok]. split; [|exact I].
unfold afact_ok. cbn [af_lo af_hi af_al2]. fold (E_X regs regsB P). rewrite E2.
unfold kHighMemBeg, kHighMemEnd, YGAlloc.AFSTACK_G. split; [lia|]. split; [exact Hal2 | lia].
Qed.

Lemma SEED_D : forall (W2 : world decodesegs0) regsB memB P,
let b := bv_unsigned (YK11.getr regsB 2) in
kHighMemBeg + YGAlloc.AFSTACK_G <= b <= kHighMemEnd - ENTRY_FRAME -> b mod 16 = 0 ->
val_mem decodesegs0 (mrestrict (w_H W2) memB) (b + 40) 8 (raZ regs) ->
val_mem decodesegs0 (mrestrict (w_H W2) memB) (b + 32) 8 (bv_unsigned (YK11.getr regs 8)) ->
val_mem decodesegs0 (mrestrict (w_H W2) memB) (b + 24) 8 (bv_unsigned (YK11.getr regs 9)) ->
val_mem decodesegs0 (mrestrict (w_H W2) memB) (b + 16) 8 (bv_unsigned (YK11.getr regs 18)) ->
val_mem decodesegs0 (mrestrict (w_H W2) memB) (b + 8) 8 (bv_unsigned (YK11.getr regs 19)) ->
st_ok decodesegs0 (E_X regs regsB P) SS_D
(restrict (w_H W2) (YK11.mkst regsB (w64 DEC_A_calloc_fill_ret) memB (YK11.seg_rom decodesegs0))).
Proof.
intros W2 regsB memB P b Hb Hal2 V40 V32 V24 V16 V8.
assert (E2 : bv_unsigned (ew (E_X regs regsB P) 2) = b) by (rewrite (EX_lo regs regsB P 2 2%bv eq_refl); reflexivity).
unfold kHighMemBeg, kHighMemEnd, YGAlloc.AFSTACK_G, ENTRY_FRAME in Hb.
rewrite restrict_mkst_fx. unfold SS_D, w64. apply (entry_st_ok_full decodesegs0).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [apply R_SAVED_ok; [fold b; unfold ENTRY_FRAME; lia | exact V40 | exact V32 | exact V24 | exact V16 | exact V8]|].
constructor.
- cbn. split; exact I.
- split; [|split; exact I]. unfold FG_C. cbn [f_atoms atoms_ok]. split; [|exact I].
unfold afact_ok. cbn [af_lo af_hi af_al2]. fold (E_X regs regsB P). rewrite E2.
unfold kHighMemBeg, kHighMemEnd, YGAlloc.AFSTACK_G. split; [lia|]. split; [exact Hal2 | lia].
Qed.

(* The return to the caller and the leaf.  The run has reached the `ret` at 0x31c94 with sp, ra and s0 .. s3
   reloaded from the frame, the other callee-saved registers as at the entry, and a0 the block. *)
Lemma ret_leaf : forall P0 regsB ss ms mdF ly' r (W2 : world decodesegs0),
let E := E_X regs regsB P0 in
st_ok decodesegs0 E ss (restrict (w_H W2) ms) -> ss_pc ss = DEC_A_calloc_ret_insn -> ss_resv ss = None ->
sr_get (ss_regs ss) (Z_to_bv 5 1) = SOff 33 0 -> sr_get (ss_regs ss) (Z_to_bv 5 2) = SOff 2 ENTRY_FRAME ->
sr_get (ss_regs ss) (Z_to_bv 5 8) = SOff 34 0 -> sr_get (ss_regs ss) (Z_to_bv 5 9) = SOff 35 0 ->
sr_get (ss_regs ss) (Z_to_bv 5 18) = SOff 36 0 -> sr_get (ss_regs ss) (Z_to_bv 5 19) = SOff 37 0 ->
(forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> sr_get (ss_regs ss) (Z_to_bv 5 k) = SOff (Z.to_nat k) 0) ->
sv_denot E (sr_get (ss_regs ss) (Z_to_bv 5 10)) = w64 (sptr_addr B ly' (fst r)) ->
YK11.getr regsB 2 = w64 (sp - ENTRY_FRAME) ->
(forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> YK11.getr regsB (Z_to_bv 5 k) = YK11.getr regs (Z_to_bv 5 k)) ->
AR decodesegs0 B ly' (snd r) W2 (ms_mem ms) mdF ->
layout_le (length (st_secs S)) ly ly' -> wle W W2 -> same_io md mdF ->
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' (snd r) a -> ~ ascratch B ENTRY_STK regs a ->
~ (fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n) ->
aview decodesegs0 (w_H W2) (ms_mem ms) a = aview decodesegs0 (w_H W) mem a) ->
(forall a, sp - ENTRY_STK <= a < sp -> apresent (w_H W2) (ms_mem ms) a) ->
qtight (snd r) -> (exists trc, apath (malloc n tr S) trc r /\ gflag trc = true) -> fst r <> PNull ->
(forall i, 0 <= i < n -> aview decodesegs0 (w_H W2) (ms_mem ms) (sptr_addr B ly' (fst r) + i) = Some 0) ->
SRr decodesegs0 W2 (mkCfg ms mdF) (entry_leaf ly S W regs mem md n tr r).
Proof.
intros P0 regsB ss ms mdF ly' r W2 E HS Hpc Hrv G1 G2 G8 G9 G18 G19 Gk G10 B2 Bk HARF Hly Hwle Hio Hfr Hpr Hqt Hpath Hnn Hz.
subst E. pre. pose proof pre_sp as (SP1 & SP2 & SP3 & SP4 & SP5 & SP6 & SP7).
unfold ENTRY_STK, ENTRY_FRAME, YGAlloc.AFSTACK_G, kHighMemBeg, kHighMemEnd in SP1.
pose proof decode_wx as Hwx.
assert (RG : forall k, 0 <= k < 32 -> YK11.getr (ms_regs ms) (Z_to_bv 5 k) = sv_denot (E_X regs regsB P0) (sr_get (ss_regs ss) (Z_to_bv 5 k)))
by (intros k Hk; exact (st_ok_restrict_reg decodesegs0 (w_H W2) _ ss ms _ HS)).
apply (SRr_ret_at decodesegs0 tbl_calloc_A tbl_calloc_A_ok Hwx W2 _ ss ms mdF _ HS Hrv); [rewrite Hpc; vm_compute; reflexivity|].
intros mat'. unfold entry_leaf.
exists ly', (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdF) mat' mdF).
assert (RA : YK11.getr (ms_regs ms) 1 = YK11.getr regs 1).
{ rewrite <- (getr_lit (ms_regs ms) 1 1%bv eq_refl), (RG 1 ltac:(lia)), G1, denot_off0. reflexivity. }
split.
{ unfold cfg_at, w64, raZ. rewrite RA, Hra, Z_to_bv_bv_unsigned. reflexivity. }
split; [apply AR_wvb; exact HARF|].
split; [exact Hly|]. split; [exact Hwle|].
split.
{ intros k Hk. rewrite (RG k ltac:(unfold acallee_saved in Hk; lia)).
unfold acallee_saved in Hk.
destruct (Z.eq_dec k 2) as [->|N2].
{ rewrite G2. cbn [sv_denot]. rewrite (EX_lo regs regsB P0 2 2%bv eq_refl), B2. unfold w64.
rewrite unsigned_lit_small by (unfold ENTRY_FRAME; lia).
replace (sp - ENTRY_FRAME + ENTRY_FRAME) with sp by lia. change sp with (spZ regs). unfold spZ.
rewrite (getr_lit regs 2 2%bv eq_refl). apply Z_to_bv_bv_unsigned. }
destruct (Z.eq_dec k 8) as [->|N8]; [rewrite G8, denot_off0, EX_34; symmetry; apply getr_lit; reflexivity|].
destruct (Z.eq_dec k 9) as [->|N9]; [rewrite G9, denot_off0, EX_35; symmetry; apply getr_lit; reflexivity|].
destruct (Z.eq_dec k 18) as [->|N18]; [rewrite G18, denot_off0, EX_36; symmetry; apply getr_lit; reflexivity|].
destruct (Z.eq_dec k 19) as [->|N19]; [rewrite G19, denot_off0, EX_37; symmetry; apply getr_lit; reflexivity|].
assert (Hk' : k = 3 \/ k = 4 \/ 20 <= k <= 27) by lia.
rewrite (Gk k Hk'), denot_off0, (EX_lo regs regsB P0 (Z.to_nat k) (Z_to_bv 5 k)).
- exact (Bk k Hk').
- rewrite Z_to_bv_unsigned, Z2Nat.id by lia. rewrite bv_wrap_small; [reflexivity|]. unfold bv_modulus. cbn. lia. }
split; [exact (same_io_trans _ _ _ Hio (same_io_wvb mdF _ _))|].
split; [exact Hfr|]. split; [exact Hpr|].
split; [rewrite <- (getr_lit (ms_regs ms) 10 10%bv eq_refl), (RG 10 ltac:(lia)); exact G10|].
split; [exact Hqt|]. split; [exact Hpath|]. split; [exact Hnn | exact Hz].
Qed.

Local Ltac gk_tac :=
let k := fresh "k" in let Hk := fresh "Hk" in let Hc := fresh "Hc" in
intros k Hk; assert (Hc : k = 3 \/ k = 4 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia;
repeat (destruct Hc as [->|Hc]; [vm_compute; reflexivity|]); subst k; vm_compute; reflexivity.
Local Ltac sr_eval :=
lazymatch goal with |- context [sr_get ?sr ?rr] => let t := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with t end.
Local Ltac cs_tac :=
unfold acallee_saved; match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.
Local Ltac sr_goal :=
lazymatch goal with |- sr_get _ _ = _ => vm_compute; reflexivity | |- ss_pc _ = _ => reflexivity | |- ss_resv _ = _ => reflexivity end.
Local Ltac mem_eqs :=
repeat match goal with H : frame_of _ _ (mrestrict _ _) _ |- _ => clear H end;
repeat match goal with H : frame_of _ ?rs ?m ?m' |- _ => apply frame_of_read_only in H; [|vm_compute; reflexivity] end.

(* Part 4: from Allocate's return to the return of asan_calloc. *)
Lemma post_alloc : forall regs1 mem1 mat r W2 c2,
A_regs regs nm sz so regs1 -> A_mem W regs mem mem1 ->
aleaf ly S W regs1 mem1 (with_vm_backing (m_vm_lazy md) mat md) n tr r W2 c2 ->
SRr decodesegs0 W2 c2 (entry_leaf ly S W regs mem md n tr r).
Proof.
intros regs1 mem1 mat r W2 c2 HR HM HL.
pre. pose proof pre_sp as (SP1 & SP2 & SP3 & SP4 & SP5 & SP6 & SP7). pose proof pre_n as PN.
unfold sp in *.
unfold ENTRY_STK, ENTRY_FRAME, YGAlloc.AFSTACK_G, kHighMemBeg, kHighMemEnd in SP1, SP2, SP6, SP7.
pose proof ERRNO_LOW as (EL1 & EL2). unfold kLowMemEnd in EL2.
pose proof (proj1 (@ASAN_CEIL_range rc)) as AC. unfold ASAN_CEIL in AC.
pose proof HR as (R1 & R2 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R18 & R19 & Rp).
pose proof HM as (MF & MP & MVra & MVs0 & MVs1 & MVs2 & MVs3).
destruct HL as (ly' & regs2 & mem2 & md2 & Hc2 & HPOST & Ha0 & Hqt & Hpath & _).
destruct HPOST as ((_ & HAR2) & Hly & Hwle & Hpr & Hio & Hfr & _ & Hpres2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (S1 : spZ regs1 = spZ regs - 48).
{ unfold spZ in *. rewrite R2. unfold w64, ENTRY_FRAME. apply unsigned_lit_small. lia. }
assert (RA1 : raZ regs1 = DEC_A_calloc_alloc_ret).
{ unfold raZ. rewrite R1. unfold w64. apply unsigned_lit_small. unfold DEC_A_calloc_alloc_ret. lia. }
rewrite RA1 in Hc2. subst c2.
(* The model: the block is not NULL and is the new entry of the block table. *)
destruct (calloc_model_of_AR _ _ _ _ _ _ _ HAR) as [HU HWf].
pose proof (calloc_nonnull _ S nm sz tr r HU HWf Hreg Hn0 Hs0 Hns Hlive Htr Hpath) as Hnn.
destruct (calloc_block_table _ S nm sz tr r HU HWf Hreg Hn0 Hs0 Hns Hlive Htr Hpath) as (Hbl & _ & _).
set (addr := sptr_addr B ly' (fst r)) in *.
assert (HIn : In (addr, n) (ablocks B ly' (snd r))).
{ unfold ablocks. rewrite Hbl, map_app. apply in_or_app. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly' (snd r) W2 mem2 md2 addr n HAR2 HIn) as (Ba16 & Ba4096 & Bceil & _ & Bbytes & _ & _).
assert (Hreq : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
(* The registers after Allocate. *)
assert (PR : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> YK11.getr regs2 rr = YK11.getr regs1 rr).
{ intros rr Hrr. rewrite <- (getr_lit regs2 _ rr eq_refl), <- (getr_lit regs1 _ rr eq_refl). exact (Hpr _ Hrr). }
assert (R2' : YK11.getr regs2 2 = w64 (spZ regs - ENTRY_FRAME)) by (rewrite PR by cs_tac; exact R2).
assert (R8' : YK11.getr regs2 8 = w64 n) by (rewrite PR by cs_tac; exact R8).
assert (R18' : YK11.getr regs2 18 = w64 DEC_A_instance) by (rewrite PR by cs_tac; exact R18).
assert (R19' : YK11.getr regs2 19 = w64 1) by (rewrite PR by cs_tac; exact R19).
assert (Rk' : forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> YK11.getr regs2 (Z_to_bv 5 k) = YK11.getr regs (Z_to_bv 5 k)).
{ intros k Hk. rewrite (Hpr k ltac:(unfold acallee_saved; lia)). exact (Rp k Hk). }
assert (B2 : bv_unsigned (YK11.getr regs2 2) = spZ regs - 48).
{ rewrite R2'. unfold w64, ENTRY_FRAME. apply unsigned_lit_small. lia. }
(* Memory after Allocate: the frame of the entry, the saved registers, the stack window. *)
assert (FSTK : forall a, spZ regs - 48 <= a < spZ regs ->
aview decodesegs0 (w_H W2) mem2 a = aview decodesegs0 (w_H W) mem1 a).
{ intros a Ha. apply Hfr.
- lia.
- exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(lia)).
- apply (al_stack _ _ LAWS ly' (snd r) W2 mem2 md2 a HAR2). rewrite Eslo, Eshi. lia.
- unfold ascratch. rewrite S1. lia.
- intros [_ Hb]. lia. }
assert (F1 : forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' (snd r) a -> ~ ascratch B ENTRY_STK regs a ->
~ (fst r <> PNull /\ addr <= a < addr + req_size n) ->
aview decodesegs0 (w_H W2) mem2 a = aview decodesegs0 (w_H W) mem a).
{ intros a Ha H1 H2 H3 H4. unfold ascratch, ENTRY_STK, ENTRY_FRAME, YGAlloc.AFSTACK_G in H3.
rewrite (Hfr a Ha H1 H2); [|unfold ascratch, YGAlloc.AFSTACK_G; rewrite S1; lia | exact H4].
apply aview_eq_of_mem. apply MF. rewrite unsigned_lit_small by lia. unfold ENTRY_FRAME. lia. }
assert (F2 : forall a, spZ regs - ENTRY_STK <= a < spZ regs -> apresent (w_H W2) mem2 a).
{ intros a Ha. unfold ENTRY_STK, ENTRY_FRAME, YGAlloc.AFSTACK_G in Ha. destruct (Z_lt_le_dec a (spZ regs - 48)) as [Hlo|Hge].
- apply Hpres2. rewrite S1. unfold YGAlloc.AFSTACK_G. lia.
- apply apresent_of_aview_high; [rewrite IMG_TOP_val; lia|]. rewrite (FSTK a ltac:(lia)).
apply aview_of_apresent. apply MP. unfold ENTRY_STK, ENTRY_FRAME, YGAlloc.AFSTACK_G. lia. }
assert (VS : forall off v, 8 <= off <= 40 -> val_mem decodesegs0 (mrestrict (w_H W) mem1) (spZ regs - off) 8 v ->
val_mem decodesegs0 (mrestrict (w_H W2) mem2) (spZ regs - 48 + (48 - off)) 8 v).
{ intros off v Ho Hv. replace (spZ regs - 48 + (48 - off)) with (spZ regs - off) by lia.
apply (val_mem_of_aview (w_H W) (w_H W2) mem1 mem2); [|exact Hv]. intros k Hk. apply FSTK. lia. }
(* The cells the code reads after Allocate: the fill pointer's two words and the space base P = ly_space ly'. *)
destruct (IMG_CONST ly') as (G1 & G2 & G3).
pose proof (const_cell_val B ly' (snd r) W2 mem2 md2 _ _ HAR2 G1) as VG1. cbn [aeval] in VG1.
pose proof (const_cell_val B ly' (snd r) W2 mem2 md2 _ _ HAR2 G2) as VG2. cbn [aeval] in VG2.
pose proof (const_cell_val B ly' (snd r) W2 mem2 md2 _ _ HAR2 G3) as VP. cbn [aeval] in VP.
rewrite HINST, Z.add_0_r in VP. change (DEC_A_instance + o_space) with DEC_A_space_cell in VP.
(* The block is a primary one: n <= PRIM_MAX, so it lies in [ly_space ly', ly_space ly' + 2 ^ 37). *)
assert (HFP : from_primary n = true) by (apply prim_fp; unfold n in *; lia).
assert (HInb : In (fst r, n) (blocks (snd r))) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
destruct (prim_block_in_space B ly' (snd r) W2 mem2 md2 (fst r) n HAR2 HInb HFP) as (Sp0 & Sp1 & Sp2 & Sp3).
fold addr in Sp1, Sp2.
set (P := ly_space ly') in *.
assert (HPr : 0 <= P < 2 ^ 64) by lia.
(* The seed at 0x31c28. *)
pose proof (SEED_C W2 regs2 mem2 P) as HS. cbv zeta in HS. rewrite B2 in HS.
specialize (HS ltac:(unfold YGAlloc.AFSTACK_G, ENTRY_FRAME, kHighMemBeg, kHighMemEnd; lia)
ltac:(replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact Hal) R18' R19'
(VS 8 _ ltac:(lia) MVra) (VS 16 _ ltac:(lia) MVs0) (VS 24 _ ltac:(lia) MVs1) (VS 32 _ ltac:(lia) MVs2) (VS 40 _ ltac:(lia) MVs3)
HPr VP VG1 VG2).
pose proof decode_wx as Hwx.
assert (U10 : forall P' regsB', YK11.getr regsB' 10 = w64 addr -> U (E_X regs regsB' P') (SOff 10 0) = addr).
{ intros P' regsB' H10. rewrite U_SOff, (EX_lo regs regsB' P' 10 10%bv eq_refl), H10, Z.add_0_r.
unfold w64, zcanon, M64. rewrite lit64_unsigned, Z.mod_mod by lia. apply Z.mod_small. lia. }
assert (U32 : U (E_X regs regs2 P) (SOff 32 0) = P).
{ rewrite U_SOff, EX_32, Z.add_0_r. unfold w64, zcanon, M64. rewrite lit64_unsigned, Z.mod_mod by lia. apply Z.mod_small. lia. }
assert (UP : U (E_X regs regs2 P) (SOff 32 137438953472) = (P + PRIM_SPACE_SIZE) mod 2 ^ 64).
{ rewrite U_SOff, EX_32. unfold w64, zcanon, M64, PRIM_SPACE_SIZE. rewrite lit64_unsigned, (Z.mod_small P (2 ^ 64)) by lia. reflexivity. }
unfold cfg_at.
srr_run_to_sh tbl_calloc_A_ok HS DEC_A_memset.
srr_branch_sh tbl_calloc_A_ok HS.
{ exfalso. rewrite branch_eq_U, (U10 P regs2 Ha0), U_SLit in Hc. apply Z.eqb_eq in Hc.
unfold zcanon, M64 in Hc. rewrite Z.mod_0_l in Hc by lia. lia. }
srr_run_to_sh tbl_calloc_A_ok HS DEC_A_memset.
srr_branch_sh tbl_calloc_A_ok HS.
{ (* 0x31c30 `bltu a0, a1`: a0 < P is refuted, the block lies at or above the space base. *)
exfalso. rewrite branch_ltu_U, (U10 P regs2 Ha0), U32 in Hc0. apply Z.ltb_lt in Hc0. lia. }
srr_run_to_sh tbl_calloc_A_ok HS DEC_A_memset.
srr_branch_sh tbl_calloc_A_ok HS.
{ (* 0x31c3c `bgeu a0, a1`: a0 >= P + 2 ^ 37 is refuted, the block lies below the end of the space. *)
exfalso. rewrite branch_geu_U, (U10 P regs2 Ha0), UP in Hc1. apply Bool.negb_true_iff, Z.ltb_ge in Hc1.
rewrite Z.mod_small in Hc1 by lia. lia. }
(* The block lies in the primary space: the fill. *)
srr_run_to_sh tbl_calloc_A_ok HS DEC_A_memset.
mem_eqs.
match type of HS with st_ok _ _ _ (restrict _ ?m) => assert (MM : ms_mem m = mem2) by congruence; rename m into msF end.
assert (GKF : forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> YK11.getr (ms_regs msF) (Z_to_bv 5 k) = YK11.getr regs (Z_to_bv 5 k)).
{ intros k Hk. rewrite (st_ok_restrict_reg decodesegs0 _ _ _ _ (Z_to_bv 5 k) HS).
match type of HS with st_ok _ _ ?ssF _ =>
assert (GK : forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> sr_get (ss_regs ssF) (Z_to_bv 5 k) = SOff (Z.to_nat k) 0) by gk_tac;
rewrite (GK k Hk) end.
rewrite denot_off0, (EX_lo regs regs2 P (Z.to_nat k) (Z_to_bv 5 k)); [exact (Rk' k Hk)|].
rewrite Z_to_bv_unsigned, Z2Nat.id by lia. rewrite bv_wrap_small; [reflexivity|]. unfold bv_modulus. cbn. lia. }
assert (F_1 : YK11.getr (ms_regs msF) 1 = w64 DEC_A_calloc_fill_ret)
by (rewrite (st_ok_restrict_reg decodesegs0 _ _ _ _ 1%bv HS); sr_eval; reflexivity).
assert (F_2 : YK11.getr (ms_regs msF) 2 = w64 (spZ regs - ENTRY_FRAME))
by (rewrite (st_ok_restrict_reg decodesegs0 _ _ _ _ 2%bv HS); sr_eval; rewrite denot_off0, (EX_lo regs regs2 P 2 2%bv eq_refl); exact R2').
assert (F_9 : YK11.getr (ms_regs msF) 9 = w64 addr)
by (rewrite (st_ok_restrict_reg decodesegs0 _ _ _ _ 9%bv HS); sr_eval; rewrite denot_off0, (EX_lo regs regs2 P 10 10%bv eq_refl); exact Ha0).
assert (F_10 : YK11.getr (ms_regs msF) 10 = w64 addr)
by (rewrite (st_ok_restrict_reg decodesegs0 _ _ _ _ 10%bv HS); sr_eval; rewrite denot_off0, (EX_lo regs regs2 P 10 10%bv eq_refl); exact Ha0).
assert (F_11 : YK11.getr (ms_regs msF) 11 = w64 0)
by (rewrite (st_ok_restrict_reg decodesegs0 _ _ _ _ 11%bv HS); sr_eval; reflexivity).
assert (F_12 : YK11.getr (ms_regs msF) 12 = w64 n)
by (rewrite (st_ok_restrict_reg decodesegs0 _ _ _ _ 12%bv HS); sr_eval; rewrite denot_off0, (EX_lo regs regs2 P 8 8%bv eq_refl); exact R8').
assert (F_3 : YK11.getr (ms_regs msF) 3 = w64 (as_gp B))
by (rewrite <- (getr_lit _ 3 3%bv eq_refl), (GKF 3 (or_introl eq_refl)), (getr_lit regs 3 3%bv eq_refl); exact Hgp).
assert (F_4 : YK11.getr (ms_regs msF) 4 = w64 (as_tp B))
by (rewrite <- (getr_lit _ 4 4%bv eq_refl), (GKF 4 (or_intror (or_introl eq_refl))), (getr_lit regs 4 4%bv eq_refl); exact Htp).
assert (SF : spZ (ms_regs msF) = spZ regs - 48).
{ unfold spZ in *. rewrite F_2. unfold w64, ENTRY_FRAME. apply unsigned_lit_small. lia. }
pose proof (st_ok_restrict_mkst decodesegs0 (w_H W2) _ _ msF HS eq_refl) as Hshape.
rewrite Hshape.
unfold decode_zero_fill_spec_A, zero_fill_specP in FILL.
eapply SRr_bind.
{ apply (FILL ly' (snd r) W2 (ms_regs msF) (ms_mem msF) _ addr 0 n).
- unfold ecall_pre. rewrite MM. split; [apply AR_wvb; exact HAR2|].
split; [rewrite F_1; apply ret_ok_even; vm_compute; reflexivity|].
split; [rewrite SF; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
split; [rewrite SF, Eslo; unfold ESTACK; lia|]. split; [rewrite SF, Eshi; lia|].
split; [intros a Ha; rewrite SF in Ha; apply Hpres2; rewrite S1; unfold ESTACK, YGAlloc.AFSTACK_G in *; lia|].
split; [exact F_3 | exact F_4].
- exact F_10.
- exact F_11.
- exact F_12.
- lia.
- lia.
- lia.
- intros a Ha. destruct (Bbytes a ltac:(lia)) as [Hp Hno]. rewrite MM.
split; [apply apresent_writable; exact Hp|]. split; [exact Hno|]. rewrite SF. unfold ESTACK. lia. }
intros W3 c3 Hle (-> & regs3 & mem3 & md3 & -> & HAR3 & Hpr3 & Hsbm & Ha03 & Hzero & Hfr3 & Hpres3).
assert (RAF : raZ (ms_regs msF) = DEC_A_calloc_fill_ret).
{ unfold raZ. rewrite F_1. unfold w64. apply unsigned_lit_small. unfold DEC_A_calloc_fill_ret. lia. }
rewrite RAF.
assert (PR3 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> YK11.getr regs3 rr = YK11.getr (ms_regs msF) rr).
{ intros rr Hrr. rewrite <- (getr_lit regs3 _ rr eq_refl), <- (getr_lit (ms_regs msF) _ rr eq_refl). exact (Hpr3 _ Hrr). }
assert (R3_2 : YK11.getr regs3 2 = w64 (spZ regs - ENTRY_FRAME)) by (rewrite PR3 by cs_tac; exact F_2).
assert (R3_9 : YK11.getr regs3 9 = w64 addr) by (rewrite PR3 by cs_tac; exact F_9).
assert (R3_k : forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> YK11.getr regs3 (Z_to_bv 5 k) = YK11.getr regs (Z_to_bv 5 k)).
{ intros k Hk. rewrite (Hpr3 k ltac:(unfold acallee_saved; lia)). exact (GKF k Hk). }
assert (B3 : bv_unsigned (YK11.getr regs3 2) = spZ regs - 48).
{ rewrite R3_2. unfold w64, ENTRY_FRAME. apply unsigned_lit_small. lia. }
assert (F3stk : forall a, spZ regs - 48 <= a < spZ regs ->
aview decodesegs0 (w_H W2) mem3 a = aview decodesegs0 (w_H W2) mem2 a).
{ intros a Ha. rewrite <- MM. apply Hfr3; [lia | lia | rewrite SF; unfold ESTACK; lia]. }
assert (VS3 : forall off v, 8 <= off <= 40 -> val_mem decodesegs0 (mrestrict (w_H W) mem1) (spZ regs - off) 8 v ->
val_mem decodesegs0 (mrestrict (w_H W2) mem3) (spZ regs - 48 + (48 - off)) 8 v).
{ intros off v Ho Hv. apply (val_mem_of_aview (w_H W2) (w_H W2) mem2 mem3); [|exact (VS off v Ho Hv)].
intros k Hk. apply F3stk. lia. }
pose proof (SEED_D W2 regs3 mem3 P) as HSD. cbv zeta in HSD. rewrite B3 in HSD.
specialize (HSD ltac:(unfold YGAlloc.AFSTACK_G, ENTRY_FRAME, kHighMemBeg, kHighMemEnd; lia)
ltac:(replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact Hal)
(VS3 8 _ ltac:(lia) MVra) (VS3 16 _ ltac:(lia) MVs0) (VS3 24 _ ltac:(lia) MVs1) (VS3 32 _ ltac:(lia) MVs2) (VS3 40 _ ltac:(lia) MVs3)).
unfold cfg_at.
srr_run_to_sh tbl_calloc_A_ok HSD DEC_A_calloc_ret_insn.
mem_eqs.
match type of HSD with st_ok _ _ _ (restrict _ ?m) => assert (MMD : ms_mem m = mem3) by congruence; rename m into msD end.
apply (ret_leaf P regs3 _ msD _ ly' r W2 HSD).
all: try sr_goal.
* gk_tac.
* sr_eval. rewrite denot_off0, (EX_lo regs regs3 P 9 9%bv eq_refl). exact R3_9.
* exact R3_2.
* exact R3_k.
* rewrite MMD. apply AR_wvb. exact HAR3.
* exact Hly.
* exact Hwle.
* exact (same_io_trans _ _ _ (same_io_trans _ _ _ (same_io_trans _ _ _ (same_io_trans _ _ _ (same_io_wvb md _ _) Hio)
(same_io_wvb md2 _ _)) (same_io_sbm _ _ Hsbm)) (same_io_wvb md3 _ _)).
* rewrite MMD. intros a Ha H1 H2 H3 H4. unfold ascratch, ENTRY_STK, ENTRY_FRAME, YGAlloc.AFSTACK_G in H3.
rewrite (Hfr3 a Ha).
-- rewrite MM. apply (F1 a Ha H1 H2); [unfold ascratch, ENTRY_STK, ENTRY_FRAME, YGAlloc.AFSTACK_G; exact H3 | exact H4].
-- intros Hd. apply H4. split; [exact Hnn | lia].
-- rewrite SF. unfold ESTACK. lia.
* rewrite MMD. intros a Ha. apply Hpres3. rewrite MM. exact (F2 a Ha).
* exact Hqt.
* exact Hpath.
* exact Hnn.
* rewrite MMD. intros i Hi. exact (Hzero i Hi).
Qed.

(* The walk: the run from the entry to Allocate's entry (SRr), Allocate's contract from there (amreal over the
   malloc tree at n = nm * sz), and the run from Allocate's return to asan_calloc's return (SRr) on each leaf. *)
Lemma entry_walk_i :
amreal decodesegs0 (malloc n tr S) W (cfg_at decodesegs0 DEC_A_asan_calloc regs mem md) (entry_leaf ly S W regs mem md n tr).
Proof.
apply (amreal_SRr_pre decodesegs0 _ W _ _ (at_alloc W regs mem md nm sz so)); [exact walk_to_alloc|].
intros W' c' _ (-> & regs1 & mem1 & mat & -> & HR & HM).
pose proof (alloc_pre_of regs1 mem1 mat HR HM) as HAP.
unfold decode_aalloc_A, aalloc_realizes_cgif, YGAlloc.aalloc_prim_realizes in ALLOC.
assert (Hprim : n <= 64512) by (pre; unfold n, PRIM_MAX in *; lia).
pose proof (ALLOC DEC_A_instance so bp ly S W regs1 mem1 _ n tr HAP Hprim) as HA.
apply (amreal_post_SRr _ _ _ _ _ _ HA).
intros r W2 c2 HL. exact (post_alloc regs1 mem1 mat r W2 c2 HR HM HL).
Qed.

(* The same run in SRr form, with the granted path of the malloc tree in the leaf (YG0d.v:185 amreal_SRr04): the form
   the call rule consumes, and the form lib/Reusable/YGCallocModel.v's lemmas take. *)
Lemma entry_walk_SRr_i :
SRr decodesegs0 W (cfg_at decodesegs0 DEC_A_asan_calloc regs mem md)
(fun W' c' => exists r trc, apath (malloc n tr S) trc r /\ gflag trc = true /\ entry_leaf ly S W regs mem md n tr r W' c').
Proof.
pre. destruct (calloc_model_of_AR _ _ _ _ _ _ _ HAR) as [HU HWf].
pose proof (calloc_model_atok _ S nm sz tr HU HWf Hreg Hn0 Hs0 Hns Hlive Htr) as HTOK.
exact (amreal_SRr04 decodesegs0 _ W _ _ entry_walk_i (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK)).
Qed.
End i.

Theorem entry_walk : forall ly S W regs mem md nm sz so bp tr,
entry_pre ly S W regs mem md nm sz so bp tr ->
amreal decodesegs0 (malloc (nm * sz) tr S) W (cfg_at decodesegs0 DEC_A_asan_calloc regs mem md)
(entry_leaf ly S W regs mem md (nm * sz) tr).
Proof. intros ly S W regs mem md nm sz so bp tr PRE. exact (entry_walk_i ly S W regs mem md nm sz so bp tr PRE). Qed.

Theorem entry_walk_SRr : forall ly S W regs mem md nm sz so bp tr,
entry_pre ly S W regs mem md nm sz so bp tr ->
SRr decodesegs0 W (cfg_at decodesegs0 DEC_A_asan_calloc regs mem md)
(fun W' c' => exists r trc, apath (malloc (nm * sz) tr S) trc r /\ gflag trc = true /\
entry_leaf ly S W regs mem md (nm * sz) tr r W' c').
Proof. intros ly S W regs mem md nm sz so bp tr PRE. exact (entry_walk_SRr_i ly S W regs mem md nm sz so bp tr PRE). Qed.

(* At the wrapper's call (ra = 0x524a8, the instruction after 0x524a4 `jal 0x31bd4`), the leaf's configuration is
   at 0x524a8. *)
Lemma entry_leaf_at_wrapper : forall ly S W regs mem md n tr r W' c',
YK11.getr regs 1 = w64 DEC_A_wrap_after_call -> entry_leaf ly S W regs mem md n tr r W' c' ->
exists regs' mem' md', c' = cfg_at decodesegs0 DEC_A_wrap_after_call regs' mem' md'.
Proof.
intros ly S W regs mem md n tr r W' c' Hra (ly' & regs' & mem' & md' & -> & _).
exists regs', mem', md'. unfold raZ. rewrite Hra. unfold w64. rewrite unsigned_lit_small by (unfold DEC_A_wrap_after_call; lia).
reflexivity.
Qed.
Lemma ret_ok_wrapper : YK0s.ret_ok (w64 DEC_A_wrap_after_call).
Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
End e.
