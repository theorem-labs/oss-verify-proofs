(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgSeg.v at 884d339334e (its cut-state
   machinery, the cut states of the build segment M01 and their continuations, and its 21 piece statements) for the
   image-B builder; the hs_ prefix renamed to hsu_, the image record and the builder's own pcs made parameters
   (Section variables, the record hsu_bld) in place of image A's module, every register, real-frame cell and frame
   object measured on image B's own twin, image A's second latch entry dropped (image B has one), and the frame's
   shadow patterns derived from the image's prologue pattern instead of written out. *)
(* THE CUT STATES of the BUILD segment M01 of LLVMFuzzerTestOneInput and the statement of every piece that segment
   is split into, for the asan-ubsan ("image B") builds of reac-pw's harnesses. Statement text only: proves no
   function (kind: segment lemma).

   THE UNIT. This file states reac-pw/fuzz_headamp's image-B builder. reac-pw/fuzz_role's image B inlines the
   same pod.h, but it keeps the builder's quantities in other R-cells (a frame-slot map, not a register renaming),
   has no cap and no null flag, and keeps a flag byte at R+0x40, so it ports this text over its own records. No
   image module is Required: the image record I (HPgCSpec.hd_himg) and the builder's own pcs (hsu_bld) are
   parameters, and the frame's shadow patterns are derived from the image's own prologue pattern (hi_shA I) by
   opening the granules of one frame object. headamp_bld_B below is reac-pw/fuzz_headamp's image B
   (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id).

   WHAT THIS FILE IS FOR. M01 runs from C1 (the first block's malloc returned) to C2 (the `jal` of the second
   block's malloc, not executed); its contract is HPgCSpec.headamp_build_contract at the image's record. M01 is cut
   again at the heads and the joins of its loops and at the boundaries of its pieces, and every piece is stated
   here, so that the pieces are proved in parallel and each proof sees only the STATEMENTS of the pieces its
   continuation goes to.

   HOW A CUT IS STATED, AND WHY NOT AS A SYMBOLIC STATE. A cut is a SEMANTIC predicate over
   (ly, S, W, regs, mem, md) at the cut's pc: the caller's journal from the segment's start, the frame's shadow
   bytes, the first block's image, the input bytes left, and a list of (location, value) facts over the run's
   quantities (HPgBase.hd_at: a register, or the 8-byte cell at an offset of a base). A symbolic state can only be
   written down after the piece before it has been run, which would serialise the pieces; a semantic cut lets each
   piece rebuild its own symbolic state from the cut, as the released walks rebuild the entry one.
   A cut states only POSITIVE facts. What a call leaves alone is not restated: the journal's own clauses and each
   callee's write-set post carry it between cuts.

   WHERE A VALUE LIVES (image B of fuzz_headamp). The harness's values live in registers and in 8-byte cells of the
   real frame at R + off, R being the
   32-aligned base the prologue puts in s1 and sp and S the entry sp (s0). The locals whose address is taken live
   in the frame for locals F, a side-stack frame of class 4 the prologue takes: t[96] at F+0x20, ch[24] at F+0xa0,
   r[4] at F+0xe0 and THREE pod_ent objects, one per inlined builder scope -- e at F+0xf0 (the shape-7 property),
   e42 at F+0x180 (the Int-7 value pod) and e62 at F+0x210 (the pod loop) -- then res at F+0x2a0 and x at F+0x2c0.
   s3 = (F >> 3) + K is the frame's shadow base and s11 = K the runtime's shadow offset (image A keeps them in s3
   and s7). Through the whole build the first block's address is in R+0x148, the cap in R+0x20, the frame for
   locals in R+0x18 and R+0x48, and 1 - the null flag in R+0x38; the input cursor and what is left of it move
   between registers from piece to piece (image A keeps what is left in R+0x118). The four `not` cells R+0xc0,
   R+0xd8, R+0xe8 and R+0xf0 are the complements this build's pointer-overflow tests compare against; image A, with
   no such test, has no counterpart.

   pod_write_ent IS OUT OF LINE in image B (image A inlines it): the pieces that write a pod call it, under
   fuzz_rate's image-independent contract PweSpec.pod_write_ent_specX, so those cuts carry the premises that
   contract asks for (the pod's 104 bytes as Layout.ent_mem, the len cell, the block) and no cut inside it.

   THE MODEL. The quantities a cut names are the shared model's (lib/Pod): the record built so far is a
   Model.pb_cut (the shape, the properties written and, inside a params Struct, the pods written), the first block
   holds Layout.pc_image of it, what is left of the input is a suffix of the bytes after the two harness bytes, and
   the cursor that names it is src + |rest| - |r|. At the end of the build the block holds Layout.pp_bytes of the
   record Model.pod_build makes. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Spa Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================= the builder's own pcs =======================================
   Each is the address of the first instruction of the piece that starts there; the two segment cuts are the
   image record's hi_c1 and hi_c2. bi_dt holds the nine targets of ent_build's jump table (kinds 0 .. 8, in that
   order) and bi_d9 the entry of kind 9, which the table's bound test takes before the table's address is formed. *)
Record hsu_bld := HSUBld {
bi_B7 : Z; bi_BO : Z; bi_PH : Z;
bi_N : Z; bi_SEL7 : Z; bi_SELK : Z; bi_SELI : Z; bi_SELS : Z;
bi_C : Z; bi_dt : list Z; bi_d9 : Z; bi_D0E : Z; bi_G : Z; bi_J : Z;
bi_CL : Z; bi_LATCH : Z; bi_P : Z; bi_P1 : Z; bi_R : Z; bi_RT : Z }.

(* reac-pw/fuzz_headamp, image B (fuzz_headamp.asan-ubsan). B7 and BO are the two arms of the shape test
   `bne a3,a4` 0x81164, each with the top size word written and len = 4; PH is their join, where the header of the
   shape is written and the property loop's preheader is about to run. The nine table targets are the ones the
   table at .rodata 0x20ecc names, in kind order; kind 9 is taken by `bltu a2,a1` 0x81924. *)
Definition headamp_bld_B : hsu_bld := {|
bi_B7 := 0x81168; bi_BO := 0x81200; bi_PH := 0x8137c;
bi_N := 0x81494; bi_SEL7 := 0x814d4; bi_SELK := 0x81590; bi_SELI := 0x828ec; bi_SELS := 0x816fc;
bi_C := 0x81888;
bi_dt := [0x8194c; 0x81e04; 0x81cbc; 0x81d34; 0x81c68; 0x81e6c; 0x81f08; 0x81d88; 0x81f5c];
bi_d9 := 0x82004; bi_D0E := 0x819c0; bi_G := 0x81afc; bi_J := 0x82618;
bi_CL := 0x82a18; bi_LATCH := 0x82ae4; bi_P := 0x82bec; bi_P1 := 0x82bf0;
bi_R := 0x82e2c; bi_RT := 0x82ec8 |}.

(* ================= the frame objects the builder brings into scope and out again =================
   Their offsets in the frame for locals, the same in every image-B build of reac-pw (the frame's object list is
   the compiler's, and the two harnesses inline the same builder): t and ch are the digit buffer and the key's
   first part of ent_build's case 0, r the little counter it reverses through, and e62 the pod the pod loop
   builds. A granule is 8 bytes, so an object at F + c owns the shadow bytes from c / 8 on. *)
Definition HSU_T : Z := 0x20.            (* t[96]: granules 0x04 .. 0x0f *)
Definition HSU_CH : Z := 0xa0.           (* ch[24]: granules 0x14 .. 0x16 *)
Definition HSU_R4 : Z := 0xe0.           (* r[4]: granule 0x1c *)
Definition HSU_E : Z := 0xf0.            (* e, the shape-7 property's pod: granules 0x1e .. 0x2a *)
Definition HSU_E42 : Z := 0x180.         (* e42, the Int-7 value pod: granules 0x30 .. 0x3c *)
Definition HSU_E62 : Z := 0x210.         (* e62, the pod loop's pod: granules 0x42 .. 0x4e *)
Definition ENT_GRAN : nat := 13%nat.     (* 104 bytes = 13 granules *)

(* The granule index of each object whose scope the builder changes, and the count of granules it owns; the
   memory layer's scope lemmas take exactly these pairs. *)
Definition HSU_G_T : nat := 4%nat.       (* t: 12 granules from 4 *)
Definition HSU_G_CH : nat := 20%nat.     (* ch: 3 from 20 *)
Definition HSU_G_E62 : nat := 66%nat.    (* e62: 13 from 66 *)
Lemma hsu_granules_of_offsets :
HSU_G_T = Z.to_nat (HSU_T / 8) /\ HSU_G_CH = Z.to_nat (HSU_CH / 8) /\ HSU_G_E62 = Z.to_nat (HSU_E62 / 8).
Proof. repeat split. Qed.

(* A shadow pattern with the n granules from lo marked usable: the scope-opening stores write 0 there and leave
   every other granule as it was. This is the term the memory layer's hm_setn gives with v = 0, written out here
   so that this file Requires no image's memory module (hm_setn pat lo n 0 is the same term, so the scope lemmas
   of the memory layer rewrite a cut's pattern without a bridge). *)
Definition hsu_open (lo n : nat) (pat : list Z) : list Z :=
map (fun i => if (lo <=? i)%nat && (i <? lo + n)%nat then 0 else nth i pat 0) (seq 0 (length pat)).
Lemma hsu_open_length : forall lo n pat, length (hsu_open lo n pat) = length pat.
Proof. intros. unfold hsu_open. rewrite length_map, length_seq. reflexivity. Qed.
Lemma hsu_open_nth : forall lo n pat i, (i < length pat)%nat ->
nth i (hsu_open lo n pat) 0 = if (lo <=? i)%nat && (i <? lo + n)%nat then 0 else nth i pat 0.
Proof.
intros lo n pat i Hi. unfold hsu_open.
set (f := fun j : nat => if (lo <=? j)%nat && (j <? lo + n)%nat then 0 else nth j pat 0).
rewrite (nth_indep _ 0 (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
rewrite map_nth, seq_nth by exact Hi. reflexivity.
Qed.
(* the granules of the window are 0; every other granule is the pattern's *)
Lemma hsu_open_in : forall lo n pat i, (lo <= i < lo + n)%nat -> (i < length pat)%nat ->
nth i (hsu_open lo n pat) 0 = 0.
Proof.
intros lo n pat i Hw Hi. rewrite hsu_open_nth by exact Hi.
destruct (Nat.leb_spec lo i) as [Hle|Hgt]; [| exfalso; lia].
destruct (Nat.ltb_spec i (lo + n)) as [Hlt|Hge]; [reflexivity | exfalso; lia].
Qed.
Lemma hsu_open_out : forall lo n pat i, ((i < lo)%nat \/ (lo + n <= i)%nat) -> (i < length pat)%nat ->
nth i (hsu_open lo n pat) 0 = nth i pat 0.
Proof.
intros lo n pat i Hw Hi. rewrite hsu_open_nth by exact Hi.
destruct (Nat.leb_spec lo i) as [Hle|Hgt]; [| reflexivity].
destruct (Nat.ltb_spec i (lo + n)) as [Hlt|Hge]; [exfalso; lia | reflexivity].
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
(* the image's record (HPgCSpec.hd_himg: the cut pcs C1 .. C9, the cut values, the frame's shadow after the
   prologue, the write ranges, the strings and cells) and the builder's own pcs *)
Variable I : hd_himg.
Variable BI : hsu_bld.

(* a list of (location, value) facts, through HPgBase.hd_at: a register holds the 64-bit word of v, a cell holds
   its 8 little-endian bytes *)
Definition hsu_at (H : word -> bool) (mem : word -> option byte) (regs : bvmap 5 word) (e : hd_env)
(L : list (hd_loc * Z)) : Prop :=
Forall (fun f => hd_at segs H mem regs e (fst f) (snd f)) L.

(* ========================= what every cut INSIDE a segment carries =========================
   The segment's own journal from its start (with the segment's event count: no middle segment allocates), sp / gp
   / tp as at the start, the frames, the blocks, the I/O state and the meter as at the start, and every byte outside
   the callees' stack [R - T_SEG_STK, R) and outside the ranges the segment writes as at the start. These are
   exactly the clauses of HPgCSpec.hd_seg_post without its pc, its float state and its result, so the cut at a
   segment's last pc IS that segment's post. *)
Definition hsu_mid (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
(E : Z -> Prop)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
(md2 : Model) : Prop :=
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
frames S2 = frames Sc /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_SEG_STK <= a < spZ regs) -> ~ E a ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).

(* ================== the fixed data of a segment's walk ==================
   One record for everything a segment's contract fixes before its first instruction: the harness's journal so far
   (its start state and the journal's parameters), the registers at the segment's first pc, the run's quantities e
   (HPgBase.hd_env: S, R, F, the four blocks, len, cap, the null flag, rc, the input cursor and what is left of it),
   the position of the frame for locals among the side stack's frames of its class, and the read-only range. A cut
   inside the segment is a predicate over this record and the state at the cut. *)
Record hsu_scx := HSUCx {
x_STK : Z; x_sp0 : Z; x_FP : list (Z * Z);
x_ly : alayout; x_S : astate; x_W0 : world segs; x_mem0 : word -> option byte; x_md0 : Model;
x_own : list (Z * Z); x_k : Z; x_regs : bvmap 5 word;
x_lyc : alayout; x_Sc : astate; x_W : world segs; x_memc : word -> option byte; x_mdc : Model;
x_RLO : Z; x_RHI : Z; x_e : hd_env; x_pos : Z }.

(* what a segment's contract asks at its start (HPgCSpec.hd_seg_pre at the image's record), with the frame's
   shadow bytes sh the contract names: hi_shA I for M01, M02 and M03, hi_shB I for M04a / M04b *)
Definition hsu_pre (cx : hsu_scx) (sh : list Z) : Prop :=
hd_seg_pre segs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
(x_own cx) (x_k cx) (x_regs cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx)
I sh (x_RLO cx) (x_RHI cx) (x_e cx) (x_pos cx).

(* the journal-and-frame part of a cut inside the segment, with the segment's write set E *)
Definition hsu_core (cx : hsu_scx) (E : Z -> Prop)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
(md2 : Model) : Prop :=
hsu_mid (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
(x_k cx) (x_regs cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) E ly2 S2 W2 regs2 mem2 md2.

(* the first block's bytes at a cut *)
Definition hsu_pp_at (cx : hsu_scx) (W2 : world segs) (mem2 : word -> option byte) (l : list byte) : Prop :=
garr8 segs (mrestrict (w_H W2) mem2) (e_pp (x_e cx)) (hd_zbytes l).
(* the frame's shadow bytes at a cut *)
Definition hsu_fsh_at (cx : hsu_scx) (W2 : world segs) (mem2 : word -> option byte) (pat : list Z) : Prop :=
hd_fsh segs (w_H W2) mem2 (e_F (x_e cx)) pat.
(* the bytes of one frame object at a cut *)
Definition hsu_obj_at (cx : hsu_scx) (W2 : world segs) (mem2 : word -> option byte) (c : Z) (l : list byte)
: Prop := garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e cx) + c) (hd_zbytes l).
(* the values at a cut's locations *)
Definition hsu_at_cx (cx : hsu_scx) (W2 : world segs) (mem2 : word -> option byte) (regs2 : bvmap 5 word)
(L : list (hd_loc * Z)) : Prop :=
hsu_at (w_H W2) mem2 regs2 (x_e cx) L.

(* M01's write set, as headamp_build_contract states it: the image's range list hi_w1 (the frame's objects, their
   shadow bytes and the real-frame cells) and the first block *)
Definition hsu_E1 (cx : hsu_scx) : Z -> Prop :=
fun a => hd_inw (x_e cx) (hi_w1 I) a \/
e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE.

(* What is left of the input the build reads: a suffix of the bytes after the two harness bytes, and the cursor
   that names it. e_src is where those bytes lie and e_left how many there are. *)
Definition hsu_suffix (rest r : list byte) : Prop := exists j, (j <= length rest)%nat /\ r = skipn j rest.
Definition hsu_cur (cx : hsu_scx) (rest r : list byte) : Z :=
e_src (x_e cx) + Z.of_nat (length rest) - Z.of_nat (length r).
(* the input bytes, as headamp_build_contract gives them: at e_src, outside the callees' stack, the ranges the
   segment writes and the first block *)
Definition hsu_in (cx : hsu_scx) (rest : list byte) : Prop :=
e_left (x_e cx) = Z.of_nat (length rest) /\
garr8 segs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_src (x_e cx)) (hd_zbytes rest) /\
range_addressable (aview segs (w_H (x_W cx)) (x_memc cx)) SHADOW_OFF (e_src (x_e cx)) (e_left (x_e cx)) /\
(0 < e_left (x_e cx) -> shadow_hull_vis (aview segs (w_H (x_W cx)) (x_memc cx)) (e_src (x_e cx)) (e_left (x_e cx))) /\
amem_range (e_src (x_e cx)) (e_left (x_e cx)) /\
0 < e_src (x_e cx) /\ e_src (x_e cx) + e_left (x_e cx) <= 2 ^ 63 /\
(forall a, e_src (x_e cx) <= a < e_src (x_e cx) + e_left (x_e cx) ->
 ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) /\ ~ hd_inw (x_e cx) (hi_w1 I) a /\
 ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE)).

(* ===================================================================================================
   THE BUILD (M01): the cuts of headamp_build_contract's walk, from C1 = hi_c1 I to C2 = hi_c2 I
   ===================================================================================================
   The builder writes one object into the first block. Its state at a cut is the record so far (a
   Model.pb_cut: the shape sh, the properties ps written and, inside a params Struct, the pods es written),
   what is left of the input, and the loop counters; the block holds Layout.pc_image of that state and the
   R-relative cells hold the loop's constants and counters. *)

(* The byte values of the frame's shadow at the states the build passes through. P0 is the prologue's pattern
   (the image's hi_shA); PJ opens e62's 13 granules (the pod loop's stores just after C, closed again before CL);
   PG is PJ with t's 12 granules and ch's 3 open (ent_build's case 0 opens them and closes them again before J),
   r's granule 0xf8 at G (the digits path brings r into scope at 0x81a24 and out again at 0x81af8; the odd_ch path
   never brings it into scope). *)
Definition hsu_P0 : list Z := hi_shA I.
Definition hsu_PJ : list Z := hsu_open HSU_G_E62 ENT_GRAN hsu_P0.
Definition hsu_PG : list Z := hsu_open HSU_G_T 12 (hsu_open HSU_G_CH 3 hsu_PJ).

(* The constants the preheader puts in R-relative cells and no piece writes again, with the cells the start of the
   build wrote. In image B of fuzz_headamp: 0x15555556 is the `% 12u` multiplier (pod.h:354), 0x10003 is
   SPA_PROP_VOLUME and 0x80001 SPA_PROP_params, -0x4001 and -0x3ffd are the two capacity bounds, R+0x28 and R+0x30
   are the top size word's offset (0: the block's length before the header) and its address, R+0x20 is the cap,
   R+0x38 is 1 - the null flag, R+0x148 the first block, R+0x18 and R+0x48 the frame for locals, R+0xf8 says the
   shape is 7 and R+0x100 is the property count. R+0xc0, R+0xd8, R+0xe8 and R+0xf0 are the complements the
   pointer-overflow tests of pod.h:177 and pod.h:250 compare against. *)
Definition hsu_Kc (cx : hsu_scx) (sh np : Z) : list (hd_loc * Z) :=
let e := x_e cx in
[(LCell XR 0x8, e_pp e + 0x4008); (LCell XR 0x10, 0x15555556); (LCell XR 0x18, e_F e);
 (LCell XR 0x20, e_cap e); (LCell XR 0x28, 0); (LCell XR 0x30, e_pp e);
 (LCell XR 0x38, 1 - e_null e); (LCell XR 0x40, e_F e + HSU_E62 + 0x10); (LCell XR 0x48, e_F e);
 (LCell XR 0x50, e_pp e + 0x4010); (LCell XR 0x60, e_F e + HSU_E42 + 0xc);
 (LCell XR 0x68, e_F e + HSU_E42); (LCell XR 0x70, 0x10003); (LCell XR 0x78, e_pp e + 0x400c);
 (LCell XR 0xa0, e_F e + HSU_E + 8); (LCell XR 0xa8, -0x4001); (LCell XR 0xb0, 0x80001);
 (LCell XR 0xb8, e_F e + HSU_E); (LCell XR 0xc0, - e_F e - HSU_CH - 1); (LCell XR 0xc8, e_F e + HSU_CH);
 (LCell XR 0xd0, e_pp e + 0x4014); (LCell XR 0xd8, - e_pp e - 0x4015);
 (LCell XR 0xe0, Z.shiftr (e_pp e + 0x4d14) 3); (LCell XR 0xe8, - e_F e - HSU_E62 - 9);
 (LCell XR 0xf0, - e_pp e - 1); (LCell XR 0xf8, if sh =? 7 then 1 else 0); (LCell XR 0x100, np);
 (LCell XR 0x108, -0x3ffd); (LCell XR 0x118, e_F e + HSU_E62 + 8); (LCell XR 0x120, e_pp e + 0x4d14);
 (LCell XR 0x130, e_F e + HSU_E62); (LCell XR 0x138, e_pp e + 0x4000); (LCell XR 0x148, e_pp e);
 (LCell XR 0x150, shadow_addr (e_pp e + 0x4000))].

(* the `v / 10` multiplier of the digit loop (pod.h:240-241), in s8 from the preheader *)
Definition HSU_MULT10 : Z := 0xcccccccd * 2 ^ 32.

(* the registers both loops keep: s0 = S, s1 = R, s3 = the frame's shadow base, s11 = the runtime's shadow offset,
   s8 = the multiplier, s6 = &r, s9 = &t *)
Definition hsu_Rc0 (cx : hsu_scx) : list (hd_loc * Z) :=
let e := x_e cx in
[(LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 27, SHADOW_OFF);
 (LReg 24, HSU_MULT10); (LReg 22, e_F e + HSU_R4); (LReg 25, e_F e + HSU_T)].
(* the property loop keeps two more: s7 = the out-of-scope byte the scope closers store, s10 = 1, the bound the
   cursor tests of fuzz.h:42 compare against. The pod loop reuses both for its own quantities. *)
Definition hsu_Rc1 (cx : hsu_scx) : list (hd_loc * Z) :=
hsu_Rc0 cx ++ [(LReg 23, -8); (LReg 26, 1)].

(* the two header reads of pod_build (pod.h:385-386): the shape and the property count *)
Definition hsu_sh (rest : list byte) : Z := fst (Cursor.fuzz_u8 rest) mod 8.
Definition hsu_np (rest : list byte) : Z := fst (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 rest))) mod 4.
Definition hsu_r0 (rest : list byte) : list byte := snd (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 rest))).
(* the record the loop may have built: what Model.pod_rec_wf asks of its parts *)
Definition hsu_wf (sh : Z) (ps : list (Z * pval)) : Prop :=
0 <= sh < 8 /\ Forall (fun kv => 0 <= fst kv < 2 ^ 32 /\ pval_wf (snd kv)) ps /\
Forall ent_wf (all_ents ps) /\ (length ps <= 3)%nat.
Definition hsu_plen (sh : Z) (ps : list (Z * pval)) : Z := Z.of_nat (length (pc_buf (PbCut sh ps None))).
Definition hsu_seen (ps : list (Z * pval)) : Z := Z.b2z (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps).
Definition hsu_first (ps : list (Z * pval)) : Z :=
Z.b2z (negb (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps)).
(* the offset of an open params Struct's size word: the property's key and flags are already written *)
Definition hsu_at_of (sh : Z) (ps : list (Z * pval)) : Z := hsu_plen sh ps + 8.

(* ---------------- the build's first own cuts: the two arms of the shape test ----------------
   The block was filled with zeros, the two header reads were made, and the top size word was written as four
   zero bytes with len := 4 (pod.h:387-388). a0 is that length, a2 = len - 0x3ffd is the capacity test's left
   side, a6 = pp + 0 and a7 = 0 are the top word's address and its offset before it, a1 = 0x4000 is POD_BUF_MAX,
   s5 = 0x5000 (the block's request 0x4d20 is s5 - 0x2e0, 0x80fc0), s7 and s9 the frame for locals and the first
   block, s2 the input cursor
   and t3 what is left of it, and s8 is the cap. *)
Definition hsu_L_hdr (cx : hsu_scx) (sh np : Z) (rest r : list byte) : list (hd_loc * Z) :=
let e := x_e cx in
[(LReg 10, 4); (LReg 11, 0x4000); (LReg 12, 4 - 0x3ffd); (LReg 16, e_pp e); (LReg 17, 0);
 (LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 27, SHADOW_OFF);
 (LReg 21, 0x5000); (LReg 23, e_F e); (LReg 24, e_cap e); (LReg 25, e_pp e);
 (LCell XR 0x38, 1 - e_null e); (LCell XR 0x48, e_F e); (LCell XR 0xf0, - e_pp e - 1);
 (LCell XR 0x100, np); (LCell XR 0x108, -0x3ffd); (LCell XR 0x138, e_pp e + 0x4000);
 (LCell XR 0x150, shadow_addr (e_pp e + 0x4000));
 (LReg 18, hsu_cur cx rest r); (LReg 28, Z.of_nat (length r))].
(* the block's bytes before the object's header: the top size word only *)
Definition hsu_img_hdr : list byte := pp_image (le32 0) false false false [] false.
Definition hsu_cut_hdr (cx : hsu_scx) (rest r : list byte) (sh np : Z)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
(md2 : Model) : Prop :=
hsu_core cx (hsu_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx cx W2 mem2 regs2 (hsu_L_hdr cx sh np rest r) /\
hsu_fsh_at cx W2 mem2 hsu_P0 /\ hsu_pp_at cx W2 mem2 hsu_img_hdr /\
hsu_in cx rest /\ hsu_suffix rest r /\
sh = hsu_sh rest /\ np = hsu_np rest /\ r = hsu_r0 rest.
Definition hsu_cut_B7 (cx : hsu_scx) (rest r : list byte) (np : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_cut_hdr cx rest r 7 np ly2 S2 W2 regs2 mem2 md2.
(* the other arm keeps the shape in a3 (the test reads it again at pod.h:395) *)
Definition hsu_cut_BO (cx : hsu_scx) (rest r : list byte) (sh np : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_cut_hdr cx rest r sh np ly2 S2 W2 regs2 mem2 md2 /\ sh <> 7 /\
hsu_at_cx cx W2 mem2 regs2 [(LReg 13, sh)].

(* ---------------- PH: the header is written, the preheader is about to run ----------------
   The block holds the image of the empty record of this shape (its header bytes and, for an Object, is_props);
   a6 and a7 still hold the top word's address and offset, and R+0xf8 now says whether the shape is 7. *)
Definition hsu_L_PH (cx : hsu_scx) (sh np : Z) (rest r : list byte) : list (hd_loc * Z) :=
let e := x_e cx in
[(LReg 11, 0x4000); (LReg 16, e_pp e); (LReg 17, 0);
 (LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 27, SHADOW_OFF);
 (LReg 21, 0x5000); (LReg 23, e_F e); (LReg 24, e_cap e); (LReg 25, e_pp e);
 (LCell XR 0x38, 1 - e_null e); (LCell XR 0x48, e_F e); (LCell XR 0xf0, - e_pp e - 1);
 (LCell XR 0xf8, if sh =? 7 then 1 else 0); (LCell XR 0x100, np); (LCell XR 0x108, -0x3ffd);
 (LCell XR 0x138, e_pp e + 0x4000); (LCell XR 0x150, shadow_addr (e_pp e + 0x4000));
 (LReg 18, hsu_cur cx rest r); (LReg 28, Z.of_nat (length r))].
Definition hsu_cut_PH (cx : hsu_scx) (rest r : list byte) (sh np : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_core cx (hsu_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx cx W2 mem2 regs2 (hsu_L_PH cx sh np rest r) /\
hsu_fsh_at cx W2 mem2 hsu_P0 /\
hsu_pp_at cx W2 mem2 (pc_image (PbCut sh [] None)) /\
hsu_in cx rest /\ hsu_suffix rest r /\
sh = hsu_sh rest /\ np = hsu_np rest /\ r = hsu_r0 rest.

(* ---------------- N: the property loop's head, |ps| properties written ----------------
   The property index is in t0, `seen` in s4, the cursor in s2 and what is left in t3. *)
Definition hsu_cur2 (cx : hsu_scx) (rest r : list byte) : list (hd_loc * Z) :=
[(LReg 18, hsu_cur cx rest r); (LReg 28, Z.of_nat (length r))].
Definition hsu_L_N (cx : hsu_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (hd_loc * Z) :=
hsu_Rc1 cx ++ hsu_Kc cx sh np
++ [(LReg 5, Z.of_nat (length ps)); (LReg 20, hsu_seen ps)] ++ hsu_cur2 cx rest r.
Definition hsu_cut_N (cx : hsu_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_core cx (hsu_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx cx W2 mem2 regs2 (hsu_L_N cx sh np ps rest r) /\
hsu_fsh_at cx W2 mem2 hsu_P0 /\
hsu_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
hsu_in cx rest /\ hsu_suffix rest r /\ hsu_wf sh ps /\
sh = hsu_sh rest /\ np = hsu_np rest /\ Z.of_nat (length ps) < np /\ np <= 3 /\
(ps, r) = props_loop sh (length ps) (hsu_r0 rest).

(* ---------------- the two ends of one property's selector (pod.h:399-423) ----------------
   SEL7 (shape 7: the property is an Int pod with no key) and SELK (any other shape: the key, its flags and the
   `first` test). The selector byte was read: t2 is the cursor after it and t3 what is left; a1 is that byte at
   SELK, where the body reads it again. *)
Definition hsu_L_SEL (cx : hsu_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (hd_loc * Z) :=
hsu_Rc0 cx ++ hsu_Kc cx sh np
++ [(LReg 5, Z.of_nat (length ps)); (LReg 20, hsu_seen ps);
    (LReg 7, hsu_cur cx rest r); (LReg 28, Z.of_nat (length r))].
(* what every cut of one property's body shares with N, with the tie of ps to the input: the properties
   written are the ones Model.props_loop makes of the bytes after the two header reads *)
Definition hsu_prop_base (cx : hsu_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_core cx (hsu_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hsu_fsh_at cx W2 mem2 hsu_P0 /\ hsu_in cx rest /\ hsu_suffix rest r /\ hsu_wf sh ps /\
e_len (x_e cx) = hd_len rest /\
ps = fst (props_loop sh (length ps) (hsu_r0 rest)) /\
sh = hsu_sh rest /\ np = hsu_np rest /\ Z.of_nat (length ps) < np /\ np <= 3.
Definition hsu_cut_SEL7 (cx : hsu_scx) (np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_prop_base cx 7 np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx cx W2 mem2 regs2 (hsu_L_SEL cx 7 np ps rest r) /\
hsu_pp_at cx W2 mem2 (pc_image (PbCut 7 ps None)) /\
r = snd (Cursor.fuzz_u8 (snd (props_loop 7 (length ps) (hsu_r0 rest)))).
Definition hsu_cut_SELK (cx : hsu_scx) (sh np sel : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_prop_base cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx cx W2 mem2 regs2 (hsu_L_SEL cx sh np ps rest r ++ [(LReg 11, sel); (LReg 23, -8); (LReg 26, 1)]) /\
hsu_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
sh <> 7 /\ 0 <= sel < 256 /\
(sel, r) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (hsu_r0 rest))).

(* ---------------- the two ends of the key piece (pod.h:407-423) ----------------
   SELI writes the Int value pod of a property whose value is an Int (the volume property, and a params property
   whose selector has bit 4 set), SELS opens a params Struct. On both, the key word and the flags word are already
   written, so the block's bytes are the record's image with those eight bytes appended; a4 is `seen` after this
   property and R+0x140 is `first`, both set on the key's two arms. SELS keeps three more: t1 the capacity bound,
   s2 the len cell's address and s7 the out-of-scope byte. *)
Definition hsu_img_key (sh : Z) (ps : list (Z * pval)) (kk : Z) : list byte :=
pp_image (pc_buf (PbCut sh ps None) ++ le32 kk ++ le32 0)
(is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
(params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false.
(* the key the selector chooses (Model.prop_step): the volume property, else the params property *)
Definition hsu_key_of (sel : Z) : Z := if sel mod 4 =? 0 then 0x10003 else 0x80001.
Definition hsu_L_KEY (cx : hsu_scx) (sh np sel : Z) (ps : list (Z * pval)) (rest r : list byte)
: list (hd_loc * Z) :=
hsu_Rc0 cx ++ hsu_Kc cx sh np
++ [(LReg 5, Z.of_nat (length ps)); (LReg 26, 1);
    (LReg 14, if sel mod 4 =? 0 then hsu_seen ps else 1);
    (LCell XR 0x140, if sel mod 4 =? 0 then 0 else hsu_first ps);
    (LReg 7, hsu_cur cx rest r); (LReg 28, Z.of_nat (length r))].
Definition hsu_cut_SELI (cx : hsu_scx) (sh np sel : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_prop_base cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx cx W2 mem2 regs2 (hsu_L_KEY cx sh np sel ps rest r) /\
hsu_pp_at cx W2 mem2 (hsu_img_key sh ps (hsu_key_of sel)) /\ sh <> 7 /\ 0 <= sel < 256 /\
(sel mod 4 = 0 \/ Z.testbit sel 4 = true) /\
(sel, r) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (hsu_r0 rest))).
Definition hsu_cut_SELS (cx : hsu_scx) (sh np sel : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_prop_base cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx cx W2 mem2 regs2
(hsu_L_KEY cx sh np sel ps rest r
 ++ [(LReg 6, -0x4001); (LReg 18, e_pp (x_e cx) + 0x4000); (LReg 23, -8)]) /\
hsu_pp_at cx W2 mem2 (hsu_img_key sh ps 0x80001) /\ sh <> 7 /\ 0 <= sel < 256 /\
sel mod 4 <> 0 /\ Z.testbit sel 4 = false /\
(sel, r) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (hsu_r0 rest))).

(* ---------------- C: the pod loop's head, |es| pods written ----------------
   The open Struct's size word offset `at` is in R+0x88 and its address in R+0x90, the property index in R+0x98,
   the count the count byte gave in R+0x128, `seen` = 1 in R+0x80 and `first` in R+0x140; the pod index is in a1
   (the pc spills it to R+0x158), the cursor in s5, what is left in s10 and &e62 in s4. The frame's shadow is
   still the prologue's: the stores just after this pc open e62's granules. *)
Definition hsu_L_pod (cx : hsu_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (rest r : list byte)
: list (hd_loc * Z) :=
hsu_Rc0 cx ++ hsu_Kc cx sh np
++ [(LCell XR 0x98, Z.of_nat (length ps)); (LCell XR 0x88, hsu_at_of sh ps);
    (LCell XR 0x90, e_pp (x_e cx) + hsu_at_of sh ps); (LCell XR 0x128, cnt);
    (LCell XR 0x80, 1); (LCell XR 0x140, hsu_first ps);
    (LReg 20, e_F (x_e cx) + HSU_E62); (LReg 23, -8);
    (LReg 21, hsu_cur cx rest r); (LReg 26, Z.of_nat (length r))].
(* What every cut inside the pod loop shares, with the tie of the count and the pods to the input: the
   selector picked the params Struct, the count byte gave cnt = c mod 33 (pod.h:425) and the pods written
   are the ones Model.ents_loop makes of what follows it, leaving rr at the turn's start. *)
Definition hsu_pod_tie (sh : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent) (rest rr : list byte)
: Prop :=
exists sel c r1 r2,
(sel, r1) = Cursor.fuzz_u8 (snd (props_loop sh (length ps) (hsu_r0 rest))) /\
(c, r2) = Cursor.fuzz_u8 r1 /\ cnt = c mod 33 /\ sel mod 4 <> 0 /\ Z.testbit sel 4 = false /\
ents_loop (length es) r2 = (es, rr).
Definition hsu_pod_base (cx : hsu_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_core cx (hsu_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hsu_in cx rest /\ hsu_suffix rest r /\ hsu_suffix rest rr /\ hsu_wf sh ps /\
e_len (x_e cx) = hd_len rest /\
ps = fst (props_loop sh (length ps) (hsu_r0 rest)) /\
hsu_pod_tie sh ps cnt es rest rr /\
sh = hsu_sh rest /\ np = hsu_np rest /\ Z.of_nat (length ps) < np /\ np <= 3 /\
sh <> 7 /\ (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\
Forall ent_wf es /\ (length es < 32)%nat /\ Z.of_nat (length es) < cnt.
Definition hsu_cut_C (cx : hsu_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_pod_base cx sh np ps cnt es rest r r ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx cx W2 mem2 regs2 (hsu_L_pod cx sh np ps cnt rest r ++ [(LReg 11, Z.of_nat (length es))]) /\
hsu_fsh_at cx W2 mem2 hsu_P0 /\
hsu_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))).

(* ---------------- the eleven entries of ent_build's switch (pod.h:265-379) ----------------
   The dispatch opens e62's granules, fills e62 with zeros, reads the kind byte and jumps through the nine
   relative entries of the image's table; the table's bound test takes case 9 and a zero count of input left takes
   case 0's second entry. At every table entry a7 is the cursor before the kind byte, s2 the cursor after it,
   t1 what was left before it, s4 what is left after it, a3 the sign-extended kind byte, t2 = 10 the `% 10`
   constant and a6 = 1 the cursor test's bound; the pod index is in R+0x158. *)
Definition hsu_pc_D (kd : Z) : Z :=
if kd mod 10 =? 9 then bi_d9 BI else nth (Z.to_nat (kd mod 10)) (bi_dt BI) 0.
Definition hsu_L_Dc (cx : hsu_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
: list (hd_loc * Z) :=
hsu_Rc0 cx ++ hsu_Kc cx sh np
++ [(LCell XR 0x98, Z.of_nat (length ps)); (LCell XR 0x88, hsu_at_of sh ps);
    (LCell XR 0x90, e_pp (x_e cx) + hsu_at_of sh ps); (LCell XR 0x128, cnt);
    (LCell XR 0x80, 1); (LCell XR 0x140, hsu_first ps); (LCell XR 0x158, Z.of_nat (length es))].
(* Case 9 is reached by the table's bound test `bltu a2,a1` 0x81924, before the eight instructions 0x81928 ..
   0x81944 that form the table's address, load its entry and sign-extend the kind byte, so a3 holds its value only
   on the nine table entries; a6 = 1 and t2 = 10 are set at 0x818d8 / 0x818dc, before the test, and hold at bi_d9
   too. *)
Definition hsu_L_D (cx : hsu_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) (kd : Z) : list (hd_loc * Z) :=
hsu_L_Dc cx sh np ps cnt es
++ [(LReg 17, hsu_cur cx rest r - 1); (LReg 18, hsu_cur cx rest r);
    (LReg 6, Z.of_nat (length r) + 1); (LReg 20, Z.of_nat (length r))]
++ [(LReg 7, 10); (LReg 16, 1); (LReg 23, -8)]
++ (if kd mod 10 =? 9 then [] else [(LReg 13, kd - 256 * (kd / 128))]).
(* rr is what is left of the input when the turn begins (at C); the kind byte is the first of it and r what
   is left after it, so the pod the turn builds is Model.ent_build rr. *)
Definition hsu_cut_D (cx : hsu_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (kd : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_pod_base cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx cx W2 mem2 regs2 (hsu_L_D cx sh np ps cnt es rest r kd) /\
hsu_fsh_at cx W2 mem2 hsu_PJ /\
hsu_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
hsu_obj_at cx W2 mem2 HSU_E62 (zeros 104) /\
hsu_suffix rest rr /\ (kd, r) = Cursor.fuzz_u8 rr /\ 0 <= kd < 256 /\ rr <> [].
(* the same with no input left: the kind byte reads as 0 and the cursor does not move (fuzz.h:37-43), so only
   the cursor is live, in s5 *)
Definition hsu_cut_D0E (cx : hsu_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_pod_base cx sh np ps cnt es rest [] [] ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx cx W2 mem2 regs2
(hsu_L_Dc cx sh np ps cnt es ++ [(LReg 21, hsu_cur cx rest []); (LReg 23, -8)]) /\
hsu_fsh_at cx W2 mem2 hsu_PJ /\
hsu_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
hsu_obj_at cx W2 mem2 HSU_E62 (zeros 104).

(* ---------------- G: case 0 with ch filled (digits and reverse, or the odd_ch copy), before the param part -------
   t and ch are in scope and r is out of scope again, so the frame's shadow is neither the prologue's nor the pod
   loop's: hsu_PG is that state. s2 = &ch, s10 = the third input byte of the head-amp key, t1 what is left and
   R+0x110 the cursor; ch holds the key's first part with its NUL. *)
Definition hsu_g_of (rr : list byte) : list byte * Z * list byte :=
let '(_, r1) := Cursor.fuzz_u8 rr in
let '(c, r2) := Cursor.fuzz_u8 r1 in
let '(pb, r3) := Cursor.fuzz_u8 r2 in
(if c <? 200 then dec64 (c mod 64) else nth (Z.to_nat (c mod 14)) odd_ch [], pb, r3).
Definition hsu_cut_G (cx : hsu_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (pb : Z) (chs : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_pod_base cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx cx W2 mem2 regs2
(hsu_L_Dc cx sh np ps cnt es
 ++ [(LCell XR 0x110, hsu_cur cx rest r); (LReg 6, Z.of_nat (length r));
     (LReg 18, e_F (x_e cx) + HSU_CH); (LReg 26, pb)]) /\
hsu_fsh_at cx W2 mem2 hsu_PG /\
hsu_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
hsu_obj_at cx W2 mem2 HSU_CH (chs ++ [NUL]) /\
hsu_obj_at cx W2 mem2 HSU_E62 (zeros 104) /\
fst (Cursor.fuzz_u8 rr) mod 10 = 0 /\ (chs, pb, r) = hsu_g_of rr /\
(length chs <= 21)%nat /\ 0 <= pb < 256.

(* ---------------- J: the pod is built; the call of pod_write_ent is about to run ----------------
   e62 holds Layout.ent_mem of the pod ent_build made of the turn's input, the cursor is in a3 and what is left
   in t1, and s2, s4 and s7 hold the len cell's address, &e62 and the first block, the three arguments the call
   and the record copy after it use. *)
Definition hsu_cut_J (cx : hsu_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (ed : ent) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_pod_base cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx cx W2 mem2 regs2
(hsu_L_Dc cx sh np ps cnt es
 ++ [(LReg 13, hsu_cur cx rest r); (LReg 6, Z.of_nat (length r));
     (LReg 18, e_pp (x_e cx) + 0x4000); (LReg 20, e_F (x_e cx) + HSU_E62);
     (LReg 23, e_pp (x_e cx))]) /\
hsu_fsh_at cx W2 mem2 hsu_PJ /\
hsu_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
hsu_obj_at cx W2 mem2 HSU_E62 (ent_mem ed) /\
(ed, r) = ent_build rr /\ ent_wf ed.

(* ---------------- CL: the count is reached; the Struct's size word is patched ----------------
   The pod loop wrote cnt pods and e62 is out of scope again. *)
Definition hsu_cut_CL (cx : hsu_scx) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_core cx (hsu_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx cx W2 mem2 regs2
(hsu_Rc0 cx ++ hsu_Kc cx sh np
 ++ [(LCell XR 0x98, Z.of_nat (length ps)); (LCell XR 0x88, hsu_at_of sh ps);
     (LCell XR 0x90, e_pp (x_e cx) + hsu_at_of sh ps);
     (LCell XR 0x80, 1); (LCell XR 0x140, hsu_first ps);
     (LReg 18, e_pp (x_e cx) + 0x4000); (LReg 23, -8);
     (LReg 21, hsu_cur cx rest r); (LReg 26, Z.of_nat (length r))]) /\
hsu_fsh_at cx W2 mem2 hsu_P0 /\
hsu_pp_at cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
hsu_in cx rest /\ hsu_suffix rest r /\ hsu_wf sh ps /\
e_len (x_e cx) = hd_len rest /\
ps = fst (props_loop sh (length ps) (hsu_r0 rest)) /\
hsu_pod_tie sh ps cnt es rest r /\
sh = hsu_sh rest /\ np = hsu_np rest /\ Z.of_nat (length ps) < np /\ np <= 3 /\
sh <> 7 /\ (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\
Forall ent_wf es /\ Z.of_nat (length es) = cnt.

(* ---------------- the latch: one property is written ----------------
   Image B has ONE latch entry (image A has two): the shape-7 piece, the Int-7 piece and the Struct's close all
   reach it with the property index still in t0 (the pc increments it), `seen` after this property in a3, the
   cursor in a7 and what is left in t3. *)
Definition hsu_cut_LATCH (cx : hsu_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_core cx (hsu_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hsu_fsh_at cx W2 mem2 hsu_P0 /\
hsu_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
hsu_in cx rest /\ hsu_suffix rest r /\ hsu_wf sh ps /\
sh = hsu_sh rest /\ np = hsu_np rest /\ 1 <= Z.of_nat (length ps) <= np /\ np <= 3 /\
(ps, r) = props_loop sh (length ps) (hsu_r0 rest) /\
hsu_at_cx cx W2 mem2 regs2
(hsu_Rc1 cx ++ hsu_Kc cx sh np
 ++ [(LReg 5, Z.of_nat (length ps) - 1); (LReg 13, hsu_seen ps);
     (LReg 17, hsu_cur cx rest r); (LReg 28, Z.of_nat (length r))]).

(* ---------------- P / P1: every property is written ----------------
   P is entered only when the object has no property, with the cursor in s2; P1 is the latch's exit, where the
   cursor is in a7. Both keep what is left in t3. The loop's own cells are dead from here on; what the rest of
   M01 reads is the block, the cap, the null flag and the three addresses of the top size word. *)
Definition hsu_L_P (cx : hsu_scx) : list (hd_loc * Z) :=
let e := x_e cx in
[(LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 27, SHADOW_OFF);
 (LCell XR 0x8, e_pp e + 0x4008); (LCell XR 0x18, e_F e); (LCell XR 0x20, e_cap e);
 (LCell XR 0x28, 0); (LCell XR 0x30, e_pp e); (LCell XR 0x38, 1 - e_null e); (LCell XR 0x48, e_F e);
 (LCell XR 0xe0, Z.shiftr (e_pp e + 0x4d14) 3); (LCell XR 0xf0, - e_pp e - 1);
 (LCell XR 0x108, -0x3ffd); (LCell XR 0x120, e_pp e + 0x4d14); (LCell XR 0x138, e_pp e + 0x4000);
 (LCell XR 0x148, e_pp e); (LCell XR 0x150, shadow_addr (e_pp e + 0x4000))].
Definition hsu_Pbody (cx : hsu_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_core cx (hsu_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hsu_fsh_at cx W2 mem2 hsu_P0 /\
hsu_pp_at cx W2 mem2 (pc_image (PbCut sh ps None)) /\
hsu_in cx rest /\ hsu_suffix rest r /\ hsu_wf sh ps /\
e_len (x_e cx) = hd_len rest /\
sh = hsu_sh rest /\ np = hsu_np rest /\ Z.of_nat (length ps) = np /\
(ps, r) = props_loop sh (length ps) (hsu_r0 rest).
Definition hsu_cut_P (cx : hsu_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_Pbody cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx cx W2 mem2 regs2
(hsu_L_P cx ++ [(LReg 18, hsu_cur cx rest r); (LReg 28, Z.of_nat (length r))]).
Definition hsu_cut_P1 (cx : hsu_scx) (sh np : Z) (ps : list (Z * pval)) (rest r : list byte)
ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_Pbody cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx cx W2 mem2 regs2
(hsu_L_P cx ++ [(LReg 17, hsu_cur cx rest r); (LReg 28, Z.of_nat (length r))]).

(* ---------------- R and RT: the corruption (pod.h:441-448) ----------------
   The object is complete (its top size word was patched), so the block holds the image of the record with no
   corruption yet. The loop writes one byte a turn: a3 = kk is the index, a2 = cnt - kk what is left of the count
   the input byte gave, a4 = off, a0 is the cursor of the byte reads and a5 what is left of the input; a6 = 1 is
   the cursor test's bound, t2 the len cell's address, s2 the first block and s8 the address of its corrupt word.
   It also leaves when off + kk reaches the length, so the bytes written, bs, are the first min(cnt, len - off) of
   the input's. At RT the corruption is done but the corrupt word is NOT yet written, so the block still holds the
   image with corrupt false and the record's own bytes. *)
Definition hsu_L_post (cx : hsu_scx) : list (hd_loc * Z) :=
let e := x_e cx in
[(LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 27, SHADOW_OFF);
 (LReg 7, e_pp e + 0x4000); (LReg 18, e_pp e); (LReg 24, e_pp e + 0x4d18);
 (LCell XR 0x8, e_pp e + 0x4008); (LCell XR 0x18, e_F e); (LCell XR 0x20, e_cap e);
 (LCell XR 0x38, 1 - e_null e); (LCell XR 0x48, e_F e);
 (LCell XR 0xe0, Z.shiftr (e_pp e + 0x4d14) 3); (LCell XR 0x108, -0x3ffd);
 (LCell XR 0x120, e_pp e + 0x4d14); (LCell XR 0x148, e_pp e);
 (LCell XR 0x150, shadow_addr (e_pp e + 0x4000))].
(* the block's bytes with the first kk corruption bytes written at off *)
Definition hsu_img_corr (sh : Z) (ps : list (Z * pval)) (off : Z) (bs : list byte) (kk : Z) : list byte :=
pp_image (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) (firstn (Z.to_nat kk) bs))
(is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
(params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false.
Definition hsu_corr_wf (sh : Z) (ps : list (Z * pval)) (off : Z) (bs : list byte) (cnt : Z) : Prop :=
8 <= off /\ off + Z.of_nat (length bs) <= hsu_plen sh ps /\ (length bs <= 7)%nat /\
0 < cnt <= 7 /\ Z.of_nat (length bs) = Z.min cnt (hsu_plen sh ps - off).
Definition hsu_cut_R (cx : hsu_scx) (sh : Z) (ps : list (Z * pval)) (rest r : list byte)
(off : Z) (bs : list byte) (cnt kk : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_core cx (hsu_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx cx W2 mem2 regs2
(hsu_L_post cx ++ [(LReg 13, kk); (LReg 12, cnt - kk); (LReg 14, off); (LReg 16, 1);
                   (LReg 10, hsu_cur cx rest r); (LReg 15, Z.of_nat (length r));
                   (LCell XR 0xf0, - e_pp (x_e cx) - 1)]) /\
hsu_fsh_at cx W2 mem2 hsu_P0 /\
hsu_pp_at cx W2 mem2 (hsu_img_corr sh ps off bs kk) /\
hsu_in cx rest /\ hsu_suffix rest r /\ hsu_wf sh ps /\
e_len (x_e cx) = hd_len rest /\
fst (pod_build rest) = PodRec sh ps (Some (off, bs)) /\
hsu_corr_wf sh ps off bs cnt /\ 0 <= kk < cnt /\ kk <= Z.of_nat (length bs) /\
skipn (Z.to_nat kk) bs = fst (fuzz_u8s (length bs - Z.to_nat kk) r).
Definition hsu_cut_RT (cx : hsu_scx) (sh : Z) (ps : list (Z * pval)) (off : Z) (bs : list byte)
(rest r : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_core cx (hsu_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx cx W2 mem2 regs2 (hsu_L_post cx) /\
hsu_fsh_at cx W2 mem2 hsu_P0 /\
hsu_pp_at cx W2 mem2 (hsu_img_corr sh ps off bs (Z.of_nat (length bs))) /\
hsu_in cx rest /\ hsu_suffix rest r /\ hsu_wf sh ps /\
e_len (x_e cx) = hd_len rest /\
fst (pod_build rest) = PodRec sh ps (Some (off, bs)) /\
8 <= off /\ off + Z.of_nat (length bs) <= hsu_plen sh ps /\ (length bs <= 7)%nat.

(* ---------------- C2: the build is done; the second request is in a0 ----------------
   This cut IS headamp_build_contract's post, at the pc its contract names (hi_c2 I): the C2 value list, the
   frame's shadow back to the prologue's, and the block holding Layout.pp_bytes of the record. *)
Definition hsu_cut_C2 (cx : hsu_scx) (rest : list byte) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_core cx (hsu_E1 cx) ly2 S2 W2 regs2 mem2 md2 /\
hd_cut segs (w_H W2) mem2 regs2 (x_e cx) (hi_L2 I) /\
hsu_fsh_at cx W2 mem2 hsu_P0 /\ hsu_pp_at cx W2 mem2 (pp_bytes (fst (pod_build rest))) /\
e_len (x_e cx) = hd_len rest.

(* ===================================================================================================
   THE CONTINUATIONS: "from this cut, the rest of the walk realizes POST"
   ===================================================================================================
   One per cut, with the LOOP INDEX as an argument (and never under the inner quantifier), so that the
   latch of a loop can hand the head its next index and the closure is an induction on the index, not a
   circular hypothesis: hsu_from_N .. (S i) is what the property loop's latch gives, hsu_from_C .. i (S k)
   what the pod loop's latch gives. A piece lemma is `hsu_start_M01 cx rest -> <the continuations of its end
   cuts> -> <the continuation of its start cut>`, so a lane proving one piece takes the other lanes'
   continuations as hypotheses and never sees their proofs. POST is generic. *)
Section f.
Variable cx : hsu_scx.
Variable POST : world segs -> config -> Prop.
Variable rest : list byte.

Definition hsu_from_B7 : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 r np, hsu_cut_B7 cx rest r np ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (bi_B7 BI) regs2 mem2 md2) POST.
Definition hsu_from_BO : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 r sh np, hsu_cut_BO cx rest r sh np ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (bi_BO BI) regs2 mem2 md2) POST.
Definition hsu_from_PH : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 r sh np, hsu_cut_PH cx rest r sh np ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (bi_PH BI) regs2 mem2 md2) POST.
Definition hsu_from_N (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r, (length ps = i)%nat ->
hsu_cut_N cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (bi_N BI) regs2 mem2 md2) POST.
Definition hsu_from_SEL7 (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 np ps r, (length ps = i)%nat ->
hsu_cut_SEL7 cx np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (bi_SEL7 BI) regs2 mem2 md2) POST.
Definition hsu_from_SELK (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np sel ps r, (length ps = i)%nat ->
hsu_cut_SELK cx sh np sel ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (bi_SELK BI) regs2 mem2 md2) POST.
Definition hsu_from_SELI (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np sel ps r, (length ps = i)%nat ->
hsu_cut_SELI cx sh np sel ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (bi_SELI BI) regs2 mem2 md2) POST.
Definition hsu_from_SELS (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np sel ps r, (length ps = i)%nat ->
hsu_cut_SELS cx sh np sel ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (bi_SELS BI) regs2 mem2 md2) POST.
Definition hsu_from_C (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es r, (length ps = i)%nat -> (length es = k)%nat ->
hsu_cut_C cx sh np ps cnt es rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (bi_C BI) regs2 mem2 md2) POST.
Definition hsu_from_D (i k : nat) (kd : Z) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r, (length ps = i)%nat -> (length es = k)%nat ->
hsu_cut_D cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (hsu_pc_D kd) regs2 mem2 md2) POST.
Definition hsu_from_D0E (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es, (length ps = i)%nat -> (length es = k)%nat ->
hsu_cut_D0E cx sh np ps cnt es rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (bi_D0E BI) regs2 mem2 md2) POST.
Definition hsu_from_G (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r pb chs, (length ps = i)%nat -> (length es = k)%nat ->
hsu_cut_G cx sh np ps cnt es rest rr r pb chs ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (bi_G BI) regs2 mem2 md2) POST.
Definition hsu_from_J (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r ed, (length ps = i)%nat -> (length es = k)%nat ->
hsu_cut_J cx sh np ps cnt es rest rr r ed ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (bi_J BI) regs2 mem2 md2) POST.
Definition hsu_from_CL (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es r, (length ps = i)%nat ->
hsu_cut_CL cx sh np ps cnt es rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (bi_CL BI) regs2 mem2 md2) POST.
Definition hsu_from_LATCH (i : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r, (length ps = S i)%nat ->
hsu_cut_LATCH cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (bi_LATCH BI) regs2 mem2 md2) POST.
Definition hsu_from_P : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r,
hsu_cut_P cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (bi_P BI) regs2 mem2 md2) POST.
Definition hsu_from_P1 : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps r,
hsu_cut_P1 cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (bi_P1 BI) regs2 mem2 md2) POST.
Definition hsu_from_R (kk : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh ps r off bs cnt,
hsu_cut_R cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (bi_R BI) regs2 mem2 md2) POST.
Definition hsu_from_RT : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh ps off bs r,
hsu_cut_RT cx sh ps off bs rest r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (bi_RT BI) regs2 mem2 md2) POST.
Definition hsu_from_C2 : Prop :=
forall ly2 S2 W2 regs2 mem2 md2,
hsu_cut_C2 cx rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs (hi_c2 I) regs2 mem2 md2) POST.
End f.

(* ===================================================================================================
   THE PIECE STATEMENTS, one per walk lane of the build
   =================================================================================================== *)
(* W3a: C1 -> the object's header (pod.h:384-395): the NULL test (dead), the block's memset, the two
   header reads, the top size word, and the header of this shape. Its start is the segment's own start
   state, which is headamp_build_contract's premise set. *)
Definition hsu_start_M01 (cx : hsu_scx) (rest : list byte) : Prop :=
hsu_pre cx (hi_shA I) /\
hd_cut segs (w_H (x_W cx)) (x_memc cx) (x_regs cx) (x_e cx) (hi_L1 I) /\
e_len (x_e cx) = hd_len rest /\ hsu_in cx rest.
Definition hsu_piece_W3a_stmt : Prop :=
forall cx POST rest,
hsu_start_M01 cx rest -> hsu_from_B7 cx POST rest -> hsu_from_BO cx POST rest ->
SRr segs (x_W cx) (cfg_at segs (hi_c1 I) (x_regs cx) (x_memc cx) (x_mdc cx)) POST.
(* W3b: the two header pieces and the property loop's preheader (pod.h:389-398). *)
Definition hsu_piece_W3b_hdr_stmt : Prop :=
forall cx POST rest,
hsu_start_M01 cx rest -> hsu_from_PH cx POST rest -> hsu_from_BO cx POST rest.
Definition hsu_piece_W3b_b7_stmt : Prop :=
forall cx POST rest,
hsu_start_M01 cx rest -> hsu_from_PH cx POST rest -> hsu_from_B7 cx POST rest.
Definition hsu_piece_W3b_pre_stmt : Prop :=
forall cx POST rest,
hsu_start_M01 cx rest -> hsu_from_N cx POST rest 0 -> hsu_from_P cx POST rest ->
hsu_from_PH cx POST rest.
(* W4: one property's selector, its shape-7 body (which calls pod_write_ent), its key, and the loop's latch. *)
Definition hsu_piece_W4_sel_stmt : Prop :=
forall cx POST rest i,
hsu_start_M01 cx rest -> hsu_from_SEL7 cx POST rest i -> hsu_from_SELK cx POST rest i ->
hsu_from_N cx POST rest i.
Definition hsu_piece_W4_int7_stmt : Prop :=
forall cx POST rest i,
hsu_start_M01 cx rest -> hsu_from_LATCH cx POST rest i -> hsu_from_SEL7 cx POST rest i.
Definition hsu_piece_W4_key_stmt : Prop :=
forall cx POST rest i,
hsu_start_M01 cx rest -> hsu_from_SELS cx POST rest i -> hsu_from_SELI cx POST rest i ->
hsu_from_SELK cx POST rest i.
Definition hsu_piece_W4_latch_stmt : Prop :=
forall cx POST rest i,
hsu_start_M01 cx rest -> hsu_from_N cx POST rest (S i) -> hsu_from_P1 cx POST rest ->
hsu_from_LATCH cx POST rest i.
(* W5: the Int-7 value pod, the params Struct's header and count, and its close (pod.h:412-438). *)
Definition hsu_piece_W5_int_stmt : Prop :=
forall cx POST rest i,
hsu_start_M01 cx rest -> hsu_from_LATCH cx POST rest i -> hsu_from_SELI cx POST rest i.
Definition hsu_piece_W5_open_stmt : Prop :=
forall cx POST rest i,
hsu_start_M01 cx rest -> hsu_from_C cx POST rest i 0 -> hsu_from_CL cx POST rest i ->
hsu_from_SELS cx POST rest i.
Definition hsu_piece_W5_close_stmt : Prop :=
forall cx POST rest i,
hsu_start_M01 cx rest -> hsu_from_LATCH cx POST rest i -> hsu_from_CL cx POST rest i.
(* W6a: the switch's dispatch and its two input-driven exits, then cases 2 and 3. *)
Definition hsu_piece_W6a_disp_stmt : Prop :=
forall cx POST rest i k,
hsu_start_M01 cx rest -> (forall kd, hsu_from_D cx POST rest i k kd) -> hsu_from_D0E cx POST rest i k ->
hsu_from_C cx POST rest i k.
Definition hsu_piece_W6a_cases_stmt : Prop :=
forall cx POST rest i k kd,
hsu_start_M01 cx rest -> In (kd mod 10) [2; 3] -> hsu_from_J cx POST rest i k ->
hsu_from_D cx POST rest i k kd.
(* W6b: cases 1, 4, 5 and 9. W6c: cases 6, 7 and 8. *)
Definition hsu_piece_W6b_stmt : Prop :=
forall cx POST rest i k kd,
hsu_start_M01 cx rest -> In (kd mod 10) [1; 4; 5; 9] -> hsu_from_J cx POST rest i k ->
hsu_from_D cx POST rest i k kd.
Definition hsu_piece_W6c_stmt : Prop :=
forall cx POST rest i k kd,
hsu_start_M01 cx rest -> In (kd mod 10) [6; 7; 8] -> hsu_from_J cx POST rest i k ->
hsu_from_D cx POST rest i k kd.
(* W7a: case 0 up to the parts, from both its entries. W7b: the parts and the key's text. *)
Definition hsu_piece_W7a_stmt : Prop :=
forall cx POST rest i k kd,
hsu_start_M01 cx rest -> kd mod 10 = 0 -> hsu_from_G cx POST rest i k ->
hsu_from_D cx POST rest i k kd /\ hsu_from_D0E cx POST rest i k.
Definition hsu_piece_W7b_stmt : Prop :=
forall cx POST rest i k,
hsu_start_M01 cx rest -> hsu_from_J cx POST rest i k -> hsu_from_G cx POST rest i k.
(* W8: the call of pod_write_ent and the record copy (pod.h:428-432), then the pod loop's latch. *)
Definition hsu_piece_W8_stmt : Prop :=
forall cx POST rest i k,
hsu_start_M01 cx rest -> hsu_from_C cx POST rest i (S k) -> hsu_from_CL cx POST rest i ->
hsu_from_J cx POST rest i k.
(* W10: the top size word, the corruption and the second block's request (pod.h:440-448, fuzz.h:73). *)
Definition hsu_piece_W10_post_stmt : Prop :=
forall cx POST rest,
hsu_start_M01 cx rest -> (forall kk, hsu_from_R cx POST rest kk) -> hsu_from_RT cx POST rest ->
hsu_from_C2 cx POST rest ->
hsu_from_P cx POST rest /\ hsu_from_P1 cx POST rest.
Definition hsu_piece_W10_corr_stmt : Prop :=
forall cx POST rest kk,
hsu_start_M01 cx rest -> hsu_from_R cx POST rest (S kk) -> hsu_from_RT cx POST rest ->
hsu_from_R cx POST rest kk.
Definition hsu_piece_W10_req_stmt : Prop :=
forall cx POST rest,
hsu_start_M01 cx rest -> hsu_from_C2 cx POST rest -> hsu_from_RT cx POST rest.

(* ============================== checks on the stated data ==============================
   Every cut list names each location once, so no list binds one location to two values. *)
Definition hsu_lkey (l : hd_loc) : Z :=
match l with LReg r => r | LCell XR o => 0x10000 + o | LCell _ _ => -1 end.
Fixpoint hsu_nodupb (l : list Z) : bool :=
match l with [] => true | x :: t => negb (existsb (Z.eqb x) t) && hsu_nodupb t end.
Definition hsu_keys_ok (L : list (hd_loc * Z)) : bool := hsu_nodupb (map (fun f => hsu_lkey (fst f)) L).
Lemma hsu_cut_lists_nodup : forall (cx : hsu_scx) sh np sel ps cnt es (rest r : list byte) kd pb,
hsu_keys_ok (hsu_L_hdr cx sh np rest r) = true /\
hsu_keys_ok (hsu_L_hdr cx sh np rest r ++ [(LReg 13, sh)]) = true /\
hsu_keys_ok (hsu_L_PH cx sh np rest r) = true /\
hsu_keys_ok (hsu_L_N cx sh np ps rest r) = true /\
hsu_keys_ok (hsu_L_SEL cx sh np ps rest r) = true /\
hsu_keys_ok (hsu_L_SEL cx sh np ps rest r ++ [(LReg 11, sel); (LReg 23, -8); (LReg 26, 1)]) = true /\
hsu_keys_ok (hsu_L_KEY cx sh np sel ps rest r) = true /\
hsu_keys_ok (hsu_L_KEY cx sh np sel ps rest r
 ++ [(LReg 6, -0x4001); (LReg 18, e_pp (x_e cx) + 0x4000); (LReg 23, -8)]) = true /\
hsu_keys_ok (hsu_L_pod cx sh np ps cnt rest r ++ [(LReg 11, Z.of_nat (length es))]) = true /\
hsu_keys_ok (hsu_L_D cx sh np ps cnt es rest r kd) = true /\
hsu_keys_ok (hsu_L_Dc cx sh np ps cnt es ++ [(LReg 21, hsu_cur cx rest []); (LReg 23, -8)]) = true /\
hsu_keys_ok (hsu_L_Dc cx sh np ps cnt es
 ++ [(LCell XR 0x110, hsu_cur cx rest r); (LReg 6, Z.of_nat (length r));
     (LReg 18, e_F (x_e cx) + HSU_CH); (LReg 26, pb)]) = true /\
hsu_keys_ok (hsu_L_Dc cx sh np ps cnt es
 ++ [(LReg 13, hsu_cur cx rest r); (LReg 6, Z.of_nat (length r));
     (LReg 18, e_pp (x_e cx) + 0x4000); (LReg 20, e_F (x_e cx) + HSU_E62);
     (LReg 23, e_pp (x_e cx))]) = true /\
hsu_keys_ok (hsu_Rc0 cx ++ hsu_Kc cx sh np
 ++ [(LCell XR 0x98, Z.of_nat (length ps)); (LCell XR 0x88, hsu_at_of sh ps);
     (LCell XR 0x90, e_pp (x_e cx) + hsu_at_of sh ps);
     (LCell XR 0x80, 1); (LCell XR 0x140, hsu_first ps);
     (LReg 18, e_pp (x_e cx) + 0x4000); (LReg 23, -8);
     (LReg 21, hsu_cur cx rest r); (LReg 26, Z.of_nat (length r))]) = true /\
hsu_keys_ok (hsu_Rc1 cx ++ hsu_Kc cx sh np
 ++ [(LReg 5, Z.of_nat (length ps) - 1); (LReg 13, hsu_seen ps);
     (LReg 17, hsu_cur cx rest r); (LReg 28, Z.of_nat (length r))]) = true /\
hsu_keys_ok (hsu_L_P cx ++ [(LReg 18, hsu_cur cx rest r); (LReg 28, Z.of_nat (length r))]) = true /\
hsu_keys_ok (hsu_L_P cx ++ [(LReg 17, hsu_cur cx rest r); (LReg 28, Z.of_nat (length r))]) = true /\
hsu_keys_ok (hsu_L_post cx) = true /\
hsu_keys_ok (hsu_L_post cx ++ [(LReg 13, 0); (LReg 12, 0); (LReg 14, 0); (LReg 16, 1);
                               (LReg 10, 0); (LReg 15, 0); (LCell XR 0xf0, 0)]) = true.
Proof.
intros. unfold hsu_L_D. destruct (kd mod 10 =? 9); vm_compute; repeat split.
Qed.
(* The two patterns the builder makes cover exactly the granules the prologue's pattern has, so a cut that names
   one of them names every granule of the frame's shadow; the windows they open hold 0 (the object is in scope)
   and every other granule is the prologue's. *)
Lemma hsu_patterns_len : length hsu_PJ = length hsu_P0 /\ length hsu_PG = length hsu_P0.
Proof. unfold hsu_PG, hsu_PJ. rewrite !hsu_open_length. split; reflexivity. Qed.
(* the window of each pattern holds 0 (the object is in scope) and every other granule is the prologue's *)
Lemma hsu_PJ_in : forall i, (66 <= i < 79)%nat -> (i < length hsu_P0)%nat -> nth i hsu_PJ 0 = 0.
Proof. intros i Hw Hi. unfold hsu_PJ, HSU_G_E62, ENT_GRAN. apply hsu_open_in; lia. Qed.
Lemma hsu_PJ_out : forall i, ((i < 66)%nat \/ (79 <= i)%nat) -> (i < length hsu_P0)%nat ->
nth i hsu_PJ 0 = nth i hsu_P0 0.
Proof. intros i Hw Hi. unfold hsu_PJ, HSU_G_E62, ENT_GRAN. apply hsu_open_out; lia. Qed.
Lemma hsu_PG_in : forall i,
((4 <= i < 16)%nat \/ (20 <= i < 23)%nat \/ (66 <= i < 79)%nat) -> (i < length hsu_P0)%nat ->
nth i hsu_PG 0 = 0.
Proof.
intros i Hw Hi. unfold hsu_PG, hsu_PJ, HSU_G_T, HSU_G_CH, HSU_G_E62, ENT_GRAN in *.
assert (LJ : length (hsu_open 66 13 hsu_P0) = length hsu_P0) by apply hsu_open_length.
assert (LC : length (hsu_open 20 3 (hsu_open 66 13 hsu_P0)) = length hsu_P0)
  by (rewrite hsu_open_length; exact LJ).
destruct Hw as [H|[H|H]].
- apply hsu_open_in; [lia | rewrite LC; lia].
- rewrite hsu_open_out by (rewrite ?LC; lia). apply hsu_open_in; [lia | rewrite LJ; lia].
- rewrite hsu_open_out by (rewrite ?LC; lia).
  rewrite hsu_open_out by (rewrite ?LJ; lia). apply hsu_open_in; lia.
Qed.
Lemma hsu_PG_out : forall i,
((i < 4)%nat \/ (16 <= i < 20)%nat \/ (23 <= i < 66)%nat \/ (79 <= i)%nat) -> (i < length hsu_P0)%nat ->
nth i hsu_PG 0 = nth i hsu_P0 0.
Proof.
intros i Hw Hi. unfold hsu_PG, hsu_PJ, HSU_G_T, HSU_G_CH, HSU_G_E62, ENT_GRAN in *.
assert (LJ : length (hsu_open 66 13 hsu_P0) = length hsu_P0) by apply hsu_open_length.
assert (LC : length (hsu_open 20 3 (hsu_open 66 13 hsu_P0)) = length hsu_P0)
  by (rewrite hsu_open_length; exact LJ).
rewrite hsu_open_out by (rewrite ?LC; lia).
rewrite hsu_open_out by (rewrite ?LJ; lia).
apply hsu_open_out; lia.
Qed.

End d.
End c.
End b.
