(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC93.v:56-59, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* reac_box_name (fuzz_identity.asan-ubsan 0x82d74, 0x85c bytes, AF_reac_box_name = 0x2600): the predicates its
   contract states (moved here from lib/B/Prog/reac_box_name.v so that the segment files of the walk can use them
   without requiring that file) and the states at the cut points of its program walk.
   The walk is cut at measured pcs into segment lemmas, each stated in the form of cgif lib/A/AC8b.v tcbb_loopX:
   the state at a cut point as machine registers and memory facts. lib/B/Prog/reac_box_name.v chains them into
   pb_reac_box_name. Offsets below are from the function's first slot (0x82d74).
   The cut points (pc, offset, what holds there):
     C1  0x83000 +0x28c  back from memset #1: frame taken, arguments checked, stem selected, wb initialised;
     C2  0x83088 +0x314  head of the stem copy loop (stem -> nb), i-th character in a0;
     C3  0x830cc +0x358  after the stem copy;
     C4  0x83128 +0x3b4  head of the w4 copy loop (w4 -> nb), j-th character in a0;
     C5  0x8316c +0x3f8  nb holds the name (bn_NM when it fits);
     C6  0x831c8 +0x454  head of the token loop (nm -> tb);
     C7  0x83230 +0x4bc  after the token loop;
     C8  0x83298 +0x524  head of the name copy into the display (nm -> db);
     C9  0x832dc +0x568  after that copy;
     C10 0x833e0 +0x66c  db holds the display;
     R   0x834ac +0x738  the frame release (magic, __asan_set_shadow_f5, flag byte), s4 = the result. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun PaShadow PaJournal IdentBase IdentRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentBSyms IdentBList IdentBPa IdentBPaLib.
(* The model of the three buffers (sbm_ch / sbm_str: what the sb_ch / sb_dec calls do to a buffer). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import reac_box_name_sbm.
(* The plain model of reac_box_name (released, origin/ossv/recipes c8557374ad2e), used as it is. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
(* The three buffers the call may write (when it accepts, nm/tk/dp are copied with their NUL; each copy is
   at most 24 / 24 / 48 bytes, the sizes of the frame arrays): the write tokens of the journal. *)
Definition rbn_fp (name name_len token token_len display display_len : Z) : list (Z * Z) :=
  [(name, if name =? 0 then name else name + Z.min name_len 24);
   (token, if token =? 0 then token else token + Z.min token_len 24);
   (display, if display =? 0 then display else display + Z.min display_len 48)].
(* A null pointer's range is empty (the harness's refusing call passes name = NULL with
   name_len = 8, fuzz_identity.c:424). The two lemmas are the A twin's
   (lib/A/Prog/reac_box_name_cuts.v), copied as they are. *)
Lemma rbn_fp_in : forall name name_len token token_len display display_len a,
  inFP (rbn_fp name name_len token token_len display display_len) a ->
  (name <> 0 /\ name <= a < name + Z.min name_len 24) \/ (token <> 0 /\ token <= a < token + Z.min token_len 24) \/
  (display <> 0 /\ display <= a < display + Z.min display_len 48).
Proof.
intros n nl t tl d dl a (r & Hr & Ha). revert Ha. unfold rbn_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd];
[destruct (n =? 0) eqn:E | destruct (t =? 0) eqn:E | destruct (d =? 0) eqn:E];
rewrite ?Z.eqb_eq, ?Z.eqb_neq in E; lia.
Qed.
Lemma rbn_fp_closed : forall name name_len token token_len display display_len,
  0 <= name -> 0 <= token -> 0 <= display ->
  ~ YI16.sink_open_fp (rbn_fp name name_len token token_len display display_len).
Proof.
intros n nl t tl d dl Hn Ht Hd H0. unfold YI16.sink_open_fp in H0. apply (proj1 (in_fp_inFP _ _)) in H0.
apply rbn_fp_in in H0. lia.
Qed.
Section h.
Variable B : asyms.
(* The registered globals of the image with their sizes (IdentRo.v globs_marked; the composition gives the
   list and its start-up certificate). *)
Variable G : list (Z * Z).
(* A NUL-terminated string s at a that the call reads with the ASan 1-byte load checks, with the strlen
   wrapper (musl's word loop reads up to the end of the 8-byte word that holds the NUL) and with the bcmp
   wrapper: bytes, shadow, the shadow's visibility and the word tail. *)
Definition rbn_cstr (W : world SEGS) (mem : word -> option byte) (a : Z) (s : list Z) : Prop :=
  Forall (fun c => 0 < c < 256) s /\ Z.of_nat (length s) < 2 ^ 31 /\
  0 < a /\ amem_range a (Z.of_nat (length s) + 8) /\
  garr8 SEGS (mrestrict (w_H W) mem) a (s ++ [0]) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a (Z.of_nat (length s) + 1) /\
  shadow_hull_vis (aview SEGS (w_H W) mem) a (Z.of_nat (length s) + 1) /\
  (forall x, a + Z.of_nat (length s) < x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
     aview SEGS (w_H W) mem x <> None).
(* [a, a + n) lies in one registered global (its shadow: IdentRo.v ro_read_ok_glob at each read). *)
Definition rbn_glob (a n : Z) : Prop :=
  exists q z, In (q, z) G /\ q <= a /\ a + n <= q + z.
(* [a, a + n) are image bytes the call's journal keeps across every call it makes (lib/Reusable/YCbq.v
   ajournal, lib/B/Prog/IdentBCJ.v tcj_kept): in the image, not the runtime's own, not errno. *)
Definition rbn_fixed (a n : Z) : Prop :=
  forall x, a <= x < a + n ->
    in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4).
(* An image string (CONVENTIONS section 3: image reads lie in [IMG_LO, IMG_TOP); 64 bytes of margin for the
   shadow window IdentRo.v ro_hull reads): bytes, its registered global, kept bytes, and the word tail, which
   is image data (seg_rom) and so readable in every state. *)
Definition rbn_imgstr (W : world SEGS) (mem : word -> option byte) (a : Z) (s : list Z) : Prop :=
  IMG_LO + 64 <= a /\ a + Z.of_nat (length s) + 1 + 64 <= IMG_TOP /\
  Forall (fun c => 0 < c < 256) s /\
  garr8 SEGS (mrestrict (w_H W) mem) a (s ++ [0]) /\
  rbn_glob a (Z.of_nat (length s) + 1) /\ rbn_fixed a (Z.of_nat (length s) + 1) /\
  (forall x, a + Z.of_nat (length s) < x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
     seg_rom SEGS (Z_to_bv 64 x) <> None).
(* The image constants the call reads (fuzz_identity.asan-ubsan: switch.table.reac_box_name = object 22
   0x9b4e0, in .data.rel.ro, its words 0x21160 "S-0808", 0x21180 "S-1608", 0x211a0 "S-4000S"; .str.3 "REAC" =
   object 19 0x211c0; .str.4 " (" = object 23 0x211e0; .str.5 " in / " = object 24 0x21200; .str.6 " out)" =
   object 25 0x21220; all registered ASan globals). The listing tests the three literal strings' low address
   bits as if they were 8-aligned (the loop index against the shadow byte, 0x83318, 0x83374, 0x833d0), so their
   alignment is part of the fact; the table's entry is read with an 8-byte check (shadow byte 0, 0x82fb4). *)
Definition rbn_img (W : world SEGS) (mem : word -> option byte) : Prop :=
  VAL (A_OBJ 22) mod 8 = 0 /\
  IMG_LO + 64 <= VAL (A_OBJ 22) /\ VAL (A_OBJ 22) + 24 + 64 <= IMG_TOP /\
  in_zs B (VAL (A_OBJ 22)) 24 /\ rbn_fixed (VAL (A_OBJ 22)) 24 /\
  (exists s1 s2 s3,
     val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 22)) 8 s1 /\
     val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 22) + 8) 8 s2 /\
     val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 22) + 16) 8 s3 /\
     rbn_imgstr W mem s1 (bn_STEM 1) /\ rbn_imgstr W mem s2 (bn_STEM 2) /\ rbn_imgstr W mem s3 (bn_STEM 3)) /\
  rbn_imgstr W mem (VAL (A_OBJ 19)) (bn_STEM 0) /\
  VAL (A_OBJ 23) mod 8 = 0 /\ rbn_imgstr W mem (VAL (A_OBJ 23)) [32; 40] /\
  VAL (A_OBJ 24) mod 8 = 0 /\ rbn_imgstr W mem (VAL (A_OBJ 24)) [32; 105; 110; 32; 47; 32] /\
  VAL (A_OBJ 25) mod 8 = 0 /\ rbn_imgstr W mem (VAL (A_OBJ 25)) [32; 111; 117; 116; 41].
(* said_name: NULL (sd = []) or a string sd in one live side-stack frame of the caller (fuzz_identity.c:420,
   id.model_name), the word tail included (plain contract: bn_said / bn_cstr). *)
Definition rbn_said (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (said : Z) (sd : list Z)
  : Prop :=
  (said = 0 /\ sd = []) \/
  (said <> 0 /\ rbn_cstr W mem said sd /\
   exists cid pos, In (cid, pos) (frames S) /\
     frame_addr ly cid pos <= said /\ said + Z.of_nat (length sd) + 8 <= frame_addr ly cid pos + fs_frame_bytes cid).
(* The three buffers: each written range inside a live heap block, the three ranges pairwise disjoint
   (plain contract: bn_bufs). *)
Definition rbn_bufs (ly : alayout) (S : astate) (name name_len token token_len display display_len : Z) : Prop :=
  (exists q N, In (q, N) (ablocks B ly S) /\ q <= name /\ name + Z.min name_len 24 <= q + N) /\
  (exists q N, In (q, N) (ablocks B ly S) /\ q <= token /\ token + Z.min token_len 24 <= q + N) /\
  (exists q N, In (q, N) (ablocks B ly S) /\ q <= display /\ display + Z.min display_len 48 <= q + N) /\
  (name + Z.min name_len 24 <= token \/ token + Z.min token_len 24 <= name) /\
  (name + Z.min name_len 24 <= display \/ display + Z.min display_len 48 <= name) /\
  (token + Z.min token_len 24 <= display \/ display + Z.min display_len 48 <= token).
(* What the call leaves (the post's own part, under apost_base): the world and the heap blocks unchanged, and
   the plain model's result (reac_box_name_c.reac_box_name_contract): on acceptance a0 = 0 and the name / token /
   display strings with their NUL, the rest of the buffers kept; on refusal a0 = -1 and the buffers kept. *)
Definition rbn_postQ (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte)
  (f : Z) (sd : list Z) (i o name name_len token token_len display display_len : Z)
  (ly' : alayout) (S' : astate) (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
  : Prop :=
  W' = W /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
  (if reac_box_name_c.bn_accept f sd i o name name_len token token_len display display_len
   then getr regs' 10 = w64 0 /\
        garr8 SEGS (mrestrict (w_H W') mem') name (bn_NM f sd i o ++ [0]) /\
        garr8 SEGS (mrestrict (w_H W') mem') token (bn_TK (bn_NM f sd i o) ++ [0]) /\
        garr8 SEGS (mrestrict (w_H W') mem') display (bn_DP (bn_NM f sd i o) i o ++ [0]) /\
        (forall a, inFP (rbn_fp name name_len token token_len display display_len) a ->
           ~ (name <= a < name + Z.of_nat (length (bn_NM f sd i o)) + 1) ->
           ~ (token <= a < token + Z.of_nat (length (bn_TK (bn_NM f sd i o))) + 1) ->
           ~ (display <= a < display + Z.of_nat (length (bn_DP (bn_NM f sd i o) i o)) + 1) ->
           aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a)
   else getr regs' 10 = w64 (-1) /\
        (forall a, inFP (rbn_fp name name_len token token_len display display_len) a ->
           (exists q N, In (q, N) (ablocks B ly S) /\ q <= a < q + N) ->
           aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a)).

(* ---------------------------------------------------------------------------------------------------------
   The cut-point states of the walk.
   --------------------------------------------------------------------------------------------------------- *)
(* One call of reac_box_name: the entry state, the arguments, and the class-3 side-stack frame it takes
   (position fpos; it exists from the return of __asan_stack_malloc_3 at 0x82e00 on). *)
Record rbx : Type := mkRbx {
  x_ly : alayout; x_S : astate; x_W : world SEGS; x_regs : bvmap 5 word; x_mem : word -> option byte; x_md : Model;
  x_ch : list (Z * Z * Z);
  x_f : Z; x_said : Z; x_i : Z; x_o : Z; x_name : Z; x_name_len : Z; x_token : Z; x_token_len : Z;
  x_display : Z; x_display_len : Z; x_sd : list Z;
  x_fpos : Z }.
Definition x_sp0 (c : rbx) : Z := spZ (x_regs c).
(* s1: sp after 0x82d74 addi sp,sp,-320 and 0x82db4 andi sp,sp,-32; every call is made with sp = s1. *)
Definition x_s1 (c : rbx) : Z := 32 * ((x_sp0 c - 320) / 32).
Definition x_F (c : rbx) : Z := frame_addr (x_ly c) 3 (x_fpos c).
(* the frame's first shadow byte (s2 from 0x82e74 on) *)
Definition x_FS (c : rbx) : Z := SHADOW_OFF + x_F c / 8.
Definition x_FP (c : rbx) : list (Z * Z) :=
  rbn_fp (x_name c) (x_name_len c) (x_token c) (x_token_len c) (x_display c) (x_display_len c).
Definition x_stem (c : rbx) : list Z := bn_stem (x_f c) (x_sd c).
Definition x_w4 (c : rbx) : list Z := bn_w4 (x_i c) (x_o c).
Definition x_mem_at (c : rbx) (m : word -> option byte) : word -> option byte := mrestrict (w_H (x_W c)) m.
(* c with the frame position fpos (__asan_stack_malloc_3's choice at 0x82dfc). *)
Definition x_setpos (c : rbx) (fpos : Z) : rbx :=
  mkRbx (x_ly c) (x_S c) (x_W c) (x_regs c) (x_mem c) (x_md c) (x_ch c) (x_f c) (x_said c) (x_i c) (x_o c)
    (x_name c) (x_name_len c) (x_token c) (x_token_len c) (x_display c) (x_display_len c) (x_sd c) fpos.
(* The contract's pre-condition (treac_box_name_spec), for c, with the stack the contract asks
   (REAC_BOX_NAME_STK = 336 + 2 * ESTACK). *)
Definition rbn_pre (c : rbx) : Prop :=
  afn_pre SEGS B (336 + 2 * ESTACK) (x_ly c) (x_S c) (x_W c) (x_regs c) (x_mem c) (x_md c) (x_ch c) /\
  arodata_okP SEGS (@pa_relro_lo _ identb_listing PI) (@pa_relro_hi _ identb_listing PI) B
    (aview SEGS (w_H (x_W c)) (x_mem c)) /\
  getr (x_regs c) 10 = w64 (x_f c) /\ - 2 ^ 31 <= x_f c < 2 ^ 31 /\
  getr (x_regs c) 11 = w64 (x_said c) /\ 0 <= x_said c < 2 ^ 64 /\
  getr (x_regs c) 12 = w64 (x_i c) /\ - 2 ^ 31 <= x_i c < 2 ^ 31 /\
  getr (x_regs c) 13 = w64 (x_o c) /\ - 2 ^ 31 <= x_o c < 2 ^ 31 /\
  getr (x_regs c) 14 = w64 (x_name c) /\ 0 <= x_name c < 2 ^ 64 /\
  getr (x_regs c) 15 = w64 (x_name_len c) /\ 0 <= x_name_len c < 2 ^ 64 /\
  getr (x_regs c) 16 = w64 (x_token c) /\ 0 <= x_token c < 2 ^ 64 /\
  getr (x_regs c) 17 = w64 (x_token_len c) /\ 0 <= x_token_len c < 2 ^ 64 /\
  (forall a, x_sp0 c <= a < x_sp0 c + 16 -> apresent (w_H (x_W c)) (x_mem c) a) /\
  val_mem SEGS (x_mem_at c (x_mem c)) (x_sp0 c) 8 (x_display c) /\ 0 <= x_display c < 2 ^ 64 /\
  val_mem SEGS (x_mem_at c (x_mem c)) (x_sp0 c + 8) 8 (x_display_len c) /\ 0 <= x_display_len c < 2 ^ 64 /\
  rbn_img (x_W c) (x_mem c) /\
  (reac_box_name_c.bn_args_ok (x_name c) (x_name_len c) (x_token c) (x_token_len c) (x_display c)
     (x_display_len c) (x_i c) (x_o c) = true ->
   rbn_said (x_ly c) (x_S c) (x_W c) (x_mem c) (x_said c) (x_sd c) /\
   rbn_bufs (x_ly c) (x_S c) (x_name c) (x_name_len c) (x_token c) (x_token_len c) (x_display c) (x_display_len c)) /\
  Z.of_nat (length (frames (x_S c))) <= 7 /\
  st_nev (x_S c) <= EV_MAX /\ blocks_bytes (x_S c) <= LIVE_MAX.
(* The caller's ra and s0..s11, saved at sp0 - 8 .. sp0 - 104 (0x82d7c .. 0x82dac). *)
Definition rbn_saved_regs : list (Z * bv 5) :=
  [(8, 1%bv); (16, 8%bv); (24, 9%bv); (32, 18%bv); (40, 19%bv); (48, 20%bv); (56, 21%bv); (64, 22%bv);
   (72, 23%bv); (80, 24%bv); (88, 25%bv); (96, 26%bv); (104, 27%bv)].
Definition rbn_saved (c : rbx) (m : word -> option byte) : Prop :=
  Forall (fun p => val_mem SEGS (x_mem_at c m) (x_sp0 c - fst p) 8 (bv_unsigned (getr (x_regs c) (snd p))))
    rbn_saved_regs.
(* The state every cut point shares from the frame allocation on (also the frame release R): the caller's
   journal with the class-3 frame (3, fpos) owned, sp / gp / tp / s0 / s1, s2 = the frame's shadow, s3 = s7 =
   the frame, the saved registers, the frame's flag pointer (__asan_stack_malloc_3's post, read at 0x834c8),
   and the three buffers still as at entry (nothing writes them before the copies at 0x8344c .. 0x8346c). *)
Definition rbn_core (c : rbx) (lyc : alayout) (Sc : astate) (memc : word -> option byte) (mdc : Model)
  (regs : bvmap 5 word) : Prop :=
  rbn_pre c /\
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) memc mdc 0 /\
  Permutation (ablocks B lyc Sc) (ablocks B (x_ly c) (x_S c)) /\
  getr regs 2 = w64 (x_s1 c) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 8 = w64 (x_sp0 c) /\ getr regs 9 = w64 (x_s1 c) /\ getr regs 18 = w64 (x_FS c) /\
  getr regs 19 = w64 (x_F c) /\ getr regs 23 = w64 (x_F c) /\
  rbn_saved c memc /\
  rdword (aview SEGS (w_H (x_W c)) memc) (x_F c + 504) = Some (flag_addr (x_ly c) 3 (x_fpos c)).
(* The buffers as at entry, where they lie in heap blocks of the entry state (when the arguments are refused
   nothing places the three ranges; they may overlap the stack window the prologue writes). *)
Definition rbn_bufkept (c : rbx) (m : word -> option byte) : Prop :=
  forall a, inFP (x_FP c) a -> (exists q N, In (q, N) (ablocks B (x_ly c) (x_S c)) /\ q <= a < q + N) ->
    aview SEGS (w_H (x_W c)) m a = aview SEGS (w_H (x_W c)) (x_mem c) a.
(* The window slots stored before C1: display (0x82fc8), name, token, token_len, display_len, in_ch / out_ch
   (0x82f68, the full registers), name_len (0x82dc4) and the frame (0x82e3c). *)
Definition rbn_slots (c : rbx) (m : word -> option byte) : Prop :=
  let s1 := x_s1 c in let mm := x_mem_at c m in
  val_mem SEGS mm s1 8 (x_display c) /\ val_mem SEGS mm (s1 + 8) 8 (x_name c) /\
  val_mem SEGS mm (s1 + 16) 8 (x_token c) /\ val_mem SEGS mm (s1 + 24) 8 (x_token_len c) /\
  val_mem SEGS mm (s1 + 32) 8 (x_display_len c) /\ val_mem SEGS mm (s1 + 40) 8 (x_i c mod 2 ^ 64) /\
  val_mem SEGS mm (s1 + 48) 8 (x_o c mod 2 ^ 64) /\ val_mem SEGS mm (s1 + 56) 8 (x_name_len c) /\
  val_mem SEGS mm (s1 + 80) 8 (x_F c).
(* The four scope shadow bytes of the frame: w4 (FS + 4; 0xf8 closed, 5 open), nm (FS + 8 .. 10), tk
   (FS + 16 .. 18), dp (FS + 24 .. 29) (0xf8 closed, 0 open). *)
Definition rbn_scope (c : rbx) (m : word -> option byte) (w nm tk dp : Z) : Prop :=
  let rd := aview SEGS (w_H (x_W c)) m in let FS := x_FS c in
  rd (FS + 4) = Some w /\
  (forall j, 8 <= j < 11 -> rd (FS + j) = Some nm) /\
  (forall j, 16 <= j < 19 -> rd (FS + j) = Some tk) /\
  (forall j, 24 <= j < 30 -> rd (FS + j) = Some dp).
(* A struct sb at b (in the window: p, cap, n at b, b + 8, b + 16, over at b + 24) whose buffer q holds cs. *)
Definition rbn_sb (c : rbx) (m : word -> option byte) (b q cap : Z) (cs : list Z) (ov : Z) : Prop :=
  let mm := x_mem_at c m in
  val_mem SEGS mm b 8 q /\ val_mem SEGS mm (b + 8) 8 cap /\ val_mem SEGS mm (b + 16) 8 (Z.of_nat (length cs)) /\
  val_mem SEGS mm (b + 24) 4 ov /\ (ov = 0 \/ ov = 1) /\ Z.of_nat (length cs) <= cap - 1 /\
  Forall (fun x => 0 <= x < 256) cs /\ garr8 SEGS mm q cs.
(* The stem the call copies (s9 from 0x82fc8 on): said when it is non-NULL and non-empty (a string in a frame of
   the caller), else the table entry for f in 1 .. 3, else "REAC" (image strings). *)
Definition rbn_stem (c : rbx) (m : word -> option byte) (st : Z) : Prop :=
  (x_sd c <> [] /\ st = x_said c /\ rbn_cstr (x_W c) m st (x_sd c) /\
   exists cid pos, In (cid, pos) (frames (x_S c)) /\
     frame_addr (x_ly c) cid pos <= st /\
     st + Z.of_nat (length (x_sd c)) + 8 <= frame_addr (x_ly c) cid pos + fs_frame_bytes cid) \/
  (x_sd c = [] /\ rbn_imgstr (x_W c) m st (x_stem c)).
(* The common part of C1 .. C10: rbn_core, the arguments accepted (0x82f10 .. 0x82f64), the buffers as at
   entry, the window slots, s6 = the shadow base. *)
Definition rbn_live (c : rbx) (lyc : alayout) (Sc : astate) (memc : word -> option byte) (mdc : Model)
  (regs : bvmap 5 word) : Prop :=
  rbn_core c lyc Sc memc mdc regs /\
  reac_box_name_c.bn_args_ok (x_name c) (x_name_len c) (x_token c) (x_token_len c) (x_display c)
    (x_display_len c) (x_i c) (x_o c) = true /\
  rbn_bufkept c memc /\ rbn_slots c memc /\ getr regs 22 = w64 SHADOW_OFF.
(* The struct offsets in the window and the arrays in the frame. *)
Definition x_wb (c : rbx) : Z := x_s1 c + 184.
Definition x_nb (c : rbx) : Z := x_s1 c + 152.
Definition x_tb (c : rbx) : Z := x_s1 c + 120.
Definition x_db (c : rbx) : Z := x_s1 c + 88.
Definition x_W4 (c : rbx) : Z := x_F c + 32.
Definition x_NM (c : rbx) : Z := x_F c + 64.
Definition x_TK (c : rbx) : Z := x_F c + 128.
Definition x_DP (c : rbx) : Z := x_F c + 192.
(* The models of the buffers (lib/B/Prog/reac_box_name_sbm.v). *)
Definition x_nb_stem (c : rbx) : list Z * Z := sbm_str 24 ([], 0) (x_stem c).
Definition x_nb_dash (c : rbx) : list Z * Z := sbm_ch 24 (x_nb_stem c) 45.
Definition x_nb_full (c : rbx) : list Z * Z := rbn_nm (x_f c) (x_sd c) (x_i c) (x_o c).
Definition x_nmc (c : rbx) : list Z := fst (x_nb_full c).

(* C1, 0x83000: back from memset(s1 + 200, 0, 16) (wb.n and wb.over zeroed); w4's scope open (0x82fe4). *)
Definition rbn_C1 (c : rbx) (st : Z) (lyc : alayout) (Sc : astate) (memc : word -> option byte) (mdc : Model)
  (regs : bvmap 5 word) : Prop :=
  rbn_live c lyc Sc memc mdc regs /\ rbn_stem c memc st /\
  getr regs 20 = w64 (x_W4 c) /\ getr regs 21 = w64 5 /\ getr regs 24 = w64 (x_name c) /\
  getr regs 25 = w64 st /\ getr regs 26 = w64 (x_token_len c) /\
  rbn_scope c memc 5 0xf8 0xf8 0xf8 /\
  rbn_sb c memc (x_wb c) (x_W4 c) 5 [] 0.
(* The state C2 .. C10 share: wb holds w4 (two sb_dec calls, 0x8300c / 0x8301c) with its NUL (0x83038); nm's
   scope open (0x83040); s11 = nm. *)
Definition rbn_w4done (c : rbx) (memc : word -> option byte) (regs : bvmap 5 word) : Prop :=
  rbn_sb c memc (x_wb c) (x_W4 c) 5 (x_w4 c) 0 /\
  garr8 SEGS (x_mem_at c memc) (x_W4 c) (x_w4 c ++ [0]) /\
  getr regs 27 = w64 (x_NM c).
(* C2, 0x83088, head of the stem copy loop: a0 = the i-th character, s5 = stem + i, s10 = stem + i + 1,
   s8 = -1; nb holds the first i characters (sb_ch at 0x83090). *)
Definition rbn_C2 (c : rbx) (st i : Z) (lyc : alayout) (Sc : astate) (memc : word -> option byte) (mdc : Model)
  (regs : bvmap 5 word) : Prop :=
  rbn_live c lyc Sc memc mdc regs /\ rbn_stem c memc st /\ rbn_w4done c memc regs /\
  0 <= i < Z.of_nat (length (x_stem c)) /\
  getr regs 10 = w64 (nth (Z.to_nat i) (x_stem c) 0) /\ getr regs 21 = w64 (st + i) /\
  getr regs 26 = w64 (st + i + 1) /\ getr regs 24 = w64 (2 ^ 64 - 1) /\
  getr regs 20 = w64 (x_W4 c) /\ getr regs 25 = w64 st /\
  rbn_scope c memc 5 0 0xf8 0xf8 /\
  rbn_sb c memc (x_nb c) (x_NM c) 24 (fst (sbm_str 24 ([], 0) (firstn (Z.to_nat i) (x_stem c))))
    (snd (sbm_str 24 ([], 0) (firstn (Z.to_nat i) (x_stem c)))).
(* C3, 0x830cc: the stem copied (the loop's exit at 0x830b4). *)
Definition rbn_C3 (c : rbx) (st : Z) (lyc : alayout) (Sc : astate) (memc : word -> option byte) (mdc : Model)
  (regs : bvmap 5 word) : Prop :=
  rbn_live c lyc Sc memc mdc regs /\ rbn_stem c memc st /\ rbn_w4done c memc regs /\
  getr regs 20 = w64 (x_W4 c) /\ getr regs 25 = w64 st /\
  rbn_scope c memc 5 0 0xf8 0xf8 /\
  rbn_sb c memc (x_nb c) (x_NM c) 24 (fst (x_nb_stem c)) (snd (x_nb_stem c)).
(* C4, 0x83128, head of the w4 copy loop (after sb_ch(nb, '-') at 0x83114): a0 = w4's j-th character,
   s4 = w4 + j, s5 = w4 + j + 1, s8 = -1; the strlen / bcmp test at 0x830d0 .. 0x83108 said "append", so the
   name is the stem, '-' and w4 (x_nb_full). *)
Definition rbn_C4 (c : rbx) (j : Z) (lyc : alayout) (Sc : astate) (memc : word -> option byte) (mdc : Model)
  (regs : bvmap 5 word) : Prop :=
  rbn_live c lyc Sc memc mdc regs /\ rbn_w4done c memc regs /\
  0 <= j < 4 /\ x_nb_full c = sbm_str 24 (x_nb_dash c) (x_w4 c) /\
  getr regs 10 = w64 (nth (Z.to_nat j) (x_w4 c) 0) /\ getr regs 20 = w64 (x_W4 c + j) /\
  getr regs 21 = w64 (x_W4 c + j + 1) /\ getr regs 24 = w64 (2 ^ 64 - 1) /\
  rbn_scope c memc 5 0 0xf8 0xf8 /\
  rbn_sb c memc (x_nb c) (x_NM c) 24 (fst (sbm_str 24 (x_nb_dash c) (firstn (Z.to_nat j) (x_w4 c))))
    (snd (sbm_str 24 (x_nb_dash c) (firstn (Z.to_nat j) (x_w4 c)))).
(* C5, 0x8316c: nb holds the name (rbn_nm: bn_NM when it fits, reac_box_name_sbm.v). *)
Definition rbn_C5 (c : rbx) (lyc : alayout) (Sc : astate) (memc : word -> option byte) (mdc : Model)
  (regs : bvmap 5 word) : Prop :=
  rbn_live c lyc Sc memc mdc regs /\ rbn_w4done c memc regs /\
  rbn_scope c memc 5 0 0xf8 0xf8 /\
  rbn_sb c memc (x_nb c) (x_NM c) 24 (x_nmc c) (snd (x_nb_full c)).
(* The state C6 .. C10 share: nm's NUL (0x8318c), tk's scope open (0x83190), s9 = tk. *)
Definition rbn_nmdone (c : rbx) (memc : word -> option byte) (regs : bvmap 5 word) : Prop :=
  rbn_sb c memc (x_nb c) (x_NM c) 24 (x_nmc c) (snd (x_nb_full c)) /\
  garr8 SEGS (x_mem_at c memc) (x_NM c) (x_nmc c ++ [0]) /\
  getr regs 25 = w64 (x_TK c).
(* C6, 0x831c8, head of the token loop: s5 = i, s10 = seen (a '-' skipped), s8 = 45, s4 = 24; tb holds the
   token of the first i characters (rbn_tok, reac_box_name_sbm.v). *)
Definition rbn_C6 (c : rbx) (i : Z) (lyc : alayout) (Sc : astate) (memc : word -> option byte) (mdc : Model)
  (regs : bvmap 5 word) : Prop :=
  rbn_live c lyc Sc memc mdc regs /\ rbn_w4done c memc regs /\ rbn_nmdone c memc regs /\
  0 <= i < Z.of_nat (length (x_nmc c)) /\
  getr regs 21 = w64 i /\
  getr regs 26 = w64 (if existsb (fun x => x =? 45) (firstn (Z.to_nat i) (x_nmc c)) then 1 else 0) /\
  getr regs 24 = w64 45 /\ getr regs 20 = w64 24 /\
  rbn_scope c memc 5 0 0 0xf8 /\
  rbn_sb c memc (x_tb c) (x_TK c) 24 (fst (rbn_tok (firstn (Z.to_nat i) (x_nmc c))))
    (snd (rbn_tok (firstn (Z.to_nat i) (x_nmc c)))).
(* C7, 0x83230: tb holds the token. *)
Definition rbn_C7 (c : rbx) (lyc : alayout) (Sc : astate) (memc : word -> option byte) (mdc : Model)
  (regs : bvmap 5 word) : Prop :=
  rbn_live c lyc Sc memc mdc regs /\ rbn_w4done c memc regs /\ rbn_nmdone c memc regs /\
  rbn_scope c memc 5 0 0 0xf8 /\
  rbn_sb c memc (x_tb c) (x_TK c) 24 (fst (rbn_tok (x_nmc c))) (snd (rbn_tok (x_nmc c))).
(* The state C8 .. C10 share: tk's NUL (0x8324c), dp's scope open (0x83254), s10 = dp. *)
Definition rbn_tkdone (c : rbx) (memc : word -> option byte) (regs : bvmap 5 word) : Prop :=
  rbn_sb c memc (x_tb c) (x_TK c) 24 (fst (rbn_tok (x_nmc c))) (snd (rbn_tok (x_nmc c))) /\
  garr8 SEGS (x_mem_at c memc) (x_TK c) (fst (rbn_tok (x_nmc c)) ++ [0]) /\
  getr regs 26 = w64 (x_DP c).
(* C8, 0x83298, head of the name copy into the display: a0 = nm's i-th character, s8 = nm + i,
   s4 = nm + i + 1, s5 = -1. *)
Definition rbn_C8 (c : rbx) (i : Z) (lyc : alayout) (Sc : astate) (memc : word -> option byte) (mdc : Model)
  (regs : bvmap 5 word) : Prop :=
  rbn_live c lyc Sc memc mdc regs /\ rbn_w4done c memc regs /\ rbn_nmdone c memc regs /\
  rbn_tkdone c memc regs /\
  0 <= i < Z.of_nat (length (x_nmc c)) /\
  getr regs 10 = w64 (nth (Z.to_nat i) (x_nmc c) 0) /\ getr regs 24 = w64 (x_NM c + i) /\
  getr regs 20 = w64 (x_NM c + i + 1) /\ getr regs 21 = w64 (2 ^ 64 - 1) /\
  rbn_scope c memc 5 0 0 0 /\
  rbn_sb c memc (x_db c) (x_DP c) 48 (fst (sbm_str 48 ([], 0) (firstn (Z.to_nat i) (x_nmc c))))
    (snd (sbm_str 48 ([], 0) (firstn (Z.to_nat i) (x_nmc c)))).
(* C9, 0x832dc: the name copied into the display. *)
Definition rbn_C9 (c : rbx) (lyc : alayout) (Sc : astate) (memc : word -> option byte) (mdc : Model)
  (regs : bvmap 5 word) : Prop :=
  rbn_live c lyc Sc memc mdc regs /\ rbn_w4done c memc regs /\ rbn_nmdone c memc regs /\
  rbn_tkdone c memc regs /\
  rbn_scope c memc 5 0 0 0 /\
  rbn_sb c memc (x_db c) (x_DP c) 48 (fst (sbm_str 48 ([], 0) (x_nmc c))) (snd (sbm_str 48 ([], 0) (x_nmc c))).
(* C10, 0x833e0: db holds the display (rbn_dp, reac_box_name_sbm.v). *)
Definition rbn_C10 (c : rbx) (lyc : alayout) (Sc : astate) (memc : word -> option byte) (mdc : Model)
  (regs : bvmap 5 word) : Prop :=
  rbn_live c lyc Sc memc mdc regs /\ rbn_w4done c memc regs /\ rbn_nmdone c memc regs /\
  rbn_tkdone c memc regs /\
  rbn_scope c memc 5 0 0 0 /\
  rbn_sb c memc (x_db c) (x_DP c) 48 (fst (rbn_dp (x_nmc c) (x_i c) (x_o c)))
    (snd (rbn_dp (x_nmc c) (x_i c) (x_o c))).
(* R, 0x834ac, the frame release: s4 = the result; the buffers as the post asks (refusal: as at entry;
   acceptance: the three strings, the rest as at entry). *)
Definition rbn_R (c : rbx) (lyc : alayout) (Sc : astate) (memc : word -> option byte) (mdc : Model)
  (regs : bvmap 5 word) : Prop :=
  rbn_core c lyc Sc memc mdc regs /\
  let acc := reac_box_name_c.bn_accept (x_f c) (x_sd c) (x_i c) (x_o c) (x_name c) (x_name_len c) (x_token c)
               (x_token_len c) (x_display c) (x_display_len c) in
  getr regs 20 = w64 (if acc then 0 else -1) /\
  (if acc
   then garr8 SEGS (x_mem_at c memc) (x_name c) (bn_NM (x_f c) (x_sd c) (x_i c) (x_o c) ++ [0]) /\
        garr8 SEGS (x_mem_at c memc) (x_token c) (bn_TK (bn_NM (x_f c) (x_sd c) (x_i c) (x_o c)) ++ [0]) /\
        garr8 SEGS (x_mem_at c memc) (x_display c)
          (bn_DP (bn_NM (x_f c) (x_sd c) (x_i c) (x_o c)) (x_i c) (x_o c) ++ [0]) /\
        (forall a, inFP (x_FP c) a ->
           ~ (x_name c <= a < x_name c + Z.of_nat (length (bn_NM (x_f c) (x_sd c) (x_i c) (x_o c))) + 1) ->
           ~ (x_token c <= a <
              x_token c + Z.of_nat (length (bn_TK (bn_NM (x_f c) (x_sd c) (x_i c) (x_o c)))) + 1) ->
           ~ (x_display c <= a <
              x_display c + Z.of_nat (length (bn_DP (bn_NM (x_f c) (x_sd c) (x_i c) (x_o c)) (x_i c) (x_o c))) + 1) ->
           aview SEGS (w_H (x_W c)) memc a = aview SEGS (w_H (x_W c)) (x_mem c) a)
   else rbn_bufkept c memc).
End h.
End f.
End d.
