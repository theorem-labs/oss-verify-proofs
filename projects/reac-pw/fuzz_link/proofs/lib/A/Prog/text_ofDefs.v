(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PcapSourceClose.v: pcap_source_close (fuzz_pcap.asan-ubsan
   0x81d4c, listing offset AF_pcap_source_close = 0x15c4, 31 instructions) on libreac v1.9.0's ASan+UBSan build, walked
   against lib/A's contract.

   The code is lib/A's ASan code (fuzz_pcap.asan 0x81e90, 27 instructions) with two UBSan guards and a register swap
   (measured: pcap-ubsan-inventory.md (sha256 5b607b62e337; internal record), row G6 and the pcap_source_close row of (c)). After
   the 32-byte frame and the saves of ra, s0 and s1, 0x81d5c `beqz a0` branches to the `unimp` at 0x81db4 when ps is
   null, 0x81d60 `mv s0,a0` (above the GOT load here), and 0x81d64 `andi a0,a0,7` / 0x81d68 `bnez a0` branch to the same
   `unimp` when ps is not 8-aligned. The shadow base is then loaded through the GOT word 0x996f8 (object 1; through a0,
   where the ASan code uses a1) from the cell 0xa17b8 (object 15). The rest is the ASan code at other pcs: the shadow
   check of ps's 8 bytes (0x81d80 `lbu`, 0x81d84 `bnez` to the error path at 0x81db8), f = ps->f (0x81d88), the test of
   f (0x81d8c `beqz` to 0x81da0), the call of the fclose wrapper's 4-byte jump (0x81d90 `jal
   __interceptor_trampoline_fclose`, 0x4161c), the second shadow check (0x81d94, 0x81d98 `bnez` to the error path at
   0x81dc0), ps->f = NULL (0x81d9c `sd zero,0(s0)`), the restores and the return (0x81db0).

   THE GUARDS. The walk's first symbolic run decides both, from the facts on a0 = ps that cl_entry proves (atom 10: ps
   >= 4096 and ps mod 2^3 = 0; ps >= 4096 because ps lies in a frame of the caller (frames_bounds), which gives the
   statement's ps <> 0; the alignment is the statement's ps mod 8 = 0):
     0x81d5c: decide_cond2 (Reusable/YP0e.v:932) through decide_eq (Reusable/YP0m.v:658-672), whose SOff / SLit arm
              (:665-666) tests ranges_disjoint (:653): ps's range [4096, ...] is disjoint from 0, so the branch is not
              taken;
     0x81d68: s_and_ptr (Reusable/YP0m.v:969-980) rewrites ps & 7 to 0 from the alignment fact, so `bnez` sees 0 and is
              not taken.
   These are the decisions of the released UBSan proof for the v1.8 image (proofs/libreac/fuzz_pcap/lib/U/Prog/
   pcap_source_close.v on origin/ossv/recipes c8557374ad2e): close_closed :43 (if_false, premise bv_unsigned a0 <> 0 at
   :23) and :45-46 (ub_align A8, premise bv_unsigned a0 mod 8 = 0 at :23), close_pro :82 and :84-85 (premises :58).

   The contract is lib/A's, not a copy (the shared-text rule): pb_pcap_source_closeX proves lib/A's image-generic
   AC.tpcap_source_close_specX (with AC.tpcap_source_close_post and AC.tclose_kept) at this image's segments SEGS and
   relro window pa_relro_lo / pa_relro_hi of the lib/B PAImg instance (on the pin PcapRelro.PCAP_RLO /
   PcapRelro.PCAP_RHI, lib/B/Prog/PcapRelro.v), at a = BASE + AF_pcap_source_close of the lib/B listing. The image-free constants
   (TPCAP_SOURCE_CLOSE_STK, EV_CLOSE, tclose_fblk) and lemmas are lib/A's too, through AC. The fclose wrapper's contract
   is the Section hypothesis AFCLOSE, of lib/A/Stdio/PFclose.v's image-generic afclose_source_spec type at this image.
   There is no lib/B/Stdio/PFclose.v (that statement takes the image as parameters). AFCLOSE is discharged by the
   asan-ubsan instance of a Theorem Labs lane's fclose walk lib/A/Stdio/WFclose.v, whose lib/B walk twin is
   lib/B/Stdio/WFclose.v (lib/B/Stdio/PFcloseInstB.v's inst_AFCLOSE_U composes it with lib/B/Stdio/WFcloseI.v).
   getr / mkst / seg_rom come from YK11; nothing from lib/Lib is imported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceClose.v, with its module names changed; 3497 of its 3557 lines of code are new or changed and 570 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessTail.v, with its module paths and module names changed; 346 of its 396 lines of code are new or changed and 3507 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_served_markDec.v; 83 of its 114 lines of code are new or changed and 365 lines of the source are left out. *)
(* text_of (fuzz_link.asan 0x87dc0, listing offset AF_text_of = 0x5bf4, 832 bytes) on image A: the cuts between the
   files of its walk against lib/A/Prog/text_of_c.v `text_of_acontract` (aleaf_alloc_rd over the caller's journal),
   in the style of lib/A/Prog/model_writeDefs.v.

   The code's shape (listing (internal path) (internal record, sha256 1c4fdcbb52aa); p = a0 the
   cursor, o = a1 = s0 the *own slot, s4 the shadow base):
     +0x00..+0x48  the 64-byte frame (ra, s0..s5 at sp0' - 8 .. sp0' - 56), s4 := the shadow base, the check of
                   p + 8, s0 := o, a1 := c1 (the count left)
     +0x4c         `beqz a1`: c1 = 0 -> +0x12c: the check of o, *own := 0, a1 := 0, then THE TABLE CUT
     +0x50..+0xa4  c1 > 0: the cursor advances by one byte (stores at p + 8 and p), b0 := the input's first byte (lb,
                   signed), *own := 0; `bgez b0` -> THE TABLE CUT with a1 = b0
     +0xa8..+0x12c b0 < 0: up to two more bytes b1, b2 (when the count allows), the cursor advanced by them
     +0x1a8..+0x298 v := b1 | b2 << 8, n := min (v mod 320, the count left), the cursor advanced by n,
                   wrapper_memchr (when n > 0), wrapper_malloc (k := the length to the first NUL, plus 1),
                   checked_memcpy (when k > 1), the NUL store, *own := the block
     +0x144..+0x19c THE TABLE ARM: i := (a1 & 0xff) mod 11, s3 := texts[i] (the check of texts + 8 i)
     +0x270..+0x294 a0 := s3, the restores, `ret`
   This file states the call's context, the contract at the context, and the TABLE CUT (+0x144) with its obligation
   `to_table_obl`: from every state the cut describes, the run reaches the contract's Post. The cut is reached
   before the malloc, so the world, the layout and the allocator state are the call's.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem text_of_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition TO_FRAME : Z := 64.                           (* addi sp,sp,-0x40  +0x00 *)
Definition TO_CUT_TABLE : Z := AF_text_of + 0x144.       (* andi a0,a1,0xff *)
Lemma TO_CUT_TABLE_pin : 0x821cc + TO_CUT_TABLE = 0x87f04. Proof. reflexivity. Qed.
(* the registers the prologue saves, in the order of their slots sp0 - 8, sp0 - 16, ... sp0 - 56 *)
Definition TO_SAVED : list Z := [1; 8; 9; 18; 19; 20; 21].
(* the registers text_of never writes *)
Definition TO_UNTOUCHED : list Z := [3; 4; 22; 23; 24; 25; 26; 27].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable CTX : list (list Z).

(* ---- the call's context: the variables of the contract, at one call ---- *)
Record tocx := mkTOCX {
  to_rlo : Z; to_rhi : Z;
  to_G : list (Z * Z); to_XO : Z; to_OUT : list (Z * Z);
  to_STK : Z; to_sp0 : Z; to_FP : list (Z * Z);
  to_ly : alayout; to_S : astate; to_W0 : world SEGS; to_mem0 : word -> option byte; to_md0 : Model;
  to_own : list (Z * Z);
  to_lyc : alayout; to_Sc : astate; to_W : world SEGS; to_memc : word -> option byte; to_mdc : Model;
  to_k : Z; to_regs : bvmap 5 word; to_ch : list (Z * Z * Z) }.

Definition to_m0 (cx : tocx) : word -> option byte := rdW (to_W cx) (to_memc cx).
Definition to_wr (cx : tocx) : list (Z * Z) := text_of_awr (to_regs cx) (to_m0 cx).
Definition to_E (cx : tocx) : Z -> Prop := fun a => inFP (to_wr cx) a.
Definition to_sp (cx : tocx) : Z := spZ (to_regs cx).
Definition to_p (cx : tocx) : Z := aarg (to_regs cx) 0.
Definition to_o (cx : tocx) : Z := aarg (to_regs cx) 1.

(* ---- the contract at the context ---- *)
Definition to_pre (cx : tocx) : Prop :=
  apre SK SEGS (to_rlo cx) (to_rhi cx) B TEXT_OF_AK 1 [] (to_wr cx)
    (to_G cx) (to_XO cx) (to_OUT cx) (to_STK cx) (to_sp0 cx) (to_FP cx)
    (to_ly cx) (to_S cx) (to_W0 cx) (to_mem0 cx) (to_md0 cx) (to_own cx)
    (to_lyc cx) (to_Sc cx) (to_W cx) (to_memc cx) (to_mdc cx) (to_k cx) (to_regs cx) /\
  (forall a, text_of_ard SEGS (to_regs cx) (to_m0 cx) a ->
     akb SEGS B (to_lyc cx) (to_Sc cx) (to_sp cx - TEXT_OF_AK) (to_sp cx) a) /\
  blocks_bytes (to_Sc cx) + TEXT_OF_LIVE <= LIVE_MAX /\
  mo_ok MT (to_Sc cx) (mo_malloc MT TEXT_OF_LIVE) /\
  achain (to_lyc cx) (aview SEGS (w_H (to_W cx)) (to_memc cx)) (to_sp cx) (s0Z (to_regs cx)) (to_ch cx) /\
  In (raZ (to_regs cx) :: spine (to_ch cx)) CTX /\
  text_of_ledpre B (to_Sc cx) /\
  text_of_apre SEGS (to_rlo cx) (to_rhi cx) B (to_regs cx) (to_m0 cx).

Definition to_post (cx : tocx) : world SEGS -> config -> Prop :=
  apost SK SEGS B TEXT_OF_AK 1 (to_E cx)
    (to_G cx) (to_XO cx) (to_OUT cx) (to_STK cx) (to_sp0 cx) (to_FP cx)
    (to_ly cx) (to_S cx) (to_W0 cx) (to_mem0 cx) (to_md0 cx) (to_own cx)
    (to_lyc cx) (to_Sc cx) (to_W cx) (to_memc cx) (to_mdc cx) (to_k cx) (to_regs cx)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       mo_le MT (to_Sc cx) S2 (mo_malloc MT TEXT_OF_LIVE) /\ text_of_ledpost B (to_Sc cx) S2 /\
       text_of_apostA SEGS (to_rlo cx) (to_rhi cx) B (to_regs cx) (to_m0 cx) regs2 (rdW W2 mem2)
         (ablocks B (to_lyc cx) (to_Sc cx)) (ablocks B ly2 S2)).

(* `to_from GI`: from every state GI describes (before the malloc: the call's world), the run reaches the Post *)
Definition to_from (GI : tocx -> machine_state -> Model -> Prop) : Prop :=
  forall (cx : tocx) (ms3 : machine_state) md3,
  to_pre cx -> GI cx ms3 md3 -> SRr SEGS (to_W cx) (mkCfg ms3 md3) (to_post cx).

(* ---- THE TABLE CUT (+0x144 `andi a0,a1,0xff`) ----
   Reached from +0x12c (count 0: the cursor as at the call, adv = 0) and from +0xa4 (b0 >= 0: adv = 1); in both
   *own is 0. a1 holds the selector (any word: the arm masks it). Everything the arm, the epilogue and the Post
   need is stated at the cut's memory m3 = rdW (to_W cx) (ms_mem ms3). *)
Definition to_gi_table (cx : tocx) (ms3 : machine_state) (md3 : Model) : Prop :=
  let regs := to_regs cx in
  let R := ms_regs ms3 in
  let m3 := rdW (to_W cx) (ms_mem ms3) in
  let rd3 := aview SEGS (w_H (to_W cx)) (ms_mem ms3) in
  let sp := to_sp cx in
  ms_pc_val ms3 = w64 (BASE + TO_CUT_TABLE) /\
  ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\ ms_rom ms3 = seg_rom SEGS /\
  ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  (* the caller's journal, at the call's layout and state *)
  ajournal_gx SEGS B (to_G cx) (to_XO cx) (to_OUT cx) (to_STK cx) (to_sp0 cx) (to_FP cx)
    (to_ly cx) (to_S cx) (to_W0 cx) (to_mem0 cx) (to_md0 cx) (to_own cx)
    (to_lyc cx) (to_Sc cx) (to_W cx) (ms_mem ms3) md3 (to_k cx) /\
  m_fds md3 = m_fds (to_mdc cx) /\ m_fs md3 = m_fs (to_mdc cx) /\
  (* the registers *)
  getr R 2 = w64 (sp - TO_FRAME) /\ getr R 8 = w64 (to_o cx) /\ getr R 20 = w64 SHADOW_OFF /\
  (* the selector: b0 >= 0 after +0x9c lb / +0xa4 bgez, or 0 after +0x13c *)
  (exists b, getr R 11 = w64 b /\ 0 <= b < 128) /\
  (forall r, In r TO_UNTOUCHED -> getr R (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
  (* the seven saves, at sp - 8 - 8 j *)
  (forall j, (j < 7)%nat ->
     rdword rd3 (sp - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr regs (Z_to_bv 5 (nth j TO_SAVED 0))))) /\
  (* what the stretch so far changed: the window and the write set *)
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - TEXT_OF_AK <= a < sp) -> ~ to_E cx a ->
     rd3 a = aview SEGS (w_H (to_W cx)) (to_memc cx) a) /\
  (forall a, apresent (w_H (to_W cx)) (to_memc cx) a -> apresent (w_H (to_W cx)) (ms_mem ms3) a) /\
  (forall a, sp - TEXT_OF_AK <= a < sp -> apresent (w_H (to_W cx)) (ms_mem ms3) a) /\
  (* the cursor and *own *)
  (forall c0 c1, au64_at SEGS (to_m0 cx) (to_p cx) c0 -> au64_at SEGS (to_m0 cx) (to_p cx + 8) c1 ->
     0 <= c0 < 2 ^ 64 -> 0 <= c1 < 2 ^ 64 ->
     exists adv, 0 <= adv <= c1 /\ au64_at SEGS m3 (to_p cx) (c0 + adv) /\ au64_at SEGS m3 (to_p cx + 8) (c1 - adv)) /\
  abuf SEGS m3 (to_p cx) 16 /\
  au64_at SEGS m3 (to_o cx) 0 /\ abuf SEGS m3 (to_o cx) 8 /\
  (* the table: its words at the call and at the cut, its strings at the cut *)
  range_addressable rd3 SHADOW_OFF LA_TEXTS (8 * TEXTS_N) /\
  (forall i, 0 <= i < TEXTS_N -> exists q s,
     au64_at SEGS (to_m0 cx) (LA_TEXTS + 8 * i) q /\ au64_at SEGS m3 (LA_TEXTS + 8 * i) q /\ 0 < q < 2 ^ 64 /\
     acstr_at SEGS m3 q s /\ Z.of_nat (length s) < 320 /\
     text_of_ro SEGS (to_rlo cx) (to_rhi cx) B q (Z.of_nat (length s) + 1)).

Definition to_table_obl : Prop := to_from to_gi_table.

End b.
End a.
