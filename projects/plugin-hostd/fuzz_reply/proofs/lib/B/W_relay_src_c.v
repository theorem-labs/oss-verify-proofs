(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the contracts of fuzz_reply.asan-ubsan's relay_source (0x85d28, 43 instructions)
   and relay_reads (0x864e8, 37 instructions), which image B calls where image A inlines them: LLVMFuzzerTestOneInput's
   drain arm calls relay_source (0x848c0), its remove and gone arms call relay_reads (0x84830, 0x84b0c), and relay_reads
   calls relay_source (0x86520).  Hand-written (no lib/A twin exists for mkbkit to generate), in the form of W6's
   lib/B/W_wake_c.v (a working branch 1b9965084f9).  The texts of rs_spec and rd_spec are W8Entry-2's
   interface, lib/B/W_LLVMFuzzerTestOneInput_cut.v `Hypothesis RSRC` (a working branch a987841a18c :683,
   the same text at 7d4f6d8955b) and `Hypothesis RRDS` (61da015af91 :707), each with the entry pc as an argument;
   rs_spec_rsrc and rd_spec_rrds below check that rs_spec at fr_B0 + AF_fr_relay_source and rd_spec at
   fr_B0 + AF_fr_relay_reads ARE those texts.  The walks are GENERIC (route (b), step 3, a Theorem Labs lane's
   CONVERSION.md (sha256 1015972e02a9; internal record)): pb_relay_source_x and pb_relay_reads_x prove rs_spec_x / rd_spec_x, the same contracts
   over any allocator relation ARx with its laws (the ghost list Hp after S, the generic journal's placement PST), at
   BASE + AF_fr_relay_source / BASE + AF_fr_relay_reads over lib/B/W_listing.v.  At fr_B0 + AF they are cut_x's RSRC_x /
   RRDS_x (lib/B/W_LLVMFuzzerTestOneInput_cut_x.v :348 / :360, a working branch e43cf0c7bef).
   pb_relay_source and pb_relay_reads keep their statements and Section hypotheses: they are the generic walks at
   ARx := W_journal_x.ARi0 (AR with the head set empty), PST := [] (Section cAR).  pb_relay_source_fr and
   pb_relay_reads_fr are them at B's pin (PB_fr, fr_globals_b), with the instance's laws and its two shadow cells as the
   only premises; pb_relay_source_x_fr and pb_relay_reads_x_fr are the generic walks there.

   relay_source (fd) is fuzz_reply.c's `for (i = 0; i < g_nsrc; i++) if (g_src[i].fd == fd) return &g_src[i];
   return NULL;`.  On image B it reads g_nsrc (A_OBJ 4 of lib/B/W_listing.v).  When g_nsrc > 0 it also reads g_src
   (A_OBJ 5) and the shadow base (through the GOT slot A_OBJ 0).  For each entry, in index order, it checks the shadow
   of the entry's first granule, loads the entry's fd with `lw` (sign-extended) and compares it with a0 as 64 bits.
   The table block's placement refutes the traps at 0x85d68 (PTR_BLTU), 0x85d74 (NULL_XOR) and 0x85d78 (BASE_OK):
   the blocks law (YCbqG.ARx_blocks_law) makes g_src 16-aligned and >= 4096, and its 896 bytes end below alloc_ceiling,
   so T + 56 i does not wrap.  The table's zero shadow (range_addressable_of_block_hp0_x) refutes the report at 0x85db8.
   When g_nsrc = 0 it returns 0 at 0x85d38 before any of them.

   relay_reads (s) is fuzz_reply.c's `r = relay_source (s->fd); return r != NULL && !r->eof;`.  0 < s and 8 | s refute
   the traps at 0x864f4 (NONNULL) and 0x864fc (ALIGN8).  The shadow check of s (0x8650c-0x86518, report 0x86568) reads
   s's granule: azs B s 4 with 8 | s puts all 8 bytes in the zero-shadow range (rd_azs8).  It loads s->fd (`lw`) and
   calls relay_source, whose contract is pb_relay_source.  Its result r is T + 56 j or 0: the table block's alignment
   refutes the trap at 0x8652c (ALIGN8 on r) and the table's zero shadow the report at 0x86578.  It returns 1 when
   entry j's eof is 0, else 0.

   The posts are W_contract.v's aleafx_post (W_contract_x.aleafx_post_x for the generic contracts): a journal at G = []
   (neither function writes a global or a block, and neither takes a fake frame), the callee-saved registers, the
   layout and the allocator state unchanged, every byte
   outside the function's own frame kept (view and writability, errno's view with them), the presence of every present
   byte, and the result in a0.  Frames: relay_source has 16 bytes (RS_STK; its one call, __asan_report_load4, is on a
   refuted path); relay_reads has 16 bytes with relay_source's 16 below them (RD_STK). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_pl W_kit W_img W_journal W_contract W_rep W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_contract_x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* relay_source's frame (its entry AF_fr_relay_source = 0x39e4, B 0x85d28, is the listing's, lib/B/W_listing.v) *)
Definition RS_FRAME : Z := 16.                 (* addi sp,sp,-16; ra at 8 *)
Definition RS_STK : Z := RS_FRAME.
(* relay_reads's frame (its entry AF_fr_relay_reads = 0x41a4, B 0x864e8) and stack: B calls relay_source (0x86520)
   where A inlines it, so relay_source's 16 bytes lie below relay_reads's 16 (W8Entry-2's RRDS_STK = 16 + RSRC_STK) *)
Definition RD_FRAME : Z := 16.                 (* addi sp,sp,-16; ra at 8, s0 at 0 *)
Definition RD_STK : Z := RD_FRAME + RS_STK.

Section c.
Variable B : asyms.
Variable RG : rep_globals.

(* relay_source's result: the address of the FIRST entry of the table T whose fd is fd (the scan runs up from
   index 0, 56 bytes a step), or 0 when there is none *)
Definition rs_found (T fd : Z) (es : list rentry) (a0 : word) : Prop :=
  (exists j e, nth_error es j = Some e /\ re_fd e = fd /\
     (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> fd) /\
     a0 = w64 (T + AENT * Z.of_nat j)) \/
  ((forall e, In e es -> re_fd e <> fd) /\ a0 = w64 0).

Definition rs_post (regs : bvmap 5 word) ly S (W : world SEGS) (mem : word -> option byte) (md : Model)
(T fd : Z) (es : list rentry) : world SEGS -> config -> Prop :=
aleafx_post B RS_STK regs ly S W mem md (rs_found T fd es).

(* fd < 2 ^ 32, not < 2 ^ 31: a0 is compared as 64 bits with the sign-extended entry fds, which are < 2 ^ 31
   (aentry_ok), so an fd in [2 ^ 31, 2 ^ 32) matches none and the result is 0, which the post says. *)
Definition rs_spec (pc : Z) : Prop :=
forall W ly S (regs : bvmap 5 word) mem md ch (T : Z) (es : list rentry) (fd : Z),
afn_pre SEGS B RS_STK ly S W regs mem md ch ->
getr regs 10 = w64 fd -> 0 <= fd < 2 ^ 32 ->
arelay_at B RG ly S W mem T es -> rom_view SEGS W mem ->
SRr SEGS W (cfg_at SEGS pc regs mem md) (rs_post regs ly S W mem md T fd es).

(* relay_reads (s): W8Entry-2's RRDS (lib/B/W_LLVMFuzzerTestOneInput_cut.v:707, a working branch
   61da015af91) with the entry pc as an argument.  s = HA is an open struct source whose four bytes s->fd lie in a
   zero-shadow range (azs: relay_reads reads them behind the shadow check at 0x8650c-0x86518).  The result is 1 when
   the first entry with s->fd has eof 0, and 0 when its eof is 1 or no entry has s->fd. *)
Definition rd_spec (pc : Z) : Prop :=
forall W ly S (regs : bvmap 5 word) mem md ch T es HA h,
afn_pre SEGS B RD_STK ly S W regs mem md ch ->
getr regs 10 = w64 HA -> 0 < HA -> HA mod 8 = 0 -> azs B HA 4 ->
asrc_at B ly S W mem HA h ->
arelay_at B RG ly S W mem T es -> rom_view SEGS W mem ->
SRr SEGS W (cfg_at SEGS pc regs mem md)
  (aleafx_post B RD_STK regs ly S W mem md
    (fun a0 =>
       (exists j e, nth_error es j = Some e /\ re_fd e = hs_fd h /\
          (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> hs_fd h) /\
          a0 = w64 (if re_eof e =? 0 then 1 else 0)) \/
       ((forall e, In e es -> re_fd e <> hs_fd h) /\ a0 = w64 0))).
End c.

(* THE GENERIC CONTRACTS (route (b), step 3, a Theorem Labs lane's CONVERSION.md (sha256 1015972e02a9; internal record)): rs_spec / rd_spec over any
   allocator relation ARx with its ghost list Hp (after S) and the generic journal's placement PST.  The posts are
   W_contract_x.aleafx_post_x (W_contract.v's aleafx_post over the generic journal; a read-only leaf allocates and
   frees nothing, so the callee's Hp is its ghost list at both ends).  These are cut_x's RSRC_x / RRDS_x
   (lib/B/W_LLVMFuzzerTestOneInput_cut_x.v :348 / :360, a working branch e43cf0c7bef) with the entry pc as an
   argument; every other conjunct is rs_spec's / rd_spec's text. *)
Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable RG : rep_globals.
Definition rs_post_x (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(T fd : Z) (es : list rentry) : world SEGS -> config -> Prop :=
aleafx_post_x B PST ARx RS_STK regs ly S Hp W mem md (rs_found T fd es).
Definition rs_spec_x (pc : Z) : Prop :=
forall W ly S Hp (regs : bvmap 5 word) mem md ch (T : Z) (es : list rentry) (fd : Z),
afn_pre_x SEGS B ARx RS_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 fd -> 0 <= fd < 2 ^ 32 ->
arelay_at B RG ly S W mem T es -> rom_view SEGS W mem ->
SRr SEGS W (cfg_at SEGS pc regs mem md) (rs_post_x regs ly S Hp W mem md T fd es).
Definition rd_spec_x (pc : Z) : Prop :=
forall W ly S Hp (regs : bvmap 5 word) mem md ch T es HA h,
afn_pre_x SEGS B ARx RD_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 HA -> 0 < HA -> HA mod 8 = 0 -> azs B HA 4 ->
asrc_at B ly S W mem HA h ->
arelay_at B RG ly S W mem T es -> rom_view SEGS W mem ->
SRr SEGS W (cfg_at SEGS pc regs mem md)
  (aleafx_post_x B PST ARx RD_STK regs ly S Hp W mem md
    (fun a0 =>
       (exists j e, nth_error es j = Some e /\ re_fd e = hs_fd h /\
          (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> hs_fd h) /\
          a0 = w64 (if re_eof e =? 0 then 1 else 0)) \/
       ((forall e, In e es -> re_fd e <> hs_fd h) /\ a0 = w64 0))).
End cx.

(* ---- what the walk takes from arelay_at (lib/B/W_rep.v), each through one projection, so that a conjunct added to
   arelay_at changes these lemmas and not the walk: g_src's value, g_nsrc's value, |es| <= 16, the table block, the
   table's bytes, the entries' representation *)
Lemma rs_rel_src : forall B RG ly S W mem T es, arelay_at B RG ly S W mem T es ->
  val_mem SEGS (arm W mem) (rg_src RG) 8 T.
Proof. intros B RG ly S W mem T es H. unfold arelay_at in H. tauto. Qed.
Lemma rs_rel_nsrc : forall B RG ly S W mem T es, arelay_at B RG ly S W mem T es ->
  val_mem SEGS (arm W mem) (rg_nsrc RG) 4 (Z.of_nat (length es)).
Proof. intros B RG ly S W mem T es H. unfold arelay_at in H. tauto. Qed.
Lemma rs_rel_len : forall B RG ly S W mem T es, arelay_at B RG ly S W mem T es -> (length es <= 16)%nat.
Proof. intros B RG ly S W mem T es H. unfold arelay_at in H. tauto. Qed.
Lemma rs_rel_blk : forall B RG ly S W mem T es, arelay_at B RG ly S W mem T es -> In (T, ATABLE) (ablocks B ly S).
Proof. intros B RG ly S W mem T es H. unfold arelay_at in H. tauto. Qed.
Lemma rs_rel_tab : forall B RG ly S W mem T es, arelay_at B RG ly S W mem T es -> exists tail, atable_at W mem T es tail.
Proof. intros B RG ly S W mem T es H. unfold arelay_at in H. tauto. Qed.
Lemma rs_rel_ents : forall B RG ly S W mem T es, arelay_at B RG ly S W mem T es -> Forall (aentry_ok B ly S W mem) es.
Proof. intros B RG ly S W mem T es H. unfold arelay_at in H. tauto. Qed.

(* ================================================================== the walk: pb_relay_source
   Structure donor (not cited): a working branch fc302b5d067 lib/B/Prog/relay_source.v, the same function's proof
   in the old a_call frame.  Its decomposition (the entry, the g_nsrc = 0 exit at 0x85d38, the loop from 0x85d68 to
   0x85dc0 with a1 = the result, then mv a0,a1 and the epilogue) and its loop invariant (a1 = a2 = the entry,
   a3 = the entries left, a4 = g_src, a5 = the shadow base, a6 = a7 = 1) are this walk's.  The symbolic-run form is
   lib/B/W_check_bounded.v's (a working branch 7e062bb9b9c: the same table walk), the entry-fd lemmas are the
   A drain arm's (lib/A/W_LLVMFuzzerTestOneInput_drain.v dr_tbl_fd / concat_entry_nth, a working branch
   6faf871ce4d), and the trap refutations cite lib/B/W_traps.v (a working branch 6c73ae99620). *)
Definition A_relay_source : Z := AF_fr_relay_source.
Definition A_relay_sourceP : Z := BASE + A_relay_source.
Definition A_rs_loop : Z := AF_fr_relay_source + 0x40.   (* 0x85d68: the loop head *)
Definition A_rs_exit : Z := AF_fr_relay_source + 0x98.   (* 0x85dc0: mv a0,a1 *)
(* The four image objects relay_source reads (the GOT slot of the shadow cell, the shadow cell, g_nsrc and g_src)
   are apart.  PAImg does not fix the objects' values relative to each other, so this is a Section hypothesis
   (W_check_bounded.v's cb_objs_apart with the GOT slot / cell pair added), discharged at PB_fr by rs_objs_apart_fr. *)
Definition rs_objs_apart : Prop :=
let g := VAL (A_OBJ 0) in let c := VAL (A_OBJ 30) in let ns := VAL A_g_nsrc in let sr := VAL A_g_src in
(ns + 4 <= sr \/ sr + 8 <= ns) /\ (ns + 4 <= g \/ g + 8 <= ns) /\ (ns + 4 <= c \/ c + 8 <= ns) /\
(sr + 8 <= g \/ g + 8 <= sr) /\ (sr + 8 <= c \/ c + 8 <= sr) /\ (g + 8 <= c \/ c + 8 <= g).
(* entry j's fd as the loop reads it: the 4 bytes at T + 56 j, and their range (aentry_ok) *)
Definition rs_ents (W : world SEGS) (mem : word -> option byte) (T : Z) (es : list rentry) : Prop :=
forall j e, nth_error es j = Some e ->
val_mem SEGS (mrestrict (w_H W) mem) (T + 56 * Z.of_nat j) 4 (re_fd e) /\ 0 <= re_fd e < 2 ^ 31.

(* ---- the bytes of the relay's table: entry j's 4-byte fd field, read out of atable_at *)
Definition rs_e0 : rentry := RE 0 0 0 [] 0 0 0 0 0 [] [] [] [].
Lemma rs_entry_bytes_length : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
  intros e H1 H2. unfold entry_bytes.
  rewrite !length_app, !Mem.length_le4, !Mem.length_le8, H1, H2. reflexivity.
Qed.
Lemma rs_concat_entry_length : forall es,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  length (concat (map entry_bytes es)) = (56 * length es)%nat.
Proof.
  induction es as [|e es IH]; intros HF; [reflexivity|].
  apply Forall_cons_iff in HF as [[H1 H2] HF].
  cbn [map concat length]. rewrite length_app, rs_entry_bytes_length, IH by assumption. lia.
Qed.
Lemma rs_concat_entry_nth : forall es i k d,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  (i < length es)%nat -> (k < 56)%nat ->
  nth (56 * i + k) (concat (map entry_bytes es)) d = nth k (entry_bytes (nth i es rs_e0)) d.
Proof.
  induction es as [|e es IH]; intros i k d HF Hi Hk; cbn [length] in Hi; [lia|].
  apply Forall_cons_iff in HF as [[H1 H2] HF].
  cbn [map concat]. destruct i as [|i].
  - replace (56 * 0 + k)%nat with k by lia. cbn [nth].
    apply app_nth1. rewrite rs_entry_bytes_length by assumption. exact Hk.
  - rewrite app_nth2 by (rewrite rs_entry_bytes_length by assumption; lia).
    rewrite rs_entry_bytes_length by assumption.
    replace (56 * S i + k - 56)%nat with (56 * i + k)%nat by lia.
    cbn [nth]. apply IH; [exact HF | lia | exact Hk].
Qed.
Lemma rs_nth_Z_to_le_bytes : forall n z k d, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  induction n as [|n IH]; intros z k d Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. f_equal.
    rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma rs_le4_le_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 v)) (Z_to_bv 8 0)) = YO0f.le_byte v 4 k.
Proof.
  intros v k Hv Hk. unfold Mem.le4. rewrite rs_nth_Z_to_le_bytes by exact Hk.
  rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 v) by (change (bv_modulus 64) with (2 ^ 64); lia).
  unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by exact Hv. reflexivity.
Qed.
Lemma rs_le_byte_1_byte : forall b : byte, Z_to_bv 8 (YO0f.le_byte (bv_unsigned b) 1 0) = b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, !(Z.mod_small (bv_unsigned b) 256) by exact Hr. reflexivity.
Qed.
Lemma rs_nth_bzs : forall l n, nth n (bzs l) 0 = bv_unsigned (nth n l (Z_to_bv 8 0)).
Proof.
  unfold bzs. induction l as [|b l IH]; intros [|n]; cbn [map nth]; try reflexivity. apply IH.
Qed.
Lemma rs_tbl_fd : forall (W : world SEGS) (mem : word -> option byte) (G : Z) (es : list rentry)
  (tail : list byte) (i : nat),
  atable_at W mem G es tail -> Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) es ->
  (i < length es)%nat ->
  val_mem SEGS (arm W mem) (G + AENT * Z.of_nat i) 4 (re_fd (nth i es rs_e0)).
Proof.
  intros W mem G es tail i [_ [_ Hg]] Hpad Hfd Hi.
  assert (Hv : 0 <= re_fd (nth i es rs_e0) < 2 ^ 31).
  { rewrite Forall_forall in Hfd. apply Hfd. apply nth_In. exact Hi. }
  pose proof (rs_concat_entry_length es Hpad) as Hcl.
  unfold val_mem. intros k Hk.
  assert (Hj : (56 * i + k < length (bzs (concat (map entry_bytes es) ++ tail)))%nat).
  { unfold bzs. rewrite length_map, length_app, Hcl. lia. }
  unfold garr8 in Hg. destruct (Hg _ Hj) as [Hb _]. unfold val_mem in Hb.
  specialize (Hb 0%nat ltac:(lia)).
  replace (G + AENT * Z.of_nat i + Z.of_nat k) with (G + Z.of_nat (56 * i + k) + Z.of_nat 0)
    by (unfold AENT; lia).
  rewrite Hb. f_equal.
  assert (Hn : nth (56 * i + k) (bzs (concat (map entry_bytes es) ++ tail)) 0 =
               bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 (re_fd (nth i es rs_e0)))) (Z_to_bv 8 0))).
  { rewrite rs_nth_bzs. f_equal.
    rewrite app_nth1 by (rewrite Hcl; lia).
    rewrite rs_concat_entry_nth by (first [exact Hpad | exact Hi | lia]).
    unfold entry_bytes. rewrite app_nth1 by (rewrite Mem.length_le4; exact Hk). reflexivity. }
  rewrite Hn, rs_le_byte_1_byte.
  apply bv_eq. rewrite Z_to_bv_unsigned, rs_le4_le_byte by lia.
  unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma rs_ents_of_relay : forall B RG ly S W mem T es, arelay_at B RG ly S W mem T es -> rs_ents W mem T es.
Proof.
  intros B0 RG0 ly S W mem T es HREL j e Hj.
  destruct (rs_rel_tab B0 RG0 ly S W mem T es HREL) as (tl & HTAB).
  pose proof (rs_rel_ents B0 RG0 ly S W mem T es HREL) as HE.
  assert (HPAD : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es /\
                 Forall (fun e => 0 <= re_fd e < 2 ^ 31) es).
  { split; rewrite Forall_forall in HE |- *; intros e' He';
      destruct (HE e' He') as (_ & _ & H3 & H4 & H5 & _); [split; assumption | exact H5]. }
  destruct HPAD as (HPAD & HFDS).
  assert (Hjl : (j < length es)%nat) by (apply nth_error_Some; congruence).
  pose proof (rs_tbl_fd W mem T es tl j HTAB HPAD HFDS Hjl) as M.
  assert (Ee : nth j es rs_e0 = e) by (apply nth_error_nth; exact Hj).
  rewrite Ee in M. unfold AENT in M. split; [exact M|].
  rewrite Forall_forall in HFDS. apply HFDS. eapply nth_error_In. exact Hj.
Qed.
(* the sign-extended 32-bit load of a small non-negative atom, and blez on it *)
Lemma rs_sx_U : forall E v, ew E 32 = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> U E (SExt true 32 (SOff 32 0)) = v.
Proof.
  intros E v Hv Hr. change (U E (SExt true 32 (SOff 32 0))) with (bv_unsigned (sv_denot E (SExt true 32 (SOff 32 0)))).
  rewrite U_sext32'. change (bv_unsigned (sv_denot E (SOff 32 0))) with (U E (SOff 32 0)).
  rewrite (U_atom E 32 v Hv) by lia. apply sx32_small. lia.
Qed.
Lemma rs_blez : forall E x v, U E x = v -> 0 <= v < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E x) = (v <=? 0).
Proof.
  intros E x v Hx Hv. cbn [branch_taken]. rewrite bv_lts_signed.
  assert (Hz : bv_signed (sv_denot E (SLit 0)) = 0) by reflexivity. rewrite Hz.
  unfold U in Hx. rewrite YK11.bv_signed_small by (rewrite Hx; lia). rewrite Hx.
  destruct (Z.ltb_spec 0 v), (Z.leb_spec v 0); try lia; reflexivity.
Qed.

(* ---- for pb_relay_reads: the eof of the first entry with fd (0 when there is none), and entry i's eof field *)
Definition rd_eofv (fd : Z) (es : list rentry) : Z :=
  match find (fun e => re_fd e =? fd) es with Some e => re_eof e | None => 0 end.
Lemma rd_eofv_first : forall fd es j e, nth_error es j = Some e -> re_fd e = fd ->
  (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> fd) -> rd_eofv fd es = re_eof e.
Proof.
  intros fd es. unfold rd_eofv. induction es as [|e0 es IH]; intros j e Hj Hfd Hfirst; [destruct j; discriminate|].
  cbn [find]. destruct j as [|j].
  - cbn in Hj. injection Hj as <-. rewrite (proj2 (Z.eqb_eq _ _) Hfd). reflexivity.
  - assert (Hne : re_fd e0 <> fd) by (apply (Hfirst 0%nat e0); [lia | reflexivity]).
    rewrite (proj2 (Z.eqb_neq _ _) Hne). apply (IH j e Hj Hfd).
    intros i e' Hi Hi'. apply (Hfirst (S i) e'); [lia | exact Hi'].
Qed.
(* entry i's eof field: the 4 bytes at T + 56 i + 4 (bytes 4..7 of entry_bytes), as rs_tbl_fd reads the fd field *)
Lemma rd_tbl_eof : forall (W : world SEGS) (mem : word -> option byte) (G : Z) (es : list rentry)
  (tail : list byte) (i : nat),
  atable_at W mem G es tail -> Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  Forall (fun e => 0 <= re_eof e < 2 ^ 31) es ->
  (i < length es)%nat ->
  val_mem SEGS (arm W mem) (G + AENT * Z.of_nat i + 4) 4 (re_eof (nth i es rs_e0)).
Proof.
  intros W mem G es tail i [_ [_ Hg]] Hpad Hev Hi.
  assert (Hv : 0 <= re_eof (nth i es rs_e0) < 2 ^ 31).
  { rewrite Forall_forall in Hev. apply Hev. apply nth_In. exact Hi. }
  pose proof (rs_concat_entry_length es Hpad) as Hcl.
  unfold val_mem. intros k Hk.
  assert (Hj : (56 * i + (4 + k) < length (bzs (concat (map entry_bytes es) ++ tail)))%nat).
  { unfold bzs. rewrite length_map, length_app, Hcl. lia. }
  unfold garr8 in Hg. destruct (Hg _ Hj) as [Hb _]. unfold val_mem in Hb.
  specialize (Hb 0%nat ltac:(lia)).
  replace (G + AENT * Z.of_nat i + 4 + Z.of_nat k) with (G + Z.of_nat (56 * i + (4 + k)) + Z.of_nat 0)
    by (unfold AENT; lia).
  rewrite Hb. f_equal.
  assert (Hn : nth (56 * i + (4 + k)) (bzs (concat (map entry_bytes es) ++ tail)) 0 =
               bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 (re_eof (nth i es rs_e0)))) (Z_to_bv 8 0))).
  { rewrite rs_nth_bzs. f_equal.
    rewrite app_nth1 by (rewrite Hcl; lia).
    rewrite rs_concat_entry_nth by (first [exact Hpad | exact Hi | lia]).
    unfold entry_bytes. rewrite app_nth2 by (rewrite Mem.length_le4; lia).
    rewrite Mem.length_le4. replace (4 + k - 4)%nat with k by lia.
    rewrite app_nth1 by (rewrite Mem.length_le4; exact Hk). reflexivity. }
  rewrite Hn, rs_le_byte_1_byte.
  apply bv_eq. rewrite Z_to_bv_unsigned, rs_le4_le_byte by lia.
  unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* ---- THE GENERIC WALKS (route (b), step 3; a Theorem Labs lane's CONVERSION.md (sha256 1015972e02a9; internal record)): relay_source and relay_reads
   over any allocator relation ARx with its laws, stated as rs_spec_x / rd_spec_x, in the form of W1Verify's
   lib/A/W_check_bounded.v (a working branch) and lib/A/W_relay_event.v pb_relay_event_x (88557c15170).  The
   Section hypotheses beyond the AR walks': PST / ARx / hl / LAWS (the generic relation), HP0 (the unit's hidden-head
   set is empty in every ARx state, a Theorem Labs lane's ruling 15:26Z, so YCbqG.ARx_shadow_law's premise holds at every state:
   W_journal_x's range_addressable_of_block_hp0_x) and, for relay_reads, HSYM (after HVcap below). ---- *)
Section w.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
(* the shadow base is read through the listing's GOT slot (A_OBJ 0) and cell (A_OBJ 30): the instance's cells are
   those two objects (W_kit.v PALib's pal_got_shadow / pal_cell, without PALib's allocator fields) *)
Hypothesis HBgot : as_got_shadow B = VAL (A_OBJ 0).
Hypothesis HBcell : as_shadow_cell B = VAL (A_OBJ 30).
(* g_nsrc and g_src are the listing's objects 4 and 5 (the PLdHi slots at 0x85d34 and 0x85d48) *)
Hypothesis HVns : VAL A_g_nsrc = rg_nsrc RG.
Hypothesis HVsr : VAL A_g_src = rg_src RG.
Hypothesis RSAP : rs_objs_apart.
Let HGnil : gx_ok SEGS B [] := gx_ok_nil SEGS B.
Let RUN := paj_run_x_x B PST ARx LAWS [] HGnil 0 []. Let RUNTO := paj_run_to_x_x B PST ARx LAWS [] HGnil 0 [].
Local Notation AJG := (ajournal_gx_x SEGS B PST ARx [] 0 []).
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Definition rs_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition RS_PHI : Z := 140737479966720.   (* 0x7fffff800000, above alloc_ceiling *)
(* the loop head 0x85d68: a1 = a2 = T + 56 i (entry i), a3 = the entries left, a4 = T, a5 = SB, a6 = (T <> 0) = 1,
   a7 = (T mod 8 = 0 && T <> 0) = 1, a0 = fd; entry i's fd is atom 32 *)
Definition rs_BxL : sv := SOff 15 0.
Definition rsl_regions : smem :=
[ YP09.mkRegion (Some 11%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))] ].
Definition rsl_facts : facts :=
mkFacts [ (11%nat, mkAF 4096 RS_PHI 3); (12%nat, mkAF 4096 RS_PHI 3); (15%nat, mkAF SB SB 0);
(16%nat, mkAF 1 1 0); (17%nat, mkAF 1 1 0); (32%nat, mkAF 0 (2 ^ 31 - 1) 0) ] [] [].
Definition ss_rsl : sstate := mkSS A_rs_loop sr_atoms rsl_regions None rsl_facts.
Definition rsl_SH : list shent := [ mkSHE 12 0 8 ].
Definition rsl_extra (f : Z) : list word := map (Z_to_bv 64) [f].
Definition RS_CLOB : list (bv 5) := [5; 6; 11; 12; 13]%bv.
Definition RS_KEPT : list (bv 5) :=
[1; 2; 3; 4; 7; 8; 9; 10; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma rs_clob_kept : forall r : bv 5, reg_in r RS_CLOB = false -> r = 0%bv \/ In r RS_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
Ltac rs_nowr := let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); vm_compute in Hin; destruct Hin as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia.
(* after a run whose regions have no writable window: the memory the run ends in is the one it began in *)
Ltac rs_meq MEQ MEQ' :=
lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict ?H ?msx), HFr : frame_of _ _ _ _ |- _ =>
lazymatch type of MEQ with forall x, mrestrict _ _ x = mrestrict _ ?m0 x =>
assert (MEQ' : forall x, mrestrict H (ms_mem msx) x = mrestrict H m0 x)
by (let x := fresh "x" in intros x; rewrite HFr; [apply MEQ | rs_nowr]) end end;
repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end; clear MEQ.
Ltac rs_awr_any := first [ OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbq.awr_ok_tac
                         | OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.awr_ok_tac ].
Ltac rs_awr := first [ rs_awr_any | cbn [ss_mem add_cond]; rs_awr_any |
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); cbn [ss_mem add_cond ss_rsl rsl_regions In] in Hin; destruct Hin as [<- | []];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia ].
(* the loop, from a fresh symbolic state at its head, by induction on the entries left; it ends at 0x85dc0 with
   a1 = the result *)
Lemma rs_loopX_x : forall (k i : nat) (T fd : Z) (es : list rentry) W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own
lyc Sc Hpc kk,
k = (length es - i)%nat -> (i < length es)%nat -> (length es <= 16)%nat ->
AJG STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc kk ->
In (T, ATABLE) (ablocks B lyc Sc) ->
getr regs 11 = w64 (T + 56 * Z.of_nat i) -> getr regs 12 = w64 (T + 56 * Z.of_nat i) ->
getr regs 13 = w64 (Z.of_nat (length es - i)) -> getr regs 14 = w64 T -> getr regs 15 = w64 SB ->
getr regs 16 = w64 1 -> getr regs 17 = w64 1 -> getr regs 10 = w64 fd -> 0 <= fd < 2 ^ 32 ->
rs_ents W memc T es ->
(forall j e, (j < i)%nat -> nth_error es j = Some e -> re_fd e <> fd) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_rs_loop)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_rs_exit)) mem' (seg_rom SEGS)) md' /\
AJG STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' kk /\
(forall r, In r RS_KEPT -> getr regs' r = getr regs r) /\
rs_found T fd es (getr regs' 11) /\
(forall x, mrestrict (w_H W) mem' x = mrestrict (w_H W) memc x)).
Proof.
induction k as [|k IH]; intros i T fd es W regs memc mdc STK sp0 FP ly Sx Hp W0 mem0 md0 own lyc Sc Hpc kk
Hk Hi Hn16 HJ HTin H11 H12 H13 H14 H15 H16 H17 H10 Hfd HENT HNM; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAR : ARx lyc Sc Hpc W memc mdc) by (eapply ajournal_gx_AR_x; exact HJ).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memc mdc T ATABLE HAR HTin) as (HT16 & HT4096 & HTceil & HTapp & HTpres & HTpw).
assert (Hreq : req_size ATABLE = 896) by reflexivity. rewrite Hreq in HTceil, HTapp.
assert (Hi16 : Z.of_nat i < 16) by lia.
assert (PB : 4096 <= T /\ T + 56 * Z.of_nat i + 56 <= T + 896 <= RS_PHI) by (unfold RS_PHI; lia).
assert (T8 : T = 8 * (T / 8)).
{ pose proof (Z.div_mod T 16 ltac:(lia)) as D. rewrite HT16, Z.add_0_r in D.
  rewrite D at 2. replace (16 * (T / 16)) with ((2 * (T / 16)) * 8) by ring. rewrite Z.div_mul by lia. lia. }
destruct (nth_error es i) as [e|] eqn:Hei; [|apply nth_error_None in Hei; lia].
destruct (HENT i e Hei) as (Mfd & Rfd).
remember (Eimg (Ereg regs (rsl_extra (re_fd e)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (rsl_extra (re_fd e))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E10 : ew E 10 = Z_to_bv 64 fd) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (T + 56 * Z.of_nat i)) by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 (T + 56 * Z.of_nat i)) by (rewrite (EEo 12%nat 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 (Z.of_nat (length es - i))) by (rewrite (EEo 13%nat 13%bv eq_refl); exact H13).
assert (E14 : ew E 14 = Z_to_bv 64 T) by (rewrite (EEo 14%nat 14%bv eq_refl); exact H14).
assert (E15 : ew E 15 = Z_to_bv 64 SB) by (rewrite (EEo 15%nat 15%bv eq_refl); exact H15).
assert (E16 : ew E 16 = Z_to_bv 64 1) by (rewrite (EEo 16%nat 16%bv eq_refl); exact H16).
assert (E17 : ew E 17 = Z_to_bv 64 1) by (rewrite (EEo 17%nat 17%bv eq_refl); exact H17).
assert (E32 : ew E 32 = Z_to_bv 64 (re_fd e))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HS : st_ok_pi SEGS VAL E ss_rsl (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_rs_loop)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rsl. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rsl_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite E11, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (T + 56 * Z.of_nat i) 0 4 (SOff 32 0) (re_fd e));
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact Mfd.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [rsl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E11, E12, E15, E16, E17, E32, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert T8 HT4096 PB Hi16 Rfd C1. clear. unfold RS_PHI, SB. intros.
  repeat match goal with |- _ /\ _ => split end; try lia;
  rewrite T8; replace (8 * (T / 8) + 56 * Z.of_nat i) with ((T / 8 + 7 * Z.of_nat i) * 8) by ring; apply Z_mod_mult. }
clear HE.
assert (HBx : U E rs_BxL = SHADOW_OFF) by (unfold rs_BxL; rewrite (U_atom E 15 SB E15) by (unfold SB; lia); reflexivity).
assert (SHOK : sh_ok SEGS rs_BxL rsl_SH E (mrestrict (w_H W) memc)).
{ constructor; [|constructor].
  eapply shent_ok_of_range.
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyc Sc Hpc W memc mdc T ATABLE (T + 56 * Z.of_nat i) 8 HAR HTin);
    rewrite ?Hreq; lia.
  + exact HBx.
  + rewrite (U_atom E 12 _ E12) by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
unfold A_rs_loop.
(* 0x85d68 bltu a2,a4: PTR_BLTU, never taken: a2 = T + 56 i does not wrap *)
psrr_branch_tok RUN BR HS SHOK rs_Bspan.
- exfalso. rewrite (trap_ptr_wrap_atom E 12 14 T (56 * Z.of_nat i) E12 E14) in Hc by lia. discriminate.
- paj_run_tok_x RUN HS HJ SHOK rs_Bspan. { apply awr_ok_x_of0; rs_awr. }
  assert (MEQ1 : forall x, mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) memc x) by (intros x; apply HFr; rs_nowr).
  clear HF HFr HG.
  (* 0x85d74 beqz t0: NULL_XOR, never taken (the runner folded seqz a2 to 0 from a2 >= 4096; a6 = 1) *)
  psrr_branch_tok RUN BR HS SHOK rs_Bspan.
  + exfalso. rewrite (trap_null_xor_folded E 16 E16) in Hc0. discriminate.
  + (* 0x85d78 beqz a7 (BASE_OK) is decided by the runner from a7 = 1; the shadow check 0x85d7c-0x85d88 by the
       token runner from rsl_SH, so its slow test 0x85da8 and the report 0x85db8 are not reached *)
    paj_run_tok_x RUN HS HJ SHOK rs_Bspan. { apply awr_ok_x_of0; rs_awr. }
    rs_meq MEQ1 MEQ2.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (F10 : ew Ev 10 = Z_to_bv 64 fd) by (rewrite ?ew_ewset_other by lia; exact E10);
      assert (F13 : ew Ev 13 = Z_to_bv 64 (Z.of_nat (length es - i))) by (rewrite ?ew_ewset_other by lia; exact E13);
      assert (F32 : ew Ev 32 = Z_to_bv 64 (re_fd e)) by (rewrite ?ew_ewset_other by lia; exact E32);
      assert (HAE2 : env_agree 32 (Ereg regs (rsl_extra (re_fd e))) Ev)
        by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite ?ed_ewset; exact (proj2 HAE)])
    end.
    (* 0x85d90 beq t0,a0: entry i's fd (lw, sign-extended; it is < 2^31) against fd as 64 bits *)
    psrr_branch_tok RUN BR HS SHOK rs_Bspan.
    * (* taken: entry i is the first with fd; to 0x85dc0 with a1 = T + 56 i *)
      rewrite trap_br_eq, (U_atom _ 32 _ F32), (U_atom _ 10 _ F10) in Hc1 by lia.
      apply Z.eqb_eq in Hc1.
      paj_run_to_tok_x RUNTO HS HJ SHOK rs_Bspan (AF_fr_relay_source + 152). { apply awr_ok_x_of0; rs_awr. }
      rs_meq MEQ2 MEQ3.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ RS_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as HK.
      cbn [ms_regs restrict] in HK.
      prreg HS (11%bv : bv 5) N11. rewrite E11 in N11.
      pmkst HS.
      apply SRr_ret. split; [reflexivity|].
      lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
      split; [reflexivity|]. split; [exact HJ|]. split; [exact HK|]. split; [|exact MEQ3].
      left. exists i, e. split; [exact Hei|]. split; [exact Hc1|]. split; [exact HNM|].
      rewrite N11. unfold w64, AENT. reflexivity.
    * (* not taken: entry i is not the one *)
      rewrite trap_br_eq, (U_atom _ 32 _ F32), (U_atom _ 10 _ F10) in Hc1 by lia.
      apply Z.eqb_neq in Hc1.
      paj_run_tok_x RUN HS HJ SHOK rs_Bspan. { apply awr_ok_x_of0; rs_awr. }
      rs_meq MEQ2 MEQ3.
      (* 0x85da0 beqz a3: no entry left *)
      psrr_branch_tok RUN BR HS SHOK rs_Bspan.
      -- (* taken: i was the last entry; 0x85dbc a1 = 0, to 0x85dc0 *)
         rewrite trap_br_eq, (U_atom_off _ 13 _ (-1) F13), U_lit in Hc2 by lia.
         assert (Hlast : S i = length es)
           by (destruct (Z.eqb_spec (Z.of_nat (length es - i) + -1) 0); [lia | discriminate]).
         paj_run_to_tok_x RUNTO HS HJ SHOK rs_Bspan (AF_fr_relay_source + 152). { apply awr_ok_x_of0; rs_awr. }
         rs_meq MEQ3 MEQ4.
         pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ RS_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as HK.
         cbn [ms_regs restrict] in HK.
         prreg HS (11%bv : bv 5) N11.
         pmkst HS.
         apply SRr_ret. split; [reflexivity|].
         lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
         split; [reflexivity|]. split; [exact HJ|]. split; [exact HK|]. split; [|exact MEQ4].
         right. split; [|rewrite N11; reflexivity].
         intros e' He'. apply In_nth_error in He' as (j & Hj).
         assert (Hjl : (j < length es)%nat) by (apply nth_error_Some; congruence).
         destruct (Nat.lt_ge_cases j i) as [Hji|Hji]; [exact (HNM j e' Hji Hj)|].
         assert (j = i) as -> by lia. rewrite Hei in Hj. injection Hj as <-. exact Hc1.
      -- (* not taken: back to the head at i + 1 *)
         rewrite trap_br_eq, (U_atom_off _ 13 _ (-1) F13), U_lit in Hc2 by lia.
         assert (Hlt : (S i < length es)%nat)
           by (destruct (Z.eqb_spec (Z.of_nat (length es - i) + -1) 0); [discriminate | lia]).
         paj_run_to_tok_x RUNTO HS HJ SHOK rs_Bspan (AF_fr_relay_source + 64). { apply awr_ok_x_of0; rs_awr. }
         rs_meq MEQ3 MEQ4.
         pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ RS_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as HK.
         cbn [ms_regs restrict] in HK.
         prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12. prreg HS (13%bv : bv 5) N13.
         rewrite E11, unsigned_lit_small in N11 by lia. rewrite E12, unsigned_lit_small in N12 by lia.
         rewrite E13, unsigned_lit_small in N13 by lia.
         lazymatch type of MEQ4 with forall x, mrestrict ?H0 ?m0 x = _ =>
           assert (MEQf : mrestrict H0 m0 = mrestrict (w_H W) memc) by (apply functional_extensionality; exact MEQ4) end.
         pmkst HS.
         eapply SRr_mono.
         { unfold A_rs_loop in IH.
           eapply (IH (S i) T fd es W _ _ _ STK sp0 FP ly Sx Hp W0 mem0 md0 own lyc Sc Hpc kk);
           [ lia | exact Hlt | exact Hn16 | exact HJ | exact HTin
           | cbn [ms_regs]; rewrite N11; unfold w64; f_equal; lia
           | cbn [ms_regs]; rewrite N12; unfold w64; f_equal; lia
           | cbn [ms_regs]; rewrite N13; unfold w64; f_equal; lia
           | cbn [ms_regs]; rewrite (HK 14%bv ltac:(cbv; tauto)); exact H14
           | cbn [ms_regs]; rewrite (HK 15%bv ltac:(cbv; tauto)); exact H15
           | cbn [ms_regs]; rewrite (HK 16%bv ltac:(cbv; tauto)); exact H16
           | cbn [ms_regs]; rewrite (HK 17%bv ltac:(cbv; tauto)); exact H17
           | cbn [ms_regs]; rewrite (HK 10%bv ltac:(cbv; tauto)); exact H10
           | exact Hfd
           | intros j e' Hj; cbn [ms_mem]; rewrite MEQf; exact (HENT j e' Hj)
           | intros j e' Hj Hj'; destruct (Nat.lt_ge_cases j i) as [Hji|Hji];
             [ exact (HNM j e' Hji Hj')
             | assert (j = i) as -> by lia; rewrite Hei in Hj'; injection Hj' as <-; exact Hc1 ] ]. }
         cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & HF3 & MEQ5).
         split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|]. split.
         { intros r Hr. rewrite (HK3 r Hr). cbn [ms_regs]. exact (HK r Hr). }
         split; [exact HF3|].
         intros x. rewrite MEQ5. cbn [ms_mem]. apply MEQ4.
Qed.
(* a byte that stays present stays writable, in the same world *)
Lemma rs_writable_kept : forall (W : world SEGS) (m m' : word -> option byte) a,
(apresent (w_H W) m a -> apresent (w_H W) m' a) ->
writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W) m') a.
Proof.
intros W m m' a Hp Hw. unfold writable_at, wview, mrestrict in Hw |- *.
destruct (w_H W (Z_to_bv 64 a)) eqn:EH; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
(* presence across the runs: chain every run's mem_grows from the entry memory to the current one *)
Ltac rs_pres :=
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
repeat match goal with
| HG' : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2), Hp : apresent ?H ?m1 a |- _ =>
  lazymatch goal with _ : apresent H m2 a |- _ => fail | _ => idtac end;
  assert (apresent H m2 a) by (eapply apresent_grows; [exact HG' | exact Hp])
end; assumption.
(* the outer walk's regions: only the stack region has a writable window, so a byte outside the frame is
   outside every region's window *)
Ltac rs_nowr5 :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); vm_compute in Hin;
repeat (destruct Hin as [<- | Hin];
 [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  repeat match goal with Hu : bv_unsigned (ew _ 2) = _ |- _ => rewrite Hu in Hr end;
  first [lia | match goal with Hno : ~ _ |- _ => apply Hno; unfold RS_STK, RS_FRAME in *; lia end] |]);
destruct Hin.
(* the entry 0x85d28 *)
Definition rs_Bx : sv := SOff 34 0.
Definition rs_regions : smem :=
[ stack_region RS_STK; got_regionP; bcell_regionP 34;
YP09.mkRegion (Some A_g_nsrc) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))];
YP09.mkRegion (Some A_g_src) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))] ].
Definition rs_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF 0 (2 ^ 32 - 1) 0); (33%nat, mkAF 0 (2 ^ 64 - 1) 0);
(34%nat, mkAF SB SB 0) ] [] [].
Definition ss_rs : sstate := mkSS A_relay_source sr_atoms rs_regions None rs_facts.
Definition rs_SH : list shent := [].
Definition rs_extra (n T : Z) : list word := map (Z_to_bv 64) [n; T; SB].
Lemma rs_entry_x : forall W ly S Hp regs mem md ch n T,
afn_pre_x SEGS B ARx RS_STK ly S Hp W regs mem md ch ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_nsrc) 4 n -> 0 <= n < 2 ^ 32 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_src) 8 T -> 0 <= T < 2 ^ 64 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (rs_extra n T))) ss_rs
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_relay_sourceP) mem (seg_rom SEGS)))
/\ sh_ok SEGS rs_Bx rs_SH (Eimg (Ereg regs (rs_extra n T))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch n T HPRE Mn Rn MT RT.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RS_STK = 16) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (rs_extra n T))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 T) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EO : forall i, (i < 31)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_obj_img 4 ltac:(lia)) as HnsR. pose proof (pa_obj_img 5 ltac:(lia)) as HsrR.
change (A_OBJ 4) with A_g_nsrc in HnsR. change (A_OBJ 5) with A_g_src in HsrR.
pose proof RSAP as (D1 & D2 & D3 & D4 & D5 & D6). cbv zeta in D1, D2, D3, D4, D5, D6.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (VBO : forall i, (i < 31)%nat -> base_val E (Some (A_OBJ i)) = VAL (A_OBJ i)).
{ intros i Hi. apply VB; [exact (EO i Hi) | exact (pa_val_range _)]. }
split.
- unfold ss_rs, A_relay_sourceP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold rs_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VBO 0%nat ltac:(lia)). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
[cbn [sv_denot]; rewrite (EO 30%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VBO 30%nat ltac:(lia)). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 (SOff 34 0) SB);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* unfold A_g_nsrc. rewrite (VBO 4%nat ltac:(lia)). fold A_g_nsrc. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL A_g_nsrc) 0 4 (SOff 32 0) n);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact Mn.
* unfold A_g_src. rewrite (VBO 5%nat ltac:(lia)). fold A_g_src. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL A_g_src) 0 8 (SOff 33 0) T);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact MT.
+ apply pairwise_disjoint_of_extents. unfold rs_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
unfold A_g_nsrc, A_g_src. rewrite (VBO 0%nat ltac:(lia)), (VBO 30%nat ltac:(lia)), (VBO 4%nat ltac:(lia)), (VBO 5%nat ltac:(lia)).
fold A_g_nsrc A_g_src. cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgotR HnsR HsrR D1 D2 D3 D4 D5 D6. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [rs_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 Rn RT. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, rs_SH. constructor.
Qed.
Theorem pb_relay_source_x : rs_spec_x B PST ARx RG A_relay_sourceP.
Proof.
intros W ly S Hp regs mem md ch T es fd HPRE H10 Hfd HREL HROM.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (rs_rel_src B RG ly S W mem T es HREL) as MT. pose proof (rs_rel_nsrc B RG ly S W mem T es HREL) as MN.
pose proof (rs_rel_len B RG ly S W mem T es HREL) as Hle16. pose proof (rs_rel_blk B RG ly S W mem T es HREL) as HTin.
pose proof (rs_ents_of_relay B RG ly S W mem T es HREL) as HENTm.
unfold arm in MT, MN. rewrite <- HVsr in MT. rewrite <- HVns in MN.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md T ATABLE HAR HTin) as (HT16 & HT4096 & HTceil & HTapp & HTpres & HTpw).
assert (Hreq : req_size ATABLE = 896) by reflexivity. rewrite Hreq in HTceil, HTapp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (RT : 0 <= T < 2 ^ 64) by lia.
assert (Rn : 0 <= Z.of_nat (length es) < 2 ^ 32) by lia.
destruct (rs_entry_x W ly S Hp regs mem md ch (Z.of_nat (length es)) T HPRE MN Rn MT RT) as [HS SHOK].
assert (HJ : AJG RS_STK (spZ regs) [] ly S Hp W mem md [] ly S Hp W mem md 0)
by (apply ajournal_gx_nil_x; exact (ajournal_x_init SEGS B PST ARx RS_STK [] ly S Hp W regs mem md ch HPRE)).
remember (Eimg (Ereg regs (rs_extra (Z.of_nat (length es)) T))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (Z.of_nat (length es))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 T) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (rs_extra (Z.of_nat (length es)) T)) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_relay_sourceP) with (Z_to_bv 64 A_relay_sourceP).
unfold A_relay_sourceP, A_relay_source.
paj_run_tok_x RUN HS HJ SHOK rs_Bspan. { apply awr_ok_x_of0; rs_awr_any. exact Usp. }
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RS_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
by (intros a Ha Hno; apply (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a Ha); rs_nowr5).
(* 0x85d38 blez a3: g_nsrc (lw, sign-extended) <= 0 *)
psrr_branch_tok RUN BR HS SHOK rs_Bspan.
-
(* taken: g_nsrc = 0, so the table has no entry; to 0x85dbc (a1 = 0) and the return with a0 = 0 *)
rewrite (rs_blez E _ (Z.of_nat (length es)) (rs_sx_U E (Z.of_nat (length es)) E32 ltac:(lia))) in Hc by lia.
apply Z.leb_le in Hc.
assert (Hnil : es = []) by (destruct es; [reflexivity | cbn [length] in Hc; lia]).
paj_run_tok_x RUN HS HJ SHOK rs_Bspan. { apply awr_ok_x_of0; rs_awr_any. exact Usp. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RS_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a)
by (intros a Ha Hno;
    match goal with H : frame_of ?Ev _ (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
      rewrite (aview_kept_out Ev _ (w_H W) (ms_mem ms) (ms_mem ms0) H a Ha) by rs_nowr5 end;
    apply KEEP0; assumption).
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold rs_post_x, aleafx_post_x.
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [|split; [|split; [|split]]].
+ cbn [ms_mem]. apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs). exact HJ.
+ lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ regs (rs_extra (Z.of_nat (length es)) T) HS);
  [exact HAE | vm_compute; reflexivity] end.
+ cbn [ms_mem]. rs_pres.
+ cbn [ms_mem]. intros a Ha Hno. split; [exact (KEEP1 a Ha Hno)|].
  apply rs_writable_kept. clear Ha Hno. revert a. rs_pres.
+ cbn [ms_regs]. rewrite R10. subst es. right. split; [intros e' []|reflexivity].
-
(* not taken: g_nsrc > 0; to the loop head 0x85d68 *)
rewrite (rs_blez E _ (Z.of_nat (length es)) (rs_sx_U E (Z.of_nat (length es)) E32 ltac:(lia))) in Hc by lia.
apply Z.leb_gt in Hc.
assert (T8 : T = 8 * (T / 8)).
{ pose proof (Z.div_mod T 16 ltac:(lia)) as D. rewrite HT16, Z.add_0_r in D.
  rewrite D at 2. replace (16 * (T / 16)) with ((2 * (T / 16)) * 8) by ring. rewrite Z.div_mul by lia. lia. }
assert (SXn : sext 64 (bv_extract 0 32 (ew E 32)) = w64 (Z.of_nat (length es))).
{ assert (Hd : sext 64 (bv_extract 0 32 (ew E 32)) = sv_denot E (SExt true 32 (SOff 32 0)))
  by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  rewrite Hd. apply bv_eq.
  change (bv_unsigned (sv_denot E (SExt true 32 (SOff 32 0)))) with (U E (SExt true 32 (SOff 32 0))).
  rewrite (rs_sx_U E _ E32) by lia. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
paj_run_to_tok_x RUNTO HS HJ SHOK rs_Bspan (AF_fr_relay_source + 64). { apply awr_ok_x_of0; rs_awr_any. exact Usp. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RS_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a)
by (intros a Ha Hno;
    match goal with H : frame_of ?Ev _ (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
      rewrite (aview_kept_out Ev _ (w_H W) (ms_mem ms) (ms_mem ms0) H a Ha) by rs_nowr5 end;
    apply KEEP0; assumption).
prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
prreg HS (13%bv : bv 5) T13. prreg HS (14%bv : bv 5) T14. prreg HS (15%bv : bv 5) T15.
prreg HS (16%bv : bv 5) T16. prreg HS (17%bv : bv 5) T17.
rewrite E10 in T10. rewrite E33 in T11, T12, T14, T16, T17. rewrite SXn in T13. rewrite E34 in T15.
assert (HT0 : 0 < T < 2 ^ 64) by lia.
assert (HT8 : T mod 8 = 0) by (rewrite T8; rewrite Z.mul_comm; apply Z_mod_mult).
(* a6 = snez g_src and a7 = (g_src 8-aligned and not null), the UBSan flags of 0x85d50-0x85d5c *)
rewrite (trap_w_snez T HT0) in T16. rewrite (trap_w_base_ok T HT0 HT8) in T17.
(* the entries are bytes of the block g_src points at, which the runs to here (writing only the frame) kept *)
assert (KB : forall a, T <= a < T + 896 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha. pose proof HJ as HJ0. apply ajournal_gx_nil_x in HJ0.
  destruct HJ0 as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & F2 & J11 & J12 & J13 & J14 & J15 & J16 & J17).
  replace a with (T + (a - T)) by lia.
  apply (F2 T ATABLE (a - T) HTin HTin); [rewrite ?Hreq; lia | apply inFP_nil]. }
assert (HENT0 : rs_ents W (ms_mem ms0) T es).
{ intros j e Hj. destruct (HENTm j e Hj) as (Mj & Rj). split; [|exact Rj].
  assert (Hjl : (j < length es)%nat) by (apply nth_error_Some; congruence).
  apply (val_mem_kept SEGS (w_H W) (w_H W) mem (ms_mem ms0)); [intros q Hq; apply KB; lia | exact Mj]. }
pmkst HS.
eapply SRr_bind.
{ unfold A_rs_loop.
  eapply (rs_loopX_x (length es) 0 T fd es W (ms_regs ms0) (ms_mem ms0) _ RS_STK (spZ regs) [] ly S Hp W mem md [] ly S Hp 0);
  [ lia | lia | lia | exact HJ | exact HTin
  | rewrite T11; unfold w64; f_equal; lia
  | rewrite T12; unfold w64; f_equal; lia
  | rewrite T13; unfold w64; f_equal; lia
  | exact T14 | exact T15 | exact T16 | exact T17
  | rewrite T10; exact H10 | exact Hfd | exact HENT0
  | intros j e Hj; lia ]. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & HF3 & MEQ3).
assert (HGL : mem_grows (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) mem3)) by (intros x Hx; rewrite MEQ3; exact Hx).
(* back at 0x85dc0: splice the loop's result into the outer state *)
jafter_stretch_pi HS 35%nat regs3 (mrestrict (w_H W) mem3) RS_CLOB (AF_fr_relay_source + 152) HS2.
match type of HS2 with ?P1 -> ?Q1 -> _ =>
assert (HP : P1); [|assert (HQ : Q1); [|specialize (HS2 HP HQ); clear HP HQ]] end.
{ intros r0 Hr0. cbn [ms_regs restrict]. destruct (rs_clob_kept r0 Hr0) as [-> | Hin]; [rewrite !getr_zero; reflexivity | exact (HK3 r0 Hin)]. }
{ cbn [ms_mem restrict].
  assert (MEQf : mrestrict (w_H W) mem3 = mrestrict (w_H W) (ms_mem ms0)) by (apply functional_extensionality; exact MEQ3).
  rewrite MEQf. repeat apply Forall_cons; try apply Forall_nil; split; intros; first [reflexivity | assumption]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 35 (map (getr regs3) RS_CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 35)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs (rs_extra (Z.of_nat (length es)) T)) Ea)
by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (Usp3 : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by (cbv; lia); exact Usp).
assert (SHOK2 : sh_ok SEGS rs_Bx rs_SH Ea (mrestrict (w_H W) mem3)) by (unfold sh_ok, rs_SH; constructor).
prreg HS (11%bv : bv 5) A11.
(* 0x85dc0 mv a0,a1; the epilogue; ret *)
paj_run_tok_x RUN HS HJ3 SHOK2 rs_Bspan. { apply awr_ok_x_of0; rs_awr_any. exact Usp3. }
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RS_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
  match goal with H : frame_of Ea _ (mrestrict (w_H W) mem3) (mrestrict (w_H W) (ms_mem ms1)) |- _ =>
  rewrite (aview_kept_out Ea _ (w_H W) mem3 (ms_mem ms1) H a Ha)
  by (let r := fresh in let Hin := fresh in let Hr := fresh in
      intros (r & Hin & Hr); vm_compute in Hin;
      repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
       rewrite ?Usp3 in Hr; first [lia | apply Hno; unfold RS_STK, RS_FRAME in *; lia] |]); destruct Hin) end.
  rewrite (aview_eq_of SEGS _ _ _ a (MEQ3 (Z_to_bv 64 a))). apply KEEP1; assumption. }
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold rs_post_x, aleafx_post_x.
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1; rewrite OLDa by (cbv; lia); rewrite E1, Hra; reflexivity|].
split; [|split; [|split; [|split]]].
+ cbn [ms_mem]. apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs). exact HJ3.
+ lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ regs (rs_extra (Z.of_nat (length es)) T) HS);
  [exact HAEa | vm_compute; reflexivity] end.
+ cbn [ms_mem]. rs_pres.
+ cbn [ms_mem]. intros a Ha Hno. split; [exact (KEEP2 a Ha Hno)|].
  apply rs_writable_kept. clear Ha Hno. revert a. rs_pres.
+ cbn [ms_regs]. rewrite R10, <- A11. exact HF3.
Qed.

(* ================================================================== the walk: pb_relay_reads
   The entry 0x864e8 runs to 0x8651c (prologue, the two traps on s, the shadow base through the GOT slot and the cell,
   the shadow check of s); there the two cells leave the symbolic state (they are not read again) and s's first word
   becomes a region; the run continues to the jal at 0x86520.  The call is discharged by pb_relay_source_x and spliced
   back as lib/B/W_relay_event.v splices send_line (afn_pre_x_at, ajournal_gx_sub_x, jafter_call_keep_pi).  From 0x86524 the
   two results of relay_source run to the ret: r = 0 (the beqz to the epilogue) and r = T + 56 j, where the engine is
   told r's range and alignment, entry j's eof word becomes a region and r's granule's shadow is the table block's. *)
(* g_capsrc lies in image B's band (at B's pin it is 0x5d8d80, lib/B/W_rep.v fr_globals_b; rd_capsrc_fr): relay_source
   reads the relay through arelay_at, so the walk carries arelay_at, g_capsrc's cell with it, past its frame stores *)
Hypothesis HVcap : 0x10000 <= rg_capsrc RG /\ rg_capsrc RG + 4 <= 0x5fc000.
(* s's placement: B's zero-shadow ranges lie below kLowMemEnd (asyms_ok's aso_zshadow), so s, whose 8 bytes lie in one
   of them, does.  The AR walk read asyms_ok off AR (ARm's am_syms); the generic laws state nothing about B's static
   ranges, so it is this Section hypothesis over ARx: at ARi0 it is am_syms (Section cAR), at the cf instance ARmcf's
   amc_syms (Reusable/YG0ncf.v:216). *)
Hypothesis HSYM : forall ly S Hp W mem md, ARx ly S Hp W mem md -> asyms_ok B.
Definition A_relay_reads : Z := AF_fr_relay_reads.
Definition A_relay_readsP : Z := BASE + A_relay_reads.
(* the entry: s = a0 is atom 10 (lo 8 decides the NONNULL trap, al2 3 the ALIGN8 trap), s->fd atom 32, the shadow base
   atom 33 (s0 from 0x86508 on), entry j's eof atom 34 (rd_eofv); the frame region, the GOT slot and the cell *)
Definition rd_Bx : sv := SOff 33 0.
Definition rd_regions : smem := [ stack_region RD_FRAME; got_regionP; bcell_regionP 33 ].
Definition rd_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 8 2147450872 3);
(32%nat, mkAF 0 (2 ^ 31 - 1) 0); (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_rd : sstate := mkSS A_relay_reads sr_atoms rd_regions None rd_facts.
Definition rd_SH : list shent := [ mkSHE 10 0 8 ].
Definition rd_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rd_extra (fd ev : Z) : list word := map (Z_to_bv 64) [fd; SB; ev].
(* s's first word (from 0x8651c), and entry j's eof word at r + 4 (r is atom 39 after the call: CLOB's a0) *)
Definition rd_sreg : YP09.region := YP09.mkRegion (Some 10%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition rd_eofr : YP09.region := YP09.mkRegion (Some 39%nat) 4 8 4 4 [YP09.mkChunk 4 (CVal 4 (SOff 34 0))].
(* keep only the first region of a symbolic state *)
Lemma rd_keep1 : forall E ss ms r rs, st_ok_pi SEGS VAL E ss ms -> ss_mem ss = r :: rs -> region_wf r = true ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) [r] (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r rs HS Hm Hw.
assert (Hs : submem [r] (ss_mem ss)).
{ rewrite Hm. apply submem_keep; [apply subregion_refl|]. clear. induction rs as [|r' rs IH]; [constructor | apply submem_drop; exact IH]. }
assert (Hwf : regions_wf [r] = true) by (unfold regions_wf; cbn; rewrite Hw; reflexivity).
destruct ss as [pc0 sr0 fr0 sm0 rv0 fs0]. exact (st_ok_submem SEGS E _ ms [r] HS Hs Hwf).
Qed.
(* a byte outside relay_reads's frame is outside every region's writable window *)
Ltac rd_nowr :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); vm_compute in Hin;
repeat (destruct Hin as [<- | Hin];
 [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  repeat match goal with Hu : bv_unsigned (ew _ 2) = _ |- _ => rewrite Hu in Hr end;
  first [lia | match goal with Hno : ~ _ |- _ => apply Hno; unfold RD_FRAME, RD_STK, RS_STK, RS_FRAME in *; lia end] |]);
destruct Hin.
(* the shadow check of s (0x8650c-0x86518) reads its whole granule: s is 8-aligned and its zero-shadow range ends on
   a granule boundary, so the range that holds s's 4 bytes holds all 8 *)
Lemma rd_azs8 : forall HA, HA mod 8 = 0 -> azs B HA 4 -> azs B HA 8.
Proof.
intros HA Hp8 (r & Hr & Hr8 & Hlo & Hhi). exists r. split; [exact Hr|]. split; [exact Hr8|]. split; [exact Hlo|].
pose proof (Z.div_mod HA 8 ltac:(lia)) as D1. pose proof (Z.div_mod (fst r) 8 ltac:(lia)) as D2.
rewrite Hp8, Z.add_0_r in D1. rewrite Hr8, Z.add_0_r in D2. lia.
Qed.
Lemma rd_entry_x : forall W ly S Hp regs mem md ch HA fd ev,
afn_pre_x SEGS B ARx RD_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 HA -> 0 < HA -> HA mod 8 = 0 -> azs B HA 8 -> HA + 8 <= kLowMemEnd ->
0 <= fd < 2 ^ 31 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (rd_extra fd ev))) ss_rd
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_relay_readsP) mem (seg_rom SEGS)))
/\ sh_ok SEGS rd_Bx rd_SH (Eimg (Ereg regs (rd_extra fd ev))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch HA fd ev HPRE H10 Hp0 Hp8 Hzs Hplo Rfd.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RD_STK = 32) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (rd_extra fd ev))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 HA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 fd) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (EG : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EC : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof RSAP as (D1 & D2 & D3 & D4 & D5 & D6). cbv zeta in D6. clear D1 D2 D3 D4 D5.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
split.
- unfold ss_rd, A_relay_readsP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold rd_regions, stack_region, got_regionP, bcell_regionP, RD_FRAME.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EG) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
[cbn [sv_denot]; rewrite EC, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) EC) by (pose proof (pa_val_range (A_OBJ 30)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 rd_Bx SB);
[cbn [sv_denot rd_Bx]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ apply pairwise_disjoint_of_extents. unfold rd_regions, stack_region, got_regionP, bcell_regionP, extent_of_region, RD_FRAME.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EG) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) EC) by (pose proof (pa_val_range (A_OBJ 30)); lia). cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgotR D6. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [rd_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold SB, kLowMemEnd in *; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
assert (H8 : 8 <= HA) by (pose proof (Z.div_mod HA 8 ltac:(lia)) as D; rewrite Hp8, Z.add_0_r in D; lia).
revert Hslo Hshi H47 Hceil Hp0 Hp8 H8 Hplo Hal16 C1 C3 WS Hstk0 Rfd. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, rd_SH. constructor; [|constructor].
assert (UBx : U E rd_Bx = SHADOW_OFF).
{ unfold U, rd_Bx. cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity. }
assert (Up : U E (SOff 10 0) = HA).
{ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold kLowMemEnd in *; lia). reflexivity. }
split; cbn [she_m she_lo she_hi].
+ rewrite UBx, Up, Z.add_0_r, Z.sub_0_r.
  exact (azs_range_addressable_x B ARx LAWS ly S Hp W mem md HA 8 HAR Hzs).
+ unfold app_apart. cbn [she_m she_lo she_hi]. rewrite UBx, Up. unfold SHADOW_OFF. unfold kLowMemEnd in Hplo. intros a Ha. lia.
Qed.
(* a byte whose memory cell is unchanged is kept (its view, and writable_at reads only that cell) *)
Lemma rd_kept_of_eq : forall (W : world SEGS) (m m' : word -> option byte) a,
  mrestrict (w_H W) m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a) -> abyte_kept W m W m' a.
Proof.
  intros W m m' a Heq. split; [apply aview_eq_of; exact Heq|].
  unfold arm, writable_at, wview. rewrite Heq. exact (fun H => H).
Qed.
Lemma rd_key_ptrs_len : forall ks, Z.of_nat (length (bzs (gestures_end_b_c.key_ptrs ks))) = 8 * Z.of_nat (length ks).
Proof.
intros ks. unfold bzs, gestures_end_b_c.key_ptrs. rewrite length_map.
induction ks as [|k ks IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, Mem.length_le8. cbn [length]. lia.
Qed.
(* every byte an entry's predicate reads lies in one of its blocks, and its blocks are live (lib/B/W_op_add.v
   oa_efp_in / oa_eblks_in, a working branch) *)
Lemma rd_efp_in : forall ly S (W : world SEGS) mem e, aentry_ok B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n.
Proof.
intros ly S W mem e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) r Hr a Ha.
unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | [<- | Hr]].
- revert Hr. destruct (Z.eqb_spec (re_cap e) 0) as [Hc | Hc]; intros Hr; [destruct Hr|].
  destruct Hr as [<- | []]. destruct H10 as [(Hc0 & _) | (Hcp & Hin & Hj & _)]; [lia|].
  exists (re_buf e), (re_cap e). split; [exact Hin|]. unfold gfp, bzs in Ha. cbn [fst snd] in Ha.
  rewrite length_map, length_app in Ha. unfold req_size. destruct (Z.eqb_spec (re_cap e) 0); lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. rewrite rd_key_ptrs_len in Ha.
  destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk8 & Hk1 & _)]; [rewrite Hk in Ha; cbn [length] in Ha; lia|].
  exists (re_hp e), (re_kh e). split; [exact Hin|]. unfold re_nheld in Hk8.
  unfold req_size. destruct (Z.eqb_spec (re_kh e) 0); lia.
- apply in_map_iff in Hr as (k & <- & Hk). rewrite Forall_forall in H15. destruct (H15 k Hk) as (Hin & _).
  exists (gestures_end_b_c.key_addr k), (Z.of_nat (length (gestures_end_b_c.key_text k)) + 1). split; [exact Hin|].
  unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
  unfold req_size. destruct (Z.eqb_spec (Z.of_nat (length (gestures_end_b_c.key_text k)) + 1) 0); lia.
Qed.
Lemma rd_eblks_in : forall ly S (W : world SEGS) mem e, aentry_ok B ly S W mem e ->
forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
intros ly S W mem e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) b Hb.
unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb]; [|apply in_app_or in Hb as [Hb | Hb]].
- revert Hb. destruct (Z.eqb_spec (re_cap e) 0) as [Hc | Hc]; intros Hb; [destruct Hb|].
  destruct Hb as [<- | []]. destruct H10 as [(Hc0 & _) | (_ & Hin & _)]; [lia | exact Hin].
- revert Hb. destruct (Z.eqb_spec (re_hp e) 0) as [Hc | Hc]; intros Hb; [destruct Hb|].
  destruct Hb as [<- | []]. destruct H12 as [(Hz & _) | (_ & Hin & _)]; [lia | exact Hin].
- apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in H15. exact (proj1 (H15 k Hk)).
Qed.
(* the relay, carried over a stretch that keeps every byte below alloc_ceiling (relay_reads writes only its frame
   before the call): its three globals are image bytes, its table and the entries' blocks are heap blocks *)
Lemma rd_relay_kept_x : forall ly S Hp (W : world SEGS) mem mem' md T es,
ARx ly S Hp W mem md -> arelay_at B RG ly S W mem T es ->
(forall a, 0 <= a < alloc_ceiling -> abyte_kept W mem W mem' a) ->
arelay_at B RG ly S W mem' T es.
Proof.
intros ly S Hp W mem mem' md T es HAR Hat HK.
pose proof (rs_rel_blk B RG ly S W mem T es Hat) as HT.
pose proof (rs_rel_ents B RG ly S W mem T es Hat) as HE. rewrite Forall_forall in HE.
pose proof asan_consts as (C1 & _).
assert (KB : forall b n a, In (b, n) (ablocks B ly S) -> b <= a < b + req_size n -> abyte_kept W mem W mem' a).
{ intros b n a Hb Ha.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b n HAR Hb) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & Hbpw).
  apply HK. lia. }
apply (arelay_at_kept B RG ly S W mem ly S W mem' T es Hat).
- intros r Hr x Hx. unfold arelay_fp in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Hx.
  + apply HK. rewrite <- HVsr in Hx. pose proof (pa_obj_img 5 ltac:(lia)) as HO. change (A_OBJ 5) with A_g_src in HO. lia.
  + apply HK. rewrite <- HVns in Hx. pose proof (pa_obj_img 4 ltac:(lia)) as HO. change (A_OBJ 4) with A_g_nsrc in HO. lia.
  + apply HK. lia.
  + apply (KB T ATABLE x HT). change (req_size ATABLE) with 896. unfold ATABLE in Hx. lia.
  + apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He).
    destruct (rd_efp_in ly S W mem e (HE e He) r Hr x Hx) as (b & n & Hb & Hbx). exact (KB b n x Hb Hbx).
- intros b Hb. destruct Hb as [<- | Hb]; [exact HT|].
  apply in_concat in Hb as (l & Hl & Hb). apply in_map_iff in Hl as (e & <- & He).
  exact (rd_eblks_in ly S W mem e (HE e He) b Hb).
Qed.
Theorem pb_relay_reads_x : rd_spec_x B PST ARx RG (BASE + AF_fr_relay_reads).
Proof.
intros W ly S Hp regs mem md ch T es HA h HPRE H10 Hp0 Hp8 Hzs HSRC HREL HROM.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : RD_STK = 32) by reflexivity.
assert (Hzs8 : azs B HA 8) by exact (rd_azs8 HA Hp8 Hzs).
(* s lies below kLowMemEnd: its zero-shadow range does (HSYM's asyms_ok, aso_zshadow) *)
assert (Hplo : HA + 8 <= kLowMemEnd).
{ destruct Hzs8 as (r & Hr & Hr8 & Hrlo & Hrhi).
  pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (HSYM ly S Hp W mem md HAR)) r Hr) as (Z1 & Z2 & Z3 & Z4 & Z5).
  assert (snd r / 8 * 8 <= snd r) by (pose proof (Z.mul_div_le (snd r) 8 ltac:(lia)); lia). lia. }
pose proof HSRC as (Mfd & _ & _ & _ & _ & _ & _ & _ & Rfd & _).
set (fd := hs_fd h) in *.
set (ev := rd_eofv fd es).
destruct (rd_entry_x W ly S Hp regs mem md ch HA fd ev HPRE H10 Hp0 Hp8 Hzs8 Hplo Rfd) as [HS SHOK].
assert (HJ : AJG RD_STK (spZ regs) [] ly S Hp W mem md [] ly S Hp W mem md 0)
by (apply ajournal_gx_nil_x; exact (ajournal_x_init SEGS B PST ARx RD_STK [] ly S Hp W regs mem md ch HPRE)).
remember (Eimg (Ereg regs (rd_extra fd ev))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 fd) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 ev) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (HAE : env_agree 32 (Ereg regs (rd_extra fd ev)) E) by (rewrite HE; split; [intros m0 Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_fr_relay_reads)) with (Z_to_bv 64 A_relay_readsP).
unfold A_relay_readsP, A_relay_reads.
paj_run_to_tok_x RUNTO HS HJ SHOK rd_Bspan (AF_fr_relay_reads + 52). { apply awr_ok_x_of0; rs_awr_any. exact Usp. }
(* 0x8651c: the two runtime cells are not read again, and s's first word becomes a region *)
assert (KEEPM0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RD_FRAME <= a < spZ regs) ->
  mrestrict (w_H W) (ms_mem ms) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)).
{ intros a Ha Hno. apply HFr. rewrite unsigned_lit_small by lia. rd_nowr. }
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RD_FRAME <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
by (intros a Ha Hno; apply aview_eq_of; apply KEEPM0; assumption).
assert (E10 : ew E 10 = Z_to_bv 64 HA) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (VB10 : base_val E (Some 10%nat) = HA)
by (cbn [base_val]; rewrite E10; apply unsigned_lit_small; unfold kLowMemEnd in Hplo; lia).
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
  let m := eval vm_compute in (ss_mem ss) in
  lazymatch m with ?r :: ?rs => apply (rd_keep1 _ _ _ r rs) in HS; [| reflexivity | vm_compute; reflexivity] end end.
cbn [ss_pc ss_regs ss_resv ss_facts] in HS.
apply (st_ok_pi_add_region E _ _ rd_sreg) in HS; [| reflexivity | | ].
2: { unfold region_ok, rd_sreg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict].
  rewrite VB10. split; [lia|]. split; [unfold kLowMemEnd in Hplo; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ HA 0 4 (SOff 32 0) fd);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  rewrite Z.add_0_r. unfold arm in Mfd. apply (val_mem_kept SEGS (w_H W) (w_H W) mem (ms_mem ms)); [|exact Mfd].
  intros k Hk. apply KEEP0; [unfold kLowMemEnd in Hplo; lia | unfold RD_FRAME; unfold kLowMemEnd in Hplo; lia]. }
2: { apply all_disjoint_of_extents. unfold rd_sreg, extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi map ss_mem].
  rewrite VB10. cbn [base_val]. rewrite Usp. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold kLowMemEnd in Hplo. lia. }
paj_run_to_tok_x RUNTO HS HJ SHOK rd_Bspan AF_fr_relay_source. { apply awr_ok_x_of0; rs_awr_any. exact Usp. }
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3.
prreg HS (4%bv : bv 5) R4. prreg HS (8%bv : bv 5) R8. prreg HS (10%bv : bv 5) R10.
assert (KEEPM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RD_FRAME <= a < spZ regs) ->
  mrestrict (w_H W) (ms_mem ms0) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)).
{ intros a Ha Hno. rewrite <- (KEEPM0 a Ha Hno). apply HFr0. rewrite unsigned_lit_small by lia. rd_nowr. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RD_FRAME <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a)
by (intros a Ha Hno; apply aview_eq_of; apply KEEPM1; assumption).
pose proof (rs_rel_blk B RG ly S W mem T es HREL) as HTin.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md T ATABLE HAR HTin) as (HT16 & HT4096 & HTceil & HTapp & HTpres & HTpw).
assert (Hreq : req_size ATABLE = 896) by reflexivity. rewrite Hreq in HTceil, HTapp.
(* relay_source's premises at the call: the relay and the ROM bytes are below alloc_ceiling, off this frame *)
assert (HREL1 : arelay_at B RG ly S W (ms_mem ms0) T es).
{ apply (rd_relay_kept_x ly S Hp W mem (ms_mem ms0) md T es HAR HREL).
  intros a Ha. apply rd_kept_of_eq. apply KEEPM1; [lia | unfold RD_FRAME; lia]. }
assert (ROM1 : rom_view SEGS W (ms_mem ms0)).
{ intros a Hrom.
  assert (Hi : in_img SEGS a) by (destruct Hrom as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
  pose proof (Hsegs a Hi) as Hlow. rewrite KEEP1; [apply HROM; exact Hrom | lia | unfold RD_FRAME; lia]. }
assert (Usp1 : spZ (ms_regs ms0) = spZ regs + (-16))
  by (unfold spZ; rewrite R2, Usp; apply unsigned_lit_small; unfold spZ in *; lia).
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
assert (HPREc : afn_pre_x SEGS B ARx RS_STK ly S Hp W (ms_regs ms0) (ms_mem ms0) mdc []).
{ pose proof HJ as HJaj. apply ajournal_gx_nil_x in HJaj.
  eapply (afn_pre_x_at SEGS B PST ARx RD_STK (spZ regs) [] ly S Hp W mem md [] ly S Hp W (ms_mem ms0) mdc 0 (ms_regs ms0)
    RS_STK (-16) [] HJaj Usp1); first
  [ reflexivity | lia | unfold RS_STK, RS_FRAME; lia | rewrite WS; unfold RS_STK, RS_FRAME; lia
  | rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | unfold raZ; rewrite R1, unsigned_lit_small by lia; lia
  | rewrite R3, (EE 3%nat 3%bv eq_refl); exact Hgp
  | rewrite R4, (EE 4%nat 4%bv eq_refl); exact Htp
  | apply achain_low; unfold s0Z; rewrite R8, E33, unsigned_lit_small by (unfold SB; lia); unfold SB; lia ]. }
(* 0x86520 jal relay_source: the callee's contract is pb_relay_source_x *)
eapply SRr_bind.
{ exact (pb_relay_source_x W ly S Hp (ms_regs ms0) (ms_mem ms0) mdc [] T es fd HPREc
    ltac:(rewrite R10, E32; reflexivity) ltac:(lia) HREL1 ROM1). }
cbv beta. intros W4 c4 Hwle4 HPOST.
unfold rs_post_x, aleafx_post_x in HPOST.
destruct HPOST as (regs4 & mem4 & md4 & -> & HJ4x & HP4 & HPR4 & HK4 & HF4).
rewrite Usp1 in HJ4x, HK4.
pose proof (ajournal_gx_sub_x SEGS B PST ARx LAWS pa_segs_low [] RD_STK (spZ regs) 0 [] [] ly S Hp W mem md [] ly S Hp W
  (ms_mem ms0) mdc 0 RS_STK (spZ regs + -16) 0 [] [] [] ly S Hp W4 mem4 md4 0 HJ HJ4x
  ltac:(rewrite WS; unfold RS_STK, RS_FRAME; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HGnil
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ5.
cbn [app] in HJ5. rewrite Z.add_0_r in HJ5.
pose proof HJ5 as HJ5a. apply ajournal_gx_nil_x in HJ5a.
destruct HJ5a as (HAR5 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & J13 & HPR5 & J15 & J16 & J17).
(* what both returns owe for the bytes outside this frame, given that the last run writes only [sp - 16, sp):
   presence, and view and writability (the frame stores, then relay_source's own post) *)
assert (TAIL : forall m' : word -> option byte,
  mem_grows (mrestrict (w_H W4) mem4) (mrestrict (w_H W4) m') ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RD_FRAME <= a < spZ regs) ->
     mrestrict (w_H W4) m' (Z_to_bv 64 a) = mrestrict (w_H W4) mem4 (Z_to_bv 64 a)) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W4) m' a) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RD_STK <= a < spZ regs) -> abyte_kept W mem W4 m' a)).
{ intros m' HGm KFm. split.
  - intros a Ha. eapply apresent_grows; [exact HGm|]. apply HPR4.
    eapply apresent_grows; [exact HG0|]. eapply apresent_grows; [exact HG|]. exact Ha.
  - intros a Ha Hno. rewrite WS in Hno.
    assert (Hno4 : ~ (spZ regs + -16 - RS_STK <= a < spZ regs + -16)) by (unfold RS_STK, RS_FRAME; lia).
    assert (Hno1 : ~ (spZ regs - RD_FRAME <= a < spZ regs)) by (unfold RD_FRAME; lia).
    pose proof (KFm a Ha Hno1) as K3.
    split.
    + transitivity (aview SEGS (w_H W4) mem4 a); [apply aview_eq_of; exact K3|].
      transitivity (aview SEGS (w_H W) (ms_mem ms0) a); [exact (proj1 (HK4 a Ha Hno4))|].
      exact (KEEP1 a Ha Hno1).
    + intros Hw. pose proof (rd_kept_of_eq W mem (ms_mem ms0) a (KEEPM1 a Ha Hno1)) as (_ & Hw0).
      pose proof (proj2 (HK4 a Ha Hno4) (Hw0 Hw)) as Hw4.
      unfold arm, writable_at, wview in Hw4 |- *. rewrite K3. exact Hw4. }
rewrite R1.
(* back in relay_reads at 0x86524: the saved ra / s0 lie outside relay_source's window [sp - 32, sp - 16) *)
jafter_call_keep_pi HS 35%nat regs4 (mrestrict (w_H W4) mem4) HP4 [1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp.
  - intros a Ha. apply (mbyte_of_aview SEGS). exact (proj1 (HK4 a ltac:(lia) ltac:(unfold RS_STK, RS_FRAME; lia))).
  - intros a Ha _. apply (apresent_writable SEGS). apply HPR5. rewrite WS. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 35 (map (getr regs4) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall n, (n < 35)%nat -> ew Ea n = ew E n) by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEa : env_agree 32 (Ereg regs (rd_extra fd ev)) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by lia; exact Usp).
prreg HS (10%bv : bv 5) A10.
assert (E33a : ew Ea 33 = Z_to_bv 64 SB) by (rewrite OLDa by lia; exact E33).
assert (HBxa : U Ea rd_Bx = SHADOW_OFF) by (unfold rd_Bx; rewrite (U_atom Ea 33 SB E33a) by (unfold SB; lia); reflexivity).
destruct HF4 as [(j & e & Hj & Hfd & Hfirst & Hr4) | (Hnone & Hz4)].
- (* found: relay_source returned r = T + 56 j, the first entry with s->fd *)
  pose proof (rs_rel_len B RG ly S W mem T es HREL) as Hle16.
  assert (Hjl : (j < length es)%nat) by (apply nth_error_Some; congruence).
  pose proof (rs_rel_ents B RG ly S W mem T es HREL) as HENT. rewrite Forall_forall in HENT.
  pose proof (HENT e (nth_error_In _ _ Hj)) as (He01 & _ & _ & _ & _).
  assert (Hev : ev = re_eof e) by exact (rd_eofv_first fd es j e Hj Hfd Hfirst).
  assert (Rev : 0 <= ev <= 1) by (rewrite Hev; lia).
  set (R := T + AENT * Z.of_nat j) in *.
  assert (HRb : 4096 <= R /\ R + 56 <= T + 896) by (unfold R, AENT; lia).
  assert (HR8 : R mod 8 = 0).
  { unfold R, AENT. pose proof (Z.div_mod T 16 ltac:(lia)) as D. rewrite HT16, Z.add_0_r in D. rewrite D.
    replace (16 * (T / 16) + 56 * Z.of_nat j) with ((2 * (T / 16) + 7 * Z.of_nat j) * 8) by ring. apply Z_mod_mult. }
  assert (E39 : ew Ea 39 = Z_to_bv 64 R) by (rewrite <- A10; exact Hr4).
  assert (VB39 : base_val Ea (Some 39%nat) = R) by (cbn [base_val]; rewrite E39; apply unsigned_lit_small; lia).
  (* r's eof field (bytes 4..7 of entry j), kept from the entry through the frame stores and relay_source *)
  assert (Mev : val_mem SEGS (mrestrict (w_H W4) mem4) (R + 4) 4 ev).
  { destruct (rs_rel_tab B RG ly S W mem T es HREL) as (tl & HTAB).
    assert (HPAD : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es /\
                   Forall (fun e => 0 <= re_eof e < 2 ^ 31) es).
    { split; rewrite Forall_forall; intros e' He'; destruct (HENT e' He') as (Q1 & _ & Q3 & Q4 & _); [split; assumption | lia]. }
    pose proof (rd_tbl_eof W mem T es tl j HTAB (proj1 HPAD) (proj2 HPAD) Hjl) as M0.
    assert (Ee : nth j es rs_e0 = e) by (apply nth_error_nth; exact Hj).
    rewrite Ee, <- Hev in M0. fold R in M0. unfold arm in M0.
    apply (val_mem_kept SEGS (w_H W) (w_H W4) mem mem4); [|exact M0].
    intros k Hk. rewrite (proj1 (HK4 (R + 4 + k) ltac:(lia) ltac:(unfold RS_STK, RS_FRAME; lia))).
    apply KEEP1; [lia | unfold RD_FRAME; lia]. }
  (* the engine learns r: 4096 <= r, 8 | r (0x86524 beqz and 0x8652c ALIGN8 decided); its eof word becomes a region;
     its granule's shadow is the table block's (0x86530-0x86540) *)
  apply (st_ok_pi_add_fact Ea _ _ 39%nat (mkAF 4096 RS_PHI 3)) in HS.
  2: { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E39, unsigned_lit_small by lia. change (2 ^ 3) with 8.
       unfold RS_PHI. lia. }
  apply (st_ok_pi_add_region Ea _ _ rd_eofr) in HS; [| reflexivity | | ].
  2: { unfold region_ok, rd_eofr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst].
    rewrite VB39. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS Ea _ R 4 4 (SOff 34 0) ev);
    [cbn [sv_denot]; rewrite OLDa by lia; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact Mev. }
  2: { apply all_disjoint_of_extents. unfold rd_eofr, extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi map ss_mem add_atom].
    rewrite VB39. cbn [base_val]. rewrite Uspa. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. lia. }
  assert (SHOKb : sh_ok SEGS rd_Bx [mkSHE 39 0 8] Ea (mrestrict (w_H W4) mem4)).
  { constructor; [|constructor].
    eapply shent_ok_of_range.
    + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S Hp W4 mem4 md4 T ATABLE R 8 HAR5 HTin); rewrite ?Hreq; unfold R, AENT; lia.
    + exact HBxa.
    + rewrite (U_atom Ea 39 R E39) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold R, AENT in Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  paj_run_tok_x RUN HS HJ5 SHOKb rd_Bspan. { apply awr_ok_x_of0; rs_awr_any. exact Uspa. }
  (* 0x86544 lw a0,4(r) ; seqz ; the epilogue restores ra and s0 from the frame ; 0x86558 ret *)
  prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (HAEb : env_agree 32 (Ereg regs (rd_extra fd ev)) Ev)
      by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAEa q Hq)
                 | rewrite ?ed_ewset; exact (proj2 HAEa)])
  end.
  pose proof (TAIL (ms_mem ms1) HG1 ltac:(intros a Ha Hno; apply HFr1; rewrite unsigned_lit_small by lia; rd_nowr))
    as (TPR & TKP).
  eapply (RET W4 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold aleafx_post_x.
  lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
  split; [cbn [ms_regs]; rewrite F1; rewrite ?OLDa by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|].
  split; [|split; [|split; [|split]]].
  + cbn [ms_mem]. apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs). exact HJ5.
  + lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ regs (rd_extra fd ev) HS); [exact HAEb | vm_compute; reflexivity] end.
  + exact TPR.
  + exact TKP.
  + cbn [ms_regs]. left. exists j, e. split; [exact Hj|]. split; [exact Hfd|]. split; [exact Hfirst|].
    rewrite F10. rewrite ?OLDa by lia. rewrite E34, Hev.
    destruct He01 as [Hq | Hq]; rewrite Hq; vm_compute; reflexivity.
- (* none: relay_source returned 0; 0x86524 beqz a0 goes to the epilogue with a0 = 0 *)
  assert (E39 : ew Ea 39 = Z_to_bv 64 0) by (rewrite <- A10; exact Hz4).
  assert (SHOKn : sh_ok SEGS rd_Bx [] Ea (mrestrict (w_H W4) mem4)) by (unfold sh_ok; constructor).
  psrr_branch_tok RUN BR HS SHOKn rd_Bspan.
  2: { exfalso. cbn [sv_denot] in Hc. rewrite ?E39 in Hc. vm_compute in Hc. discriminate. }
  paj_run_tok_x RUN HS HJ5 SHOKn rd_Bspan. { apply awr_ok_x_of0; rs_awr_any. exact Uspa. }
  prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
  pose proof (TAIL (ms_mem ms1) HG1 ltac:(intros a Ha Hno; apply HFr1; rewrite unsigned_lit_small by lia; rd_nowr))
    as (TPR & TKP).
  eapply (RET W4 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold aleafx_post_x.
  lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
  split; [cbn [ms_regs]; rewrite F1; rewrite ?OLDa by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|].
  split; [|split; [|split; [|split]]].
  + cbn [ms_mem]. apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs). exact HJ5.
  + eapply (aregs_preserved_of_st_ok SEGS _ Ea _ _ regs (rd_extra fd ev) HS); [exact HAEa | vm_compute; reflexivity].
  + exact TPR.
  + exact TKP.
  + cbn [ms_regs]. right. split; [exact Hnone|]. rewrite F10, E39. reflexivity.
Qed.
End w.

(* ---- THE LAWS AT ARi0 FROM AR_laws ALONE (Section cAR's laws).  YCbqG.v:1653 AR_laws_x_of_AR takes three facts beyond
   AR_laws; all three are theorems of cgif's AR, and lib/B carries no W_laws_x, so they are proved here as
   lib/A/W_laws_x.v (17dd7592e52) proves them for image A: rs_AR_stk8 (layout_ok's lo_top, AR's am_layout), rs_AR_tail
   (lib/A/W_alloc_tail.v alloc_tail, 53a00ba6fe3a: the chunk's extent is a multiple of 8, so a block's granule tail lies
   in chunk_junk's last range, which am_junk makes visible) and rs_AR_const (AR's am_const). ---- *)
Section laws.
Variable segs : list Segment.
Variable B : asyms.
Lemma rs_at_in_zseq : forall lo n a, lo <= a < lo + n -> In a (YG0n.zseq lo n).
Proof.
intros lo n a H. unfold YG0n.zseq. apply in_map_iff. exists (Z.to_nat (a - lo)). split.
- rewrite Z2Nat.id by lia. lia.
- apply in_seq. lia.
Qed.
Lemma rs_at_cls8 : forall c, 1 <= c <= 30 -> class_size c mod 8 = 0.
Proof.
intros c Hc.
assert (A : forallb (fun c => class_size c mod 8 =? 0) (YG0n.zseq 1 30) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in A. apply Z.eqb_eq. apply A. apply rs_at_in_zseq. lia.
Qed.
Lemma rs_at_ext8 : forall ly S k, YG0s.cfacts B ly S k -> ck_extent k mod 8 = 0.
Proof.
intros ly S k (_ & _ & _ & _ & _ & _ & _ & _ & G9).
destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct G9].
- cbv beta iota zeta in G9. destruct G9 as (Hc & _ & _ & He & _). rewrite He. apply rs_at_cls8. exact Hc.
- cbv beta iota in G9. destruct G9 as (_ & _ & _ & He & _). rewrite He. unfold sec_map_size, round_up, kPage.
  assert (E : forall q, (q * 4096 + 4096 - 4096) mod 8 = 0)
    by (intros q; replace (q * 4096 + 4096 - 4096) with (q * 512 * 8) by lia; apply Z.mod_mul; lia).
  apply E.
Qed.
Lemma rs_alloc_tail : forall ly S (W : world segs) mem md p n a,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview segs (w_H W) mem a <> None.
Proof.
intros ly S W mem md p n a HAR Hin Ha.
destruct HAR as (HM & _).
apply YG0s.In_ablocks in Hin as (k & Hk & Hst & Hu & Hr).
pose proof (YG0s.chunk_facts B ly S _ k HM Hk) as CF.
pose proof (rs_at_ext8 ly S k CF) as E8.
destruct CF as (_ & _ & G3 & G4 & _ & _ & _ & G8 & _).
assert (HJ : In (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k) (ajunk B ly S)).
{ unfold ajunk. right. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply in_flat_map. exists k. split; [exact Hk|]. unfold chunk_junk.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ HM) _ HJ) as V.
unfold range_vis in V. cbn [fst snd] in V.
rewrite aeval_aoff in V by (intros e' Ee; destruct (ck_beg k); cbn in Ee; discriminate Ee).
change (aeval B ly (sptr_exp (ck_beg k))) with (ck_base B ly k) in V.
unfold ck_n in V. rewrite <- Hu, G4, <- Hr in Ha.
pose proof (Z.div_mod (ck_base B ly k) 16 ltac:(lia)) as D1.
pose proof (Z.div_mod (ck_extent k) 8 ltac:(lia)) as D2.
pose proof (Z.div_mod (ck_base B ly k + ck_rz k + req_size (ck_req k) - 1) 8 ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound (ck_base B ly k + ck_rz k + req_size (ck_req k) - 1) 8 ltac:(lia)) as D4.
specialize (V (a - (ck_base B ly k + (ck_rz k + req_size (ck_req k))))).
replace (ck_base B ly k + (ck_rz k + req_size (ck_req k)) + (a - (ck_base B ly k + (ck_rz k + req_size (ck_req k)))))
  with a in V by lia.
apply V. lia.
Qed.
Lemma rs_AR_stk8 : forall ly S W mem md, AR segs B ly S W mem md -> ly_stk_lo ly mod 8 = 0 /\ ly_stk_hi ly mod 8 = 0.
Proof.
intros ly S W mem md (HM & _).
pose proof (lo_top _ (am_layout _ _ _ _ HM)) as (_ & _ & _ & _ & H1 & H2 & _).
unfold page_aligned in H1, H2. try unfold page_size in H1, H2.
assert (D : forall x, x mod 4096 = 0 -> x mod 8 = 0).
{ intros x Hx. apply Z.mod_divide in Hx; [|lia]. destruct Hx as [q ->].
  replace (q * 4096) with ((q * 512) * 8) by lia. apply Z_mod_mult. }
split; apply D; assumption.
Qed.
Lemma rs_AR_tail : forall ly S W mem md p n a, AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n <= a < (p + req_size n + 7) / 8 * 8 -> aview segs (w_H W) mem a <> None.
Proof.
intros ly S W mem md p n a HAR Hin Ha.
apply (rs_alloc_tail ly S W mem md p n a HAR Hin).
assert (E : (p + req_size n + 7) / 8 * 8 = p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8).
{ replace (p + req_size n + 7) with (p + req_size n - 1 + 1 * 8) by lia.
  rewrite Z.div_add by lia. pose proof (Z.div_mod (p + req_size n - 1) 8 ltac:(lia)). lia. }
lia.
Qed.
Lemma rs_AR_const : forall ly S W mem md, AR segs B ly S W mem md ->
Forall (cell_holds B ly (aview segs (w_H W) mem)) (as_const B ly).
Proof. intros ly S W mem md (HM & _). exact (am_const _ _ _ _ HM). Qed.
Lemma rs_laws_ARi0 : AR_laws segs B -> AR_laws_x segs B (ARi0 segs B) 0.
Proof. intros L. exact (AR_laws_x_ARi0 segs B (AR_laws_x_of_AR segs B L rs_AR_stk8 rs_AR_tail rs_AR_const)). Qed.
End laws.

(* ---- THE AR STATEMENTS, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_relay_source and pb_relay_reads keep
   their statements and their Section hypotheses (LAWS : AR_laws among them), now corollaries of the generic walks at
   ARx := W_journal_x.ARi0 (AR with the head set empty), PST := [].  The laws at ARi0 are rs_laws_ARi0 LAWS (so this
   Section needs no LX0, CONVERSION.md (sha256 1015972e02a9; internal record) 4.), HP0 is ARi0_hp0, HSYM is AR's am_syms; the pres go to ARi0 through
   W_journal_x.afn_pre_x_ARi0_of_AR, the posts come back through W_contract_x.aleafx_post_x_AR0. ---- *)
Section cAR.
Variable B : asyms.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HBgot : as_got_shadow B = VAL (A_OBJ 0).
Hypothesis HBcell : as_shadow_cell B = VAL (A_OBJ 30).
Hypothesis HVns : VAL A_g_nsrc = rg_nsrc RG.
Hypothesis HVsr : VAL A_g_src = rg_src RG.
Hypothesis RSAP : rs_objs_apart.
Theorem pb_relay_source : rs_spec B RG A_relay_sourceP.
Proof.
intros W ly S regs mem md ch T es fd HPRE H10 Hfd HREL HROM.
eapply SRr_mono.
{ exact (pb_relay_source_x B [] (ARi0 SEGS B) RG (rs_laws_ARi0 SEGS B LAWS) (ARi0_hp0 SEGS B) HBgot HBcell HVns HVsr RSAP
    W ly S [] regs mem md ch T es fd (afn_pre_x_ARi0_of_AR SEGS B RS_STK ly S W regs mem md ch HPRE) H10 Hfd HREL HROM). }
cbv beta. intros W2 c2 _ HQ. exact (aleafx_post_x_AR0 B RS_STK regs ly S [] W mem md (rs_found T fd es) W2 c2 HQ).
Qed.
Hypothesis HVcap : 0x10000 <= rg_capsrc RG /\ rg_capsrc RG + 4 <= 0x5fc000.
Theorem pb_relay_reads : rd_spec B RG (BASE + AF_fr_relay_reads).
Proof.
intros W ly S regs mem md ch T es HA h HPRE H10 Hp0 Hp8 Hzs HSRC HREL HROM.
assert (HSYM0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> asyms_ok B)
  by (intros ly0 S0 Hp' W0 mem0 md0 ((HM & _) & _); exact (am_syms _ _ _ _ HM)).
eapply SRr_mono.
{ exact (pb_relay_reads_x B [] (ARi0 SEGS B) RG (rs_laws_ARi0 SEGS B LAWS) (ARi0_hp0 SEGS B) HBgot HBcell HVns HVsr RSAP
    HVcap HSYM0 W ly S [] regs mem md ch T es HA h (afn_pre_x_ARi0_of_AR SEGS B RD_STK ly S W regs mem md ch HPRE)
    H10 Hp0 Hp8 Hzs HSRC HREL HROM). }
cbv beta. intros W2 c2 _ HQ. exact (aleafx_post_x_AR0 B RD_STK regs ly S [] W mem md _ W2 c2 HQ).
Qed.
End cAR.
End b.
End a.

(* rs_spec at B's pin IS W8Entry-2's RSRC (lib/B/W_LLVMFuzzerTestOneInput_cut.v:683, a987841a18c): the right-hand
   side is RSRC's text, with the cut's `segs` = pa_segs PB_fr, `fr_RG` = fr_globals_b and `RSRC_STK` = 16 written out *)
Section fr. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Lemma rs_spec_rsrc : forall B : asyms,
  rs_spec (PI := PB_fr) B fr_globals_b (fr_B0 + AF_fr_relay_source) <->
  (forall W ly S (regs : bvmap 5 word) mem md ch T es fd,
   afn_pre segs B 16 ly S W regs mem md ch ->
   getr regs 10 = w64 fd -> 0 <= fd < 2 ^ 32 ->
   arelay_at B fr_globals_b ly S W mem T es -> rom_view segs W mem ->
   SRr segs W (cfg_at segs (fr_B0 + AF_fr_relay_source) regs mem md)
     (aleafx_post B 16 regs ly S W mem md
       (fun a0 =>
          (exists j e, nth_error es j = Some e /\ re_fd e = fd /\
             (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> fd) /\
             a0 = w64 (T + AENT * Z.of_nat j)) \/
          ((forall e, In e es -> re_fd e <> fd) /\ a0 = w64 0)))).
Proof. intros B. split; intros H; exact H. Qed.
(* the placement hypotheses of pb_relay_source at B's pin PB_fr (lib/B/W_img.v) and fr_globals_b (lib/B/W_rep.v):
   GOT slot 0x9df50, cell 0xa6638, g_nsrc 0x5d8d20, g_src 0x5d8d40 *)
Lemma rs_objs_apart_fr : rs_objs_apart (PI := PB_fr).
Proof.
  unfold rs_objs_apart, A_g_nsrc, A_g_src. cbv zeta.
  assert (E0 : pa_val (PAImg := PB_fr) (A_OBJ 0) = 0x9df50) by (vm_compute; reflexivity).
  assert (E30 : pa_val (PAImg := PB_fr) (A_OBJ 30) = 0xa6638) by (vm_compute; reflexivity).
  assert (E4 : pa_val (PAImg := PB_fr) (A_OBJ 4) = 0x5d8d20) by (vm_compute; reflexivity).
  assert (E5 : pa_val (PAImg := PB_fr) (A_OBJ 5) = 0x5d8d40) by (vm_compute; reflexivity).
  rewrite E0, E30, E4, E5. lia.
Qed.
Lemma rs_nsrc_fr : pa_val (PAImg := PB_fr) A_g_nsrc = rg_nsrc fr_globals_b.
Proof. vm_compute. reflexivity. Qed.
Lemma rs_src_fr : pa_val (PAImg := PB_fr) A_g_src = rg_src fr_globals_b.
Proof. vm_compute. reflexivity. Qed.
(* pb_relay_source at B's pin: what W8Entry-2's RSRC asks for (rs_spec_rsrc), from the instance's laws and its two
   shadow cells (TfibB: as_got_shadow = 0x9df50, as_shadow_cell = 0xa6638, lib/B/YD2l.v) *)
Theorem pb_relay_source_fr : forall B : asyms, AR_laws segs B ->
  as_got_shadow B = 0x9df50 -> as_shadow_cell B = 0xa6638 ->
  rs_spec (PI := PB_fr) B fr_globals_b (fr_B0 + AF_fr_relay_source).
Proof.
  intros B LAWS Hg Hc.
  assert (Hg' : as_got_shadow B = pa_val (PAImg := PB_fr) (A_OBJ 0)) by (rewrite Hg; vm_compute; reflexivity).
  assert (Hc' : as_shadow_cell B = pa_val (PAImg := PB_fr) (A_OBJ 30)) by (rewrite Hc; vm_compute; reflexivity).
  assert (EB : fr_B0 + AF_fr_relay_source = A_relay_sourceP (PI := PB_fr)) by (vm_compute; reflexivity).
  rewrite EB.
  exact (pb_relay_source (PI := PB_fr) B fr_globals_b LAWS Hg' Hc' rs_nsrc_fr rs_src_fr rs_objs_apart_fr).
Qed.
(* rd_spec at B's pin IS W8Entry-2's RRDS (lib/B/W_LLVMFuzzerTestOneInput_cut.v:707, 61da015af91): the right-hand side
   is RRDS's text, with the cut's `segs` = pa_segs PB_fr, `fr_RG` = fr_globals_b and `RRDS_STK` = 16 + RSRC_STK = 16 + 16
   written out *)
Lemma rd_spec_rrds : forall B : asyms,
  rd_spec (PI := PB_fr) B fr_globals_b (fr_B0 + AF_fr_relay_reads) <->
  (forall W ly S (regs : bvmap 5 word) mem md ch T es HA h,
   afn_pre segs B (16 + 16) ly S W regs mem md ch ->
   getr regs 10 = w64 HA -> 0 < HA -> HA mod 8 = 0 -> azs B HA 4 ->
   asrc_at B ly S W mem HA h ->
   arelay_at B fr_globals_b ly S W mem T es -> rom_view segs W mem ->
   SRr segs W (cfg_at segs (fr_B0 + AF_fr_relay_reads) regs mem md)
     (aleafx_post B (16 + 16) regs ly S W mem md
       (fun a0 =>
          (exists j e, nth_error es j = Some e /\ re_fd e = hs_fd h /\
             (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> hs_fd h) /\
             a0 = w64 (if re_eof e =? 0 then 1 else 0)) \/
          ((forall e, In e es -> re_fd e <> hs_fd h) /\ a0 = w64 0)))).
Proof. intros B. split; intros H; exact H. Qed.
(* the placement hypothesis of pb_relay_reads at fr_globals_b: g_capsrc is 0x5d8d80 *)
Lemma rd_capsrc_fr : 0x10000 <= rg_capsrc fr_globals_b /\ rg_capsrc fr_globals_b + 4 <= 0x5fc000.
Proof. assert (E : rg_capsrc fr_globals_b = 0x5d8d80) by (vm_compute; reflexivity). rewrite E. lia. Qed.
(* pb_relay_reads at B's pin: what W8Entry-2's RRDS asks for (rd_spec_rrds), from the instance's laws and its two
   shadow cells, as pb_relay_source_fr.  BASE = fr_B0 at PB_fr (lib/B/W_img.v): EB below *)
Theorem pb_relay_reads_fr : forall B : asyms, AR_laws segs B ->
  as_got_shadow B = 0x9df50 -> as_shadow_cell B = 0xa6638 ->
  rd_spec (PI := PB_fr) B fr_globals_b (fr_B0 + AF_fr_relay_reads).
Proof.
  intros B LAWS Hg Hc.
  assert (Hg' : as_got_shadow B = pa_val (PAImg := PB_fr) (A_OBJ 0)) by (rewrite Hg; vm_compute; reflexivity).
  assert (Hc' : as_shadow_cell B = pa_val (PAImg := PB_fr) (A_OBJ 30)) by (rewrite Hc; vm_compute; reflexivity).
  assert (EB : fr_B0 + AF_fr_relay_reads = pa_val (PAImg := PB_fr) A_TEXT + AF_fr_relay_reads) by (vm_compute; reflexivity).
  rewrite EB.
  exact (pb_relay_reads (PI := PB_fr) B fr_globals_b LAWS Hg' Hc' rs_nsrc_fr rs_src_fr rs_objs_apart_fr rd_capsrc_fr).
Qed.
(* the generic walks at B's pin: what cut_x's RSRC_x / RRDS_x ask for (lib/B/W_LLVMFuzzerTestOneInput_cut_x.v :348 /
   :360, e43cf0c7bef) at any ARx with its laws and HP0 (and HSYM for relay_reads), from the instance's two shadow cells.
   The composition's ARX := ARcf /\ Hp = [] (lib/B/W_LLVMFuzzerTestOneInput_top_x.v:154, 1bf97df81de) gives the laws
   (ARX_laws), HP0 (its second projection) and HSYM (ARmcf's amc_syms, Reusable/YG0ncf.v:216). *)
Theorem pb_relay_source_x_fr : forall (B : asyms) (PST : list (Z * Z))
  (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop) (hl : Z),
  AR_laws_x segs B ARx hl -> (forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = []) ->
  as_got_shadow B = 0x9df50 -> as_shadow_cell B = 0xa6638 ->
  rs_spec_x (PI := PB_fr) B PST ARx fr_globals_b (fr_B0 + AF_fr_relay_source).
Proof.
  intros B PST ARx hl LAWS HP0 Hg Hc.
  assert (Hg' : as_got_shadow B = pa_val (PAImg := PB_fr) (A_OBJ 0)) by (rewrite Hg; vm_compute; reflexivity).
  assert (Hc' : as_shadow_cell B = pa_val (PAImg := PB_fr) (A_OBJ 30)) by (rewrite Hc; vm_compute; reflexivity).
  assert (EB : fr_B0 + AF_fr_relay_source = A_relay_sourceP (PI := PB_fr)) by (vm_compute; reflexivity).
  rewrite EB.
  exact (pb_relay_source_x (PI := PB_fr) B PST ARx fr_globals_b LAWS HP0 Hg' Hc' rs_nsrc_fr rs_src_fr rs_objs_apart_fr).
Qed.
Theorem pb_relay_reads_x_fr : forall (B : asyms) (PST : list (Z * Z))
  (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop) (hl : Z),
  AR_laws_x segs B ARx hl -> (forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = []) ->
  (forall ly S Hp W mem md, ARx ly S Hp W mem md -> asyms_ok B) ->
  as_got_shadow B = 0x9df50 -> as_shadow_cell B = 0xa6638 ->
  rd_spec_x (PI := PB_fr) B PST ARx fr_globals_b (fr_B0 + AF_fr_relay_reads).
Proof.
  intros B PST ARx hl LAWS HP0 HSYM Hg Hc.
  assert (Hg' : as_got_shadow B = pa_val (PAImg := PB_fr) (A_OBJ 0)) by (rewrite Hg; vm_compute; reflexivity).
  assert (Hc' : as_shadow_cell B = pa_val (PAImg := PB_fr) (A_OBJ 30)) by (rewrite Hc; vm_compute; reflexivity).
  assert (EB : fr_B0 + AF_fr_relay_reads = pa_val (PAImg := PB_fr) A_TEXT + AF_fr_relay_reads) by (vm_compute; reflexivity).
  rewrite EB.
  exact (pb_relay_reads_x (PI := PB_fr) B PST ARx fr_globals_b LAWS HP0 Hg' Hc' rs_nsrc_fr rs_src_fr rs_objs_apart_fr
    rd_capsrc_fr HSYM).
Qed.
End fr.
