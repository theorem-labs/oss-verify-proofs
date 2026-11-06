(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 76 of its 115 lines of code are new or changed and 414 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A: the shared vocabulary of segment A8b of reac_segconf_parse_file's
   walk (by the G3 walk owner), in the shape of plugin-hostd/fuzz_command's chain_words_d.v at origin/ossv/recipes
   501c0d516c69: the walk-internal cut JOIN, the seed every sub-walk starts from, and the small arithmetic
   facts about this call's realigned stack and about the reader's block that all four sub-walks use.
   proves no function (kind: statement text); the lane's rule-24 record is
   the unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md (reuse
   verdict: none, written new).

   THE CUT. NEW (0x8890c) and FOUND (0x88964) both reach 0x889b4, which this file cuts as PF_A8B_JOIN:
   FOUND's `bne a0,a1,0x889b4` arm jumps straight to it, and both NEW's `j 0x889b0` and the return of the
   F_twice refuse call reach it after the one `ld a3,0x38(s1)` of 0x889b0 (PF_A8B_J0). JOIN's own work is
   the seen_gen store (checks #38, #39) and the cur_name snprintf at 0x889f0, which is PROV2's cut pc.
   JOIN is taken at EVERY FP state (HA_A8B_JOIN): FOUND reaches it after a refuse call. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtFormat RtPFCmd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstA pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(** ** The walk-internal cut JOIN (0x889b4), and the listing offsets this segment names *)
(* 0x889b4 = 0x87a78 + 0xf3c: after FOUND's `bne` arm and after the `ld a3,0x38(s1)` of 0x889b0 *)
Definition PF_A8B_JOIN : Z := AF_reac_segconf_parse_file + 0xf3c.
(* 0x889b0: where NEW's `j` and refuse's return land *)
Definition PF_A8B_J0 : Z := AF_reac_segconf_parse_file + 0xf38.
(* the two call returns inside the segment *)
Definition PF_A8B_RET_MEMSET : Z := AF_reac_segconf_parse_file + 0xecc.   (* 0x88944 *)
Definition PF_A8B_RET_SNPN : Z := AF_reac_segconf_parse_file + 0xee4.     (* 0x8895c *)
Definition PF_A8B_RET_REFUSE : Z := AF_reac_segconf_parse_file + 0xf38.   (* 0x889b0 *)
Definition PF_A8B_RET_SNPC : Z := AF_reac_segconf_parse_file + 0xf7c.     (* 0x889f4 *)

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* No Section hypothesis here: a definition of this file must not pick one up, so that every sub-walk of the
   segment keeps its own callee list. Section c below adds only the ambient FP state. *)
Section c. Context {fx : YK11.FPState}.
(* JOIN (0x889b4): the shared tail of NEW and FOUND. c holds cf (the record after seg_get and, on FOUND's
   path, after the F_twice refusal), entry i is the header's, the name is still in buf at np, and a3 already
   holds the shadow address of c->gen (0x88974 on FOUND's `bne` arm, 0x889b0 otherwise). s8 and s3 are the
   loop's again (reloaded at 0x8892c / 0x88980 and 0x8895c / 0x88984).
   THE COUNTER BUDGET IS THE NEXT LINE'S, `length (skipn (pf_next (p_s v) o) (p_s v))`, as INV_PROV2's is,
   and NOT this line's: FOUND reaches JOIN after the F_twice refuse call, and SegModel.refuse always adds 1
   to rc_refused, so `pf_cnt cf (length (skipn o (p_s v)))` cannot be re-established there. With the next
   line's budget k' < k (pfA_facts: pf_next moves past the line) it can, on both of FOUND's arms and on
   NEW's path, where pf_cnt is simply monotone. Found by the FOUND sub-walk's proof, 2026-10-30 (fixed at commit
   d60ebb8b416c of this branch). This is a cut of THIS file, not of
   pf_pieces.v, so it is fixed here and no contract or segment statement changes. *)
Definition INV_A8B_JOIN (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (np : Z) (name : list Z) (i : nat) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn (pf_next (p_s v) o) (p_s v))) /\
  sa_str (rdW Wc memc) np name /\ pf_inb (pf_F v pos + PF_O_BUF) np name /\ (1 <= length name <= 15)%nat /\
  (i < length (rc_seg cf))%nat /\
  pf_rg rX ([(18, 0x23); (19, pf_SH v pos + 8); (24, p_c v); (27, pf_SH v pos);
             (20, seg_spec.rseg_addr (p_c v) i); (25, np);
             (13, shadow_addr (p_c v + seg_spec.RC_GEN))] ++ PF_RM v o ln).
Definition H_A8B_JOIN (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i,
  INV_A8B_JOIN n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_A8B_JOIN) rX memc mdc)
    (pf_postm B v (r_upd cf i (rs_with_gen (rc_gen cf)), Some i, snprintf_s 16 F_s [AS name]) o ln).
End c.
Definition HA_A8B_JOIN (n : nat) : Prop := forall f1 : YK11.FPState, H_A8B_JOIN (fx := f1) n.

(* ================================ the kit of this segment ================================ *)

(* the realigned locals base: 0x87a78 `addi sp,sp,-0x140` then 0x87ab8 `andi sp,sp,-0x20` *)
Lemma pfa8b_s1_val : forall v, spZ (p_regs v) mod 16 = 0 ->
  pf_s1 v = pf_sp0 v - 320 \/ pf_s1 v = pf_sp0 v - 336.
Proof.
intros v H16. unfold pf_s1, pf_sp0 in *. set (sp0 := spZ (p_regs v)) in *.
assert (E : (sp0 - 0x140) mod 32 = sp0 mod 32).
{ rewrite Zminus_mod. change (0x140 mod 32) with 0. rewrite Z.sub_0_r, Z.mod_mod by lia. reflexivity. }
rewrite E.
pose proof (Z.mod_pos_bound sp0 32 ltac:(lia)) as Hb.
pose proof (Z.div_mod sp0 32 ltac:(lia)) as Hd. pose proof (Z.div_mod sp0 16 ltac:(lia)) as Hd16.
assert (Hm : sp0 mod 32 = 0 \/ sp0 mod 32 = 16) by lia.
destruct Hm as [Hm|Hm]; rewrite Hm; [left | right]; lia.
Qed.
(* the offset of the call sp from the entry sp, and what the two stack premises of a call step need *)
Lemma pfa8b_o_ok : forall v, spZ (p_regs v) mod 16 = 0 ->
  (pf_s1 v - pf_sp0 v) mod 16 = 0 /\ pf_s1 v - pf_sp0 v <= 0 /\
  -336 <= pf_s1 v - pf_sp0 v.
Proof.
intros v H16. destruct (pfa8b_s1_val v H16) as [E|E]; rewrite E;
  (split; [replace (pf_sp0 v - 320 - pf_sp0 v) with (-320) by lia | idtac]);
  try (replace (pf_sp0 v - 336 - pf_sp0 v) with (-336) by lia); try reflexivity; lia.
Qed.

(* the address of c->seg[i].<field> stays inside the block, and inside parse_file's footprint *)
Lemma pfa8b_seg_in : forall c i off len, (i < 32)%nat -> 0 <= off -> 0 <= len -> off + len <= 356 ->
  c <= seg_spec.rseg_addr c i + off /\ seg_spec.rseg_addr c i + off + len <= c + seg_spec.RC_N.
Proof.
intros c i off len Hi Ho Hl Hol. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RC_N.
assert (Z.of_nat i <= 31) by lia. lia.
Qed.
Lemma pfa8b_fp_block : forall c a, c <= a -> a < c + seg_spec.RC_N + 4 -> inFP (seg_spec.RC_PARSE_W c) a.
Proof.
intros c a H1 H2. exists (c, c + seg_spec.RC_N + 4). split; [left; reflexivity | cbn [fst snd]; lia].
Qed.

(* the seed every sub-walk of this segment starts from: every register its own atom, no region, no fact *)
Definition pfa8b_ss (pcq : Z) : sstate := mkSS pcq sr_atoms [] None (mkFacts [] [] []).
Section sd. Context {fx : YK11.FPState}.
Lemma pfa8b_seed : forall (pcq : Z) (Wc : world SEGS) (rX : bvmap 5 word) (memc : word -> option byte),
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) (pfa8b_ss pcq)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pcq)) memc (seg_rom SEGS))).
Proof.
intros pcq Wc rX memc. rewrite restrict_mkst_fx. unfold pfa8b_ss. apply pa_entry_st_ok_full;
  [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto
  | split; [exact I | split; exact I]].
Qed.
End sd.
End e.
End f.
End d.
