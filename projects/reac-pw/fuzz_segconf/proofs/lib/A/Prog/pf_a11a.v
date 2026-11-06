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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a8b_d.v; 203 of its 258 lines of code are new or changed and 60 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a8b_k.v, with its module paths and module names changed; 66 of its 95 lines of code are new or changed and 229 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): segment A11a of reac_segconf_parse_file's walk,
   ASSEMBLED. pf_pieces.v states the segment as

     Definition S_A11a : Prop :=
       forall (f0 : YK11.FPState) (n : nat), HA_MISS n -> HA_LOWOUT n -> H_MODEL (fx := f0) B n.

   MODEL 0x8826c -> MISS 0x885a8 (reac_box_catalogue_by_token returned NULL) or LOWOUT 0x88774 (a hit);
   84 instructions, checks 18, 19, 26 and 27, one program call and two snprintf calls.
   Segment A11a's proof, by the G3 walk owner, 2026-10-30.

   THE FIVE PIECES, one file each, in the order the walk meets them (the cut points and the state at each
   are lib/A/Prog/pf_a11a_k.v):
     pf_a11a_e.v  a11a_model_ok  MODEL 0x8826c -> CHK: the three shadow stores that put low146 in scope
     pf_a11a_e.v  a11a_chk_ok    CHK 0x88278 -> LOOP 0 or ZST 0: check #18, val[0], s4 = low146
     pf_a11a_l.v  a11a_loop_ok   LOOP 0x8829c, the fold loop, by induction on 23 - li
     pf_a11a_m.v  a11a_zst_ok    ZST 0x8851c -> MISS or HIT: check #26, the NUL, the by_token call
     pf_a11a_h.v  a11a_hit_ok    HIT 0x88540 -> LOWOUT: two snprintf into the block and cur->model_set
   Each is stated at the ambient FP state, and that is enough: the only call before HIT is
   reac_box_catalogue_by_token, whose post is apost_base and so returns at the SAME FP state (its
   lib/A/Prog/reac_box_catalogue_by_token_c.v), and the two calls that do move the FP state are inside the
   last piece, which is why pf_pieces.v hands HA_MISS and HA_LOWOUT at EVERY FP state.

   WHAT THIS FILE ADDS: the spine step. Every piece carries the post `a11_post`, written as the match on
   by_token that the model branch of SegModel.r_key takes once the two strcasecmp results of H_MODEL are
   known; `a11_r_key_post` below turns it into H_MODEL's own post with pf_a11a_f.v's a11f_r_key (the port of
   the plain-build walk owner's pf_p7_lemmas.v p7_r_key at commit cfdd99183965).

   `a11a_compose` states the chaining with the five pieces as hypotheses (it was built first, to check the
   decomposition before the pieces were proved); `pf_a11a_holds` discharges all five with the theorems above.
   Each piece carries the cut's facts across its own writes with a transport stated at its own write set
   (pf_a11a_e.v a11e_base_scope, pf_a11a_l.v a11l_cx_move, pf_a11a_t.v a11m_cx for pf_a11a_m.v, pf_a11a_h.v
   a11h_base_move), all without a Section hypothesis; the image-free lemmas are pf_a11a_f.v, and the snprintf
   step is the stream's pf_a8b_t.v. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c reac_box_catalogue_by_token_c SegObj SegInstA pf_pieces pf_a11a_k pf_a11a_f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtFormat.
(* the five pieces *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require pf_a11a_e pf_a11a_l pf_a11a_m pf_a11a_h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* The post every cut of the segment carries is H_MODEL's own post: under the two strcasecmp results, the
   model branch of r_key IS the match on by_token that a11_step takes. *)
Lemma a11_r_key_post : forall (v : pfv) (cf : rconf) (gi : nat) (nm : list Z) (o : nat) (ln : Z)
  (kp vp : Z) (key val : list Z) (rd : reader) (pos : Z),
  pf_kv rd v pos (pf_tline (p_s v) o) kp vp key val ->
  strcasecmp key S_role <> 0 -> strcasecmp key S_model = 0 ->
  r_key cf (Some gi) nm (ln + 1) (pf_tline (p_s v) o) = a11_step cf gi nm val ln.
Proof.
intros v cf gi nm o ln kp vp key val rd pos (HSPL & _) Hrole Hmodel.
unfold a11_step. exact (a11f_r_key cf gi nm (pf_tline (p_s v) o) key val (ln + 1) HSPL Hrole Hmodel).
Qed.

(* The five pieces, each at the ambient FP state of its own statement. *)
Section g.
Hypothesis HIT : forall (f0 : YK11.FPState) (n : nat),
  HA_LOWOUT B n -> A11_HIT_stmt (fx := f0) B n.
Hypothesis ZST : forall (f0 : YK11.FPState) (n : nat),
  HA_MISS B n -> A11_HIT_stmt (fx := f0) B n -> forall li : nat, A11_ZST_stmt (fx := f0) B n li.
Hypothesis LOOP : forall (f0 : YK11.FPState) (n : nat),
  (forall j : nat, A11_ZST_stmt (fx := f0) B n j) -> forall li : nat, A11_LOOP_stmt (fx := f0) B n li.
Hypothesis CHK : forall (f0 : YK11.FPState) (n : nat),
  (forall j : nat, A11_ZST_stmt (fx := f0) B n j) -> A11_LOOP_stmt (fx := f0) B n 0%nat ->
  A11_CHK_stmt (fx := f0) B n.
Hypothesis MODEL : forall (f0 : YK11.FPState) (n : nat),
  A11_CHK_stmt (fx := f0) B n ->
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val,
  INV_KV (fx := f0) B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_MODEL) rX memc mdc) (a11_post (fx := f0) B v cf gi nm val o ln).

Theorem a11a_compose : S_A11a B.
Proof.
unfold S_A11a. intros f0 n HMISS HLOW.
assert (HH : A11_HIT_stmt (fx := f0) B n) by exact (HIT f0 n HLOW).
assert (HZ : forall j : nat, A11_ZST_stmt (fx := f0) B n j) by exact (ZST f0 n HMISS HH).
assert (HL : forall li : nat, A11_LOOP_stmt (fx := f0) B n li) by exact (LOOP f0 n HZ).
assert (HC : A11_CHK_stmt (fx := f0) B n) by exact (CHK f0 n HZ (HL 0%nat)).
unfold H_MODEL.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val HKV Hrole Hmodel.
pose proof HKV as (_ & _ & _ & HKVsplit & _).
rewrite (a11_r_key_post v cf gi nm o ln kp vp key val (rdW Wc memc) pos HKVsplit Hrole Hmodel).
exact (MODEL f0 n HC v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val HKV).
Qed.
End g.

(* The five pieces discharged. Between them they take exactly the callee texts pf_pieces.v's list names for
   A11a, at the listing's terms, each at every FP state, and two listing facts:
     BT    reac_box_catalogue_by_token_contract at BASE + AF_reac_box_catalogue_by_token,
           STK_reac_box_catalogue_by_token, RLO_A, RHI_A, catA (pf_pieces.v:686)       -- the ZST piece
     SIGP  seg_sig_prog: the call target pa_sigma SS_reac_box_catalogue_by_token
           is BASE + AF_reac_box_catalogue_by_token (SegObj.v)                         -- the ZST piece
     SNP   RtFormat.asnprintf_realizes at pa_sigma SS___interceptor_trampoline_snprintf,
           gotwA, guardA (pf_pieces.v:672-673)                                          -- the hit piece
     OBJ   seg_val_objs: the format literal's listing atom A_OBJ 35 is 0x21340 = seg_litA_rc F_s
           (SegObj.v)                                                                    -- the hit piece
   The entry and the loop take none. No SSPX, no VRO, no ROMV: A11a calls no refuse, and both of its calls
   carry an address keep clause in their post (reac_box_catalogue_by_token_c.v's sa_kept ... (fun _ => False);
   RtPFCmd.v:341-343 for snprintf) that reaches gotwA, guardA and RLO_A .. RHI_A. *)
Section h.
Hypothesis BT : forall fx0 : YK11.FPState,
  reac_box_catalogue_by_token_contract (fx := fx0) SEGS B
    (BASE + AF_reac_box_catalogue_by_token) STK_reac_box_catalogue_by_token RLO_A RHI_A catA.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis SNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (@pa_sigma _ seg_listing PI SS___interceptor_trampoline_snprintf)
    gotwA guardA.
Hypothesis OBJ : seg_val_objs (PI := PI).
(* the four pieces before HIT *)
Theorem a11a_of_hit :
  (forall (f0 : YK11.FPState) (n : nat), HA_LOWOUT B n -> A11_HIT_stmt (fx := f0) B n) -> S_A11a B.
Proof.
intros HIT. apply (a11a_compose HIT).
- intros f0 n HM HH li. exact (pf_a11a_m.a11a_zst_ok (fx := f0) B BT SIGP n HM HH li).
- intros f0 n HZ li. exact (pf_a11a_l.a11a_loop_ok (fx := f0) B n HZ li).
- intros f0 n HZ HL. exact (pf_a11a_e.a11a_chk_ok (fx := f0) B n HZ HL).
- intros f0 n HC. exact (pf_a11a_e.a11a_model_ok (fx := f0) B n HC).
Qed.
(* THE SEGMENT *)
Theorem pf_a11a_holds : S_A11a B.
Proof.
apply a11a_of_hit. intros f0 n HL. exact (pf_a11a_h.a11a_hit_ok B SNP OBJ (fx := f0) n HL).
Qed.
End h.
End e.
End f.
End d.
