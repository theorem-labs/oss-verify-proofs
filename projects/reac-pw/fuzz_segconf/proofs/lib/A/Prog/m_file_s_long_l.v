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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 808 of its 860 lines of code are new or changed and 401 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc), the first half of segment S_MF_LONGP (guide MF-CUTS-A.md
   section 4): LONG (0x86110) to LK_CALLP (0x861e4), the long line's blank-skip loop and its two exits.
   The LONGP blank-skip sub-lane of the LONGP / KKNOCKP segment lane (the G2 walk owner's G2). Base: commit c3fe5d4adfce.

   THE CODE (listing dis/m_file.fuzz_segconf.asan.s; listing offset = AF_m_file + (pc - 0x85ebc)):
     86110 bgeu s11,s7,861e0      not taken at LONG (s7 = p + |line|, |line| >= 512, so s11 = p < s7)
     86114 mv a0,s11
     86118 LK_LH: srli a1,a0,3 ; add a1,a1,s2 ; lb a2,0(a1) ; bnez a2,8614c   the check of *a0
     86128 lbu a2,0(s11) ; bltu s3,a2,863b4 ; srl a2,s9,a2 ; andi a2,a2,1 ; beqz a2,863b4
     8613c addi s11,s11,1 ; addi a0,a0,1 ; bne s11,s7,86118 ; j 861e0
     861e0 mv s4,a7                                     exit 1, every byte of the line blank
     863b4 lb a1,0(a1) ; bnez a1,86d30                  exit 2, the first non-blank byte
     863bc mv s4,a7 ; lbu a0,0(s11) ; addi a0,a0,-91 ; seqz a0,a0 ; addi a0,a0,-1 ; ld a1,136(s1) ; and a1,a0,a1
     863d8 sd a1,136(s1) ; j 861e4
   Both exits meet at LK_CALLP = 0x861e4 (m_file_s_long_d.v), where m_file_s_long.v takes over.

   THE PROOF. One small symbolic state per token run (fuzz_command's lib/A/Prog/answer_l.v form at
   origin/ossv/recipes 501c0d516c69: a loop re-seeded at each iteration, by strong induction on the bytes left):
   the registers are atoms (s3 and s9 pinned to the two constants the loop reads), two regions - the text byte at
   s11 = a0 = p + i (read only, atom 32 its value) and the cur slot 136(s1) (writable, atom 33 its value) - and no
   shadow entry, so each inline check leaves the obligation that the byte at a0 is addressable, which mf_loop's
   sa_addr p (|rest| + 1) discharges.  The loop-head statement lk_head_n carries the index i of the cursor inside
   the line, the fact that the bytes before i are blank, and the memory memL at the head, which agrees (rdW) with
   LONG's memc everywhere off the cur slot and whose cur slot holds cur; the two exits hand LK_CALLPX_stmt the same
   two facts, with cur' = cur (exit 1) or cur' = (byte = '[' ? None : cur) (exit 2).
   The model: m_line_long (the long-line equation of SegModel.m_line) and dropwhile_blank_idx (the blank prefix
   fixes dropwhile blank), plain lemmas copied from the plain / image-B owner's lib/Prog/mfp_facts.v at dec616e11c2f (cited at each
   one; that file is not in this tree and its Prog/mfu_facts dependency is not either, so mff_line_split is
   reproved here from break_nl).
   No Section hypothesis beyond the contract's B: every image fact the runs need is in mf_cx / mf_core / mf_loop. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegObj SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_s_long_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* 0x86118, the blank-skip loop's head *)
Definition LK_LH : Z := AF_m_file + 0x25c.

(* ================================ the model (plain lemmas) ================================ *)
(* The line is a prefix of the text left (plain mfp_facts.v:48-53 mff_line_split, reproved from break_nl: that
   file's proof goes through Prog/mfu_facts.v, which is not in this tree). *)
Lemma lk_line_split : forall l, exists R, l = fst (break_nl l) ++ R.
Proof.
  induction l as [|b r IH]; [exists []; reflexivity|].
  destruct IH as [R IH]. cbn [break_nl].
  destruct (b =? NL) eqn:E; [exists (b :: r); reflexivity|].
  destruct (break_nl r) as [l1 q] eqn:Er. cbn [fst] in IH |- *.
  exists R. cbn [app]. f_equal. exact IH.
Qed.
(* plain mfp_facts.v:54-58 mf_line_nth *)
Lemma lk_line_nth : forall rest i, (i < length (mf_line rest))%nat -> nth i rest 0 = nth i (mf_line rest) 0.
Proof.
  intros rest i Hi. destruct (lk_line_split rest) as [R E].
  transitivity (nth i (mf_line rest ++ R) 0); [unfold mf_line; rewrite <- E; reflexivity|].
  apply app_nth1. exact Hi.
Qed.
Lemma lk_line_le : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
  intros rest. destruct (lk_line_split rest) as [R E].
  assert (HL : length rest = (length (mf_line rest) + length R)%nat).
  { unfold mf_line. transitivity (length (fst (break_nl rest) ++ R));
    [rewrite <- E; reflexivity | apply length_app]. }
  lia.
Qed.
(* plain mfp_facts.v:117-129 dropwhile_blank_idx (its all_blank unfolded) *)
Lemma lk_dropwhile_blank_idx : forall u i, (i <= length u)%nat ->
  (forall k, (k < i)%nat -> blank (nth k u 0) = true) ->
  (i = length u \/ blank (nth i u 0) = false) -> dropwhile blank u = skipn i u.
Proof.
  induction u as [|x r IH]; intros i Hi Hb Hs; [destruct i; reflexivity|].
  cbn [dropwhile]. destruct i as [|i].
  - destruct Hs as [Hs|Hs]; [cbn [length] in Hs; discriminate|].
    change (blank x = false) in Hs. rewrite Hs. reflexivity.
  - assert (Hx : blank x = true) by exact (Hb 0%nat ltac:(lia)). rewrite Hx. cbn [skipn].
    cbn [length] in Hi. apply IH; [lia| |].
    + intros k Hk. exact (Hb (S k) ltac:(lia)).
    + destruct Hs as [Hs|Hs]; [left; cbn [length] in Hs; lia|right; exact Hs].
Qed.
(* plain mfp_facts.v:25-28 hd0_skipn *)
Lemma lk_hd0_skipn : forall (l : list Z) i, hd0 (skipn i l) = nth i l 0.
Proof.
  intros l; induction l as [|x r IH]; intros [|i]; cbn [skipn nth hd0]; try reflexivity. apply IH.
Qed.
(* plain mfp_facts.v:282-287 m_line_long *)
Lemma lk_m_line_long : forall c cur n l, (512 <= length l)%nat ->
  m_line (c, cur) n l = (m_refuse c n false, if hd0 (dropwhile blank l) =? LBR then None else cur).
Proof.
  intros c cur n l H. unfold m_line. cbv beta iota zeta.
  rewrite (proj2 (Nat.leb_le _ _) H). reflexivity.
Qed.
(* plain mfp_facts.v:13-17 blank_gt32 *)
Lemma lk_blank_gt32 : forall c, 32 < c -> blank c = false.
Proof.
  intros c H. unfold blank.
  rewrite (proj2 (Z.eqb_neq c 32)), (proj2 (Z.eqb_neq c 9)), (proj2 (Z.eqb_neq c 13)) by lia. reflexivity.
Qed.
(* the loop's shift-mask test is SegModel.blank (plain mfp_facts.v:18-24 blank_mask, in the code's form:
   MF_BLANK = 0x100002200 has exactly the bits 9, 13 and 32) *)
Lemma lk_mask_val : forall b, 0 <= b <= 32 -> Z.land (Z.shiftr 4294976000 b) 1 = (if blank b then 1 else 0).
Proof.
  intros b Hb.
  assert (E : exists n, b = Z.of_nat n /\ (n <= 32)%nat) by (exists (Z.to_nat b); split; lia).
  destruct E as [n [-> Hn]]. clear Hb.
  do 33 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

(* =============================== the symbolic state of one run =============================== *)
(* s3 = ' ' and s9 = MF_BLANK are the two constants the loop reads; every other register is its own atom.
   Atom 32 = the text byte at the cursor, atom 33 = the cur pointer in 136(s1). *)
Definition lk_regs : list sv := sr_set (sr_set sr_atoms 19%bv (SLit 32)) 25%bv (SLit 4294976000).
Definition lk_regions : smem :=
[ YP09.mkRegion (Some 27%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))];
  YP09.mkRegion (Some 9%nat) 136 144 136 144 [YP09.mkChunk 136 (CVal 8 (SOff 33 0))] ].
(* at LK_LH the shadow check reads a0, so a0 (atom 10) is a pointer too; at MF_LONG a0 is still dead *)
Definition lk_facts : facts :=
mkFacts [ (10%nat, PTR 0); (27%nat, PTR 0); (23%nat, PTR 0); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
          (32%nat, mkAF 0 255 0); (18%nat, mkAF SB SB 0) ] [] [].
Definition lk_facts0 : facts :=
mkFacts [ (27%nat, PTR 0); (23%nat, PTR 0); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
          (32%nat, mkAF 0 255 0); (18%nat, mkAF SB SB 0) ] [] [].
Definition lk_ss (pc : Z) (G : facts) : sstate := mkSS pc lk_regs lk_regions None G.
Definition lk_Bx : sv := SOff 18 0.
Definition lk_SH : list shent := [].
(* the registers an iteration does not touch and that are their own atoms (s3 and s9 are pinned literals, so they
   are read back with prreg) *)
Definition LK_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 17; 18; 21; 22; 23; 24; 26]%bv.
(* only the cur slot can be written *)
Definition lk_wins_ok (rs : smem) : bool :=
forallb (fun r => (YP09.r_whi r <=? YP09.r_wlo r) ||
  ((match YP09.r_base r with Some n => Nat.eqb n 9 | None => false end)
   && (136 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 144))) rs.

Lemma lk_stk : SegInstA.STK_m_file = 8560.
Proof. reflexivity. Qed.

Lemma lk_mod32 : forall x, (x - x mod 32) mod 32 = 0.
Proof.
  intros x. pose proof (Z.div_mod x 32 ltac:(lia)) as DM.
  replace (x - x mod 32) with (32 * (x / 32)) by lia.
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the environment of one run: the registers at the run's start, then the text byte and the cur pointer *)
Definition lk_E (regs1 : bvmap 5 word) (b curz : Z) : env := Eimg (Ereg regs1 [Z_to_bv 64 b; Z_to_bv 64 curz]).

Lemma lk_ew_reg : forall regs1 b curz n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (lk_E regs1 b curz) n = getr regs1 r.
Proof.
  intros regs1 b curz n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold lk_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma lk_ew32 : forall regs1 b curz, ew (lk_E regs1 b curz) 32 = Z_to_bv 64 b.
Proof. intros. unfold lk_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 0). Qed.
Lemma lk_ew33 : forall regs1 b curz, ew (lk_E regs1 b curz) 33 = Z_to_bv 64 curz.
Proof. intros. unfold lk_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 1). Qed.
Lemma lk_env_agree : forall regs1 b curz,
  env_agree 32 (Ereg regs1 [Z_to_bv 64 b; Z_to_bv 64 curz]) (lk_E regs1 b curz).
Proof.
  intros. split; [intros n Hn; unfold lk_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity].
Qed.
Lemma lk_ag32 : forall (regs1 : bvmap 5 word) extra E0 E,
  env_agree 32 (Ereg regs1 extra) E0 -> env_agree 34 E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.
Lemma lk_ag_ew : forall E0 E n v, env_agree 34 E0 E -> (n < 34)%nat -> ew E0 n = Z_to_bv 64 v -> ew E n = Z_to_bv 64 v.
Proof. intros E0 E n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
Lemma lk_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hv. reflexivity. Qed.
Lemma lk_u_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  U E (SOff n c) = v + c.
Proof. intros E n v c H Hv Hc. apply (U_atom_off E n v c H Hv Hc). Qed.

(* a one-byte reader fact as a region's chunk *)
Lemma lk_val_mem1 : forall (H : word -> bool) mem a v,
  aview SEGS H mem a = Some v -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
  intros H mem a v Hv. destruct (aview_byte SEGS H mem a v Hv) as (bb & Hb & Hvb & Hr).
  intros k Hk. destruct k as [|k]; [|exfalso; cbn [length] in Hk; lia].
  cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
  unfold YO0f.le_byte. replace (8 * Z.of_nat 1%nat) with 8 by (cbn; lia).
  replace (8 * Z.of_nat 0%nat) with 0 by (cbn; lia).
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
  rewrite Z.mod_mod by lia. rewrite (Z.mod_small v 256) by lia.
  rewrite Hvb. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* an 8-byte value only matters modulo 2 ^ 64 *)
Lemma lk_vm_mod : forall (m : word -> option byte) a v,
  val_mem SEGS m a 8 (v mod 2 ^ 64) <-> val_mem SEGS m a 8 v.
Proof.
  intros m a v.
  assert (E : forall k, YO0f.le_byte (v mod 2 ^ 64) 8 k = YO0f.le_byte v 8 k).
  { intros k. unfold YO0f.le_byte. replace (8 * Z.of_nat 8%nat) with 64 by (cbn; lia).
    rewrite Z.mod_mod by lia. reflexivity. }
  split; intros Hv k Hk; specialize (Hv k Hk).
  - rewrite (E k) in Hv. exact Hv.
  - rewrite (E k). exact Hv.
Qed.
(* the cur slot's value, read back from the state's second region *)
Lemma lk_slot_val : forall E ss ms (H : word -> bool) s1 e,
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  nth_error (ss_mem ss) 1 = Some (YP09.mkRegion (Some 9%nat) 136 144 136 144 [YP09.mkChunk 136 (CVal 8 e)]) ->
  bv_unsigned (ew E 9) = s1 ->
  val_mem SEGS (mrestrict H (ms_mem ms)) (s1 + 136) 8 (U E e mod 2 ^ 64).
Proof.
  intros E ss ms H s1 e HS Hn H9.
  pose proof (st_ok_pi_region_nth E ss (restrict H ms) 1 _ HS Hn) as Hr.
  cbn [ms_mem restrict] in Hr.
  pose proof (field_of_region_any E _ 9%nat s1 _ 136 144 136 144 136 8%N e Hr H9 (or_introl eq_refl)
    ltac:(cbn; lia)) as V.
  change (N.to_nat 8) with 8%nat in V. replace (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V by (cbn; lia). exact V.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* a run writes at most the cur slot *)
Lemma lk_keep_step : forall (Wc : world SEGS) E (rs : smem) s1 (m0 m m' : word -> option byte),
  frame_of E rs (mrestrict (w_H Wc) m) (mrestrict (w_H Wc) m') ->
  lk_wins_ok rs = true -> bv_unsigned (ew E 9) = s1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (s1 + 136 <= a < s1 + 144) -> rdW Wc m a = rdW Wc m0 a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (s1 + 136 <= a < s1 + 144) -> rdW Wc m' a = rdW Wc m0 a.
Proof.
  intros Wc E rs s1 m0 m m' HFr Hw H9 KM a Ha Hn.
  assert (HW : forall bb wlo whi a', In (bb, wlo, whi) (windows rs) ->
    base_val E bb + wlo <= a' < base_val E bb + whi -> s1 + 136 <= a' < s1 + 144).
  { intros bb wlo whi a' Hin Hr. unfold windows in Hin. apply in_map_iff in Hin.
    destruct Hin as (r & Hq & Hinr). injection Hq as <- <- <-.
    pose proof (proj1 (forallb_forall _ _) Hw r Hinr) as Hr'. cbn beta in Hr'.
    apply orb_true_iff in Hr'. destruct Hr' as [Hro | Hst].
    - apply Z.leb_le in Hro. lia.
    - apply andb_true_iff in Hst as [Hst Hhi]. apply andb_true_iff in Hst as [Hb9 Hlo].
      apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
      destruct (YP09.r_base r) as [n|] eqn:Eb; [|discriminate].
      apply Nat.eqb_eq in Hb9. subst n. cbn [base_val] in Hr. rewrite H9 in Hr. lia. }
  rewrite (kept_of_frame (segs := SEGS) E rs (w_H Wc) m m' (fun x => s1 + 136 <= x < s1 + 144) HFr HW a Ha Hn).
  exact (KM a Ha Hn).
Qed.
(* addressability moves with the memory: the cur slot is in the stack, far above the shadow of the text *)
Lemma lk_ra_move : forall (Wc : world SEGS) (m m' : word -> option byte) s1 q n,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (s1 + 136 <= a < s1 + 144) -> rdW Wc m' a = rdW Wc m a) ->
  alloc_ceiling <= s1 -> 0 <= q -> q + n <= alloc_ceiling ->
  range_addressable (rdW Wc m) SHADOW_OFF q n -> range_addressable (rdW Wc m') SHADOW_OFF q n.
Proof.
  intros Wc m m' s1 q n KEEP Hs1 Hq Hqn HRA.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply (range_addressable_agree (rdW Wc m) (rdW Wc m') SHADOW_OFF q n); [|exact HRA].
  intros x Hx. unfold shadow_of_addr.
  pose proof (Z.div_mod x 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as MB.
  apply KEEP; unfold SHADOW_OFF; lia.
Qed.

(* ========================== what one iteration knows about the state ========================== *)
Lemma lk_iter_facts : forall v lyc Sc Wc memc mdc pos mcc cur line p rest,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc ->
  mf_loop v Wc memc mcc cur line p rest ->
  4096 <= p /\ p + Z.of_nat (length rest) + 1 <= alloc_ceiling /\
  alloc_ceiling + 8560 <= mv_sp v /\ mv_sp v <= 2 ^ 47 /\
  mf_s1 (mv_sp v) mod 32 = 0 /\ mv_sp v - 319 <= mf_s1 (mv_sp v) <= mv_sp v - 288 /\
  range_addressable (rdW Wc memc) SHADOW_OFF p (Z.of_nat (length rest) + 1) /\
  sa_str (rdW Wc memc) p rest.
Proof.
  intros v lyc Sc Wc memc mdc pos mcc cur line p rest HCX HCORE HLOOP. unfold mv_sp.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMFP & _).
  pose proof HPRE as (HARe & _ & _ & _ & _ & Hstk & _ & _ & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & _ & _).
  pose proof HMFP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHEAP & _).
  pose proof HLOOP as (Hlen & _ & Hp & HSTR & HADDR & _).
  destruct HHEAP as (bb & mm & Hin & Hle1 & Hle2).
  destruct (al_blocks _ _ LAWS (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) bb mm HARe Hin)
    as (_ & H4096 & Hceilb & _).
  pose proof (req_size_pos mm ltac:(lia)) as (_ & Hrq).
  destruct HADDR as (_ & _ & _ & HRA & _).
  assert (HSTK : SegInstA.STK_m_file = 8560) by exact lk_stk.
  rewrite HSTK in Hslo.
  assert (Hplen : p + Z.of_nat (length rest) = mv_t v + Z.of_nat (length (mv_s v))) by (rewrite Hp; lia).
  pose proof (Z.mod_pos_bound (mv_sp v - 288) 32 ltac:(lia)) as HM32. unfold mv_sp in HM32.
  split; [rewrite Hp; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [unfold mf_s1; apply lk_mod32|].
  split; [unfold mf_s1; lia|].
  split; [exact HRA | exact HSTR].
Qed.

(* ======================================== the seed ======================================== *)
Lemma lk_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) (m : word -> option byte) pc G x e s1 b curz,
  getr regs1 19 = w64 0x20 -> getr regs1 25 = w64 MF_BLANK ->
  getr regs1 9 = w64 s1 -> getr regs1 27 = w64 x -> getr regs1 23 = w64 e ->
  4096 <= x -> x + 1 <= alloc_ceiling -> alloc_ceiling <= s1 -> s1 + 144 <= 2 ^ 47 ->
  0 <= b <= 255 -> 0 <= curz < 2 ^ 64 ->
  aview SEGS (w_H W) m x = Some b ->
  (forall o, 136 <= o < 144 -> apresent (w_H W) m (s1 + o)) ->
  val_mem SEGS (mrestrict (w_H W) m) (s1 + 136) 8 curz ->
  facts_ok (lk_E regs1 b curz) G ->
  st_ok_pi SEGS VAL (lk_E regs1 b curz) (lk_ss pc G)
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))).
Proof.
  intros W regs1 m pc G x e s1 b curz H19 H25 H9 H27 H23 Hx1 Hx2 Hs1 Hs2 Hb Hcz Hrd Hpres Hslot HG.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (E := lk_E regs1 b curz).
  assert (E9 : ew E 9 = Z_to_bv 64 s1) by (subst E; rewrite (lk_ew_reg regs1 b curz 9 9%bv eq_refl); exact H9).
  assert (E27 : ew E 27 = Z_to_bv 64 x) by (subst E; rewrite (lk_ew_reg regs1 b curz 27 27%bv eq_refl); exact H27).
  assert (E32 : ew E 32 = Z_to_bv 64 b) by (subst E; apply lk_ew32).
  assert (E33 : ew E 33 = Z_to_bv 64 curz) by (subst E; apply lk_ew33).
  assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew E 27) = x) by (rewrite E27; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold lk_ss. apply pa_entry_st_ok_full.
  - unfold lk_regs. apply regs_ok_pin;
    [ apply regs_ok_pin;
      [ subst E; unfold lk_E; apply regs_ok_Eimg_Ereg
      | intros X; discriminate X
      | cbn [sv_denot]; exact H19 ]
    | intros X; discriminate X
    | cbn [sv_denot]; exact H25 ].
  - vm_compute. reflexivity.
  - unfold lk_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ x 0 1%N (SOff 32 0) b);
      [ cbn [sv_denot]; rewrite E32, Z.add_0_r, unsigned_lit_small by lia; reflexivity
      | cbn; lia | cbn; lia | rewrite Z.add_0_r; change (N.to_nat 1) with 1%nat; apply lk_val_mem1; exact Hrd ].
    + rewrite U9. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ s1 136 8%N (SOff 33 0) curz);
      [ cbn [sv_denot]; rewrite E33, Z.add_0_r, unsigned_lit_small by lia; reflexivity
      | cbn; lia | cbn; lia | change (N.to_nat 8) with 8%nat; exact Hslot ].
  - apply pairwise_disjoint_of_extents. unfold lk_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U27.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - exact HG.
Qed.

Lemma lk_facts_lh : forall regs1 b curz x e s1,
  getr regs1 10 = w64 x -> getr regs1 27 = w64 x -> getr regs1 23 = w64 e ->
  getr regs1 9 = w64 s1 -> getr regs1 18 = w64 SHADOW_OFF ->
  4096 <= x <= 140737479966720 -> 4096 <= e <= 140737479966720 ->
  2 ^ 46 <= s1 <= 2 ^ 47 -> s1 mod 32 = 0 -> 0 <= b <= 255 ->
  facts_ok (lk_E regs1 b curz) lk_facts.
Proof.
  intros regs1 b curz x e s1 H10 H27 H23 H9 H18 Hx He Hs1 Hs1m Hb.
  set (E := lk_E regs1 b curz).
  assert (E10 : ew E 10 = Z_to_bv 64 x) by (subst E; rewrite (lk_ew_reg regs1 b curz 10 10%bv eq_refl); exact H10).
  assert (E27 : ew E 27 = Z_to_bv 64 x) by (subst E; rewrite (lk_ew_reg regs1 b curz 27 27%bv eq_refl); exact H27).
  assert (E23 : ew E 23 = Z_to_bv 64 e) by (subst E; rewrite (lk_ew_reg regs1 b curz 23 23%bv eq_refl); exact H23).
  assert (E9 : ew E 9 = Z_to_bv 64 s1) by (subst E; rewrite (lk_ew_reg regs1 b curz 9 9%bv eq_refl); exact H9).
  assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF)
    by (subst E; rewrite (lk_ew_reg regs1 b curz 18 18%bv eq_refl); exact H18).
  assert (E32 : ew E 32 = Z_to_bv 64 b) by (subst E; apply lk_ew32).
  split; [|split; [exact I | exact I]].
  cbn [lk_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite E10, E27, E23, E9, E18, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32. unfold SB, SHADOW_OFF.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.
Lemma lk_facts_long : forall regs1 b curz x e s1,
  getr regs1 27 = w64 x -> getr regs1 23 = w64 e ->
  getr regs1 9 = w64 s1 -> getr regs1 18 = w64 SHADOW_OFF ->
  4096 <= x <= 140737479966720 -> 4096 <= e <= 140737479966720 ->
  2 ^ 46 <= s1 <= 2 ^ 47 -> s1 mod 32 = 0 -> 0 <= b <= 255 ->
  facts_ok (lk_E regs1 b curz) lk_facts0.
Proof.
  intros regs1 b curz x e s1 H27 H23 H9 H18 Hx He Hs1 Hs1m Hb.
  set (E := lk_E regs1 b curz).
  assert (E27 : ew E 27 = Z_to_bv 64 x) by (subst E; rewrite (lk_ew_reg regs1 b curz 27 27%bv eq_refl); exact H27).
  assert (E23 : ew E 23 = Z_to_bv 64 e) by (subst E; rewrite (lk_ew_reg regs1 b curz 23 23%bv eq_refl); exact H23).
  assert (E9 : ew E 9 = Z_to_bv 64 s1) by (subst E; rewrite (lk_ew_reg regs1 b curz 9 9%bv eq_refl); exact H9).
  assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF)
    by (subst E; rewrite (lk_ew_reg regs1 b curz 18 18%bv eq_refl); exact H18).
  assert (E32 : ew E 32 = Z_to_bv 64 b) by (subst E; apply lk_ew32).
  split; [|split; [exact I | exact I]].
  cbn [lk_facts0 f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite E27, E23, E9, E18, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32. unfold SB, SHADOW_OFF.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ===================================== the loop statement ===================================== *)
(* LK_LH with the cursor at the byte i of the line: the bytes before i are blank, every register as at LONG
   except a0 = s11 = p + i, and the memory memL, which agrees with LONG's memc off the cur slot *)
Definition lk_head_n (n0 k : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc memL mdL pos (mcc : mconf) (cur : option nat) (line p : Z)
  (rest : list Z) (i : nat),
(length (mf_line rest) - i = k)%nat ->
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur ->
mf_regs_at B v lyc pos regs1 ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(length rest <= n0)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
(512 <= length (mf_line rest))%nat ->
mf_fin (m_line (mcc, cur) (line + 1) (mf_line rest)) line rest = mf_final v ->
(i < length (mf_line rest))%nat ->
(forall j, (j < i)%nat -> blank (nth j (mf_line rest) 0) = true) ->
getr regs1 27 = w64 (p + Z.of_nat i) -> getr regs1 10 = w64 (p + Z.of_nat i) ->
getr regs1 23 = w64 (p + Z.of_nat (length (mf_line rest))) ->
getr regs1 17 = w64 (mf_next p rest) -> getr regs1 22 = w64 (line + 1) -> getr regs1 21 = w64 (mv_c v) ->
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memL mdL 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 136 <= a < mf_s1 (mv_sp v) + 144) ->
 rdW Wc memL a = rdW Wc memc a) ->
val_mem SEGS (mrestrict (w_H Wc) memL) (mf_s1 (mv_sp v) + 136) 8 (mf_cur_ptr (mv_c v) cur) ->
mf_at B v Wc regs1 memL mdL LK_LH.

(* ---------------------------------- the tactics of a run ---------------------------------- *)
(* after a run: the environment still agrees with the seed's E0 below 34, and the memory with memc off the slot *)
Ltac lk_after E0 E9 HAE KM :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo ?rs (mrestrict _ _) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in
    assert (HAEn : env_agree 34 E0 En) by (env_agree_chain HAE);
    pose proof (lk_keep_step _ Eo rs _ _ _ _ HFr ltac:(vm_compute; reflexivity)
      ltac:(rewrite (lk_ag_ew _ _ 9%nat _ HAE ltac:(lia) E9); apply unsigned_lit_small; lia) KM) as KMn;
    clear HFr HAE KM; rename HAEn into HAE; rename KMn into KM;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
(* the writes a run may do: nothing in the text byte, the cur slot inside m_file's own stack window *)
Ltac lk_awr_tac HAE E9 dd :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 9%nat dd);
  [ reflexivity
  | rewrite (lk_ag_ew _ _ 9%nat _ HAE ltac:(lia) E9), unsigned_lit_small by lia; lia
  | cbn [YP09.r_wlo]; rewrite lk_stk; lia
  | cbn [YP09.r_whi]; lia
  | apply awr_ok_nil ].
(* the obligation of an inline check: the byte at a0 is addressable *)
Ltac lk_obl_tac HAE E18 E10 RAmove KM :=
  unfold lk_Bx;
  rewrite (U_atom _ 18%nat SHADOW_OFF (lk_ag_ew _ _ 18%nat _ HAE ltac:(lia) E18)
            ltac:(unfold SHADOW_OFF; lia));
  rewrite (U_atom _ 10%nat _ (lk_ag_ew _ _ 10%nat _ HAE ltac:(lia) E10) ltac:(lia));
  rewrite <- (aview_rd_of SEGS);
  apply RAmove; exact KM.
(* the kept registers and the two pinned ones at the end of a run *)
Ltac lk_kept HS HA0 HAE regs1 HK N19 N25 :=
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ LK_KEPT HS (lk_ag32 _ _ _ _ HA0 HAE)
    ltac:(vm_compute; reflexivity)) as HK;
  cbn [ms_regs restrict] in HK;
  prreg HS (19%bv : bv 5) N19; prreg HS (25%bv : bv 5) N25.
Ltac lk_hk HK r := rewrite (HK r ltac:(cbv [LK_KEPT In]; tauto)).
(* the cur slot at the end of a run: the chunk's value is read off the state first, so that no evar goes
   under the vm_compute of the nth_error side goal (an evar there makes the evaluation blow the memory up) *)
Ltac lk_slot HS HAE E9 s1v VS :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx _ =>
    let ee := eval vm_compute in
      (match nth_error (ss_mem ssx) 1 with
       | Some r => match YP09.r_chunks r with
                   | c :: _ => match YP09.c_val c with CVal _ x => x | _ => SLit 0 end
                   | nil => SLit 0
                   end
       | None => SLit 0
       end) in
    pose proof (lk_slot_val _ _ _ _ s1v ee HS ltac:(vm_compute; reflexivity)
      ltac:(rewrite (lk_ag_ew _ _ 9%nat _ HAE ltac:(lia) E9); apply unsigned_lit_small; lia)) as VS
  end.


(* the branch conditions of the loop, as arithmetic on the atoms *)
Lemma lk_br_ltu : forall E n v z bb, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SLit z)) (sv_denot E (SOff n 0)) = bb -> (z <? v) = bb.
Proof.
  intros E n v z bb H Hv Hz Hc. rewrite branch_ltu_U in Hc.
  rewrite (U_lit E z Hz), (U_atom E n v H Hv) in Hc. exact Hc.
Qed.
Lemma lk_br_eq0 : forall E (x : sv) w bb, U E x = w ->
  branch_taken BC_EQ (sv_denot E x) (sv_denot E (SLit 0)) = bb -> (w =? 0) = bb.
Proof.
  intros E x w bb Hw Hc. rewrite branch_eq_U in Hc. rewrite (U_lit E 0 ltac:(lia)), Hw in Hc. exact Hc.
Qed.
Lemma lk_br_ne : forall E n m v1 v2 c1 bb, ew E n = Z_to_bv 64 v1 -> ew E m = Z_to_bv 64 v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v1 + c1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n c1)) (sv_denot E (SOff m 0)) = bb -> negb (v1 + c1 =? v2) = bb.
Proof.
  intros E n m v1 v2 c1 bb Hn Hm Hv1 Hc1 Hv2 Hc. rewrite branch_ne_U in Hc.
  rewrite (U_atom_off E n v1 c1 Hn Hv1 Hc1), (U_atom E m v2 Hm Hv2) in Hc. exact Hc.
Qed.
Lemma lk_br_geu : forall E n m v1 v2 bb, ew E n = Z_to_bv 64 v1 -> ew E m = Z_to_bv 64 v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 ->
  branch_taken BC_GEU (sv_denot E (SOff n 0)) (sv_denot E (SOff m 0)) = bb -> negb (v1 <? v2) = bb.
Proof.
  intros E n m v1 v2 bb Hn Hm Hv1 Hv2 Hc. rewrite branch_geu_U in Hc.
  rewrite (U_atom E n v1 Hn Hv1), (U_atom E m v2 Hm Hv2) in Hc. exact Hc.
Qed.
(* the shift-mask test of 0x86130-0x86134 is SegModel.blank *)
Lemma lk_mask_U : forall E b, ew E 32 = Z_to_bv 64 b -> 0 <= b <= 32 ->
  U E (SAlu ALU_AND (SAlu ALU_SRL (SLit 4294976000) (SOff 32 0)) (SLit 1)) = (if blank b then 1 else 0).
Proof.
  intros E b Hb Hr. rewrite (U_and_lit E _ 1 ltac:(lia)), U_SAlu. cbn [zalu_raw].
  rewrite (U_lit E 4294976000 ltac:(lia)), (U_atom E 32 b Hb ltac:(lia)).
  assert (Ex : exists n, b = Z.of_nat n /\ (n <= 32)%nat) by (exists (Z.to_nat b); split; lia).
  destruct Ex as [n [-> Hn]]. clear Hr Hb.
  do 33 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.
(* the value the store of 0x863d8 writes: 0 when the byte is '[', the old cur pointer otherwise *)
Lemma lk_store_U : forall E b curz, ew E 32 = Z_to_bv 64 b -> ew E 33 = Z_to_bv 64 curz ->
  0 <= b <= 255 -> 0 <= curz < 2 ^ 64 ->
  U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 32 (-91)) (SLit 1)) (SLit (-1))) (SOff 33 0))
  = (if b =? LBR then 0 else curz).
Proof.
  intros E b curz H32 H33 Hb Hc.
  assert (U32 : U E (SOff 32 (-91)) = (b - 91) mod 2 ^ 64).
  { rewrite U_SOff, H32, unsigned_lit_small by lia. unfold zcanon, M64. f_equal; lia. }
  assert (U33 : U E (SOff 33 0) = curz) by (apply (U_atom E 33 curz H33); lia).
  assert (HU : U E (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 32 (-91)) (SLit 1)) (SLit (-1)))
             = (if b =? LBR then 0 else 2 ^ 64 - 1)).
  { rewrite !U_SAlu. cbn [zalu_raw]. rewrite U32, (U_lit E 1 ltac:(lia)), U_SLit.
    destruct (Z.eqb_spec b 91) as [->|Hne]; [vm_compute; reflexivity|].
    assert (Hlt : ((b - 91) mod 2 ^ 64 <? 1) = false).
    { apply Z.ltb_ge. pose proof (Z.mod_pos_bound (b - 91) (2 ^ 64) ltac:(lia)) as HB.
      assert (Hnz : (b - 91) mod 2 ^ 64 <> 0).
      { intros HE. apply Z.mod_divide in HE; [|lia]. destruct HE as [q Hq].
        change (2 ^ 64) with 18446744073709551616 in Hq. nia. }
      lia. }
    rewrite Hlt. vm_compute. reflexivity. }
  rewrite U_SAlu. cbn [zalu_raw]. rewrite HU, U33.
  destruct (Z.eqb_spec b 91) as [->|Hne].
  - rewrite Z.land_0_l. unfold zcanon, M64. apply Z.mod_0_l. lia.
  - rewrite Z.land_comm.
    replace (2 ^ 64 - 1) with (Z.ones 64) by (rewrite Z.ones_equiv; lia).
    rewrite Z.land_ones by lia.
    rewrite (Z.mod_small curz (2 ^ 64)) by lia. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

(* =================================== the two exits =================================== *)
(* exit 1 (0x861e0): every byte of the line is blank, so dropwhile blank gives [] and cur is kept *)
Lemma lk_exit1_close : forall n0, LK_CALLPX_stmt B n0 ->
  forall v lyc Sc Wc memc mdc pos mcc cur line p rest regs' memL' mdL',
  mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
  mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur ->
  (length rest <= n0)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
  (512 <= length (mf_line rest))%nat ->
  mf_fin (m_line (mcc, cur) (line + 1) (mf_line rest)) line rest = mf_final v ->
  (forall j, (j < length (mf_line rest))%nat -> blank (nth j (mf_line rest) 0) = true) ->
  mf_regs_at B v lyc pos regs' -> getr regs' 24 = w64 (frame_addr lyc 1 pos) ->
  getr regs' 20 = w64 (mf_next p rest) -> getr regs' 22 = w64 (line + 1) -> getr regs' 21 = w64 (mv_c v) ->
  ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memL' mdL' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 136 <= a < mf_s1 (mv_sp v) + 144) ->
   rdW Wc memL' a = rdW Wc memc a) ->
  val_mem SEGS (mrestrict (w_H Wc) memL') (mf_s1 (mv_sp v) + 136) 8 (mf_cur_ptr (mv_c v) cur) ->
  mf_at B v Wc regs' memL' mdL' LK_CALLP.
Proof.
  intros n0 HCALL v lyc Sc Wc memc mdc pos mcc cur line p rest regs' memL' mdL'
    HCX HLS HFRM HCORE HCELLS Hrn Hne HLOOP H512 HFIN HBL HREGS H24 H20 H22 H21 HJ KM VSLOT.
  assert (HDW : dropwhile blank (mf_line rest) = []).
  { rewrite (lk_dropwhile_blank_idx (mf_line rest) (length (mf_line rest)) ltac:(lia) HBL (or_introl eq_refl)).
    apply skipn_all. }
  rewrite (lk_m_line_long mcc cur (line + 1) (mf_line rest) H512), HDW in HFIN.
  cbn [hd0] in HFIN. change (0 =? LBR) with false in HFIN. cbn [andb] in HFIN.
  exact (HCALL v lyc Sc Wc regs' memc mdc pos mcc cur cur line p rest memL' mdL'
    HCX HLS HFRM HCORE HCELLS HREGS H24 Hrn Hne HLOOP H512 (or_introl eq_refl) HFIN H20 H22 H21 HJ KM VSLOT).
Qed.
(* exit 2 (0x863b4): the first non-blank byte b at the index i; cur' = NULL when b is '[' *)
Lemma lk_exit2_close : forall n0, LK_CALLPX_stmt B n0 ->
  forall v lyc Sc Wc memc mdc pos mcc cur line p rest i regs' memL' mdL' b,
  mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
  mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur ->
  (length rest <= n0)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
  (512 <= length (mf_line rest))%nat ->
  mf_fin (m_line (mcc, cur) (line + 1) (mf_line rest)) line rest = mf_final v ->
  (i < length (mf_line rest))%nat ->
  (forall j, (j < i)%nat -> blank (nth j (mf_line rest) 0) = true) ->
  b = nth i (mf_line rest) 0 -> blank b = false ->
  mf_regs_at B v lyc pos regs' -> getr regs' 24 = w64 (frame_addr lyc 1 pos) ->
  getr regs' 20 = w64 (mf_next p rest) -> getr regs' 22 = w64 (line + 1) -> getr regs' 21 = w64 (mv_c v) ->
  ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memL' mdL' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 136 <= a < mf_s1 (mv_sp v) + 144) ->
   rdW Wc memL' a = rdW Wc memc a) ->
  val_mem SEGS (mrestrict (w_H Wc) memL') (mf_s1 (mv_sp v) + 136) 8
    (mf_cur_ptr (mv_c v) (if b =? LBR then None else cur)) ->
  mf_at B v Wc regs' memL' mdL' LK_CALLP.
Proof.
  intros n0 HCALL v lyc Sc Wc memc mdc pos mcc cur line p rest i regs' memL' mdL' b
    HCX HLS HFRM HCORE HCELLS Hrn Hne HLOOP H512 HFIN Hi HBL Hbd Hnb HREGS H24 H20 H22 H21 HJ KM VSLOT.
  assert (HDW : dropwhile blank (mf_line rest) = skipn i (mf_line rest))
    by (apply (lk_dropwhile_blank_idx (mf_line rest) i ltac:(lia) HBL); right; rewrite <- Hbd; exact Hnb).
  rewrite (lk_m_line_long mcc cur (line + 1) (mf_line rest) H512), HDW, lk_hd0_skipn, <- Hbd in HFIN.
  exact (HCALL v lyc Sc Wc regs' memc mdc pos mcc cur (if b =? LBR then None else cur) line p rest memL' mdL'
    HCX HLS HFRM HCORE HCELLS HREGS H24 Hrn Hne HLOOP H512
    ltac:(destruct (b =? LBR); [right | left]; reflexivity) HFIN H20 H22 H21 HJ KM VSLOT).
Qed.

(* ============================ one iteration of the blank-skip loop ============================ *)
Lemma lk_step : forall n0, LK_CALLPX_stmt B n0 ->
  forall k, (forall j, (j < k)%nat -> lk_head_n n0 j) -> lk_head_n n0 k.
Proof.
intros n0 HCALL k IHk.
intros v lyc Sc Wc regs1 memc mdc memL mdL pos mcc cur line p rest i
  Hk HCX HLS HFRM HCORE HCELLS HREGS H24 Hrn Hne HLOOP H512 HFIN Hi HBLANKS
  H27 H10 H23 H17 H22 H21 HJ KMc VSLOT.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HP46 : (2:Z) ^ 46 = 70368744177664) by reflexivity.
assert (HP47 : (2:Z) ^ 47 = 140737488355328) by reflexivity.
assert (HP64 : (2:Z) ^ 64 = 18446744073709551616) by reflexivity.
destruct (lk_iter_facts v lyc Sc Wc memc mdc pos mcc cur line p rest HCX HCORE HLOOP)
  as (Hp4096 & Hpceil & Hsp1 & Hsp2 & Hs1m & Hs1b & HRA & HSTR).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof (lk_line_le rest) as HLle.
assert (Hnext : p <= mf_next p rest <= p + Z.of_nat (length rest)) by (unfold mf_next; lia).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresL & _ & _ & _).
remember (nth i (mf_line rest) 0) as b eqn:Hbd.
remember (mf_cur_ptr (mv_c v) cur mod 2 ^ 64) as curz eqn:Hcurz.
assert (Hbrd : rdW Wc memc (p + Z.of_nat i) = Some b).
{ destruct HSTR as [[HZS _] _]. rewrite Hbd, <- (lk_line_nth rest i Hi).
  replace (nth i rest 0) with (nth i (rest ++ [0]) 0) by (rewrite app_nth1 by lia; reflexivity).
  apply HZS. rewrite length_app. cbn [length]. lia. }
assert (HbrdL : rdW Wc memL (p + Z.of_nat i) = Some b)
  by (rewrite (KMc (p + Z.of_nat i) ltac:(lia) ltac:(lia)); exact Hbrd).
assert (Hbr : 0 <= b <= 255)
  by (destruct (aview_byte SEGS (w_H Wc) memc (p + Z.of_nat i) b Hbrd) as (_ & _ & _ & HB); lia).
assert (Hcz : 0 <= curz < 2 ^ 64) by (rewrite Hcurz; apply Z.mod_pos_bound; lia).
assert (VSLOTz : val_mem SEGS (mrestrict (w_H Wc) memL) (mf_s1 (mv_sp v) + 136) 8 curz).
{ rewrite Hcurz.
  exact (proj2 (lk_vm_mod (mrestrict (w_H Wc) memL) (mf_s1 (mv_sp v) + 136) (mf_cur_ptr (mv_c v) cur)) VSLOT). }
assert (Hpres136 : forall o, 136 <= o < 144 -> apresent (w_H Wc) memL (mf_s1 (mv_sp v) + o))
  by (intros o Ho; apply HpresL; rewrite lk_stk; lia).
pose proof (lk_facts_lh regs1 b curz (p + Z.of_nat i) (p + Z.of_nat (length (mf_line rest)))
  (mf_s1 (mv_sp v)) H10 H27 H23 R9 R18 ltac:(lia) ltac:(lia) ltac:(lia) Hs1m Hbr) as HG.
pose proof (lk_entry Wc regs1 memL LK_LH lk_facts (p + Z.of_nat i)
  (p + Z.of_nat (length (mf_line rest))) (mf_s1 (mv_sp v)) b curz
  R19 R25 R9 H27 H23 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hbr Hcz HbrdL Hpres136 VSLOTz HG) as HS.
assert (SHOK : sh_ok SEGS lk_Bx lk_SH (lk_E regs1 b curz) (mrestrict (w_H Wc) memL))
  by (unfold lk_SH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (lk_E regs1 b curz)) by (unfold lk_E; apply Eimg_env).
pose proof (lk_env_agree regs1 b curz) as HA0.
assert (E9 : ew (lk_E regs1 b curz) 9 = Z_to_bv 64 (mf_s1 (mv_sp v)))
  by (rewrite (lk_ew_reg regs1 b curz 9 9%bv eq_refl); exact R9).
assert (E10 : ew (lk_E regs1 b curz) 10 = Z_to_bv 64 (p + Z.of_nat i))
  by (rewrite (lk_ew_reg regs1 b curz 10 10%bv eq_refl); exact H10).
assert (E17 : ew (lk_E regs1 b curz) 17 = Z_to_bv 64 (mf_next p rest))
  by (rewrite (lk_ew_reg regs1 b curz 17 17%bv eq_refl); exact H17).
assert (E18 : ew (lk_E regs1 b curz) 18 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (lk_ew_reg regs1 b curz 18 18%bv eq_refl); exact R18).
assert (E23 : ew (lk_E regs1 b curz) 23 = Z_to_bv 64 (p + Z.of_nat (length (mf_line rest))))
  by (rewrite (lk_ew_reg regs1 b curz 23 23%bv eq_refl); exact H23).
assert (E27 : ew (lk_E regs1 b curz) 27 = Z_to_bv 64 (p + Z.of_nat i))
  by (rewrite (lk_ew_reg regs1 b curz 27 27%bv eq_refl); exact H27).
assert (E32 : ew (lk_E regs1 b curz) 32 = Z_to_bv 64 b) by (apply lk_ew32).
assert (E33 : ew (lk_E regs1 b curz) 33 = Z_to_bv 64 curz) by (apply lk_ew33).
assert (U9 : bv_unsigned (ew (lk_E regs1 b curz) 9) = mf_s1 (mv_sp v))
  by (rewrite E9; apply unsigned_lit_small; lia).
revert HS SHOK HEI HA0 E9 E10 E17 E18 E23 E27 E32 E33 U9.
generalize (lk_E regs1 b curz) as E0.
intros E0 HS SHOK HEI HA0 E9 E10 E17 E18 E23 E27 E32 E33 U9.
pose proof (env_agree_refl 34 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 136 <= a < mf_s1 (mv_sp v) + 144) ->
  rdW Wc memL a = rdW Wc memL a) by (intros; reflexivity).
assert (RAL : range_addressable (rdW Wc memL) SHADOW_OFF (p + Z.of_nat i) 1).
{ apply (lk_ra_move Wc memc memL (mf_s1 (mv_sp v)) (p + Z.of_nat i) 1 KMc ltac:(lia) ltac:(lia) ltac:(lia)).
  apply (range_addressable_sub _ _ p (Z.of_nat (length rest) + 1) (p + Z.of_nat i) 1 HRA); lia. }
assert (RAmove : forall (mm : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 136 <= a < mf_s1 (mv_sp v) + 144) ->
   rdW Wc mm a = rdW Wc memL a) ->
  range_addressable (rdW Wc mm) SHADOW_OFF (p + Z.of_nat i) 1).
{ intros mm Hmm.
  exact (lk_ra_move Wc memL mm (mf_s1 (mv_sp v)) (p + Z.of_nat i) 1 Hmm ltac:(lia) ltac:(lia) ltac:(lia) RAL). }
unfold mf_at.
(* 0x86118 .. 0x8612c: the inline check of *a0, the byte load, `bltu s3,a2` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lk_obl_tac HAE E18 E10 RAmove KM. }
{ lk_awr_tac HAE E9 (mf_s1 (mv_sp v) - mv_sp v). }
lk_after E0 E9 HAE KM.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* 32 < b: the byte is not blank, exit 2 *)
  assert (Hnb : blank b = false).
  { apply lk_blank_gt32. apply Z.ltb_lt.
    exact (lk_br_ltu _ 32%nat b 32 true (lk_ag_ew _ _ 32%nat _ HAE ltac:(lia) E32) ltac:(lia) ltac:(lia) Hc). }
  clear Hc.
  (* 0x863b4 .. 0x863dc: the re-check, cur' and the store, `j 861e4` *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan LK_CALLP.
  { lk_obl_tac HAE E18 E10 RAmove KM. }
  { lk_awr_tac HAE E9 (mf_s1 (mv_sp v) - mv_sp v). }
  lk_after E0 E9 HAE KM.
  lk_kept HS HA0 HAE regs1 HK N19 N25. prreg HS (20%bv : bv 5) N20.
  lk_slot HS HAE E9 (mf_s1 (mv_sp v)) VS.
  cbn [ms_mem restrict] in VS.
  rewrite (lk_store_U _ b curz (lk_ag_ew _ _ 32%nat _ HAE ltac:(lia) E32)
    (lk_ag_ew _ _ 33%nat _ HAE ltac:(lia) E33) Hbr Hcz) in VS.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
    refine (lk_exit2_close n0 HCALL v lyc Sc Wc memc mdc pos mcc cur line p rest i rg mm mdn b
      HCX HLS HFRM HCORE HCELLS Hrn Hne HLOOP H512 HFIN Hi HBLANKS Hbd Hnb _ _ _ _ _ HJ _ _) end.
  + unfold mf_regs_at. lk_hk HK (2%bv : bv 5). lk_hk HK (3%bv : bv 5). lk_hk HK (4%bv : bv 5). lk_hk HK (8%bv : bv 5). lk_hk HK (9%bv : bv 5).
    lk_hk HK (18%bv : bv 5). lk_hk HK (26%bv : bv 5). rewrite N19, N25.
    repeat split; try assumption; reflexivity.
  + lk_hk HK (24%bv : bv 5). exact H24.
  + rewrite N20, E17. reflexivity.
  + lk_hk HK (22%bv : bv 5). exact H22.
  + lk_hk HK (21%bv : bv 5). exact H21.
  + intros a Ha Hn. rewrite (KM a Ha Hn). exact (KMc a Ha Hn).
  + destruct (b =? LBR).
    * rewrite (Z.mod_0_l (2 ^ 64) ltac:(lia)) in VS. cbn [mf_cur_ptr]. exact VS.
    * rewrite (Z.mod_small curz (2 ^ 64)) in VS by lia.
         apply (proj1 (lk_vm_mod _ _ _)). rewrite <- Hcurz. exact VS.
- (* b <= 32: the shift-mask test of 0x86130 *)
  assert (Hb32 : b <= 32).
  { pose proof (lk_br_ltu _ 32%nat b 32 false (lk_ag_ew _ _ 32%nat _ HAE ltac:(lia) E32)
      ltac:(lia) ltac:(lia) Hc) as HB1. apply Z.ltb_ge in HB1. lia. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lk_awr_tac HAE E9 (mf_s1 (mv_sp v) - mv_sp v). }
  lk_after E0 E9 HAE KM.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* the mask bit is 0: the byte is not blank, exit 2 *)
    assert (Hnb : blank b = false).
    { pose proof (lk_br_eq0 _ _ _ true (lk_mask_U _ b (lk_ag_ew _ _ 32%nat _ HAE ltac:(lia) E32)
        ltac:(lia)) Hc) as HB2.
      destruct (blank b); [discriminate HB2 | reflexivity]. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan LK_CALLP.
    { lk_obl_tac HAE E18 E10 RAmove KM. }
    { lk_awr_tac HAE E9 (mf_s1 (mv_sp v) - mv_sp v). }
    lk_after E0 E9 HAE KM.
    lk_kept HS HA0 HAE regs1 HK N19 N25. prreg HS (20%bv : bv 5) N20.
    lk_slot HS HAE E9 (mf_s1 (mv_sp v)) VS.
    cbn [ms_mem restrict] in VS.
    rewrite (lk_store_U _ b curz (lk_ag_ew _ _ 32%nat _ HAE ltac:(lia) E32)
      (lk_ag_ew _ _ 33%nat _ HAE ltac:(lia) E33) Hbr Hcz) in VS.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
      refine (lk_exit2_close n0 HCALL v lyc Sc Wc memc mdc pos mcc cur line p rest i rg mm mdn b
        HCX HLS HFRM HCORE HCELLS Hrn Hne HLOOP H512 HFIN Hi HBLANKS Hbd Hnb _ _ _ _ _ HJ _ _) end.
    * unfold mf_regs_at. lk_hk HK (2%bv : bv 5). lk_hk HK (3%bv : bv 5). lk_hk HK (4%bv : bv 5). lk_hk HK (8%bv : bv 5). lk_hk HK (9%bv : bv 5).
      lk_hk HK (18%bv : bv 5). lk_hk HK (26%bv : bv 5). rewrite N19, N25.
      repeat split; try assumption; reflexivity.
    * lk_hk HK (24%bv : bv 5). exact H24.
    * rewrite N20, E17. reflexivity.
    * lk_hk HK (22%bv : bv 5). exact H22.
    * lk_hk HK (21%bv : bv 5). exact H21.
    * intros a Ha Hn. rewrite (KM a Ha Hn). exact (KMc a Ha Hn).
    * destruct (b =? LBR).
      -- rewrite (Z.mod_0_l (2 ^ 64) ltac:(lia)) in VS. cbn [mf_cur_ptr]. exact VS.
      -- rewrite (Z.mod_small curz (2 ^ 64)) in VS by lia.
         apply (proj1 (lk_vm_mod _ _ _)). rewrite <- Hcurz. exact VS.
  + (* the byte is blank: 0x8613c .. 0x86144, the cursor moves on *)
    assert (Hblk : blank b = true).
    { pose proof (lk_br_eq0 _ _ _ false (lk_mask_U _ b (lk_ag_ew _ _ 32%nat _ HAE ltac:(lia) E32)
        ltac:(lia)) Hc) as HB2.
      destruct (blank b); [reflexivity | discriminate HB2]. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK Bspan.
    { lk_awr_tac HAE E9 (mf_s1 (mv_sp v) - mv_sp v). }
    lk_after E0 E9 HAE KM.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* s11 + 1 <> s7: back to the head with the index i + 1 *)
      assert (Hlt1 : (i + 1 < length (mf_line rest))%nat).
      { pose proof (lk_br_ne _ 27%nat 23%nat (p + Z.of_nat i) (p + Z.of_nat (length (mf_line rest))) 1 true
          (lk_ag_ew _ _ 27%nat _ HAE ltac:(lia) E27) (lk_ag_ew _ _ 23%nat _ HAE ltac:(lia) E23)
          ltac:(lia) ltac:(lia) ltac:(lia) Hc) as HB3.
        apply negb_true_iff, Z.eqb_neq in HB3. lia. }
      clear Hc.
      assert (HBL1 : forall j, (j < i + 1)%nat -> blank (nth j (mf_line rest) 0) = true).
      { intros j Hj. destruct (Nat.eq_dec j i) as [->|Hj']; [rewrite <- Hbd; exact Hblk | apply HBLANKS; lia]. }
      (* 0x86144 `bne s11,s7` taken: back at the head *)
      paj_run_to_tok RUNTO HS HJ SHOK Bspan LK_LH.
      { lk_awr_tac HAE E9 (mf_s1 (mv_sp v) - mv_sp v). }
      lk_after E0 E9 HAE KM.
      lk_kept HS HA0 HAE regs1 HK N19 N25.
      prreg HS (27%bv : bv 5) N27. prreg HS (10%bv : bv 5) N10.
      lk_slot HS HAE E9 (mf_s1 (mv_sp v)) VS.
      cbn [ms_mem restrict] in VS.
      rewrite (U_atom _ 33%nat curz (lk_ag_ew _ _ 33%nat _ HAE ltac:(lia) E33) ltac:(lia)) in VS.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
        refine (IHk (length (mf_line rest) - (i + 1))%nat ltac:(lia)
          v lyc Sc Wc rg memc mdc mm mdn pos mcc cur line p rest (i + 1)%nat
          ltac:(lia) HCX HLS HFRM HCORE HCELLS _ _ Hrn Hne HLOOP H512 HFIN ltac:(lia) HBL1
          _ _ _ _ _ _ HJ _ _) end.
      -- unfold mf_regs_at. lk_hk HK (2%bv : bv 5). lk_hk HK (3%bv : bv 5). lk_hk HK (4%bv : bv 5). lk_hk HK (8%bv : bv 5). lk_hk HK (9%bv : bv 5).
         lk_hk HK (18%bv : bv 5). lk_hk HK (26%bv : bv 5). rewrite N19, N25.
         repeat split; try assumption; reflexivity.
      -- lk_hk HK (24%bv : bv 5). exact H24.
      -- rewrite N27, E27, unsigned_lit_small by lia. unfold w64. f_equal. lia.
      -- rewrite N10, E10, unsigned_lit_small by lia. unfold w64. f_equal. lia.
      -- lk_hk HK (23%bv : bv 5). exact H23.
      -- lk_hk HK (17%bv : bv 5). exact H17.
      -- lk_hk HK (22%bv : bv 5). exact H22.
      -- lk_hk HK (21%bv : bv 5). exact H21.
      -- intros a Ha Hn. rewrite (KM a Ha Hn). exact (KMc a Ha Hn).
      -- rewrite (Z.mod_small curz (2 ^ 64)) in VS by lia.
         apply (proj1 (lk_vm_mod _ _ _)). rewrite <- Hcurz. exact VS.
    * (* s11 + 1 = s7: the line is all blank, exit 1 *)
      assert (Heq1 : (i + 1 = length (mf_line rest))%nat).
      { pose proof (lk_br_ne _ 27%nat 23%nat (p + Z.of_nat i) (p + Z.of_nat (length (mf_line rest))) 1 false
          (lk_ag_ew _ _ 27%nat _ HAE ltac:(lia) E27) (lk_ag_ew _ _ 23%nat _ HAE ltac:(lia) E23)
          ltac:(lia) ltac:(lia) ltac:(lia) Hc) as HB3.
        apply negb_false_iff, Z.eqb_eq in HB3. lia. }
      clear Hc.
      assert (HBLall : forall j, (j < length (mf_line rest))%nat -> blank (nth j (mf_line rest) 0) = true).
      { intros j Hj. destruct (Nat.eq_dec j i) as [->|Hj']; [rewrite <- Hbd; exact Hblk | apply HBLANKS; lia]. }
      paj_run_to_tok RUNTO HS HJ SHOK Bspan LK_CALLP.
      { lk_awr_tac HAE E9 (mf_s1 (mv_sp v) - mv_sp v). }
      lk_after E0 E9 HAE KM.
      lk_kept HS HA0 HAE regs1 HK N19 N25. prreg HS (20%bv : bv 5) N20.
      lk_slot HS HAE E9 (mf_s1 (mv_sp v)) VS.
      cbn [ms_mem restrict] in VS.
      rewrite (U_atom _ 33%nat curz (lk_ag_ew _ _ 33%nat _ HAE ltac:(lia) E33) ltac:(lia)) in VS.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
        refine (lk_exit1_close n0 HCALL v lyc Sc Wc memc mdc pos mcc cur line p rest rg mm mdn
          HCX HLS HFRM HCORE HCELLS Hrn Hne HLOOP H512 HFIN HBLall _ _ _ _ _ HJ _ _) end.
      -- unfold mf_regs_at. lk_hk HK (2%bv : bv 5). lk_hk HK (3%bv : bv 5). lk_hk HK (4%bv : bv 5). lk_hk HK (8%bv : bv 5). lk_hk HK (9%bv : bv 5).
         lk_hk HK (18%bv : bv 5). lk_hk HK (26%bv : bv 5). rewrite N19, N25.
         repeat split; try assumption; reflexivity.
      -- lk_hk HK (24%bv : bv 5). exact H24.
      -- rewrite N20, E17. reflexivity.
      -- lk_hk HK (22%bv : bv 5). exact H22.
      -- lk_hk HK (21%bv : bv 5). exact H21.
      -- intros a Ha Hn. rewrite (KM a Ha Hn). exact (KMc a Ha Hn).
      -- rewrite (Z.mod_small curz (2 ^ 64)) in VS by lia.
         apply (proj1 (lk_vm_mod _ _ _)). rewrite <- Hcurz. exact VS.
Qed.

(* the loop head, by strong induction on the bytes of the line left *)
Lemma lk_head_ok : forall n0, LK_CALLPX_stmt B n0 -> forall k, lk_head_n n0 k.
Proof.
  intros n0 HCALL.
  assert (ALL : forall kk m, (m <= kk)%nat -> lk_head_n n0 m).
  { induction kk as [|kk IHkk]; intros m Hm.
    - apply (lk_step n0 HCALL m). intros m' Hm'. lia.
    - apply (lk_step n0 HCALL m). intros m' Hm'. apply (IHkk m'). lia. }
  intros k. exact (ALL k k (le_n k)).
Qed.

(* ===================== LONG (0x86110) -> the loop head, and the segment ===================== *)
Lemma lk_long : forall n, LK_CALLPX_stmt B n -> MF_LONG_stmt B n.
Proof.
intros n HCALL.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest
  HCX HLS HFRM HCORE HCELLS HREGS H24 Hrn Hne HLOOP H512 HFIN H27 H23 H17 H22 H21.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HP46 : (2:Z) ^ 46 = 70368744177664) by reflexivity.
assert (HP47 : (2:Z) ^ 47 = 140737488355328) by reflexivity.
assert (HP64 : (2:Z) ^ 64 = 18446744073709551616) by reflexivity.
destruct (lk_iter_facts v lyc Sc Wc memc mdc pos mcc cur line p rest HCX HCORE HLOOP)
  as (Hp4096 & Hpceil & Hsp1 & Hsp2 & Hs1m & Hs1b & HRA & HSTR).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof HCELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VSLOT & _).
pose proof (lk_line_le rest) as HLle.
pose proof HCORE as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresL & _ & _ & _).
remember (nth 0 (mf_line rest) 0) as b eqn:Hbd.
remember (mf_cur_ptr (mv_c v) cur mod 2 ^ 64) as curz eqn:Hcurz.
assert (Hbrd : rdW Wc memc p = Some b).
{ destruct HSTR as [[HZS _] _].
  pose proof (HZS 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as H0.
  cbn [Z.of_nat] in H0. rewrite Z.add_0_r in H0. rewrite app_nth1 in H0 by lia.
  rewrite Hbd, <- (lk_line_nth rest 0%nat ltac:(lia)). exact H0. }
assert (Hbr : 0 <= b <= 255)
  by (destruct (aview_byte SEGS (w_H Wc) memc p b Hbrd) as (_ & _ & _ & HB); lia).
assert (Hcz : 0 <= curz < 2 ^ 64) by (rewrite Hcurz; apply Z.mod_pos_bound; lia).
assert (VSLOTz : val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 136) 8 curz).
{ rewrite Hcurz.
  exact (proj2 (lk_vm_mod (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 136) (mf_cur_ptr (mv_c v) cur)) VSLOT). }
assert (Hpres136 : forall o, 136 <= o < 144 -> apresent (w_H Wc) memc (mf_s1 (mv_sp v) + o))
  by (intros o Ho; apply HpresL; rewrite lk_stk; lia).
pose proof (lk_facts_long regs1 b curz p (p + Z.of_nat (length (mf_line rest)))
  (mf_s1 (mv_sp v)) H27 H23 R9 R18 ltac:(lia) ltac:(lia) ltac:(lia) Hs1m Hbr) as HG.
pose proof (lk_entry Wc regs1 memc MF_LONG lk_facts0 p
  (p + Z.of_nat (length (mf_line rest))) (mf_s1 (mv_sp v)) b curz
  R19 R25 R9 H27 H23 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hbr Hcz Hbrd Hpres136 VSLOTz HG) as HS.
assert (SHOK : sh_ok SEGS lk_Bx lk_SH (lk_E regs1 b curz) (mrestrict (w_H Wc) memc))
  by (unfold lk_SH; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (lk_E regs1 b curz)) by (unfold lk_E; apply Eimg_env).
pose proof (lk_env_agree regs1 b curz) as HA0.
assert (E9 : ew (lk_E regs1 b curz) 9 = Z_to_bv 64 (mf_s1 (mv_sp v)))
  by (rewrite (lk_ew_reg regs1 b curz 9 9%bv eq_refl); exact R9).
assert (E23 : ew (lk_E regs1 b curz) 23 = Z_to_bv 64 (p + Z.of_nat (length (mf_line rest))))
  by (rewrite (lk_ew_reg regs1 b curz 23 23%bv eq_refl); exact H23).
assert (E27 : ew (lk_E regs1 b curz) 27 = Z_to_bv 64 p)
  by (rewrite (lk_ew_reg regs1 b curz 27 27%bv eq_refl); exact H27).
assert (E33 : ew (lk_E regs1 b curz) 33 = Z_to_bv 64 curz) by (apply lk_ew33).
revert HS SHOK HEI HA0 E9 E23 E27 E33.
generalize (lk_E regs1 b curz) as E0.
intros E0 HS SHOK HEI HA0 E9 E23 E27 E33.
pose proof (env_agree_refl 34 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 136 <= a < mf_s1 (mv_sp v) + 144) ->
  rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
unfold mf_at.
(* 0x86110: `bgeu s11,s7` is not taken, the line is at least 512 bytes long *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lk_awr_tac HAE E9 (mf_s1 (mv_sp v) - mv_sp v). }
lk_after E0 E9 HAE KM.
psrr_branch_tok RUN BR HS SHOK Bspan.
- exfalso.
  pose proof (lk_br_geu _ 27%nat 23%nat p (p + Z.of_nat (length (mf_line rest))) true
    (lk_ag_ew _ _ 27%nat _ HAE ltac:(lia) E27) (lk_ag_ew _ _ 23%nat _ HAE ltac:(lia) E23)
    ltac:(lia) ltac:(lia) Hc) as HB.
  apply negb_true_iff, Z.ltb_ge in HB. lia.
- clear Hc.
  (* 0x86114 `mv a0,s11`, then the head *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan LK_LH.
  { lk_awr_tac HAE E9 (mf_s1 (mv_sp v) - mv_sp v). }
  lk_after E0 E9 HAE KM.
  lk_kept HS HA0 HAE regs1 HK N19 N25.
  prreg HS (27%bv : bv 5) N27. prreg HS (10%bv : bv 5) N10.
  lk_slot HS HAE E9 (mf_s1 (mv_sp v)) VS.
  cbn [ms_mem restrict] in VS.
  rewrite (U_atom _ 33%nat curz (lk_ag_ew _ _ 33%nat _ HAE ltac:(lia) E33) ltac:(lia)) in VS.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
    refine (lk_head_ok n HCALL (length (mf_line rest) - 0)%nat
      v lyc Sc Wc rg memc mdc mm mdn pos mcc cur line p rest 0%nat
      eq_refl HCX HLS HFRM HCORE HCELLS _ _ Hrn Hne HLOOP H512 HFIN ltac:(lia) _ _ _ _ _ _ _ HJ _ _) end.
  + unfold mf_regs_at. lk_hk HK (2%bv : bv 5). lk_hk HK (3%bv : bv 5). lk_hk HK (4%bv : bv 5). lk_hk HK (8%bv : bv 5). lk_hk HK (9%bv : bv 5).
    lk_hk HK (18%bv : bv 5). lk_hk HK (26%bv : bv 5). rewrite N19, N25.
    repeat split; try assumption; reflexivity.
  + lk_hk HK (24%bv : bv 5). exact H24.
  + intros j Hj. lia.
  + rewrite N27, E27. unfold w64. f_equal. lia.
  + rewrite N10, E27. unfold w64. f_equal. lia.
  + lk_hk HK (23%bv : bv 5). exact H23.
  + lk_hk HK (17%bv : bv 5). exact H17.
  + lk_hk HK (22%bv : bv 5). exact H22.
  + lk_hk HK (21%bv : bv 5). exact H21.
  + intros a Ha Hn. exact (KM a Ha Hn).
  + rewrite (Z.mod_small curz (2 ^ 64)) in VS by lia.
         apply (proj1 (lk_vm_mod _ _ _)). rewrite <- Hcurz. exact VS.
Qed.


End e.
End f.
End d.
