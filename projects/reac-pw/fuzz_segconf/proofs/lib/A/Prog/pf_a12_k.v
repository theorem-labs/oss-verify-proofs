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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 302 of its 349 lines of code are new or changed and 406 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the KIT of segment A12 of reac_segconf_parse_file's
   walk, the ignore key (reac_segconf.c:271-280 with parse_bool R:88-99 inlined). The segment itself,
   [pf_a12_holds : S_A12 B] (lib/A/Prog/pf_pieces.v), is proved in lib/A/Prog/pf_a12.v: from the cut IGN
   (0x88364) the walk reaches RS3 (0x88100, the F_badignore refusal) or PROV2 (0x889f0, ignore = b and
   ignore_set = 1 stored, the ignore_file snprintf next). This file holds the pcs, the literals, the symbolic
   state and the seed [a12_seed] that opens the walk at any of A12's program points.

   The code (excerpt in the unit's internal record, commit dfb49d6ad789, path records/segp/dis/reac_segconf_parse_file.fuzz_segconf.asan.s;
   96 instructions, listing offsets from
   BASE + AF_reac_segconf_parse_file = 0x87a78):
     0x88364 .. 0x88370  strcasecmp(val = s9, "yes" 0x21b80); 0x88374 s7 = 1; 0x88378 beqz -> 0x888bc
     0x8837c .. 0x88388  strcasecmp(val, "true" 0x21ba0);     0x8838c beqz -> 0x888bc
     0x88390 .. 0x8839c  check #22 (load1 val[0]);            0x883a0 s3 = val[0]
     0x883a8 bne s3, '1' -> 0x883c8; 0x883ac .. 0x883bc check #23 (load1 val[1]); 0x883c0 a0 = val[1];
     0x883c4 beqz -> 0x888bc
     0x883c8 .. 0x883d4  strcasecmp(val, "no" 0x21bc0);       0x883d8 beqz -> 0x888b8
     0x883dc .. 0x883e8  strcasecmp(val, "false" 0x21be0);    0x883ec beqz -> 0x888b8
     0x883f4 bne s3, '0' -> 0x88414; 0x883f8 .. 0x88408 check #24 (load1 val[1]); 0x8840c a0 = val[1];
     0x88410 beqz -> 0x888b8
     0x88414 .. 0x8842c  refuse(c, lineno, F_badignore 0x21900, cur_name, val);   0x88430 j RS3
     0x888b8 s7 = 0; 0x888bc .. 0x888cc check #33 (store4); 0x888d0 cur->ignore = s7
     0x888d4 .. 0x888e8 check #34 (store4), s3 reloaded from slot 0x98; 0x888f0 cur->ignore_set = 1
     0x888f4 .. 0x88904 a0 = &cur->ignore_file, a1 = 0x60, a2 = "%s" 0x21340, a3 = c->reading (slot 0x58);
     0x88908 j PROV2
   The five slow blocks of the checks (0x88af4, 0x88b04, 0x88b14, 0x88b58, 0x88b9c) and the five error arms
   (0x88d60, 0x88d64, 0x88d68, 0x88d84, 0x88da0) are decided by the token executor from the SH entries below.

   The form is this unit's own image-A walk form (lib/A/Prog/trim_t.v's tf_entry and trim_s.v's ta_after, over
   plugin-hostd/fuzz_command's released shape at origin/ossv/recipes 501c0d516c69): a symbolic state over the
   position-abstract listing whose region bases are the REGISTER atoms the code addresses through (s1 = atom 9
   for the spill slots, s9 = atom 25 for the value in buf, s4 = atom 20 for &c->seg[gi], s6 = atom 22 for the
   shadow base), seeded from the cut predicate INV_KV and run by the token executor.
   Segment A12's proof, by the G3 walk owner, 2026-10-30. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
pf_pieces pf_a12_pure.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require pf_a5_k.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(** ** The fold of the strcasecmp interceptor is SegModel's *)
Lemma a12_lc_tolower : forall c, 0 <= c < 256 -> RtSeg.lc c = tolower c.
Proof.
  intros c _. unfold RtSeg.lc. rewrite tolower_lower. unfold lower.
  destruct ((65 <=? c) && (c <=? 90)); [lia | reflexivity].
Qed.

Lemma a12_bvu64 : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8).
Proof. intros w. exact (bv_unsigned_in_range 64 w). Qed.

(** ** The listing offsets of the cuts and call sites of A12 (BASE + AF_reac_segconf_parse_file = 0x87a78) *)
Definition A12_SC1 : Z := AF_reac_segconf_parse_file + 0x8f8.      (* 0x88370 jal strcasecmp "yes" *)
Definition A12_SC2 : Z := AF_reac_segconf_parse_file + 0x910.      (* 0x88388 jal strcasecmp "true" *)
Definition A12_SC3 : Z := AF_reac_segconf_parse_file + 0x95c.      (* 0x883d4 jal strcasecmp "no" *)
Definition A12_SC4 : Z := AF_reac_segconf_parse_file + 0x970.      (* 0x883e8 jal strcasecmp "false" *)
Definition A12_REF : Z := AF_reac_segconf_parse_file + 0x9b4.      (* 0x8842c jal refuse *)
Definition A12_RET1 : Z := AF_reac_segconf_parse_file + 0x8fc.     (* 0x88374 *)
Definition A12_RET2 : Z := AF_reac_segconf_parse_file + 0x914.     (* 0x8838c *)
Definition A12_RET3 : Z := AF_reac_segconf_parse_file + 0x960.     (* 0x883d8 *)
Definition A12_RET4 : Z := AF_reac_segconf_parse_file + 0x974.     (* 0x883ec *)
Definition A12_RETR : Z := AF_reac_segconf_parse_file + 0x9b8.     (* 0x88430 j RS3 *)
Definition A12_B1 : Z := AF_reac_segconf_parse_file + 0x934.       (* 0x883ac, val[0] = '1' *)
Definition A12_B0 : Z := AF_reac_segconf_parse_file + 0x980.       (* 0x883f8, val[0] = '0' *)
Definition A12_ST0 : Z := AF_reac_segconf_parse_file + 0xe40.      (* 0x888b8 li s7, 0; the false stores *)
Definition A12_ST : Z := AF_reac_segconf_parse_file + 0xe44.       (* 0x888bc the two stores, s7 = b *)
Definition A12_REFS : Z := AF_reac_segconf_parse_file + 0x99c.     (* 0x88414 the refuse call's set-up *)
Definition A12_NO : Z := AF_reac_segconf_parse_file + 0x950.       (* 0x883c8 a1 = "no", the third call *)

(** ** The object atoms of the literals A12 names (SegAddr.v seg_objs; VAL (A_OBJ i) by seg_val_objs) *)
Definition A12_O_S : nat := 35%nat.         (* 0x21340 "%s" *)
Definition A12_O_YES : nat := 50%nat.       (* 0x21b80 *)
Definition A12_O_TRUE : nat := 51%nat.      (* 0x21ba0 *)
Definition A12_O_NO : nat := 52%nat.        (* 0x21bc0 *)
Definition A12_O_FALSE : nat := 53%nat.     (* 0x21be0 *)
Definition A12_O_BADIGN : nat := 54%nat.    (* 0x21900 *)

(** ** The literal addresses at image A (SegInstA.v's map, by computation) *)
Lemma a12_lit_yes : seg_litA_rc S_yes = 0x21b80. Proof. vm_compute. reflexivity. Qed.
Lemma a12_lit_true : seg_litA_rc S_true = 0x21ba0. Proof. vm_compute. reflexivity. Qed.
Lemma a12_lit_no : seg_litA_rc S_no = 0x21bc0. Proof. vm_compute. reflexivity. Qed.
Lemma a12_lit_false : seg_litA_rc S_false = 0x21be0. Proof. vm_compute. reflexivity. Qed.
Lemma a12_lit_badignore : seg_litA_rc F_badignore = 0x21900. Proof. vm_compute. reflexivity. Qed.
Lemma a12_lit_s : seg_litA_rc F_s = 0x21340. Proof. vm_compute. reflexivity. Qed.

(** ** The four literals are byte strings *)
Lemma a12_vals_yes : a12_byte_vals S_yes. Proof. apply a12_bv_lit. vm_compute. reflexivity. Qed.
Lemma a12_vals_true : a12_byte_vals S_true. Proof. apply a12_bv_lit. vm_compute. reflexivity. Qed.
Lemma a12_vals_no : a12_byte_vals S_no. Proof. apply a12_bv_lit. vm_compute. reflexivity. Qed.
Lemma a12_vals_false : a12_byte_vals S_false. Proof. apply a12_bv_lit. vm_compute. reflexivity. Qed.

(** ** The symbolic state at a point of A12
    The register atoms carry the addresses the code uses: 2 = sp, 9 = s1 (the realigned locals base, the spill
    slots' base), 20 = s4 = &c->seg[gi], 22 = s6 = the shadow base (the Bx of every inline check), 24 = s8 = c,
    25 = s9 = the value in buf, 27 = s11 = the frame's shadow base. The three extra atoms carry the values the
    regions hold: 32 = F (the class-5 frame, for the slot that holds &cur_name), 33 = val[0], 34 = val[1].
    The regions: the three spill slots A12 reads (0x50 &cur_name, 0x58 &c->reading, 0x98 SH + 8), the value's
    first byte, and cur's ignore / ignore_set words, writable for the two stores. The value's SECOND byte is
    added as a region (a12_rval1) only on the two paths that have already read a non-NUL first byte. *)
Definition a12_regions_w (wr two : bool) : smem :=
[ YP09.mkRegion (Some 9%nat) 0x50 0xa0 0 0
    [YP09.mkChunk 0x50 (CVal 8 (SOff 32 PF_O_CN));
     YP09.mkChunk 0x58 (CVal 8 (SOff 24 seg_spec.RC_READING));
     YP09.mkChunk 0x98 (CVal 8 (SOff 27 8))];
  YP09.mkRegion (Some 25%nat) 0 (if two then 2 else 1) 0 0
    (YP09.mkChunk 0 (CVal 1 (SOff 33 0))
     :: (if two then [YP09.mkChunk 1 (CVal 1 (SOff 34 0))] else []));
  YP09.mkRegion (Some 20%nat) seg_spec.RS_IGNORE (seg_spec.RS_IGNORE_SET + 4)
    (if wr then seg_spec.RS_IGNORE else 0) (if wr then seg_spec.RS_IGNORE_SET + 4 else 0) [] ].
Definition a12_regions : smem := a12_regions_w true false.
Definition a12_facts : facts :=
mkFacts [ (22%nat, mkAF SB SB 0); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, PTR 2); (25%nat, PTR 0);
          (32%nat, PTR 5); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0) ] [] [].
(* the state whose region on cur is writable (the two ignore stores) and the state where it is not (every other
   run of A12, so that a run that stores nothing leaves the memory alone) *)
Definition a12_ss_w (pc : Z) (wr two : bool) : sstate :=
mkSS pc sr_atoms (a12_regions_w wr two) None a12_facts.
Definition a12_ss (pc : Z) : sstate := a12_ss_w pc true false.
Definition a12_ss_ro (pc : Z) : sstate := a12_ss_w pc false false.
(* the state of the two paths that have already read a non-NUL first byte, so the value's second byte is in buf *)
Definition a12_ss2_ro (pc : Z) : sstate := a12_ss_w pc false true.
Definition a12_Bx : sv := SOff 22 0.
Definition a12_SH1 : list shent := [mkSHE 25 0 1; mkSHE 20 seg_spec.RS_IGNORE (seg_spec.RS_IGNORE_SET + 4)].
Definition a12_SH2 : list shent := [mkSHE 25 0 2; mkSHE 20 seg_spec.RS_IGNORE (seg_spec.RS_IGNORE_SET + 4)].

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
(* the interceptor (the interceptor owner's row 10, lib/A/Rt/RtSeg.v) and the program callee this segment calls, at every
   FP state, at the listing's call targets (the image-A owner's ruling 16:54Z) *)
Hypothesis ASC : forall fx0 : YK11.FPState,
  @RtSeg.astrcasecmp_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strcasecmp).
Hypothesis REFUSE : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
(* the listing's facts over the walk's abstract instance (SegObj.v) *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
(* the record hypothesis the donor walks carry (fuzz_command numberA.v:83); PALib gives api_env, which the
   runtime-entry step lemma PaArt.aj_art_at asks for *)
Hypothesis TL : PALib B.
(* the stack-protector cells at every AR state (the image-A owner's ROUTE (A), 17:05Z): discharged from
   SegRecCells.seg_rec_cells once the listing layer's owner's stage 2 compiles *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Section s.
Context {fx : YK11.FPState}.

(** *** Reading a register and a spill slot of the cut's lists *)
Lemma a12_sl_get : forall (rd : reader) b L off z, pf_sl rd b L -> In (off, z) L ->
  rdword rd (b + off) = Some z.
Proof. intros rd b L off z H Hin. exact (proj1 (Forall_forall _ _) H (off, z) Hin). Qed.

(** *** One byte of the reader as a region chunk *)
Lemma a12_byte_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma a12_val_mem1 : forall (H : word -> bool) (mem : word -> option byte) a z,
  aview SEGS H mem a = Some z -> 0 <= z < 256 -> val_mem SEGS (mrestrict H mem) a 1 z.
Proof.
intros H mem a z Hv Hz k Hk. assert (k = 0%nat) as -> by lia.
destruct (aview_byte SEGS H mem a z Hv) as (b & Hb & Hvb & _).
cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
rewrite le_byte_small by (cbn; lia).
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Hvb.
symmetry. apply a12_byte_self.
Qed.

(** *** The environment of the state at a point of A12 *)
Definition a12_extra (v : pfv) (pos : Z) (val : list Z) : list word :=
map (Z_to_bv 64) [pf_F v pos; nth 0 val 0; nth 1 val 0].
Definition a12_E (rX : bvmap 5 word) (v : pfv) (pos : Z) (val : list Z) : env :=
Eimg (Ereg rX (a12_extra v pos val)).

(** *** The mid-walk invariant of A12
    What holds at every program point of A12 between two runtime calls: the cut's base facts, the line, the
    spine (this line's counter budget), the value in buf, and the callee-saved registers the code uses (s2,
    s3 = z3, s4 = cur, s5, s8 = c, s9 = vp, s10, s11 = SH). s3 is SH + 8 at IGN and val[0] after 0x883a0; s7
    (the key at IGN, then parse_bool's answer) is not carried. *)
Definition a12_I (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) (z3 : Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val /\
  pf_rg rX ([(18, 0x23); (19, z3); (24, p_c v); (27, pf_SH v pos)] ++ PF_RM v o ln ++
            [(20, seg_spec.rseg_addr (p_c v) gi); (25, vp)]).

Lemma a12_I_of_kv : forall n v pos lyc Sc (Wc : world SEGS) rX memc mdc cf nm o ln d gi kp vp key val,
  INV_KV B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val ->
  a12_I n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (pf_SH v pos + 8).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val
  (HB & HMID & HST & (_ & _ & _ & HVstr & HVinb) & _ & HRG).
split; [exact HB|]. split; [exact HMID|]. split; [exact HST|]. split; [exact HVstr|]. split; [exact HVinb|].
unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin. apply HRG.
unfold PF_RL, PF_RM in *. cbn [app In] in Hin |- *. tauto.
Qed.

(** *** The seed: the symbolic state of A12 at any of its program points, from the mid-walk invariant *)
Lemma a12_seed_I_w : forall n v pos lyc Sc (Wc : world SEGS) rX memc mdc cf nm o ln d gi vp val z3 (pc : Z)
    (wr two : bool),
  a12_I n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 ->
  (if two then (1 <= length val)%nat else True) ->
  st_ok_pi SEGS VAL (a12_E rX v pos val) (a12_ss_w pc wr two)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 pc wr two HINV Htwo.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HINV as ((HCX & HFI & HOBJ & HSL & HFSH) & HMID & HST & HVstr & HVinb & HRG).
pose proof HFI as (HJ & Hly & Hfs & Hperm & Hsaved & Hflag & Hfrm & HRG0).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hfin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 5 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hfin) as (HFal & _ & HFpres & _).
change (fs_frame_bytes 5) with 2048 in *.
assert (HFeq : frame_addr lyc 5 pos = pf_F v pos) by (rewrite Hly; reflexivity).
rewrite HFeq in HF4096, HFceil, HFapp, HFal, HFpres.
(* the block that holds c *)
pose proof HOBJ as (_ & _ & _ & HAc & HHc & _ & _ & _ & _).
destruct HHc as (bq & mq & Hinq & Hbq1 & Hbq2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bq mq HAR Hinq) as (_ & Hq4096 & Hqceil & _ & Hqpres & _ & Hqm).
pose proof (req_size_pos mq ltac:(lia)) as [Hrq1 Hrq2].
(* the frame and the block do not meet *)
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bq mq 5 pos HAR Hinq Hfin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite HFeq in Hsep.
change (fs_frame_bytes 5) with 2048 in Hsep.
(* where the value lies: inside buf, inside the frame *)
unfold pf_inb in HVinb. unfold PF_O_BUF in HVinb.
pose proof HVstr as ((HVz & HVn) & _).
assert (Hvb : forall i, (i < length val)%nat -> 0 <= nth i val 0 < 256).
{ intros i Hi. assert (Hi' : Nat.lt i (length (val ++ @cons Z 0 nil)))
    by (rewrite length_app; cbn [length]; lia).
  pose proof (HVz i Hi') as Hz. rewrite app_nth1 in Hz by exact Hi.
  destruct (aview_byte SEGS (w_H Wc) memc (vp + Z.of_nat i) (nth i val 0) Hz) as (_ & _ & _ & Hr).
  exact Hr. }
assert (Hv0 : 0 <= nth 0 val 0 < 256).
{ destruct val as [|x r]; [cbn; lia | apply Hvb; cbn [length]; lia]. }
assert (Hv1 : 0 <= nth 1 val 0 < 256).
{ destruct (Nat.lt_ge_cases 1 (length val)) as [Hl|Hl]; [apply Hvb; exact Hl|].
  rewrite nth_overflow by lia. lia. }
(* the registers of the cut *)
assert (R2 : getr rX 2 = w64 (pf_s1 v))
  by (exact (pf_a5_k.a5_rg_get rX _ 2 (pf_s1 v) HRG0 ltac:(cbn [In]; tauto))).
assert (R6 : getr rX 22 = w64 SHADOW_OFF)
  by (exact (pf_a5_k.a5_rg_get rX _ 22 SHADOW_OFF HRG0 ltac:(cbn [In]; tauto))).
assert (R9 : getr rX 9 = w64 (pf_s1 v))
  by (exact (pf_a5_k.a5_rg_get rX _ 9 (pf_s1 v) HRG0 ltac:(cbn [In]; tauto))).
assert (R20 : getr rX 20 = w64 (seg_spec.rseg_addr (p_c v) gi))
  by (exact (pf_a5_k.a5_rg_get rX _ 20 (seg_spec.rseg_addr (p_c v) gi) HRG
               ltac:(cbn [PF_RL PF_RM app In]; tauto))).
assert (R24 : getr rX 24 = w64 (p_c v))
  by (exact (pf_a5_k.a5_rg_get rX _ 24 (p_c v) HRG ltac:(cbn [PF_RL PF_RM app In]; tauto))).
assert (R25 : getr rX 25 = w64 vp)
  by (exact (pf_a5_k.a5_rg_get rX _ 25 vp HRG ltac:(cbn [PF_RL PF_RM app In]; tauto))).
assert (R27 : getr rX 27 = w64 (pf_SH v pos))
  by (exact (pf_a5_k.a5_rg_get rX _ 27 (pf_SH v pos) HRG ltac:(cbn [PF_RL PF_RM app In]; tauto))).
(* the entry c and the index gi *)
pose proof HCX as (_ & _ & _ & Hc64 & _ & _ & _ & _ & (fe & HPRE1) & _ & _).
pose proof HPRE1 as ((Hc0 & Hc16 & _) & _ & _).
pose proof HST as (HRC & HOKcur & HNM & HCNT).
assert (Hgi32 : (gi < 32)%nat).
{ destruct HRC as (bs & _ & (_ & Hn32 & _)). cbn [pf_cur_ok] in HOKcur. lia. }
unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE in *.
unfold seg_spec.SEG_C_SIZE in Hbq2.
assert (Hgi' : 0 <= Z.of_nat gi <= 31) by lia.
(* the locals base of the call *)
pose proof STK_values as (_ & _ & _ & SPF & _).
assert (Hs1 : alloc_ceiling <= pf_s1 v /\ pf_s1 v <= 2 ^ 47).
{ unfold pf_s1. pose proof (Z.mod_pos_bound (pf_sp0 v - 0x140) 32 ltac:(lia)) as Hm.
  rewrite SPF in Hslo. lia. }
assert (Hs116 : pf_s1 v mod 16 = 0).
{ unfold pf_s1. pose proof (Z.div_mod (pf_sp0 v - 0x140) 32 ltac:(lia)) as Hd.
  replace (pf_sp0 v - 0x140 - (pf_sp0 v - 0x140) mod 32) with (2 * ((pf_sp0 v - 0x140) / 32) * 16) by lia.
  apply Z_mod_mult. }
(* the frame's shadow base *)
assert (HSHv : pf_SH v pos = SHADOW_OFF + pf_F v pos / 8) by reflexivity.
assert (HF8lo : 512 <= pf_F v pos / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : pf_F v pos / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
(* the alignment of &c->seg[gi] *)
assert (Hcu4 : (p_c v + 356 * Z.of_nat gi) mod 4 = 0).
{ destruct (proj1 (Z.mod_divide (p_c v) 16 ltac:(lia)) Hc16) as [q Hq].
  apply (proj2 (Z.mod_divide _ 4 ltac:(lia))). exists (4 * q + 89 * Z.of_nat gi). lia. }
(* the slots A12 reads *)
pose proof (a12_sl_get _ _ _ 0x50 (pf_F v pos + PF_O_CN) HSL ltac:(cbn [PF_SL In]; tauto)) as S50.
pose proof (a12_sl_get _ _ _ 0x58 (p_c v + seg_spec.RC_READING) HSL ltac:(cbn [PF_SL In]; tauto)) as S58.
pose proof (a12_sl_get _ _ _ 0x98 (pf_SH v pos + 8) HSL ltac:(cbn [PF_SL In]; tauto)) as S98.
(* the value's first byte through the reader *)
assert (HB0 : rdW Wc memc vp = Some (nth 0 val 0)).
{ pose proof (HVz 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as Hz.
  cbn [Z.of_nat] in Hz. rewrite Z.add_0_r in Hz. rewrite Hz. f_equal.
  destruct val as [|x r]; reflexivity. }
(* the symbolic state *)
rewrite restrict_mkst_fx.
set (E := a12_E rX v pos val).
assert (ER : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; unfold a12_E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (a12_extra v pos val) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold a12_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth a12_extra map] in E32, E33, E34.
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (ER 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = p_c v + 356 * Z.of_nat gi)
  by (rewrite (ER 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = SHADOW_OFF)
  by (rewrite (ER 22%nat 22%bv eq_refl), R6; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U24 : bv_unsigned (ew E 24) = p_c v)
  by (rewrite (ER 24%nat 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = vp)
  by (rewrite (ER 25%nat 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = pf_SH v pos)
  by (rewrite (ER 27%nat 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF in *; lia).
assert (U32 : bv_unsigned (ew E 32) = pf_F v pos) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = nth 0 val 0) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = nth 1 val 0) by (rewrite E34; apply unsigned_lit_small; lia).
unfold a12_ss_w. apply pa_entry_st_ok_full.
- subst E. unfold a12_E. apply regs_ok_Eimg_Ereg.
- destruct wr, two; vm_compute; reflexivity.
- unfold a12_regions_w. constructor; [|constructor; [|constructor; [|constructor]]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros oo Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    * apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x50 8 (SOff 32 PF_O_CN) (pf_F v pos + PF_O_CN));
        [cbn [sv_denot]; rewrite U32; reflexivity | unfold PF_O_CN; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ S50).
    * apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x58 8 (SOff 24 seg_spec.RC_READING)
               (p_c v + seg_spec.RC_READING));
        [cbn [sv_denot]; rewrite U24; reflexivity | unfold seg_spec.RC_READING; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ S58).
    * apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x98 8 (SOff 27 8) (pf_SH v pos + 8));
        [cbn [sv_denot]; rewrite U27; reflexivity | unfold SHADOW_OFF in *; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ S98).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U25. split; [lia|]. split; [destruct two; lia|]. split; [intros oo Ho; lia|].
    pose proof (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) vp 0 1 (SOff 33 0) (nth 0 val 0)
      ltac:(cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)
      ltac:(rewrite Z.add_0_r; apply a12_val_mem1; [exact HB0 | lia])) as HC0.
    destruct two; [|constructor; [exact HC0 | constructor]].
    constructor; [exact HC0|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ vp 1 1 (SOff 34 0) (nth 1 val 0));
      [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
    apply a12_val_mem1; [|lia].
    pose proof (HVz 1%nat ltac:(rewrite length_app; cbn [length]; lia)) as Hz1.
    change (Z.of_nat 1) with 1 in Hz1. rewrite Hz1. f_equal.
    destruct (Nat.lt_ge_cases 1 (length val)) as [Hl|Hl]; [apply app_nth1; lia|].
    rewrite app_nth2 by lia. replace (1 - length val)%nat with 0%nat by lia. cbn [nth].
    rewrite nth_overflow by lia. reflexivity.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U20. unfold seg_spec.RS_IGNORE, seg_spec.RS_IGNORE_SET.
    split; [lia|]. split; [lia|]. split; [|constructor].
    destruct wr; intros oo Ho; [|lia]. apply (apresent_writable SEGS).
    exact (proj1 (Hqpres (p_c v + 356 * Z.of_nat gi + oo) ltac:(lia))).
- unfold a12_regions_w. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
  rewrite U9, U20, U25. unfold seg_spec.RS_IGNORE, seg_spec.RS_IGNORE_SET.
  destruct two; destruct Hsep as [Hsep | Hsep]; repeat split; first [exact I | lia].
- split; [|split; exact I].
  cbn [a12_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite U9, U20, U22, U25, U32, U33, U34.
  rewrite SB_SHADOW_OFF.
  change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 2) with 4.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat split; try exact I; try (unfold SHADOW_OFF in *; lia).
Qed.

(** The state the two ignore stores run in, and the state every other run of A12 runs in. *)
Lemma a12_seed_I : forall n v pos lyc Sc (Wc : world SEGS) rX memc mdc cf nm o ln d gi vp val z3 (pc : Z),
  a12_I n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 ->
  st_ok_pi SEGS VAL (a12_E rX v pos val) (a12_ss pc)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof. intros. apply (a12_seed_I_w n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 pc true false);
  [assumption | exact I]. Qed.

Lemma a12_seed_I_ro : forall n v pos lyc Sc (Wc : world SEGS) rX memc mdc cf nm o ln d gi vp val z3 (pc : Z),
  a12_I n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 ->
  st_ok_pi SEGS VAL (a12_E rX v pos val) (a12_ss_ro pc)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof. intros. apply (a12_seed_I_w n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 pc false false);
  [assumption | exact I]. Qed.

Lemma a12_seed_I2_ro : forall n v pos lyc Sc (Wc : world SEGS) rX memc mdc cf nm o ln d gi vp val z3 (pc : Z),
  a12_I n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 -> (1 <= length val)%nat ->
  st_ok_pi SEGS VAL (a12_E rX v pos val) (a12_ss2_ro pc)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof. intros. apply (a12_seed_I_w n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 pc false true);
  assumption. Qed.

(** The seed at the cut itself. *)
Lemma a12_seed : forall n v pos lyc Sc (Wc : world SEGS) rX memc mdc cf nm o ln d gi kp vp key val (pc : Z),
  INV_KV B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val ->
  st_ok_pi SEGS VAL (a12_E rX v pos val) (a12_ss pc)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val pc HINV.
apply (a12_seed_I n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (pf_SH v pos + 8) pc).
exact (a12_I_of_kv n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val HINV).
Qed.

End s.
End e.
End f.
End d.
