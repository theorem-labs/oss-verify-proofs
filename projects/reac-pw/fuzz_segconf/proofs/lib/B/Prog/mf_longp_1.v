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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 168 of its 217 lines of code are new or changed and 404 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, m_file at 0x86140): segment S_MF_LONGP of its walk
   (LONG 0x863d4 -> TAIL 0x86820; the image-B m_file cut map section 4, the image-B m_file segment table section 3), part 1:
   the program points the segment is cut at, their statements, the pure facts of a long line and the light symbolic
   state of the blank skip. A walk lane of the image-B m_file-family owner's G2B. Adapted from the image-A m_file-family lane's image-A walk (commit 93220999e732: lib/A/Prog/m_file_s_long_d.v LK_CALLPX_stmt and
   lib/A/Prog/m_file_s_long.v) at image B's numbers.
   THE CODE (listing m_file.fuzz_segconf.asan-ubsan.s, lines 167-185, 429-441, 714-716, 868-869, 878-879):
     0x863d4 mv s5,a2                          s5 = the next line's address (kept across m_refuse)
     0x863d8 bgeu s10,a0 -> 0x86810            p >= e: never taken, the line has 512 bytes or more
     0x863dc mv a1,s10                         a1 = s10 = the cursor f
     0x863e0 (LP_HEAD) srli a2,a1,3; add a2,a2,s2; lb a3,0(a2); bnez a3 -> 0x86414
                                               the instrumented check of *f (a load of the shadow byte at
                                               (f >> 3) + s2 and a compare; the slow path 0x86414-0x8641c compares
                                               f & 7; the error path 0x86ec8, a call of errpath_load1, is not reached)
     0x863f0 lbu a3,0(s10); bltu a6,a3 -> 0x867ec            *f > 0x20 (a6 = 0x20): not blank
     0x863f8 srl a3,s3,a3; andi a3,a3,1; beqz a3 -> 0x867ec  bit *f of the blank mask s3 = 0x100002200 clear
     0x86404 addi s10,s10,1; addi a1,a1,1; bne s10,a0 -> 0x863e0   the next byte
     0x86410 j 0x86810                         every byte of the line is blank
     0x867ec lb a0,0(a2); bnez a0 -> 0x86c60  the check of *f again (a2 left at 0x863e4; the slow
                                               path 0x86c60-0x86c68, the error path 0x86ef0 is not reached)
     0x867f4 lbu a0,0(s10); addi a0,a0,-91; seqz; addi a0,a0,-1; ld a1,136(s1); and a1,a0,a1; sd a1,136(s1)
                                               cur = NULL when *f is '[', else cur
     0x86810 (LP_CALLP) mv a0,s9; mv a1,s11; 0x86818 (LP_JAL) jal m_refuse; 0x8681c (LP_AFT) mv s10,s5 -> TAIL
   No UBSan trap branch lies in the segment (the image-B m_file cut map section 1).
   THE CUTS: LP_CALLPX_stmt at LP_CALLP 0x86810 (image A's LK_CALLPX_stmt at 0x861e4): the LONG facts at the LONG
   state's memory memc, the memory memc' that differs from memc at most in the cur cell [s1 + 136, s1 + 144) and holds
   cur' there (cur, or NULL when the first non-blank byte is '['), the journal at memc', and the long line's model
   with cur'. LP_LOOP_stmt k at LP_HEAD 0x863e0: the blank skip after k blank bytes, the same memory form with the
   cur cell holding cur. mf_longp_2.v proves LONG from both; mf_longp_3.v proves LP_CALLPX from TAIL.
   THE LIGHT STATE (lp_ss): every register its own atom, atom 32 = the byte *f, atom 33 = the cur cell's value,
   two regions: the byte at s10 (read-only) and the cur cell 136(s1) (writable); the shadow base of the token runs
   is s2 (atom 18). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ===================================== the program points ===================================== *)
Definition LP_HEAD : Z := AF_m_file + 0x2a0.    (* 0x863e0, the blank skip's head *)
Definition LP_CALLP : Z := AF_m_file + 0x6d0.   (* 0x86810, m_refuse's arguments: both arms meet *)
Definition LP_JAL : Z := AF_m_file + 0x6d8.     (* 0x86818, jal m_refuse *)
Definition LP_AFT : Z := AF_m_file + 0x6dc.     (* 0x8681c, m_refuse's return point *)

(* ===================================== the light symbolic state ===================================== *)
Definition lp_ss (pc : Z) (rs : smem) : sstate := mkSS pc sr_atoms rs None (mkFacts [] [] []).
(* the byte at s10 (the cursor f), atom 32 *)
Definition lp_rtxt : YP09.region := YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
(* the cur cell 136(s1), atom 33, writable *)
Definition lp_rcur : YP09.region :=
  YP09.mkRegion (Some 9%nat) 136 144 136 144 [YP09.mkChunk 136 (CVal 8 (SOff 33 0))].
(* the shadow base of the token runs: s2 *)
Definition lp_Bx : sv := SOff 18 0.

(* ===================================== pure facts ===================================== *)
Lemma lp_line_len : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
intros rest. unfold mf_line. induction rest as [|b r IH]; [cbn; lia|]. cbn [break_nl].
destruct (b =? NL); [cbn; lia|]. destruct (break_nl r) as [l q]. cbn [fst length] in *. lia.
Qed.
(* a byte of the line is the byte of the text left at the same index *)
Lemma lp_line_nth : forall rest j, (j < length (mf_line rest))%nat -> nth j (mf_line rest) 0 = nth j rest 0.
Proof.
unfold mf_line. induction rest as [|b r IH]; intros j Hj; cbn [break_nl] in *.
- cbn in Hj. lia.
- destruct (b =? NL) eqn:Eb; [cbn in Hj; lia|].
  specialize (IH (pred j)). destruct (break_nl r) as [l q] eqn:E. cbn [fst length] in *.
  destruct j as [|j]; [reflexivity|]. cbn [nth pred] in *. apply IH. lia.
Qed.
(* the first non-blank byte of a line whose k first bytes are blank *)
Lemma lp_drop_k : forall (l : list Z) k, (k < length l)%nat ->
  (forall j, (j < k)%nat -> blank (nth j l 0) = true) -> blank (nth k l 0) = false ->
  hd0 (dropwhile blank l) = nth k l 0.
Proof.
induction l as [|x r IH]; intros k Hk Hb Hn; cbn [length] in Hk; [lia|]. cbn [dropwhile].
destruct k as [|k].
- cbn [nth] in Hn. rewrite Hn. reflexivity.
- pose proof (Hb 0%nat ltac:(lia)) as H0. cbn [nth] in H0. rewrite H0. cbn [nth].
  apply IH; [lia | intros j Hj; exact (Hb (S j) ltac:(lia)) | exact Hn].
Qed.
(* a line of blank bytes only *)
Lemma lp_drop_all : forall (l : list Z), (forall j, (j < length l)%nat -> blank (nth j l 0) = true) ->
  dropwhile blank l = [].
Proof.
induction l as [|x r IH]; intros Hb; [reflexivity|]. cbn [dropwhile].
pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as H0. cbn [nth] in H0. rewrite H0.
apply IH. intros j Hj. exact (Hb (S j) ltac:(cbn [length]; lia)).
Qed.
(* the model of a line of 512 bytes or more (plain mfp_facts.v m_line_long) *)
Lemma lp_line_long : forall mcc cur line l, (512 <= length l)%nat ->
  m_line (mcc, cur) line l = (m_refuse mcc line false, if hd0 (dropwhile blank l) =? LBR then None else cur).
Proof.
intros mcc cur line l Hl. unfold m_line.
replace (512 <=? length l)%nat with true by (symmetry; apply Nat.leb_le; lia). reflexivity.
Qed.
(* the blank mask's bit b, 0 <= b <= 32, is the blank test of b *)
Lemma lp_mask : forall b, 0 <= b <= 32 -> Z.land (Z.shiftr MF_BLANK b) 1 = if blank b then 1 else 0.
Proof.
intros b Hb. replace b with (Z.of_nat (Z.to_nat b)) by lia. assert (Hn : (Z.to_nat b <= 32)%nat) by lia.
generalize (Z.to_nat b) Hn. clear. intros n Hn.
do 33 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.
(* no byte above 0x20 is blank *)
Lemma lp_blank_gt : forall b, 32 < b -> blank b = false.
Proof.
intros b Hb. unfold blank.
destruct (b =? 32) eqn:E1; [apply Z.eqb_eq in E1; lia|].
destruct (b =? 9) eqn:E2; [apply Z.eqb_eq in E2; lia|].
destruct (b =? 13) eqn:E3; [apply Z.eqb_eq in E3; lia|]. reflexivity.
Qed.
(* s1 - sp0 (-320 or -336) is a multiple of 16 *)
Lemma lp_o16 : forall sp0 s1, s1 = sp0 - 320 \/ s1 = sp0 - 336 -> (s1 - sp0) mod 16 = 0.
Proof.
intros sp0 s1 [-> | ->].
- replace (sp0 - 320 - sp0) with (-20 * 16) by lia. apply Z_mod_mult.
- replace (sp0 - 336 - sp0) with (-21 * 16) by lia. apply Z_mod_mult.
Qed.
(* a register value plus a constant *)
Lemma lp_bv_off : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
intros x c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the environment of the light state: atom 32 = b, atom 33 = cp *)
Definition lp_E (regs1 : bvmap 5 word) (b cp : Z) : env := Eimg (Ereg regs1 [Z_to_bv 64 b; Z_to_bv 64 cp]).
Lemma lp_ew_reg : forall regs1 b cp n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (lp_E regs1 b cp) n = getr regs1 r.
Proof.
intros regs1 b cp n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold lp_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma lp_ew32 : forall regs1 b cp, ew (lp_E regs1 b cp) 32 = Z_to_bv 64 b.
Proof. intros. unfold lp_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 0). Qed.
Lemma lp_ew33 : forall regs1 b cp, ew (lp_E regs1 b cp) 33 = Z_to_bv 64 cp.
Proof. intros. unfold lp_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 1). Qed.
Lemma lp_env_agree : forall regs1 b cp, env_agree 32 (Ereg regs1 [Z_to_bv 64 b; Z_to_bv 64 cp]) (lp_E regs1 b cp).
Proof. intros. split; [intros n Hn; unfold lp_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.

(* the state with no region (the run from LONG) *)
Lemma lp_seed0 : forall (W : world SEGS) regs1 mem pc b cp,
  st_ok_pi SEGS VAL (lp_E regs1 b cp) (lp_ss pc [])
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs1 mem pc b cp. rewrite restrict_mkst_fx. unfold lp_ss. apply pa_entry_st_ok_full.
- unfold lp_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint]. exact I.
- split; [exact I | split; exact I].
Qed.

(* the state of the blank skip: the byte b at x = s10, the cur cell's value cp at s1 + 136 *)
Lemma lp_seed : forall (W : world SEGS) regs1 mem pc x s1 b cp,
  getr regs1 26 = w64 x -> getr regs1 9 = w64 s1 ->
  0 <= x -> x + 1 <= s1 + 136 -> 0 <= s1 -> s1 + 144 <= 2 ^ 64 ->
  0 <= b < 256 -> 0 <= cp < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) x 1 b ->
  val_mem SEGS (mrestrict (w_H W) mem) (s1 + 136) 8 cp ->
  (forall a, s1 + 136 <= a < s1 + 144 -> writable_at SEGS (mrestrict (w_H W) mem) a) ->
  st_ok_pi SEGS VAL (lp_E regs1 b cp) (lp_ss pc [lp_rtxt; lp_rcur])
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs1 mem pc x s1 b cp R26 R9 Hx0 Hx1 Hs0 Hs1 Hb Hcp V1 V8 Hwr.
assert (E26 : ew (lp_E regs1 b cp) 26 = getr regs1 26) by (apply lp_ew_reg; reflexivity).
assert (E9 : ew (lp_E regs1 b cp) 9 = getr regs1 9) by (apply lp_ew_reg; reflexivity).
pose proof (lp_ew32 regs1 b cp) as E32. pose proof (lp_ew33 regs1 b cp) as E33.
assert (B26 : base_val (lp_E regs1 b cp) (Some 26%nat) = x)
  by (cbn [base_val]; rewrite E26, R26; unfold w64; apply unsigned_lit_small; lia).
assert (B9 : base_val (lp_E regs1 b cp) (Some 9%nat) = s1)
  by (cbn [base_val]; rewrite E9, R9; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold lp_ss. apply pa_entry_st_ok_full.
- unfold lp_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, lp_rtxt, lp_rcur;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite B26. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS (lp_E regs1 b cp) _ x 0 1 (SOff 32 0) b);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact V1.
  + rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS (lp_E regs1 b cp) _ s1 136 8 (SOff 33 0) cp);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | exact V8].
- apply pairwise_disjoint_of_extents. unfold extent_of_region, lp_rtxt, lp_rcur.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B26, B9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [exact I | split; exact I].
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
#[local] Notation MF_STK := SegInstB.STK_m_file.

(* the text left lies in a live block: above 4096, below the allocator's ceiling *)
Lemma lp_txt_bounds : forall v lyc Sc Wc memc mdc pos lowsh mcc mcc' cur line p rest,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_loop v Wc memc mcc' cur line p rest ->
  4096 <= p /\ p + Z.of_nat (length rest) + 1 <= alloc_ceiling.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc mcc' cur line p rest CX0 CORE LOOP.
destruct (mf_txt_blk B v Wc memc mcc' cur line p rest CX0 LOOP) as (bb & bm & Hbin & Hb1 & Hb2).
pose proof CORE as (HJ & HPerm & _). pose proof HJ as (HAR & _).
assert (Hbin2 : In (bb, bm) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hbin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bm HAR Hbin2) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hbm).
pose proof (req_size_pos bm ltac:(lia)) as [_ Hreq]. lia.
Qed.
(* ===================================== the statements ===================================== *)
(* the memory at a point of the segment: the journal there, every byte but the cur cell as at the LONG state's
   memory memc, the cur cell holding cur *)
Definition lp_mem (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte) (pos : Z)
  (cur : option nat) (memk : word -> option byte) (mdk : Model) : Prop :=
ajournal SEGS B MF_STK (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v)
  (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memk mdk 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 136 <= a < mf_s1 (mv_sp v) + 144) ->
 rdW Wc memk a = rdW Wc memc a) /\
val_mem SEGS (mrestrict (w_H Wc) memk) (mf_s1 (mv_sp v) + 136) 8 (mf_cur_ptr (mv_c v) cur).

(* 0x86810: the LONG cut's facts at the LONG state (memc, mdc), the registers m_refuse's call and the tail read (s5
   = the next line's address, s11 = line + 1, s4 = 511, and mf_regs_at), the long line's model with the new cursor
   cur', and the memory memc' (model mdc') at 0x86810 *)
Definition LP_CALLPX_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur cur' : option nat) (line p : Z) (rest : list Z) memc' mdc',
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
(512 <= length (mf_line rest))%nat ->
(cur' = cur \/ cur' = None) ->
mf_fin (m_refuse mcc (line + 1) false, cur') line rest = mf_final v ->
getr regs1 21 = w64 (mf_next p rest) -> getr regs1 27 = w64 (line + 1) -> getr regs1 20 = w64 511 ->
lp_mem v lyc Sc Wc memc pos cur' memc' mdc' ->
mf_at B v Wc regs1 memc' mdc' LP_CALLP.

(* 0x863e0, the blank skip after k bytes, all blank: s10 = a1 = p + k, a0 = the line's end, a6 = 0x20, s5 = the next
   line's address, s11 = line + 1, s4 = 511; the memory at the LONG state's but the cur cell, which holds cur *)
Definition LP_LOOP_stmt (n k : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) memk mdk,
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
(512 <= length (mf_line rest))%nat ->
mf_fin (m_line (mcc, cur) (line + 1) (mf_line rest)) line rest = mf_final v ->
(k < length (mf_line rest))%nat -> (forall j, (j < k)%nat -> blank (nth j (mf_line rest) 0) = true) ->
getr regs1 26 = w64 (p + Z.of_nat k) -> getr regs1 11 = w64 (p + Z.of_nat k) ->
getr regs1 10 = w64 (p + Z.of_nat (length (mf_line rest))) ->
getr regs1 21 = w64 (mf_next p rest) -> getr regs1 16 = w64 0x20 ->
getr regs1 27 = w64 (line + 1) -> getr regs1 20 = w64 511 ->
lp_mem v lyc Sc Wc memc pos cur memk mdk ->
mf_at B v Wc regs1 memk mdk LP_HEAD.
End e.
End f.
End d.
