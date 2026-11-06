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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module names changed; 390 of its 519 lines of code are new or changed and 324 lines of the source are left out. *)
(* The kit and the n_kept = 8 arm of the walk of m_refuse on fuzz_segconf.asan-ubsan (image B, pin sha256 c3796c0b38f3..., entry 0x8782c, 416 bytes,
   104 instructions, a 48-byte frame, no side-stack frame): m_refuse_contract of lib/B/Prog/m_refuse_c.v at image B's
   numbers (lib/B/Prog/SegInstB.v), in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the entry, SRr of
   apost_baseF at the return, over `Context {PI : PAImg seg_listing}`).

   ADAPTATION of the image-A m_file-family lane's image-A walk form (lib/A/Prog/reac_box_catalogueA.v, ieqA.v: the entry seed, the token
   run, the awr_ok goal, field_of_region, kept_of_frame, the ret) and of fuzz_command's image-B walk of `record`
   (lib/B/Prog/record_aux.v / record_s0.v / record_s1.v at origin/ossv/recipes 501c0d516c69: the counter region with
   a CVal 4 chunk, the UBSan trap edges decided by the atoms' facts, the explicit refutation of the pointer-overflow
   trap) and of fuzz_command's snprintf step (lib/A/Prog/check_reply_s4.v: srr_art_postF_of_pf, aj_art_own_atF,
   srr_after_artF). The functional content is lib/B/Prog/m_refuse_f.v.

   The code (the neutral listing of m_refuse in image B):
     0x8782c-0x87844  frame of 48: ra s0 s1 s2 s3 at sp+40 .. sp+8; a2 = c & 3
     0x87848 bnez a2 -> unimp 0x87978       UBSan trap 1 (c is 4-aligned): not taken, c mod 16 = 0
     0x8784c-0x87870  a4 = line; s2 = the shadow base (the GOT word as_got_shadow B, image B 0xa3210, listing object
                      0, holds the cell 0xac7b8 that holds it); s0 = c + 0x2008 = &refused; s1 = s0 + 932 = &n_kept;
                      s3 = (s1 >> 3) + s2 (the shadow byte of n_kept)
     0x87874-0x87878  the instrumented check of n_kept (a load of the shadow byte at s3 and a compare; the slow block
                      0x8797c and the error path, a call of errpath_load4 at 0x8798c, are not reached)
     0x8787c-0x87884  n_kept = lw 0(s1); blt 7,n_kept -> 0x87940 (n_kept = 8: only refused++)
     0x87888          blez line -> 0x878d8 (the "%s: " arm)
     0x8788c-0x878d0  line > 0: bgeu n_kept,9 -> unimp (trap 2), a5 = c + 0x200c + 112 n_kept = &kept[n_kept],
                      a3 = ~a5, bltu a3,112n -> unimp (trap 3, the address of kept[n_kept] wrapping), a3 = c + 0x23b4
                      = c->reading, a2 = .str.7 0x210c0 (SegModel.F_addr_line), a1 = 112, a0 = a5;
                      jal 0x43af0 the snprintf wrapper; j 0x87920
     0x878d8-0x8791c  line = 0: bltu 8,n_kept -> unimp (trap 4), the same slot and the same wrap check (trap 5),
                      a2 = .str.8 0x210e0 (SegModel.F_addr); jal the snprintf wrapper
     0x87920-0x8793c  the check of n_kept again (slow block 0x879a4), n_kept + 1 (addiw), blt n_kept+1,n_kept ->
                      unimp (trap 6, the signed overflow of n_kept + 1), the check again (slow block 0x879b8, the
                      store check), sw n_kept+1,0(s1)
     0x87940-0x87958  the check of refused (slow block 0x87990), refused = lw 0(s0), refused + 1, sw 0(s0)
     0x8795c-0x87974  ra s0 s1 s2 s3 restored, sp += 48, ret
   Every one of the six trap branches to `unimp` 0x87978 is refuted at its branch: traps 1, 2, 4 and 6 by the atoms'
   facts (c's 16-alignment; 0 <= n_kept <= 7 or n_kept = 8, from mconf_encp's u32_enc and the kept list's length;
   n_kept + 1 <= 8 < 2 ^ 31), traps 3 and 5 by mr_no_wrap below (c + 9236 <= 2 ^ 47, so ~(c + 0x200c) is far above
   112 * 7). The four instrumented checks are decided by the two shadow entries of mr_SH (the 4 bytes of n_kept and
   of refused, addressable by the contract's sa_addr over the whole 9236-byte block), so no error path is reached.

   Image B's numbers of the statement: the entry BASE + AF_m_refuse, STK_m_refuse (48 + 2 * ESTACK = 8240),
   RLO_A / RHI_A, seg_litA_fz, gotwA / guardA, all of lib/B/Prog/SegInstB.v. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt PaArtOwn PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtPFPf RtPFShared RtPFCmd RtPFSeg RtAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require m_refuse_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Module SM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec.SegModel.
Module SP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.seg_spec.
(* the walk's functional lemmas (the mconf encoding and the two printf texts) *)
Module MF := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog.m_refuse_f.

(* ---------- image B's numbers ---------- *)
(* STK_m_refuse = 48 + 2 * ESTACK: the frame and the window row 4's snprintf text asks (SegInstB.v) *)
#[local] Notation MR_STK := SegInstB.STK_m_refuse.
Definition MR_FRAME : Z := 48.
(* the walk's points, as offsets from the listing's base (BASE = 0x84dc0) *)
Definition MR_E : Z := AF_m_refuse.      (* 0x8782c, the entry *)
Definition MR_JOIN : Z := 0x2b80.        (* 0x87940: the check of refused, refused++ and the epilogue *)
Definition MR_SNP1 : Z := 0x2b10.        (* 0x878d0: jal the snprintf wrapper, the "%s:%d: " arm *)
Definition MR_RET1 : Z := 0x2b14.        (* 0x878d4: j 0x87920 *)
Definition MR_SNP2 : Z := 0x2b5c.        (* 0x8791c: jal the snprintf wrapper, the "%s: " arm *)
Definition MR_TAIL : Z := 0x2b60.        (* 0x87920: n_kept++ and on to the join *)

(* ---------- the symbolic state ---------- *)
(* atoms above the 32 registers: 32 = the shadow base, 33 = n_kept, 34 = refused; the registers' own atoms carry
   the arguments (10 = c, 11 = line) *)
Definition SA_SB : nat := 32.
Definition SA_N : nat := 33.
Definition SA_R : nat := 34.
Definition SA_C : nat := 10.
Definition mr_Bx : sv := SOff SA_SB 0.
Definition mr_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the two cells the code reads and writes, as regions of the block (base atom 10 = c); `w` is the write window,
   empty in the arm that does not write the cell *)
Definition mr_refused (w : bool) : YP09.region :=
YP09.mkRegion (Some SA_C) SP.MC_REFUSED (SP.MC_REFUSED + 4) SP.MC_REFUSED
  (if w then SP.MC_REFUSED + 4 else SP.MC_REFUSED) [YP09.mkChunk SP.MC_REFUSED (CVal 4 (SOff SA_R 0))].
Definition mr_nkept (w : bool) : YP09.region :=
YP09.mkRegion (Some SA_C) SP.MC_NKEPT (SP.MC_NKEPT + 4) SP.MC_NKEPT
  (if w then SP.MC_NKEPT + 4 else SP.MC_NKEPT) [YP09.mkChunk SP.MC_NKEPT (CVal 4 (SOff SA_N 0))].
(* the shadow entries of the four instrumented checks: the 4 bytes of refused and the 4 bytes of n_kept *)
Definition mr_SH : list shent := [mkSHE SA_C SP.MC_REFUSED (SP.MC_REFUSED + 4); mkSHE SA_C SP.MC_NKEPT (SP.MC_NKEPT + 4)].
(* the entry state: the frame the prologue writes, the shadow base's GOT word and cell, the two counters *)
Definition mr_regions (wn : bool) : smem :=
[stack_region MR_FRAME; got_regionP; bcell_regionP SA_SB; mr_refused true; mr_nkept wn].
Definition mr_facts (nlo nhi llo lhi : Z) : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (SA_SB, mkAF SB SB 0);
         (SA_C, mkAF 4096 (2 ^ 47 - SP.SEG_M_SIZE) 4);
         (SA_N, mkAF nlo nhi 0); (SA_R, mkAF 0 (2 ^ 32 - 2) 0); (11%nat, mkAF llo lhi 0)] [] [].
Definition mr_ss (wn : bool) (nlo nhi llo lhi : Z) : sstate :=
mkSS MR_E sr_atoms (mr_regions wn) None (mr_facts nlo nhi llo lhi).
Definition mr_extra (n r : Z) : list word := [Z_to_bv 64 SB; Z_to_bv 64 n; Z_to_bv 64 r].

(* ---------- small arithmetic the walk needs ---------- *)
(* a 4-byte cell holds a value modulo 2 ^ 32: what the `lw` / `addi` / `sw` of a u32 counter stores *)
Lemma mr_val4_mod : forall (rd : reader) a v v', sa_val rd a 4 v -> v mod 2 ^ 32 = v' mod 2 ^ 32 -> sa_val rd a 4 v'.
Proof.
intros rd a v v' H E k Hk. rewrite (H k Hk). f_equal. unfold le_byte.
change (8 * Z.of_nat 4) with 32. rewrite E. reflexivity.
Qed.
(* the u32 counter step the code runs twice (refused, n_kept): `lw` sign-extends the cell, `addi 1` adds and `sw`
   keeps the low 32 bits, so the cell holds the counter + 1 whenever that is below 2 ^ 32 *)
Lemma mr_mm32 : forall a : Z, (a mod 2 ^ 64) mod 2 ^ 32 = a mod 2 ^ 32.
Proof.
intros a. rewrite <- Znumtheory.Zmod_div_mod; [reflexivity | lia | lia | exists (2 ^ 32); reflexivity].
Qed.
Lemma mr_swrap32 : forall z, bv_swrap 32 z mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
intros z. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2 ^ 32).
change (bv_half_modulus 32) with (2 ^ 31). rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.
Lemma mr_incr32 : forall r, 0 <= r <= 2 ^ 32 - 2 ->
zcanon (zalu_raw 63 64 ALU_ADD (zcanon (bv_swrap 32 (zcanon r mod 2 ^ Z.of_N 32))) (zcanon 1)) mod 2 ^ 32 = r + 1.
Proof.
intros r Hr. unfold zcanon, M64. change (2 ^ Z.of_N 32) with (2 ^ 32). cbn [zalu_raw].
rewrite (Z.mod_small r (2 ^ 64)) by lia.
rewrite (Z.mod_small r (2 ^ 32)) by lia.
rewrite (Z.mod_small 1 (2 ^ 64)) by lia.
rewrite mr_mm32, Zplus_mod, mr_mm32, mr_swrap32, <- Zplus_mod.
apply Z.mod_small. lia.
Qed.
(* a field read through the ASan reader is the same field of the restricted memory (ieqA.v's ie_val_mem_of_sa_val) *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mr_val_mem : forall segs H mem a n v,
sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
(* and the converse, for a cell the run wrote (rbc's rbc_sa_val11, general in the value) *)
Lemma mr_sa_val_of : forall segs H mem a n v,
val_mem segs (mrestrict H mem) a n v -> sa_val (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.
End r.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the environment of the walk: the registers, then the three extra atoms *)
Definition mr_E (regs : bvmap 5 word) (n r : Z) : env := Eimg (Ereg regs (mr_extra n r)).
Section e.
Variable B : asyms.
(* the record hypotheses: PALib (SegPaLib.v; SegRecRest.v seg_palib gives it at PB_seg) and the listing's objects
   against the image's addresses (SegObj.v; SegRecRest.v seg_val_objs_PB) *)
Hypothesis TL : PALib B.
Hypothesis VOBJS : seg_val_objs.
(* the snprintf wrapper, row 4 of the image-A wrapper lane's interface at image B (lib/B/Rt/RtPFSeg.v
   seg_asnprintf_realizes, at RtPFCmd's image constants and the listing's call target), at every FP state: the
   wrapper returns a state whose rounding mode may be 0, so the walk's post is apost_baseF *)
Hypothesis SNP : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR
    (SIGMA SS___interceptor_trampoline_snprintf) RtPFCmd.CMD_GOTW RtAPI.A_SSP_GUARD.
(* the awr_ok goal of a token run of the n_kept < 8 arms: the frame, the two read-only shadow regions and the two
   counter cells, each byte of them in the call's footprint (m_refuse_W) *)
Ltac mr_awrK Usp Uc Hcwr HSTK :=
lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
  let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0);
[ reflexivity
| cbn [base_val]; repeat (rewrite ew_ewset_other by lia); rewrite Usp; lia
| cbn [YP09.r_wlo]; rewrite HSTK; lia | cbn [YP09.r_whi]; lia |];
apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 10%nat _);
[ reflexivity
| cbn [base_val]; repeat (rewrite ew_ewset_other by lia); exact Uc
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
  apply (Hcwr _ _ _ _ _ a);
  [ eexists; split;
    [right; right; left; reflexivity | cbn [fst snd]; unfold SP.MC_REFUSED in *; lia]
  | unfold SP.MC_REFUSED, SP.SEG_M_SIZE in *; lia ] |];
eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 10%nat _);
[ reflexivity
| cbn [base_val]; repeat (rewrite ew_ewset_other by lia); exact Uc
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
  apply (Hcwr _ _ _ _ _ a);
  [ eexists; split;
    [right; left; reflexivity | cbn [fst snd]; unfold SP.MC_NKEPT in *; lia]
  | unfold SP.MC_NKEPT, SP.SEG_M_SIZE in *; lia ] |];
apply awr_ok_nil.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

(* 0x87888 `blez a4` (a4 = line): the branch the `%s:%d: ` and `%s: ` arms split at. The executor cannot decide it
   (line is only bounded), so the walk splits it and reads the condition here. *)
Lemma mr_blez : forall (E : env) x (b : bool), ew E 11 = Z_to_bv 64 x -> 0 <= x < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff 11 0)) = b -> if b then x = 0 else 0 < x.
Proof.
intros E x b E11 Hx Hb.
rewrite YO0c.branch_ge in Hb.
change (bv_unsigned (sv_denot E (SLit 0))) with (U E (SLit 0)) in Hb.
change (bv_unsigned (sv_denot E (SOff 11 0))) with (U E (SOff 11 0)) in Hb.
rewrite U_SLit, (U_atom E 11 x E11 ltac:(lia)) in Hb.
rewrite (zcanon_id 0) in Hb by (unfold M64; lia).
rewrite (YO0b.s64_small 0 ltac:(lia)), (YO0b.s64_small x ltac:(lia)) in Hb.
destruct b.
- apply Bool.negb_true_iff, Z.ltb_ge in Hb. lia.
- apply Bool.negb_false_iff, Z.ltb_lt in Hb. lia.
Qed.
(* 0x878b0 and 0x878fc `bltu a3,a1`, a3 = ~(c + 0x200c) and a1 = 112 n_kept (the UBSan check that the address of
   kept[n_kept] does not wrap): the complement of an address below alloc_ceiling is far above 112 * 7 *)
Lemma mr_ub_wrap : forall (E : env) cc n,
ew E 10 = Z_to_bv 64 cc -> ew E 33 = Z_to_bv 64 n ->
0 <= cc -> cc + SP.SEG_M_SIZE <= alloc_ceiling -> 0 <= n <= 7 ->
branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff 10 8204) (SLit (-1))))
                    (sv_denot E (SMd M_MUL (SOff 33 0) (SLit 112))) = false.
Proof.
intros E cc n E10 E33 H0 Hc Hn. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold SP.SEG_M_SIZE in Hc.
rewrite branch_ltu_U.
rewrite (U_not_off E 10 cc 8204 E10 ltac:(lia) ltac:(lia)).
rewrite U_SMd, (U_atom E 33 n E33 ltac:(lia)), U_SLit.
cbn [zmd_raw]. rewrite (zcanon_id 112) by (unfold M64; lia).
rewrite (zcanon_id (n * 112)) by (unfold M64; lia).
apply Z.ltb_ge. lia.
Qed.
(* the UBSan wrap trap of kept[n_kept]'s address, refuted at its branch *)
Ltac mr_nowrap E10 E33 :=
lazymatch goal with
| Hc : branch_taken _ (sv_denot ?Eb _) _ = true |- _ =>
  let B10 := fresh "B10" in let B33 := fresh "B33" in
  assert (B10 : ew Eb 10 = Z_to_bv 64 ltac:(lazymatch type of E10 with ew _ _ = Z_to_bv 64 ?v => exact v end))
    by (repeat (rewrite ew_ewset_other by lia); exact E10);
  assert (B33 : ew Eb 33 = Z_to_bv 64 ltac:(lazymatch type of E33 with ew _ _ = Z_to_bv 64 ?v => exact v end))
    by (repeat (rewrite ew_ewset_other by lia); exact E33);
  rewrite (mr_ub_wrap Eb _ _ B10 B33 ltac:(lia) ltac:(lia) ltac:(lia)) in Hc; discriminate Hc
end.

(* the entry state of the walk: the two counters as regions with their values, the GOT word and the shadow cell *)
Lemma mr_entry : forall wn nlo nhi llo lhi ly S W (regs : bvmap 5 word) mem md ch c line n r,
afn_pre SEGS B MR_STK ly S W regs mem md ch ->
getr regs 10 = w64 c -> getr regs 11 = w64 line ->
4096 <= c -> c mod 16 = 0 -> c + SP.SEG_M_SIZE <= alloc_ceiling ->
(* the block is off the image (AR's blk_off_imgP), so it does not meet the GOT word or the shadow cell *)
(c + SP.SEG_M_SIZE <= 0x10000 \/ kImgEnd <= c) ->
(* and apart from the shadow band (AR's in_app) *)
(c + SP.SEG_M_SIZE <= kLowShadowBeg \/ kHighMemBeg <= c) ->
sa_addr (rdW W mem) c SP.SEG_M_SIZE ->
(forall a, c <= a < c + SP.SEG_M_SIZE -> apresent (w_H W) mem a) ->
sa_val (rdW W mem) (c + SP.MC_NKEPT) 4 n -> nlo <= n <= nhi -> 0 <= n < 2 ^ 32 ->
sa_val (rdW W mem) (c + SP.MC_REFUSED) 4 r -> 0 <= r <= 2 ^ 32 - 2 ->
llo <= line <= lhi -> 0 <= line < 2 ^ 32 ->
st_ok_pi SEGS VAL (mr_E regs n r) (mr_ss wn nlo nhi llo lhi)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + MR_E)) mem (seg_rom SEGS)))
/\ sh_ok SEGS mr_Bx mr_SH (mr_E regs n r) (mrestrict (w_H W) mem).
Proof.
intros wn nlo nhi llo lhi ly S W regs mem md ch c line n r HPRE H10 H11 Hc4096 Hc16 Hcceil Hcimg Hcband HADDR HPRES
  HN HNb HN32 HR HRb HLb HL32.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : MR_STK = 8240) by (vm_compute; reflexivity).
destruct HADDR as (_ & _ & _ & HRA & _).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
unfold kImgEnd in *.
rewrite restrict_mkst_fx.
set (E := mr_E regs n r).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mr_E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (mr_extra n r)) k)
by (intros k Hk; unfold E, mr_E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 line)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E0o : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
by (unfold E, mr_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
by (unfold E, mr_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Uc : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; unfold SP.SEG_M_SIZE in *; lia).
assert (Ul : bv_unsigned (ew E 11) = line) by (rewrite E11; apply unsigned_lit_small; lia).
assert (USB : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (Un : bv_unsigned (ew E 33) = n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (Ur : bv_unsigned (ew E 34) = r) by (rewrite E34; apply unsigned_lit_small; lia).
assert (UBx : U E mr_Bx = SHADOW_OFF).
{ unfold mr_Bx, SA_SB. rewrite U_SOff, E32, Z.add_0_r, unsigned_lit_small by (unfold SB; lia).
  rewrite zcanon_id by (unfold SB, M64; lia). reflexivity. }
assert (UC : U E (SOff SA_C 0) = c).
{ unfold SA_C. rewrite U_SOff, E10, Z.add_0_r, unsigned_lit_small by (unfold SP.SEG_M_SIZE in *; lia).
  apply zcanon_id. unfold M64, SP.SEG_M_SIZE in *. lia. }
split.
- unfold mr_ss, mr_regions. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + destruct wn; vm_compute; reflexivity.
  + unfold stack_region, got_regionP, bcell_regionP, mr_refused, mr_nkept.
    repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. unfold MR_FRAME. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite HSTK in *. lia.
    * cbn [base_val]. rewrite E0o, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 0)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); pose proof (pa_val_range (A_OBJ 12)); lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * cbn [base_val]. rewrite E12, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff SA_SB 0) SB);
      [cbn [sv_denot]; unfold SA_SB; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SB; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * cbn [base_val]. unfold SA_C. rewrite E10, unsigned_lit_small by (unfold SP.SEG_M_SIZE in *; lia).
      unfold SP.MC_REFUSED, SP.SEG_M_SIZE in *. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPRES; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ c SP.MC_REFUSED 4 (SOff SA_R 0) r);
      [cbn [sv_denot]; unfold SA_R; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); unfold SP.MC_REFUSED; lia | cbn; lia |].
      change (N.to_nat 4) with 4%nat. exact (mr_val_mem SEGS (w_H W) mem (c + SP.MC_REFUSED) 4 r HR).
    * cbn [base_val]. unfold SA_C. rewrite E10, unsigned_lit_small by (unfold SP.SEG_M_SIZE in *; lia).
      unfold SP.MC_NKEPT, SP.SEG_M_SIZE in *. split; [lia|]. split; [destruct wn; lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPRES; destruct wn; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ c SP.MC_NKEPT 4 (SOff SA_N 0) n);
      [cbn [sv_denot]; unfold SA_N; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); unfold SP.MC_NKEPT; lia | cbn; lia |].
      change (N.to_nat 4) with 4%nat. exact (mr_val_mem SEGS (w_H W) mem (c + SP.MC_NKEPT) 4 n HN).
  + apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, mr_refused, mr_nkept, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. unfold SA_C.
    rewrite E10, E0o, E12, !unsigned_lit_small
      by (pose proof (pa_val_range (A_OBJ 0)); pose proof (pa_val_range (A_OBJ 12));
          unfold SP.SEG_M_SIZE in *; lia).
    rewrite Usp.
    rewrite (VOBJS 0%nat ltac:(vm_compute; lia)), (VOBJS 12%nat ltac:(vm_compute; lia)).
    cbn [nth seg_objs]. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold MR_FRAME, SP.MC_REFUSED, SP.MC_NKEPT, SP.SEG_M_SIZE in *. rewrite HSTK in *.
    repeat split; first [exact I | lia].
  + split; [|split; [exact I | exact I]].
    cbn [mr_facts f_atoms atoms_ok]. unfold afact_ok, SA_SB, SA_N, SA_R, SA_C. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uc, Ul, USB, Un, Ur.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SP.SEG_M_SIZE in *. rewrite HSTK in *.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia; try exact Hc16.
- unfold sh_ok, mr_SH. repeat apply Forall_cons; try apply Forall_nil.
  + apply (shent_ok_of_range SEGS (w_H W) mem E mr_Bx SA_C c SP.SEG_M_SIZE c SP.MC_REFUSED (SP.MC_REFUSED + 4));
    [exact HRA | exact UBx | exact UC | unfold SP.MC_REFUSED, SP.SEG_M_SIZE; lia
    | unfold SP.MC_REFUSED, SP.SEG_M_SIZE; lia
    | intros x Hx; cbn [Z.min Z.max] in Hx;
      unfold SP.MC_REFUSED, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, SP.SEG_M_SIZE in *; lia].
  + apply (shent_ok_of_range SEGS (w_H W) mem E mr_Bx SA_C c SP.SEG_M_SIZE c SP.MC_NKEPT (SP.MC_NKEPT + 4));
    [exact HRA | exact UBx | exact UC | unfold SP.MC_NKEPT, SP.SEG_M_SIZE; lia
    | unfold SP.MC_NKEPT, SP.SEG_M_SIZE; lia
    | intros x Hx; cbn [Z.min Z.max] in Hx;
      unfold SP.MC_NKEPT, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, SP.SEG_M_SIZE in *; lia].
Qed.

(* where the mconf block lies: the facts AR gives about the live heap block that holds it (m_refuse_pre's sa_heap) *)
Lemma mr_blk : forall ly S W mem md c,
AR SEGS B ly S W mem md -> sa_heap B ly S c SP.SEG_M_SIZE ->
4096 <= c /\ c + SP.SEG_M_SIZE <= alloc_ceiling /\
(c + SP.SEG_M_SIZE <= 0x10000 \/ kImgEnd <= c) /\
(c + SP.SEG_M_SIZE <= kLowShadowBeg \/ kHighMemBeg <= c) /\
(forall a, c <= a < c + SP.SEG_M_SIZE -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
(forall STK sp0 FP fr0 own a, inFP FP a -> c <= a < c + SP.SEG_M_SIZE ->
   awr_byte SEGS B STK sp0 FP (ablocks B ly S) (ablocks B ly S) fr0 ly own a).
Proof.
intros ly S W mem md c HAR (b & m & Hin & Hlo & Hhi).
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hm).
pose proof (blk_off_imgP B ly S W mem md b m HAR Hin) as Himg.
pose proof (req_size_pos m ltac:(lia)) as [Hr1 Hr2].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, off_img in *.
split; [lia|]. split; [lia|]. split; [unfold kImgEnd; lia|].
split; [unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia|].
split; [intros a Ha; exact (Hbpres a ltac:(lia))|].
intros STK sp0 FP fr0 own a HFP Ha. unfold awr_byte. right; left.
split; [exact HFP|]. exists b, m. split; [exact Hin | lia].
Qed.


(* ---------- the post of the walk, and the three arms ---------- *)
(* the contract's post at image B's numbers; every arm proves it *)
Definition mr_Q (c line : Z) (mc : SM.mconf) (knock : bool) (ly : alayout) (S : astate) (W : world SEGS)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : world SEGS -> config -> Prop :=
apost_baseF SEGS B MR_STK (m_refuse_W c mc) regs ly S W mem md EV_m_refuse
(fun ly' S' W' regs' mem' md' =>
 sa_mconf (rdW W' mem') c (SM.m_refuse mc line knock) /\
 sa_kept SEGS W mem W' mem' regs MR_STK
 (fun a =>
  (Z.of_nat (length (SM.mc_kept mc)) < 8 /\
   SP.kept_addr c (length (SM.mc_kept mc)) <= a <
   SP.kept_addr c (length (SM.mc_kept mc)) + SP.MC_KEPT_LEN) \/
  (Z.of_nat (length (SM.mc_kept mc)) < 8 /\ c + SP.MC_NKEPT <= a < c + SP.MC_NKEPT + 4) \/
  c + SP.MC_REFUSED <= a < c + SP.MC_REFUSED + 4) /\
 sa_noalloc B ly S ly' S').
(* one arm of the walk: the contract's premises, with P picking the arm (n_kept = 8, or n_kept < 8 and the sign
   of line, which is what the `blez a4` at 0x87888 splits on) *)
Definition MR_ARM (P : Z -> nat -> Prop) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch c line mc knock,
afn_pre SEGS B MR_STK ly S W regs mem md ch ->
arodata_okP SEGS SegInstB.RLO_A SegInstB.RHI_A B (rdW W mem) ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 -> getr regs 11 = w64 line ->
m_refuse_pre SEGS B ly S (rdW W mem) SegInstB.seg_litA_fz RtPFCmd.CMD_GOTW RtAPI.A_SSP_GUARD c line mc knock ->
P line (length (SM.mc_kept mc)) ->
SRr SEGS W (cfg_at SEGS (BASE + MR_E) regs mem md) (mr_Q c line mc knock ly S W regs mem md).
(* n_kept = 8: only refused++ (this file) *)
Definition MR_FULL_stmt : Prop := MR_ARM (fun _ n => n = 8%nat).
(* n_kept < 8 and line = 0: the "%s: " arm, the call at 0x8791c (lib/B/Prog/m_refuse_l0.v) *)
Definition MR_KEPT0_stmt : Prop := MR_ARM (fun line n => line = 0 /\ (n < 8)%nat).
(* n_kept < 8 and line > 0: the "%s:%d: " arm, the call at 0x878d0 (lib/B/Prog/m_refuse_ln.v) *)
Definition MR_KEPTL_stmt : Prop := MR_ARM (fun line n => 0 < line /\ (n < 8)%nat).

(* n_kept = 8 (the blt at 0x87884 is taken): the walk reads n_kept, jumps to the join, and only bumps refused *)
Lemma mr_walk_full : forall ly S W (regs : bvmap 5 word) mem md ch c line mc knock,
afn_pre SEGS B MR_STK ly S W regs mem md ch ->
getr regs 10 = w64 c -> getr regs 11 = w64 line ->
c mod 16 = 0 -> sa_heap B ly S c SP.SEG_M_SIZE -> sa_addr (rdW W mem) c SP.SEG_M_SIZE ->
sa_mconfp knock (rdW W mem) c mc -> length (SM.mc_kept mc) = 8%nat ->
SM.mc_refused mc + 1 < 2 ^ 32 -> 0 <= line <= 65536 ->
SRr SEGS W (cfg_at SEGS (BASE + MR_E) regs mem md)
(apost_base SEGS B MR_STK [(c + SP.MC_REFUSED, c + SP.MC_REFUSED + 4)] regs ly S W mem md EV_m_refuse
(fun ly' S' W' regs' mem' md' =>
 sa_mconf (rdW W' mem') c (SM.m_refuse mc line knock) /\
 sa_kept SEGS W mem W' mem' regs MR_STK (fun a => c + SP.MC_REFUSED <= a < c + SP.MC_REFUSED + 4) /\
 sa_noalloc B ly S ly' S')).
Proof.
intros ly S W regs mem md ch c line mc knock HPRE H10 H11 Hc16 HHEAP HADDR HMC H8 HRF Hline.
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : MR_STK = 8240) by (vm_compute; reflexivity).
destruct (mr_blk ly S W mem md c HAR HHEAP) as (Hc4096 & Hcceil & Hcimg & Hcband & Hcpres & Hcwr).
destruct (MF.mr_fields knock (rdW W mem) c mc HMC) as (Hk8 & HNV & HRb & HRV & Hrd96 & Hrdb & Hrdbytes & Hblkmap).
rewrite H8 in HNV. change (Z.of_nat 8) with 8 in HNV.
destruct (mr_entry false 8 8 0 65536 ly S W regs mem md ch c line 8 (SM.mc_refused mc)
  HPRE H10 H11 Hc4096 Hc16 Hcceil Hcimg Hcband HADDR (fun a Ha => proj1 (Hcpres a Ha))
  HNV ltac:(lia) ltac:(lia) HRV ltac:(lia) ltac:(lia) ltac:(lia)) as [HS SHOK].
pose proof (ajournal_init SEGS B MR_STK [(c + SP.MC_REFUSED, c + SP.MC_REFUSED + 4)] ly S W regs mem md ch HPRE)
  as HJ.
remember (mr_E regs 8 (SM.mc_refused mc)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mr_E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (mr_extra 8 (SM.mc_refused mc))) k)
by (intros k Hk; subst E; unfold mr_E; apply Eimg_low; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E34 : ew E 34 = Z_to_bv 64 (SM.mc_refused mc))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (HAE : env_agree 32 (Ereg regs (mr_extra 8 (SM.mc_refused mc))) E)
by (split; [intros k Hk; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Uc : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; unfold SP.SEG_M_SIZE in *; lia).
clear HE.
unfold cfg_at. change (w64 (BASE + MR_E)) with (Z_to_bv 64 (BASE + MR_E)).
paj_run_tok RUN HS HJ SHOK mr_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0);
  [ reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo]; rewrite HSTK; lia | cbn [YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 10%nat c);
  [ reflexivity | exact Uc
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
    apply (Hcwr MR_STK (spZ regs) [(c + SP.MC_REFUSED, c + SP.MC_REFUSED + 4)] (frames S) [] a);
    [ exists (c + SP.MC_REFUSED, c + SP.MC_REFUSED + 4); split;
      [left; reflexivity | cbn [fst snd]; unfold SP.MC_REFUSED in *; lia]
    | unfold SP.MC_REFUSED, SP.SEG_M_SIZE in *; lia ] |].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil. }
(* the run's env Ev is E with the fresh atoms the token run added *)
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ (restrict _ _) |- _ => set (Ev := Ex) in * end.
assert (EV1 : ew Ev 1 = getr regs 1)
by (unfold Ev; repeat (rewrite ew_ewset_other by lia); exact E1).
assert (EV2 : bv_unsigned (ew Ev 2) = spZ regs)
by (unfold Ev; repeat (rewrite ew_ewset_other by lia); exact Usp).
assert (EV10 : bv_unsigned (ew Ev 10) = c)
by (unfold Ev; repeat (rewrite ew_ewset_other by lia); exact Uc).
assert (EV34 : ew Ev 34 = Z_to_bv 64 (SM.mc_refused mc))
by (unfold Ev; repeat (rewrite ew_ewset_other by lia); exact E34).
assert (HAEV : env_agree 32 (Ereg regs (mr_extra 8 (SM.mc_refused mc))) Ev).
{ unfold Ev. split.
  - intros k Hk. repeat (rewrite ew_ewset_other by lia). apply (proj1 HAE). lia.
  - cbn [ed ewset]. exact (proj2 HAE). }
(* the store at 0x87958 left refused + 1 in the cell (the `lw` sign-extends, the `sw` keeps the low 32 bits) *)
lazymatch goal with
| HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
  let rg := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ev ssx (restrict (w_H W) msc) 3%nat rg HS eq_refl) as HR3
end.
cbn [restrict ms_mem] in HR3.
pose proof (field_of_region_any (segs := SEGS) Ev _ 10%nat c _ 8200 8204 8200 8204 8200 4%N
  (SAlu ALU_ADD (SExt true 32 (SOff 34 0)) (SLit 1)) HR3 EV10 ltac:(cbn; left; reflexivity) ltac:(cbn; lia)) as VR.
assert (VRv : bv_unsigned (sv_denot Ev (SAlu ALU_ADD (SExt true 32 (SOff 34 0)) (SLit 1)))
              mod 2 ^ (8 * Z.of_N 4) = SM.mc_refused mc + 1).
{ change (bv_unsigned (sv_denot Ev (SAlu ALU_ADD (SExt true 32 (SOff 34 0)) (SLit 1))))
    with (U Ev (SAlu ALU_ADD (SExt true 32 (SOff 34 0)) (SLit 1))).
  rewrite U_SAlu, U_SExt, U_SLit, U_SOff, EV34, Z.add_0_r.
  rewrite unsigned_lit_small by lia.
  change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
  apply mr_incr32. lia. }
rewrite VRv in VR. cbn [N.to_nat] in VR.
assert (VRa : sa_val (rdW W (ms_mem ms)) (c + SP.MC_REFUSED) 4 (SM.mc_refused mc + 1))
by (apply mr_sa_val_of; unfold SP.MC_REFUSED; exact VR).
(* every byte outside the frame and the refused cell is kept *)
lazymatch goal with
| HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc),
  HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc2)) |- _ =>
  assert (HKEEP : forall a, 0 <= a < 2 ^ 64 ->
    ~ (c + SP.MC_REFUSED <= a < c + SP.MC_REFUSED + 4) -> ~ (spZ regs - MR_STK <= a < spZ regs) ->
    aview SEGS (w_H W) (ms_mem msc) a = aview SEGS (w_H W) mem a);
  [ intros a Ha HnP HnS;
    refine (kept_of_frame Ex rs (w_H W) m0 (ms_mem msc)
      (fun x => (c + SP.MC_REFUSED <= x < c + SP.MC_REFUSED + 4) \/ (spZ regs - MR_STK <= x < spZ regs))
      HFr _ a Ha _);
    [ intros bb wlo whi x Hin Hr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [ injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?EV2, ?EV10 in Hr; cbv beta;
          rewrite HSTK in *; unfold SP.MC_REFUSED in *; first [left; lia | right; lia] |]);
      destruct Hin
    | intros [Hq | Hq]; [exact (HnP Hq) | exact (HnS Hq)] ]
  | ]
end.
(* the ret at 0x87974 *)
lazymatch goal with
| HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  prreg HS (1%bv : bv 5) R1;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  intros mat'; unfold apost_base;
  exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
  split; [cbn [ms_regs]; rewrite R1, EV1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|];
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
  split;
  [ eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ regs (mr_extra 8 (SM.mc_refused mc)) HS);
    [ exact HAEV | vm_compute; reflexivity ] |]
end.
split.
{ (* the block holds m_refuse mc line knock *)
  apply (MF.mr_enc_full knock (rdW W mem) _ c mc line HMC H8 HRF).
  - cbn [ms_mem]. exact VRa.
  - intros a Ha Hn. cbn [ms_mem]. apply HKEEP; [unfold SP.SEG_M_SIZE in *; lia | exact Hn|].
    rewrite HSTK. unfold SP.SEG_M_SIZE in *. lia. }
split.
{ intros a Ha HnS HnE. cbn [ms_mem]. exact (HKEEP a Ha HnE HnS). }
split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs S). destruct S; reflexivity.
Qed.

(* the n_kept = 8 arm in the shape every arm has *)
Lemma mr_arm_full : MR_FULL_stmt.
Proof.
intros ly S W regs mem md ch c line mc knock HPRE HROD H10 Hc64 H11 HP H8.
pose proof HP as (Hc0 & Hc16 & HHEAP & HADDR & HMC & HTAIL & Hline & HRF & HFRM & HSSP & HLIT).
assert (HFP : m_refuse_W c mc = [(c + SP.MC_REFUSED, c + SP.MC_REFUSED + 4)]).
{ unfold m_refuse_W. rewrite H8.
  replace (Z.of_nat 8 <? 8) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
unfold mr_Q. rewrite HFP.
eapply SRr_mono.
- exact (mr_walk_full ly S W regs mem md ch c line mc knock HPRE H10 H11 Hc16 HHEAP HADDR HMC H8
    ltac:(lia) ltac:(lia)).
- cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & Hc' & HJ' & HPres' & HQ1 & HQ2 & HQ3).
  apply apost_baseF_of_base.
  exists ly', S', regs', mem', md'.
  split; [exact Hc'|]. split; [exact HJ'|]. split; [exact HPres'|].
  split; [exact HQ1|]. split; [|exact HQ3].
  intros a Ha HnS HnE. apply HQ2; [exact Ha | exact HnS |].
  intros Hq. apply HnE. right; right. exact Hq.
Qed.

End e.
End f.
End d.
