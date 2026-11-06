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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module names changed; 564 of its 639 lines of code are new or changed and 378 lines of the source are left out. *)
(* The "%s:%d: " arm of the walk of m_refuse on fuzz_segconf.asan-ubsan (image B, pin sha256 c3796c0b38f3...,
   entry 0x8782c): n_kept < 8 and line > 0, the snprintf call at 0x878d0 and the tail to the ret at 0x87974.
   mr_arm_keptL : MR_KEPTL_stmt B, the statement of lib/B/Prog/m_refuse_k.v (which carries the walk's kit: the
   entry state mr_entry, the block facts mr_blk, the branch lemmas mr_blez / mr_ub_wrap, the post mr_Q and the
   three arm statements). The sibling arm (line = 0, the call at 0x8791c) is lib/B/Prog/m_refuse_l0.v.

   ADAPTATION of the image-A m_file-family lane's image-A walk of the same function (lib/A/Prog/m_refuseA.v at
   commit 0e3b3a97f9af: the entry seed, the token runs, mr_snp's snprintf step and the
   tail), at image B's numbers and with image B's UBSan trap branches.

   The code this arm walks (the neutral listing of m_refuse in image B):
     0x8782c-0x87844  the 48-byte frame (ra s0 s1 s2 s3), a2 = c & 3
     0x87848 bnez a2 -> unimp         UBSan trap 1, not taken: c mod 16 = 0 (m_refuse_pre, atom 10's fact)
     0x8784c-0x87878  the shadow base through the GOT word, s0 = &refused, s1 = &n_kept, s3 = n_kept's shadow
                      byte, and the instrumented check of n_kept (a load of that shadow byte and a compare):
                      decided by mr_SH's n_kept entry, so the slow block 0x8797c and its error path (a call of
                      errpath_load4 at 0x8798c) are not reached
     0x8787c-0x87884  n_kept = lw 0(s1); blt 7,n_kept not taken (n_kept <= 7, atom 33's fact)
     0x87888          blez a4: not taken here (0 < line; the walk splits and mr_blez reads the condition)
     0x87890          bgeu n_kept,9 -> unimp, UBSan trap 2, not taken: n_kept <= 7 (atom 33's fact)
     0x878b0          bltu ~(c + 0x200c), 112 n_kept -> unimp, UBSan trap 3 (the address of kept[n_kept]
                      wrapping), refuted by mr_ub_wrap at its branch
     0x878b4-0x878d0  a0 = &kept[n_kept], a1 = 112, a2 = .str.7 (the listing's object 27, 0x210c0 =
                      SegInstB.seg_litA_fz SegModel.F_addr_line), a3 = c->reading, a4 = line; jal the snprintf
                      wrapper (ml_snp, row 4 of the interface at image B)
     0x878d4-0x8793c  j 0x87920; the check of n_kept twice (mr_SH again, slow blocks 0x879a4 / 0x879b8 not
                      reached), n_kept + 1 (addiw), blt n_kept+1,n_kept -> unimp, UBSan trap 6, not taken
                      (n_kept + 1 <= 8 < 2 ^ 31), sw n_kept+1,0(s1)
     0x87940-0x87974  the check of refused (mr_SH's refused entry, slow block 0x87990 not reached),
                      refused + 1, the frame restored, ret.
   Every write is inside the call's footprint m_refuse_W c mc: kept[n_kept] (what the wrapper writes), the
   n_kept cell and the refused cell, all three in the live heap block the contract names (sa_heap). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_refuse_k.

(* ---------- small facts, no state ---------- *)
(* m_refuse_W of an n_kept < 8 call, written out (the rewrite HFPk of the walk gives this list) *)
Definition ml_FP (c : Z) (mc : SM.mconf) : list (Z * Z) :=
[(SP.kept_addr c (length (SM.mc_kept mc)), SP.kept_addr c (length (SM.mc_kept mc)) + SP.MC_KEPT_LEN);
 (c + SP.MC_NKEPT, c + SP.MC_NKEPT + 4); (c + SP.MC_REFUSED, c + SP.MC_REFUSED + 4)].
(* a word read through two readers that agree on its 8 bytes (m_refuseA.v mr_rdword_kept) *)
Lemma ml_rdword_kept : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma ml_argZ3 : forall regs : bvmap 5 word, argZ regs 3 = bv_unsigned (getr regs 13).
Proof.
intros regs. unfold argZ. assert (E : Z_to_bv 5 (10 + 3) = (13%bv : bv 5)) by (apply bv_eq; reflexivity).
rewrite E. reflexivity.
Qed.
Lemma ml_argZ4 : forall regs : bvmap 5 word, argZ regs 4 = bv_unsigned (getr regs 14).
Proof.
intros regs. unfold argZ. assert (E : Z_to_bv 5 (10 + 4) = (14%bv : bv 5)) by (apply bv_eq; reflexivity).
rewrite E. reflexivity.
Qed.
(* a0 at the call: c + 0x200c + 112 n_kept = &kept[n_kept] (m_refuseA.v mr_a0_kept) *)
Lemma ml_a0_kept : forall E c n, ew E 10 = Z_to_bv 64 c -> ew E 33 = Z_to_bv 64 n -> 0 <= c -> c + 9236 < 2 ^ 63 ->
0 <= n <= 8 ->
alu64 ALU_ADD (Z_to_bv 64 (bv_unsigned (ew E 10) + 8204)) (mul_div M_MUL (ew E 33) (Z_to_bv 64 112)) =
w64 (c + 8204 + 112 * n).
Proof.
intros E c n H10 H33 Hc0 Hc Hn. apply bv_eq. rewrite alu64_unsigned, mul_div_unsigned.
rewrite H10, H33. cbn [zalu_raw zmd_raw]. unfold w64.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
repeat match goal with |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)) by lia end.
lia.
Qed.
Lemma ml_set_fs_id : forall S, S = set_fs (st_fs S) S.
Proof. intros S. destruct S. reflexivity. Qed.
(* the value a u32 counter cell holds after `lw` / `addiw 1` / `sw`, in the two shapes the executor leaves:
   the chunk SOff k 1 (the atom's range lets it drop the sign extension) and the explicit sign-extended add *)
Lemma ml_soff1 : forall E k v, ew E k = Z_to_bv 64 v -> 0 <= v -> v + 1 < 2 ^ 32 ->
bv_unsigned (sv_denot E (SOff k 1)) mod 2 ^ (8 * Z.of_N 4) = v + 1.
Proof.
intros E k v H Hv Hv1. cbn [sv_denot]. rewrite H.
replace (bv_unsigned (Z_to_bv 64 v) + 1) with (v + 1) by (rewrite unsigned_lit_small by lia; lia).
rewrite unsigned_lit_small by lia.
change (8 * Z.of_N 4) with 32. apply Z.mod_small. lia.
Qed.
Lemma ml_inc32 : forall E k v, ew E k = Z_to_bv 64 v -> 0 <= v <= 2 ^ 32 - 2 ->
bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff k 0)) (SLit 1))) mod 2 ^ (8 * Z.of_N 4) = v + 1.
Proof.
intros E k v H Hv.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff k 0)) (SLit 1))))
  with (U E (SAlu ALU_ADD (SExt true 32 (SOff k 0)) (SLit 1))).
rewrite U_SAlu, U_SExt, U_SLit, U_SOff, H, Z.add_0_r.
rewrite unsigned_lit_small by lia.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
apply mr_incr32. lia.
Qed.

(* the windows of a token run's regions: the frame [sp - 48, sp), refused and n_kept of the block at c (the GOT
   word and the shadow cell are read-only); a byte outside the three is kept by the run (kept_of_frame) *)
Ltac ml_win Usp Uc :=
  let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
  intros bb wlo whi x Hin Hr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [ injection Hq as <- <- <-; cbn [base_val] in Hr; repeat (rewrite ew_ewset_other in Hr by lia);
      rewrite ?Usp, ?Uc in Hr; cbv beta; first [left; lia | right; left; lia | right; right; lia | exfalso; lia] |]);
  destruct Hin.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation MR_STK := SegInstB.STK_m_refuse.
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SNP : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR
    (SIGMA SS___interceptor_trampoline_snprintf) RtPFCmd.CMD_GOTW RtAPI.A_SSP_GUARD.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
(* m_refuse_k.v's two tactics (an Ltac of a Section does not outlive it), copied verbatim: the awr_ok goal of a token
   run of the n_kept < 8 arms, and the refutation of the UBSan wrap trap of kept[n_kept]'s address *)
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
Ltac mr_nowrap E10 E33 :=
lazymatch goal with
| Hc : branch_taken _ (sv_denot ?Eb _) _ = true |- _ =>
  let B10 := fresh "B10" in let B33 := fresh "B33" in
  assert (B10 : ew Eb 10 = Z_to_bv 64 ltac:(lazymatch type of E10 with ew _ _ = Z_to_bv 64 ?v => exact v end))
    by (repeat (rewrite ew_ewset_other by lia); exact E10);
  assert (B33 : ew Eb 33 = Z_to_bv 64 ltac:(lazymatch type of E33 with ew _ _ = Z_to_bv 64 ?v => exact v end))
    by (repeat (rewrite ew_ewset_other by lia); exact E33);
  rewrite (mr_ub_wrap (rc := rc) Eb _ _ B10 B33 ltac:(lia) ltac:(lia) ltac:(lia)) in Hc; discriminate Hc
end.

(* the snprintf call at 0x878d0, snprintf(kept[n_kept], 112, "%s:%d: ", c->reading, line): the format .str.7 is the
   listing's object 27 (0x210c0 = seg_litA_fz SM.F_addr_line), the text MF.mr_text mc line (MF.mr_text_al), through
   row 4 at image B (RtPFSeg.seg_asnprintf_realizes = RtPFCmd.cmd_asnprintf_realizes at FR_seg), stepped by PaFx.v's
   aj_art_own_atF / srr_art_postF_of_pf (the image-A m_file-family lane's image-A m_refuseA.v mr_snp pattern). The destination is
   kept[n_kept] in the footprint's first range and in the live heap block; the memory at the call is the entry's
   outside the frame and the two counter cells (KEEPT). *)
Lemma ml_snp : forall W regsT memT mdc ly S mem md regs ch c line mc knock raw,
afn_pre SEGS B MR_STK ly S W regs mem md ch ->
arodata_okP SEGS SegInstB.RLO_A SegInstB.RHI_A B (rdW W mem) ->
m_refuse_pre SEGS B ly S (rdW W mem) SegInstB.seg_litA_fz RtPFCmd.CMD_GOTW RtAPI.A_SSP_GUARD c line mc knock ->
0 < line -> (length (SM.mc_kept mc) < 8)%nat ->
ajournal SEGS B MR_STK (spZ regs) (ml_FP c mc) ly S W mem md [] ly S W memT mdc 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (c + 9132 <= a < c + 9136) ->
  ~ (spZ regs - 48 <= a < spZ regs) -> rdW W memT a = rdW W mem a) ->
spZ regsT = spZ regs - 48 -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 10 = w64 (SP.kept_addr c (length (SM.mc_kept mc))) -> getr regsT 11 = w64 112 ->
getr regsT 12 = w64 (SegInstB.seg_litA_fz SM.F_addr_line) ->
getr regsT 13 = w64 (c + SP.MC_READING) -> getr regsT 14 = w64 line ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fx fx1 /\
 c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal SEGS B MR_STK (spZ regs) (ml_FP c mc) ly S W mem md [] ly S W mem2 md2 0 /\
 aregs_preserved regsT regs2 /\
 (getr regs2 10 = w64 (Z.of_nat (length (MF.mr_text mc line))) /\
  forall i, 0 <= i < RtPFShared.sn_len (112 - 1) (MF.mr_text mc line) ->
   rdW W mem2 (SP.kept_addr c (length (SM.mc_kept mc)) + i) =
   Some (nth (Z.to_nat i) (RtPFShared.sn_bytes (112 - 1) (MF.mr_text mc line)) 0)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 - RtPFSeg.SEG_SNP_K <= a < spZ regs - 48) ->
  ~ (SP.kept_addr c (length (SM.mc_kept mc)) <= a <
     SP.kept_addr c (length (SM.mc_kept mc)) + RtPFShared.sn_len (112 - 1) (MF.mr_text mc line)) ->
  rdW W mem2 a = rdW W memT a)).
Proof.
intros W regsT memT mdc ly S mem md regs ch c line mc knock raw
  HPRE HROD HMR Hl0 Hlt HJ KEEPT Tsp T1 Traw T3 T4 T10 T11 T12 T13 T14.
destruct HMR as (Hc0 & Hc16 & HHEAP & HADDR & HMC & HTAIL & Hline & Href & HFRM & HSSP & HLIT).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : MR_STK = 8240) by (vm_compute; reflexivity).
assert (HK : RtPFSeg.SEG_SNP_K = 8192) by (vm_compute; reflexivity).
rewrite HSTK in Hslo.
destruct (mr_blk B ly S W mem md c HAR HHEAP) as (Hc4096 & Hcceil & Hcimg & Hcband & Hcpres & Hcwr).
destruct HHEAP as (b & m & Hin & Hb1 & Hb2).
pose proof (proj1 HJ) as HARc.
destruct (al_blocks _ _ LAWS ly S W memT mdc b m HARc Hin) as (_ & _ & _ & _ & Hbpres & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [Hr1 Hr2].
destruct (MF.mr_fields knock (rdW W mem) c mc HMC) as (_ & _ & _ & _ & Hrd96 & Hrdb & Hrdbytes & Hblkmap).
unfold SP.SEG_M_SIZE in *. unfold kImgEnd in Hcimg.
(* the slack after the block's last byte: c and alloc_ceiling are both 16-aligned (the ceiling is page-aligned),
   so c + 9236 <= alloc_ceiling gives c + 9248 <= alloc_ceiling, which covers the reading's read span *)
pose proof (@YG0f.ASAN_CEIL_range _) as [CR1 CR2]. unfold YG0f.ASAN_CEIL in CR1, CR2.
assert (Hc16c : alloc_ceiling mod 16 = 0).
{ pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)) as D. rewrite CR2, Z.add_0_r in D.
  replace alloc_ceiling with (256 * (alloc_ceiling / 4096) * 16) by lia.
  apply Z_mod_mult. }
assert (Hceil4 : c + 9248 <= alloc_ceiling).
{ pose proof (Z.div_mod c 16 ltac:(lia)) as Dc. rewrite Hc16 in Dc.
  pose proof (Z.div_mod alloc_ceiling 16 ltac:(lia)) as Da. rewrite Hc16c in Da. lia. }
(* the text: "%s:%d: " of the reading and line, at most 104 bytes, so all of it and its NUL are written *)
assert (HT : MF.mr_text mc line = SM.fmt SM.F_addr_line [SM.AS (SM.mc_reading mc); SM.AI line]).
{ unfold MF.mr_text. replace (0 <? line) with true by (symmetry; apply Z.ltb_lt; exact Hl0). reflexivity. }
pose proof (MF.mr_text_len mc line Hrd96 Hline) as HTL.
destruct (MF.mr_sn (MF.mr_text mc line) HTL) as [HsnB HsnL].
assert (HRN : ~ In 0 (SM.mc_reading mc)).
{ intros H0. rewrite Forall_forall in Hrdb. specialize (Hrdb 0 H0). lia. }
set (n := Z.of_nat (length (SM.mc_kept mc))) in *.
set (d := SP.kept_addr c (length (SM.mc_kept mc))) in *.
assert (Hd : d = c + 8204 + 112 * n) by (unfold d, n, SP.kept_addr, SP.MC_KEPT, SP.MC_KEPT_LEN; lia).
set (w := RtPFShared.sn_len (112 - 1) (MF.mr_text mc line)) in *.
assert (Hw : 1 <= w <= 105) by (unfold w; change (112 - 1) with 111; rewrite HsnL; lia).
set (f := SegInstB.seg_litA_fz SM.F_addr_line) in *.
assert (Hn0 : 0 <= n < 8) by (unfold n; lia).
set (rdg := SM.mc_reading mc) in *.
set (wr := c + SP.MC_READING) in *.
assert (Hwr : wr = c + 9140) by (unfold wr, SP.MC_READING; lia).
assert (Ec : c = 16 * (c / 16)) by (pose proof (Z.div_mod c 16 ltac:(lia)) as Hq; rewrite Hc16 in Hq; lia).
assert (Ese : (wr + Z.of_nat (length rdg)) - (wr + Z.of_nat (length rdg)) mod 8 =
  8 * ((wr + Z.of_nat (length rdg)) / 8)) by (pose proof (Z.div_mod (wr + Z.of_nat (length rdg)) 8 ltac:(lia)); lia).
assert (Hse : RtPFShared.str_end wr rdg <= c + 9240).
{ unfold RtPFShared.str_end. rewrite Ese. lia. }
assert (Hse0 : wr + Z.of_nat (length rdg) < RtPFShared.str_end wr rdg).
{ unfold RtPFShared.str_end. pose proof (Z.mod_pos_bound (wr + Z.of_nat (length rdg)) 8 ltac:(lia)). lia. }
assert (Hse8 : RtPFShared.str_end wr rdg <= wr + Z.of_nat (length rdg) + 8).
{ unfold RtPFShared.str_end. pose proof (Z.mod_pos_bound (wr + Z.of_nat (length rdg)) 8 ltac:(lia)). lia. }
assert (Htl : (c + 9236 - 1) mod 8 = 3).
{ rewrite Ec. replace (16 * (c / 16) + 9236 - 1) with (3 + (2 * (c / 16) + 1154) * 8) by lia.
  rewrite Z_mod_plus_full. reflexivity. }
(* the scratch window and the runtime-call pre-state at the call *)
destruct (ecall_pre_stk_at SEGS B RtPFSeg.SEG_SNP_K MR_STK (spZ regs) (ml_FP c mc) ly S W mem md []
  ly S W memT mdc 0 regsT (-48) HJ ltac:(lia) eq_refl ltac:(lia) ltac:(rewrite HK; unfold ESTACK; lia)
  ltac:(rewrite HK, HSTK; lia) ltac:(rewrite T1; exact Traw) T3 T4) as (HEC & HSLO & HSCR).
pose proof (SNP fx) as HA.
unfold RtPFSeg.seg_asnprintf_realizes, RtPFCmd.cmd_asnprintf_realizes in HA.
(* the image bytes at the call are the entry's: the block is off the image, the frame far above it *)
assert (KIMG : forall a, 0x10000 <= a < 0x602000 -> rdW W memT a = rdW W mem a).
{ intros a Ha. apply KEEPT; lia. }
(* rt_rom_view from the contract's arodata_okP (its in-segment arm) *)
assert (HROM : RtDefs.rt_rom_view SEGS B W memT).
{ intros a (sg & Hsg & Hwr' & Hr) Ho He.
  pose proof (pa_img_range a (ex_intro _ sg (conj Hsg Hr))) as Hia. unfold kImgEnd in Hia.
  rewrite (KIMG a Hia).
  exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hwr' Hr)))) Ho He). }
destruct HSSP as (HG1 & cval & HG2).
assert (HG1' : rdword (rdW W memT) RtPFCmd.CMD_GOTW = Some RtAPI.A_SSP_GUARD).
{ rewrite (ml_rdword_kept (rdW W mem)); [exact HG1|]. intros i Hi. apply KIMG. unfold RtPFCmd.CMD_GOTW. lia. }
assert (HG2' : rdword (rdW W memT) RtAPI.A_SSP_GUARD = Some cval).
{ rewrite (ml_rdword_kept (rdW W mem)); [exact HG2|]. intros i Hi. apply KIMG. unfold RtAPI.A_SSP_GUARD. lia. }
(* the format literal .str.7 *)
destruct (HLIT SM.F_addr_line ltac:(left; reflexivity)) as (Hf0 & ((HFZ & HFnz) & HFT) & HFP & HFR & HFI).
destruct (HFP ly S W memT mdc HARc) as (Hfa0 & Hfa63 & HFAM & HFRA & HFHV).
assert (Ef : f = 0x210c0) by (unfold f; vm_compute; reflexivity).
assert (Lf : Z.of_nat (length SM.F_addr_line) = 7) by (vm_compute; reflexivity).
(* the reading at the call *)
assert (HRDK : forall a, c + 9140 <= a < c + 9240 -> rdW W memT a = rdW W mem a).
{ intros a Ha. apply KEEPT; lia. }
assert (U13 : bv_unsigned (getr regsT 13) = wr) by (rewrite T13; unfold w64; apply unsigned_lit_small; lia).
assert (U14 : bv_unsigned (getr regsT 14) = line) by (rewrite T14; unfold w64; apply unsigned_lit_small; lia).
pose proof (amem8_of_block SEGS B LAWS ly S W memT mdc b m wr (Z.of_nat (length rdg) + 1) HARc Hin
  ltac:(lia) ltac:(lia) ltac:(lia)) as HAM8.
assert (HPTR : RtPFShared.pf_arg_asan (rdW W memT)
  (RtPFShared.snp_out RtPFSeg.SEG_SNP_K (spZ regsT) d w) wr (RtPFPf.APtr rdg)).
{ cbn [RtPFShared.pf_arg_asan]. split; [exact Hrdb|]. split; [lia|]. split; [lia|]. split.
  - intros i Hi. rewrite HRDK by lia.
    replace (wr + i) with (wr + Z.of_nat (Z.to_nat i)) by lia. apply Hrdbytes. lia.
  - split.
    + intros x Hx. rewrite HRDK by lia.
      destruct (Z_lt_le_dec x (c + 9236)) as [Hx1 | Hx1].
      * apply Hblkmap. lia.
      * apply HTAIL. rewrite Htl. lia.
    + split.
      { unfold RtPFShared.snp_out. rewrite Tsp, HK.
        repeat (apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|]). apply Forall_nil. }
      split; [apply (amem_range_of_block SEGS B LAWS ly S W memT mdc b m); [exact HARc | exact Hin | lia | lia]|].
      split; [apply (range_addressable_of_block SEGS B LAWS ly S W memT mdc b m); [exact HARc | exact Hin | lia | lia]|].
      apply (shadow_hull_vis_of_block SEGS B LAWS ly S W memT mdc b m); [exact HARc | exact Hin | lia | lia | lia]. }
(* the call *)
eapply SRr_mono.
{ eapply (aj_art_own_atF SEGS B LAWS pa_segs_low RtPFSeg.SEG_SNP_K (fun a => d <= a < d + w)
    (SIGMA SS___interceptor_trampoline_snprintf) W regsT memT MR_STK (spZ regs) (ml_FP c mc)
    ly S W mem md [] ly S mdc 0 (-48) raw _ HJ).
  - lia.
  - reflexivity.
  - lia.
  - rewrite HK; lia.
  - rewrite HK, HSTK; lia.
  - exact T1.
  - intros a Ha. apply (Hcwr MR_STK (spZ regs) (ml_FP c mc) (frames S) [] a).
    + exists (d, d + SP.MC_KEPT_LEN). split; [left; reflexivity | cbn [fst snd]; unfold SP.MC_KEPT_LEN; lia].
    + lia.
  - apply (srr_art_postF_of_pf SEGS B RtPFSeg.SEG_SNP_K ly S W regsT memT mdc _ d w
      (RtPFShared.sn_bytes (112 - 1) (MF.mr_text mc line)) (Z.of_nat (length (MF.mr_text mc line))) HSCR).
    apply (HA ly S W regsT memT mdc d 112 f [] (map (argZ regsT) [3; 4; 5; 6; 7] ++ []) (MF.mr_text mc line) cval
      HEC HSLO HSCR T10 T11 T12 HROM).
    + unfold RtPFCmd.CMD_SNP_CR. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    + unfold RtPFCmd.CMD_SNP_CR, RtPFShared.snp_out. fold w. rewrite Tsp, HK.
      repeat (apply Forall_cons; [repeat (apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|]); apply Forall_nil|]).
      apply Forall_nil.
    + exact HG1'.
    + exact HG2'.
    + unfold RtPFCmd.CMD_GOTW; lia.
    + unfold RtPFCmd.CMD_GOTW; lia.
    + unfold RtAPI.A_SSP_GUARD; lia.
    + unfold RtAPI.A_SSP_GUARD; lia.
    + unfold RtPFShared.snp_out. fold w. rewrite Tsp, HK.
      repeat (apply Forall_cons; [unfold zdisjoint, RtPFCmd.CMD_GOTW; cbn [fst snd]; lia|]). apply Forall_nil.
    + unfold RtPFShared.snp_out. fold w. rewrite Tsp, HK.
      repeat (apply Forall_cons; [unfold zdisjoint, RtAPI.A_SSP_GUARD; cbn [fst snd]; lia|]). apply Forall_nil.
    + split; [reflexivity | intros i Hi; cbn [length] in Hi; lia].
    + cbn [length Z.of_nat]. lia.
    + unfold RtPFShared.snp_out. fold w. rewrite Tsp, HK. cbn [length Z.of_nat].
      repeat (apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|]). apply Forall_nil.
    + (* the format family FR_seg: "%s:%d: " at object 27, the reading and line *)
      unfold RtPFSeg.FR_seg, RtPFSeg.seg_fam.
      exists SM.F_addr_line, MF.mr_qs_al, [RtPFPf.APtr rdg; RtPFPf.AInt line].
      split.
      { unfold RtPFShared.fmt_at. split; [lia|]. split.
        - intros i Hi. rewrite (KIMG (f + i)).
          + replace (f + i) with (f + Z.of_nat (Z.to_nat i)) by lia. apply HFZ. rewrite length_app. cbn [length]. lia.
          + destruct (HFI (f + i) ltac:(lia)) as (Himg & _). pose proof (pa_img_range _ Himg) as Hia.
            unfold kImgEnd in Hia. lia.
        - split.
          + unfold RtPFShared.snp_out. fold w. rewrite Tsp, HK.
            repeat (apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|]). apply Forall_nil.
          + split; [exact HFAM|]. split; [exact HFRA | apply HFHV; lia]. }
      split; [exact MF.mr_parse_al|].
      split; [unfold MF.mr_qs_al; repeat constructor|].
      split.
      { cbn [map app]. rewrite ml_argZ3, ml_argZ4, U13, U14.
        cbn [RtPFShared.pf_args_asan]. split; [exact HPTR|].
        split; [cbn [RtPFShared.pf_arg_asan]; split; [lia | reflexivity] | exact I]. }
      split; [rewrite HT; exact (MF.mr_text_al rdg line HRN Hline)|].
      split; [cbn; exact I|].
      split; [unfold RtPFCmd.CMD_IMG_LO; lia|].
      split; [unfold RtPFCmd.CMD_GOTW; lia|].
      split.
      { cbn [map app]. rewrite ml_argZ3, U13. cbn [RtPFCmd.cmd_args_slack].
        split; [unfold amem_range in *; lia | exact I]. }
      split; [discriminate|].
      cbn [map app]. rewrite ml_argZ3, U13. cbn [RtPFCmd.cmd_args_amem].
      split; [unfold amem_range in *; lia | exact I].
    + lia.
    + lia.
    + lia.
    + fold w. lia.
    + unfold RtPFShared.snp_out. fold w. rewrite Tsp, HK. cbn [pairwise].
      split; [|split; [apply Forall_nil | exact I]].
      apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
    + fold w. intros a Ha. destruct (Hbpres a ltac:(lia)) as [Hp Hno].
      split; [apply (apresent_writable SEGS); exact Hp|].
      split; [exact Hno|]. rewrite Tsp. unfold ESTACK. lia.
    + fold w. exact (amem8_of_block SEGS B LAWS ly S W memT mdc b m d w HARc Hin ltac:(lia) ltac:(lia) ltac:(lia)).
    + fold w. apply (range_addressable_of_block SEGS B LAWS ly S W memT mdc b m); [exact HARc | exact Hin | lia | lia].
    + fold w. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W memT mdc b m); [exact HARc | exact Hin | lia | lia | lia].
    + fold w. unfold zdisjoint, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI, kImgEnd. cbn [fst snd]. lia.
    + exact HFRM. }
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HP2 & HQ2 & HK2).
split; [reflexivity|]. exists fx1, regs2, mem2, md2.
split; [exact Hfx|]. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HQ2|].
intros a Ha H1 H2. apply (HK2 a Ha); [lia | exact H2].
Qed.

(* a byte outside the frame [sp - 48, sp) and the two counter cells is kept by a token run (kept_of_frame) *)
Lemma ml_kof : forall E rs H (m m' : word -> option byte) c sp,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi ->
     (fun x => (c + 8200 <= x < c + 8204) \/ (c + 9132 <= x < c + 9136) \/ (sp - 48 <= x < sp)) a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (c + 9132 <= a < c + 9136) ->
  ~ (sp - 48 <= a < sp) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' c sp HF HZ a Ha H1 H2 H3.
exact (kept_of_frame E rs H m m' _ HF HZ a Ha
  ltac:(intros [Hq|[Hq|Hq]]; [exact (H1 Hq) | exact (H2 Hq) | exact (H3 Hq)])).
Qed.

(* the "%s:%d: " arm: n_kept < 8 and line > 0 *)
Theorem mr_arm_keptL : MR_KEPTL_stmt B.
Proof.
intros ly S W regs mem md ch c line mc knock HPRE HROD H10 Hc64 H11 HP (Hl & H8).
pose proof HP as (Hc0 & Hc16 & HHEAP & HADDR & HMC & HTAIL & Hline & HRF & HFRM & HSSP & HLIT).
pose proof pa_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : MR_STK = 8240) by (vm_compute; reflexivity).
pose proof Hslo as Hslo8. rewrite HSTK in Hslo8.
destruct (mr_blk B ly S W mem md c HAR HHEAP) as (Hc4096 & Hcceil & Hcimg & Hcband & Hcpres & Hcwr).
assert (Hc9236 : c + 9236 <= alloc_ceiling) by (unfold SP.SEG_M_SIZE in Hcceil; exact Hcceil).
destruct (MF.mr_fields knock (rdW W mem) c mc HMC) as (Hk8 & HNV & HRb & HRV & Hrd96 & Hrdb & Hrdbytes & Hblkmap).
(* the struct's offsets and the call's window as numbers, for the arithmetic below *)
assert (HKL : SP.MC_KEPT_LEN = 112) by reflexivity.
assert (HNKo : SP.MC_NKEPT = 9132) by reflexivity.
assert (HRFo : SP.MC_REFUSED = 8200) by reflexivity.
assert (HSM : SP.SEG_M_SIZE = 9236) by reflexivity.
assert (HKK : RtPFSeg.SEG_SNP_K = 8192) by (vm_compute; reflexivity).
assert (Hcimg9 : c + 9236 <= 65536 \/ kImgEnd <= c) by (unfold SP.SEG_M_SIZE in Hcimg; exact Hcimg).
assert (Hcband9 : c + 9236 <= kLowShadowBeg \/ kHighMemBeg <= c)
  by (unfold SP.SEG_M_SIZE in Hcband; exact Hcband).
unfold kImgEnd in Hcimg9.
assert (Hdk : SP.kept_addr c (length (SM.mc_kept mc)) = c + 8204 + 112 * Z.of_nat (length (SM.mc_kept mc)))
  by (unfold SP.kept_addr, SP.MC_KEPT, SP.MC_KEPT_LEN; lia).
(* the text the call prints and the bytes it writes: at most 104 bytes, so all of it and its NUL *)
assert (HTL : (length (MF.mr_text mc line) <= 104)%nat) by (apply MF.mr_text_len; [exact Hrd96 | exact Hline]).
destruct (MF.mr_sn (MF.mr_text mc line) HTL) as [HsnB HsnL].
assert (Hw : 1 <= RtPFShared.sn_len 111 (MF.mr_text mc line) <= 105) by (rewrite HsnL; lia).
destruct HHEAP as (b & m & Hin & Hb1 & Hb2).
assert (Hb2' : c + 9236 <= b + m) by (unfold SP.SEG_M_SIZE in Hb2; exact Hb2).
destruct (mr_entry B TL VOBJS true 0 7 0 65536 ly S W regs mem md ch c line (Z.of_nat (length (SM.mc_kept mc)))
  (SM.mc_refused mc) HPRE H10 H11 Hc4096 Hc16 Hcceil Hcimg Hcband HADDR (fun a Ha => proj1 (Hcpres a Ha))
  HNV ltac:(lia) ltac:(lia) HRV ltac:(lia) ltac:(lia) ltac:(lia)) as [HS SHOK].
pose proof (ajournal_init SEGS B MR_STK (m_refuse_W c mc) ly S W regs mem md ch HPRE) as HJ.
remember (mr_E regs (Z.of_nat (length (SM.mc_kept mc))) (SM.mc_refused mc)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mr_E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat ->
  ew E k = ew (Ereg regs (mr_extra (Z.of_nat (length (SM.mc_kept mc))) (SM.mc_refused mc))) k)
by (intros k Hk; subst E; unfold mr_E; apply Eimg_low; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 line)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat (length (SM.mc_kept mc))))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (SM.mc_refused mc))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (HAE : env_agree 32 (Ereg regs (mr_extra (Z.of_nat (length (SM.mc_kept mc))) (SM.mc_refused mc))) E)
by (split; [intros k Hk; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Uc : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; unfold SP.SEG_M_SIZE in *; lia).
clear HE.
unfold mr_Q, cfg_at. change (w64 (BASE + MR_E)) with (Z_to_bv 64 (BASE + MR_E)).
assert (HFPk : m_refuse_W c mc =
  [(SP.kept_addr c (length (SM.mc_kept mc)), SP.kept_addr c (length (SM.mc_kept mc)) + SP.MC_KEPT_LEN);
   (c + SP.MC_NKEPT, c + SP.MC_NKEPT + 4); (c + SP.MC_REFUSED, c + SP.MC_REFUSED + 4)]).
{ unfold m_refuse_W. replace (Z.of_nat (length (SM.mc_kept mc)) <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity. }
rewrite HFPk in HJ |- *.
(* entry to 0x87888: the frame, a2 = c & 3 and trap 1 (bnez a2, not taken: c mod 16 = 0, atom 10's fact), the shadow
   base, s0 / s1 / s3, the instrumented check of n_kept (mr_SH's entry of n_kept: its shadow byte is 0, so the slow
   block 0x8797c and its error path are not reached), lw n_kept, blt 7,n_kept (not taken: n_kept <= 7, atom 33's
   fact) *)
paj_run_to_tok RUNTO HS HJ SHOK mr_Bspan MR_SNP1.
{ mr_awrK Usp Uc Hcwr HSTK. }
(* 0x87888 blez a4 (line) *)
psrr_branch_tok RUN BR HS SHOK mr_Bspan.
{ (* taken: line <= 0, which mr_blez makes line = 0, against 0 < line *)
  exfalso.
  lazymatch goal with Hc : branch_taken _ (sv_denot ?Eb _) _ = ?b |- _ =>
    assert (B11 : ew Eb 11 = Z_to_bv 64 line) by (repeat (rewrite ew_ewset_other by lia); exact E11);
    pose proof (mr_blez Eb line b B11 ltac:(lia) Hc) as Hlb; cbn in Hlb end.
  lia. }
(* line > 0: 0x8788c-0x878ac (bgeu n_kept,9 -> trap 2, not taken: n_kept <= 7, atom 33's fact), to the wrap check *)
paj_run_to_tok RUNTO HS HJ SHOK mr_Bspan MR_SNP1.
{ mr_awrK Usp Uc Hcwr HSTK. }
(* 0x878b0 bltu ~(c + 0x200c), 112 n_kept: trap 3, refuted by mr_ub_wrap *)
psrr_branch_tok RUN BR HS SHOK mr_Bspan.
{ exfalso. mr_nowrap E10 E33. }
(* 0x878b4-0x878cc: a0 = &kept[n_kept], a1 = 112, a2 = .str.7, a3 = c->reading (a4 = line); to the jal *)
paj_run_to_tok RUNTO HS HJ SHOK mr_Bspan MR_SNP1.
{ mr_awrK Usp Uc Hcwr HSTK. }
(* 0x878d0 jal: the call of the snprintf trampoline, ra = 0x878d4 *)
paj_run_tok RUN HS HJ SHOK mr_Bspan.
{ mr_awrK Usp Uc Hcwr HSTK. }
rewrite ?wvb_wvb in HJ.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14.
(* the register state at the call, as the contract reads it *)
assert (Tsp : spZ (ms_regs ms2) = spZ regs - 48).
{ unfold spZ at 1. rewrite Q2, Usp. rewrite unsigned_lit_small by lia. lia. }
assert (T3 : getr (ms_regs ms2) 3 = w64 (as_gp B))
  by (rewrite Q3, EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl); exact Hgp).
assert (T4 : getr (ms_regs ms2) 4 = w64 (as_tp B))
  by (rewrite Q4, EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl); exact Htp).
assert (T10 : getr (ms_regs ms2) 10 = w64 (SP.kept_addr c (length (SM.mc_kept mc)))).
{ rewrite Q10, (ml_a0_kept E c (Z.of_nat (length (SM.mc_kept mc))) E10 E33 ltac:(lia) ltac:(lia) ltac:(lia)).
  unfold SP.kept_addr, SP.MC_KEPT, SP.MC_KEPT_LEN, w64. f_equal; lia. }
(* a2 = the listing's object 27 = .str.7 0x210c0 = seg_litA_fz F_addr_line (a positional name, checked by VOBJS) *)
assert (T12 : getr (ms_regs ms2) 12 = w64 (SegInstB.seg_litA_fz SM.F_addr_line)).
{ rewrite Q12, (img_env_atomP E 268 HEI ltac:(unfold A_TEXT, A_LIM; lia)).
  change (VAL 268) with (VAL (A_OBJ 27)). rewrite (VOBJS 27%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. }
assert (T13 : getr (ms_regs ms2) 13 = w64 (c + SP.MC_READING))
  by (rewrite Q13, Uc; unfold SP.MC_READING, w64; reflexivity).
assert (T14 : getr (ms_regs ms2) 14 = w64 line) by (rewrite Q14, E11; reflexivity).
assert (Traw : YK0s.ret_ok (Z_to_bv 64 (BASE + 11028))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
(* every byte outside the frame and the two counter cells is the entry's, from the entry to the call *)
assert (KC4 : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (c + 9132 <= a < c + 9136) ->
  ~ (spZ regs - 48 <= a < spZ regs) -> rdW W (ms_mem ms2) a = rdW W (ms_mem ms1) a)
by (apply (ml_kof _ _ _ _ _ c (spZ regs) HFr2); ml_win Usp Uc).
assert (KC3 : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (c + 9132 <= a < c + 9136) ->
  ~ (spZ regs - 48 <= a < spZ regs) -> rdW W (ms_mem ms1) a = rdW W (ms_mem ms0) a)
by (apply (ml_kof _ _ _ _ _ c (spZ regs) HFr1); ml_win Usp Uc).
assert (KC2 : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (c + 9132 <= a < c + 9136) ->
  ~ (spZ regs - 48 <= a < spZ regs) -> rdW W (ms_mem ms0) a = rdW W (ms_mem ms) a)
by (apply (ml_kof _ _ _ _ _ c (spZ regs) HFr0); ml_win Usp Uc).
assert (KC1 : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (c + 9132 <= a < c + 9136) ->
  ~ (spZ regs - 48 <= a < spZ regs) -> rdW W (ms_mem ms) a = rdW W mem a)
by (apply (ml_kof _ _ _ _ _ c (spZ regs) HFr); ml_win Usp Uc).
assert (KEEPC : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (c + 9132 <= a < c + 9136) ->
  ~ (spZ regs - 48 <= a < spZ regs) -> rdW W (ms_mem ms2) a = rdW W mem a).
{ intros a Ha H1 H2 H3.
  rewrite (KC4 a Ha H1 H2 H3), (KC3 a Ha H1 H2 H3), (KC2 a Ha H1 H2 H3). exact (KC1 a Ha H1 H2 H3). }
(* name the env the four token runs left (the entry's E with the runs' two fresh atoms) *)
lazymatch type of HS with st_ok _ ?Ex _ _ => remember Ex as Eb eqn:HEb in * end.
assert (OLDb : forall k, (k < 1024)%nat -> ew Eb k = ew E k)
  by (intros k Hk; rewrite HEb; repeat (rewrite ew_ewset_other by lia); reflexivity).
assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by lia; exact Usp).
assert (Ucb : bv_unsigned (ew Eb 10) = c) by (rewrite OLDb by lia; exact Uc).
(* the call *)
eapply (srr_after_artF SEGS W _ (Z_to_bv 64 (BASE + 11028)) _ B MR_STK
  [(SP.kept_addr c (length (SM.mc_kept mc)), SP.kept_addr c (length (SM.mc_kept mc)) + SP.MC_KEPT_LEN);
   (c + SP.MC_NKEPT, c + SP.MC_NKEPT + 4); (c + SP.MC_REFUSED, c + SP.MC_REFUSED + 4)]
  regs ly S W mem md EV_m_refuse).
{ exact (ml_snp W (ms_regs ms2) (ms_mem ms2) _ ly S mem md regs ch c line mc knock _
    HPRE HROD HP Hl H8 HJ KEEPC Tsp Q1 Traw T3 T4 T10 Q11 T12 T13 T14). }
(* back at 0x878d4 at the FP state fx1 the wrapper returns *)
intros fx1 regs3 mem3 md3 Hfx (HJ2 & HP2 & (HR10 & HBY) & HK2).
change (112 - 1) with 111 in HBY, HK2.
(* the symbolic state at the FP state fx1 the wrapper returns: the five regions are kept (the call writes only
   [kept[n_kept], + sn_len) and its own window) *)
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
rewrite HSTK in Hpres2.
destruct (al_blocks _ _ LAWS ly S W mem3 md3 b m HAR2 Hin) as (_ & _ & _ & _ & Hbpres2 & _ & Hm2).
pose proof (req_size_pos m ltac:(lia)) as [Hq1 Hq2].
pose proof (pa_obj_img 0 ltac:(lia)) as HO0. pose proof (pa_obj_img 12 ltac:(lia)) as HO12.
unfold kImgEnd in HO0, HO12.
assert (EOb0 : bv_unsigned (ew Eb 241) = VAL (A_OBJ 0)).
{ change 241%nat with (A_OBJ 0).
  rewrite (img_env_atomP Eb (A_OBJ 0) HEI3 ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  apply unsigned_lit_small. lia. }
assert (EOb12 : bv_unsigned (ew Eb 253) = VAL (A_OBJ 12)).
{ change 253%nat with (A_OBJ 12).
  rewrite (img_env_atomP Eb (A_OBJ 12) HEI3 ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  apply unsigned_lit_small. lia. }
pose proof (PaFx.st_ok_restrict_xfx fx fx1 _ _ _ _ _ HS eq_refl) as HSf. clear HS. rename HSf into HS.
jafter_call_keep_pi HS 35%nat regs3 (mrestrict (w_H W) mem3) HP2 [0; 1; 2; 3; 4]%nat HS2.
lazymatch type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  repeat apply Forall_cons; try apply Forall_nil; split;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha;
    rewrite ?Uspb, ?Ucb, ?EOb0, ?EOb12 in Ha.
  - apply (mbyte_of_aview SEGS). apply HK2; [lia | lia | lia].
  - intros _. apply (apresent_writable SEGS). apply Hpres2. lia.
  - apply (mbyte_of_aview SEGS). apply HK2; [lia | lia | destruct Hcimg9; lia].
  - lia.
  - apply (mbyte_of_aview SEGS). apply HK2; [lia | lia | destruct Hcimg9; lia].
  - lia.
  - apply (mbyte_of_aview SEGS). apply HK2; [lia | lia | lia].
  - intros _. apply (apresent_writable SEGS). apply (proj1 (Hbpres2 a ltac:(lia))).
  - apply (mbyte_of_aview SEGS). apply HK2; [lia | lia | lia].
  - intros _. apply (apresent_writable SEGS). apply (proj1 (Hbpres2 a ltac:(lia))). }
clear HS. rewrite <- (restrict_mkst_fx (fx := fx1)) in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as Ef eqn:HEf in HS end.
assert (OLDf : forall k, (k < 35)%nat -> ew Ef k = ew E k).
{ intros k Hk. rewrite HEf, YN3v.ew_havoc_old by exact Hk. apply OLDb. lia. }
assert (HEIf : img_env VAL A_LIM Ef) by (rewrite HEf; apply img_env_havoc; [exact HEI3 | cbv; lia]).
assert (Uspf : bv_unsigned (ew Ef 2) = spZ regs) by (rewrite OLDf by lia; exact Usp).
assert (Ucf : bv_unsigned (ew Ef 10) = c) by (rewrite OLDf by lia; exact Uc).
assert (HAEf : env_agree 32 (Ereg regs (mr_extra (Z.of_nat (length (SM.mc_kept mc))) (SM.mc_refused mc))) Ef).
{ destruct HAE as [HA1 HA2]. split; [intros k Hk; rewrite OLDf by lia; apply HA1; exact Hk|].
  rewrite HEf, HEb. exact HA2. }
(* the two shadow entries still hold: the call kept the block's bytes and AR is back *)
assert (SHOKf : sh_ok SEGS mr_Bx mr_SH Ef (mrestrict (w_H W) mem3)).
{ assert (UBx : U Ef mr_Bx = SHADOW_OFF).
  { unfold mr_Bx, SA_SB. rewrite U_SOff, OLDf by lia.
    rewrite E32, Z.add_0_r, unsigned_lit_small by (unfold SB; lia).
    rewrite zcanon_id by (unfold SB, M64; lia). reflexivity. }
  assert (U10 : U Ef (SOff SA_C 0) = c).
  { unfold SA_C. rewrite U_SOff, Ucf, Z.add_0_r. apply zcanon_id. unfold M64. lia. }
  pose proof (range_addressable_of_block SEGS B LAWS ly S W mem3 md3 b m c 9236 HAR2 Hin ltac:(lia) ltac:(lia))
    as HRA2.
  unfold sh_ok, mr_SH. repeat apply Forall_cons; try apply Forall_nil.
  - apply (shent_ok_of_range SEGS (w_H W) mem3 Ef mr_Bx SA_C c 9236 c SP.MC_REFUSED (SP.MC_REFUSED + 4));
    [exact HRA2 | exact UBx | exact U10 | lia | lia
    | intros x Hx; cbn [Z.min Z.max] in Hx;
      unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; destruct Hcband9; lia].
  - apply (shent_ok_of_range SEGS (w_H W) mem3 Ef mr_Bx SA_C c 9236 c SP.MC_NKEPT (SP.MC_NKEPT + 4));
    [exact HRA2 | exact UBx | exact U10 | lia | lia
    | intros x Hx; cbn [Z.min Z.max] in Hx;
      unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; destruct Hcband9; lia]. }
(* 0x878d4 j 0x87920, then the tail: the check of n_kept twice (mr_SH), n_kept + 1 (the signed-overflow trap
   0x87930 is not taken: n_kept <= 7), the store, the check of refused (mr_SH), refused + 1, the epilogue, ret *)
pose proof (paj_run (fx := fx1) B LAWS) as RUNf.
paj_run_tok RUNf HS HJ2 SHOKf mr_Bspan.
{ mr_awrK Uspf Ucf Hcwr HSTK. }
(* name the env the tail run left *)
lazymatch goal with HSx : st_ok_pi _ _ ?Ex _ _ |- _ => remember Ex as Eg eqn:HEg in * end.
assert (OLDg : forall k, (k < 1024)%nat -> ew Eg k = ew Ef k)
  by (intros k Hk; rewrite HEg; repeat (rewrite ew_ewset_other by lia); reflexivity).
assert (Uspg : bv_unsigned (ew Eg 2) = spZ regs) by (rewrite OLDg by lia; exact Uspf).
assert (Ucg : bv_unsigned (ew Eg 10) = c) by (rewrite OLDg by lia; exact Ucf).
assert (Eg1 : ew Eg 1 = getr regs 1) by (rewrite OLDg, OLDf by lia; exact E1).
assert (Eg33 : ew Eg 33 = Z_to_bv 64 (Z.of_nat (length (SM.mc_kept mc))))
  by (rewrite OLDg, OLDf by lia; exact E33).
assert (Eg34 : ew Eg 34 = Z_to_bv 64 (SM.mc_refused mc)) by (rewrite OLDg, OLDf by lia; exact E34).
assert (HAEg : env_agree 32 (Ereg regs (mr_extra (Z.of_nat (length (SM.mc_kept mc))) (SM.mc_refused mc))) Eg).
{ destruct HAE as [HA1 HA2]. split; [intros k Hk; rewrite OLDg, OLDf by lia; apply HA1; exact Hk|].
  rewrite HEg, HEf, HEb. exact HA2. }
(* the two cells the tail wrote: refused + 1 and n_kept + 1 *)
lazymatch goal with
| HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
  pose proof (st_ok_pi_region_nth Eg ssx (restrict (w_H W) msc) 3%nat _ HSx eq_refl) as HRr3;
  pose proof (st_ok_pi_region_nth Eg ssx (restrict (w_H W) msc) 4%nat _ HSx eq_refl) as HRn4;
  cbn [restrict ms_mem] in HRr3, HRn4;
  pose proof (field_of_region_any Eg _ 10%nat c _ _ _ _ _ 8200 4%N _ HRr3 Ucg
    ltac:(cbn; left; reflexivity) ltac:(lia)) as VpR;
  pose proof (field_of_region_any Eg _ 10%nat c _ _ _ _ _ 9132 4%N _ HRn4 Ucg
    ltac:(cbn; left; reflexivity) ltac:(lia)) as VpN
end.
lazymatch type of VpR with val_mem _ _ _ _ ?v =>
  assert (HvR : v = SM.mc_refused mc + 1);
  [ first [ exact (ml_inc32 Eg 34 (SM.mc_refused mc) Eg34 ltac:(lia))
          | exact (ml_soff1 Eg 34 (SM.mc_refused mc) Eg34 ltac:(lia) ltac:(lia)) ]
  | rewrite HvR in VpR ] end.
lazymatch type of VpN with val_mem _ _ _ _ ?v =>
  assert (HvN : v = Z.of_nat (length (SM.mc_kept mc)) + 1);
  [ first [ exact (ml_soff1 Eg 33 (Z.of_nat (length (SM.mc_kept mc))) Eg33 ltac:(lia) ltac:(lia))
          | exact (ml_inc32 Eg 33 (Z.of_nat (length (SM.mc_kept mc))) Eg33 ltac:(lia)) ]
  | rewrite HvN in VpN ] end.
change (N.to_nat 4) with 4%nat in VpR, VpN.
(* the tail keeps every byte but its frame and the two cells *)
lazymatch goal with
| HFx : frame_of Ef _ (mrestrict _ mem3) (mrestrict _ (ms_mem ?mf)) |- _ =>
  assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (c + 9132 <= a < c + 9136) ->
    ~ (spZ regs - 48 <= a < spZ regs) -> rdW W (ms_mem mf) a = rdW W mem3 a)
  by (apply (ml_kof _ _ _ _ _ c (spZ regs) HFx); ml_win Uspf Ucf)
end.
(* the ret at 0x87974 *)
pose proof (paj_ret_at (fx := fx1) (PL := PL_seg) (PI := PI)) as RETf.
lazymatch goal with
| HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  prreg HSx (1%bv : bv 5) R1;
  eapply (RETf W _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity));
  intros mat'; apply (apost_baseF_of_base (fx := fx1) SEGS); unfold apost_base;
  exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
  split; [cbn [ms_regs]; rewrite R1, Eg1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|];
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJx|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ Eg _ _ regs
    (mr_extra (Z.of_nat (length (SM.mc_kept mc))) (SM.mc_refused mc)) HSx); [exact HAEg | vm_compute; reflexivity]|]
end.
split.
{ (* the block holds m_refuse mc line knock: the text in kept[n_kept], n_kept + 1, refused + 1, the rest kept *)
  apply (MF.mr_enc_kept knock (rdW W mem) _ c mc line HMC H8 HRF Hline).
  - intros i Hi. cbn [ms_mem]. rewrite KEEPF by lia. rewrite HBY by lia. reflexivity.
  - cbn [ms_mem]. apply mr_sa_val_of. exact VpN.
  - cbn [ms_mem]. apply mr_sa_val_of. exact VpR.
  - intros a Ha H1 H2 H3. cbn [ms_mem].
    rewrite KEEPF by lia. rewrite HK2 by lia. apply KEEPC; lia. }
split.
{ intros a Ha HnS HnE. cbn [ms_mem]. rewrite HSTK in HnS.
  assert (H1 : ~ (c + 8200 <= a < c + 8204)) by (intros Hq; apply HnE; right; right; lia).
  assert (H2 : ~ (c + 9132 <= a < c + 9136)) by (intros Hq; apply HnE; right; left; split; lia).
  assert (H3 : ~ (SP.kept_addr c (length (SM.mc_kept mc)) <= a <
                  SP.kept_addr c (length (SM.mc_kept mc)) + RtPFShared.sn_len 111 (MF.mr_text mc line)))
    by (intros Hq; apply HnE; left; split; lia).
  rewrite KEEPF by lia. rewrite HK2 by lia. apply KEEPC; lia. }
split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs S). apply ml_set_fs_id.
Qed.
About mr_arm_keptL.
Print Assumptions mr_arm_keptL.
End e.
End f.
End d.
