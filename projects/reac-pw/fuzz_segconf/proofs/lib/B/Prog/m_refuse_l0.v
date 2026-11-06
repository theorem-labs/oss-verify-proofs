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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module names changed; 492 of its 566 lines of code are new or changed and 379 lines of the source are left out. *)
(* proves no function (kind: segment lemma of m_refuse's image-B walk: the line = 0 snprintf arm).
   mr_arm_kept0 : MR_KEPT0_stmt B (statement in lib/B/Prog/m_refuse_k.v): on fuzz_segconf.asan-ubsan (image B, pin
   sha256 c3796c0b38f3..., m_refuse at 0x8782c), when n_kept < 8 and line = 0, the walk from the entry to the ret
   0x87974 proves mr_Q (the contract's post at image B's numbers, apost_baseF). The n_kept = 8 arm is m_refuse_k.v's
   mr_arm_full, the line > 0 arm lib/B/Prog/m_refuse_ln.v; a walk lane composes the three.

   The path (the neutral listing of m_refuse in image B):
   - entry to 0x87888: m_refuse_k.v's seed mr_entry (n_kept a writable region from the start, its fact [0, 7]); the
     token run decides trap 1 (0x87848 bnez c & 3: c is 16-aligned), the instrumented check of n_kept (0x87874, its
     shadow entry in mr_SH) and the blt 7, n_kept at 0x87884 (not taken: n_kept <= 7); it stops at the blez of line.
   - 0x87888 blez line: split; the not-taken arm is refuted by mr_blez (it gives 0 < line, against line = 0).
   - 0x878d8 to 0x878fc: trap 4 (0x878dc bltu 8, n_kept) is decided by the run (n_kept <= 7); the run stops at
     trap 5 (0x878fc bltu ~(c + 0x200c), 112 n_kept, the address of kept[n_kept] wrapping), split, and the taken
     edge is refuted by mr_ub_wrap (c + 9236 <= alloc_ceiling, n_kept <= 7).
   - to 0x8791c and through the jal: a0 = kept[n_kept] = c + 0x200c + 112 n_kept, a1 = 112, a2 = listing object 28
     = .str.8 0x210e0 (seg_val_objs; seg_litA_fz's address of SegModel.F_addr "%s: "), a3 = c + 0x23b4 = the
     reading; the run stops at the wrapper's trampoline with ra = BASE + 0x2b60 (0x87920).
   - the call: mr0_snp below, row 4 (RtPFSeg.seg_asnprintf_realizes, Section hypothesis SNP) at FR_seg, stepped
     by PaFx.v's aj_art_own_atF / srr_art_postF_of_pf / srr_after_artF; the text is MF.mr_text mc 0 (at most 104
     bytes, so the wrapper writes it and its NUL into kept[n_kept]).
   - after the call (at the FP state fx1 the wrapper returns): jafter_call_keep_pi keeps all five regions (the
     wrapper keeps every byte outside kept[n_kept] and its window) and the shadow entries are re-derived from the
     live block; the token run from 0x87920 to the ret decides the instrumented checks of n_kept at 0x87920 and
     0x87934 and of refused at 0x87940 (mr_SH, so no error path is reached) and trap 6 (0x87930 blt n_kept + 1,
     n_kept, the signed overflow: n_kept <= 7), stores n_kept + 1 and refused + 1 and returns.
   - the post: MF.mr_enc_kept (the text, n_kept + 1, refused + 1, every other byte of the block as at the entry),
     sa_kept over m_refuse_W's three ranges, sa_noalloc.
   The call step and the tail follow the image-A m_file-family lane's image-A walk lib/A/Prog/m_refuseA.v (commit
   0e3b3a97f9af: mr_snp :386-587 and the n_kept < 8 arm), at image B's numbers and with row 4's FR_seg family. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_refuse_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Module SM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec.SegModel.
Module SP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.seg_spec.
Module MF := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog.m_refuse_f.
#[local] Notation MR_STK := SegInstB.STK_m_refuse.

(* ---------- small facts with no state (image A's walk lib/A/Prog/m_refuseA.v of the image-A m_file-family lane, the same code) ---------- *)
Lemma l0_rdword_kept : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma l0_argZ3 : forall regs : bvmap 5 word, argZ regs 3 = bv_unsigned (getr regs 13).
Proof.
intros regs. unfold argZ. assert (E : Z_to_bv 5 (10 + 3) = (13%bv : bv 5)) by (apply bv_eq; reflexivity).
rewrite E. reflexivity.
Qed.
(* a0 at the call: c + 0x200c + 112 n_kept = &kept[n_kept] *)
Lemma l0_a0_kept : forall E c n, ew E 10 = Z_to_bv 64 c -> ew E 33 = Z_to_bv 64 n -> 0 <= c -> c + 9236 < 2 ^ 63 ->
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
(* n_kept + 1 as the tail stores it: the executor drops the sign extension of the loaded word (n_kept <= 7), so
   the cell's chunk is SOff 33 1 *)
Lemma l0_soff1 : forall E k v, ew E k = Z_to_bv 64 v -> 0 <= v -> v + 1 < 2 ^ 32 ->
bv_unsigned (sv_denot E (SOff k 1)) mod 2 ^ (8 * Z.of_N 4) = v + 1.
Proof.
intros E k v H Hv Hv1. cbn [sv_denot]. rewrite H.
replace (bv_unsigned (Z_to_bv 64 v) + 1) with (v + 1) by (rewrite unsigned_lit_small by lia; lia).
rewrite unsigned_lit_small by lia. change (8 * Z.of_N 4) with 32. apply Z.mod_small. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* m_refuse_k.v's Section e, reopened with its exact hypotheses *)
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SNP : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR
    (SIGMA SS___interceptor_trampoline_snprintf) RtPFCmd.CMD_GOTW RtAPI.A_SSP_GUARD.
(* m_refuse_k.v's mr_awrK, copied: an Ltac of a Section does not outlive it *)
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
(* the disjointness goals of the call: the stack window (above alloc_ceiling), the destination and the reading (in
   the heap block, off the image), the image's words and literals (in [0x10000, kImgEnd)) *)
Ltac l0_disj := unfold zdisjoint; cbn [fst snd]; unfold kImgEnd, RtPFCmd.CMD_GOTW, RtAPI.A_SSP_GUARD in *; lia.

(* ---------- the call at 0x8791c: snprintf(kept[n_kept], 112, "%s: ", c->reading) ----------
   Row 4 (RtPFSeg.seg_asnprintf_realizes = RtPFCmd.cmd_asnprintf_realizes at the family FR_seg), stepped by PaFx.v's
   aj_art_own_atF (the destination kept[n_kept] is in the footprint and in the live heap block) and
   srr_art_postF_of_pf; the format is .str.8 0x210e0 (SegModel.F_addr, seg_litA_fz), the one argument the reading at
   c + 0x23b4. The pattern is image A's mr_snp (lib/A/Prog/m_refuseA.v:386-587 at a working branch). *)
Lemma mr0_snp : forall W regsT memT mdc ly S mem md regs ch FP c line mc knock raw,
afn_pre SEGS B MR_STK ly S W regs mem md ch ->
arodata_okP SEGS SegInstB.RLO_A SegInstB.RHI_A B (rdW W mem) ->
m_refuse_pre SEGS B ly S (rdW W mem) SegInstB.seg_litA_fz RtPFCmd.CMD_GOTW RtAPI.A_SSP_GUARD c line mc knock ->
ajournal SEGS B MR_STK (spZ regs) FP ly S W mem md [] ly S W memT mdc 0 ->
(forall a, SP.kept_addr c (length (SM.mc_kept mc)) <= a < SP.kept_addr c (length (SM.mc_kept mc)) + 112 ->
  inFP FP a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (c + 9132 <= a < c + 9136) ->
  ~ (spZ regs - 48 <= a < spZ regs) -> rdW W memT a = rdW W mem a) ->
spZ regsT = spZ regs - 48 -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
(length (SM.mc_kept mc) < 8)%nat -> line = 0 ->
getr regsT 10 = w64 (SP.kept_addr c (length (SM.mc_kept mc))) -> getr regsT 11 = w64 112 ->
getr regsT 12 = w64 (SegInstB.seg_litA_fz SM.F_addr) -> getr regsT 13 = w64 (c + SP.MC_READING) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fx fx1 /\
 c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal SEGS B MR_STK (spZ regs) FP ly S W mem md [] ly S W mem2 md2 0 /\
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
intros W regsT memT mdc ly S mem md regs ch FP c line mc knock raw
  HPRE HROD HMR HJ HFPd KEEPT Tsp T1 Traw T3 T4 Hlt Hl0 T10 T11 T12 T13.
destruct HMR as (Hc0 & Hc16 & HHEAP & HADDR & HMC & HTAIL & Hline & Href & HFRM & HSSP & HLIT).
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : MR_STK = 8240) by (vm_compute; reflexivity).
assert (HK : RtPFSeg.SEG_SNP_K = 8192) by reflexivity.
rewrite HSTK in Hslo.
destruct (mr_blk B ly S W mem md c HAR HHEAP) as (Hc4096 & Hcceil & Hcimg & Hcband & Hcpres & Hcwr).
destruct HHEAP as (b & m & Hin & Hb1 & Hb2).
destruct (MF.mr_fields knock (rdW W mem) c mc HMC) as (Hk8 & HNV & HRb & HRV & Hrd96 & Hrdb & Hrdbytes & Hblkmap).
unfold SP.SEG_M_SIZE in Hcceil, Hcimg, Hcband, Hcwr, Hb2, HTAIL, Hblkmap.
pose proof (proj1 HJ) as HARc.
destruct (al_blocks _ _ LAWS ly S W memT mdc b m HARc Hin) as (_ & _ & _ & _ & Hbpres & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [Hr1 Hr2].
(* the literal "%s: " (sa_lit through seg_litA_fz) and the stack-protector words *)
destruct (HLIT SM.F_addr ltac:(right; left; reflexivity)) as (Hf0 & ((HFZ & HFnz) & HFT) & HFP & HFR & HFI).
destruct (HFP ly S W memT mdc HARc) as (Hfa0 & Hfa63 & HFAM & HFRA & HFHV).
destruct HSSP as (HG1 & cval & HG2).
set (f := SegInstB.seg_litA_fz SM.F_addr) in *.
assert (Hfv : f = 0x210e0) by (unfold f; vm_compute; reflexivity).
assert (HFL : Z.of_nat (length SM.F_addr) = 4) by (vm_compute; reflexivity).
set (d := SP.kept_addr c (length (SM.mc_kept mc))) in *.
assert (Hd : d = c + 8204 + 112 * Z.of_nat (length (SM.mc_kept mc)))
  by (unfold d, SP.kept_addr, SP.MC_KEPT, SP.MC_KEPT_LEN; lia).
subst line.
set (T := MF.mr_text mc 0) in *.
assert (HTL : (length T <= 104)%nat) by (apply MF.mr_text_len; [exact Hrd96 | lia]).
assert (HT : T = SM.fmt SM.F_addr [SM.AS (SM.mc_reading mc)]) by reflexivity.
destruct (MF.mr_sn T HTL) as [HsnB HsnL].
set (w := RtPFShared.sn_len (112 - 1) T) in *.
assert (Hw : 1 <= w <= 105) by (unfold w; change (112 - 1) with 111; rewrite HsnL; lia).
set (rdg := SM.mc_reading mc) in *.
assert (HRN : ~ In 0 rdg).
{ intros H0. rewrite Forall_forall in Hrdb. specialize (Hrdb 0 H0). lia. }
set (wr := c + SP.MC_READING) in *.
assert (Hwr : wr = c + 9140) by (unfold wr, SP.MC_READING; lia).
assert (Ec : c = 16 * (c / 16)) by (pose proof (Z.div_mod c 16 ltac:(lia)) as Hq; rewrite Hc16 in Hq; lia).
(* alloc_ceiling is page-aligned and c 16-aligned, so the block ends at least 12 bytes below it: the reading's
   slack [c + 9236, c + 9240) is below the stack window too *)
pose proof (@ASAN_CEIL_range rc) as [CR1 CR2]. unfold ASAN_CEIL in CR1, CR2.
assert (Ea : alloc_ceiling = 4096 * (alloc_ceiling / 4096))
  by (pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)) as Hq; rewrite CR2 in Hq; lia).
assert (Hcc : c + 9248 <= alloc_ceiling) by lia.
assert (Hse : RtPFShared.str_end wr rdg <= c + 9240 /\ wr + Z.of_nat (length rdg) < RtPFShared.str_end wr rdg /\
              RtPFShared.str_end wr rdg <= wr + Z.of_nat (length rdg) + 8).
{ unfold RtPFShared.str_end.
  pose proof (Z.div_mod (wr + Z.of_nat (length rdg)) 8 ltac:(lia)) as Hq.
  pose proof (Z.mod_pos_bound (wr + Z.of_nat (length rdg)) 8 ltac:(lia)) as Hb.
  lia. }
assert (Htl : (c + 9236 - 1) mod 8 = 3).
{ rewrite Ec. replace (16 * (c / 16) + 9236 - 1) with (3 + (2 * (c / 16) + 1154) * 8) by lia.
  rewrite Z_mod_plus_full. reflexivity. }
(* what the call reads keeps its entry value: the image, the reading and its slack *)
assert (KIMG : forall a, 0x10000 <= a < kImgEnd -> rdW W memT a = rdW W mem a).
{ intros a Ha. unfold kImgEnd in *. apply KEEPT; lia. }
assert (HRDK : forall a, c + 9140 <= a < c + 9240 -> rdW W memT a = rdW W mem a).
{ intros a Ha. apply KEEPT; lia. }
assert (HROM : RtDefs.rt_rom_view SEGS B W memT).
{ intros a (sg & Hsg & Hwr' & Hr) Ho He.
  pose proof (pa_img_range a (ex_intro _ sg (conj Hsg Hr))) as Hia.
  rewrite (KIMG a Hia).
  exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hwr' Hr)))) Ho He). }
assert (HG1' : rdword (rdW W memT) RtPFCmd.CMD_GOTW = Some RtAPI.A_SSP_GUARD).
{ rewrite (l0_rdword_kept (rdW W mem)); [exact HG1|]. intros i Hi. apply KIMG.
  unfold RtPFCmd.CMD_GOTW, kImgEnd. lia. }
assert (HG2' : rdword (rdW W memT) RtAPI.A_SSP_GUARD = Some cval).
{ rewrite (l0_rdword_kept (rdW W mem)); [exact HG2|]. intros i Hi. apply KIMG.
  unfold RtAPI.A_SSP_GUARD, kImgEnd. lia. }
(* the scratch window and the entry's precondition at the call *)
destruct (ecall_pre_stk_at SEGS B RtPFSeg.SEG_SNP_K MR_STK (spZ regs) FP ly S W mem md []
  ly S W memT mdc 0 regsT (-48) HJ ltac:(lia) eq_refl ltac:(lia) ltac:(rewrite HK; unfold ESTACK; lia)
  ltac:(rewrite HK, HSTK; lia) ltac:(rewrite T1; exact Traw) T3 T4) as (HEC & HSLO & HSCR).
pose proof (SNP fx) as HA.
unfold RtPFSeg.seg_asnprintf_realizes, RtPFCmd.cmd_asnprintf_realizes in HA.
assert (U13 : bv_unsigned (getr regsT 13) = wr) by (rewrite T13; unfold w64; apply unsigned_lit_small; lia).
eapply SRr_mono.
{ eapply (aj_art_own_atF SEGS B LAWS pa_segs_low RtPFSeg.SEG_SNP_K (fun a => d <= a < d + w)
    (SIGMA SS___interceptor_trampoline_snprintf) W regsT memT MR_STK (spZ regs) FP
    ly S W mem md [] ly S mdc 0 (-48) raw _ HJ).
  - lia.
  - reflexivity.
  - lia.
  - rewrite HK; lia.
  - rewrite HK, HSTK; lia.
  - exact T1.
  - intros a Ha. apply Hcwr; [apply HFPd; lia | lia].
  - apply (srr_art_postF_of_pf SEGS B RtPFSeg.SEG_SNP_K ly S W regsT memT mdc _ d w
      (RtPFShared.sn_bytes (112 - 1) T) (Z.of_nat (length T)) HSCR).
    apply (HA ly S W regsT memT mdc d 112 f [] (map (argZ regsT) [3; 4; 5; 6; 7] ++ []) T cval HEC HSLO HSCR
      T10 T11 T12 HROM).
    + unfold RtPFCmd.CMD_SNP_CR. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    + unfold RtPFCmd.CMD_SNP_CR, RtPFShared.snp_out.
      repeat (apply Forall_cons; [repeat (apply Forall_cons; [l0_disj|]); apply Forall_nil|]). apply Forall_nil.
    + exact HG1'.
    + exact HG2'.
    + unfold RtPFCmd.CMD_GOTW; lia.
    + unfold RtPFCmd.CMD_GOTW; lia.
    + unfold RtAPI.A_SSP_GUARD; lia.
    + unfold RtAPI.A_SSP_GUARD; lia.
    + unfold RtPFShared.snp_out. repeat (apply Forall_cons; [l0_disj|]). apply Forall_nil.
    + unfold RtPFShared.snp_out. repeat (apply Forall_cons; [l0_disj|]). apply Forall_nil.
    + split; [reflexivity | intros i Hi; cbn [length] in Hi; lia].
    + cbn [length Z.of_nat]. lia.
    + unfold RtPFShared.snp_out. cbn [length Z.of_nat]. repeat (apply Forall_cons; [l0_disj|]). apply Forall_nil.
    + (* the format family FR_seg: "%s: " parses to %s ':' ' ', its one argument the reading *)
      unfold RtPFSeg.FR_seg, RtPFSeg.seg_fam.
      exists SM.F_addr, MF.mr_qs_a, [RtPFPf.APtr rdg].
      split.
      { unfold RtPFShared.fmt_at. split; [lia|]. split.
        - intros i Hi. rewrite (KIMG (f + i)) by (unfold kImgEnd; lia).
          replace (f + i) with (f + Z.of_nat (Z.to_nat i)) by lia. apply HFZ.
          rewrite length_app. cbn [length]. lia.
        - split.
          + unfold RtPFShared.snp_out. repeat (apply Forall_cons; [l0_disj|]). apply Forall_nil.
          + split; [exact HFAM|]. split; [exact HFRA | apply HFHV; lia]. }
      split; [exact MF.mr_parse_a|].
      split; [unfold MF.mr_qs_a; repeat (apply Forall_cons; [exact I|]); apply Forall_nil|].
      split.
      { cbn [map app RtPFShared.pf_args_asan]. split; [|exact I].
        rewrite l0_argZ3, U13. cbn [RtPFShared.pf_arg_asan].
        split; [exact Hrdb|]. split; [lia|]. split; [lia|]. split.
        - intros i Hi. rewrite HRDK by lia.
          replace (wr + i) with (wr + Z.of_nat (Z.to_nat i)) by lia. apply Hrdbytes. lia.
        - split.
          + intros x Hx. rewrite HRDK by lia.
            destruct (Z_lt_le_dec x (c + 9236)) as [Hx1 | Hx1].
            * apply Hblkmap. lia.
            * apply HTAIL. rewrite Htl. lia.
          + split.
            { unfold RtPFShared.snp_out. repeat (apply Forall_cons; [l0_disj|]). apply Forall_nil. }
            split; [apply (amem_range_of_block SEGS B LAWS ly S W memT mdc b m); [exact HARc | exact Hin | lia | lia]|].
            split; [apply (range_addressable_of_block SEGS B LAWS ly S W memT mdc b m); [exact HARc | exact Hin | lia | lia]|].
            apply (shadow_hull_vis_of_block SEGS B LAWS ly S W memT mdc b m); [exact HARc | exact Hin | lia | lia | lia]. }
      split; [rewrite HT; exact (MF.mr_text_a rdg HRN)|].
      split; [exact I|].
      split; [unfold RtPFCmd.CMD_IMG_LO; lia|].
      split; [unfold RtPFCmd.CMD_GOTW; lia|].
      pose proof (amem8_of_block SEGS B LAWS ly S W memT mdc b m wr (Z.of_nat (length rdg) + 1) HARc Hin
        ltac:(lia) ltac:(lia) ltac:(lia)) as HAM8.
      split.
      { cbn [map app RtPFCmd.cmd_args_slack]. rewrite l0_argZ3, U13. split; [|exact I].
        unfold amem_range in *. lia. }
      split; [intros Hq; vm_compute in Hq; discriminate Hq|].
      cbn [map app RtPFCmd.cmd_args_amem]. rewrite l0_argZ3, U13. split; [|exact I].
      unfold amem_range in *. lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + unfold RtPFShared.snp_out. cbn [pairwise]. split; [|split; [apply Forall_nil | exact I]].
      apply Forall_cons; [l0_disj | apply Forall_nil].
    + intros a Ha. destruct (Hbpres a ltac:(lia)) as [Hp Hno].
      split; [apply (apresent_writable SEGS); exact Hp|]. split; [exact Hno|]. unfold ESTACK. lia.
    + exact (amem8_of_block SEGS B LAWS ly S W memT mdc b m d w HARc Hin ltac:(lia) ltac:(lia) ltac:(lia)).
    + apply (range_addressable_of_block SEGS B LAWS ly S W memT mdc b m); [exact HARc | exact Hin | lia | lia].
    + apply (shadow_hull_vis_of_block SEGS B LAWS ly S W memT mdc b m); [exact HARc | exact Hin | lia | lia | lia].
    + unfold zdisjoint, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI. cbn [fst snd]. unfold kImgEnd in *. lia.
    + exact HFRM. }
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HP2 & HQ2 & HK2).
split; [reflexivity|]. exists fx1, regs2, mem2, md2.
split; [exact Hfx|]. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HQ2|].
intros a Ha H1 H2. apply (HK2 a Ha); [lia | exact H2].
Qed.

Lemma mr_arm_kept0 : MR_KEPT0_stmt B.
Proof.
intros ly S W regs mem md ch c line mc knock HPRE HROD H10 Hc64 H11 HP (Hl & H8).
pose proof HP as (Hc0 & Hc16 & HHEAP & HADDR & HMC & HTAIL & Hline & HRF & HFRM & HSSP & HLIT).
pose proof pa_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : MR_STK = 8240) by (vm_compute; reflexivity).
destruct (mr_blk B ly S W mem md c HAR HHEAP) as (Hc4096 & Hcceil & Hcimg & Hcband & Hcpres & Hcwr).
destruct (MF.mr_fields knock (rdW W mem) c mc HMC) as (Hk8 & HNV & HRb & HRV & Hrd96 & Hrdb & Hrdbytes & Hblkmap).
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
paj_run_to_tok RUNTO HS HJ SHOK mr_Bspan MR_SNP1.
{ mr_awrK Usp Uc Hcwr HSTK. }
psrr_branch_tok RUN BR HS SHOK mr_Bspan.
2: { exfalso.
  lazymatch goal with Hc : branch_taken _ (sv_denot ?Eb _) _ = ?b |- _ =>
    assert (B11 : ew Eb 11 = Z_to_bv 64 line) by (repeat (rewrite ew_ewset_other by lia); exact E11);
    pose proof (mr_blez Eb line b B11 ltac:(lia) Hc) as Hlb; cbn in Hlb end.
  lia. }
paj_run_to_tok RUNTO HS HJ SHOK mr_Bspan MR_SNP2.
{ mr_awrK Usp Uc Hcwr HSTK. }
psrr_branch_tok RUN BR HS SHOK mr_Bspan.
1: { exfalso.
  lazymatch goal with Hw : branch_taken BC_LTU (sv_denot ?Eb _) _ = true |- _ =>
    assert (B10 : ew Eb 10 = Z_to_bv 64 c) by (repeat (rewrite ew_ewset_other by lia); exact E10);
    assert (B33 : ew Eb 33 = Z_to_bv 64 (Z.of_nat (length (SM.mc_kept mc))))
      by (repeat (rewrite ew_ewset_other by lia); exact E33);
    rewrite (mr_ub_wrap (rc := rc) Eb c (Z.of_nat (length (SM.mc_kept mc))) B10 B33 ltac:(lia) ltac:(lia) ltac:(lia)) in Hw;
    discriminate Hw
  end. }
paj_run_tok RUN HS HJ SHOK mr_Bspan.
{ mr_awrK Usp Uc Hcwr HSTK. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
repeat rewrite wvb_collapse in HJ.
assert (Tsp : spZ (ms_regs ms1) = spZ regs - 48).
{ unfold spZ at 1. rewrite Q2, Usp. rewrite unsigned_lit_small by (rewrite HSTK in Hslo; lia). lia. }
assert (T3 : getr (ms_regs ms1) 3 = w64 (as_gp B))
  by (rewrite Q3, EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl); exact Hgp).
assert (T4 : getr (ms_regs ms1) 4 = w64 (as_tp B))
  by (rewrite Q4, EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl); exact Htp).
unfold SP.SEG_M_SIZE in Hcceil, Hcimg, Hcband.
assert (T10 : getr (ms_regs ms1) 10 = w64 (SP.kept_addr c (length (SM.mc_kept mc)))).
{ rewrite Q10, (l0_a0_kept E c (Z.of_nat (length (SM.mc_kept mc))) E10 E33 ltac:(lia) ltac:(lia) ltac:(lia)).
  unfold SP.kept_addr, SP.MC_KEPT, SP.MC_KEPT_LEN. f_equal; lia. }
(* a2 = listing object 28; seg_val_objs puts it at 0x210e0, which is seg_litA_fz's address of the text "%s: " *)
assert (T12 : getr (ms_regs ms1) 12 = w64 (SegInstB.seg_litA_fz SM.F_addr)).
{ rewrite Q12, (img_env_atomP E 269 HEI ltac:(unfold A_TEXT, A_LIM; lia)).
  change (VAL 269) with (VAL (A_OBJ 28)). rewrite (VOBJS 28%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. }
assert (T13 : getr (ms_regs ms1) 13 = w64 (c + SP.MC_READING)) by (rewrite Q13, Uc; reflexivity).
assert (Traw : YK0s.ret_ok (Z_to_bv 64 (BASE + 11104))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
(* the runs from the entry to the call wrote only the frame and the two counter windows *)
assert (KF : forall Ex rs m1 m2, frame_of Ex rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  bv_unsigned (ew Ex 2) = spZ regs -> bv_unsigned (ew Ex 10) = c ->
  windows rs = windows (ss_mem (mr_ss true 0 7 0 65536)) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (c + 9132 <= a < c + 9136) ->
  ~ (spZ regs - 48 <= a < spZ regs) -> rdW W m2 a = rdW W m1 a).
{ intros Ex rs m1 m2 HFx U2 U10 Hrs a Ha H1 H2 H3.
  refine (kept_of_frame Ex rs (w_H W) m1 m2
    (fun x => (c + 8200 <= x < c + 8204) \/ (c + 9132 <= x < c + 9136) \/ (spZ regs - 48 <= x < spZ regs))
    HFx _ a Ha _); [| intros [Hq|[Hq|Hq]]; auto].
  intros bb wlo whi x Hin' Hr. rewrite Hrs in Hin'. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hr;
    first [ rewrite U10 in Hr; first [left; lia | right; left; lia]
          | rewrite U2 in Hr; right; right; lia | exfalso; lia ] |]).
  destruct Hin'. }
lazymatch goal with
| HF1 : frame_of _ _ (mrestrict _ mem) (mrestrict _ (ms_mem ?m1)),
  HF2 : frame_of _ _ (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)),
  HF3 : frame_of _ _ (mrestrict _ (ms_mem ?m2)) (mrestrict _ (ms_mem ms1)) |- _ =>
  assert (KEEPC : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (c + 9132 <= a < c + 9136) ->
    ~ (spZ regs - 48 <= a < spZ regs) -> rdW W (ms_mem ms1) a = rdW W mem a)
  by (intros a Ha H1 H2 H3;
      rewrite (KF _ _ _ _ HF3 ltac:(repeat (rewrite ew_ewset_other by lia); exact Usp)
        ltac:(repeat (rewrite ew_ewset_other by lia); exact Uc) ltac:(vm_compute; reflexivity) a Ha H1 H2 H3);
      rewrite (KF _ _ _ _ HF2 ltac:(repeat (rewrite ew_ewset_other by lia); exact Usp)
        ltac:(repeat (rewrite ew_ewset_other by lia); exact Uc) ltac:(vm_compute; reflexivity) a Ha H1 H2 H3);
      exact (KF _ _ _ _ HF1 ltac:(repeat (rewrite ew_ewset_other by lia); exact Usp)
        ltac:(repeat (rewrite ew_ewset_other by lia); exact Uc) ltac:(vm_compute; reflexivity) a Ha H1 H2 H3))
end.
(* 0x8791c: snprintf(kept[n_kept], 112, "%s: ", c->reading) *)
eapply (srr_after_artF SEGS W _ (Z_to_bv 64 (BASE + 11104)) _ B MR_STK _ regs ly S W mem md EV_m_refuse).
{ refine (mr0_snp W (ms_regs ms1) (ms_mem ms1) _ ly S mem md regs ch _ c line mc knock _
    HPRE HROD HP HJ _ KEEPC Tsp Q1 Traw T3 T4 H8 Hl T10 Q11 T12 T13).
  intros a Ha.
  exists (SP.kept_addr c (length (SM.mc_kept mc)), SP.kept_addr c (length (SM.mc_kept mc)) + SP.MC_KEPT_LEN).
  split; [left; reflexivity | exact Ha]. }
intros fx1 regs2 mem2 md2 Hfx (HJ2 & HP2 & (HR10 & HBY) & HK2).
(* back at 0x87920 at the FP state fx1 the wrapper returns: the text and its NUL at kept[n_kept] *)
assert (HTL : (length (MF.mr_text mc line) <= 104)%nat) by (apply MF.mr_text_len; [exact Hrd96 | lia]).
destruct (MF.mr_sn (MF.mr_text mc line) HTL) as [HsnB HsnL].
change (112 - 1) with 111 in HBY, HK2.
rewrite HsnB in HBY. rewrite HsnL in HBY, HK2.
assert (Hd : SP.kept_addr c (length (SM.mc_kept mc)) = c + 8204 + 112 * Z.of_nat (length (SM.mc_kept mc)))
  by (unfold SP.kept_addr, SP.MC_KEPT, SP.MC_KEPT_LEN; lia).
rewrite Hd in HBY, HK2.
assert (HK : RtPFSeg.SEG_SNP_K = 8192) by reflexivity.
(* the symbolic state after the call: the wrapper keeps every byte outside kept[n_kept] and its window, so all five
   regions (the frame, the GOT word and the shadow cell, refused, n_kept) stay, and s0..s3 by aregs_preserved *)
pose proof (PaFx.st_ok_restrict_xfx fx fx1 _ _ _ _ _ HS eq_refl) as HSf. clear HS. rename HSf into HS.
jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
destruct HHEAP as (b & m & Hin & Hb1 & Hb2). unfold SP.SEG_M_SIZE in Hb2.
destruct (al_blocks _ _ LAWS ly S W mem2 md2 b m HAR2 Hin) as (_ & _ & _ & _ & Hbpres2 & _).
pose proof (req_size_pos m ltac:(lia)) as [Hr1 Hr2].
pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 12 ltac:(lia)) as HcellR.
assert (EO0 : bv_unsigned (ew E 241) = VAL (A_OBJ 0)).
{ rewrite (img_env_atomP E 241 HEI ltac:(unfold A_TEXT, A_LIM; lia)). apply unsigned_lit_small.
  change 241%nat with (A_OBJ 0). pose proof (pa_val_range (A_OBJ 0)). lia. }
assert (EO12 : bv_unsigned (ew E 253) = VAL (A_OBJ 12)).
{ rewrite (img_env_atomP E 253 HEI ltac:(unfold A_TEXT, A_LIM; lia)). apply unsigned_lit_small.
  change 253%nat with (A_OBJ 12). pose proof (pa_val_range (A_OBJ 12)). lia. }
lazymatch type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  repeat apply Forall_cons; try apply Forall_nil; split;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha;
    repeat (rewrite ew_ewset_other in Ha by lia); rewrite ?Usp, ?Uc, ?EO0, ?EO12 in Ha.
  all: first
    [ apply (mbyte_of_aview SEGS); apply HK2; unfold kImgEnd in *; lia
    | intros _; apply (apresent_writable SEGS); apply Hpres2; lia
    | intros _; apply (apresent_writable SEGS); apply (proj1 (Hbpres2 a ltac:(lia)))
    | exfalso; lia ]. }
clear HS. rewrite <- (restrict_mkst_fx (fx := fx1)) in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as Ef eqn:HEf in HS end.
assert (HEIf : img_env VAL A_LIM Ef) by (rewrite HEf; apply img_env_havoc; [assumption | cbv; lia]).
assert (OLDf : forall k, (k < 35)%nat -> ew Ef k = ew E k).
{ intros k Hk. rewrite HEf, YN3v.ew_havoc_old by exact Hk. repeat (rewrite ew_ewset_other by lia). reflexivity. }
assert (Uspf : bv_unsigned (ew Ef 2) = spZ regs) by (rewrite OLDf by lia; exact Usp).
assert (Ucf : bv_unsigned (ew Ef 10) = c) by (rewrite OLDf by lia; exact Uc).
assert (HAEf : env_agree 32 (Ereg regs (mr_extra (Z.of_nat (length (SM.mc_kept mc))) (SM.mc_refused mc))) Ef).
{ destruct HAE as [HA1 HA2]. split; [intros k Hk; rewrite OLDf by lia; apply HA1; exact Hk|].
  rewrite HEf. exact HA2. }
(* the two shadow entries at the memory after the call: the block is still a live, addressable heap block *)
assert (SHOKf : sh_ok SEGS mr_Bx mr_SH Ef (mrestrict (w_H W) mem2)).
{ assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (UBx : U Ef mr_Bx = SHADOW_OFF).
  { unfold mr_Bx, SA_SB. rewrite U_SOff, OLDf by lia.
    rewrite E32, Z.add_0_r, unsigned_lit_small by (unfold SB; lia).
    rewrite zcanon_id by (unfold SB, M64; lia). reflexivity. }
  assert (UC : U Ef (SOff SA_C 0) = c).
  { unfold SA_C. rewrite U_SOff, Ucf, Z.add_0_r. apply zcanon_id. unfold M64. lia. }
  pose proof (range_addressable_of_block SEGS B LAWS ly S W mem2 md2 b m c 9236 HAR2 Hin ltac:(lia) ltac:(lia))
    as HRA2.
  unfold sh_ok, mr_SH. repeat apply Forall_cons; try apply Forall_nil.
  - apply (shent_ok_of_range SEGS (w_H W) mem2 Ef mr_Bx SA_C c 9236 c SP.MC_REFUSED (SP.MC_REFUSED + 4));
    [exact HRA2 | exact UBx | exact UC | unfold SP.MC_REFUSED; lia | unfold SP.MC_REFUSED; lia
    | intros x Hx; cbn [Z.min Z.max] in Hx; unfold SP.MC_REFUSED, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia].
  - apply (shent_ok_of_range SEGS (w_H W) mem2 Ef mr_Bx SA_C c 9236 c SP.MC_NKEPT (SP.MC_NKEPT + 4));
    [exact HRA2 | exact UBx | exact UC | unfold SP.MC_NKEPT; lia | unfold SP.MC_NKEPT; lia
    | intros x Hx; cbn [Z.min Z.max] in Hx; unfold SP.MC_NKEPT, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia]. }
(* the tail from 0x87920: the checks of n_kept, n_kept + 1, refused + 1, the epilogue *)
pose proof (paj_run (fx := fx1) B LAWS) as RUNf.
paj_run_tok RUNf HS HJ2 SHOKf mr_Bspan.
{ mr_awrK Uspf Ucf Hcwr HSTK. }
(* the run's env Ev is Ef with the fresh atoms the tail added *)
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ (restrict _ _) |- _ => set (Ev := Ex) in * end.
assert (EV1 : ew Ev 1 = getr regs 1)
  by (unfold Ev; repeat (rewrite ew_ewset_other by lia); rewrite OLDf by lia; exact E1).
assert (EV10 : bv_unsigned (ew Ev 10) = c) by (unfold Ev; repeat (rewrite ew_ewset_other by lia); exact Ucf).
assert (EV33 : ew Ev 33 = Z_to_bv 64 (Z.of_nat (length (SM.mc_kept mc))))
  by (unfold Ev; repeat (rewrite ew_ewset_other by lia); rewrite OLDf by lia; exact E33).
assert (EV34 : ew Ev 34 = Z_to_bv 64 (SM.mc_refused mc))
  by (unfold Ev; repeat (rewrite ew_ewset_other by lia); rewrite OLDf by lia; exact E34).
assert (HAEV : env_agree 32 (Ereg regs (mr_extra (Z.of_nat (length (SM.mc_kept mc))) (SM.mc_refused mc))) Ev).
{ unfold Ev. split.
  - intros k Hk. repeat (rewrite ew_ewset_other by lia). apply (proj1 HAEf). lia.
  - cbn [ed ewset]. exact (proj2 HAEf). }
(* the two cells the tail stored: refused + 1 (lw, addi 1, sw as in mr_walk_full) and n_kept + 1 *)
lazymatch goal with
| HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
  let rg3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ev ssx (restrict (w_H W) msc) 3%nat rg3 HS eq_refl) as HR3;
  let rg4 := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ev ssx (restrict (w_H W) msc) 4%nat rg4 HS eq_refl) as HR4
end.
cbn [restrict ms_mem] in HR3, HR4.
pose proof (field_of_region_any (segs := SEGS) Ev _ 10%nat c _ 8200 8204 8200 8204 8200 4%N
  (SAlu ALU_ADD (SExt true 32 (SOff 34 0)) (SLit 1)) HR3 EV10 ltac:(cbn; left; reflexivity) ltac:(cbn; lia)) as VR.
pose proof (field_of_region_any (segs := SEGS) Ev _ 10%nat c _ 9132 9136 9132 9136 9132 4%N
  (SOff 33 1) HR4 EV10 ltac:(cbn; left; reflexivity) ltac:(cbn; lia)) as VN.
assert (VRv : bv_unsigned (sv_denot Ev (SAlu ALU_ADD (SExt true 32 (SOff 34 0)) (SLit 1)))
              mod 2 ^ (8 * Z.of_N 4) = SM.mc_refused mc + 1).
{ change (bv_unsigned (sv_denot Ev (SAlu ALU_ADD (SExt true 32 (SOff 34 0)) (SLit 1))))
    with (U Ev (SAlu ALU_ADD (SExt true 32 (SOff 34 0)) (SLit 1))).
  rewrite U_SAlu, U_SExt, U_SLit, U_SOff, EV34, Z.add_0_r.
  rewrite unsigned_lit_small by lia.
  change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
  apply mr_incr32. lia. }
rewrite VRv in VR. cbn [N.to_nat] in VR.
rewrite (l0_soff1 Ev 33 _ EV33 ltac:(lia) ltac:(lia)) in VN. cbn [N.to_nat] in VN.
(* the tail kept every byte but its frame and the two cells *)
lazymatch goal with
| HFx : frame_of Ef _ (mrestrict _ mem2) (mrestrict _ (ms_mem ?mf)) |- _ =>
  assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (c + 9132 <= a < c + 9136) ->
    ~ (spZ regs - 48 <= a < spZ regs) -> rdW W (ms_mem mf) a = rdW W mem2 a)
  by (intros a Ha H1 H2 H3; exact (KF _ _ _ _ HFx Uspf Ucf ltac:(vm_compute; reflexivity) a Ha H1 H2 H3))
end.
(* the ret at 0x87974 *)
pose proof (paj_ret_at (fx := fx1) (PL := PL_seg) (PI := PI)) as RETf.
lazymatch goal with
| HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
  prreg HS (1%bv : bv 5) R1;
  eapply (RETf W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  intros mat'; apply (apost_baseF_of_base (fx := fx1) SEGS); unfold apost_base;
  exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
  split; [cbn [ms_regs]; rewrite R1, EV1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|];
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ regs
            (mr_extra (Z.of_nat (length (SM.mc_kept mc))) (SM.mc_refused mc)) HS);
          [exact HAEV | vm_compute; reflexivity]|]
end.
rewrite HSTK in Hslo.
split.
{ (* the block holds m_refuse mc line knock: the text in kept[n_kept], n_kept + 1, refused + 1, the rest kept *)
  apply (MF.mr_enc_kept knock (rdW W mem) _ c mc line HMC H8 HRF Hline).
  - intros i Hi. rewrite HsnL in Hi. rewrite HsnB, Hd.
    rewrite KEEPF by lia. apply HBY. lia.
  - apply mr_sa_val_of. exact VN.
  - apply mr_sa_val_of. exact VR.
  - intros a Ha H1 H2 H3. rewrite HsnL, Hd in H1. unfold SP.SEG_M_SIZE, SP.MC_NKEPT, SP.MC_REFUSED in *.
    rewrite KEEPF by lia. rewrite HK2 by lia. apply KEEPC; lia. }
split.
{ intros a Ha HnS HnE.
  assert (H1 : ~ (c + 8200 <= a < c + 8204))
    by (intros Hq; apply HnE; right; right; unfold SP.MC_REFUSED; lia).
  assert (H2 : ~ (c + 9132 <= a < c + 9136))
    by (intros Hq; apply HnE; right; left; unfold SP.MC_NKEPT; lia).
  assert (H3 : ~ (c + 8204 + 112 * Z.of_nat (length (SM.mc_kept mc)) <= a <
                  c + 8204 + 112 * Z.of_nat (length (SM.mc_kept mc)) + 112))
    by (intros Hq; apply HnE; left; rewrite Hd; unfold SP.MC_KEPT_LEN; lia).
  rewrite KEEPF by lia. rewrite HK2 by lia. apply KEEPC; lia. }
split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs S). destruct S; reflexivity.
Qed.
(* inside the Sections, so the Section hypotheses (TL, VOBJS, SNP) show as its assumptions *)
About mr_arm_kept0.
Print Assumptions mr_arm_kept0.

End e.
End f.
End d.
