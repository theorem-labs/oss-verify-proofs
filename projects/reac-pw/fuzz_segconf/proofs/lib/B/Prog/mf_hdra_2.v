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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 322 of its 369 lines of code are new or changed and 406 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140), segment S_MF_HDRA of
   lib/B/Prog/m_file_m.v, the point walk RMC -> REF / RS1 (lib/B/Prog/mf_hdra_m.v). A walk lane of the image-B m_file-family owner's
   G2B (a point worker, on a working branch).
   proves no function (kind: segment lemma of m_file's image-B walk: the point RMC -> REF / RS1 of segment S_MF_HDRA).

   hda_rmc : HDA_REF_stmt B n -> HDA_RS1_stmt B n -> HDA_RMC_stmt B n.
   THE CODE (the neutral listing of m_file in image B lines 242-255; RMC = BASE + AF_m_file + 0x3c0):
     0x86500 `beqz a0,867c0`       no ']' (a0 = 0, k = j - i): REF; m_header refuses (mf_hdra_t.v hd_hdr_refuse_nf)
     0x86504 `li a1,-1`
     0x86508 `beq a0,a1,86e84`     the UBSan trap (close = (char * )-1)
     0x8650c `addi a1,a0,1`
     0x86510 `bne a1,s4,867c0`     close + 1 <> e (S k <> |sl|): REF; m_header refuses (hd_hdr_refuse_end)
     0x86514 `li a1,-1`
     0x86518 `beq s10,a1,86e84`    the UBSan trap (s = (char * )-1)
     0x8651c `addi s10,s10,1`; 0x86520 `sd s10,208(s1)`; 0x86524 `sd a0,200(s1)`; 0x86528 `addi a0,s1,208`;
     0x8652c `addi a1,s1,200`; 0x86530 `jal 879cc <strip>`, which returns to 0x86534 = RS1.
   THE TRAPS: each is psrr_branch_tok's taken edge, refuted from the text's place: mf_loop's
   sa_addr (rdW Wc memc) p (|rest| + 1) gives 0 <= p and p + |rest| + 1 <= 2 ^ 63, and close = p + i + k (k < j - i)
   and s = p + i lie below p + |line| <= p + |rest|, so neither is 2 ^ 64 - 1, the value of `li a1,-1`.
   THE WALK: the token executor over lib/B/Prog/m_file_sd.v's mf_seed at RMC, the frame cells' region 1 with the
   write window [200, 216) (the two stores 0x86520 / 0x86524); after each run the reader is unchanged outside
   [s1 + 200, s1 + 216) (kept_of_frame), so m_file_k.v's mf_keep_run_s keeps mf_core, mf_cells, mf_loop and
   mf_val_keep the cell 152(s1) (hd2_keep). The new 208(s1) = p + i + 1 and 200(s1) = close = p + j - 1 are the run's
   final chunks at 208 / 200 (PaDenot.v field_of_region). The `jal` by m_file_rf.v's mf_jal_step (the slot
   PCall SS_strip 1 at AF_m_file + 0x3f0), its target pa_sigma SS_strip = BASE + AF_strip by SIGP; the call by
   m_file_strip.v's mf_strip_call at osc = 208, oec = 200 over the text's bytes [i + 1, j - 1); its post is RS1's
   208(s1) = p + hda_q1 rest i j and 200(s1) = p + hda_r1 rest i j (mf_hdra_t.v's definitions), hda_close from the
   bne's fall-through (k = j - i - 1) and hd_close_pos (k >= 1); s5 = 0x20 and s11 = line + 1 are callee-saved.
   POSITIONAL NAMES (checked against the listing by what each is): x10 = a0 (memchr's answer), x26 = s10 (s),
   x20 = s4 (e), x21 = s5, x27 = s11, x9 = s1 (atom 2 in mf_seed); the cells 208(s1) = b and 200(s1) = be
   (the image-B m_file cut map section 3 row 8); the jal's listing offset HDA_J_STRIP1 = AF_m_file + 0x3f0 (pc 0x86530), the return
   HDA_RS1 = AF_m_file + 0x3f4 (0x86534), the refusal HDA_REF = AF_m_file + 0x680 (0x867c0). 8 checked, 0 elsewhere.
   Section hypotheses: VOBJS (mf_seed), SIGP (the jal's target, the lane's shared list), STRIP (strip_contract at
   BASE + AF_strip and SegInstB.STK_strip, at every FP state). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaNoChain PaArt PaFx SegObj SegGlob SegPgBase SegBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k strip_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_refuse_c m_file_rf m_file_strip.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_hdra_t mf_hdra_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the state's form, computed *)
Ltac hd2_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.

(* a membership in a computed chunk list *)
Ltac hd2_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* the taken edge of a UBSan trap `beq x,a1` with a1 = -1: x's value Ua is not 2 ^ 64 - 1 *)
Ltac hd2_trap Hc Ua :=
  rewrite branch_eq_U, Ua, U_SLit in Hc;
  lazymatch type of Hc with context [zcanon ?z] => replace (zcanon z) with (2 ^ 64 - 1) in Hc by reflexivity end;
  apply Z.eqb_eq in Hc; lia.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
(* the jal's target (SegObj.v seg_sig_prog; the lane's shared list, as m_file_rf.v takes it) *)
Hypothesis SIGP : seg_sig_prog.
(* the callee, at every FP state (the image-B m_file segment table's strip row) *)
Hypothesis STRIP : forall fx0 : YK11.FPState, @strip_contract fx0 rc SK SEGS B (BASE + AF_strip) SegInstB.STK_strip.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the line's facts across a run that writes only [s1 + 200, s1 + 216) (m_file_k.v mf_keep_run_s with that set),
   and the frame cells below 200(s1) *)
Lemma hd2_keep : forall v lyc Sc (Wc : world SEGS) memc mdc pos mcc cur line p rest mem2 md2,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur ->
  mf_loop v Wc memc mcc cur line p rest ->
  ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem2 md2 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 200 <= a < mf_s1 (mv_sp v) + 216) ->
     rdW Wc mem2 a = rdW Wc memc a) ->
  mf_core B v lyc Sc Wc mem2 md2 pos MF_LOW_OFF mcc /\ mf_cells v lyc pos mem2 Wc cur /\
  mf_loop v Wc mem2 mcc cur line p rest /\
  (forall o x, 16 <= o -> o + 8 <= 200 -> mf_slot v memc Wc o x -> mf_slot v mem2 Wc o x).
Proof.
intros v lyc Sc Wc memc mdc pos mcc cur line p rest mem2 md2 CX CORE CELLS LOOP HJ2 K.
set (RW := fun a => mf_s1 (mv_sp v) + 200 <= a < mf_s1 (mv_sp v) + 216) in K.
pose proof CORE as (HJ & _ & _ & VSH & _ & _ & Hmc & _).
pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V136 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Sp1.
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Bk1 & Bk2 & _).
pose proof (Z.mod_pos_bound (mv_sp v - 320) 32 ltac:(lia)) as M32.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
assert (RWok : forall a, RW a -> mf_rw v lyc pos a)
  by (intros a Ha; unfold mf_rw; unfold RW in Ha; right; right; right; right; right; lia).
assert (RWS : mf_rws v RW) by (intros a Ha _; right; unfold RW in Ha; lia).
destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur mem2 md2 RW MF_LOW_OFF cur mcc CX CORE CELLS
  HJ2 K RWok RWS) as (C1 & C2 & C3).
- intros i Hi. apply (mf_val_keep Wc Wc memc mem2 RW _ 1 _ K);
    [unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia | | exact (VSH i Hi)].
  intros k Hk HR. unfold RW, mf_s1 in HR. change (Z.of_nat 1) with 1 in Hk. unfold SHADOW_OFF in HR. lia.
- apply (mf_val_keep Wc Wc memc mem2 RW _ 8 _ K);
    [unfold mf_s1; lia | change (Z.of_nat 8) with 8; unfold mf_s1; lia | | exact V136].
  intros k Hk HR. unfold RW in HR. change (Z.of_nat 8) with 8 in Hk. lia.
- apply (mf_mconf_keep Wc Wc memc mem2 RW _ _ K); [lia | unfold seg_spec.SEG_M_SIZE in *; lia | | exact Hmc].
  intros a Ha HR. unfold RW, mf_s1 in HR. unfold seg_spec.SEG_M_SIZE in *. lia.
- split; [exact C1|]. split; [exact C2|]. split; [exact (C3 _ _ _ _ _ LOOP)|].
  intros o x Ho1 Ho2 V. unfold mf_slot in V |- *.
  apply (mf_val_keep Wc Wc memc mem2 RW _ 8 _ K);
    [unfold mf_s1; lia | change (Z.of_nat 8) with 8; unfold mf_s1; lia | | exact V].
  intros k Hk HR. unfold RW in HR. change (Z.of_nat 8) with 8 in Hk. lia.
Qed.

(* the run's write permission: region 1 (base s1, window [200, 216)) is the caller's real stack below sp0, every
   other region read-only *)
Ltac hd2_awr v U2v HSTKv :=
  lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
  repeat first
    [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat (mf_s1 (mv_sp v) - mv_sp v));
        [ reflexivity | rewrite U2v; ring
        | cbn [YP09.r_wlo YP09.r_whi]; try rewrite HSTKv; unfold mf_s1; lia
        | cbn [YP09.r_wlo YP09.r_whi]; unfold mf_s1; lia |] ];
  apply awr_ok_nil.
(* the reader after a run equals the start reader mc outside [s1 + 200, s1 + 216) (K, updated); the run's frame
   hypotheses and the machine states no hypothesis names any more are dropped, the current one named ms *)
Ltac hd2_k v mc K HS U2v :=
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict (w_H ?W) ?m0) (mrestrict _ ?m1) |- _ =>
    let K1 := fresh "K" in
    assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 200 <= a < mf_s1 (mv_sp v) + 216) ->
      aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mc a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hna := fresh "Hna" in
      intros a Ha Hna; transitivity (aview SEGS (w_H W) m0 a); [|exact (K a Ha Hna)];
      refine (kept_of_frame Ex rs (w_H W) m0 m1 (fun x => mf_s1 (mv_sp v) + 200 <= x < mf_s1 (mv_sp v) + 216)
        HFr _ a Ha Hna);
      let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
      let Hinw := fresh "Hinw" in let Hr := fresh "Hr" in
      intros bb wlo whi x Hinw Hr; vm_compute in Hinw; cbv beta;
      repeat (let Hq := fresh "Hq" in destruct Hinw as [Hq | Hinw];
        [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?U2v in Hr; lia |]); destruct Hinw
    | clear K; rename K1 into K ] end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with old : machine_state |- _ =>
    lazymatch type of HS with context [old] => fail | _ => clear old end end;
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => try rename msx into ms end.

Lemma hda_rmc : forall n, HDA_REF_stmt B n -> HDA_RS1_stmt B n -> HDA_RMC_stmt B n.
Proof.
intros n REF RS1. unfold HDA_RMC_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j k HL RA HH Hk HMC R10 R26 R20 R21 R27.
pose proof HL as (CX & LS & FRM & CORE & CELLS & Hn & Hne & LOOP & NP).
pose proof HH as (HL512 & Hij & HjL & HSL & HLB & HFIN).
pose proof CORE as (HJ & _).
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Sp1.
pose proof LOOP as (_ & _ & _ & _ & (PA1 & PA2 & _) & Hcurok & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE Hcurok) as Hcur.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.mod_pos_bound (mv_sp v - 320) 32 ltac:(lia)) as M32.
pose proof (hd_line_le rest) as HLr.
assert (Lsl : length (hda_sl rest i j) = (j - i)%nat) by (unfold hda_sl; apply hd_slice_length; lia).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur 0 [] HDA_RMC true false [] false false
  [] false CX CORE RB (fun _ => CELLS) Hcur ltac:(intros Hf; discriminate Hf) ltac:(lia)
  ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos cur 0 []) as E eqn:HE.
assert (EE : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> ew E k0 = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j0, (32 + j0 < A_TEXT)%nat -> ew E (32 + j0) = nth j0 (mf_extra v lyc pos cur 0 []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. cbn [Nat.add nth mf_extra map app] in E32.
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64, mf_s1; apply unsigned_lit_small; lia).
assert (E26 : ew E 26 = Z_to_bv 64 (p + Z.of_nat i)) by (rewrite (EE 26%nat 26%bv eq_refl), R26; reflexivity).
assert (E20 : ew E 20 = Z_to_bv 64 (p + Z.of_nat j)) by (rewrite (EE 20%nat 20%bv eq_refl), R20; reflexivity).
assert (U20 : U E (SOff 20 0) = p + Z.of_nat j) by (apply U_atom; [exact E20 | lia]).
assert (U26 : U E (SOff 26 0) = p + Z.of_nat i) by (apply U_atom; [exact E26 | lia]).
(* region 1 (the frame cells) written only at [200, 216) *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 200 216) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 200 216 HR1
      ltac:(destruct HR1 as (_ & _ & HW & _); intros o Ho; apply HW; cbv [mf_r_slots YP09.r_wlo YP09.r_whi]; lia))) as HS end.
clear HS0 HR1. hd2_norm HS.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 200 <= a < mf_s1 (mv_sp v) + 216) ->
  rdW Wc memc a = rdW Wc memc a) by reflexivity.
unfold mf_at.
revert HMC R10. destruct (Nat.ltb_spec k (j - i)) as [HkL|HkL]; intros HMC R10; cbv iota in HMC, R10.
2:{ (* sl has no ']': a0 = 0 *)
  assert (U10 : U E (SOff 10 0) = 0) by (apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity | lia]).
  psrr_branch_tok RUN BR HS SHOK Bspan.
  - (* 0x86500 taken: to REF; m_header refuses *)
    paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_REF; [hd2_awr v U2 HSTK|].
    hd2_k v memc K HS U2.
    destruct (hd2_keep v lyc Sc Wc memc mdc pos mcc cur line p rest _ _ CX CORE CELLS LOOP HJ K)
      as (CORE' & CELLS' & LOOP' & SLK).
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
    prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
    prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
    prreg HS (27%bv : bv 5) Q27.
    assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
    { apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
      - rewrite Q2. apply EE. reflexivity.
      - rewrite Q3. apply EE. reflexivity.
      - rewrite Q4. apply EE. reflexivity.
      - rewrite Q8. apply EE. reflexivity.
      - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
      - rewrite Q18, E32, R18. reflexivity.
      - rewrite Q23. apply EE. reflexivity.
      - rewrite Q24. apply EE. reflexivity.
      - rewrite Q19. apply EE. reflexivity.
      - rewrite Q22. apply EE. reflexivity.
      - rewrite Q25. apply EE. reflexivity. }
    pmkst HS.
    apply (REF v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur line p rest).
    + exact (conj CX (conj LS (conj FRM (conj CORE' (conj CELLS' (conj Hn (conj Hne (conj LOOP'
        (SLK 152 _ ltac:(lia) ltac:(lia) NP))))))))).
    + exact RA'.
    + rewrite <- HFIN, (hd_hdr_refuse_nf mcc _ (line + 1) HMC). reflexivity.
    + rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
  - (* 0x86500 not taken: a0 <> 0, but a0 = 0 *)
    rewrite branch_eq_U, U10, U_lit in Hc by lia. discriminate Hc. }
(* the first ']' at k < j - i: a0 = s + k, k >= 1 since sl[0] = '[' *)
assert (Hij' : (i < j <= length (mf_line rest))%nat) by lia.
pose proof (hd_close_pos rest i j k Hij' HLB HMC) as Hk1.
assert (E10 : ew E 10 = Z_to_bv 64 (p + Z.of_nat (i + k))) by (rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity).
assert (U10 : U E (SOff 10 0) = p + Z.of_nat (i + k)) by (apply U_atom; [exact E10 | lia]).
assert (U10' : U E (SOff 10 1) = p + Z.of_nat (i + k) + 1) by (apply U_atom_off; [exact E10 | lia | lia]).
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* 0x86500 taken: a0 = p + i + k >= 1, so not 0 *)
  rewrite branch_eq_U, U10, U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia. }
clear Hc.
(* 0x86504 `li a1,-1`; stop at the trap branch 0x86508 *)
paj_run_tok RUN HS HJ SHOK Bspan; [hd2_awr v U2 HSTK|].
hd2_k v memc K HS U2.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* 0x86508 taken, the UBSan trap: close = p + i + k < 2 ^ 63, not 2 ^ 64 - 1 *)
  exfalso. hd2_trap Hc U10. }
clear Hc.
(* 0x8650c `addi a1,a0,1`; stop at 0x86510 *)
paj_run_tok RUN HS HJ SHOK Bspan; [hd2_awr v U2 HSTK|].
hd2_k v memc K HS U2.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* 0x86510 taken: close + 1 <> e, to REF; m_header refuses *)
  rewrite branch_ne_U, U10', U20 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  assert (HSk : S k <> length (hda_sl rest i j)) by (rewrite Lsl; lia).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_REF; [hd2_awr v U2 HSTK|].
  hd2_k v memc K HS U2.
  destruct (hd2_keep v lyc Sc Wc memc mdc pos mcc cur line p rest _ _ CX CORE CELLS LOOP HJ K)
    as (CORE' & CELLS' & LOOP' & SLK).
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
  prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
  prreg HS (27%bv : bv 5) Q27.
  assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
  { apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
    - rewrite Q2. apply EE. reflexivity.
    - rewrite Q3. apply EE. reflexivity.
    - rewrite Q4. apply EE. reflexivity.
    - rewrite Q8. apply EE. reflexivity.
    - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
    - rewrite Q18, E32, R18. reflexivity.
    - rewrite Q23. apply EE. reflexivity.
    - rewrite Q24. apply EE. reflexivity.
    - rewrite Q19. apply EE. reflexivity.
    - rewrite Q22. apply EE. reflexivity.
    - rewrite Q25. apply EE. reflexivity. }
  pmkst HS.
  apply (REF v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur line p rest).
  + exact (conj CX (conj LS (conj FRM (conj CORE' (conj CELLS' (conj Hn (conj Hne (conj LOOP'
      (SLK 152 _ ltac:(lia) ltac:(lia) NP))))))))).
  + exact RA'.
  + rewrite <- HFIN, (hd_hdr_refuse_end mcc _ (line + 1) k HMC HSk). reflexivity.
  + rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
- (* 0x86510 not taken: close + 1 = e, the close is sl's last byte (k = j - i - 1) *)
  rewrite branch_ne_U, U10', U20 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Ek : k = (j - i - 1)%nat) by lia.
  assert (HCL : hda_close rest i j) by (split; [rewrite <- Ek; exact HMC | lia]).
  clear Hc.
  (* 0x86514 `li a1,-1`; stop at the trap branch 0x86518 *)
  paj_run_tok RUN HS HJ SHOK Bspan; [hd2_awr v U2 HSTK|].
  hd2_k v memc K HS U2.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { (* 0x86518 taken, the UBSan trap: s = p + i < 2 ^ 63, not 2 ^ 64 - 1 *)
    exfalso. hd2_trap Hc U26. }
  clear Hc.
  (* 0x8651c .. 0x8652c: s10 = s + 1, 208(s1) = s + 1, 200(s1) = close, a0 = s1 + 208, a1 = s1 + 200; stop at the
     jal 0x86530 *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_J_STRIP1; [hd2_awr v U2 HSTK|].
  hd2_k v memc K HS U2.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (mf_r_slots true false [])) in
    pose proof (st_ok_pi_region_nth E ssx (restrict (w_H Wc) msx) 1 r1 HS eq_refl) as HRf end.
  cbn [ms_mem restrict mkst] in HRf.
  pose proof (field_of_region (segs := SEGS) E _ 2%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 208 8%N (SOff 26 1)
    (p + Z.of_nat (i + 1)) HRf U2 ltac:(hd2_in)
    ltac:(cbn [sv_denot]; rewrite E26, unsigned_lit_small by lia; f_equal; lia)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as V208.
  pose proof (field_of_region (segs := SEGS) E _ 2%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 200 8%N (SOff 10 0)
    (p + Z.of_nat (j - 1)) HRf U2 ltac:(hd2_in)
    ltac:(cbn [sv_denot]; rewrite E10, unsigned_lit_small by lia; f_equal; lia)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as V200.
  change (N.to_nat 8) with 8%nat in V208, V200. clear HRf.
  destruct (hd2_keep v lyc Sc Wc memc mdc pos mcc cur line p rest _ _ CX CORE CELLS LOOP HJ K)
    as (CORE1 & CELLS1 & LOOP1 & SLK).
  pose proof (SLK 152 _ ltac:(lia) ltac:(lia) NP) as NP1.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
  prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
  prreg HS (27%bv : bv 5) Q27. prreg HS (21%bv : bv 5) Q21.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  assert (RA1 : mf_regs_at B v lyc pos (ms_regs ms)).
  { apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
    - rewrite Q2. apply EE. reflexivity.
    - rewrite Q3. apply EE. reflexivity.
    - rewrite Q4. apply EE. reflexivity.
    - rewrite Q8. apply EE. reflexivity.
    - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
    - rewrite Q18, E32, R18. reflexivity.
    - rewrite Q23. apply EE. reflexivity.
    - rewrite Q24. apply EE. reflexivity.
    - rewrite Q19. apply EE. reflexivity.
    - rewrite Q22. apply EE. reflexivity.
    - rewrite Q25. apply EE. reflexivity. }
  assert (G10 : getr (ms_regs ms) 10 = w64 (mf_s1 (mv_sp v) + 208)) by (rewrite Q10, U2; reflexivity).
  assert (G11 : getr (ms_regs ms) 11 = w64 (mf_s1 (mv_sp v) + 200)) by (rewrite Q11, U2; reflexivity).
  assert (G21 : getr (ms_regs ms) 21 = w64 0x20) by (rewrite Q21, (EE 21%nat 21%bv eq_refl); exact R21).
  assert (G27 : getr (ms_regs ms) 27 = w64 (line + 1)) by (rewrite Q27, (EE 27%nat 27%bv eq_refl); exact R27).
  pmkst HS.
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k0)] =>
    change (Z_to_bv 64 (BASE + k0)) with (Z_to_bv 64 (BASE + HDA_J_STRIP1)) end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?md0) _ => set (mdw := md0) in * end.
  (* 0x86530: jal strip *)
  apply (mf_jal_step Wc (ms_regs ms) (ms_mem ms) mdw _ HDA_J_STRIP1 SS_strip);
    [vm_compute; reflexivity | unfold HDA_J_STRIP1, AF_m_file; lia |].
  intros mat'.
  assert (SIGR : pa_sigma SS_strip = BASE + AF_strip).
  { rewrite (SIGP SS_strip) by (unfold seg_prog_syms; cbn [In]; tauto). f_equal; try (vm_compute; reflexivity). }
  rewrite SIGR.
  set (mdc' := with_vm_backing (m_vm_lazy mdw) mat' mdw).
  set (regsc := regupd (ms_regs ms) 1%bv (Z_to_bv 64 (BASE + (HDA_J_STRIP1 + 4)))).
  pose proof CORE1 as (HJ1 & CRk1).
  pose proof pa_segs_low as Hsegs.
  pose proof (ajournal_materialize SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ1) as HJ1'.
  fold mdc' in HJ1'.
  assert (CORE1' : mf_core B v lyc Sc Wc (ms_mem ms) mdc' pos MF_LOW_OFF mcc) by exact (conj HJ1' CRk1).
  assert (GR : forall r : bv 5, r <> 1%bv -> getr regsc r = getr (ms_regs ms) r)
    by (intros r Hr; apply mf_getr_upd1; exact Hr).
  assert (RAc : mf_regs_at B v lyc pos regsc).
  { apply (mf_regs_at_of B v lyc pos (ms_regs ms) regsc RA1); apply GR; discriminate. }
  assert (ERS : HDA_J_STRIP1 + 4 = HDA_RS1) by (unfold HDA_J_STRIP1, HDA_RS1; lia).
  (* strip(s1 + 208, s1 + 200) over the text's bytes [i + 1, j - 1) *)
  apply (mf_strip_call B STRIP v lyc Sc Wc regsc (ms_mem ms) mdc' pos MF_LOW_OFF mcc cur line p rest (mf_next p rest)
    HDA_RS1 208 200 (i + 1) (j - 1) CX LS CORE1' CELLS1 LOOP1 NP1 RAc).
  + rewrite <- ERS. apply mf_getr_upd1_same.
  + unfold HDA_RS1, AF_m_file; lia.
  + vm_compute. reflexivity.
  + lia.
  + lia.
  + vm_compute. reflexivity.
  + lia.
  + lia.
  + vm_compute. reflexivity.
  + lia.
  + rewrite GR by discriminate. exact G10.
  + rewrite GR by discriminate. exact G11.
  + lia.
  + exact V208.
  + exact V200.
  + intros S2 W2 regs2 mem2 md2 HWle LS2 CORE2 CELLS2 LOOP2 NP2 RA2 HPR V208' V200' _.
    pose proof (hd_strip_le rest (i + 1) (j - 1) ltac:(lia)) as Hsle.
    apply (RS1 v lyc S2 W2 regs2 mem2 md2 pos mcc cur line p rest i j).
    * exact (conj CX (conj LS2 (conj FRM (conj CORE2 (conj CELLS2 (conj Hn (conj Hne (conj LOOP2 NP2)))))))).
    * exact RA2.
    * exact HH.
    * exact HCL.
    * replace (p + Z.of_nat (hda_q1 rest i j)) with
        (p + Z.of_nat (i + 1) + Z.of_nat (strip_lead (slice (i + 1) (j - 1) rest))) by (unfold hda_q1; lia).
      exact V208'.
    * replace (p + Z.of_nat (hda_r1 rest i j)) with
        (p + Z.of_nat (j - 1) - Z.of_nat (strip_trail (slice (i + 1) (j - 1) rest))) by (unfold hda_r1; lia).
      exact V200'.
    * transitivity (getr regsc 21); [exact (HPR 21 ltac:(unfold acallee_saved; lia))|].
      rewrite GR by discriminate. exact G21.
    * transitivity (getr regsc 27); [exact (HPR 27 ltac:(unfold acallee_saved; lia))|].
      rewrite GR by discriminate. exact G27.
Qed.
End e.
End f.
End d.

(* inside nothing: the lemma's assumptions *)
About hda_rmc.
Print Assumptions hda_rmc.
