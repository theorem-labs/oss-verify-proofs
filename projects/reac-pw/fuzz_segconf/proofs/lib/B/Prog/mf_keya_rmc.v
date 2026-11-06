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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 269 of its 319 lines of code are new or changed and 403 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3), segment S_MF_KEYA, piece KB_RMC: from memchr's
   return KB_RMC 0x86628 to the refusal's jal KB_JREF 0x867dc or to the key's strip call KB_S1 0x86658
   (mf_keya_d.v kb_rmc : KB_REF_stmt n -> KB_S1_stmt n -> KB_RMC_stmt n), in the form of plugin-hostd/fuzz_command's
   lib/A/Prog walks (origin/ossv/recipes 501c0d516c69). proves no function (kind: segment lemma of m_file's image-B
   walk, piece of S_MF_KEYA).
   THE CODE (the neutral listing of m_file in image B lines 316-332, 423-425):
     0x86628  ld a1,136(s1)        a1 = cur (136(s1) = mf_cur_ptr c cur, atom 37 of the seed)
     0x8662c  beqz a1 -> 0x867d4   cur = NULL: the refusal
     0x86630  beqz a0 -> 0x867d4   memchr found no equals sign (a0 = res = 0): the refusal
     0x86634  sd s10,208(s1); 0x86638 sd a0,200(s1); 0x8663c li a1,-1
     0x86640  beq a0,a1 -> 0x86e84 the UBSan trap (eq + 1 wraps)
     0x86644  addi a0,a0,1; 0x86648 sd a0,192(s1); 0x8664c sd s4,184(s1); 0x86650 addi a0,s1,208;
     0x86654  addi a1,s1,200; KB_S1 0x86658 jal strip
     0x867d4  mv a0,s9; 0x867d8 mv a1,s11; KB_JREF 0x867dc jal m_refuse
   No instrumented check and no call inside the piece; one trap branch.
   THE TRAP 0x86640 (beq a0,-1): the run stops at the branch (atom 10 = res has no fact); psrr_branch_tok splits it
   and the taken edge is refuted from res = p + i + ei <= p + |rest| < p + |rest| + 1 <= 2 ^ 63 < 2 ^ 64 - 1
   (mf_loop's sa_addr p (|rest| + 1), the found case of KB_RMC_stmt's memchr premise); the trap instruction is never
   executed.
   THE PROOF: one seed (m_file_sd.v mf_seed: cells = true, hnp = true, no extra chunk, no extra value) with the frame
   cell region rewindowed to [184, 216) (ast_ok_pi_set_region, region_ok_rewindow), so that every run of the piece
   writes only kr_rw = [s1 + 184, s1 + 216), which is inside m_file_k.v's mf_rw and mf_rws; token runs with
   psrr_branch_tok at the two beqz and at the trap. 136(s1) = atom 37 decides cur (0 exactly when cur = None, as
   image A's Hcur in m_file_s_keya_a.v, at image B's numbers: c <> 0 and mf_cur_range); a0 = res decides the found
   case (res <> 0 exactly when memchr gave Some ei, since p >= 4096). Every cut fact crosses the runs by m_file_k.v's
   mf_keep_run_s, mf_val_keep and mf_mconf_keep (the assertion CARRY); the four new slots 208 / 200 / 192 / 184 come from the
   final frame cell region (field_of_region_any). The model premises come from mf_keya_m.v's kb_model_refuse and
   kb_model_disp. Section hypotheses: VOBJS only. A walk lane of the image-B m_file-family owner's G2B (a piece agent). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_keya_m mf_keya_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the bytes the piece writes: the four scratch cells [s1 + 184, s1 + 216) *)
Definition kr_rw (s1 a : Z) : Prop := s1 + 184 <= a < s1 + 216.

(* the state's form, computed *)
Ltac kr_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.

(* a beqz on atom n holding v *)
Lemma kr_br_eq0 : forall E n v b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> (v =? 0) = b.
Proof.
intros E n v b H R Hc. rewrite branch_eq_U, (U_atom E n v H R), U_lit in Hc by lia. exact Hc.
Qed.
(* a beq of atom n holding v against a literal *)
Lemma kr_br_eqlit : forall E n v z b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = b -> (v =? zcanon z) = b.
Proof.
intros E n v z b H R Hc. rewrite branch_eq_U, (U_atom E n v H R), U_SLit in Hc. exact Hc.
Qed.
(* the 8-byte value of a chunk holding atom n + k *)
Lemma kr_soff_val : forall E n x k, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + k < 2 ^ 64 ->
bv_unsigned (sv_denot E (SOff n k)) mod 2 ^ (8 * Z.of_N 8) = x + k.
Proof.
intros E n x k H Hx Hxk. cbn [sv_denot]. rewrite H, (unsigned_lit_small x Hx), (unsigned_lit_small (x + k) Hxk).
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_small. exact Hxk.
Qed.

(* the registers mf_regs_at names, at the end of a run from the seed (s1 = atom 2, s2 = atom 32, the others their own
   atoms) *)
Ltac kr_ra HS RA EE R2 R9 R18 E32 :=
  let Q2 := fresh "Q" in let Q3 := fresh "Q" in let Q4 := fresh "Q" in let Q8 := fresh "Q" in
  let Q9 := fresh "Q" in let Q18 := fresh "Q" in let Q23 := fresh "Q" in let Q24 := fresh "Q" in
  let Q19 := fresh "Q" in let Q22 := fresh "Q" in let Q25 := fresh "Q" in
  prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8;
  prreg HS (9%bv : bv 5) Q9; prreg HS (18%bv : bv 5) Q18; prreg HS (23%bv : bv 5) Q23; prreg HS (24%bv : bv 5) Q24;
  prreg HS (19%bv : bv 5) Q19; prreg HS (22%bv : bv 5) Q22; prreg HS (25%bv : bv 5) Q25;
  apply (mf_regs_at_of _ _ _ _ _ _ RA);
  [ rewrite Q2; apply EE; reflexivity
  | rewrite Q3; apply EE; reflexivity
  | rewrite Q4; apply EE; reflexivity
  | rewrite Q8; apply EE; reflexivity
  | rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9; reflexivity
  | rewrite Q18, E32, R18; reflexivity
  | rewrite Q23; apply EE; reflexivity
  | rewrite Q24; apply EE; reflexivity
  | rewrite Q19; apply EE; reflexivity
  | rewrite Q22; apply EE; reflexivity
  | rewrite Q25; apply EE; reflexivity ].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a run keeps every byte outside RW when each of its windows lies in RW *)
Lemma kr_keep_step : forall E rs (H : word -> bool) (m0 m m' : word -> option byte) (RW : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> aview SEGS H m a = aview SEGS H m0 a) ->
(forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> RW a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> aview SEGS H m' a = aview SEGS H m0 a.
Proof.
intros E rs H m0 m m' RW HFr KM HW a Ha HR.
rewrite (kept_of_frame (segs := SEGS) E rs H m m' RW HFr HW a Ha HR). exact (KM a Ha HR).
Qed.

(* the windows of a run of the piece lie in [s1 + 184, s1 + 216) *)
Ltac kr_win B2 :=
  let b := fresh "bw" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "aw" in
  let Hw := fresh "Hw" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
  intros b wlo whi a Hw Hr; vm_compute in Hw;
  repeat (destruct Hw as [Hq | Hw];
    [injection Hq as <- <- <-; first [lia | rewrite B2 in Hr; unfold kr_rw; lia] |]);
  destruct Hw.
(* after a run: the bytes outside [s1 + 184, s1 + 216) still those of memchr's return *)
Ltac kr_after KM B2 :=
  lazymatch goal with
  | HFr : frame_of ?Eo ?rs (mrestrict ?H ?m1) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let KMn := fresh "KMn" in
    pose proof (kr_keep_step Eo rs H _ m1 (ms_mem msn) _ HFr KM ltac:(kr_win B2)) as KMn;
    clear HFr KM; rename KMn into KM
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
(* the writes a run may do: [s1 + 184, s1 + 216) of the frame cells (base atom 2 = s1), in m_file's stack frame
   [sp0 - STK, sp0) *)
Ltac kr_awr U2 d :=
  lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply (YCbq.awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat d);
        [reflexivity | rewrite U2; ring | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | ] ].

Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma kb_rmc : forall n, KB_REF_stmt B n -> KB_S1_stmt B n -> KB_RMC_stmt B n.
Proof.
intros n REF S1. unfold KB_RMC_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j res CX LS FRM CORE CELLS RA Hn Hr LOOP Hij HjL
  HRES HFIN R10 R26 R20 R27 NP.
pose proof CORE as (HJ & HPerm & _ & VSH & _ & _ & HMC & HMA & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V136 & _).
pose proof LOOP as (_ & _ & _ & _ & (Hp0 & Hp63 & _) & LCUR & _).
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HMP as (Hc0 & Hc16 & _).
pose proof HMA as (CA0 & CA1 & _).
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
destruct (mf_s1_facts B v CX) as (Ss1 & Ss2 & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Sp1.
assert (Hs1r : alloc_ceiling + 8000 <= mf_s1 (mv_sp v) <= 2 ^ 47) by (destruct Ss1 as [Q | Q]; rewrite Q; lia).
assert (HD : - SegInstB.STK_m_file <= mf_s1 (mv_sp v) - mv_sp v + 184 /\ mf_s1 (mv_sp v) - mv_sp v + 216 <= 0)
  by (rewrite HSTK; destruct Ss1 as [Q | Q]; rewrite Q; lia).
(* the mconf block lies below the allocator's ceiling *)
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Hbc4096 & Hbceil & _).
(* the text left lies in a live heap block: p >= 4096 *)
destruct (mf_loop_blk B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP)
  as (bt & mt & Hbt & Hbt1 & Hbt2 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt HAR Hbt) as (_ & Hbt4096 & _).
(* the sizes: memchr's answer lies in the line, inside the text left *)
pose proof (kb_line_len rest) as HLr.
assert (Hres : 0 <= res < 2 ^ 63).
{ revert HRES. destruct (memchr (slice i j (mf_line rest)) EQ) as [ei|] eqn:HM; intros HRES; [|lia].
  destruct (kb_memchr_some _ _ _ HM) as (Hei & _ & _). rewrite kb_slice_length in Hei by lia. lia. }
(* cur decides 136(s1): 0 exactly when cur = None *)
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE LCUR) as Hcur.
assert (Hcur0 : mf_cur_ptr (mv_c v) cur = 0 -> cur = None).
{ destruct cur as [gi|]; [|intros; reflexivity]. cbn [mf_cur_ptr].
  unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE. intros H0. exfalso. lia. }
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP) as Hnp.
(* every cut fact at a memory that keeps every byte outside [s1 + 184, s1 + 216) *)
assert (CARRY : forall mem2 md2,
  ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem2 md2 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ kr_rw (mf_s1 (mv_sp v)) a -> rdW Wc mem2 a = rdW Wc memc a) ->
  mf_core B v lyc Sc Wc mem2 md2 pos MF_LOW_OFF mcc /\ mf_cells v lyc pos mem2 Wc cur /\
  mf_loop v Wc mem2 mcc cur line p rest /\ mf_np v mem2 Wc (mf_next p rest)).
{ intros mem2 md2 HJ2 K2.
  destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur mem2 md2 (kr_rw (mf_s1 (mv_sp v)))
    MF_LOW_OFF cur mcc CX CORE CELLS HJ2 K2) as (C1 & C2 & C3).
  - intros a Ha. unfold kr_rw in Ha. unfold mf_rw. right; right; right; right; right. lia.
  - intros a Ha _. unfold kr_rw in Ha. right. lia.
  - intros k Hk. apply (mf_val_keep Wc Wc memc mem2 _ _ 1 _ K2).
    + unfold SHADOW_OFF. lia.
    + change (Z.of_nat 1) with 1. unfold SHADOW_OFF. lia.
    + intros k' Hk' HR. unfold kr_rw in HR.
      apply (mf_stack_apart B lyc Sc Wc memc mdc pos (SHADOW_OFF + frame_addr lyc 1 pos / 8 + k + k') HAR Hin);
        [lia | unfold mf_win; right; left; lia].
    + exact (VSH k Hk).
  - apply (mf_val_keep Wc Wc memc mem2 _ _ 8 _ K2);
      [lia | change (Z.of_nat 8) with 8; lia | intros k' Hk' HR; unfold kr_rw in HR; lia | exact V136].
  - apply (mf_mconf_keep Wc Wc memc mem2 _ _ _ K2);
      [lia | unfold seg_spec.SEG_M_SIZE in *; lia
      | intros a Ha HR; unfold kr_rw in HR; unfold seg_spec.SEG_M_SIZE in *; lia | exact HMC].
  - split; [exact C1|]. split; [exact C2|]. split; [exact (C3 _ _ _ _ _ LOOP)|].
    unfold mf_np, mf_slot in NP |- *.
    apply (mf_val_keep Wc Wc memc mem2 _ _ 8 _ K2);
      [lia | change (Z.of_nat 8) with 8; lia | intros k' Hk' HR; unfold kr_rw in HR; lia | exact NP]. }
(* the refusal leaf, KB_REF_stmt at the jal 0x867dc *)
assert (CREF : forall regs' mem' md', (memchr (slice i j (mf_line rest)) EQ = None \/ cur = None) ->
  ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem' md' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ kr_rw (mf_s1 (mv_sp v)) a -> rdW Wc mem' a = rdW Wc memc a) ->
  mf_regs_at B v lyc pos regs' -> getr regs' 10 = w64 (mv_c v) -> getr regs' 11 = w64 (line + 1) ->
  getr regs' 27 = w64 (line + 1) ->
  SRr SEGS Wc (mkCfg (mkst regs' (Z_to_bv 64 (BASE + KB_JREF)) mem' (seg_rom SEGS)) md') (MF_POST B v)).
{ intros regs' mem' md' Hm HJ' K' RA' R10' R11' R27'.
  destruct (CARRY mem' md' HJ' K') as (C1 & C2 & C3 & C4).
  exact (REF v lyc Sc Wc regs' mem' md' pos mcc cur line p rest CX LS FRM C1 C2 RA' Hn Hr C3
    (kb_model_refuse mcc cur (slice i j (mf_line rest)) line rest (mf_final v) Hm HFIN) C4 R10' R11' R27'). }
(* ---- the seed at KB_RMC: the frame cells (cells = true), 152(s1) = the next line's address (hnp = true) ---- *)
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [] KB_RMC true true []
  false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_OFF; lia)
  (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos cur (mf_next p rest) []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j0, (32 + j0 < A_TEXT)%nat ->
  ew E (32 + j0) = nth j0 (mf_extra v lyc pos cur (mf_next p rest) []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 5%nat ltac:(unfold A_TEXT; lia)) as E37.
cbn [Nat.add nth mf_extra map app] in E32, E37.
assert (G2 : ew E 2 = Z_to_bv 64 (mf_s1 (mv_sp v))) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v)) by (rewrite G2; apply unsigned_lit_small; lia).
assert (B2 : base_val E (Some 2%nat) = mf_s1 (mv_sp v)) by (cbn [base_val]; exact U2).
assert (E10 : ew E 10 = Z_to_bv 64 res) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E20 : ew E 20 = Z_to_bv 64 (p + Z.of_nat j)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E26 : ew E 26 = Z_to_bv 64 (p + Z.of_nat i)) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
(* the frame cells writable only at [184, 216) *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 184 216) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 184 216 HR1
      ltac:(intros o Ho; destruct HR1 as (_ & _ & HW & _); apply HW; cbn; lia))) as HS end.
clear HS0 HR1. kr_norm HS.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ kr_rw (mf_s1 (mv_sp v)) a -> rdW Wc memc a = rdW Wc memc a)
  by (intros; reflexivity).
unfold mf_at.
(* ---- 0x86628 ld a1,136(s1); the run stops at 0x8662c beqz a1 ---- *)
paj_run_tok RUN HS HJ SHOK Bspan; [kr_awr U2 (mf_s1 (mv_sp v) - mv_sp v) |].
kr_after KM B2.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* 0x8662c taken: cur = NULL, the refusal *)
  pose proof (kr_br_eq0 _ 37 _ true E37 Hcur Hc) as Hb. apply Z.eqb_eq in Hb. clear Hc.
  pose proof (Hcur0 Hb) as HcN.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KB_JREF; [kr_awr U2 (mf_s1 (mv_sp v) - mv_sp v) |].
  kr_after KM B2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (RA' : mf_regs_at B v lyc pos (ms_regs msx)) by (kr_ra HS RA EE R2 R9 R18 E32) end.
  prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (27%bv : bv 5) N27.
  pmkst HS.
  apply (CREF _ _ _ (or_intror HcN) HJ KM RA').
  + rewrite N10, (EE 25%nat 25%bv eq_refl). exact R25.
  + rewrite N11, (EE 27%nat 27%bv eq_refl). exact R27.
  + rewrite N27, (EE 27%nat 27%bv eq_refl). exact R27.
- (* 0x8662c not taken: cur = Some gi *)
  pose proof (kr_br_eq0 _ 37 _ false E37 Hcur Hc) as Hb. apply Z.eqb_neq in Hb. clear Hc.
  assert (Hsg : exists gi, cur = Some gi).
  { destruct cur as [gi|]; [exists gi; reflexivity | exfalso; apply Hb; reflexivity]. }
  destruct Hsg as (gi & ->).
  paj_run_tok RUN HS HJ SHOK Bspan; [kr_awr U2 (mf_s1 (mv_sp v) - mv_sp v) |].
  kr_after KM B2.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* 0x86630 taken: res = 0, memchr found no equals sign; the refusal *)
    pose proof (kr_br_eq0 _ 10 _ true E10 ltac:(lia) Hc) as Hb2. apply Z.eqb_eq in Hb2. clear Hc.
    assert (Hnf : memchr (slice i j (mf_line rest)) EQ = None).
    { revert HRES. destruct (memchr (slice i j (mf_line rest)) EQ) as [ei|] eqn:HM; intros HRES; [|reflexivity].
      exfalso. lia. }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan KB_JREF; [kr_awr U2 (mf_s1 (mv_sp v) - mv_sp v) |].
    kr_after KM B2.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
      assert (RA' : mf_regs_at B v lyc pos (ms_regs msx)) by (kr_ra HS RA EE R2 R9 R18 E32) end.
    prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (27%bv : bv 5) N27.
    pmkst HS.
    apply (CREF _ _ _ (or_introl Hnf) HJ KM RA').
    * rewrite N10, (EE 25%nat 25%bv eq_refl). exact R25.
    * rewrite N11, (EE 27%nat 27%bv eq_refl). exact R27.
    * rewrite N27, (EE 27%nat 27%bv eq_refl). exact R27.
  + (* 0x86630 not taken: res <> 0, the equals sign at ei *)
    pose proof (kr_br_eq0 _ 10 _ false E10 ltac:(lia) Hc) as Hb2. apply Z.eqb_neq in Hb2. clear Hc.
    revert HRES. destruct (memchr (slice i j (mf_line rest)) EQ) as [ei|] eqn:HM; intros HRES; [|exfalso; lia].
    subst res.
    destruct (kb_memchr_some _ _ _ HM) as (Hei & _ & _). rewrite kb_slice_length in Hei by lia.
    (* 0x86634 .. 0x8663c: the stores of s and the equals sign; the run stops at the trap branch 0x86640 *)
    paj_run_tok RUN HS HJ SHOK Bspan; [kr_awr U2 (mf_s1 (mv_sp v) - mv_sp v) |].
    kr_after KM B2.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* 0x86640 taken: the UBSan trap (eq + 1 wraps), refuted: eq = p + i + ei < 2 ^ 63 < 2 ^ 64 - 1 *)
      exfalso.
      pose proof (kr_br_eqlit _ 10 _ _ true E10 ltac:(lia) Hc) as Hb3. apply Z.eqb_eq in Hb3. clear Hc.
      lazymatch type of Hb3 with _ = zcanon ?z =>
        let r := eval vm_compute in (zcanon z) in change (zcanon z) with r in Hb3 end.
      lia.
    * (* 0x86640 not taken; 0x86644 .. 0x86654: 192(s1) = eq + 1, 184(s1) = e, a0 = s1 + 208, a1 = s1 + 200 *)
      clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan KB_S1; [kr_awr U2 (mf_s1 (mv_sp v) - mv_sp v) |].
      kr_after KM B2.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => rename msx into msF end.
      destruct (CARRY (ms_mem msF) _ HJ KM) as (CORE' & CELLS' & LOOP' & NP').
      assert (RA' : mf_regs_at B v lyc pos (ms_regs msF)) by (kr_ra HS RA EE R2 R9 R18 E32).
      prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (27%bv : bv 5) N27.
      (* the four scratch cells from the run's final frame cell region *)
      pose proof (st_ok_pi_region_nth E _ _ 1 _ HS eq_refl) as HRf. cbn [restrict ms_mem] in HRf.
      assert (S208 : mf_slot v (ms_mem msF) Wc 208 (p + Z.of_nat i)).
      { unfold mf_slot.
        pose proof (field_of_region_any _ _ 2 (mf_s1 (mv_sp v)) _ _ _ _ _ 208 8%N _ HRf U2
          ltac:(cbn; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V.
        change (N.to_nat 8) with 8%nat in V.
        rewrite (kr_soff_val E 26 (p + Z.of_nat i) 0 E26 ltac:(lia) ltac:(lia)), Z.add_0_r in V. exact V. }
      assert (S200 : mf_slot v (ms_mem msF) Wc 200 (p + Z.of_nat (i + ei))).
      { unfold mf_slot.
        pose proof (field_of_region_any _ _ 2 (mf_s1 (mv_sp v)) _ _ _ _ _ 200 8%N _ HRf U2
          ltac:(cbn; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V.
        change (N.to_nat 8) with 8%nat in V.
        rewrite (kr_soff_val E 10 (p + Z.of_nat (i + ei)) 0 E10 ltac:(lia) ltac:(lia)), Z.add_0_r in V. exact V. }
      assert (S192 : mf_slot v (ms_mem msF) Wc 192 (p + Z.of_nat (i + ei) + 1)).
      { unfold mf_slot.
        pose proof (field_of_region_any _ _ 2 (mf_s1 (mv_sp v)) _ _ _ _ _ 192 8%N _ HRf U2
          ltac:(cbn; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V.
        change (N.to_nat 8) with 8%nat in V.
        rewrite (kr_soff_val E 10 (p + Z.of_nat (i + ei)) 1 E10 ltac:(lia) ltac:(lia)) in V. exact V. }
      assert (S184 : mf_slot v (ms_mem msF) Wc 184 (p + Z.of_nat j)).
      { unfold mf_slot.
        pose proof (field_of_region_any _ _ 2 (mf_s1 (mv_sp v)) _ _ _ _ _ 184 8%N _ HRf U2
          ltac:(cbn; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V.
        change (N.to_nat 8) with 8%nat in V.
        rewrite (kr_soff_val E 20 (p + Z.of_nat j) 0 E20 ltac:(lia) ltac:(lia)), Z.add_0_r in V. exact V. }
      pmkst HS.
      refine (S1 v lyc Sc Wc _ _ _ pos mcc gi line p rest i j ei _ _ S208 S200 S192 S184 _ _).
      -- unfold kb_ctx.
         exact (conj CX (conj LS (conj FRM (conj CORE' (conj CELLS' (conj Hn (conj Hr (conj LOOP' (conj Hij
           (conj HjL (conj HM (conj (kb_model_disp mcc gi _ line rest ei (mf_final v) HM HFIN) NP')))))))))))).
      -- unfold kb_regs. split; [exact RA'|]. rewrite N27, (EE 27%nat 27%bv eq_refl). exact R27.
      -- rewrite N10, U2. reflexivity.
      -- rewrite N11, U2. reflexivity.
Qed.
End e.
End f.
End d.
